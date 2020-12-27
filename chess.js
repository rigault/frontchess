/* jshint esversion: 6 */
/* jshint -W097 */ // don't warn about "use strict"

"use strict";
const N = 8;
const VOID = 0, PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6, CASTLE_KING = 7;
const ROCKING_GAMER = 9999; // signale que le joueur tente le roque
const REQ_TYPE = 2;
const CINQUANTE = 50; // pour la regle des 50 coups

// const MY_URL = "http://23.251.143.190/cgi-bin/chess.cgi?";
// const MY_URL = "http://192.168.1.100/cgi-bin/chess.cgi?";
const MY_URL = "http://127.0.0.1/cgi-bin/chess.cgi?";

const EVAL_THRESHOLD = 900000;
// Pawn, kNight, Bishop, Rook, Queen, King, rOckking
// FEN notation
// White : minuscules. Black: Majuscules
// Le roi qui roque est code 7. Si non 6.
const DICT = ['-', 'P', 'N', 'B', 'R', 'Q', 'K', 'K' ];

const TRANSLATE = {"-": 0, "P":PAWN, "N": KNIGHT, "B": BISHOP, "R":ROOK, "Q":QUEEN, "K": KING};

// representation HTML des pieces Ordi dans l'ordre  VOID ... CASTLE_KING
// const UNICODE = ["-", "&#x265F", "&#x265E", "&#x265D", "&#x265C", "&#x265B", "&#x265A", "&#x265A"];
// const UNICODE = ["-", " &#x2659", "&#x2658", "&#x2657", "&#x2656", "&#x2655", "&#x2654", "&#x2654"];
const UNICODE = ["-", " &#x265F", "&#x2658", "&#x2657", "&#x2656", "&#x2655", "&#x2654", "&#x2654"];

const KINGSTATE = {NOEXIST:0, EXIST:1, IS_IN_CHECK:2, UNVALID_IN_CHECK:3, IS_MATE:4, IS_PAT:5};

let jeu = [
   [-4,-2,-3,-5,-6,-3,-2,-4],
   [-1,-1,-1,-1,-1,-1,-1,-1],
   [0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0],
   [1,1,1,1,1,1,1,1],
   [4,2,3,5,6,3,2,4]
   ];
//let jeu = [[0,0,0,0,-6,0,0,0],[0,0,-5,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,1,0,0],[0,0,0,0,6,0,0,4]];
//let jeu = [[0,-2,0,0,-6,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,-1,0,0,1,0,0,0],[0,0,0,0,6,0,0,4]];
let historyGame = [JSON.stringify(jeu)];
let indexHistory = 0;
let maxIndexHistory = 0;
let testState = false;
let computerColor = "b";

let gamerCount; // pour chrono Joueur

let responseServer = {}; // objet JSON

let info = {
   indicator: false,
   nb: 1,
   cpt50: 0,
   level: 3,
   normal: true,             // pour representation "normale" avec blanc joueur en bas. Sinon on inverse. Cf display ()
   nGamerPieces: 16,         // nombre de pieces Joueur
   nComputerPieces: 16,      // nombre de pieces Ordi
   lastGamerPlay: '',        // dernier coup joueur au format complet Xa1-b1
   lastGamerPlayA: '',       // dernier coup joueur au format Alg abrege
   lastComputerPos: '',      // dernier coup ordi ai format complet Xa1-b1
   kingStateGamer: 0,
   kingStateComputer: 0,
   castleComputer: "Non",
   castleGamer: "Non",
   story: "",                // historique du jeu
   gamerTime: 0,             // en secondes
   totalGamerTime: 0,
   totalComputerTime: 0,
   lastTakenByGamer: '',     // derniere prise par joueur
   lastTake: '',             // derniere prise par Ord
   leftCastleGamerOK: true,
   rightCastleGamerOK: true
};

let lSource, cSource;

/* Forsyth–Edwards Notation */
function gameToFen (jeu, color, cpt50, noCoup) {
   let n, v;
   let sFen = "";
   let bCastleB = (computerColor == 'w' && (! info.leftCastleGamerOK || ! info.rightCastleGamerOK)); // gamer a les noirs
   let bCastleW = (computerColor == 'b' && (! info.leftCastleGamerOK || ! info.rightCastleGamerOK)); // gamer a les blancs
   for (let l = N-1; l >= 0; l -= 1) {
      for (let c = 0; c < N; c += 1) {
         v = jeu [l][c];
         if (v != VOID) {
            if (v == CASTLE_KING) bCastleB = true;
            if (v == -CASTLE_KING) bCastleW = true;
            sFen += ((v >= 0)? DICT [v].toLowerCase () : DICT [-v]);
         }
         else {
            for (n = 0; (c+n < N) && (jeu [l][c+n] == VOID); n += 1);
            sFen += String.fromCharCode(48 + n);
            c += n-1;
         }
      }
      sFen += '/';
   }
   sFen = sFen.substring(0, sFen.length-1) + "+" + color + "+";
   sFen += (bCastleW ? "-" : "KQ") + (bCastleB ? "-" : "kq");
   sFen += "+-+" + cpt50 + "+" + noCoup;
   return sFen;
}

/* Forsyth–Edwards Notation */
function fenToGame (fen, jeu) {
   let sign;
   let l = 7;
   let c = 0;
   let cChar;
   let fenNorm = fen.replaceAll (' ', '+');   
   let list = fenNorm.split ("+");
   let sFen = list [0];
   let bCastleW = false;
   let bCastleB = false; 
   if (list [2] != null) {
      bCastleW =  (list [2][0] == '-') ;
      bCastleB = (bCastleW ? (list [2][1] == '-') : (list [2][2] == '-'));
   }
   for (let i = 0; i < sFen.length ; i += 1) {
      cChar = sFen [i];
      if (cChar == ' ' || cChar == '\t' || cChar == '\n') break;
      if (cChar == '/') continue; 
      if ((cChar >= '1') && (cChar <= '8')) {
         for (let k = 0; k < (cChar.charCodeAt(0) - 48); k += 1) {
            jeu [l][c] = VOID;
            c += 1;
         }
      }
      else {
         sign = ((cChar == cChar.toUpperCase())? -1 : 1);
         jeu [l][c] = sign * TRANSLATE [cChar.toUpperCase()];
         if ((cChar == 'K') && (bCastleW)) jeu [l][c] = -CASTLE_KING; // roi blanc a deja roque
         if ((cChar == 'k') && (bCastleB)) jeu [l][c] = CASTLE_KING; // roi noir a deja roque
         c += 1;
      }
      if (c == N) {
         l -= 1;
         c = 0;
      }
   }
   return jeu;
}

function symetryV (sq64, l1, c1, cDest) { 
   /* vraie si il y a une piece egale a l1, c1 dans le symetrique par rapport a la colonne cDest */
   let cSym = cDest + cDest - c1;
   return (cSym >= 0 && cSym < N) ? (sq64 [l1][c1] == sq64 [l1][cSym]): false;
}

function symetryH (sq64, l1, c1, lDest) { 
   /* vraie si il y a une piece egale a l1, c1 dans le symetrique par rapport a la ligne lDest */
   let lSym = lDest + lDest - l1;
   return (lSym >= 0 && lSym < N) ? (sq64 [l1][c1] == sq64 [lSym][c1]): false;
}

function abbrev (sq64, complete) { /* */ 
   /* transforme la specif algebriqe complete en abregee */
   let l1 = parseInt (complete [2]) - 1;
   let l2 = parseInt (complete [5]) - 1;
   let c1 = complete.charCodeAt(1) - 'a'.charCodeAt(0);
   let c2 = complete.charCodeAt(4) - 'a'.charCodeAt(0);
   let cCharPiece = complete [0]; 
   let prise = complete [3];
   let v = sq64 [l1][c1];
   let promotion = "";
   let spec = "";                    // pour notation algebrique abrégée
   let abbr = "";
   if (complete.length >= 7) promotion = '=' + complete [7];
   // calcul de la notation abregee
   switch (Math.abs (v)) {                              
   case PAWN:
      cCharPiece = ""; 
      if ((prise == 'x') && (symetryV (sq64, l1, c1, c2))) // il y a deux pions symetrique prenant en c2 a partir de la ligne l1
         spec = String.fromCharCode(97+c1);              // on donne la colonne
      break;
   case KNIGHT:
      if (symetryV (sq64, l1, c1, c2)) spec = String.fromCharCode(97+c1); //cavaliers symetrique par rapport à la col. dest
      else if (symetryH (sq64, l1, c1, l2)) spec = String.fromCharCode(49+l1); //cavaliers symetrique par rapport à la ligne dest
      break;
   case ROOK:
      if ((l1 == l2) && (c1 < c2)) {               // meme ligne, recherche a droite  
         for (let i = (c2 + 1); i < N; i++) {
            if (sq64 [l1][i] == v) {// il y a une autre tour en position d'aller vers l2 c2
               spec = String.fromCharCode(97+c1);   // Trouve. on donne la colonne
               break;
            }
            if (sq64 [l2][i] != VOID) break;
         }
      }
      if ((l1 == l2) && (c1 > c2)) {               // meme ligne, recherche a droite  
         for (let i = (c2 - 1); i >= 0; i--) {
            if (sq64 [l1][i] == v) {// il y a une autre tour en position d'aller vers l2 c2
               spec = String.fromCharCode(97+c1);                    // Trouve. On donne la colonne
               break;
            }
            if (sq64 [l2][i] != VOID) break;
         }
      }
      if ((c1 == c2) && (l1 < l2)) {               // meme colonne, recherche en bas 
         for (let i = (l2 + 1); i < N; i++) {
            if (sq64 [i][c1] == v) {// il y a une autre tour en position d'aller vers l2 c2
               spec = String.fromCharCode(49+l1);
               break;
            }
            if (sq64 [i][c2] != VOID) break;
         }
      }
      if ((c1 == c2) && (l1 > l2)) {               // meme colonne, recherce en haut  
         for (let i = (l2 - 1); i >= 0; i--) {
            if (sq64 [i][c1] == v) {// il y a une autre tour en position d'aller vers l2 c2
               spec = String.fromCharCode(49+l1);
               break;
            }
            if (sq64 [i][c2] != VOID) break;
         }
      }
      break;
   case QUEEN: // cas ou il y aurait 2 reines apres une promotion
      for (let l = 0; l < N; l++)
         for (let c = 0; c < N; c ++)
            if (l != l1 && c != c1 && sq64 [l][c] == v) spec = String.fromCharCode(97+c1) + String.fromCharCode(49+l1);
      break;
   default:; // BISHOP, KING
   }
   abbr = cCharPiece + spec + ((prise == 'x') ? "x" : "") + String.fromCharCode(97+c2) + String.fromCharCode(49+l2) + promotion;
   return abbr;
}

/* vrai si le roi situe case l, c est echec au roi */
/* 'who' est la couleur du roi who est attaque */
function LCkingInCheck (sq64, who, l, c) {
   let w, w1, w2, i, j, k;

   // pion menace
   if (who == -1) {
      if (l < 7) {
         if (c < 7 && sq64 [l+1][c+1] == PAWN) return true;
         if (c > 0 && sq64 [l+1][c-1] == PAWN) return true;
      }
   }
   else { //  who == 1
      if (l > 0) {
         if (c < 7 && sq64 [l-1][c+1] == -PAWN) return true;
         if (c > 0 && sq64 [l-1][c-1] == -PAWN) return true;
      }
   } // fin if (who...
   w1 = -who * KING;
   w2 = -who * CASTLE_KING;
   // roi adverse  menace
   if (l < 7 && (sq64 [l+1][c] == w1 || sq64 [l+1][c] == w2)) return true;
   if (l > 0 && (sq64 [l-1][c] == w1 || sq64 [l-1][c] == w2)) return true;
   if (c < 7 && (sq64 [l][c+1] == w1 || sq64 [l][c+1] == w2)) return true;
   if (c > 0 && (sq64 [l][c-1] == w1 || sq64 [l][c-1] == w2)) return true;
   if (l < 7 && c < 7 &&(sq64 [l+1][c+1] == w1 || sq64 [l+1][c+1] == w2)) return true;
   if (l < 7 && c > 0 &&(sq64 [l+1][c-1] == w1 || sq64 [l+1][c-1] == w2)) return true;
   if (l > 0 && c < 7 &&(sq64 [l-1][c+1] == w1 || sq64 [l-1][c+1] == w2)) return true;
   if (l > 0 && c > 0 &&(sq64 [l-1][c-1] == w1 || sq64 [l-1][c-1] == w2)) return true;

   w = -who * KNIGHT;
   // cavalier menace
   if (l < 7 && c < 6 && sq64 [l+1][c+2] == w) return true;
   if (l < 7 && c > 1 && sq64 [l+1][c-2] == w) return true;
   if (l < 6 && c < 7 && sq64 [l+2][c+1] == w) return true;
   if (l < 6 && c > 0 && sq64 [l+2][c-1] == w) return true;
   if (l > 0 && c < 6 && sq64 [l-1][c+2] == w) return true;
   if (l > 0 && c > 1 && sq64 [l-1][c-2] == w) return true;
   if (l > 1 && c < 7 && sq64 [l-2][c+1] == w) return true;
   if (l > 1 && c > 0 && sq64 [l-2][c-1] == w) return true;

   w1 = -who * QUEEN;
   w2 = -who * ROOK;
   // tour ou reine menace
   for (i = l+1; i < N; i++) {
      w = sq64 [i][c];
      if (w == w1 || w == w2) return true;
      if (w != 0) break;
   }
   for (i = l-1; i >= 0; i--) {
      w = sq64 [i][c];
      if (w == w1 || w == w2) return true;
      if (w != 0) break;
   }
   for (j = c+1; j < N; j++) {
      w = sq64 [l][j];
      if (w == w1 || w == w2) return true;
      if (w != 0) break;
   }
   for (j = c-1; j >= 0; j--) {
      w = sq64 [l][j];
      if (w == w1 || w == w2) return true;
      if (w != 0) break;
   }

   // fou ou reine menace
   w2 = -who * BISHOP;
   for (k = 0; k < Math.min (7-l, 7-c); k++) { // vers haut droit
      w = sq64 [l+k+1][c+k+1];
      if (w == w1 || w == w2) return true;
      if (w != 0) break;
   }
   for (k = 0; k < Math.min (7-l, c); k++) {// vers haut gauche
      w = sq64 [l+k+1][c-k-1];
      if (w == w1 || w == w2) return true;
      if (w != 0) break;
   }
   for (k = 0; k < Math.min (l, 7-c); k++) { // vers bas droit
      w = sq64 [l-k-1][c+k+1];
      if (w == w1 || w == w2) return true;
      if (w != 0) break;
   }
   for (k = 0; k < Math.min (l, c); k++) { // vers bas gauche
      w = sq64 [l-k-1] [c-k-1];
      if (w == w1 || w == w2) return true;
      if (w != 0) break;
   }

   return false;
}

/* verifie que le deplacement choisi est valide */
/* renvoie ROCKING_GAMER ou vrai ou faux */
function verification (jeu, l, c, lDest, cDest, who) {
   let k;
   let sup;
   let v = jeu[l][c];
   let w = jeu[lDest][cDest];

   // pour roquer le roi ne doit pas etre en echec (etat = EXIST), il ne doit pas avoir bouge et les
   // cases intemédiaires ne doivet pas etre echec au roi
   if (who == 1 && v == KING && w == ROOK && l == 7 && c == 4 && lDest == 7 && cDest == 1 && 
      jeu[7][3] == 0 && jeu [7][2] == 0 && jeu [7][1] == 0 && 
      info.leftCastleGamerOK && info.kingStateGamer == KINGSTATE.EXIST &&
      ! LCkingInCheck (jeu, who, 7,4) && ! LCkingInCheck (jeu, who, 7,3) && ! LCkingInCheck (jeu, who, 7,2))
      return ROCKING_GAMER;

   if (who == 1 && v == KING && w == ROOK && l == 7 && c == 4 && lDest == 7 && cDest == 7 && 
      jeu[7][5] == 0 && jeu [7][6] == 0 && 
      info.rightCastleGamerOK && info.kingStateGamer == KINGSTATE.EXIST &&
      ! LCkingInCheck (jeu, who, 7, 4) && ! LCkingInCheck (jeu, who, 7, 5) && ! LCkingInCheck (jeu, who, 7,6))
      return ROCKING_GAMER;

   if (who == -1 && v == -KING && w == -ROOK && l == 0 && c == 4 && lDest == 0 && cDest == 0 && 
      jeu[0][3] == 0 && jeu [0][2] == 0 && jeu[0][1] == 0 && 
      info.leftCastleGamerOK && info.kingStateGamer == KINGSTATE.EXIST && 
      ! LCkingInCheck (jeu, who, 0, 4) && ! LCkingInCheck (jeu, who, 0, 3) && ! LCkingInCheck (jeu, who, 0, 2))
      return ROCKING_GAMER;
   
   if (who == -1 && v == -KING && w == -ROOK && l == 0 && c == 4 && lDest == 0 && cDest == 7 && 
      jeu[0][5] == 0 && jeu [0][6] == 0 && 
      info.rightCastleGamerOK && info.kingStateGamer == KINGSTATE.EXIST &&
      ! LCkingInCheck (jeu, who, 0, 4) && ! LCkingInCheck (jeu, who, 0, 5) && ! LCkingInCheck (jeu, who, 0,6))
      return ROCKING_GAMER;
   
   if  (v*w > 0) return false;

   switch (Math.abs (v)) {
   case PAWN:
      if (who == -1) {
         if ((l == 1) && ((lDest == 2) || (lDest == 3)) && (c == cDest) && (w == 0)) return true;
         if ((lDest ==  l+1) && (c == cDest) && (w == 0)) return true;
         if ((lDest == l+1) && ((cDest == c-1) || (cDest == c+1)) && (w*who < 0)) return true;
      }
      if (who == 1) {
         if ((l == 6) && ((lDest ==  5) || (lDest == 4)) && (c == cDest) && (w == 0)) return true;
         if ((lDest ==  l-1) && (c == cDest) && (w == 0)) return true;
         if ((lDest == l-1) && ((cDest == c-1) || (cDest == c+1)) && (w*who < 0)) return true;
     }
     break;

   case KING: case CASTLE_KING:
      return ((Math.abs (cDest-c) * (lDest-l) <= 1) && (Math.abs (cDest - c) == 1 || (Math.abs (lDest - l) == 1)));

   case KNIGHT:
      return (Math.abs((lDest-l) * (cDest-c)) == 2);

   case ROOK: case QUEEN:
      if (l == lDest) {
         for (k=c+1; k<cDest; k += 1) if (jeu [l][k] != 0) return false;
         for (k=c-1; k>cDest; k -= 1) if (jeu [l][k] != 0) return false;
         return true;
      }
      if (c == cDest) {
         for (k=l+1; k<lDest; k += 1) if (jeu [k][c] != 0) return false;
         for (k=l-1; k>lDest; k -= 1) if (jeu [k][c] != 0) return false;
         return true;
      }
   // surtout ne pas ajouter de break.
   case BISHOP: case QUEEN:
      if (Math.abs(lDest-l)== Math.abs(cDest-c)) {
         sup = Math.min (Math.abs(c-cDest), Math.abs (l-lDest))-1;
         if (lDest > l && cDest > c)
            for (k = 0; k < sup; k += 1)
               if (jeu [l+k+1][c+k+1] != 0) return false;
         if (lDest > l && cDest < c)
            for (k = 0; k < sup; k +=1)
               if (jeu [l+k+1][c-k-1] != 0) return false;
         if (lDest < l && cDest > c)
            for (k = 0; k < sup; k += 1)
               if (jeu [l-k-1][c+k+1] != 0) return false;
         if (lDest < l && cDest < c)
            for (k = 0; k < sup; k += 1)
               if (jeu [l-k-1][c-k-1] != 0) return false;
         return true;
      }
      break;
   default:
   }
   return false;
}

/* verifie que la case choisie par le joueur est valide */
function choiceIsOK (jeu, l, c, who) {
   let v = jeu[l][c];
   if  (v*who <= 0) return false;
   switch (Math.abs (v)) {
   case PAWN:
      if (who == -1) {
         if ((l+1 < N && jeu [l+1][c] == 0) ||
             (l+1 < N && c-1 >= 0 && jeu [l+1][c-1] > 0) ||
             (l+1 < N && c+1 <= N && jeu [l+1][c+1] > 0))
            return true;
      }
      else {
         if ((l-1 >= 0 && jeu [l-1][c] == 0) ||
             (l-1 >= 0 && c-1 >= 0 && jeu [l-1][c-1] < 0) ||
             (l-1 >= 0 && c+1 <= N && jeu [l-1][c+1] < 0))
            return true;
      }
      break;
   case KING: case CASTLE_KING: case ROOK: case QUEEN:
      if ((l+1 < N && jeu [l+1][c]*who <= 0) ||
          (l-1 >=0 && jeu [l-1][c]*who <= 0) ||
          (c+1 < N && jeu [l][c+1]*who <= 0) ||
          (c-1 >=0 && jeu [l][c-1]*who <= 0))
         return true;
      if (Math.abs (v) == ROOK) 
         return false;
      // ne pas inserer de break !
   case BISHOP: // valide aussi pour KING CASTLE_KING et QUEEN
      if ((l+1 < N && c+1 < N && jeu [l+1][c+1]*who <= 0) ||
          (l-1 >=0 && c+1 < N && jeu [l-1][c+1]*who <= 0) ||
          (l+1 < N && c-1 < N && jeu [l+1][c-1]*who <= 0) ||
          (l-1 >=0 && c-1 < N && jeu [l-1][c-1]*who <= 0))
         return true;
      break;
   case KNIGHT:
      if ((l+1 < N && c+2 < N && jeu [l+1][c+2]*who <= 0) ||
          (l-1 >=0 && c+2 < N && jeu [l-1][c+2]*who <= 0) ||
          (l+1 < N && c-2 < N && jeu [l+1][c-2]*who <= 0) ||
          (l-1 >=0 && c-2 < N && jeu [l-1][c-2]*who <= 0) ||
          (l+2 < N && c+1 < N && jeu [l+2][c+1]*who <= 0) ||
          (l-2 >=0 && c+1 < N && jeu [l-2][c+1]*who <= 0) ||
          (l+2 < N && c-1 < N && jeu [l+2][c-1]*who <= 0) ||
          (l-2 >=0 && c-1 < N && jeu [l-2][c-1]*who <= 0))
         return true;
      break;
   default:
   }
   return false;
}

/* traduit des secondes au format HH:MM:SS */
function secToHHMMSS(sec) {
   let sec_num = parseInt(sec);
   let hours   = Math.floor(sec_num / 3600);
   let minutes = Math.floor((sec_num - (hours * 3600)) / 60);
   let seconds = sec_num - (hours * 3600) - (minutes * 60);

   if (hours   < 10) {hours   = "0"+hours;}
   if (minutes < 10) {minutes = "0"+minutes;}
   if (seconds < 10) {seconds = "0"+seconds;}
   return hours+':'+minutes+':'+seconds;
}

/* affiche le chrono joueur */
function chronoGamer() {
   document.getElementById ('timePlayer').value = secToHHMMSS (info.gamerTime);
   info.gamerTime += 1;
   document.getElementById ('cumulTimePlayer').value = secToHHMMSS (info.totalGamerTime);
   info.totalGamerTime += 1;
}

/* met a jour le niveau pour profondeur de la recherche */
function updateLevel () {
   document.getElementById ('niveauValeur').innerHTML = document.getElementById ('niveau').value;
   info.level = parseInt (document.getElementById ('niveau').value);
}

/* provoque une requete vers le serveur */
function pass () {
   infoUpdate (jeu);
   displayUpdate ();
   display ();
   clearInterval (gamerCount);
   document.getElementById ('info').value = "Le serveur pense... !\n";
   document.getElementById ('FEN').value = gameToFen (jeu, computerColor, info.cpt50, info.nb);
   serverRequest ();
}

/* inverse l'affichage */
function reverseDisplay () {
   info.normal = !info.normal;
   display ();
}

/* fait passer du mode normal au mode test */
function reverseTest () {
   testState = !testState;
   if (testState)  document.getElementById ('test').value = 'TEST';
   else document.getElementById ('test').value = 'NORM';
}

/* va un coup en arrière */
function back () {
   if (indexHistory > 0) {
      document.getElementById ('info').value = '';
      indexHistory -= 1;
      jeu = JSON.parse(historyGame [indexHistory]);
      infoUpdate (jeu);
      displayUpdate ();
      display ();
   }
}

/* repart un coup en avant */
function forward () {
   if (indexHistory < historyGame.length - 1) {
      indexHistory += 1;
      jeu = JSON.parse(historyGame [indexHistory]);
      infoUpdate (jeu);
      displayUpdate ();
      display ();
   }
}

/* met à jour le jeu suite à saisie d'un chaîne FEN */
function refresh () {
   jeu = fenToGame (document.getElementById ('FEN').value, jeu);
   infoUpdate (jeu);
   displayUpdate ();
   display ();
}

/* met à jour le jeu suite à saisie d'un chaîne FEN */
function whoGetWhites () {
   computerColor = (computerColor == "b") ? "w" : "b";
   alert ("computerColor = " + computerColor);
   infoUpdate (jeu);
   displayUpdate ();
   reverseDisplay ();
}

/* retourne false si on arrete le jeu, TRUE si on continue */
/* affiche un info fonction des codes reçus du serveur */
function statusAnalysis () {
   // NO_EXIT = 0, EXIST = 1, IS_IN_CHECK = 2, UNVALID_IN_CHECK = 3, IS_MATE = 4, IS_PAT = 5;
   const STATE_MESSAGE_PLAYER = [
      "Il n'y a pas de roi joueur. C'est fini\n", 
      "", 
      "Tu es echec au Roi !\n" , 
      "Tu es echec au Roi, tu n'as pas le droit, c'est fini !\n", 
      "Tu es MAT, c'est fini !\n", 
      "Jeu Pat !, c'est fini.\n" 
   ];
   const STATE_MESSAGE_COMPUTER = [
      "Il n'y a pas de roi Ordi. C'est fini.\n", 
      "", 
      "Je suis echec au Roi !. Bizarre. C'est fini.\n", 
      "Etat bizarre !, cest fini.\n", 
      "Je suis MAT, c'est fini.\n", 
      "Jeu Pat !, c'est fini.\n" 
   ];
   let r = parseInt (responseServer.playerStatus);
   document.getElementById ('info').value = STATE_MESSAGE_PLAYER [r]; 

   if (r != KINGSTATE.EXIST && r != KINGSTATE.IS_IN_CHECK) return false;
   
   r = parseInt (responseServer.computerStatus);
   document.getElementById ('info').value += STATE_MESSAGE_COMPUTER [r]; 
   if (r != KINGSTATE.EXIST) return false;

   let intComputerColor = (computerColor == "b") ? 1 : -1;

   if ((parseInt (responseServer.eval) * intComputerColor >= EVAL_THRESHOLD) ||
      (parseInt (responseServer.wdl) == 4 && intComputerColor == 1) ||
      (parseInt (responseServer.wdl) == 0 && intComputerColor == -1))
      document.getElementById ('info').value += "Je vais gagner, c'est certain !\n";
   if (info.cpt50 >= CINQUANTE)
      document.getElementById ('info').value = "Règle des 50 coups sans prise ni mouv. pion atteinte";
   return true;
}

/* saisie du deplacement par le joueur sans vérif pour test */
function test (nom) {
   let lDest, cDest;
   let v;
   let elem = document.getElementById (nom);

   if (info.lastGamerPlay == '') {                    // saisie de la case source
      lSource = parseInt (nom [1]) - 1;
      cSource =  nom.charCodeAt(0) - 'a'.charCodeAt(0);
      info.lastGamerPlay = nom;                       // la case source
      elem.style.background = 'olive';
      elem.style.color = 'white';
      }
   else {                                             // saisie de la case destination
      lDest = parseInt (nom [1]) - 1;
      cDest =  nom.charCodeAt(0) - 'a'.charCodeAt(0);
      v = jeu [lSource][cSource];
      if ((v == -PAWN) && (lDest == 7)) jeu [lDest][cDest] = -QUEEN; // promotion
      else jeu [lDest][cDest] = v;
      jeu [lSource][cSource] = 0;
      infoUpdate (jeu);
      displayUpdate ();
      display ();
      info.lastGamerPlay = '';
   }
}

/* saisie du deplacement par le joueur */
function moveRead (nom) {
   if (testState) {
      test (nom);
      return;
   }
   let lDest, cDest;
   let v;
   let carPiece;
   let res;
   let prise;
   let spaces;
   let gamerColor = ((computerColor == "b") ? -1 : 1);
   let elem = document.getElementById (nom);
   let pawnMove = false;

   if ((info.kingStateGamer == KINGSTATE.NOEXIST) || (info.kingStateGamer == KINGSTATE.IS_MATE))
      return;

   if (info.lastGamerPlay == '') {                               // saisie de la case source
      lSource = parseInt (nom [1]) - 1;
      cSource =  nom.charCodeAt(0) - 'a'.charCodeAt(0);
      if (choiceIsOK (jeu, lSource, cSource, gamerColor)) {      // who a le meme signe que la case jouee
         info.lastGamerPlay = nom;                               // la case source
         elem.style.background = 'olive';
         elem.style.color = 'white';
      }
      return;
   }

   lDest = parseInt (nom [1]) - 1;
   cDest =  nom.charCodeAt(0) - 'a'.charCodeAt(0);
   if (lSource == lDest && cSource == cDest) {                //+ on annule tout
      info.lastGamerPlay = '';
      display ();
      return;
   }

   res = verification(jeu, lSource, cSource, lDest, cDest, gamerColor);
   if (Math.abs(jeu [lSource][cSource]) == KING) { 
         info.leftCastleGamerOK = false;
         info.rightCastleGamerOK = false;
   }
	   
   if (Math.abs(jeu [lDest][cDest]) == ROOK) {
      if (cDest == 7) info.rightCastleGamerOK = false;
      else if (cDest == 0) info.leftCastleGamerOK = false;
   }
   if (res == ROCKING_GAMER) {
      spaces = (info.nb < 10) ? "  ": ((info.nb < 100) ? " " : "");
      info.rightCastleGamerOK = false;
      info.leftCastleGamerOK = false;
      if (cDest == 0) {           // grand Roque
         jeu [lSource][0] = 0;
         jeu [lSource][2] = gamerColor * CASTLE_KING;
         jeu [lSource][3] = gamerColor * ROOK;
         jeu [lSource][4] = 0;
         info.lastGamerPlay = "O-O-O";
         info.story += "\n" + info.nb + spaces + "  O-O-O";
      }
      else if (cDest == 7) {       //petit Roque
         jeu [lSource][4] = 0;
         jeu [lSource][5] = gamerColor * ROOK;
         jeu [lSource][6] = gamerColor * CASTLE_KING;
         jeu [lSource][7] = 0;
         info.lastGamerPlay = "O-O";
         info.story += "\n" + info.nb + spaces + "    O-O";
      }
   }
   else if (res == true) {
      v = Math.abs (jeu [lDest][cDest]);
      info.lastTakenByGamer = (v != 0) ? UNICODE [v]: '';  // prise de piece
      prise = (v != 0)? 'x' : '-';
      v = Math.abs(jeu [lSource][cSource]);
      carPiece = DICT [v];
      info.lastGamerPlay = carPiece + info.lastGamerPlay + prise + nom; // source + destination
      info.lastGamerPlayA = abbrev (jeu, info.lastGamerPlay);
      if ((info.story != '') && (gamerColor == -1)) info.story += '\n';
      spaces = (info.nb < 10) ? "  ": ((info.nb < 100) ? " " : "");
      if (gamerColor == -1) info.story += info.nb + spaces + "   " + info.lastGamerPlayA.padStart(4, ' ');
      else info.story += "   " + info.lastGamerPlayA.padStart(4, ' ');
      pawnMove = (Math.abs (jeu [lSource][cSource])) == PAWN;

      if (((jeu [lSource][cSource] == -PAWN) && (lDest == 7)) || 
         ((jeu [lSource][cSource] == PAWN) && (lDest == 0)))  {
         jeu [lDest][cDest] = gamerColor * QUEEN; // promotion
         info.story += "=Q";
      }
      else jeu [lDest][cDest] = jeu [lSource][cSource];
      jeu [lSource][cSource] = 0;
   }
   if (res == ROCKING_GAMER || res == true) {
      if (computerColor != 'b') info.nb += 1; // computer a les blancs
      if (prise == 'x' || pawnMove) 
         info.cpt50 = 0;
      else info.cpt50 += 1; 
      infoUpdate (jeu);
      displayUpdate ();
      display ();
      clearInterval (gamerCount);
      document.getElementById ('info').value = "Le serveur pense... !\n";
      document.getElementById ('FEN').value = gameToFen (jeu, computerColor, info.cpt50, info.nb);
      if (info.cpt50 > CINQUANTE)
         alert ("règle des 50 coups atteinte");
      else serverRequest ();
   }
}

/* envoie requete asynchrone XMLHttpRequest au serveur */
function serverRequest () {
   let response;
   let http = new XMLHttpRequest ();
   let gamerColor = ((computerColor == "b") ? -1 : 1);
   let spaces;
   let url = MY_URL + "reqType=" + REQ_TYPE + "&level=" + info.level;
   url += "&fen=" + gameToFen (jeu, computerColor, info.cpt50, info.nb);
   console.log ("\nurl: %s\n", url);
   // alert (url);
   
   http.onreadystatechange = function (event) {
   // XMLHttpRequest.DONE === 4
      if (this.readyState === XMLHttpRequest.DONE) {
         if (this.status === 200) {
            console.log ("Réponse reçue: %s\n", this.responseText);
            response = this.responseText;
            // alert (response);
            responseServer = JSON.parse (response);
            fenToGame (responseServer.fen, jeu);
            if ((info.story != '') && (gamerColor == 1)) info.story += '\n';
            spaces = (info.nb < 10) ? "  ": ((info.nb < 100) ? " " : "");
            info.story += (gamerColor == 1) ? info.nb + spaces : "";
            info.story += "    " + responseServer.computePlayA.padStart(4, ' ');
            info.lastComputerPos = responseServer.computePlayC;
            new Audio ('beep.wav').play ();
            document.getElementById ('info').value = "A toi de jouer\n";
            info.indicator = true;
            if (computerColor == 'b') info.nb += 1; // computer a les noirs
            if (responseServer.computePlayC [0] == 'P' || responseServer.computePlayC [3] == 'x') 
               info.cpt50 = 0;
            else info.cpt50 += 1;
            infoUpdate (jeu);
            displayUpdate ();
            info.lastGamerPlay = '';
            info.gamerTime = 0;
            display ();
            indexHistory += 1;
            historyGame [indexHistory] = JSON.stringify(jeu);
            historyGame.length = indexHistory + 1; // a garder meme si semble bizarre 
            if (statusAnalysis ())
               gamerCount = setInterval (chronoGamer,1000); //la fonction est relancee
            // else alert ("C'est fini : faire RAZ");
         }
      }
   };
   http.open('GET', url, true);
   http.send (null);
}

/* met a jour l'objet info a partir de l'objet jeu */
function infoUpdate (jeu) {
   let v;
   let color = (computerColor == 'b') ? 1 : -1;
   info.kingStateGamer = info.kingStateComputer = KINGSTATE.NOEXIST;
   info.castleComputer = info.castleGamer = "Non";
   info.nGamerPieces = info.nComputerPieces = 0;
   for (let l = 0; l < N; l += 1) {
      for (let c = 0; c < N; c += 1) {
         v = jeu[l][c] * color;
         if (v > 0) info.nComputerPieces += 1;
         else if (v < 0) info.nGamerPieces += 1;
         if (v == KING || v == CASTLE_KING) {
            info.kingStateComputer = KINGSTATE.EXIST;
         }
         if (v == CASTLE_KING) info.castleComputer = "Oui";
         if (v == -KING || v == -CASTLE_KING) {
            info.kingStateGamer = KINGSTATE.EXIST;
         }
         if (v == -CASTLE_KING) info.castleGamer = "Oui";
      }
   }
}

/* met a jour la page */
function displayUpdate () {
   // info.noJoueur = info.noOrdi = 0;
   if (responseServer.gameFEN != null)
      document.getElementById ('FEN').value = responseServer.gameFEN;
   if (responseServer.dump != null)
      document.getElementById ('dump').innerHTML = responseServer.dump;
   if (responseServer.note != null)
      document.getElementById ('note').value = parseInt (responseServer.note);
   if (responseServer.eval != null) {
      document.getElementById ('eval').value = parseInt (responseServer.eval);
   }
   if (responseServer.computePlayC != null)
      document.getElementById ('computePlay').value = responseServer.computePlayA;
   if (responseServer.openingName != null)
      document.getElementById ('message').value = responseServer.openingName.trim();
   if (responseServer.endName != null && responseServer.endName != '')
      document.getElementById ('message').value = responseServer.endName;

   if (responseServer.lastTake != null && responseServer.lastTake != '' && responseServer.lastTake != ' ') 
      info.lastTake = UNICODE [TRANSLATE [responseServer.lastTake.toUpperCase()]];
   else info.lastTake = '';

   document.getElementById ('lastTake').innerHTML += info.lastTake;
   responseServer.lastTake = '';

   if (responseServer.time != null) {
      document.getElementById ('timeComputer').value = secToHHMMSS (parseFloat(responseServer.time));
      info.totalComputerTime += parseFloat (responseServer.time);
      document.getElementById ('cumulTimeComputer').value = secToHHMMSS (info.totalComputerTime);
   }

   //b : black. Inversion car joueur
   document.getElementById ('votreCouleur').value = (computerColor == 'b') ? "blanche" : "noire"; 
   document.getElementById ('noCoup').value = info.nb;
   document.getElementById ('cpt50').value = info.cpt50;
   document.getElementById ('dernierJoueur').value = info.lastGamerPlayA; // dernier coup du joueur
   document.getElementById ('nJoueur').value = info.nGamerPieces;             // nb de pieces
   document.getElementById ('nOrdi').value = info.nComputerPieces;                 //nb de pieces
   document.getElementById ('joueurRoque').value = info.castleGamer;
   document.getElementById ('ordiRoque').value = info.castleComputer;
   document.getElementById ('historique').value = info.story;
   document.getElementById ('piecePrise').innerHTML += info.lastTakenByGamer;
   info.lastTakenByGamer = '';
}

/* partie commune dans Display */
function commonDisplay (l, c) {
   //istr contient le nom de la case au format a1
   let istr = String.fromCharCode(97+c) + String.fromCharCode(49+l);
   let v = jeu [l][c];
   let sBut = "<button class = '";
   if ((info.lastComputerPos.indexOf ("O-O") != -1) && info.indicator) { // cas du roque
      info.indicator = false;
      alert ("Roque !");
   }
   if ((info.lastComputerPos.slice (4, 6) == istr) && info.indicator) {
       info.indicator = false;
       sBut += "last";
   }
   sBut += ((c + l) % 2) ? "blanc" : "noir";
   sBut += (v > 0) ? "Ordi" : ((v < 0) ? "Joueur" : "Vide");
   sBut += "' onclick = 'moveRead (";
   sBut += '"' + istr + '"';
   sBut += ")' ";
   sBut += 'id = ' + istr + '>';
   sBut += (v > 0) ? UNICODE [v] : UNICODE [-v];
   sBut += '</button>\n';
   return sBut;
}

/* affiche l echiquier en page HTML */
function display () {
   let l, c;
   let sJeu= "<p><button class = 'deco'>-</button>";
   if (info.normal) { // a l'endroit : noirs en haut
      for (c = 0; c < N; c +=1) {
         sJeu+= " <button class = 'deco'>"+String.fromCharCode(97+c) + "</button>\n";
      }
      sJeu += "<button class = 'deco'>-</button>\n";
      for (l = N-1; l >=0; l -=1) {
         sJeu+= "<br/><button class = 'deco'>" + String.fromCharCode(49+l) + "</button>\n";
         for (c = 0; c < N; c +=1)
	    sJeu += commonDisplay (l, c);
         sJeu+= "<button class = 'deco'>" + String.fromCharCode(49+l) + "</button>\n";
      }
      sJeu+= "<br/>";
      sJeu+= "<button class = 'deco'>-</button>\n";
      for (c = 0; c < N; c += 1)
         sJeu += "<button class = 'deco'>" + String.fromCharCode(97+c) + "</button>\n";
      sJeu += "<button class = 'deco'>-</button>\n";
   }
   else { // a l'envers
      for (c = N-1; c >= 0; c -= 1)
         sJeu+= " <button class = 'deco'>"+String.fromCharCode(97+c) + "</button>";
      sJeu += "<button class = 'deco'>-</button>\n";
      for (l = 0; l < N; l += 1) {
         sJeu+= "<br/><button class = 'deco'>" + String.fromCharCode(49+l) + "</button>";
         for (c = N-1; c >= 0; c -= 1)
	    sJeu += commonDisplay (l, c);
         sJeu+= "<button class = 'deco'>" + String.fromCharCode(49+l) + "</button>\n";
      }
      sJeu+= ("<br/>");
      sJeu+= "<button class = 'deco'>-</button>\n";
      for (c = N-1; c >= 0; c -= 1)
         sJeu += "<button class = 'deco'>" + String.fromCharCode(97+c) + "</button>\n";
      sJeu += "<button class = 'deco'>-</button>\n";
   }
   document.getElementById('milieu').innerHTML = sJeu;
}

/* programme principal */
function main () {
   gamerCount = setInterval (chronoGamer,1000); // la fonction est relancee
   infoUpdate (jeu);
   displayUpdate ();
   display ();
   document.getElementById ('niveau').value = info.level;
   document.getElementById ('niveauValeur').innerHTML = document.getElementById ('niveau').value;
}
