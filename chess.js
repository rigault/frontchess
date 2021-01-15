/* jshint esversion: 6 */
/* jshint -W097 */ // don't warn about "use strict"

"use strict";
const N = 8;
const PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6, CASTLE_KING = 7;
const CASTLING_GAMER = 999;  // signale que le joueur tente le roque
const EN_PASSANT = 998;      // signale que le joueur tente la prise en passant
const REQ_TYPE = 2;
const CINQUANTE = 50;         // pour la regle des 50 coups
const EVAL_THRESHOLD = 9000;

// const MY_URL = "http://23.251.143.190/cgi-bin/chess.cgi?"; // GCP
// const MY_URL = "http://192.168.1.100/cgi-bin/chess.cgi?";  // serveur reseau local
const MY_URL = "http://127.0.0.1/cgi-bin/chess.cgi?";  // mac

// Pawn, kNight, Bishop, Rook, Queen, King, rOckking
// FEN notation
// White : minuscules. Black: Majuscules
// Le roi qui roque est code 7. Si non 6.
const DICT = ['-', 'P', 'N', 'B', 'R', 'Q', 'K', 'K' ];

const TRANSLATE = {"-": 0, "P":PAWN, "N": KNIGHT, "B": BISHOP, "R":ROOK, "Q":QUEEN, "K": KING};

// representation HTML des pieces Ordi dans l'ordre  PAWN ... CASTLE_KING
// const UNICODE = [" ", "&#x265F", "&#x265E", "&#x265D", "&#x265C", "&#x265B", "&#x265A", "&#x265A"];
// const UNICODE = [" ", " &#x2659", "&#x2658", "&#x2657", "&#x2656", "&#x2655", "&#x2654", "&#x2654"];
const UNICODE = ["&nbsp;", " &#x265F", "&#x2658", "&#x2657", "&#x2656", "&#x2655", "&#x2654", "&#x2654"];

const KINGSTATE = {NOEXIST:0, EXIST:1, IS_IN_CHECK:2, UNVALID_IN_CHECK:3, IS_MATE:4, IS_PAT:5};

const initFen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR+w+KQkq";
// const initFen = "4k3/8/8/8/p7/8/8/4K3+w+-";

let jeu = new Array (N);      // cree le jeu un tableau de N lignes qui contiendront N Cases (cd inii dans main)
let historyGame = [JSON.stringify(jeu)];
let indexHistory = 0;
let testState = false;
let gamerCount;               // pour chrono Joueur
let computerCount;            // pour chrono computer quand gere du navigateur
let responseServer = {};      // objet JSON

let info = {
   nb: 1,                     // numero du coup complet en cours
   cpt50: 0,                  // compteur pour regle des 50 coups 
   level: 4,                  // niveau demane au serveur
   normal: true,              // pour representation "normale" avec blanc joueur en bas. Sinon on inverse. Cf display ()
   gamerColor: -1,            // -1 : whites, 1 : black
   nGamerPieces: 16,          // nombre de pieces Joueur
   nComputerPieces: 16,       // nombre de pieces Ordi
   lastGamerPlayC: '',        // dernier coup joueur au format complet Xa1-b1
   lastGamerPlayA: '',        // dernier coup joueur au format Alg abrege
   lastComputerPlayC: '',     // dernier coup ordi au format complet Xa1-b1
   kingStateGamer: 0,
   kingStateComputer: 0,
   story: "",                 // story du jeu, a ne pas confondre avec historyGame...
   gamerTime: 0,              // en secondes
   computerTime: 0,           // en secondes
   totalGamerTime: 0,
   totalComputerTime: 0,
   takenByGamer: '',          // prises par joueur
   takenByComputer: '',       // prises par Ord
   queenCastleGamerOK: true,  // 4 boolens indiquent de quel cote quel roi a encore le droit de roquer
   kingCastleGamerOK: true,
   queenCastleComputerOK: true,
   kingCastleComputerOK: true,
   epComputer:"-",            // en passant Ordi
   epGamer: "-"               // en passant Joueur
};

let lSource, cSource;        // necessaire en variable globale pour moveread. 

/* Code colonne au format a-h. c = 0, cToString = "a" */
function cToString (c) {
   return String.fromCharCode(97+c);
}

/* renvoie l, c en fonction de la case en notation "e1" */
function stringToLC (str) {
   return [parseInt (str [1]) - 1, str.charCodeAt(0) - 'a'.charCodeAt(0)];
}

/* traduit booleen decrivant les possibilits de roque en string */
function castleToStr (info) {
   let str = "";
   if (info.gamerColor == -1) {
      if (info.kingCastleGamerOK) str += "K";
      if (info.queenCastleGamerOK) str += "Q";
      if (info.kingCastleComputerOK) str += "k";
      if (info.queenCastleComputerOK) str += "q";
   }
   else {
      if (info.kingCastleComputerOK) str += "K";
      if (info.queenCastleComputerOK) str += "Q";
      if (info.kingCastleGamerOK) str += "k";
      if (info.queenCastleGamerOK) str += "q";
   }
   return ((str == "") ? "-" : str) ;
}

/* traduit les possibilites de roque en booleens */
function strToCastle (str) {
   info.kingCastleGamerOK = info.kingCastleComputerOK = info.queenCastleGamerOK = info.queenCastleComputerOK = false;
   let whiteCanCastle = false;
   let blackCanCastle = false;
   
   for (let i = 0; i < str.length; i++) {
      switch (str [i]) {
      case "K": if (info.gamerColor == -1) info.kingCastleGamerOK = true;
                else info.kingCastleComputerOK = true;
                whiteCanCastle = true;
                break;
      case "k": if (info.gamerColor == 1) info.kingCastleGamerOK = true;
                else info.kingCastleComputerOK = true;
                blackCanCastle = true;
                break;
      case "Q": if (info.gamerColor == -1) info.queenCastleGamerOK = true;
                else info.queenCastleComputerOK = true;
                whiteCanCastle = true;
                break;
      case "q": if (info.gamerColor == 1) info.queenCastleGamerOK = true;
                else info.queenCastleComputerOK = true;
                blackCanCastle = true;
                break;
      default:
      }
   }
   return [whiteCanCastle, blackCanCastle];
}

/* Forsyth–Edwards Notation */
/* genere le jeu sous la forme d'une chaine de caracteres au format FEN */
/* le separateur est : "+" */
/* le roque est indiqué ainsi que "en passant" */
/* le compteur des 50 coups et le nb de coups */
function gameToFen (jeu, color, castle, ep, cpt50, noCoup) {
   let n, v;
   let sFen = "";
   for (let l = N-1; l >= 0; l -= 1) {
      for (let c = 0; c < N; c += 1) {
         v = jeu [l][c];
         if (v != 0) {
            sFen += ((v >= 0)? DICT [v].toLowerCase () : DICT [-v]);
         }
         else {
            for (n = 0; (c+n < N) && (jeu [l][c+n] == 0); n += 1);
            sFen += String.fromCharCode(48 + n);
            c += n-1;
         }
      }
      sFen += '/';
   }
   sFen = sFen.substring(0, sFen.length-1) + "+" + ((color == -1) ? "w" : "b") + "+";
   sFen += castle + "+" + ep + "+" + cpt50 + "+" + noCoup;
   return sFen;
}

/* Forsyth–Edwards Notation */
/* fenToGame traduit une chaine de caracteres au format FEN et renvoie l'objet jeu  */
/* 3kq3/8/8/8/8/3K4/+w+-- */
/* retourne le jeu et la valeur de la case "en passant" */
/* n'interprete pas la couleur recue qui est deja connue */ 
/* le roque est contenu dans la valeur du roi : KING ou CASTLEKING */
/* les separateurs acceptes entre les differents champs sont : + et Espace */ 
function fenToGame (fen, jeu) {
   let sign;
   let l = 7;
   let c = 0;
   let cChar;
   let bCastleW = false; 
   let bCastleB = false; 
   let fenNorm = fen.replaceAll (' ', '+');   
   let list = fenNorm.split ("+");
   let sFen = list [0];
   let ep = ((list [3] != null) ? list [3] : "-");
   if (list [1] != null) info.gamerColor = (list [1] == "w") ? -1 : 1; 
   if (list [2] != null) [bCastleW, bCastleB] = strToCastle (list [2]);

   for (let i = 0; i < sFen.length ; i += 1) {
      cChar = sFen [i];
      if (cChar == ' ' || cChar == '\t' || cChar == '\n') break;
      if (cChar == '/') continue; 
      if ((cChar >= '1') && (cChar <= '8')) {
         for (let k = 0; k < parseInt (cChar); k += 1) {
            jeu [l][c] = 0;
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
   return [jeu, ep];
}

/* vraie si il y a une piece egale a l1, c1 dans le symetrique par rapport a la colonne cDest */
function symetryV (sq64, l1, c1, cDest) { 
   let cSym = cDest + cDest - c1;
   return (cSym >= 0 && cSym < N) ? (sq64 [l1][c1] == sq64 [l1][cSym]): false;
}

/* vraie si il y a une piece egale a l1, c1 dans le symetrique par rapport a la ligne lDest */
function symetryH (sq64, l1, c1, lDest) { 
   let lSym = lDest + lDest - l1;
   return (lSym >= 0 && lSym < N) ? (sq64 [l1][c1] == sq64 [lSym][c1]): false;
}

/* transforme la specif algebriqe complete en abregee */
function abbrev (sq64, complete) {
   let [l1, c1] = stringToLC (complete.slice (1,3));
   let [l2, c2] = stringToLC (complete.slice (4,6));
   let cCharPiece = complete [0]; 
   let prise = complete [3];
   let v = sq64 [l1][c1];
   let promotion = "";
   let spec = "";                    // pour notation algebrique abrégée
   let abbr = "";
   // calcul de la notation abregee
   switch (Math.abs (v)) {                              
   case PAWN:
      cCharPiece = ""; 
      if ((prise == 'x') && (symetryV (sq64, l1, c1, c2))) // il y a deux pions symetrique prenant en c2 a partir de la ligne l1
         spec = cToString (c1);                    // on donne la colonne
      break;
   case KNIGHT:
      if (symetryV (sq64, l1, c1, c2)) spec = cToString (c1); //cavaliers symetrique par rapport à la col. dest
      else if (symetryH (sq64, l1, c1, l2)) spec = (l1+1).toString (); //cavaliers symetrique par rapport à la ligne dest
      break;
   case ROOK:
      if ((l1 == l2) && (c1 < c2)) {               // meme ligne, recherche a droite  
         for (let i = (c2 + 1); i < N; i++) {
            if (sq64 [l1][i] == v) {               // il y a une autre tour en position d'aller vers l2 c2
               spec = cToString (c1);              // Trouve. on donne la colonne
               break;
            }
            if (sq64 [l2][i] != 0) break;
         }
      }
      if ((l1 == l2) && (c1 > c2)) {               // meme ligne, recherche a droite  
         for (let i = (c2 - 1); i >= 0; i--) {
            if (sq64 [l1][i] == v) {               // il y a une autre tour en position d'aller vers l2 c2
               spec = cToString (c1);              // Trouve. On donne la colonne
               break;
            }
            if (sq64 [l2][i] != 0) break;
         }
      }
      if ((c1 == c2) && (l1 < l2)) {               // meme colonne, recherche en bas 
         for (let i = (l2 + 1); i < N; i++) {
            if (sq64 [i][c1] == v) {               // il y a une autre tour en position d'aller vers l2 c2
               spec = (l1+1).toString ();
               break;
            }
            if (sq64 [i][c2] != 0) break;
         }
      }
      if ((c1 == c2) && (l1 > l2)) {               // meme colonne, recherce en haut  
         for (let i = (l2 - 1); i >= 0; i--) {
            if (sq64 [i][c1] == v) {               // il y a une autre tour en position d'aller vers l2 c2
               spec = (l1+1).toString ();
               break;
            }
            if (sq64 [i][c2] != 0) break;
         }
      }
      break;
   case QUEEN:                                     // cas ou il y aurait 2 reines apres une promotion
      for (let l = 0; l < N; l++)
         for (let c = 0; c < N; c ++)
            if (l != l1 && c != c1 && sq64 [l][c] == v) spec = cToString (c1) + (l1+1).toString ();
      break;
   default: // BISHOP, KING
   }
   abbr = cCharPiece + spec + ((prise == 'x') ? "x" : "") + cToString (c2) + (l2+1).toString () + promotion;
   if (complete.includes ("e.p.")) abbr += " e.p."; 
   if (complete.includes ("=")) abbr += '=' + complete [7];
   return abbr;
}

/* vrai si le roi situe case l, c est echec au roi */
function LCkingInCheck (sq64, who, l, c) {
   let w, k;
   // roi adverse  menace.  Matche -KING et -CASTLEKING
   if (l < 7 && (-who * sq64 [l+1][c] >= KING)) return true;
   if (l > 0 && (-who * sq64 [l-1][c] >= KING)) return true;
   if (c < 7 && (-who * sq64 [l][c+1] >= KING)) return true;
   if (c > 0 && (-who * sq64 [l][c-1] >= KING)) return true;
   if (l < 7 && c < 7 && (-who * sq64 [l+1][c+1] >= KING)) return true;
   if (l < 7 && c > 0 && (-who * sq64 [l+1][c-1] >= KING)) return true;
   if (l > 0 && c < 7 && (-who * sq64 [l-1][c+1] >= KING || -who * sq64 [l-1][c+1] == PAWN)) return true;
   if (l > 0 && c > 0 && (-who * sq64 [l-1][c-1] >= KING || -who * sq64 [l-1][c-1] == PAWN)) return true;

   // cavalier menace
   if (l < 7 && c < 6 && (-who * sq64 [l+1][c+2] == KNIGHT)) return true;
   if (l < 7 && c > 1 && (-who * sq64 [l+1][c-2] == KNIGHT)) return true;
   if (l < 6 && c < 7 && (-who * sq64 [l+2][c+1] == KNIGHT)) return true;
   if (l < 6 && c > 0 && (-who * sq64 [l+2][c-1] == KNIGHT)) return true;
   if (l > 0 && c < 6 && (-who * sq64 [l-1][c+2] == KNIGHT)) return true;
   if (l > 0 && c > 1 && (-who * sq64 [l-1][c-2] == KNIGHT)) return true;
   if (l > 1 && c < 7 && (-who * sq64 [l-2][c+1] == KNIGHT)) return true;
   if (l > 1 && c > 0 && (-who * sq64 [l-2][c-1] == KNIGHT)) return true;

   // tour ou reine menace
   for (k = l+1; k < N; k++) {
      if ((w = -who * sq64 [k][c]) == ROOK || w == QUEEN) return true;
      if (w) break;
   }
   for (k = l-1; k >= 0; k--) {
      if ((w = -who * sq64 [k][c]) == ROOK || w == QUEEN) return true;
      if (w) break;
   }
   for (k = c+1; k < N; k++) {
      if ((w = -who * sq64 [l][k]) == ROOK || w == QUEEN) return true;
      if (w) break;
   }
   for (k = c-1; k >= 0; k--) {
      if ((w = -who * sq64 [l][k]) == ROOK || w == QUEEN) return true;
      if (w) break;
   }

   // fou ou reine menace
   for (k = 0; k < Math.min (7-l, 7-c); k++) { // vers haut droit
      if ((w = -who * sq64 [l+k+1][c+k+1]) == BISHOP || w == QUEEN) return true;
      if (w) break;
   }
   for (k = 0; k < Math.min (7-l, c); k++) {// vers haut gauche
      if ((w = -who * sq64 [l+k+1][c-k-1]) == BISHOP || w == QUEEN) return true;
      if (w) break;
   }
   for (k = 0; k < Math.min (l, 7-c); k++) { // vers bas droit
      if ((w = -who * sq64 [l-k-1][c+k+1]) == BISHOP || w == QUEEN) return true;
      if (w) break;
   }
   for (k = 0; k < Math.min (l, c); k++) { // vers bas gauche
      if ((w = -who * sq64 [l-k-1] [c-k-1]) == BISHOP || w == QUEEN) return true;
      if (w) break;
   }
   return false;
}

/* verifie que le deplacement choisi est valide */
/* renvoie CASTLING_GAMER ou EN_PASSANT ou vrai ou faux */
function verification (jeu, l, c, lDest, cDest, who) {
   let k;
   let sup;
   let v = jeu[l][c];
   let w = jeu[lDest][cDest];
   let cEp = -1; // pour en Passant
   let lEp = -1; // pour en Passant
   let base = (l == 0) ? 0 : 7;
   // pour roquer le roi ne doit pas etre en echec (etat = EXIST), il ne doit pas avoir bouge et les
   // cases intemédiaires ne doivet pas etre echec au roi
   // cote reine
   if (v * who >= KING && w * who == ROOK && l == base && c == 4 && lDest == base && cDest == 0 && 
      jeu[base][3] == 0 && jeu [base][2] == 0 && jeu [base][1] == 0 && 
      info.queenCastleGamerOK && info.kingStateGamer == KINGSTATE.EXIST &&
      ! LCkingInCheck (jeu, who, base, 4) && ! LCkingInCheck (jeu, who, base, 3) && 
      ! LCkingInCheck (jeu, who, base ,2))
      return CASTLING_GAMER;
   // cote Roi
   if (v * who >= KING && w * who == ROOK && l == base && c == 4 && lDest == base && cDest == 7 && 
      jeu[base][5] == 0 && jeu [base][6] == 0 && 
      info.kingCastleGamerOK && info.kingStateGamer == KINGSTATE.EXIST &&
      ! LCkingInCheck (jeu, who, base, 4) && ! LCkingInCheck (jeu, who, base, 5) && ! LCkingInCheck (jeu, who, base,6))
      return CASTLING_GAMER;

   if  (v*w > 0) return false;

   switch (Math.abs (v)) {
   case PAWN:
      if (info.epComputer != "-") { // prise en passant possible
         [lEp, cEp] = stringToLC (info.epComputer);
         if ((cEp == cDest) && (Math.abs (c - cDest) == 1) && (lDest == lEp) && ((lDest-l) == -who))
           return EN_PASSANT;
      }
      // alert (lEp);
      
      if (who == -1) {
         if ((l == 1) && ((lDest == 2) || (lDest == 3)) && (c == cDest) && (w == 0)) return true;
         if ((lDest ==  l+1) && (c == cDest) && (w == 0)) return true;
         if ((lDest == l+1) && (Math.abs (c - cDest) == 1) && (w*who < 0)) return true;
      }
      if (who == 1) {
         if ((l == 6) && ((lDest ==  5) || (lDest == 4)) && (c == cDest) && (w == 0)) return true;
         if ((lDest ==  l-1) && (c == cDest) && (w == 0)) return true;
         if ((lDest == l-1) && (Math.abs (c - cDest) == 1) && (w*who < 0)) return true;
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
/* il est nécessaire que la pièce puisse bouger d'au moins une case */
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
function secToHHMMSS (sec) {
   sec = parseInt (sec);
   let hours = Math.floor(sec / 3600).toString ().padStart (2, "0");
   let minutes = Math.floor((sec - (hours * 3600)) / 60).toString ().padStart (2, "0");
   let seconds = (sec - (hours * 3600) - (minutes * 60)).toString().padStart (2, "0");
   return hours + ':' + minutes + ':' + seconds;
}

/* affiche le chrono joueur */
function chronoGamer () {
   document.getElementById ('timePlayer').value = secToHHMMSS (info.gamerTime);
   info.gamerTime += 1;
   document.getElementById ('cumulTimePlayer').value = secToHHMMSS (info.totalGamerTime);
   info.totalGamerTime += 1;
}

/* affiche le chrono computer quand gere cote navigateur */
function chronoComputer () {
   document.getElementById ('timeComputer').value = secToHHMMSS (info.computerTime);
   info.computerTime += 1;
   document.getElementById ('cumulTimeComputer').value = secToHHMMSS (info.totalComputerTime);
   info.totalComputerTime += 1;
}

/* met a jour le niveau pour profondeur de la recherche */
function updateLevel () {
   document.getElementById ('niveauValeur').innerHTML = document.getElementById ('niveau').value;
   info.level = parseInt (document.getElementById ('niveau').value);
}

/* provoque une requete vers le serveur */
function pass () {
   fullDisplay ();
   clearInterval (gamerCount);
   document.getElementById ('FEN').value = gameToFen (jeu, -info.gamerColor, castleToStr (info), "-", info.cpt50, info.nb);
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
   document.getElementById ('test').value = ((testState) ? 'NORM' : 'TEST');
}

/* va un coup en arrière */
function back () {
   if (indexHistory > 0) {
      document.getElementById ('info').value = '';
      indexHistory -= 1;
      info.lastComputerPlayC = info.lastComputerPlayC = '';
      jeu = JSON.parse(historyGame [indexHistory]);
      fullDisplay ();
   }
}

/* repart un coup en avant */
function forward () {
   if (indexHistory < historyGame.length - 1) {
      indexHistory += 1;
      jeu = JSON.parse(historyGame [indexHistory]);
      fullDisplay ();
   }
}

/* met à jour le jeu suite à saisie d'un chaîne FEN */
function refresh () {
   [jeu, info.epComputer] = fenToGame (document.getElementById ('FEN').value, jeu);
   fullDisplay ();
}

/* retourne false si on arrete le jeu, TRUE si on continue */
/* affiche des infos fonction des codes reçus du serveur */
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

   if ((parseInt ((-info.gamerColor * responseServer.eval)) >= EVAL_THRESHOLD) ||
      (parseInt (responseServer.wdl) == 4))
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

   if (info.lastGamerPlayC == '') {                    // saisie de la case source
      [lSource, cSource] = stringToLC (nom);
      info.lastGamerPlayC = nom;                       // la case source
      elem.style.background = 'olive';
      elem.style.color = 'white';
      }
   else {                                             // saisie de la case destination
      [lDest, cDest] = stringToLC (nom);
      v = jeu [lSource][cSource];
      if ((v == -PAWN) && (lDest == 7)) jeu [lDest][cDest] = -QUEEN; // promotion
      else jeu [lDest][cDest] = v;
      jeu [lSource][cSource] = 0;
      fullDisplay ();
      info.lastGamerPlayC = '';
   }
}

/* saisie du deplacement par le joueur */
function moveRead (nom) {
   if (testState) return test (nom);
   let lDest, cDest;
   let v;
   let carPiece;
   let res;
   let prise;
   let elem = document.getElementById (nom);
   let pawnMove = false;

   if ((info.kingStateGamer == KINGSTATE.NOEXIST) || (info.kingStateGamer == KINGSTATE.IS_MATE))
      return;

   if (info.lastGamerPlayC == '') {                          // saisie de la case source
      [lSource, cSource] = stringToLC (nom);
      if (choiceIsOK (jeu, lSource, cSource, info.gamerColor)) {     
         info.lastGamerPlayC = nom;                          // la case source
         elem.style.background = 'olive';
         elem.style.color = 'white';
      }
      return;
   }

   [lDest, cDest] = stringToLC (nom);                       // saisie case destination
   if (lSource == lDest && cSource == cDest) {              // on annule tout
      info.lastGamerPlayC = '';
      display ();
      return;
   }
   res = verification (jeu, lSource, cSource, lDest, cDest, info.gamerColor);
   
   // en passant
   if ((Math.abs(jeu [lSource][cSource]) == PAWN) && (cDest == cSource) && (Math.abs (lDest - lSource) == 2)) // en Passant possible
      info.epGamer = nom [0] + (lSource + 1 - info.gamerColor); // genre : c6. On ne change pas la colonne. 
   else info.epGamer = "-";

   // limitation du roque si on touche au roi ou a la tour
   if (jeu [lSource][cSource] * info.gamerColor >= KING) { 
      info.queenCastleGamerOK = false;
      info.kingCastleGamerOK = false;
   }
   if (jeu [lSource][cSource] * info.gamerColor == ROOK) {
      if (cSource == 7) info.kingCastleGamerOK = false;
      else if (cSource == 0) info.queenCastleGamerOK = false;
   }
   
   // gestion du roque
   if (res == CASTLING_GAMER) {
      info.kingCastleGamerOK = false;
      info.queenCastleGamerOK = false;
      if (cDest == 0) {           // grand Roque
         jeu [lSource][0] = 0;
         jeu [lSource][2] = info.gamerColor * CASTLE_KING;
         jeu [lSource][3] = info.gamerColor * ROOK;
         jeu [lSource][4] = 0;
         info.lastGamerPlayA = info.lastGamerPlayC = "O-O-O";
         if ((info.story != '') && (info.gamerColor == -1)) info.story += '\n';
         if (info.gamerColor == -1) info.story += info.nb.toString ().padStart (3, ' ');
         info.story += " O-O-O";
      }
      else if (cDest == 7) {       // petit Roque
         jeu [lSource][4] = 0;
         jeu [lSource][5] = info.gamerColor * ROOK;
         jeu [lSource][6] = info.gamerColor * CASTLE_KING;
         jeu [lSource][7] = 0;
         info.lastGamerPlayA = info.lastGamerPlayC = "O-O";
         if ((info.story != '') && (info.gamerColor == -1)) info.story += '\n';
         if (info.gamerColor == -1) info.story += info.nb.toString ().padStart (3, ' ');
         info.story += "   O-O";
      }
   }

   // cas general
   if (res == true || res == EN_PASSANT) {
      v = Math.abs (jeu [lDest][cDest]);
      prise = (v != 0 || res == EN_PASSANT) ? 'x' : '-';
      v = Math.abs(jeu [lSource][cSource]);
      carPiece = DICT [v];
      info.lastGamerPlayC = carPiece + info.lastGamerPlayC + prise + nom; // source + destination
      if (res == EN_PASSANT) info.lastGamerPlayC += "e.p.";
      info.lastGamerPlayA = abbrev (jeu, info.lastGamerPlayC);
      if ((info.story != '') && (info.gamerColor == -1)) info.story += '\n';
      if (info.gamerColor == -1) info.story += info.nb.toString ().padStart (3, ' ') + info.lastGamerPlayA.padStart(6, ' ');
      else info.story += info.lastGamerPlayA.padStart (6, ' ');
      pawnMove = (Math.abs (jeu [lSource][cSource])) == PAWN;

      if (((jeu [lSource][cSource] == -PAWN) && (lDest == 7)) || 
         ((jeu [lSource][cSource] == PAWN) && (lDest == 0)))  {
         jeu [lDest][cDest] = info.gamerColor * QUEEN;   // promotion
         info.story += "=Q";
      }
      else jeu [lDest][cDest] = jeu [lSource][cSource];
      if (res == EN_PASSANT) jeu [lSource][cDest] = 0;   // bizarre mais vrai
      jeu [lSource][cSource] = 0;
   }

   if (res == CASTLING_GAMER || res == EN_PASSANT || res == true) {
      if (info.gamerColor == 1) info.nb += 1;           // computer a les blancs
      if (prise == 'x' || pawnMove) 
         info.cpt50 = 0;
      else info.cpt50 += 1; 
      fullDisplay ();
      clearInterval (gamerCount);
      if (info.cpt50 > CINQUANTE)
         alert ("règle des 50 coups atteinte");
      else serverRequest ();                             // on appelle le serveur
   }
}

/* envoie requete asynchrone XMLHttpRequest au serveur */
function serverRequest () {
   let response;
   let http = new XMLHttpRequest ();
   let url = MY_URL + "reqType=" + REQ_TYPE + "&level=" + info.level;
   let strFen = gameToFen (jeu, -info.gamerColor, castleToStr (info), info.epGamer, info.cpt50, info.nb);
   document.getElementById ('info').value = "Le serveur pense... !\n";
   document.getElementById ('FEN').value = strFen;
   url += "&fen=" + strFen;
   console.log ("\nurl: %s\n", url);
   info.computerTime = 0;
   computerCount = setInterval (chronoComputer,1000);        //la fonction est relancee
   
   http.onreadystatechange = function (event) {
   // XMLHttpRequest.DONE === 4
      if (this.readyState === XMLHttpRequest.DONE) {
         if (this.status === 200) {
            clearInterval (computerCount);
            response = this.responseText;
            console.log ("Réponse reçue: %s\n", response);
            responseServer = JSON.parse (response);
            [jeu, info.epComputer] = fenToGame (responseServer.fen, jeu);
            if ((info.story != '') && (info.gamerColor == 1)) info.story += '\n';
            info.story += (info.gamerColor == 1) ? info.nb.toString ().padStart (4, ' ') : "";
            info.story += responseServer.computePlayA.padStart(8, ' ');
            info.lastComputerPlayC = responseServer.computePlayC;
            new Audio ('beep.wav').play ();
            document.getElementById ('FEN').value = responseServer.fen;
            document.getElementById ('info').value = "A toi de jouer\n";
            if (info.gamerColor == -1) info.nb += 1; // computer a les noirs
            if (responseServer.computePlayC [0] == 'P' || responseServer.computePlayC [3] == 'x') 
               info.cpt50 = 0;
            else info.cpt50 += 1;
            fullDisplay ();
            info.lastGamerPlayC = '';
            info.gamerTime = 0;
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

/* affiche le jeu */
function fullDisplay () {
   analPieces ();
   infoUpdate (jeu);
   displayUpdate ();
   display ();
}

/* met a jour l'objet info a partir de l'objet jeu */
/* compte les pieces et MAJ l'etat du roi */
function infoUpdate (jeu) {
   let v;
   info.kingStateGamer = info.kingStateComputer = KINGSTATE.NOEXIST;
   info.nGamerPieces = info.nComputerPieces = 0;
   for (let l = 0; l < N; l += 1) {
      for (let c = 0; c < N; c += 1) {
         v = jeu[l][c] * info.gamerColor;
         if (v > 0) info.nGamerPieces += 1;
         else if (v < 0) info.nComputerPieces += 1;
         if (v == KING || v == CASTLE_KING) {
            info.kingStateComputer = KINGSTATE.EXIST;
         }
         if (v == -KING || v == -CASTLE_KING) {
            info.kingStateGamer = KINGSTATE.EXIST;
         }
      }
   }
}

/* liste les pieces prise de part et d'autre */
function analPieces () {
   // 8 pions, 2 cavaliers, 2 fous, 2 tours, 1 reine
   let pBlack = [0, 8, 2, 2, 2, 1]; // les noirs qui restent
   let pWhite = [0, 8, 2, 2, 2, 1]; // les blancs qui restent
   let v;
   for (let l = 0; l < N; l++) {
      for (let c = 0; c < N; c++) {
         v = jeu [l][c];
         if ((v > 0) && (v <= QUEEN)) pBlack [v] -= 1;
         if ((v < 0) && (v >= -QUEEN)) pWhite [-v] -= 1;
      }
   }
   info.takenByGamer = info.takenByComputer = '';
   for (let p = 1; p < 6; p++) {
      for (let i = 0; i < pBlack [p] ; i++) {
         if (info.gamerColor == -1) 
            info.takenByGamer += UNICODE [p] + ' ';
         else info.takenByComputer += UNICODE [p] + ' ';
      } 
   }
   for (let p = 1; p < 6; p++) {
      for (let i = 0; i < pWhite [p] ; i++) {
         if (info.gamerColor == -1) 
            info.takenByComputer += UNICODE [p] + ' ';
         else info.takenByGamer += UNICODE [p] + ' ';
      }
   }
}

/* met a jour la page */
function displayUpdate () {
   // info.noJoueur = info.noOrdi = 0;
   document.getElementById ('epComputer').value = info.epComputer;
   if (responseServer.gameFEN != null)
      document.getElementById ('FEN').value = responseServer.gameFEN;
   if (responseServer.dump != null)
      document.getElementById ('dump').innerHTML = responseServer.dump;
   if (responseServer.eval != null) {
      document.getElementById ('eval').value = parseInt (responseServer.eval);
   }
   if (responseServer.computePlayC != null)
      document.getElementById ('computePlay').value = responseServer.computePlayA;
   if (responseServer.openingName != null)
      document.getElementById ('message').value = responseServer.openingName.trim();
   if (responseServer.endName != null && responseServer.endName != '')
      document.getElementById ('message').value = responseServer.endName;

   document.getElementById ('takenByComputer').innerHTML = info.takenByComputer;

   /* Quand temps de reponse ordi geree cote ordi
   if (responseServer.time != null) {
      document.getElementById ('timeComputer').value = secToHHMMSS (parseFloat(responseServer.time));
      info.totalComputerTime += parseFloat (responseServer.time);
      document.getElementById ('cumulTimeComputer').value = secToHHMMSS (info.totalComputerTime);
   }
   */
   //b : black. Inversion car joueur
   document.getElementById ('votreCouleur').value = (info.gamerColor) ? "blanche" : "noire"; 
   document.getElementById ('noCoup').value = info.nb;
   document.getElementById ('cpt50').value = info.cpt50;
   document.getElementById ('epGamer').value = info.epGamer;               // dernier coup du joueur
   document.getElementById ('dernierJoueur').value = info.lastGamerPlayA;  // dernier coup du joueur
   document.getElementById ('nJoueur').value = info.nGamerPieces;          // nb de pieces
   document.getElementById ('nOrdi').value = info.nComputerPieces;         // nb de pieces
   document.getElementById ('historique').value = info.story;
   document.getElementById ('joueurRoqueRoi').value = (info.kingCastleGamerOK) ? "Oui" : "Non";
   document.getElementById ('joueurRoqueReine').value = (info.queenCastleGamerOK) ? "Oui" : "Non";
   document.getElementById ('ordiRoqueRoi').value = (info.kingCastleComputerOK) ? "Oui" : "Non";
   document.getElementById ('ordiRoqueReine').value = (info.queenCastleComputerOK) ? "Oui" : "Non";
   document.getElementById ('niveau').value = info.level;
   document.getElementById ('niveauValeur').innerHTML = document.getElementById ('niveau').value;
   document.getElementById ('takenByGamer').innerHTML = info.takenByGamer;
   info.takenByGamer = '';
}

/* en fonction du deplacement marque les case a colorier */
/* revoie vrai si la case l, c doit être marquee a colorier */
function marque (dep, l, c) {
   let l1, c1, l2, c2;
   [l1, c1] = stringToLC (dep.slice (1,3));
   [l2, c2] = stringToLC (dep.slice (4,6));
   if (l2 == l && c2 == c) return true;
   if (l1 == l && c1 == c) return true;
   let lMin = Math.min (l1, l2);
   let lMax = Math.max (l1, l2);
   let cMin = Math.min (c1, c2);
   let cMax = Math.max (c1, c2);
   // verticale/
   if ((c1 == c2) && (c1 == c)) {
      for (let k = lMin; k < lMax; k++)
         if (l == k) return true;
   }  
   // horizontale 
   if ((l1 == l2) && (l1 == l)) {
      for (let k = cMin; k < cMax; k++)
         if (c == k) return true;
   }
   // diagonale
   let delta = Math.abs (l2 - l1);
   if (delta != (cMax - cMin)) return false; // pas de diagonale
   
   if (((l1 < l2) && (c1 < c2)) || ((l1 > l2 && c1 > c2))) {
      for (let k = 0; k < delta; k++)
         if (l == lMin + k && c == cMin + k) return true; 
   }
   if (((l1 < l2) && (c1 > c2)) || ((l1 > l2 && c1 < c2))) {
      for (let k = 0; k < delta; k++)
         if (l == lMin + k  && c == cMax - k) return true; 
   }
   return false;
}

/* partie commune dans Display */
function commonDisplay (l, c) {
   //istr contient le nom de la case au format a1
   let istr = cToString (c) + (l+1).toString ();
   let v = jeu [l][c];
   let sBut = "<button class = '";
   if (info.lastComputerPlayC.indexOf ("O-O") != -1) {   // cas du roque
      alert ("Roque !");
   }
   if (marque (info.lastComputerPlayC, l, c)) sBut += "last";
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
         sJeu+= " <button class = 'deco'>"+cToString (c) + "</button>\n";
      }
      sJeu += "<button class = 'deco'>-</button>\n";
      for (l = N-1; l >=0; l -=1) {
         sJeu+= "<br/><button class = 'deco'>" + (l+1).toString () + "</button>\n";
         for (c = 0; c < N; c +=1)
	         sJeu += commonDisplay (l, c);
         sJeu+= "<button class = 'deco'>" + (l+1).toString () + "</button>\n";
      }
      sJeu+= "<br/>";
      sJeu+= "<button class = 'deco'>-</button>\n";
      for (c = 0; c < N; c += 1)
         sJeu += "<button class = 'deco'>" + cToString (c) + "</button>\n";
      sJeu += "<button class = 'deco'>-</button>\n";
   }
   else { // a l'envers
      for (c = N-1; c >= 0; c -= 1)
         sJeu+= " <button class = 'deco'>"+cToString (c) + "</button>";
      sJeu += "<button class = 'deco'>-</button>\n";
      for (l = 0; l < N; l += 1) {
         sJeu+= "<br/><button class = 'deco'>" + (l+1).toString () + "</button>";
         for (c = N-1; c >= 0; c -= 1)
	         sJeu += commonDisplay (l, c);
         sJeu+= "<button class = 'deco'>" + (l+1).toString () + "</button>\n";
      }
      sJeu+= ("<br/>");
      sJeu+= "<button class = 'deco'>-</button>\n";
      for (c = N-1; c >= 0; c -= 1)
         sJeu += "<button class = 'deco'>" + cToString (c) + "</button>\n";
      sJeu += "<button class = 'deco'>-</button>\n";
   }
   document.getElementById('milieu').innerHTML = sJeu;
}

/* programme principal */
function main () {
   for (let i = 0; i < N; i++) jeu [i] = [0,0,0,0,0,0,0,0];  // creer 8 cases pour les 8 lignes
   fenToGame (initFen, jeu);
   let rep = prompt ("Tu veux les blanc O/N ?",  "O");
   info.gamerColor = (rep[0] == "O" || rep[0] == "o") ? -1 : 1; // blancs -1, noirs 1
   if (info.gamerColor == 1) { // le joueur a les noirs. Le serveur joue...
      info.normal = !info.normal;
      serverRequest ();
   }
   else {
      gamerCount = setInterval (chronoGamer,1000);              // la fonction est relancee
   }
   fullDisplay ();
}
