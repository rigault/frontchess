#!/bin/bash
grep -E '(^function|/\*)' chess.js | sed 's/(\(.*\))/(\1)\n/g' | tr { ' '
