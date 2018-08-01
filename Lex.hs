{-# LANGUAGE PatternGuards #-}

module Lex where

import Data.Char

import Bwd

tokens :: String -> [Token]
tokens = findBrackets B0 . raw

data Token
  = Spc Int
  | Newline
  | Id String
  | Num Int
  | Sym String
  | Bracket Bracket [Token]
  | BadOpen Bracket [Token]
  | BadClose Bracket
  deriving Eq

instance Show Token where
  show (Spc n) = replicate n ' '
  show Newline = "\n"
  show (Id x)  = x
  show (Num n) = show n
  show (Sym s) = s
  show (Bracket b ts) = o ++ foldMap show ts ++ c where (o, c) = brackets b
  show (BadOpen b ts) = fst (brackets b) ++ foldMap show ts
  show (BadClose b) = snd (brackets b)

data Bracket = Round | Square | Curly deriving (Eq, Show)
brackets :: Bracket -> (String, String)
brackets Round  = ("(",")")
brackets Square = ("[","]")
brackets Curly  = ("{","}")

openers, closers :: [(Token, Bracket)]
openers = [(Sym "(", Round),(Sym "[", Square),(Sym "{", Curly)]
closers = [(Sym ")", Round),(Sym "]", Square),(Sym "}", Curly)]

raw :: String -> [Token]
raw "" = []
raw ('\n' : s) = newline True s
raw ('\r' : s) = newline False s
raw (c : s) | elem c " \t" = spaces 1 s
raw (c : s) | elem c solos = Sym [c] : raw s
raw (c : s) | isAlphaNum c = alphanum (B0 :< c) s
raw (c : s) = symbol (B0 :< c) s

solos :: String
solos = ",;()[]{}"

newline :: Bool -> String -> [Token]
newline b (c : s) | c == (if b then '\r' else '\n') = newline b s
newline b s = Newline : raw s

spaces :: Int -> String -> [Token]
spaces i (c : s) | elem c " \t" = spaces (i + 1) s
spaces i s = Spc i : raw s

alphanum :: Bwd Char -> String -> [Token]
alphanum cz (c : s) | isAlphaNum c = alphanum (cz :< c) s
alphanum cz s | all isDigit cz = Num (read (cz <>> [])) : raw s
              | otherwise = Id (cz <>> []) : raw s

symbol :: Bwd Char -> String -> [Token]
symbol cz (c : s) | not (or ([isSpace, isAlphaNum, (`elem` solos)] <*> [c]))
  = symbol (cz :< c) s
symbol cz s = Sym (cz <>> []) : raw s

findBrackets :: Bwd (Bracket, Bwd Token) -> [Token] -> [Token]
findBrackets B0 [] = []
findBrackets (bz :< (b, tz)) [] = findBrackets bz [BadOpen b (tz <>> [])]
findBrackets bz (t : ts) | Just b <- lookup t openers = findBrackets (bz :< (b, B0)) ts
findBrackets bz (t : ts) | Just c <- lookup t closers = case bz of
  bz' :< (b, tz) | b == c -> findBrackets bz' (Bracket b (tz <>> []) : ts)
  _ -> findBrackets bz (BadClose c : ts)
findBrackets (bz :< (b, tz)) (t : ts) = findBrackets (bz :< (b, tz :< t)) ts
findBrackets B0 (t : ts) = t : findBrackets B0 ts
