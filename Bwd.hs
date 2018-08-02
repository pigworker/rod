{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Bwd where

import HalfZip

data Bwd x = B0 | Bwd x :< x deriving (Show, Eq, Functor, Foldable, Traversable)

infixl 3 :<

(+<) :: Bwd x -> Bwd x -> Bwd x
xz +< B0 = xz
xz +< (yz :< y) = (xz +< yz) :< y

infixl 3 +<

instance Applicative Bwd where
  pure x = pure x :< x
  (fz :< f) <*> (sz :< s) = (fz <*> sz) :< f s
  _ <*> _ = B0

instance HalfZip Bwd where
  halfZip B0 B0 = Just B0
  halfZip (xz :< x) (yz :< y) = (:<) <$> halfZip xz yz <*> Just (x, y)

instance Monoid (Bwd x) where
  mempty = B0
  mappend = (+<)

(<!) :: Bwd x -> Int -> x
(xz :< x) <! i = if i == 0 then x else xz <! (i - 1)

bwdBr :: String -> Bwd String -> String -> String
bwdBr l B0 r = ""
bwdBr l (sz :< s) r = l ++ foldMap (++ ",") sz ++ s ++ r

(<><) :: Bwd x -> [x] -> Bwd x
xz <>< [] = xz
xz <>< (x : xs) = (xz :< x) <>< xs

(<>>) :: Bwd x -> [x] -> [x]
B0 <>> xs = xs
(xz :< x) <>> xs = xz <>> (x : xs)

