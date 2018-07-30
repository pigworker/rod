{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, DeriveFunctor #-}

module Tm where

import Bwd
import OPE

data Sort = Tm deriving Eq
instance Show Sort where
  show Tm = "."

data Kind = Bwd Kind :- Sort deriving (Eq)
infix 2 :-
instance Show Kind where
  show (B0 :- i) = show i
  show (kz :- i) = "[" ++ foldMap show kz ++ "]" ++ show i

data Bi x = Bwd String :. x deriving (Eq, Functor)
infix 1 :.

data Tm
  = Hd :$ Bwd (Bi Tm)
  | String :? OPE
  deriving Eq
infix 2 :$
infix 2 :?

data Hd = C String Kind | V Int deriving (Show, Eq)

instance Thin Tm where
  (h@(C _ _) :$ tz) << th = h :$ fmap (<< th) tz
  (V i       :$ tz) << th = V (i << th) :$ fmap (<< th) tz
  (m :? ph)         << th = m :? (th << ph)
  th <? (h@(C _ _) :$ tz) = (h :$) <$> traverse (th <?) tz
  th <? (V i :$ tz)       = (:$) <$> (V <$> (th <? i)) <*> traverse (th <?) tz
  th <? (m :? ph)         = (m :?) <$> (th <? ph)

instance Thin t => Thin (Bi t) where
  (xz :. t) << th = xz :. (t << (th +< fmap (const True) xz))
  th <? (xz :. t) = (xz :.) <$> ((th +< fmap (const True) xz) <? t)

instance Show Tm where
  show t = go B0 t where
    go nz (C c _ :$ tz) = c ++ bwdBr "(" (fmap (bi nz) tz) ")"
    go nz (V i :$ tz)   = (nz <! i) ++ bwdBr "(" (fmap (bi nz) tz) ")"
    go nz (m :? th)     = m ++ bwdBr "[" (th ?< nz) "]"
    bi nz (xz :. t) = foldMap (++ ".") yz ++ go mz t where
      (mz, yz) = freshen nz xz

freshen :: Bwd String    -- nz distinct
        -> Bwd String    -- xz any old names
        -> ( Bwd String  -- nz +< yz distinct
           , Bwd String  -- yz the same length as xz
           )
freshen nz B0 = (nz, B0)
freshen nz (xz :< x) = (mz :< y, yz :< y) where
  (mz, yz) = freshen nz xz
  x' = (if null x then "_" else x)
  y = if any (x' ==) mz then next 0 else x'
  next i = if any (z ==) mz then next (i + 1) else z where
    z = x' ++ show i

stan :: [(String, Tm)] -> Tm -> Tm
stan sg (m :? th) = case lookup m sg of
  Just t  -> t << th
  Nothing -> m :? th
stan sg (h :$ tz) = h :$ fmap (fmap (stan sg)) tz