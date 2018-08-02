{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, DeriveFunctor #-}

module Tm where

import Bwd
import OPE

newtype Sort = S String deriving (Eq, Ord)
instance Show Sort where
  show (S i) = i

data Kind = Scope :- Sort deriving (Eq)
type Scope = Bwd Kind
infix 2 :-
instance Show Kind where
  show (B0 :- i) = show i
  show (kz :- i) = "[" ++ foldMap show kz ++ "]" ++ show i

so :: String -> Kind
so i = B0 :- S i
(->>) :: Kind -> Kind -> Kind
s ->> (sz :- i) = B0 :< s +< sz :- i
infixr 3 ->>

data Bi x = Bwd String :. x deriving (Eq, Functor)
infix 1 :.


data Tm
  = Hd :$ Bwd (Bi Tm)
  | Meta :? OPE
  deriving Eq
infix 2 :$
infix 2 :?

data Hd = C String Kind | V Int deriving (Show, Eq)

type Meta = String

instance Thin Tm where
  (h@(C _ _) :$ tz) << th = h :$ (tz << th)
  (V i       :$ tz) << th = V (i << th) :$ (tz << th)
  (m :? ph)         << th = m :? (th << ph)
  th <? (h@(C _ _) :$ tz) = (h :$) <$> (th <? tz)
  th <? (V i :$ tz)       = (:$) <$> (V <$> (th <? i)) <*> (th <? tz)
  th <? (m :? ph)         = (m :?) <$> (th <? ph)

instance Thin t => Thin (Bi t) where
  (xz :. t) << th = xz :. (t << (th <|- xz))
  th <? (xz :. t) = (xz :.) <$> ((th <|- xz) <? t)

instance Thin t => Thin (Bwd t) where
  tz << th = fmap (<< th) tz
  th <? tz = traverse (th <?) tz

instance Show Tm where
  show t = go B0 t where
    go nz (C c _ :$ tz) = c ++ bwdBr "(" (fmap (bi nz) tz) ")"
    go nz (V i :$ tz)   = (nz <! i) ++ bwdBr "(" (fmap (bi nz) tz) ")"
    go nz (m :? th)     = m ++ bwdBr "[" (sel 0 th nz) "]"
    bi nz (xz :. t) = foldMap (++ ".") yz ++ go mz t where
      (mz, yz) = freshen nz xz
    sel i (OPE B0) nz = nz
    sel i th B0 = sel (i + 1) th (B0 :< show i)
    sel i (OPE (th :< b)) (nz :< n) = (if b then (:< n) else id) (sel i (OPE th) nz)

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


metaDep :: Meta -> Tm -> Bool
metaDep m (n :? _)  = m == n
metaDep m (h :$ tz) = any (\ (_ :. t) -> metaDep m t) tz
