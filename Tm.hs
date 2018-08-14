{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, DeriveFunctor #-}

module Tm where

import Control.Applicative

import Bwd
import OPE
import BigArray
import HalfZip

{-
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
-}

data Sort = P Prim
          | T Tm deriving (Show, Eq)
data Prim = Type | Goal | Hypo | Rule deriving (Show, Eq)
data Kind = Cx :- Sort deriving (Show, Eq)
data Cx = C0 | Cx :& (String, Kind) deriving Show
data Tm = Hd :$ Bwd (Bi Tm)
        | Meta :? OPE
        deriving Show
data Bi x = Bwd String :. x deriving (Show, Functor)
data Hd = C String | V Int | M Meta deriving (Show, Eq)
newtype Meta = Meta Int deriving (Eq, Ord)
instance Show Meta where
  show (Meta i) = "?" ++ show i

infix 1 :.
infix 2 :$
infix 2 :?

instance Eq Tm where
  (f :$ az) == (g :$ bz) = f == g && az == bz
  (m :? th) == (n :? ph) = m == n && th == ph
  _ == _ = False

instance Eq t => Eq (Bi t) where
  (xz :. s) == (yz :. t) = case halfZip xz yz of
    Nothing -> False
    Just _ -> s == t

instance Eq Cx where
  C0 == C0 = True
  (ga :& (_, k)) == (de :& (_, l)) = ga == de && k == l
  _ == _ = False

(<&) :: OPE -> Cx -> OPE
th <& C0 = th
th <& (ga :& _) = (th <& ga) <: True

(<^) :: OPE -> Cx -> OPE
th <^ C0 = th
th <^ (ga :& _) = (th <& ga) <: False

cxDom :: Cx -> Bwd String
cxDom C0 = B0
cxDom (ga :& (x, _)) = cxDom ga :< x

cxCat :: Cx -> Cx -> Cx
cxCat ga C0 = ga
cxCat ga (de :& xk) = cxCat ga de :& xk

instance Thin Sort where
  P p << th = P p
  T t << th = T (t << th)
  th <? P p = pure (P p)
  th <? T t = T <$> (th <? t)

instance Thin Kind where
  (ga :- s) << th = (ga << th) :- (s << (th <& ga))
  th <? (ga :- s) = (:-) <$> (th <? ga) <*> ((th <& ga) <? s)

instance Thin Cx where
  C0 << th = C0
  (ga :& (x, k)) << th = (ga << th) :& (x, k << (th <& ga))
  th <? C0 = pure C0
  th <? (ga :& (x, k)) =
    (:&) <$> (th <? ga) <*> ((,) x <$> ((th <& ga) <? k))

instance Thin Tm where
  (h :$ tz) << th = (h << th) :$ (tz << th)
  (m :? ph) << th = m :? (ph << th)
  th <? (h :$ tz) = (:$) <$> (th <? h) <*> (th <? tz)
  th <? (m :? ph) = (m :?) <$> (th <? ph)

instance Thin Hd where
  C c << th = C c
  V i << th = V (i << th)
  M m << th = M m
  th <? C c = pure (C c)
  th <? V i = V <$> (th <? i)
  th <? M m = pure (M m)

instance Thin t => Thin (Bi t) where
  (xz :. t) << th = xz :. (t << (th <|- xz))
  th <? (xz :. t) = (xz :.) <$> ((th <|- xz) <? t)

mkOPE :: Eq x => Bwd x -> Bwd x -> [OPE]
mkOPE B0 B0 = [oi]
mkOPE _  B0 = []
mkOPE xz (yz :< y) =
  (case xz of {xz :< x | x == y -> (<: True) <$> mkOPE xz yz; _ -> []}) <|>
  (<: False) <$> mkOPE xz yz

data Morph = Morph
  { passive      :: OPE
  , active       :: OPE -- passive and active must cover
  , thinning     :: OPE
  , substitution :: Bwd (Bi Tm)
  }

wkMorph :: Morph -> Bwd x -> Morph
wkMorph (Morph
  { passive      = pa
  , active       = ac
  , thinning     = th
  , substitution = su
  }) de = Morph
  { passive      = pa <|- de
  , active       = ac <|^ de
  , thinning     = th <|- de
  , substitution = fmap (<< (oi <|^ de)) su
  }

spim :: Bwd (Bi Tm) -> Morph
spim bz = Morph
  { passive      = oi <|^ bz
  , active       = oi <|- bz
  , thinning     = oi
  , substitution = bz
  }

class Morphic t where
  morph :: Arr Meta Kind -> Morph -> t -> t

instance Morphic Tm where
  morph mka m (V i :$ az) = case (passive m <? i, active m <? i) of
      (Just i, _) -> V (i << thinning m) :$ az'
      (_, Just j) ->
        let xz :. t = substitution m <! j
        in  morph mka (spim az') t
    where az' = morph mka m az
  morph mka m (h :$ az) = h :$ morph mka m az
  morph mka m (x :? th) = case passive m <? th of
    Just ph -> x :? (ph << thinning m)
    Nothing -> case findArr x mka of
      Nothing -> error "unkind metavar"
      Just (de :- t) -> M x :$ mkSpine de th m

-- pullbacks instead?
popMorph :: Morph -> (Morph, Either Int (Bi Tm))
popMorph (Morph {passive = pa, active = ac, thinning = th, substitution = sz}) =
  case (popOPE pa, popOPE ac) of
    ((pa, True), (ac, _)) -> (Morph
      { passive      = pa
      , active       = ac
      , thinning     = (oi <: False) << th
      , substitution = sz
      }, Left (0 << th))
    ((pa, False), (ac, True)) -> let sz' :< s = sz in (Morph
      { passive = pa
      , active  = ac
      , thinning = th
      , substitution = sz
      }, Right s)

mkSpine :: Cx -> OPE -> Morph -> Bwd (Bi Tm)
mkSpine C0 _ _ = B0
mkSpine ga'@(ga :& (_, k)) th m = case (popOPE th, popMorph m) of
  ((th, False), (m, _)) -> mkSpine ga' th m
  ((th, True),  (m, a)) -> mkSpine ga th m :< case a of
    Right b -> b
    Left  i -> eta k i

eta :: Kind -> Int -> Bi Tm
eta (de :- _) i = xz :. (V (i << (oi <|^ xz)) :$ etaSpine 0 de) where
  xz = cxDom de
  etaSpine i C0 = B0
  etaSpine i (ga :& (_, k)) = etaSpine (i + 1) ga :< eta k i

instance Morphic t => Morphic (Bwd t) where
  morph mka m tz = fmap (morph mka m) tz

instance Morphic t => Morphic (Bi t) where
  morph mka m (xz :. t) = xz :. morph mka (wkMorph m xz) t

cxMorph :: Arr Meta Kind -> Morph -> Cx -> (Cx, Morph)
cxMorph mka m C0             = (C0, m)
cxMorph mka m (ga :& (x, k)) = (ga' :& (x, morph mka m' k), wkMorph m (B0 :< ()))
  where (ga', m') = cxMorph mka m ga

instance Morphic Cx where
  morph mka m ga = fst (cxMorph mka m ga)

instance Morphic Kind where
  morph mka m (ga :- i) = ga' :- morph mka m' i where (ga', m') = cxMorph mka m ga

instance Morphic Sort where
  morph mka m (T t) = T (morph mka m t)
  morph mka m i     = i

cxKi :: Cx -> Int -> Kind
cxKi ga x = k << th where
  (k, th) = go ga x
  go (_ :& (_, k)) 0 = (k, oi <: False)
  go (ga :& _)     x = (k, th <: False) where (k, th) = go ga (x -1)
