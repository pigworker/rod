{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, 
             DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Tm where

import Control.Applicative

import Bwd
import OPE
import BigArray
import HalfZip

data Sort
  = P Prim
  | T TM deriving (Show, Eq)
data Prim = Type | Goal | Hypo | Rule deriving (Show, Eq)

data Kind = Cx :- Sort deriving (Show, Eq)
type Signature = Arr String Kind

data Cx = C0 | Cx :& (String, Kind) deriving Show

data Tm k
  = Hd k :$ Bwd (Bi (Tm k))
  | Meta k :? OPE
  deriving (Show, Functor, Foldable, Traversable)
type TM = Tm Kind

data Bi x = Bwd String :. x
  deriving (Show, Functor, Foldable, Traversable)

data Hd k = C String | V Int | M (Meta k)
  deriving (Show, Eq, Functor, Foldable, Traversable)

newtype Meta k = Meta (Int, k)
  deriving (Functor, Foldable, Traversable)
type META = Meta Kind
instance Show (Meta k) where
  show (Meta (i, _)) = "?" ++ show i
instance Eq (Meta k) where
  Meta (i, _) == Meta (j, _) = i == j
instance Ord (Meta k) where
  compare (Meta (i, _)) (Meta (j, _)) = compare i j

infix 1 :.
infix 2 :$
infix 2 :?

metaK :: Meta Kind -> Kind
metaK (Meta (_, k)) = k

instance Eq (Tm k) where
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

instance Thin (Tm k) where
  (h :$ tz) << th = (h << th) :$ (tz << th)
  (m :? ph) << th = m :? (ph << th)
  th <? (h :$ tz) = (:$) <$> (th <? h) <*> (th <? tz)
  th <? (m :? ph) = (m :?) <$> (th <? ph)

instance Thin (Hd k) where
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
  , substitution :: Bwd (Bi TM)
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

spim :: Bwd (Bi TM) -> Morph
spim bz = Morph
  { passive      = oi <|^ bz
  , active       = oi <|- bz
  , thinning     = oi
  , substitution = bz
  }

class Morphic t where
  morph :: Morph -> t -> t

instance Morphic TM where
  morph m (V i :$ az) = case (passive m <? i, active m <? i) of
      (Just i, _) -> V (i << thinning m) :$ az'
      (_, Just j) ->
        let xz :. t = substitution m <! j
        in  morph (spim az') t
    where az' = morph m az
  morph m (h :$ az) = h :$ morph m az
  morph m (x :? th) = case passive m <? th of
    Just ph -> x :? (ph << thinning m)
    Nothing -> let (de :- t) = metaK x in M x :$ mkSpine de th m

-- pullbacks instead?
popMorph :: Morph -> (Morph, Either Int (Bi TM))
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

mkSpine :: Cx -> OPE -> Morph -> Bwd (Bi TM)
mkSpine C0 _ _ = B0
mkSpine ga'@(ga :& (_, k)) th m = case (popOPE th, popMorph m) of
  ((th, False), (m, _)) -> mkSpine ga' th m
  ((th, True),  (m, a)) -> mkSpine ga th m :< case a of
    Right b -> b
    Left  i -> eta k i

eta :: Kind -> Int -> Bi TM
eta (de :- _) i = xz :. (V (i << (oi <|^ xz)) :$ etaSpine 0 de) where
  xz = cxDom de
  etaSpine i C0 = B0
  etaSpine i (ga :& (_, k)) = etaSpine (i + 1) ga :< eta k i

instance Morphic t => Morphic (Bwd t) where
  morph m tz = fmap (morph m) tz

instance Morphic t => Morphic (Bi t) where
  morph m (xz :. t) = xz :. morph (wkMorph m xz) t

cxMorph :: Morph -> Cx -> (Cx, Morph)
cxMorph m C0             = (C0, m)
cxMorph m (ga :& (x, k)) = (ga' :& (x, morph m' k), wkMorph m (B0 :< ()))
  where (ga', m') = cxMorph m ga

instance Morphic Cx where
  morph m ga = fst (cxMorph m ga)

instance Morphic Kind where
  morph m (ga :- i) = ga' :- morph m' i where (ga', m') = cxMorph m ga

instance Morphic Sort where
  morph m (T t) = T (morph m t)
  morph m i     = i

cxKi :: Cx -> Int -> Kind
cxKi ga x = k << th where
  (k, th) = go ga x
  go (_ :& (_, k)) 0 = (k, oi <: False)
  go (ga :& _)     x = (k, th <: False) where (k, th) = go ga (x -1)

thCx :: OPE -> Cx -> Maybe Cx
thCx (OPE B0) ga' = pure ga'
thCx (OPE (bz :< True)) (ga' :& (x, k')) =
  (:&) <$> thCx (OPE bz) ga' <*> ((,) x <$> OPE bz <? k')
thCx (OPE (bz :< False)) (ga' :& _) = thCx (OPE bz) ga'

synKi :: OPE -> Kind -> Maybe Kind
synKi th (ga' :- i') = (:-) <$> thCx th ga' <*> (th <? i') where
