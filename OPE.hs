{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

module OPE where

import Control.Arrow

import Bwd

newtype OPE = OPE {ope :: Bwd Bool}

instance Show OPE where
  show (OPE B0)        = "-"
  show (OPE (th :< b)) = show (OPE th) ++ (if b then "-" else ".")

instance Eq OPE where
  OPE B0 == OPE ph = all id ph
  OPE th == OPE B0 = all id th
  OPE (th :< a) == OPE (ph :< b) = (a == b) && OPE th == OPE ph

(<:) :: OPE -> Bool -> OPE
OPE B0 <: True = OPE B0
OPE bz <: b    = OPE (bz :< b)

class Thin t where
  (<<) :: t -> OPE -> t
  (<?) :: OPE -> t -> Maybe t
  -- t << B0 = t
  -- th <? (t << th) = Just t

oi :: OPE
oi = OPE B0

instance Thin Int where
  i << OPE B0            = i
  i << OPE (th :< False) = 1 + (i << OPE th)
  i << OPE (th :< True)  = if i == 0 then 0 else 1 + (i << OPE th)
  
  OPE B0            <? i = Just i
  OPE (th :< False) <? i = if i == 0 then Nothing else OPE th <? (i - 1)
  OPE (th :< True)  <? i = if i == 0 then Just 0  else (1+) <$> (OPE th <? i)

instance Thin OPE where
  th            << OPE B0            = th
  OPE B0        << ph                = ph
  th            << OPE (ph :< False) = (th << OPE ph) <: False
  OPE (th :< a) << OPE (ph :< True)  = (OPE th << OPE ph) <: a

  OPE B0            <? ph            = Just ph
  th                <? OPE B0        = th <? OPE (B0 :< True)
  OPE (th :< True)  <? OPE (ph :< b) = (<: b) <$> (OPE th <? OPE ph)
  OPE (th :< False) <? OPE (ph :< b) = if b then Nothing else OPE th <? OPE ph

pullback :: OPE       -- th'
         -> OPE       -- ph'
         -> ( OPE     -- ps
            , ( OPE   -- th s.t. th << th' = ps
              , OPE   -- ph s.t. ph << ph' = ps
            ) )
pullback (OPE B0)      ph            = (ph, (ph, oi))
pullback th            (OPE B0)      = (th, (oi, th))
pullback (OPE (th :< True))  (OPE (ph :< True))  =
  ((<: True)  *** ((<: True)  *** (<: True))) (pullback (OPE th) (OPE ph))
pullback (OPE (th :< True))  (OPE (ph :< False)) =
  ((<: False) *** ((<: False) *** id))        (pullback (OPE th) (OPE ph))
pullback (OPE (th :< False)) (OPE (ph :< True))  =
  ((<: False) *** (id *** (<: False)))        (pullback (OPE th) (OPE ph))
pullback (OPE (th :< False)) (OPE (ph :< False)) =
  ((<: False) *** id)                         (pullback (OPE th) (OPE ph))

(?<) :: OPE -> Bwd x -> Bwd x
OPE B0        ?< xz        = xz
OPE (th :< b) ?< (xz :< x) = (if b then (:< x) else id) (OPE th ?< xz)

(<|-) :: OPE -> Bwd x -> OPE
th <|- xz = foldl (const . (<: True)) th xz
