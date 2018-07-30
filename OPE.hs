{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

module OPE where

import Control.Arrow

import Bwd

type OPE = Bwd Bool

(<:) :: OPE -> Bool -> OPE
B0 <: True = B0
bz <: b    = bz :< b

class Thin t where
  (<<) :: t -> OPE -> t
  (<?) :: OPE -> t -> Maybe t
  -- t << B0 = t
  -- th <? (t << th) = Just t

instance Thin Int where
  i << B0            = i
  i << (th :< False) = 1 + (i << th)
  i << (th :< True)  = if i == 0 then 0 else 1 + (i << th)
  
  B0            <? i = Just i
  (th :< False) <? i = if i == 0 then Nothing else th <? (i - 1)
  (th :< True)  <? i = if i == 0 then Just 0  else (1+) <$> (th <? i)

instance Thin OPE where
  th        << B0            = th
  B0        << ph            = ph
  th        << (ph :< False) = (th << ph) :< False
  (th :< a) << (ph :< True)  = (th << ph) :< a

  B0            <? ph = Just ph
  th            <? B0 = th <? (B0 :< True)
  (th :< True)  <? (ph :< b) = (<: b) <$> (th <? ph)
  (th :< False) <? (ph :< b) = if b then Nothing else th <? ph

pullback :: OPE -> OPE -> (OPE, (OPE, OPE))
pullback B0            ph            = (ph, (ph, B0))
pullback th            B0            = (th, (B0, th))
pullback (th :< True)  (ph :< True)  = ((:< True)  *** ((<: True)  *** (<: True))) (pullback th ph)
pullback (th :< True)  (ph :< False) = ((:< False) *** ((:< False) *** id))        (pullback th ph)
pullback (th :< False) (ph :< True)  = ((:< False) *** (id *** (:< False)))        (pullback th ph)
pullback (th :< False) (ph :< False) = ((:< False) *** id)                         (pullback th ph)

(?<) :: OPE -> Bwd x -> Bwd x
B0        ?< xz        = xz
(bz :< b) ?< (xz :< x) = (if b then (:< x) else id) (bz ?< xz)
