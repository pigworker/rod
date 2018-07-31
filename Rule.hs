{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Rule where

import Control.Monad

import Data.List
import Data.Function

import Bwd
import OPE
import Tm
import Unify

data RuleF x = Rule
  { parametas   :: [(Meta, Kind)]
  , ruleHead    :: x
  , needGiven   :: [x]
  , subproblems :: [ProblemF x]
  } deriving (Show, Functor, Foldable, Traversable)
type Rule = RuleF Tm

data ProblemF x = Problem
  { universals  :: Bwd (String, Kind)
  , probGivens  :: Bwd x
  , probRoot    :: Meta
  , probShow    :: x
  } deriving (Show, Functor, Foldable, Traversable)
type Problem = ProblemF Tm

instance Thin x => Thin (RuleF x) where
  ts << th = fmap (<< th) ts
  th <? ts = traverse (th <?) ts
instance Stan x => Stan (RuleF x) where
  stan = fmap . stan

instance Thin x => Thin (ProblemF x) where
  ts << th = fmap (<< th) ts
  th <? ts = traverse (th <?) ts
instance Stan x => Stan (ProblemF x) where
  stan = fmap . stan

metaFresh :: Meta -> Rule -> Rule
metaFresh root (Rule mz h hs ps) = Rule mz' h' hs' ps' where
  mz' = [(root ++ "-" ++ m, k) | (m, k) <- mz]
  sg  = Stanner (sortBy (compare `on` fst)
          [(m, (root ++ "-" ++ m) :? oi) | (m, k) <- mz])
  h'  = stan sg h
  hs' = stan sg hs
  ps' = [stan sg p {probRoot = root ++ "-" ++ probRoot p} | p <- ps]

refine :: Problem            -- to solve
       -> Rule               -- rule to use
       -> [Tm]               -- the givens to be eliminated
       -> Maybe [Problem]    -- resulting subproblems

refine (Problem xz gz m g) r gs = case metaFresh m r of
  Rule mz h hs ps -> do
    sg <- unify (g : gs) (h : hs)
    guard $ all (`elem` gz) (stan sg gs)
    return [p {universals = xz +< universals p, probGivens = gz +< probGivens p}
           | p <- stan sg ps]
  
assumption :: Problem -> Maybe Stanner
assumption (Problem xz hz m g) = case nub (foldMap (foldMap pure . unify g) hz) of
  [sg] -> Just sg
  _    -> Nothing


--------

cAND :: Tm -> Tm -> Tm
cAND a b = C "AND" (tm ->> tm ->> tm) :$ B0 :< (B0 :. a) :< (B0 :. b)

rANDi :: Rule
rANDi = Rule
  { parametas    = [("A", tm), ("B", tm)]
  , ruleHead     = cAND ("A" :? oi) ("B" :? oi)
  , needGiven    = []
  , subproblems  = [ Problem B0 B0 "a" ("A" :? oi)
                   , Problem B0 B0 "b" ("B" :? oi)
                   ]
  }

rANDe :: Rule
rANDe = Rule
  { parametas    = [("A", tm), ("B", tm), ("P", tm)]
  , ruleHead     = ("P" :? oi)
  , needGiven    = [cAND ("A" :? oi) ("B" :? oi)]
  , subproblems  = [ Problem B0 (B0 :< ("A" :? oi) :< ("B" :? oi)) "p" ("P" :? oi)
                   ]
  }

cP = C "P" tm :$ B0
cQ = C "Q" tm :$ B0

myProb0 = Problem B0 B0 "?" (cAND cP cQ)
myProb1 = Problem B0 (B0 :< (cAND cP cQ)) "?" (cAND cQ cP)
