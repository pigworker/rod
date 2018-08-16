{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Decl where

import Tm
import Bwd

data Decl
  = DECLARE String Kind
  | RULE (Tm ()) (RuleSort, Tm ()) (Bwd (Tm ())) (Bwd (Subgoal Tm ()))
  | SOLVE String Cx (Tm ()) (Derivation ())
  deriving Show

data RuleSort = By | From deriving Show

data Subgoal f k = Subgoal Cx (Bwd (Tm k)) (f k)
  deriving (Show, Functor, Foldable, Traversable)

data Derivation k = Tm k ::: Command k
  deriving (Show, Functor, Foldable, Traversable)

data Command k
  = Query
  | Derive RuleSort (Tm k) (Response k)
  deriving (Show, Functor, Foldable, Traversable)

data Response k
  = Bang
  | Subs (Bwd (Subgoal Derivation k))
  deriving (Show, Functor, Foldable, Traversable)
  