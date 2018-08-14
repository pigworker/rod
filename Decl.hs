module Decl where

import Tm
import Bwd

data Decl
  = DECLARE String Kind
  | RULE Tm (RuleSort, Tm) (Bwd Tm) (Bwd (Subgoal Tm))
  | SOLVE String Cx Tm Derivation
  deriving Show

data RuleSort = By | From deriving Show

data Subgoal x = Subgoal Cx (Bwd Tm) x deriving Show

type Derivation = (Tm, Command)

data Command
  = Query
  | Derive RuleSort Tm Response
  deriving Show

data Response
  = Bang
  | Subs (Bwd (Subgoal Derivation))
  deriving Show