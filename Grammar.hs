{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Grammar where

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Foldable

import Bwd
import Lex
import Tm
import BigArray

data Syntax = Syntax
  { grammars :: Arr Sort Grammar
  , keywords :: Set String
  , excluded :: SpatialCx -> (Sort, Int) -> Bool
  }

type Grammar = [(Bwd Scopex, [Grammaton Int])]

type Production = ( Sort
                  , Int   -- production number
                  )
type Parent =  ( Production
               , Int      -- position number
               )
type SpatialCx =  Bwd Parent

data ParEnv = ParEnv
  { syntax     :: Syntax
  , spatialCx  :: SpatialCx
  , boundVars  :: LEnv
  , leftRec    :: Bwd Sort
  }

data ParSta = ParSta
  { source :: [Token] -- what inputs have we?
  , metEnv :: MEnv    -- what's our metalexical environment?
  } deriving Show

newtype Parser x = Parser {parser
  :: ParEnv -> ParSta -> [(x, Bool {-advanced?-}, ParSta)]
  } deriving Monoid

type MEnv = [(String, SComp)]  -- metalexical environment
type LEnv = Bwd (String, Kind) -- lexical environment
data SComp = IdId String | ScId LEnv deriving Show
data Scopex = Sc String | Va String (Bwd Scopex) Sort
scopex :: MEnv
       -> Scopex              -- scope former
       -> LEnv
scopex env (Sc x) = case lookup x env of
  Just (ScId g) -> g
  _             -> B0
scopex env (Va x g k) = case lookup x env of
  Just (IdId y) -> B0 :< (y, fmap snd (foldMap (scopex env) g) :- k)
  _             -> B0

instance Monad Parser where
  return x = Parser $ \ _ sta -> [(x, False, sta)]
  Parser ps >>= k = Parser $ \ env sta -> do
    (s, b, sta) <- ps env sta
    let Parser pt = k s
    (t, c, sta) <- pt (if b then env{leftRec=B0} else env) sta
    return (t, b || c, sta)

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Functor Parser where fmap = (<*>) . pure

instance Alternative Parser where
  empty = mempty
  (<|>) = mappend

data PTree
  = (Sort, Int) ::: [(LEnv, PTree)]
  | Paren PTree
  | PV Int [PTree]
  | PM String (Maybe [Int])
  deriving Show

data Grammaton n
  = GBracket Bracket [Grammaton n]
  | GToken Token
  | GNonTerm n (Bwd Scopex) Sort (Maybe String)
  | GBId String
  | GMaySp
  | GMustSp Int
  deriving (Functor, Foldable, Traversable)

parsaton :: Maybe Production -> Grammaton Int -> Parser [(LEnv, PTree)]
parsaton p (GBracket b gs) = concat <$> pBracket b (traverse (parsaton Nothing) gs)
parsaton p (GToken t) = [] <$ pTok (guard . (t ==))
parsaton p (GNonTerm i ga s m) = (:[]) <$> pBind ga (pNonTerm ((,) <$> p <*> pure i) s m)
parsaton p (GBId x) = pId >>= \ y -> [] <$ pMeta x (IdId y)
parsaton p (GMustSp i) = pSpc >>= \ j -> if j >= i then pure [] else empty
parsaton p GMaySp = ([] <$ pSpc) <|> pure []

pTok :: (Token -> Maybe x) -> Parser x
pTok f = Parser $ \ env sta -> case source sta of
  t : ts | Just x <- f t -> return (x, True, sta{source=ts})
  _ -> []

pId :: Parser String
pId = Parser $ \ env sta -> case source sta of
  Id x : ts | Nothing <- findArr x (keywords (syntax env)) ->
    pure (x, True, sta{source = ts})
  _ -> empty

pMeta :: String -> SComp -> Parser ()
pMeta x m = Parser $ \ env sta -> return ((), False, sta {metEnv = (x, m) : metEnv sta})

pBind :: Bwd Scopex -> Parser x -> Parser (LEnv, x)
pBind ga p = Parser $ \ env sta -> do
  let de = foldMap (scopex (metEnv sta)) ga
  (x, b, sta) <- parser p (env{boundVars = boundVars env +< de}) sta
  return ((de, x), b, sta)

pBound :: String -> Parser (Maybe (Int, Kind))
pBound x = Parser $ \ env sta -> go sta 0 x (boundVars env) where
  go sta i x B0 = [(Nothing, False, sta)]
  go sta i x (bz :< (y, k))
    | x == y = [(Just (i, k), False, sta)]
    | otherwise = go sta (i + 1) x bz

pBracket :: Bracket -> Parser x -> Parser x
pBracket b p = Parser $ \ env sta -> case source sta of
  Bracket c ts : us | b == c -> do
    (x, _, sta) <- parser p
      (env{spatialCx = B0, leftRec = B0})
      (sta{source = ts})
    guard (null (source sta))
    return (x, True, sta{source = us})
  _ -> []

pSpc :: Parser Int
pSpc = pTok $ \ t -> case t of {Spc i -> Just i; _ -> Nothing}

pNonTerm :: Maybe Parent -> Sort -> Maybe String -> Parser PTree
pNonTerm p s m = pBracket Round (pNonTerm Nothing s m)
       <|> pVar s
       <|> pRec p s m

pVar :: Sort -> Parser PTree
pVar s = pId >>= \ x -> pBound x >>= \ r -> case r of
  Nothing -> pure (PM x Nothing)
  Just (i, k) | k == (B0 :- s) -> pure (PV i [])
              | otherwise -> empty

pRec :: Maybe Parent -> Sort -> Maybe String -> Parser PTree
pRec w s m = Parser $ \ env sta -> do
  cutOff (leftRec env) s (source sta)
  case findArr s (grammars (syntax env)) of
    Nothing -> []
    Just ps ->
      let sc = fromMaybe B0 ((spatialCx env :<) <$> w)
          go (j, (ga, p)) =
            if excluded (syntax env) sc (s, j) then [] else do
              (tss, b, sta) <- parser (traverse (parsaton (Just (s, j))) p)
                (env{leftRec = leftRec env :< s, spatialCx = sc})
                sta
              let me' = let me = metEnv sta in case m of
                              Nothing -> me
                              Just x  -> (x, ScId (foldMap (scopex me) ga)) : me
              return ((s, j) ::: concat tss, b, sta{metEnv = me'})
      in  foldMap go (zip [0..] ps)

cutOff :: Bwd Sort -> Sort -> [x] -> [()]
cutOff B0 x _ = [()]
cutOff (rz :< r) x ts
  | r == x = case ts of
    [] -> []
    _ : ts -> cutOff rz x ts
  | otherwise = cutOff rz x ts

parse :: Syntax -> Sort -> [Token] -> [PTree]
parse sy s ts = do
  (t, _, sta) <- parser (pNonTerm Nothing s Nothing)
    (ParEnv {syntax = sy, spatialCx = B0, boundVars = B0, leftRec = B0})
    (ParSta {metEnv = [], source = ts})
  guard (null (source sta))
  return t

-----------
{-
myGs :: Syntax
myGs = Syntax
  { grammars = single ("foo",
         [ [GToken (Num 0)]
         , [GNonTerm (B0 :. "foo"), GMaySp, GToken (Sym "&"), GMaySp, GNonTerm (B0 :. "foo")]
         ])
  , keywords = mempty
  , excluded = single (("foo",1), single ((1, ("foo", 1)), ()))
  }
-}

laG :: Syntax
laG = Syntax
  { grammars = single (S "term",
      [ (B0, [GNonTerm 0 B0 (S "term") Nothing, GMaySp, GNonTerm 1 B0 (S "term") Nothing])
      , (B0, [GToken (Sym "\\"), GMaySp, GBId "x", GMaySp, GToken (Sym "->"), GMaySp,
              GNonTerm 0 (B0 :< Va "x" B0 (S "term")) (S "term") Nothing])
      ])
  , keywords = mempty
  , excluded = ex
  } where
    ex (_ :< ((S "term", 0), 1)) (S "term", 0) = True -- applications in args must be bracketed
    ex (_ :< ((S "term", 0), 0)) (S "term", 1) = True -- lambdas in funs must be bracketed
    ex (_ :< ((S "term", 0), 0) :< ((S "term", 0), 1)) (S "term", 1) = True
       -- lambdas in args in funs must be bracketed
    ex _ _ = False
