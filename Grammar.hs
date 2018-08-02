{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Grammar where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Maybe
import Data.Foldable

import Bwd
import Lex
import Tm
import BigArray

data PTree
  = Head ::: [(LEnv, PTree)]
  | Paren PTree
  | PV Int (Bwd (LEnv,PTree))
  | PM String (Maybe [Int])
  | PN Int
  | PS String
  | PK String
  deriving Show

newtype Parser x = Parser {parser
  :: ParEnv -> ParSta -> [(x, Bool {-advanced?-}, ParSta)]
  } deriving Monoid

data ParEnv = ParEnv
  { syntax     :: Syntax
  , boundVars  :: LEnv
  , leftRec    :: Bwd Sort
  }

data ParSta = ParSta
  { source :: [Token] -- what inputs have we?
  , metEnv :: MEnv    -- what's our metalexical environment?
  , outLEnv :: LEnv   -- what lexical environment are we building?
  } deriving Show

data Syntax = Syntax
  { grammars :: Arr Sort Grammar
  , keywords :: Set String
  , excluded :: Theseus -> Head -> Bool
  }

type Grammar = [Production ()]

data Production  n = Spacer :/ Production' n
  deriving (Show, Functor, Foldable, Traversable)
data Production' n = End | Grammaton n :\ Production n
  deriving  (Show, Functor, Foldable, Traversable)
infixr 4 :/
infixr 4 :\

data Spacer = Exactly Int | AtLeast Int | Sp deriving Show

data Grammaton n
  = GRec n (Bwd Scopex) Sort (Maybe String)
  | GPun String
  | GKey String
  | GBrk Bracket (Production ())
  | GOut (Bwd Scopex)
  | GBId String
  | GNum
  | GSym
  | GNam
  deriving (Show, Functor, Foldable, Traversable)

type Child = Int

type Head = ( Sort
            , Int   -- production number
            )
type Position =  ( Head
                 , Child
                 )
type Theseus =  Bwd Position

type MEnv = [(String, SComp)]  -- metalexical environment
type LEnv = Bwd (String, Kind) -- lexical environment
data SComp = IdId String | ScId LEnv deriving Show
data Scopex = Sc String | Va String (Bwd Scopex) Sort deriving Show
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
  fail _ = empty

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Functor Parser where fmap = (<*>) . pure

instance Alternative Parser where
  empty = mempty
  (<|>) = mappend

spacer :: Spacer -> Parser ()
spacer Sp = spacer (AtLeast 0)
spacer sp = Parser $ \ env sta -> case (sp, source sta) of
  (_        , [])         -> [((), False, sta)]
  (Exactly 0, Spc _ : ts) -> []
  (Exactly i, Newline : ts) -> []
  (AtLeast _, Newline : Spc _ : ts) -> [((), True, sta{source = ts})]
  (Exactly i, Spc j : ts) -> if j == i then [((), True, sta{source = ts})] else []
  (AtLeast i, Spc j : ts) -> if j >= i then [((), True, sta{source = ts})] else []
  (Exactly 0, ts)         -> [((), False, sta)]
  (AtLeast 0, ts)         -> [((), False, sta)]
  (AtLeast i, ts)         -> []

production :: Production Theseus -> Parser [(LEnv, PTree)]
production (sp :/ pr') = spacer sp *> production' pr'

production' :: Production' Theseus -> Parser [(LEnv, PTree)]
production' End = pure []
production' (gr :\ pr) = (++) <$> grammaton gr <*> production pr

grammaton :: Grammaton Theseus -> Parser [(LEnv, PTree)]
grammaton (GRec th ga s m) = (:[]) <$> pBind ga (pNonTerm th s m)
grammaton (GPun s)         = [] <$ pTok (guard . (Sym s ==))
grammaton (GKey s)         = [] <$ pTok (guard . (Id s ==))
grammaton (GBrk b pr)      = pBracket b (production (fmap (const B0) pr))
grammaton (GOut ga)        = [] <$ pOutLEnv ga
grammaton (GBId x)         = pId >>= \ y -> [] <$ pMeta x (IdId y)
grammaton  GNum            = (:[]) <$> ((,) B0 <$> (PN <$> pNum))
grammaton  GSym            =
  (:[]) <$> ((,) B0 <$> (PS <$> pTok (\ t -> case t of {Sym s -> Just s; _ -> Nothing})))
grammaton  GNam            =
  (:[]) <$> ((,) B0 <$> (PK <$> pId))

pTok :: (Token -> Maybe x) -> Parser x
pTok f = Parser $ \ env sta -> case source sta of
  t : ts | Just x <- f t -> return (x, True, sta{source=ts})
  _ -> []

pSym :: String -> Parser ()
pSym s = pTok (guard . (Sym s ==))

pId :: Parser String
pId = Parser $ \ env sta -> case source sta of
  Id x : ts | Nothing <- findArr x (keywords (syntax env)) ->
    pure (x, True, sta{source = ts})
  _ -> empty

pNum :: Parser Int
pNum = Parser $ \ env sta -> case source sta of
  Num x : ts ->
    pure (x, True, sta{source = ts})
  _ -> empty

pMeta :: String -> SComp -> Parser ()
pMeta x m = Parser $ \ env sta -> return ((), False, sta {metEnv = (x, m) : metEnv sta})

pOutLEnv :: Bwd Scopex -> Parser ()
pOutLEnv ga = Parser $ \ env sta ->
  let de = foldMap (scopex (metEnv sta)) ga
  in  return ((), False, sta{outLEnv = outLEnv sta +< de})

pBind :: Bwd Scopex -> Parser x -> Parser (LEnv, x)
pBind ga p = pScopex ga >>= \ de -> pLEnv de p

pScopex :: Bwd Scopex -> Parser LEnv
pScopex ga = Parser $ \ env sta ->
  let de = foldMap (scopex (metEnv sta)) ga
  in  return (de, False, sta)

pLEnv :: LEnv -> Parser x -> Parser (LEnv, x)
pLEnv de p = Parser $ \ env sta -> do
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
      (env{leftRec = B0})
      (sta{source = ts})
    guard (null (source sta))
    return (x, True, sta{source = us})
  _ -> []

pSpc :: Parser Int
pSpc = pTok $ \ t -> case t of {Spc i -> Just i; _ -> Nothing}

pOpSpc :: Parser ()
pOpSpc = (() <$ pSpc) <|> pure ()

pNonTerm :: Theseus -> Sort -> Maybe String -> Parser PTree
pNonTerm th s m
  =    pBracket Round (pNonTerm B0 s m)
  <|>  pRec th s m
  <|>  pVar s
  <|>  PM <$ pSym "?" <*> pId <*> (Just <$> pBracket Square deps <|> pure Nothing)
  where
    deps = many (pOpSpc *> var) <* pOpSpc
    var = pId >>= \ x -> pBound x >>= \ r -> case r of
      Nothing -> empty
      Just (i, _) -> pure i

pVar :: Sort -> Parser PTree
pVar s = pId >>= \ x -> pBound x >>= \ r -> case r of
    Nothing -> empty
    Just (i, kz :- s')
      | s' == s -> case kz of
          B0 -> pure (PV i B0)
          kz -> PV i <$> pBracket Round (go kz)
      | otherwise -> empty
  where
    go (B0 :< k) = (B0 :<) <$ pOpSpc <*> ki k <* pOpSpc
    go (kz :< k) = (:<) <$> go kz <* pOpSpc <* pSym "," <* pOpSpc <*> ki k <* pOpSpc
    ki (B0 :- s) = (,) B0 <$> pNonTerm B0 s Nothing
    ki (kz :- s) = bi kz >>= \ de -> pSym "." *> pOpSpc *> pLEnv de (pNonTerm B0 s Nothing)
    bi B0        = B0 <$ pOpSpc
    bi (kz :< k) = (:<) <$> bi kz <*> ((,) <$> pId <* pOpSpc <*> pure k)

pRec :: Theseus -> Sort -> Maybe String -> Parser PTree
pRec th s m = Parser $ \ env sta -> do
  cutOff (leftRec env) s (source sta)
  case findArr s (grammars (syntax env)) of
    Nothing -> []
    Just ps ->
      let ol = outLEnv sta
          me = metEnv sta
          next :: Head -> () -> State Int Theseus
          next h _ = get >>= \ i -> put (i + 1) >> return (th :< (h, i))
          go (j, pr) =
            if excluded (syntax env) th (s, j) then [] else do
              (ts, b, sta) <- parser
                (production (evalState (traverse (next (s, j)) pr) 0))
                (env{leftRec = leftRec env :< s})
                (sta{outLEnv = B0})
              let me' = let ol' = outLEnv sta in case m of
                              Nothing -> me
                              Just x  -> (x, ScId ol') : me
              return ((s, j) ::: ts, b, sta{outLEnv = ol, metEnv = me'})
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
  (t, _, sta) <- parser (pNonTerm B0 s Nothing)
    (ParEnv {syntax = sy, boundVars = B0, leftRec = B0})
    (ParSta {metEnv = [], source = ts, outLEnv = B0})
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
      [ Sp :/ GRec () B0 (S "term") Nothing :\ Sp :/ GRec () B0 (S "term") Nothing :\ Sp :/ End
      , Sp :/ GPun "\\" :\ Sp :/ GBId "x" :\ Sp :/ GPun "->" :\ Sp :/
              GRec () (B0 :< Va "x" B0 (S "term")) (S "term") Nothing :\ Sp :/ End
      ])
  , keywords = mempty
  , excluded = ex
  } where
    ex (_ :< ((S "term", 0), 1)) (S "term", 0) = True -- applications in args must be bracketed
    ex (_ :< ((S "term", 0), 0)) (S "term", 1) = True -- lambdas in funs must be bracketed
    ex (_ :< ((S "term", 0), 0) :< ((S "term", 0), 1)) (S "term", 1) = True
       -- lambdas in args in funs must be bracketed
    ex _ _ = False

grG = Syntax
  { grammars = fold
    [ single (S "spacer",
      [ Sp :/ GPun "<" :\ Exactly 0 :/ GNum :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GNum :\ Exactly 0 :/ GPun "+>" :\ Sp :/ End
      , Sp :/ End
      ])
    , single (S "production",
      [ Sp :/ GRec () B0 (S "spacer") Nothing :\
        Sp :/ GRec () B0 (S "production0") (Just "x") :\
        Sp :/ GOut (B0 :< Sc "x") :\ Sp :/ End
      ])
    , single (S "production0",
      [ Sp :/ GRec () B0 (S "grammaton") (Just "a") :\
        Sp :/ GRec () (B0 :< Sc "a") (S "production") (Just "b") :\
        Sp :/ GOut (B0 :< Sc "a" :< Sc "b") :\ Sp :/ End
      , Sp :/ End
      ])
    , single (S "grammaton",
      [ Sp :/ GPun "<" :\ Exactly 0 :/ GRec () B0 (S "scope") Nothing :\
        Exactly 0 :/ GNam :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GRec () B0 (S "scope") Nothing :\
        Exactly 0 :/ GNam :\ Exactly 0 :/ GPun "|" :\
        Exactly 0 :/ GBId "g" :\ Exactly 0 :/ GPun ">" :\
        Sp :/ GOut (B0 :< Va "g" B0 (S "scid")) :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GKey "id" :\ Exactly 0 :/ GPun "|" :\
        Exactly 0 :/ GBId "x" :\ Exactly 0 :/ GPun ">" :\
        Sp :/ GOut (B0 :< Va "x" B0 (S "idid")) :\ Sp :/ End
      , Sp :/ GBrk Round (Sp :/ GRec () B0 (S "production") (Just "a") :\ Sp :/ End) :\
        Sp :/ GOut (B0 :< Sc "a") :\ Sp :/ End
      , Sp :/ GBrk Square (Sp :/ GRec () B0 (S "production") (Just "a") :\ Sp :/ End) :\
        Sp :/ GOut (B0 :< Sc "a") :\ Sp :/ End
      , Sp :/ GBrk Curly (Sp :/ GRec () B0 (S "production") (Just "a") :\ Sp :/ End) :\
        Sp :/ GOut (B0 :< Sc "a") :\ Sp :/ End
      , Sp :/ GSym :\ AtLeast 1 :/ End
      , Sp :/ GNam :\ Sp :/ End
      , Sp :/ GPun "<|" :\ Exactly 0 :/ GRec () B0 (S "scope") Nothing :\
        Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GKey "num" :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GKey "sym" :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GKey "id" :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      ])
    , single (S "scope",
      [ Exactly 0 :/ GBrk Round (Sp :/ GRec () B0 (S "scopexz") Nothing :\
                                 Sp :/ GRec () B0 (S "scopex") Nothing :\ Sp :/ End) :\
        Exactly 0 :/ End
      , Exactly 0 :/ End
      ])
    , single (S "scopex",
      [ Sp :/ GRec () B0 (S "scid") Nothing :\ Sp :/ End
      , Sp :/ GRec () B0 (S "idid") Nothing :\ Sp :/ GRec () B0 (S "kind") Nothing :\ Sp :/ End
      ])
    , single (S "scopexz",
      [ Sp :/ GRec () B0 (S "scopexz") Nothing :\
        Sp :/ GRec () B0 (S "scopex") Nothing :\ Sp :/ GPun "," :\ Sp :/ End
      , Sp :/ End
      ])
    , single (S "kind",
      [ Sp :/ GRec () B0 (S "scope") Nothing :\ Exactly 0 :/ GNam :\ Sp :/ End
      ])
    , single (S "idid", [])
    , single (S "scid", [])
    ]
  , keywords = foldMap (single . flip (,) ()) ["id", "num", "sym"]
  , excluded = \ _ _ -> False
  }