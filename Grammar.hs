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

data Production  n = Spacer :/ Production0 n
  deriving (Show, Functor, Foldable, Traversable)
data Production0 n = End | Grammaton n :\ Production n
  deriving  (Show, Functor, Foldable, Traversable)
infixr 4 :/
infixr 4 :\

data Spacer = Exactly Int | AtLeast Int | Sp deriving Show

data Grammaton n
  = GRec n (Bwd Scopex) Sort Bool
  | GPun String
  | GKey String
  | GBrk Bracket (Production ())
  | GOut (Bwd Scopex)
  | GBId
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

type MEnv = Bwd SComp  -- metalexical environment
type LEnv = Bwd (String, Kind) -- lexical environment
data SComp = IdId String | ScId LEnv deriving Show
data Scopex = Sc Int | Va Int (Bwd Scopex) Sort deriving Show
scopex :: MEnv
       -> Scopex              -- scope former
       -> LEnv
scopex env (Sc i) = case env <! i of
  ScId g -> g
  _      -> B0
scopex env (Va i g k) = case env <! i of
  IdId y -> B0 :< (y, fmap snd (foldMap (scopex env) g) :- k)
  _      -> B0

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

production' :: Production0 Theseus -> Parser [(LEnv, PTree)]
production' End = pure []
production' (gr :\ pr) = (++) <$> grammaton gr <*> production pr

grammaton :: Grammaton Theseus -> Parser [(LEnv, PTree)]
grammaton (GRec th ga s m) = (:[]) <$> pBind ga (pNonTerm th s m)
grammaton (GPun s)         = [] <$ pTok (guard . (Sym s ==))
grammaton (GKey s)         = [] <$ pTok (guard . (Id s ==))
grammaton (GBrk b pr)      = pBracket b (production (fmap (const B0) pr))
grammaton (GOut ga)        = [] <$ pOutLEnv ga
grammaton  GBId            = pId >>= \ y -> [] <$ pMeta (IdId y)
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

pMeta :: SComp -> Parser ()
pMeta m = Parser $ \ env sta -> return ((), False, sta {metEnv = metEnv sta :< m})

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

pNonTerm :: Theseus -> Sort -> Bool -> Parser PTree
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
    ki (B0 :- s) = (,) B0 <$> pNonTerm B0 s False
    ki (kz :- s) = bi kz >>= \ de -> pSym "." *> pOpSpc *> pLEnv de (pNonTerm B0 s False)
    bi B0        = B0 <$ pOpSpc
    bi (kz :< k) = (:<) <$> bi kz <*> ((,) <$> pId <* pOpSpc <*> pure k)

pRec :: Theseus -> Sort -> Bool -> Parser PTree
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
                              False -> me
                              True  -> me :< ScId ol'
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
  (t, _, sta) <- parser (pNonTerm B0 s False)
    (ParEnv {syntax = sy, boundVars = B0, leftRec = B0})
    (ParSta {metEnv = B0, source = ts, outLEnv = B0})
  guard (null (source sta))
  return t

grG = Syntax
  { grammars = fold
    [ single (S "Spacer",
      [ Sp :/ GPun "<" :\ Exactly 0 :/ GNum :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GNum :\ Exactly 0 :/ GPun "+>" :\ Sp :/ End
      , Sp :/ End
      ])
    , single (S "Production",
      [ Sp :/ GRec () B0 (S "Spacer") False :\
        Sp :/ GRec () B0 (S "Production0") True :\
        Sp :/ GOut (B0 :< Sc 0) :\ Sp :/ End
      ])
    , single (S "Production0",
      [ Sp :/ GRec () B0 (S "Grammaton") True :\
        Sp :/ GRec () (B0 :< Sc 0) (S "Production") True :\
        Sp :/ GOut (B0 :< Sc 1 :< Sc 0) :\ Sp :/ End
      , Sp :/ End
      ])
    , single (S "Grammaton",
      [ Sp :/ GPun "<" :\ Exactly 0 :/ GRec () B0 (S "Scope") False :\
        Exactly 0 :/ GNam :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GRec () B0 (S "Scope") False :\
        Exactly 0 :/ GNam :\ Exactly 0 :/ GPun "|" :\
        Exactly 0 :/ GBId :\ Exactly 0 :/ GPun ">" :\
        Sp :/ GOut (B0 :< Va 0 B0 (S "ScId")) :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GKey "Id" :\ Exactly 0 :/ GPun "|" :\
        Exactly 0 :/ GBId :\ Exactly 0 :/ GPun ">" :\
        Sp :/ GOut (B0 :< Va 0 B0 (S "IdId")) :\ Sp :/ End
      , Sp :/ GBrk Round (Sp :/ GRec () B0 (S "Production") True :\ Sp :/ End) :\
        Sp :/ GOut (B0 :< Sc 0) :\ Sp :/ End
      , Sp :/ GBrk Square (Sp :/ GRec () B0 (S "Production") True :\ Sp :/ End) :\
        Sp :/ GOut (B0 :< Sc 0) :\ Sp :/ End
      , Sp :/ GBrk Curly (Sp :/ GRec () B0 (S "Production") True :\ Sp :/ End) :\
        Sp :/ GOut (B0 :< Sc 0) :\ Sp :/ End
      , Sp :/ GSym :\ AtLeast 1 :/ End
      , Sp :/ GNam :\ Sp :/ End
      , Sp :/ GPun "<|" :\ Exactly 0 :/ GRec () B0 (S "Scope") False :\
        Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GKey "Num" :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GKey "Sym" :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      , Sp :/ GPun "<" :\ Exactly 0 :/ GKey "Id" :\ Exactly 0 :/ GPun ">" :\ Sp :/ End
      ])
    , single (S "Scope",
      [ Exactly 0 :/ GBrk Round (Sp :/ GRec () B0 (S "Scopexz") False :\
                                 Sp :/ GRec () B0 (S "Scopex") False :\ Sp :/ End) :\
        Exactly 0 :/ End
      , Exactly 0 :/ End
      ])
    , single (S "Scopex",
      [ Sp :/ GRec () B0 (S "ScId") False :\ Sp :/ End
      , Sp :/ GRec () B0 (S "IdId") False :\ Sp :/ GRec () B0 (S "Kind") False :\ Sp :/ End
      ])
    , single (S "Scopexz",
      [ Sp :/ GRec () B0 (S "Scopexz") False :\
        Sp :/ GRec () B0 (S "Scopex") False :\ Sp :/ GPun "," :\ Sp :/ End
      , Sp :/ End
      ])
    , single (S "Kind",
      [ Sp :/ GRec () B0 (S "Scope") False :\ Exactly 0 :/ GNam :\ Sp :/ End
      ])
    , single (S "IdId", [])
    , single (S "ScId", [])
    ]
  , keywords = foldMap (single . flip (,) ()) ["Id", "Num", "Sym"]
  , excluded = \ _ _ -> False
  }

mkSpacer :: PTree -> Maybe Spacer
mkSpacer ((S "Spacer", 0) ::: [(_, PN n)]) = pure (Exactly n)
mkSpacer ((S "Spacer", 1) ::: [(_, PN n)]) = pure (AtLeast n)
mkSpacer ((S "Spacer", 2) ::: []) = pure Sp
mkSpacer _ = Nothing

mkProduction :: PTree -> Maybe (Production ())
mkProduction ((S "Production", 0) ::: [(_, sp), (_, pr')]) =
  (:/) <$> mkSpacer sp <*> mkProduction0 pr'
mkProduction _ = Nothing

mkProduction0 :: PTree -> Maybe (Production0 ())
mkProduction0 ((S "Production0", 0) ::: [(_, gr), (_, pr)]) =
  (:\) <$> mkGrammaton gr <*> mkProduction pr
mkProduction0 ((S "Production0", 1) ::: []) = pure End
mkProduction0 _ = Nothing

mkGrammaton :: PTree -> Maybe (Grammaton ())
mkGrammaton ((S "Grammaton", 0) ::: [(_, sc), (_, nom)]) =
  GRec () <$> mkScope sc <*> mkSort nom <*> pure False
mkGrammaton ((S "Grammaton", 1) ::: [(_, sc), (_, nom)]) =
  GRec () <$> mkScope sc <*> mkSort nom <*> pure True
mkGrammaton ((S "Grammaton", 2) ::: _) =
  pure GBId
mkGrammaton ((S "Grammaton", 3) ::: [(_, pr)]) =
  GBrk Round <$> mkProduction pr
mkGrammaton ((S "Grammaton", 4) ::: [(_, pr)]) =
  GBrk Square <$> mkProduction pr
mkGrammaton ((S "Grammaton", 5) ::: [(_, pr)]) =
  GBrk Curly <$> mkProduction pr
mkGrammaton ((S "Grammaton", 6) ::: [(_, PS s)]) =
  pure (GPun s)
mkGrammaton ((S "Grammaton", 7) ::: [(_, PK s)]) =
  pure (GKey s)
mkGrammaton ((S "Grammaton", 8) ::: [(_, sc)]) =
  GOut <$> mkScope sc
mkGrammaton ((S "Grammaton", 9) ::: _) =
  pure GNum
mkGrammaton ((S "Grammaton", 10) ::: _) =
  pure GSym
mkGrammaton ((S "Grammaton", 11) ::: _) =
  pure GNam
mkGrammaton _ = Nothing

mkScope :: PTree -> Maybe (Bwd Scopex)
mkScope ((S "Scope", 0) ::: [(_, sxz), (_, sx)]) =
  (:<) <$> mkScopexz sxz <*> mkScopex sx
mkScope ((S "Scope", 1) ::: _) =
  pure B0
mkScope _ = Nothing

mkScopexz :: PTree -> Maybe (Bwd Scopex)
mkScopexz ((S "Scopexz", 0) ::: [(_, sxz), (_, sx)]) =
  (:<) <$> mkScopexz sxz <*> mkScopex sx
mkScopexz ((S "Scopexz", 1) ::: _) =
  pure B0
mkScopexz _ = Nothing

mkScopex :: PTree -> Maybe Scopex
mkScopex ((S "Scopex", 0) ::: [(_, PV i _)]) =
  pure (Sc i)
mkScopex ((S "Scopex", 1) ::: [(_, PV i _), (_, (S "Kind", 0) ::: [(_, sc), (_, s)])]) =
  Va i <$> mkScope sc <*> mkSort s
mkScopex _ = Nothing

mkSort :: PTree -> Maybe Sort
mkSort (PK s) = Just (S s)
mkSort _ = Nothing

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
      [ Sp :/ GRec () B0 (S "term") False :\ Sp :/ GRec () B0 (S "term") False :\ Sp :/ End
      , Sp :/ GPun "\\" :\ Sp :/ GBId :\ Sp :/ GPun "->" :\ Sp :/
              GRec () (B0 :< Va 0 B0 (S "term")) (S "term") False :\ Sp :/ End
      ])
  , keywords = mempty
  , excluded = ex
  } where
    ex (_ :< ((S "term", 0), 1)) (S "term", 0) = True -- applications in args must be bracketed
    ex (_ :< ((S "term", 0), 0)) (S "term", 1) = True -- lambdas in funs must be bracketed
    ex (_ :< ((S "term", 0), 0) :< ((S "term", 0), 1)) (S "term", 1) = True
       -- lambdas in args in funs must be bracketed
    ex _ _ = False
