{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Par where

import Control.Applicative
import Control.Monad

import Bwd
import OPE
import Lex
import Tm
import BigArray
import Decl

newtype Parser x = Parser {parser
  :: ParEnv -> ParSta -> [(x, ParSta)]
  } deriving Monoid

data ParEnv = ParEnv
  { pSignature :: Signature
  , pScope     :: Bwd String
  , pKeywords  :: Set String
  }
data ParSta = ParSta
  { pSource :: [Token]
  , pMetas  :: Arr String Meta
  , pNamer  :: Int
  }

keywords :: Set String
keywords = foldMap singleton
  [ "declare"
  , "Type"
  , "Goal"
  , "Hypo"
  , "Rule"
  , "rule"
  , "by"
  , "from"
  , "when"
  , "solve"
  ]

instance Monad Parser where
  return x = Parser $ \ _ sta -> [(x, sta)]
  Parser ps >>= k = Parser $ \ env sta -> do
    (s, sta) <- ps env sta
    let Parser pt = k s
    (t, sta) <- pt env sta
    return (t, sta)
  fail _ = empty

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Functor Parser where fmap = (<*>) . pure

instance Alternative Parser where
  empty = mempty
  (<|>) = mappend

tokDecl :: Signature -> [Token] -> [(Decl, ParSta)]
tokDecl sg src = do
  (x, sta) <- parser pDecl
    (ParEnv {pSignature = sg, pScope = B0, pKeywords = keywords})
    (ParSta {pSource = src, pMetas = emptyArr, pNamer = 0})
  guard (null (pSource sta))
  return (x, sta)

pTry :: Parser x -> [Token] -> [x]
pTry p src = do
  (x, sta) <- parser p
    (ParEnv {pSignature = emptyArr, pScope = B0, pKeywords = keywords})
    (ParSta {pSource = src, pMetas = emptyArr, pNamer = 0})
  guard (null (pSource sta))
  return x

pTryS :: Parser x -> String -> [x]
pTryS p = pTry p . tokens

pTok :: (Token -> Maybe x) -> Parser x
pTok f = Parser $ \ env sta -> case pSource sta of
  t : ts | Just x <- f t -> return (x, sta{pSource=ts})
  _ -> []

pSym :: String -> Parser ()
pSym s = pTok (guard . (Sym s ==))

pKey :: String -> Parser ()
pKey s = pTok (guard . (Id s ==))

pEnv :: (ParEnv -> t) -> Parser t
pEnv f = Parser $ \ env sta -> [(f env, sta)]

pMeta :: String -> Parser (Meta ())
pMeta x = Parser $ \ env sta -> case findArr x (pMetas sta) of
  Just m   -> [(m, sta)]
  Nothing  -> [(m, sta{pMetas = insertArr (x, m) (pMetas sta)
                       ,pNamer = n + 1})] where
    n = pNamer sta
    m = Meta (n, ())

pId :: Parser String
pId = do
  ks <- pEnv pKeywords
  x <- pTok $ \ t -> case t of {Id x -> Just x; _ -> Nothing}
  guard $ not (x `inSet` ks)
  return x

pSpc :: Parser ()
pSpc = Parser $ \ env sta -> [((), sta{pSource = go (pSource sta)})] where
  go (Spc _ : ts) = go ts
  go ts = ts

pBracket :: Bracket -> Parser x -> Parser x
pBracket b p = Parser $ \ env sta -> case pSource sta of
  Bracket c ts : us | b == c -> do
    (x, sta) <- parser p env (sta{pSource = ts})
    guard (null (pSource sta))
    return (x, sta{pSource = us})
  _ -> []
  
pIn :: Bwd String -> Parser x -> Parser x
pIn de p = Parser $ \ env sta ->
  parser p (env{pScope = pScope env +< de}) sta

pDecl :: Parser Decl
pDecl
  =    DECLARE <$ pKey "declare" <* pSpc <*> pId <* pSpc <*> pKind <* pSpc
  <|>  RULE <$ pKey "rule" <*> pTm <* pSpc <*>
         ((,) <$> pRuleSort <* pSpc <*> pTm) <*
         pSpc <*>
         (id <$ pKey "when" <*> pSep pTm (pSym ",") <|> pure B0) <*
         pSpc <*>
         (pBracket Curly (pSep pSubgoal (pSym ";")) <|> pure B0) <*
         pSpc
  <|>  do
       pKey "solve"
       pSpc
       x <- pId
       pSpc
       ga <- pBracket Round pCx <|> pure C0
       pSpc
       g <- pIn (cxDom ga) pTm
       pSpc
       d <- pIn (cxDom ga) pDer
       pSpc
       return (SOLVE x ga g d)

pRuleSort :: Parser RuleSort
pRuleSort = By <$ pKey "by" <|> From <$ pKey "from"

pDer :: Parser Derivation
pDer = (,) <$ pSpc <*> pTm <* pSpc <*> pCom <* pSpc

pCom :: Parser Command
pCom = Query <$ pSym "?"
   <|> Derive <$> pRuleSort <* pSpc <*> pTm <* pSpc <*> pResp

pResp :: Parser Response
pResp = Bang <$ pSym "!"
    <|> Subs <$> (pBracket Curly (pSep pSubDir (pSym ";")) <|> pure B0)

pSubDir :: Parser (Subgoal Derivation)
pSubDir = do
  pSpc
  ga <- pBracket Round pCx <|> pure C0
  hz <- pIn (cxDom ga) (pSep (pTm <* pSpc <* pSym ",") pSpc)
  d  <- pIn (cxDom ga) pDer
  return (Subgoal ga hz d)
  
pSubgoal :: Parser (Subgoal Tm)
pSubgoal = do
  pSpc
  ga <- pBracket Round pCx <|> pure C0
  gz <- pIn (cxDom ga) (pSep pTm (pSym ","))
  case gz of
    B0 -> empty
    hz :< g -> pure (Subgoal ga hz g)

pKind :: Parser Kind
pKind = do
  pSpc
  ga <- pBracket Round pCx <|> pure C0
  pSpc
  (ga :-) <$> pIn (cxDom ga) pSort

pCx :: Parser Cx
pCx' :: Cx -> Parser Cx
pCx = pCx' C0 <|> pure C0 <* pSpc
pCx' ga = do pSpc
             xk <- pIn (cxDom ga) pCxE
             pSpc
             (pSym "," *> pSpc *> pCx' (ga :& xk)) <|> pure (ga :& xk) 
pCxE :: Parser (String, Kind)
pCxE = (,) <$> (pId <|> pure "") <* pSpc <*> pKind

pSort :: Parser Sort
pSort = P <$> pPrim
    <|> T <$> pTm

pPrim :: Parser Prim
pPrim = Type <$ pKey "Type"
    <|> Goal <$ pKey "Goal"
    <|> Hypo <$ pKey "Hypo"
    <|> Rule <$ pKey "Rule"

pTm :: Parser (Tm ())
pTm = do
  pSpc
  h <- pHd
  pSpc
  (h :$) <$> pBracket Round pSpine <|> case h of
    M m -> (m :?) <$> (pBracket Square pThin <|> pure oi)
    _   -> pure (h :$ B0)

pThin :: Parser OPE
pThin = do
  ga <- pEnv pScope
  de <- pSep pId (pSym ",")
  case mkOPE de ga of
    [th] -> pure th
    _ -> empty

pSep :: Parser x -> Parser () -> Parser (Bwd x)
pSep p s = pSpc *> ((p >>= \ x -> go (B0 :< x)) <|> pure B0) where
  go xz = pSpc *>
          ((do s; pSpc; x <- p; go (xz :< x)) <|>
           pure xz)

pSpine :: Parser (Bwd (Bi Tm))
pSpine = pSep (pBind pTm) (pSym ",")

pBind :: Parser x -> Parser (Bi x)
pBind p = do
  de <- pSep pId pSpc <* pSym "." <|> pure B0
  pSpc
  (de :.) <$> pIn de p

pHd :: Parser (Hd ())
pHd = do
  xz <- pEnv pScope
  sig <- pEnv pSignature
  x <- pId
  case deBr (x ==) xz of
    Just (i, _) -> pure (V i)
    Nothing -> do
      case findArr x sig of
        Just _ -> pure (C x)
        Nothing -> M <$> pMeta x