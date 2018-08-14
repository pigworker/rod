module Chk where

import Data.Maybe
import Control.Monad
import Control.Applicative

import HalfZip
import Bwd
import OPE
import BigArray
import Lex
import Decl
import Par
import Tm

type Postponed = (Meta, (Cx, Sort, Bwd (Bi Tm)))

type Rule = (Tm, RuleSort, Tm, Bwd Tm, Bwd (Subgoal Tm), Arr Meta Kind)

data RodSta = RodSta
  { rSignature :: Signature
  , rRules :: Bwd Rule
  } deriving Show

initSta :: RodSta
initSta = RodSta
  { rSignature = emptyArr
  , rRules = B0
  }

newtype Chk x = Chk {chk
  :: RodSta          -- what we know so far
  -> Arr Meta Kind   -- what we have inferred, so far
  -> Cx              -- bound vars we're under
  -> Maybe           -- it might go wrong
   ( x
   , Arr Meta Kind   -- what we have now inferred
   , [Postponed]     -- what we wish we knew
   )}

instance Monad Chk where
  return x = Chk $ \ rod mka ga -> return (x, mka, [])
  Chk ca >>= k = Chk $ \ rod mka ga -> do
    (a, mka, qs0) <- ca rod mka ga
    (b, mka, qs1) <- chk (k a) rod mka ga
    (mka, qs2) <- stabilize rod mka (qs0 ++ qs1)
    return (b, mka, qs2)
  fail s = Chk $ \ _ _ _ -> fail s

stabilize
  :: RodSta          -- what we know so far
  -> Arr Meta Kind   -- what we have inferred, so far
  -> [Postponed]     -- bound vars we're under
  -> Maybe           -- it might go wrong
   ( Arr Meta Kind   -- what we have now inferred
   , [Postponed]     -- what we wish we knew
   )
stabilize rod mka qs = case go mka qs of
    Just (False, mka, qs) -> Just (mka, qs)
    Just (True,  mka, qs) -> stabilize rod mka qs
    Nothing               -> Nothing
  where
    go :: Arr Meta Kind -> [Postponed] ->
          Maybe (Bool, Arr Meta Kind, [Postponed])
    go mka [] = return (False, mka, [])
    go mka (q@(m, (ga, s, bz)) : qs) = case findArr m mka of
      Nothing -> do
        (b, mka, qs) <- go mka qs
        return (b, mka, q : qs)
      Just _ -> do
        ((), mka, qs') <- chk (sortChk s (M m :$ bz)) rod mka ga 
        (_, mka, qs) <- go mka qs
        return (True, mka, qs' ++ qs)

instance Applicative Chk where
  pure = return
  (<*>) = ap

instance Alternative Chk where
  empty = Chk $ \ _ _ _ -> empty
  Chk c <|> Chk d = Chk $ \ rod mka ga ->
    c rod mka ga <|> d rod mka ga

instance Functor Chk where
  fmap = ap . return

chkU :: Cx -> Chk x -> Chk x
chkU de c = Chk $ \ rod mka ga ->
  chk c rod mka (cxCat ga de)

synKi :: Cx -> OPE -> Sort -> Maybe Kind
synKi ga' th@(OPE bz) i' = (:-) <$> thCx bz ga' <*> (th <? i') where
  thCx B0 ga' = pure ga'
  thCx  (bz :< True)(ga' :& (x, k')) =
    (:&) <$> thCx bz ga' <*> ((,) x <$> OPE bz <? k')
  thCx (bz :< False) (ga' :& _) = thCx bz ga'

chkH :: Hd -> Chk (Either Meta Kind)
chkH h = Chk $ \ rod mka ga -> case h of
  C c -> do
    k <- findArr c (rSignature rod)
    return (Right k, mka, [])
  V x -> return (Right (cxKi ga x), mka, [])
  M m -> case findArr m mka of
    Just k  -> return (Right k, mka, [])
    Nothing -> return (Left m, mka, [])

chkM :: Meta -> OPE -> Sort -> Chk ()
chkM m th s = Chk $ \ rod mka ga -> do
  k <- synKi ga th s
  case findArr m mka of
    Just k' -> do
      guard $ k == k'
      return ((), mka, [])
    Nothing -> return ((), insertArr (m, k) mka, [])

chkP :: Sort -> Meta -> Bwd (Bi Tm) -> Chk ()
chkP s m bz = Chk $ \ rod mka ga ->
  return ((), mka, [(m, (ga, s, bz))])

chkMo :: Morphic t => Morph -> t -> Chk t
chkMo m t = Chk $ \ rod mka ga -> return (morph mka m t, mka, [])

stable :: RodSta -> Chk x -> Maybe (x, Arr Meta Kind)
stable rod c = do
  (x, mka, []) <- chk c rod emptyArr C0
  return (x, mka)

declare :: RodSta -> [Token] -> Maybe RodSta
declare rod src = case tokDecl sg src of
    [(DECLARE con k, sta)] | pNamer sta == 0 -> do
      -- ought to check k
      return $ rod {rSignature = insertArr (con, k) sg}
    [(RULE g (By, r) wz sgz, sta)] -> do
      ((), mka) <- stable rod $ do
        sortChk (P Goal) g
        sortChk (P Rule) r
        traverse (sortChk (P Hypo)) wz
        traverse subgChk sgz
        return ()
      return $ rod {rRules = rRules rod :< (g,By,r,wz,sgz,mka)}
    [(RULE g (From, h) wz sgz, sta)] -> do
      ((), mka) <- stable rod $ do
        sortChk (P Goal) g
        sortChk (P Hypo) h
        traverse (sortChk (P Hypo)) wz
        traverse subgChk sgz
        return ()
      return $ rod {rRules = rRules rod :< (g,From,h,wz,sgz,mka)}
    _ -> Nothing
  where
    sg = rSignature rod
  
declare' :: RodSta -> [Token] -> RodSta
declare' sta src = fromMaybe sta (declare sta src)

grok :: String -> RodSta
grok = foldl declare' initSta . lexFile

subgChk :: Subgoal Tm -> Chk ()
subgChk (Subgoal ga hz g) = do
  cxChk ga
  chkU ga $ do
    traverse (sortChk (P Hypo)) hz
    sortChk (P Goal) g

cxChk :: Cx -> Chk ()
cxChk C0 = return ()
cxChk (de :& (x, (xi :- s))) = do
  cxChk de
  chkU de $ do
    cxChk xi
    chkU xi $ case s of
      P _ -> return ()
      T t -> sortChk (P Type) t

sortChk :: Sort -> Tm -> Chk ()
sortChk i (h :$ bz) = do
  z <- chkH h
  case z of
    Right (jz :- j) -> do
      spineChk jz bz
      j <- chkMo (spim bz) j
      guard $ j == i
    Left m -> chkP i m bz
sortChk i (m :? th) = chkM m th i

spineChk :: Cx -> Bwd (Bi Tm) -> Chk ()
spineChk C0 B0 = return ()
spineChk (de :& (_, k)) (bz :< b) = do
  spineChk de bz
  k <- chkMo (spim bz) k
  bindChk k b
  return ()
spineChk _ _ = fail "spine does not match scope"

cxEx :: Cx -> Bwd String -> Maybe Cx
cxEx C0 B0 = return C0
cxEx (de :& (y, k)) (xz :< x) = do
  ga <- cxEx de xz
  return (ga :& (if null y then x else y, k))
cxEx _ _ = Nothing

bindChk :: Kind -> Bi Tm -> Chk ()
bindChk (de :- i) (xz :. t) = case cxEx de xz of
  Nothing -> fail ""
  Just de -> chkU de (sortChk i t)
