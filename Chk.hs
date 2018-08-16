{-# LANGUAGE PatternGuards #-}

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

data Constraint
  = HetHet (Cx, Sort, Tm) (Cx, Sort, Tm)
  | HomHet Cx (Sort, Tm) (Sort, Tm)
  | Hom Cx Sort Tm Tm
  deriving Show

constraint :: (Cx, Sort, Tm) -> (Cx, Sort, Tm) -> Constraint
constraint (ga0, s0, t0) (ga1, s1, t1)
  | ga0 == ga1 = if s0 == s1 then Hom ga0 s0 t0 t1
                             else HomHet ga0 (s0, t0) (s1, t1)
constraint l r = HetHet l r

lhs, rhs :: Constraint -> (Cx, Sort, Tm) 
lhs (HetHet l _)          = l
lhs (HomHet ga (s, t) _)  = (ga, s, t)
lhs (Hom ga s t _)        = (ga, s, t)
rhs (HetHet _ r)          = r
rhs (HomHet ga _ (s, t))  = (ga, s, t)
rhs (Hom ga s _ t)        = (ga, s, t)




spineCons :: Arr Meta Kind
          -> (Cx, Cx, Bwd (Bi Tm))
          -> (Cx, Cx, Bwd (Bi Tm))
          -> [Constraint] -> Maybe [Constraint]
spineCons _ (_, C0, B0) (_, C0, B0) cs = return cs
spineCons mka
  (ga0, de0 :& (_, k0), bz0 :< (xz0 :. t0))
  (ga1, de1 :& (_, k1), bz1 :< (xz1 :. t1))
  cs =
  spineCons mka (ga0, de0, bz0) (ga1, de1, bz1)
    (constraint (cxCat ga0 xi0, s0, t0) (cxCat ga1 xi1, s1, t1) : cs) where
    xi0 :- s0 = morph mka (spim bz0) k0
    xi1 :- s1 = morph mka (spim bz1) k1
spineCons _ _ _ _ = Nothing

solve :: RodSta -> Arr Meta Kind -> Constraint ->
         Maybe (Arr Meta (Bi Tm), [Constraint])
solve rod mka (Hom _ _ t0 t1) | t0 == t1 = return (emptyArr, [])
solve rod mka (HomHet _ (_, t0) (_, t1)) | t0 == t1 = return (emptyArr, [])
solve rod mka (HetHet (_, _, t0) (_, _, t1)) | t0 == t1 = return (emptyArr, [])
solve rod mka (Hom ga s (m :? th) t) = trySol rod mka ga s m th t
solve rod mka (Hom ga s t (m :? th)) = trySol rod mka ga s m th t
solve rod mka c = case (lhs c, rhs c) of
  ((ga0, s0, C c0 :$ bz0), (ga1, s1, C c1 :$ bz1)) -> do
    guard $ c0 == c1
    (de :- _) <- findArr c0 (rSignature rod)
    cs <- spineCons mka (ga0, de, bz0) (ga1, de, bz1) []
    return (emptyArr, cs)
  ((ga0, s0, V i0 :$ bz0), (ga1, s1, V i1 :$ bz1)) -> do
    guard $ i0 == i1
    let de0 :- _ = cxKi ga0 i0
    let de1 :- _ = cxKi ga1 i1
    cs <- spineCons mka (ga0, de0, bz0) (ga1, de1, bz1) []
    return (emptyArr, cs)
  ((_, _, M _ :$ _), _) -> return (emptyArr, [c])
  (_, (_, _, M _ :$ _)) -> return (emptyArr, [c])
  _ -> Nothing

pruSt :: [(Meta, (Kind, OPE))] -> Arr Meta (Bi Tm)
pruSt = foldr go emptyArr where
  go (m, (_, th)) = single (m

trySol :: RodSta -> Arr Meta Kind ->
          Cx -> Sort -> Meta -> OPE -> Tm ->
          Maybe (Arr Meta (Bi Tm), [Constraint])
trySol rod mka ga s m th t = case prune mka m th True t of
  Pruned pr t -> do
    (de :- _) <- findArr m mka
    return (insertArr (m, cxDom de :. t) (pruSt pr), [])
  Occ True    -> fail "fatal dependency"
  Occ False   -> return (emptyArr, [Hom ga s (m :? th) t])

data Pruning x
  = Pruned [(Meta, (Kind, OPE))] x
  | Occ Bool
  deriving Show

prullback :: [(Meta, (Kind, OPE))] -> [(Meta, (Kind, OPE))] ->
  Maybe ([(Meta, (Kind, OPE))], [(Meta, (Kind, OPE))], [(Meta, (Kind, OPE))])
prullback = undefined

class Prune x where
  prune :: Arr Meta Kind -> Meta -> OPE -> Bool -> x -> Pruning x
  pruned :: [(Meta, (Kind, OPE))] -> x -> x

instance Prune Tm where
  prune mka m th r (V i :$ bz) = case th <? i of
    Nothing -> Occ r
    Just i -> case prune mka m th r bz of
      Pruned pr bz -> Pruned pr (V i :$ bz)
      Occ r -> Occ r
  pruned pr (h :$ bz) = case h of
      M m | Just (k, th) <- lookup m pr -> M m :$ (th ?< bz')
      _ -> h :$ (pruned pr bz')
    where bz' = pruned pr bz
  pruned pr (m :? ph) = case lookup m pr of
    Nothing -> m :? ph
    Just (_, th) -> m :? (th << ph)

instance Prune t => Prune (Bwd t) where
  prune mka m th r B0 = Pruned [] B0
  prune mka m th r (tz :< t) = case prune mka m th r tz of
    Occ r -> Occ r
    Pruned pr tz -> case prune mka m th r t of
      Occ r -> Occ r
      Pruned qr t -> case prullback pr qr of
        Nothing -> Occ r
        Just (rr, pr, qr) -> Pruned rr (pruned pr tz :< pruned qr t)
  pruned pr bz = fmap (pruned pr) bz

instance Prune t => Prune (Bi t) where
  prune mka m th r (xz :. t) = case prune mka m (th <|- xz) r t of
    Pruned pr t -> Pruned pr (xz :. t)
    Occ r -> Occ r
  pruned pr (xz :. t) = xz :. pruned (fmap w pr) t where
    w (m, (k, th)) = (m, (k, th <|^ xz))
    