{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Unify where

import Control.Monad
import Control.Arrow

import BigArray
import Bwd
import OPE
import Tm

data Pruning
  = Pruning [(META, OPE)] -- sorted by metas
  | KiBosh
  deriving Show
instance Monoid Pruning where
  mempty = Pruning []
  mappend (Pruning p) (Pruning q) = Pruning (go p q) where
    go [] q' = q'
    go p' [] = p'
    go p'x@(x@(m, th) : p) q'y@(y@(n, ph) : q) = case compare m n of
      LT -> x : go p q'y
      EQ -> (m , th << ph) : go p q
      GT -> y : go p'x q
  mappend _ _ = KiBosh

prune1 :: META -> OPE -> Pruning
prune1 _ (OPE B0) = Pruning mempty
prune1 (Meta (i, k)) th = case synKi th k of
  Just k  -> Pruning [(Meta (i, k), th)]
  Nothing -> KiBosh

newtype Stanner = Stanner [(META, TM)] deriving (Show, Eq) -- sorted by metas

stan1 :: META -> TM -> Stanner
stan1 m t = Stanner [(m, t)]

instance Monoid Stanner where
  mempty = Stanner []
  mappend (Stanner as) sg@(Stanner bs) =
    Stanner (go (fmap (id *** stan sg) as) bs) where
    go [] bs = bs
    go as [] = as
    go aas@(a@(m, _) : as) bbs@(b@(n, _) : bs) = case compare m n of
      LT -> a : go as bbs
      EQ -> a : go as bs
      GT -> b : go aas bs

prullback :: Pruning      -- p'
          -> Pruning      -- q'
          -> ( Pruning    -- r
             , ( Pruning  -- p s.t. mappend p p' = r
               , Pruning  -- q s.t. mappend q q' = r
             ) )
prullback (Pruning p) (Pruning q) = go p q where
  go [] q' = (Pruning q', (Pruning q', mempty))
  go p' [] = (Pruning p', (mempty, Pruning p'))
  go p'x@(x@(m@(Meta (i, k')), th') : p') q'y@(y@(n, ph') : q') = case compare m n of
    LT -> case go p' q'y of
      (Pruning r, (Pruning p, Pruning q)) ->
        (Pruning (x : r), (Pruning p, Pruning (x : q)))
      _ -> (KiBosh, (KiBosh, KiBosh))
    EQ -> case go p' q' of
      (Pruning r, (Pruning p, Pruning q)) ->
         let (ps, (th, ph)) = pullback th' ph'
         in  case synKi th k' of
               Just k -> let m = Meta (i, k) in
                 (Pruning ((m, ps) : r),
                   (Pruning ((m, th) : p), Pruning ((m, ph) : q)))
               Nothing -> (KiBosh, (KiBosh, KiBosh))
      _ -> (KiBosh, (KiBosh, KiBosh))
    GT -> case go p'x q' of
      (Pruning r, (Pruning p, Pruning q)) ->
        (Pruning (y : r), (Pruning (y : p), Pruning q))
      _ -> (KiBosh, (KiBosh, KiBosh))
prullback _ _ = (KiBosh, (KiBosh, KiBosh))

pruneStan :: [(META, OPE)] -> Stanner
pruneStan mos = Stanner (fmap (\ (m, th) -> (m, m :? th)) mos)

class Stan t where
  stan :: Stanner -> t -> t

instance Stan TM where
  stan (Stanner sg) (m :? th) = case lookup m sg of
    Just t  -> t << th
    Nothing -> m :? th
  stan (Stanner sg) (M m :$ tz) = case lookup m sg of
    Just t  -> morph (spim tz) t
    Nothing -> M m :$ stan (Stanner sg) tz
  stan sg (h :$ tz) = h :$ stan sg tz

instance Stan x => Stan (Bwd x) where
  stan = fmap . stan

instance Thin x => Thin [x] where
  ts << th = fmap (<< th) ts
  th <? ts = traverse (th <?) ts
instance Stan x => Stan [x] where
  stan = fmap . stan

instance Stan x => Stan (Bi x) where
  stan = fmap . stan

instance Stan Cx where
  stan sg C0 = C0
  stan sg (ga :& (x, k)) = stan sg ga :& (x, stan sg k)

instance Stan Kind where
  stan sg (ga :- s) = stan sg ga :- stan sg s

instance Stan Sort where
  stan sg s@(P _) = s
  stan sg (T t)   = T (stan sg t)

data PruneOut t
  = Pruned Pruning t
  | Occurs Bool -- is the occurrence lethal?

class Stan t => Prune t where
  prune :: OPE -> Bool -> t -> PruneOut t
  pruned :: [(META, OPE)] -> t -> t
  pruned = stan . pruneStan
  -- prune th t' = Just (p, t)  ->  t << th = pruned p t'

instance Prune TM where
  prune th' r (h@(C _) :$ tz') = case prune th' r tz' of
    Pruned p tz -> Pruned p (h :$ tz)
    Occurs r -> Occurs r
  prune th' r (V i' :$ tz') = case (th' <? i', prune th' r tz') of
    (Just i, Pruned p tz) -> Pruned p (V i :$ tz)
    _ -> Occurs r
  prune th' r (h@(M m) :$ tz') = case prune th' False tz' of
    Pruned p tz -> Pruned p (h :$ tz)
    Occurs _ -> Occurs False
  prune th' r (m :? ph') = case prune1 m ph of
      KiBosh -> Occurs r
      p -> Pruned p (m :? th)
    where (ps, (th, ph)) = pullback th' ph'
    
{-
  unify s t | s == t = Just mempty
  unify (m :? th') t'
    | metaDep m t' = Nothing
    | otherwise = do
    (p, t) <- prune th' t'
    return (mappend (pruneStan p) (stan1 m t))  -- slightly inefficient?
  unify t' (m :? th')
    | metaDep m t' = Nothing
    | otherwise = do
    (p, t) <- prune th' t'
    return (mappend (pruneStan p) (stan1 m t))  -- slightly inefficient?
  unify (f :$ sz) (g :$ tz)
    | f == g = unify sz tz
    | otherwise = Nothing
-}

instance Prune x => Prune (Bwd x) where
  prune th r B0 = Pruned mempty B0
  prune th r (xz' :< x') = case (prune th r xz', prune th r x') of
    (Pruned p' xz, Pruned q' x) -> case prullback p' q' of
      (r@(Pruning _), (Pruning p, Pruning q)) ->
        Pruned r (pruned p xz :< pruned q x)
      _ -> Occurs r
    _ -> Occurs r
    
{-
  unify B0 B0 = Just mempty
  unify (sz :< s) (tz :< t) = do
    rh <- unify sz tz
    sg <- unify (stan rh s) (stan rh t)
    return (mappend rh sg)
  unify _  _  = Nothing
-}

instance Prune x => Prune [x] where
  prune th r [] = Pruned mempty []
  prune th r (x' : xs') = case (prune th r x', prune th r xs') of
    (Pruned p' x, Pruned q' xs) -> case prullback p' q' of
      (r@(Pruning _), (Pruning p, Pruning q)) ->
        Pruned r (pruned p x : pruned q xs)
      _ -> Occurs r
    _ -> Occurs r

{-
  unify [] [] = Just mempty
  unify (s : ss) (t : ts) = do
    rh <- unify s t
    sg <- unify (stan rh ss) (stan rh ts)
    return (mappend rh sg)
  unify _  _  = Nothing
-}

instance Prune x => Prune (Bi x) where
  prune th r (xz :. t') = case prune (th <|- xz) r t' of
    Pruned p t -> Pruned p (xz :. t)
    Occurs r -> Occurs r
    
{-
  unify (xz :. s) (yz :. t)
    | length xz == length yz = unify s t
    | otherwise = Nothing
-}


data Constraint
  = HetHet (Cx, Sort, TM) (Cx, Sort, TM)
  | HomHet Cx (Sort, TM) (Sort, TM)
  | Hom Cx Sort TM TM
  deriving Show

instance Stan Constraint where
  stan sg (HetHet (ga0, s0, t0) (ga1, s1, t1)) = constraint
    (stan sg ga0, stan sg s0, stan sg t0)
    (stan sg ga1, stan sg s1, stan sg t1)
  stan sg (HomHet ga (s0, t0) (s1, t1)) = let ga' = stan sg ga in constraint
    (ga', stan sg s0, stan sg t0)
    (ga', stan sg s1, stan sg t1)
    -- shouldn't really retest context equality
  stan sg (Hom ga s t0 t1) =
    Hom (stan sg ga) (stan sg s) (stan sg t0) (stan sg t1)

constraint :: (Cx, Sort, TM) -> (Cx, Sort, TM) -> Constraint
constraint (ga0, s0, t0) (ga1, s1, t1)
  | ga0 == ga1 = if s0 == s1 then Hom ga0 s0 t0 t1
                             else HomHet ga0 (s0, t0) (s1, t1)
constraint l r = HetHet l r

lhs, rhs :: Constraint -> (Cx, Sort, TM) 
lhs (HetHet l _)          = l
lhs (HomHet ga (s, t) _)  = (ga, s, t)
lhs (Hom ga s t _)        = (ga, s, t)
rhs (HetHet _ r)          = r
rhs (HomHet ga _ (s, t))  = (ga, s, t)
rhs (Hom ga s _ t)        = (ga, s, t)

spineCons :: (Cx, Cx, Bwd (Bi TM))
          -> (Cx, Cx, Bwd (Bi TM))
          -> [Constraint] -> Maybe [Constraint]
spineCons (_, C0, B0) (_, C0, B0) cs = return cs
spineCons 
  (ga0, de0 :& (_, k0), bz0 :< (xz0 :. t0))
  (ga1, de1 :& (_, k1), bz1 :< (xz1 :. t1))
  cs =
  spineCons (ga0, de0, bz0) (ga1, de1, bz1)
    (constraint (cxCat ga0 xi0, s0, t0) (cxCat ga1 xi1, s1, t1) : cs) where
    xi0 :- s0 = morph (spim bz0) k0
    xi1 :- s1 = morph (spim bz1) k1
spineCons _ _ _ = Nothing

solve :: Signature -> Constraint ->
         Maybe
         ( Stanner
         , Bwd Constraint  -- postponed
         , [Constraint]    -- subconstraints
         )
solve sig (Hom _ _ t0 t1) | t0 == t1 = return (mempty, B0, [])
solve sig (HomHet _ (_, t0) (_, t1)) | t0 == t1 = return (mempty, B0, [])
solve sig (HetHet (_, _, t0) (_, _, t1)) | t0 == t1 = return (mempty, B0, [])
solve sig (Hom ga s (m :? th) t) = trySol ga s m th t
solve sig (Hom ga s t (m :? th)) = trySol ga s m th t
solve sig c = case (lhs c, rhs c) of
  ((ga0, s0, C c0 :$ bz0), (ga1, s1, C c1 :$ bz1)) -> do
    guard $ c0 == c1
    (de :- _) <- findArr c0 sig
    cs <- spineCons (ga0, de, bz0) (ga1, de, bz1) []
    return (mempty, B0, cs)
  ((ga0, s0, V i0 :$ bz0), (ga1, s1, V i1 :$ bz1)) -> do
    guard $ i0 == i1
    let de0 :- _ = cxKi ga0 i0
    let de1 :- _ = cxKi ga1 i1
    cs <- spineCons (ga0, de0, bz0) (ga1, de1, bz1) []
    return (mempty, B0, cs)
  ((_, _, M _ :$ _), _) -> return (mempty, B0 :< c, [])
  (_, (_, _, M _ :$ _)) -> return (mempty, B0 :< c, [])
  _ -> Nothing

trySol :: Cx -> Sort -> META -> OPE -> TM ->
          Maybe (Stanner, Bwd Constraint, [Constraint])
trySol ga s m th t = case prune th True t of
  Pruned (Pruning pr) t -> 
    return (mappend (pruneStan pr) (stan1 m t), B0, [])
  Pruned KiBosh _  -> fail "pruning kiboshed"
  Occurs True      -> fail "fatal dependency"
  Occurs False     -> return (mempty, B0 :< Hom ga s (m :? th) t, [])

solver :: Signature
       -> Bool            -- any progress?
       -> Bwd Constraint  -- postponed
       -> Stanner         -- accumulated solution
       -> [Constraint]    -- active constraints (not yet instantiated)
       -> Maybe (Either (Bwd Constraint) Stanner)   -- solution?
solver sig p B0 sg [] = return (Right sg)
solver sig True cz sg [] = solver sig False B0 sg (cz <>> [])
solver sig False cz sg [] = return (Left cz)
solver sig p cz sg (c : cs) = do
  (sg', cz', cs') <- solve sig (stan sg c)
  let p' = case cz' of {B0 -> True; _ -> p}
  solver sig p' (cz +< cz') (mappend sg sg') (cs' ++ cs)

-----------
myKind :: Kind
myKind = C0 :& ("X", C0 :- P Type) :- P Type

mySig :: Signature
mySig = insertArr ("Foo", myKind) (single ("Goo", myKind))

myCon0 :: Constraint
myCon0 = Hom (C0 :& ("X", C0 :- P Type)) (P Type)
           (M (Meta (0, myKind)) :$ B0 :< (B0 :. V 0 :$ B0))
           (C "Foo" :$ B0 :< (B0 :. V 0 :$ B0))

myCon0' :: Constraint
myCon0' = Hom (C0 :& ("X", C0 :- P Type)) (P Type)
           (M (Meta (0, myKind)) :$ B0 :< (B0 :. V 0 :$ B0))
           (C "Goo" :$ B0 :< (B0 :. V 0 :$ B0))

myCon1 = Hom (C0 :& ("X", C0 :- P Type)) (P Type)
           (Meta (0, myKind) :? oi)
           (C "Foo" :$ B0 :< (B0 :. V 0 :$ B0))

-- solver mySig False B0 mempty [myCon0, myCon1]
