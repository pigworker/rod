module Unify where

import Control.Arrow

import Bwd
import OPE
import Tm

newtype Pruning = Pruning [(Meta, OPE)] deriving Show -- sorted by metas

instance Monoid Pruning where
  mempty = Pruning []
  mappend (Pruning p) (Pruning q) = Pruning (go p q) where
    go [] q' = q'
    go p' [] = p'
    go p'x@(x@(m, th) : p) q'y@(y@(n, ph) : q) = case compare m n of
      LT -> x : go p q'y
      EQ -> (m , th << ph) : go p q
      GT -> y : go p'x q

prune1 :: Meta -> OPE -> Pruning
prune1 _ (OPE B0) = mempty
prune1 m th = Pruning [(m, th)]

newtype Stanner = Stanner [(Meta, Tm)] deriving (Show, Eq) -- sorted by metas

stan1 :: Meta -> Tm -> Stanner
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
  go p'x@(x@(m, th') : p') q'y@(y@(n, ph') : q') = case compare m n of
    LT -> let (Pruning r, (Pruning p, Pruning q)) = go p' q'y
          in  (Pruning (x : r),
                (Pruning p, Pruning (x : q)))
    EQ -> let (Pruning r, (Pruning p, Pruning q)) = go p' q'
              (ps, (th, ph)) = pullback th' ph'
          in  (Pruning ((m, ps) : r),
                (Pruning ((m, th) : p), Pruning ((m, ph) : q)))
    GT -> let (Pruning r, (Pruning p, Pruning q)) = go p'x q'
          in  (Pruning (y : r),
                (Pruning (y : p), Pruning q))

pruneStan :: Pruning -> Stanner
pruneStan (Pruning mos) = Stanner (fmap (\ (m, th) -> (m, m :? th)) mos)

class Thin t => Stan t where
  stan  :: Stanner -> t -> t

class Stan t => Unify t where
  prune :: OPE -> t -> Maybe (Pruning, t)
  pruned :: Pruning -> t -> t
  pruned = stan . pruneStan
  -- prune th t' = Just (p, t)  ->  t << th = pruned p t'
  unify :: t -> t -> Maybe Stanner

instance Stan Tm where
  stan (Stanner sg) (m :? th) = case lookup m sg of
    Just t  -> t << th
    Nothing -> m :? th
  stan sg (h :$ tz) = h :$ stan sg tz

instance Unify Tm where
  prune th' (h@(C _ _) :$ tz') = do
    (p, tz) <- prune th' tz'
    return (p, h :$ tz)
  prune th' (V i' :$ tz') = do
    i <- th' <? i'
    (p, tz) <- prune th' tz'
    return (p, V i :$ tz)
  prune th' (m :? ph') = return (prune1 m ph, m :? th) where
    (ps, (th, ph)) = pullback th' ph'
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
  
instance Stan x => Stan (Bwd x) where
  stan = fmap . stan

instance Unify x => Unify (Bwd x) where
  prune th B0 = Just (mempty, B0)
  prune th (xz' :< x') = do
    (p', xz) <- prune th xz'
    (q', x)  <- prune th x'
    let (r, (p, q)) = prullback p' q'
    return (r, pruned p xz :< pruned q x)
  unify B0 B0 = Just mempty
  unify (sz :< s) (tz :< t) = do
    rh <- unify sz tz
    sg <- unify (stan rh s) (stan rh t)
    return (mappend rh sg)
  unify _  _  = Nothing

instance Thin x => Thin [x] where
  ts << th = fmap (<< th) ts
  th <? ts = traverse (th <?) ts
instance Stan x => Stan [x] where
  stan = fmap . stan

instance Unify x => Unify [x] where
  prune th [] = Just (mempty, [])
  prune th (x' : xs') = do
    (p', x)  <- prune th x'
    (q', xs) <- prune th xs'
    let (r, (p, q)) = prullback p' q'
    return (r, pruned p x : pruned q xs)
  unify [] [] = Just mempty
  unify (s : ss) (t : ts) = do
    rh <- unify s t
    sg <- unify (stan rh ss) (stan rh ts)
    return (mappend rh sg)
  unify _  _  = Nothing

instance Stan x => Stan (Bi x) where
  stan = fmap . stan

instance Unify x => Unify (Bi x) where
  prune th (xz :. t') = do
    (p, t) <- prune (th <|- xz) t'
    return (p, (xz :. t))
  unify (xz :. s) (yz :. t)
    | length xz == length yz = unify s t
    | otherwise = Nothing

