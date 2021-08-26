module Chap01.Equation1 where

import Control.Arrow (first)
import Control.Monad (foldM)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Traversable as T

import Z3.Monad

{- |
>>> evalZ3 sample
Just [1, -2, -2]
-}
sample :: Z3 (Maybe [Integer])
sample = do
  x <- mkFreshIntVar "x"
  y <- mkFreshIntVar "y"
  z <- mkFreshIntVar "z"
  _0  <- mkInteger 0
  _1  <- mkInteger 1
  _1' <- mkInteger (-1)
  _2  <- mkInteger 2
  _2' <- mkInteger (-2)
  _3  <- mkInteger 3
  _4  <- mkInteger 4
  _0_5 <- mkRealNum 0.5
  assert =<< mkAnd =<< T.sequence
    [ mkEq _1  =<< mkAdd =<< T.sequence [mkMul [_3, x], mkMul [_2, y], mkMul [_1', z]]
    , mkEq _2' =<< mkAdd =<< T.sequence [mkMul [_2, x], mkMul [_2', y], mkMul [_4, z]]
    , mkEq _0  =<< mkAdd =<< T.sequence [mkMul [_1', x], mkMul [_0_5, y], mkMul [_1', z]]
    ]
  fmap snd $ withModel $ \m ->
    catMaybes <$> mapM (evalInt m) [x, y, z]

simple :: Z3 (Maybe [Integer])
simple = do
  let m0 = Map.empty
  m1 <- constraint m0
        [ EInt 1    :==: EInt 3    :*: EVar "x" :+: EInt 2    :*: EVar "y" :+: EInt (-1) :*: EVar "z"
        , EInt (-2) :==: EInt 2    :*: EVar "x" :+: EInt (-2) :*: EVar "y" :+: EInt 4    :*: EVar "z"
        , EInt 0    :==: EInt (-1) :*: EVar "x" :+: EReal 0.5 :*: EVar "y" :+: EInt (-1) :*: EVar "z"
        ]
  fmap snd $ withModel $ \m ->
    catMaybes <$> mapM (evalInt m) (query' m1 [EVar "x", EVar "y", EVar "z"])

query' :: Map.Map Expr AST -> [Expr] -> [AST]
query' = mapMaybe . flip Map.lookup

-- | TODO: EVar を EIVar とかして Typable にしつつ evalReal などを呼ぶようにしたい
query m e@(EVar var) o = do
  let Just x = Map.lookup e m
  evalInt o x

constraint :: MonadZ3 z3 => Map.Map Expr AST -> [Rel] -> z3 (Map.Map Expr AST)
constraint m rels = do
  (rs, m') <- evalRels rels m
  assert =<< mkAnd rs
  return m'

evalRels :: MonadZ3 z3 => [Rel] -> Map.Map Expr AST -> z3 ([AST], Map.Map Expr AST)
evalRels rels m0 = first reverse <$> foldM f ([], m0) rels
  where f (rs, m) rel = do
          (r,  m') <- evalRel rel m
          return (r:rs, m')

{- |
>>> evalZ3 test
Just [1,2]
-}
test :: Z3 (Maybe [Integer])
test = do
  let m0 = Map.empty
  (r1, m1) <- evalRel (EVar "x" :>: EInt 0) m0
  (r2, m2) <- evalRel (EVar "y" :>: EInt 0) m1
  (r3, m3) <- evalRel (EVar "y" :>=: EVar "x") m2
  (r4, m4) <- evalRel (EInt 3 :==: EVar "x" :+: EVar "y") m3
  assert =<< mkAnd [r1, r2, r3, r4]
  let (Just x) = Map.lookup (EVar "x") m4
  let (Just y) = Map.lookup (EVar "y") m4
  fmap snd $ withModel $ \m ->
    catMaybes <$> mapM (evalInt m) [x, y]

data Expr = EVar String
          | EInt Integer
          | EReal Double
          | Expr :+: Expr
          | Expr :-: Expr
          | Expr :*: Expr
          deriving (Eq, Ord, Show)

data Rel = Expr :==: Expr
         | Expr :/=: Expr
         | Expr :<: Expr
         | Expr :>: Expr
         | Expr :<=: Expr
         | Expr :>=: Expr
         deriving (Eq, Show)

infixl 7 :*:
infixl 6 :+:, :-:
infix  4 :==:, :/=:, :<:, :>:, :<=:, :>=:

rel1, rel2, rel3 :: Rel
rel1 = EInt 1    :==: EInt 3    :*: EVar "x" :+: EInt 2    :*: EVar "y" :-: EVar "z"
rel2 = EInt (-2) :==: EInt 2    :*: EVar "x" :+: EInt (-2) :+: EVar "y" :+: EInt 4    :*: EVar "z"
rel3 = EInt 0    :==: EInt (-1) :*: EVar "x" :+: EReal 0.5 :*: EVar "y" :+: EInt (-1) :*: EVar "z"

evalRel :: MonadZ3 z3 => Rel -> Map.Map Expr AST -> z3 (AST, Map.Map Expr AST)
evalRel (lhs :==: rhs) m = do
  (lhs', m1) <- evalExpr lhs m
  (rhs', m2) <- evalExpr rhs m1
  rel <- mkEq lhs' rhs'
  return (rel, m2)
evalRel (lhs :/=: rhs) m = do
  (lhs', m1) <- evalExpr lhs m
  (rhs', m2) <- evalExpr rhs m1
  rel  <- mkNot =<< mkEq lhs' rhs'
  return (rel, m2)
evalRel (lhs :<: rhs) m = do
  (lhs', m1) <- evalExpr lhs m
  (rhs', m2) <- evalExpr rhs m1
  rel <- mkLt lhs' rhs'
  return (rel, m2)
evalRel (lhs :>: rhs) m = do
  (lhs', m1) <- evalExpr lhs m
  (rhs', m2) <- evalExpr rhs m1
  rel <- mkGt lhs' rhs'
  return (rel, m2)
evalRel (lhs :<=: rhs) m = do
  (lhs', m1) <- evalExpr lhs m
  (rhs', m2) <- evalExpr rhs m1
  rel <- mkLe lhs' rhs'
  return (rel, m2)
evalRel (lhs :>=: rhs) m = do
  (lhs', m1) <- evalExpr lhs m
  (rhs', m2) <- evalExpr rhs m1
  rel <- mkGe lhs' rhs'
  return (rel, m2)

evalExpr :: MonadZ3 z3 => Expr -> Map.Map Expr AST -> z3 (AST, Map.Map Expr AST)
evalExpr key@(EVar x) m
  = case Map.lookup key m of
      Just v -> do
        return (v, m)
      Nothing -> do
        v <- mkFreshIntVar x
        return (v, Map.insert key v m)
evalExpr key@(EInt n) m
  = case Map.lookup key m of
      Just v -> do
        return (v, m)
      Nothing -> do
        v <- mkInteger n
        return (v, Map.insert key v m)
evalExpr key@(EReal d) m
  = case Map.lookup key m of
      Just v -> do
        return (v, m)
      Nothing -> do
        v <- mkRealNum d
        return (v, Map.insert key v m)
evalExpr (x :+: y) m = do
  (x', m1) <- evalExpr x  m
  (y', m2) <- evalExpr y m1
  v <- mkAdd [x', y']
  return (v, m2)
evalExpr (x :-: y) m = do
  (x', m1) <- evalExpr x  m
  (y', m2) <- evalExpr y m1
  v <- mkSub [x', y']
  return (v, m2)
evalExpr (x :*: y) m = do
  (x', m1) <- evalExpr x  m
  (y', m2) <- evalExpr y m1
  v <- mkMul [x', y']
  return (v, m2)
