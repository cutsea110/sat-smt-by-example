module Chap01.Equation1 where

import Control.Arrow (second)
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
  (m', rs) <- evalRels m rels
  assert =<< mkAnd rs
  return m'

evalRels :: MonadZ3 z3 => Map.Map Expr AST -> [Rel] -> z3 (Map.Map Expr AST, [AST])
evalRels m0 rels = second reverse <$> foldM f (m0, []) rels
  where f (m,  rs) rel = do
          (m', r) <- evalRel m rel
          return (m', r:rs)

{- |
>>> evalZ3 test
Just [1,2]
-}
test :: Z3 (Maybe [Integer])
test = do
  let m0 = Map.empty
  (m1, r1) <- evalRel m0 (EVar "x" :>: EInt 0)
  (m2, r2) <- evalRel m1 (EVar "y" :>: EInt 0)
  (m3, r3) <- evalRel m2 (EVar "y" :>=: EVar "x")
  (m4, r4) <- evalRel m3 (EInt 3 :==: EVar "x" :+: EVar "y")
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

evalRel :: MonadZ3 z3 => Map.Map Expr AST -> Rel -> z3 (Map.Map Expr AST, AST)
evalRel m (lhs :==: rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel <- mkEq lhs' rhs'
  return (m2, rel)
evalRel m (lhs :/=: rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel  <- mkNot =<< mkEq lhs' rhs'
  return (m2, rel)
evalRel m (lhs :<: rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel <- mkLt lhs' rhs'
  return (m2, rel)
evalRel m (lhs :>: rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel <- mkGt lhs' rhs'
  return (m2, rel)
evalRel m (lhs :<=: rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel <- mkLe lhs' rhs'
  return (m2, rel)
evalRel m (lhs :>=: rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel <- mkGe lhs' rhs'
  return (m2, rel)

evalExpr :: MonadZ3 z3 => Map.Map Expr AST -> Expr -> z3 (Map.Map Expr AST, AST)
evalExpr m key@(EVar x)
  = case Map.lookup key m of
      Just v -> do
        return (m, v)
      Nothing -> do
        v <- mkFreshIntVar x
        return (Map.insert key v m, v)
evalExpr m key@(EInt n)
  = case Map.lookup key m of
      Just v -> do
        return (m, v)
      Nothing -> do
        v <- mkInteger n
        return (Map.insert key v m, v)
evalExpr m key@(EReal d)
  = case Map.lookup key m of
      Just v -> do
        return (m, v)
      Nothing -> do
        v <- mkRealNum d
        return (Map.insert key v m, v)
evalExpr m (x :+: y) = do
  (m1, x') <- evalExpr m  x
  (m2, y') <- evalExpr m1 y
  v <- mkAdd [x', y']
  return (m2, v)
evalExpr m (x :-: y) = do
  (m1, x') <- evalExpr m  x
  (m2, y') <- evalExpr m1 y
  v <- mkSub [x', y']
  return (m2, v)
evalExpr m (x :*: y) = do
  (m1, x') <- evalExpr m  x
  (m2, y') <- evalExpr m1 y
  v <- mkMul [x', y']
  return (m2, v)
