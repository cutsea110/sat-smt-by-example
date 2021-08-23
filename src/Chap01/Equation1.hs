module Chap01.Equation1 where

import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Traversable as T

import Z3.Monad

script :: Z3 (Maybe [Integer])
script = do
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
    [ mkEq _1  =<< mkAdd =<< T.sequence [mkMul [_3, x], mkMul [_2, y], mkUnaryMinus z]
    , mkEq _2' =<< mkAdd =<< T.sequence [mkMul [_2, x], mkMul [_2', y], mkMul [_4, z]]
    , mkEq _0  =<< mkAdd =<< T.sequence [mkMul [_1', x], mkMul [_0_5, y], mkMul [_1', z]]
    ]
  fmap snd $ withModel $ \m ->
    catMaybes <$> mapM (evalInt m) [x, y, z]

data Expr = EVar String
          | EInt Integer
          | EReal Double
          | EPlus Expr Expr
          | EMinus Expr Expr
          | ETimes Expr Expr
          deriving (Eq, Ord, Show)

data Rel = Eq Expr Expr
         | Lt Expr Expr
         | Gt Expr Expr
         | Le Expr Expr
         | Ge Expr Expr
         deriving (Eq, Show)

rel1, rel2, rel3 :: Rel
rel1 = EInt 1 `Eq` ((EInt 3 `ETimes` EVar "x") `EPlus` (EInt 2 `ETimes` EVar "y") `EMinus` EVar "z")
rel2 = EInt (-2) `Eq` ((EInt 2 `ETimes` EVar "x") `EMinus` (EInt 2 `EPlus` EVar "y") `EPlus` (EInt 4 `ETimes` EVar "z"))
rel3 = EInt 0 `Eq` (EVar "x" `EPlus` (EReal 0.5 `ETimes` EVar "y") `EMinus` EVar "z")

evalRel :: MonadZ3 z3 => Map.Map Expr AST -> Rel -> z3 (Map.Map Expr AST, AST)
evalRel m (Eq lhs rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel <- mkEq lhs' rhs'
  return (m2, rel)
evalRel m (Lt lhs rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel <- mkLt lhs' rhs'
  return (m2, rel)
evalRel m (Gt lhs rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel <- mkGt lhs' rhs'
  return (m2, rel)
evalRel m (Le lhs rhs) = do
  (m1, lhs') <- evalExpr m  lhs
  (m2, rhs') <- evalExpr m1 rhs
  rel <- mkLe lhs' rhs'
  return (m2, rel)
evalRel m (Ge lhs rhs) = do
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
evalExpr m (EPlus x y) = do
  (m1, x') <- evalExpr m  x
  (m2, y') <- evalExpr m1 y
  v <- mkAdd [x', y']
  return (m2, v)
evalExpr m (EMinus x y) = do
  (m1, x') <- evalExpr m  x
  (m2, y') <- evalExpr m1 y
  v <- mkSub [x', y']
  return (m2, v)
evalExpr m (ETimes x y) = do
  (m1, x') <- evalExpr m  x
  (m2, y') <- evalExpr m1 y
  v <- mkMul [x', y']
  return (m2, v)
