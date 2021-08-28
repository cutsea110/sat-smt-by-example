{-# LANGUAGE FlexibleContexts #-}
module Chap01.Equation1 where

import Control.Arrow (first)
import Control.Monad (foldM)
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Traversable as T

import Z3.Monad

instance MonadZ3 z3 => MonadZ3 (StateT s z3) where
  -- getSolver :: StateT s z3 Solver
  getSolver = StateT $ \s -> do
    svr <- getSolver
    return (svr, s)
  -- getContext :: StateT s z3 Context
  getContext = StateT $ \s -> do
    ctx <- getContext
    return (ctx, s)

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

{- |
>>> runZ3 simple
Just [1, 2, 3]
-}
simple :: MonadZ3 z3 => StateT (Map.Map Expr AST) z3 (Maybe [Integer])
simple = do
  constraint [ EInt 1    :==: EInt 3    :*: EVar "x" :+: EInt 2    :*: EVar "y" :+: EInt (-1) :*: EVar "z"
             , EInt (-2) :==: EInt 2    :*: EVar "x" :+: EInt (-2) :*: EVar "y" :+: EInt 4    :*: EVar "z"
             , EInt 0    :==: EInt (-1) :*: EVar "x" :+: EReal 0.5 :*: EVar "y" :+: EInt (-1) :*: EVar "z"
             ]
  xs <- query [EVar "x", EVar "y", EVar "z"]
  fmap snd $ withModel $ \m ->
    catMaybes <$> mapM (evalInt m) xs

{--
simple :: Z3 (Maybe [Integer])
simple = do
  (_, m1) <- constraint [ EInt 1    :==: EInt 3    :*: EVar "x" :+: EInt 2    :*: EVar "y" :+: EInt (-1) :*: EVar "z"
                        , EInt (-2) :==: EInt 2    :*: EVar "x" :+: EInt (-2) :*: EVar "y" :+: EInt 4    :*: EVar "z"
                        , EInt 0    :==: EInt (-1) :*: EVar "x" :+: EReal 0.5 :*: EVar "y" :+: EInt (-1) :*: EVar "z"
                        ] Map.empty
  fmap snd $ withModel $ \m ->
    catMaybes <$> mapM (evalInt m) (query m1 [EVar "x", EVar "y", EVar "z"])
--}

query :: MonadZ3 z3 => [Expr] -> StateT (Map.Map Expr AST) z3 [AST]
query es = do
  m <- get
  return $ mapMaybe (`Map.lookup` m) es

{-- | TODO: EVar を EIVar とかして Typable にしつつ evalReal などを呼ぶようにしたい
query m e@(EVar var) o = do
  let Just x = Map.lookup e m
  evalInt o x
--}

constraint :: MonadZ3 z3 => [Rel] -> StateT (Map.Map Expr AST) z3 ()
constraint rels = do
  m <- get
  (rs, m') <- runStateT (evalRels rels) m
  put m'
  assert =<< mkAnd rs


-- | Utility function
runZ3 :: StateT (Map.Map k a) Z3 b -> IO b
runZ3 prog = fst <$> evalZ3 (prog `runStateT` Map.empty)

{- |
>>> runZ3 test
Just [1,2]
-}
test :: MonadZ3 z3 => StateT (Map.Map Expr AST) z3 (Maybe [Integer])
test = do
  constraint [ EVar "x" :>: EInt 0
             , EVar "y" :>: EInt 0
             , EVar "y" :>=: EVar "x"
             , EInt 3 :==: EVar "x" :+: EVar "y"
             ]
  xs <- query [EVar "x", EVar "y"]
  fmap snd $ withModel $ \m ->
    catMaybes <$> mapM (evalInt m) xs
{--
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
--}

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

evalRels :: MonadZ3 z3 => [Rel] -> StateT (Map.Map Expr AST) z3 [AST]
evalRels = foldM f []
  where f rs rel = do
          m <- get
          (r,  m') <- runStateT (evalRel rel) m
          put m'
          return (r:rs)

evalRel :: MonadZ3 z3 => Rel -> StateT (Map.Map Expr AST) z3 AST
evalRel (lhs :==: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (evalExpr lhs) m
  (rhs', m2) <- runStateT (evalExpr rhs) m1
  rel <- mkEq lhs' rhs'
  put m2
  return rel
evalRel (lhs :/=: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (evalExpr lhs) m
  (rhs', m2) <- runStateT (evalExpr rhs) m1
  rel  <- mkNot =<< mkEq lhs' rhs'
  put m2
  return rel
evalRel (lhs :<: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (evalExpr lhs) m
  (rhs', m2) <- runStateT (evalExpr rhs) m1
  rel <- mkLt lhs' rhs'
  put m2
  return rel
evalRel (lhs :>: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (evalExpr lhs) m
  (rhs', m2) <- runStateT (evalExpr rhs) m1
  rel <- mkGt lhs' rhs'
  put m2
  return rel
evalRel (lhs :<=: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (evalExpr lhs) m
  (rhs', m2) <- runStateT (evalExpr rhs) m1
  rel <- mkLe lhs' rhs'
  put m2
  return rel
evalRel (lhs :>=: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (evalExpr lhs) m
  (rhs', m2) <- runStateT (evalExpr rhs) m1
  rel <- mkGe lhs' rhs'
  put m2
  return rel

evalExpr :: MonadZ3 z3 => Expr -> StateT (Map.Map Expr AST) z3 AST
evalExpr key@(EVar x) = do
  m <- get
  case Map.lookup key m of
      Just v -> do
        return v
      Nothing -> do
        v <- mkFreshIntVar x
        put (Map.insert key v m)
        return v
evalExpr key@(EInt n) = do
  m <- get
  case Map.lookup key m of
      Just v -> do
        return v
      Nothing -> do
        v <- mkInteger n
        put (Map.insert key v m)
        return v
evalExpr key@(EReal d) = do
  m <- get
  case Map.lookup key m of
      Just v -> do
        return v
      Nothing -> do
        v <- mkRealNum d
        put (Map.insert key v m)
        return v
evalExpr (x :+: y) = do
  m <- get
  (x', m1) <- runStateT (evalExpr x) m
  (y', m2) <- runStateT (evalExpr y) m1
  v <- mkAdd [x', y']
  put m2
  return v
evalExpr (x :-: y) = do
  m <- get
  (x', m1) <- runStateT (evalExpr x) m
  (y', m2) <- runStateT (evalExpr y) m1
  v <- mkSub [x', y']
  put m2
  return v
evalExpr (x :*: y) = do
  m <- get
  (x', m1) <- runStateT (evalExpr x) m
  (y', m2) <- runStateT (evalExpr y) m1
  v <- mkMul [x', y']
  put m2
  return v
