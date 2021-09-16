{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
module Language
  ( Expr (..)
  , Rel (..)
  , liftRels, liftRel
  , liftExpr
  , queries
  , constraint
  , runZ3
  , returnInts
  ) where

import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe

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

newtype SZ3 a = SZ3 { out :: StateT (Map.Map Expr AST) Z3 a }
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadZ3 SZ3 where
  getSolver = SZ3 . StateT $ \s -> do
    svr <- getSolver
    return (svr, s)
  getContext = SZ3 . StateT $ \s -> do
    ctx <- getContext
    return (ctx, s)

data Expr = EVar String
          | EInt Integer
          | EReal Double
          | Expr :+: Expr
          | Expr :-: Expr
          | Expr :*: Expr
          | Rel :&&: Rel
          | Rel :||: Rel
          deriving (Eq, Ord, Show)

data Rel = Expr :==: Expr
         | Expr :/=: Expr
         | Expr :<: Expr
         | Expr :>: Expr
         | Expr :<=: Expr
         | Expr :>=: Expr
         deriving (Eq, Ord, Show)

infixl 7 :*:
infixl 6 :+:, :-:
infix  4 :==:, :/=:, :<:, :>:, :<=:, :>=:

liftRels :: MonadZ3 z3 => [Rel] -> StateT (Map.Map Expr AST) z3 [AST]
liftRels = foldM f []
  where f rs rel = do
          m <- get
          (r,  m') <- runStateT (liftRel rel) m
          put m'
          return (r:rs)

liftRel :: MonadZ3 z3 => Rel -> StateT (Map.Map Expr AST) z3 AST
liftRel (lhs :==: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (liftExpr lhs) m
  (rhs', m2) <- runStateT (liftExpr rhs) m1
  rel <- mkEq lhs' rhs'
  put m2
  return rel
liftRel (lhs :/=: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (liftExpr lhs) m
  (rhs', m2) <- runStateT (liftExpr rhs) m1
  rel  <- mkNot =<< mkEq lhs' rhs'
  put m2
  return rel
liftRel (lhs :<: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (liftExpr lhs) m
  (rhs', m2) <- runStateT (liftExpr rhs) m1
  rel <- mkLt lhs' rhs'
  put m2
  return rel
liftRel (lhs :>: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (liftExpr lhs) m
  (rhs', m2) <- runStateT (liftExpr rhs) m1
  rel <- mkGt lhs' rhs'
  put m2
  return rel
liftRel (lhs :<=: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (liftExpr lhs) m
  (rhs', m2) <- runStateT (liftExpr rhs) m1
  rel <- mkLe lhs' rhs'
  put m2
  return rel
liftRel (lhs :>=: rhs) = do
  m <- get
  (lhs', m1) <- runStateT (liftExpr lhs) m
  (rhs', m2) <- runStateT (liftExpr rhs) m1
  rel <- mkGe lhs' rhs'
  put m2
  return rel

liftExpr :: MonadZ3 z3 => Expr -> StateT (Map.Map Expr AST) z3 AST
liftExpr key@(EVar x) = do
  m <- get
  case Map.lookup key m of
      Just v -> do
        return v
      Nothing -> do
        v <- mkFreshIntVar x
        put (Map.insert key v m)
        return v
liftExpr key@(EInt n) = do
  m <- get
  case Map.lookup key m of
      Just v -> do
        return v
      Nothing -> do
        v <- mkInteger n
        put (Map.insert key v m)
        return v
liftExpr key@(EReal d) = do
  m <- get
  case Map.lookup key m of
      Just v -> do
        return v
      Nothing -> do
        v <- mkRealNum d
        put (Map.insert key v m)
        return v
liftExpr (x :+: y) = do
  m <- get
  (x', m1) <- runStateT (liftExpr x) m
  (y', m2) <- runStateT (liftExpr y) m1
  v <- mkAdd [x', y']
  put m2
  return v
liftExpr (x :-: y) = do
  m <- get
  (x', m1) <- runStateT (liftExpr x) m
  (y', m2) <- runStateT (liftExpr y) m1
  v <- mkSub [x', y']
  put m2
  return v
liftExpr (x :*: y) = do
  m <- get
  (x', m1) <- runStateT (liftExpr x) m
  (y', m2) <- runStateT (liftExpr y) m1
  v <- mkMul [x', y']
  put m2
  return v
liftExpr (x :&&: y) = do
  m <- get
  (x', m1) <- runStateT (liftRel x) m
  (y', m2) <- runStateT (liftRel y) m1
  v <- mkAnd [x', y']
  put m
  return v
liftExpr (x :||: y) = do
  m <- get
  (x', m1) <- runStateT (liftRel x) m
  (y', m2) <- runStateT (liftRel y) m1
  v <- mkOr [x', y']
  put m
  return v


query :: MonadZ3 z3 => Expr -> StateT (Map.Map Expr AST) z3 (Maybe AST)
query x = do
  m <- get
  return $ x `Map.lookup` m

queries :: MonadZ3 z3 => [Expr] -> StateT (Map.Map Expr AST) z3 [AST]
queries es = do
  m <- get
  return $ mapMaybe (`Map.lookup` m) es


constraint :: MonadZ3 z3 => [Rel] -> StateT (Map.Map Expr AST) z3 ()
constraint rels = do
  m <- get
  (rs, m') <- runStateT (liftRels rels) m
  put m'
  assert =<< mkAnd rs


-- | Utility function
runZ3 :: StateT (Map.Map k a) Z3 b -> IO b
runZ3 prog = fst <$> evalZ3 (prog `runStateT` Map.empty)

returnInt :: MonadZ3 z3 => Expr -> StateT (Map.Map Expr AST) z3 (Maybe (String, Integer))
returnInt e@(EVar s) = do
  x <- query e
  case x of
    Nothing -> return Nothing
    Just x' -> do
      (_, v) <- withModel $ \m -> evalInt m x'
      case v of
        Nothing -> return Nothing
        Just v' -> case v' of
          Nothing  -> return Nothing
          Just v'' -> return (Just (s, v''))
returnInt _ = error "EVar is required."

returnInts :: MonadZ3 z3 => [String] -> StateT (Map.Map Expr AST) z3 [(String, Integer)]
returnInts names = do
  xs <- queries $ map EVar names
  fmap (maybe [] (zip names) . snd) $ withModel $ \m ->
    catMaybes <$> mapM (evalInt m) xs
