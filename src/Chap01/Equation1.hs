module Chap01.Equation1 where

import Control.Arrow (first)
import Control.Monad (foldM)
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Traversable as T
import GHC.Real

import Z3.Monad

import Language

{- |
>>> evalZ3 sample
Just [1, -2, -2]
-}
{-
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
-}
{- |
>>> runZ3 simple
Just [1,-2,-2]
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

{-- | TODO: EVar を EIVar とかして Typable にしつつ evalReal などを呼ぶようにしたい
query m e@(EVar var) o = do
  let Just x = Map.lookup e m
  evalInt o x
--}


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
