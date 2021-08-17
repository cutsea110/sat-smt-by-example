module Chap01.Equation1 where

import Control.Monad.State
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
          | ETimes Expr Expr
          deriving (Eq, Ord, Show)
