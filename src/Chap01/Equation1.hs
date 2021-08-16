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
          | EPlus Expr Expr
          deriving (Eq, Ord, Show)

intVar :: MonadZ3 z3 => String -> State (Map.Map Expr (z3 AST)) (z3 AST)
intVar name = do
  m <- get
  let (mayVal, m') = Map.insertLookupWithKey (\ _ n _ -> n) (EVar name) (mkFreshIntVar name) m
  put m'
  return $ m' Map.! EVar name

plus :: MonadZ3 z3 => AST -> AST -> State (Map.Map AST (z3 AST))  (z3 AST)
x `plus` y = undefined

e1 :: MonadZ3 z3 => AST -> AST -> AST -> AST -> AST -> AST -> z3 AST
e1 x y z _1 _2 _3 = do
  t1 <- mkMul [_3, x]
  t2 <- mkMul [_2, y]
  t3 <- mkUnaryMinus z
  lhs <- mkAdd [t1,t2,t3]
  mkEq _1 lhs
