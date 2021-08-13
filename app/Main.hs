module Main where

import MyLib
import Z3.Monad

main :: IO ()
main = evalZ3 script >>= \mbSol ->
  case mbSol of
    Nothing  -> error "No solution found."
    Just sol -> putStr "Solution: " >> print sol
