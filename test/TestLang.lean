import Clingo
open Lean

open Clingo.Lang

def main : IO Unit := do
   println! "example: {clingo!(1)}"
   println! "example: {clingo!(-x)}"
   println! "example: {clingo!(f(p(x), q(x), d(x)))}"
   println! "language!!"

