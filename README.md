# CLeanGo - Bindings to libclingo for Lean 4

This repository includes bindings to the Clingo ASP programming system
for the Lean 4 Theorem Prover.

The bindings are currently work in progress, but the final goal is to
have a DSL from which you can write Clingo queries in Lean and have
then sent directly to Clingo and their results returned in a Lean
format.

Using: https://github.com/Anderssorby/SDL.lean/blob/main/bindings/sdl2-shim.c and https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h for reference

Requires Clingo 5.4.0 (important, as the FFI has changed in newer releases).

Example file:

```lean
def main : IO Unit := do

   let control <- Clingo.makeControl

   add_clingo_query! control :

     p(X) :- q(X).
     q(a).
     q(b).


   Clingo.ground control
   Clingo.solve control

   println! "finished!"
```

