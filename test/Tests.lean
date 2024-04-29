import Clingo
open Lean

def test_version : IO Unit := do
   let ⟨ major, minor, revision ⟩ <- Clingo.version
   println! s!"clingo version {major}.{minor}.{revision}"

def test_signature : IO Unit := do
   let Except.ok test <- Clingo.Signature.mk "random" 0 | return ()
   
   println! s!"signature is {test} name is {Clingo.Signature.name
   test}, arity is {Clingo.Signature.arity test}, is_positive
   {Clingo.Signature.isPositive test}, refl eq {test == test},
   {test.hash}"

def test_symbol : IO Unit := do
let sym <- Clingo.Symbol.mk_number 1000
   println! "made a number symbol {sym}"
   println! "the number is {sym.number?}"
   println! "type is {repr sym.type}"

   let sym <- Clingo.Symbol.mk_infimum
   println! "made a infimum symbol {sym}"
   println! "type is {repr sym.type}"

   let sym <- Clingo.Symbol.mk_supremum
   println! "made a supremum symbol {sym}"
   println! "type is {repr sym.type}"

   let sym <- Clingo.Symbol.mk_string "hello"
   println! "made a string symbol {sym}"
   println! "the string is {sym.string?}"
   println! "type is {repr sym.type}"

   let sym <- Clingo.Symbol.mk_id "hello" true
   println! "made a id symbol {sym}"
   println! "type is {repr sym.type}"
   println! "hash is {sym.hash}"

   let sym <- Clingo.Symbol.mk_fun "hello" #[sym] true
   println! "made a fun symbol {sym}"
   println! "the name is {sym.name?}"
   println! "args are {sym.args?}"
   println! "type is {repr sym.type}"

def my_callback (_evt : Clingo.SolveEvent) : IO Bool := do
  match _evt with
  | Clingo.SolveEvent.ModelFound none => println! "found a model (none)"
  | Clingo.SolveEvent.ModelFound (some m) =>
       println! "found a model (some)"
       let symbols := m.symbols
       for sym in Array.toList symbols do
           println! "{sym}"
  | Clingo.SolveEvent.StatsUpdated _s1 _s2 => do println! "stats updated"
  | Clingo.SolveEvent.Finished res => do println! "search finished {repr res}"

  return true


def main : IO Unit := do
   -- let _ <- Clingo.test (Except.error 3 : Except UInt32 UInt32)
   
   let Except.ok control <- Clingo.Control.mk (args := #[]) | throw (IO.userError "failed to create control")

   let Except.ok () <- control.load "./test/test.clingo" | throw (IO.userError "failed to load test file")

   let Except.ok () <- control.add "base" #[] "p(b)." | throw (IO.userError "failed to load expression")

   let Except.ok _handle <- control.solve Clingo.SolveMode.Neither (#[] : Array Clingo.Literal) my_callback | throw (IO.userError "failed to solve")

   println! s!"finished!"
