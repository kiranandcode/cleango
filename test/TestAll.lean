import Clingo
open Lean

open Clingo.Lang

def handle_solve_event (_evt : Clingo.SolveEvent) : IO Bool := do
  match _evt with
  | Clingo.SolveEvent.ModelFound (some m) =>
       println! "found model: "
       let symbols := m.symbols
       for sym in Array.toList symbols do
           println! " - {sym}"
       return Bool.true
  | _ => return Bool.true

def Clingo.ground (control: Clingo.Control) : IO Unit := do
   let Except.ok () <-
      control.ground
        #[Clingo.Part.mk "base" #[]] (fun _ _ _ _ => pure Bool.true) | throw (IO.userError "failed to load expression")

def Clingo.solve (control: Clingo.Control) : IO Unit := do
   let Except.ok handle <- control.solve Clingo.SolveMode.Neither (#[] : Array Clingo.Literal) handle_solve_event
         | throw (IO.userError "failed to solve")
   let _ <- handle.wait (-1.0)

def Clingo.makeControl : IO Clingo.Control := do
   let Except.ok control <- Clingo.Control.mk (args := #[]) | throw (IO.userError "failed to create control")
   return control


def main : IO Unit := do

   let control <- Clingo.makeControl

   add_clingo_query! control :

     p(X) :- q(X).
     q(a).
     q(b).


   Clingo.ground control
   Clingo.solve control

   println! "finished!"

