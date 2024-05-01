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
   let sym := Clingo.Symbol.mk_number 1000
   println! "made a number symbol {sym}"
   println! "the number is {sym.number?}"
   println! "type is {repr sym.type}"

   let sym := Clingo.Symbol.mk_infimum
   println! "made a infimum symbol {sym}"
   println! "type is {repr sym.type}"

   let sym := Clingo.Symbol.mk_supremum
   println! "made a supremum symbol {sym}"
   println! "type is {repr sym.type}"

   let sym := Clingo.Symbol.mk_string "hello"
   println! "made a string symbol {sym}"
   println! "the string is {sym.string?}"
   println! "type is {repr sym.type}"

   let sym := Clingo.Symbol.mk_id "a" true
   println! "made a id symbol {sym}"
   println! "type is {repr sym.type}"
   println! "hash is {sym.hash}"

   let sym := Clingo.Symbol.mk_fun "hello" #[sym] true
   println! "made a fun symbol {sym}"
   println! "the name is {sym.name?}"
   println! "args are {sym.args?}"
   println! "type is {repr sym.type}"



def test_control : IO Unit := do
   let my_callback (_evt : Clingo.SolveEvent) : IO Bool := do
       match _evt with
       | Clingo.SolveEvent.ModelFound none => println! "found a model (none)"
       | Clingo.SolveEvent.ModelFound (some m) =>
            println! "found a model (some)"
            let size := m.size Clingo.Model.FilterFlags.selectAll
            println! "clingo says there are {size} symbols"
            let symbols := m.symbols
            println! "retrieved {symbols.size} symbols"
            for sym in Array.toList symbols do
                println! "{repr sym.repr} {sym}"
            println! "retrieved {m.costs.size} costs"
            for cost in m.costs do
                println! "{cost}"
       | Clingo.SolveEvent.StatsUpdated _s1 _s2 => do
           println! "stats updated"
           println! "root stat s1 {repr (_s1.type _s1.root)}"
           println! "root stat s2 {repr (_s1.type _s2.root)}"
       | Clingo.SolveEvent.Finished res => do
           println! "search finished {repr res}"

       return true
   let Except.ok control <- Clingo.Control.mk (args := #[]) | throw (IO.userError "failed to create control")
   let Except.ok () <- control.load "./test/test.clingo" | throw (IO.userError "failed to load test file")
   let Except.ok () <- control.add "main" #[] "p(b). q(A) :- p(A)." | throw (IO.userError "failed to load expression")
   let Except.ok () <- control.ground #[Clingo.Part.mk "base" #[]] (fun loc name args ret => pure true) | throw (IO.userError "failed to load expression")
   let Except.ok handle <- control.solve Clingo.SolveMode.Neither (#[] : Array Clingo.Literal) my_callback | throw (IO.userError "failed to solve")
   let _ <- handle.wait (-1.0)
   let Except.ok _model <- handle.model | throw (IO.userError "failed to retrieve model")

def test_program_builder : IO Unit := open Clingo.Ast in do
   let my_callback (_evt : Clingo.SolveEvent) : IO Bool := do
       match _evt with
       | Clingo.SolveEvent.ModelFound none => println! "found a model (none)"
       | Clingo.SolveEvent.ModelFound (some m) =>
            println! "found a model (some)"
            let size := m.size Clingo.Model.FilterFlags.selectAll
            println! "clingo says there are {size} symbols"
            let symbols := m.symbols
            println! "retrieved {symbols.size} symbols"
            for sym in Array.toList symbols do
                println! "{repr sym.repr} {sym}"
            println! "retrieved {m.costs.size} costs"
            for cost in m.costs do
                println! "{cost}"
       | Clingo.SolveEvent.StatsUpdated _s1 _s2 => do
           println! "stats updated"
           println! "root stat s1 {repr (_s1.type _s1.root)}"
           println! "root stat s2 {repr (_s1.type _s2.root)}"
       | Clingo.SolveEvent.Finished res => do
           println! "search finished {repr res}"

       return true
   let Except.ok control <- Clingo.Control.mk (args := #[]) | throw (IO.userError "failed to create control")
   let location := Clingo.Location.mk "beginFile" "endFile" 1 2 3 4
   control.withProgramBuilder fun pb => do
      println! "retrieved and began pb modifications"

      pb.addStatement $ ⟨
         location,
         .Rule ⟨
          location,
         .Literal ⟨ location, .None, .Symbolic ⟨
            location,
             .Function "p" #[⟨ location, .Variable "X" ⟩ ]
           ⟩⟩ ⟩
           #[⟨
               location,
               .None,
               .Literal ⟨ location, .None, .Symbolic ⟨
                    location,
                     .Function "q" #[⟨ location, .Variable "X" ⟩ ]
                    ⟩⟩ 
              ⟩]⟩;
      pb.addStatement $ ⟨
         location,
         .Rule ⟨
          location,
         .Literal ⟨ location, .None, .Symbolic ⟨
            location,
             .Symbol (Clingo.Symbol.mk (.Function "q" #[(.Variable "a")] true) )
           ⟩⟩ ⟩
           #[]⟩;
      pb.addStatement $ ⟨
         location,
         .Rule ⟨
          location,
         .Literal ⟨ location, .None, .Symbolic ⟨
            location,
             .Symbol (Clingo.Symbol.mk (.Function "q" #[(.Variable "b")] true) )
           ⟩⟩ ⟩
           #[]⟩;

      println! "finished"
   let Except.ok () <- control.ground #[Clingo.Part.mk "base" #[]] (fun loc name args ret => pure true) | throw (IO.userError "failed to load expression")
   let Except.ok handle <- control.solve Clingo.SolveMode.Neither (#[] : Array Clingo.Literal) my_callback | throw (IO.userError "failed to solve")
   let _ <- handle.wait (-1.0)

def main : IO Unit := do
   test_version
   test_signature
   test_symbol
   test_control
   test_program_builder
   println! s!"finished!"
