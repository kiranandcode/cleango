import Clingo.Types
import Clingo.SolveHandle
import Clingo.Ast
open Lean

private def max_uint64 := (UInt64.shiftLeft 1 63) + ((UInt64.shiftLeft 1 63) - 2)

namespace Clingo
namespace ProgramBuilder

@[extern "lean_clingo_program_builder_begin"]
private opaque begin_modify: @& ProgramBuilder -> IO Unit


@[extern "lean_clingo_program_builder_end"]
private opaque end_modify: @& ProgramBuilder -> IO Unit


@[extern "lean_clingo_program_builder_add"]
opaque addStatement: @& ProgramBuilder -> @& Ast.Statement -> IO Unit

def addStatements (pb: @& ProgramBuilder) (stmts: List Ast.Statement) : IO Unit :=
   for stmt in stmts do
      pb.addStatement stmt
   


end ProgramBuilder

namespace Control

@[extern "lean_clingo_control_mk_unsafe"]
private opaque mk_unsafe : @& Array String -> Logger -> UInt64 ->  IO Control

@[extern "lean_clingo_control_mk_safe"]
private opaque mk_safe : @& Array String -> Logger -> UInt64 ->  IO (Except Error Control)

def mk(args : @& Array String := #[]) (logger : Logger := fun _ _ => return ()) (limit : UInt64 := max_uint64) :=
  mk_safe args logger limit

def mk! (args : @& Array String := #[]) (logger : Logger := fun _ _ => return ()) (limit : UInt64 := max_uint64) :=
  mk_unsafe args logger limit

@[extern "lean_clingo_control_load"]
opaque load: @& Control -> @& String -> IO (Except (Prod Error String) Unit)

@[extern "lean_clingo_control_add"]
opaque add : @& Control -> (name : @& String) -> (params: @& Array String) -> (program: @& String) -> IO (Except Error Unit)

@[extern "lean_clingo_control_ground"]
opaque ground : @& Control -> (parts: @& Array (@& Part)) -> (callback: @& GroundCallback) -> IO (Except Error Unit)

@[extern "lean_clingo_solve"]
opaque solve: @& Control -> SolveMode -> @& Array Literal -> SolveEventCallback -> IO (Except Error SolveHandle)

@[extern "lean_clingo_control_statistics"]
opaque statistics : @& Control -> IO (Except Error Statistics)

@[extern "lean_clingo_control_interrupt"]
opaque interrupt : @& Control -> IO Unit

instance : Repr Control where
   reprPrec _ _ := s!"(Clingo.Control.mk)"

@[extern "lean_clingo_control_program_builder"]
private opaque programBuilder: @& Control -> IO ProgramBuilder

def withProgramBuilder (ctrl : Control) (f : ProgramBuilder -> IO A) : IO A := do
    let pb <- ctrl.programBuilder
    pb.begin_modify
    let res <- f pb
    pb.end_modify
    return res

end Control

end Clingo
