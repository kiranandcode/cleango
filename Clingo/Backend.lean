import Clingo.Types

open Lean

namespace Clingo
inductive ExternalType where | AssignFreely | AssignTrue | AsisgnFalse | Release

namespace Backend

-- @[extern "lean_clingo_backend_begin"]
-- opaque begin_modify: @& Backend -> IO Unit

-- @[extern "lean_clingo_backend_end"]
-- opaque end_modify: @& Backend -> IO Unit

-- @[extern "lean_clingo_backend_rule"]
-- opaque add_rule: @& Backend -> Bool -> Array Atom -> Array Literal -> IO Unit

-- @[extern "lean_clingo_backend_weighted_rule"]
-- opaque add_weighted_rule: @& Backend -> Bool -> Array Atom -> (weight: Int) -> (weighted_literals: Array (Literal × Int)) -> IO Unit

-- @[extern "lean_clingo_backend_minimize_constraint"]
-- opaque add_minimize_constraint: @& Backend -> (priority: Int) -> (weighted_literals: Array (Literal × Int)) -> IO Unit

-- @[extern "lean_clingo_backend_project"]
-- opaque add_projection_directive: @& Backend -> Array Atom -> IO Unit

-- @[extern "lean_clingo_backend_external"]
-- opaque add_external: @& Backend -> Atom -> ExternalType -> IO Unit

-- @[extern "lean_clingo_backend_assume"]
-- opaque add_assumptions: @& Backend -> Array Literal -> IO Unit

-- @[extern "lean_clingo_backend_add_atom"]
-- opaque add_atom: @& Backend -> Option Symbol -> IO Atom

end Backend

end Clingo
