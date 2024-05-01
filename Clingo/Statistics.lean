import Clingo.Types

open Lean

namespace Clingo
inductive StatisticsType where | Empty | Value | Array | Map
deriving Repr, Inhabited

namespace Statistics

@[extern "lean_clingo_statistics_root"]
opaque root: @& Statistics -> UInt64

@[extern "lean_clingo_statistics_type"]
opaque type: @& Statistics -> UInt64 -> StatisticsType

@[extern "lean_clingo_statistics_array_size"]
opaque arraySize: @& Statistics -> UInt64 -> USize

@[extern "lean_clingo_statistics_array_ref"]
opaque arrayRef: @& Statistics -> (key: UInt64) -> (offset: USize) -> UInt64

@[extern "lean_clingo_statistics_map_size"]
opaque mapSize: @& Statistics -> UInt64 -> USize

@[extern "lean_clingo_statistics_map_has_key"]
opaque mapHasKey?: @& Statistics -> (key: UInt64) -> (name : @& String) -> Bool

@[extern "lean_clingo_statistics_map_ref"]
opaque mapRef: @& Statistics -> (key: UInt64) -> (name : @& String) -> UInt64

@[extern "lean_clingo_statistics_value_get"]
opaque valueGet: @& Statistics -> (key: UInt64) -> Float

end Statistics

end Clingo
