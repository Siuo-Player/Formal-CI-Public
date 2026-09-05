import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.ZeroLengthBridge

namespace FiniteBridge

/-- A singleton witness has exactly zero edges. -/
theorem singleton_witness_has_zero_edges
    {n : Nat} {r : Transition n} (start : State n) :
    ([start] : List (State n)).length - 1 = 0 := by
  simp

/-- The canonical zero-edge witness is valid independently of the transition relation. -/
theorem zero_edge_witness_is_valid
    {n : Nat} {r : Transition n} (start : State n) :
    BoundedWitness r start start [start] := by
  exact singleton_boundedWitness start

end FiniteBridge
