import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- A witness with exactly two states has exactly one edge. -/
theorem two_state_witness_one_edge
    {n : Nat} {r : Transition n} {start target : State n}
    {xs : List (State n)}
    (hw : BoundedWitness r start target xs)
    (hlen : xs.length = 2) :
    xs.length - 1 = 1 := by
  omega

/-- Any two-state bounded witness connects distinct positions in its list. -/
theorem two_state_witness_has_transition
    {n : Nat} {r : Transition n} {start target : State n}
    {x y : State n}
    (hw : BoundedWitness r start target [x, y]) :
    r x y := by
  rcases hw with ⟨_, _, _, _, hvalid, _⟩
  simpa [TransitionValid] using hvalid.1

end FiniteBridge
