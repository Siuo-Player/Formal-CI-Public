import Mathlib
import FiniteBridge.BoundedReachability
import FiniteBridge.BoundedWitnessReachability

namespace FiniteBridge

/-- A finite bounded witness exists exactly when the endpoints are reachable. -/
theorem boundedWitness_iff_reflTransGen
    {n : Nat} {r : Transition n} {start target : State n} :
    (∃ xs : List (State n), BoundedWitness r start target xs) ↔
      Relation.ReflTransGen r start target := by
  constructor
  · rintro ⟨xs, hw⟩
    exact boundedWitness_to_reflTransGen hw
  · intro hreach
    exact boundedWitness_of_reflTransGen hreach

end FiniteBridge
