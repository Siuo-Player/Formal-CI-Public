import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.ZeroLengthBridge
import FiniteBridge.SingletonCharacterization

namespace FiniteBridge

/-- A bounded witness is a singleton witness exactly when its endpoints coincide and
its list has length one. -/
theorem singleton_boundedWitness_iff
    {n : Nat} {r : Transition n} {start target : State n} :
    (∃ xs : List (State n), BoundedWitness r start target xs ∧ xs.length = 1) ↔
      start = target := by
  constructor
  · rintro ⟨xs, hw, hlen⟩
    exact singleton_witness_endpoints_equal xs hw hlen
  · intro hsame
    subst target
    exact zero_length_bridge_witness start

end FiniteBridge
