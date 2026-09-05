import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.ReachabilityWitness

namespace FiniteBridge

/-- A bounded witness contains an explicit non-empty chain witness. -/
theorem boundedWitness_to_chainWitness
    {n : Nat} {r : Transition n} {start target : State n} {xs : List (State n)}
    (hw : BoundedWitness r start target xs) :
    ChainWitness r start target xs := by
  rcases hw with ⟨hne, hhead, hlast, _, hvalid, _⟩
  have hchain : List.IsChain r xs := by
    induction xs with
    | nil => simp [List.isChain_nil]
    | cons x xs ih =>
        cases xs with
        | nil => simp [List.isChain_singleton]
        | cons y ys =>
            have hrel : r x y := by
              simpa [TransitionValid] using hvalid.1
            have htail : TransitionValid r (y :: ys) := by
              simpa [TransitionValid] using hvalid.2
            apply (List.isChain_cons_iff r x (y :: ys)).2
            exact Or.inr ⟨y, ys, hrel, ih htail, rfl⟩
  exact ⟨hne, hhead, hlast, hchain⟩

end FiniteBridge
