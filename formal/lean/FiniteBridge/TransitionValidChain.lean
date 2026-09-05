import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- Every recursively transition-valid list is an explicit relation chain. -/
theorem isChain_of_transitionValid
    {n : Nat} {r : Transition n} {xs : List (State n)}
    (hvalid : TransitionValid r xs) :
    List.IsChain (fun a b => r a b) xs := by
  induction xs with
  | nil =>
      simp [List.isChain_nil]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [TransitionValid, List.isChain_singleton]
      | cons y ys =>
          have hrel : r x y := by
            simpa [TransitionValid] using hvalid.1
          have htail : TransitionValid r (y :: ys) := by
            simpa [TransitionValid] using hvalid.2
          apply (List.isChain_cons_iff (fun a b => r a b) x (y :: ys)).2
          exact Or.inr ⟨y, ys, hrel, ih htail, rfl⟩

end FiniteBridge
