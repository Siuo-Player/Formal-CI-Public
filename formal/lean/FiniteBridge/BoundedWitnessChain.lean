import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.ReachabilityWitness
import FiniteBridge.TransitionValidChain

namespace FiniteBridge

/-- A bounded witness contains an explicit non-empty chain witness. -/
theorem boundedWitness_to_chainWitness
    {n : Nat} {r : Transition n} {start target : State n} {xs : List (State n)}
    (hw : BoundedWitness r start target xs) :
    ChainWitness r start target xs := by
  rcases hw with ⟨hne, hhead, hlast, _, hvalid, _⟩
  have hchain : List.IsChain (fun a b => r a b) xs :=
    isChain_of_transitionValid hvalid
  exact ⟨hne, hhead, hlast, hchain⟩

end FiniteBridge
