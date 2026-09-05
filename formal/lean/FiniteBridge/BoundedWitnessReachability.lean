import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.ReachabilityWitness
import FiniteBridge.TransitionValidChain

namespace FiniteBridge

/-- A bounded witness certifies the corresponding reflexive-transitive reachability. -/
theorem boundedWitness_to_reflTransGen
    {n : Nat} {r : Transition n} {start target : State n} {xs : List (State n)}
    (hw : BoundedWitness r start target xs) :
    Relation.ReflTransGen r start target := by
  rcases hw with ⟨hne, hhead, hlast, _, hvalid, _⟩
  have hchain : List.IsChain (fun a b => r a b) xs :=
    isChain_of_transitionValid hvalid
  exact chainWitness_to_reflTransGen ⟨hne, hhead, hlast, hchain⟩

end FiniteBridge
