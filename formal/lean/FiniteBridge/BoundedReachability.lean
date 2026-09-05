import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.ReachabilityWitness
import FiniteBridge.SimpleWitness
import FiniteBridge.TransitionValidChain

namespace FiniteBridge

/-- A directed list chain is exactly transition-valid for the recursive witness predicate. -/
theorem transitionValid_of_isChain
    {n : Nat} {r : Transition n} {xs : List (State n)}
    (hchain : List.IsChain (fun a b => r a b) xs) :
    TransitionValid r xs := by
  induction xs with
  | nil => simp [TransitionValid]
  | cons x xs ih =>
      cases xs with
      | nil => simp [TransitionValid]
      | cons y ys =>
          simp only [TransitionValid]
          rcases (List.isChain_cons_iff (fun a b => r a b) x (y :: ys)).1 hchain with
            ⟨z, zs, hrel, htail, heq⟩
          cases heq
          exact ⟨hrel, ih htail⟩

/-- Every reachable pair of finite states has an endpoint-preserving bounded witness. -/
theorem boundedWitness_of_reflTransGen
    {n : Nat} {r : Transition n} {start target : State n}
    (hreach : Relation.ReflTransGen r start target) :
    ∃ xs : List (State n), BoundedWitness r start target xs := by
  rcases reflTransGen_to_simpleChainWitness hreach with
    ⟨xs, hne, hhead, hlast, hsimple, hchain⟩
  have hvalid : TransitionValid r xs := transitionValid_of_isChain hchain
  exact ⟨xs, boundedWitness_of_simplePath hne hhead hlast hsimple hvalid⟩

/-- The finite witness length is bounded by the number of available states. -/
theorem reachable_has_edge_bound
    {n : Nat} {r : Transition n} {start target : State n}
    (hreach : Relation.ReflTransGen r start target) :
    ∃ xs : List (State n),
      BoundedWitness r start target xs ∧
      xs.length - 1 ≤ n - 1 := by
  rcases boundedWitness_of_reflTransGen hreach with ⟨xs, hw⟩
  rcases hw with ⟨hne, hhead, hlast, hsimple, hvalid, hbound⟩
  exact ⟨xs, ⟨hne, hhead, hlast, hsimple, hvalid, hbound⟩, hbound⟩

end FiniteBridge
