import Mathlib
import FiniteBridge.BoundedReachability
import FiniteBridge.BoundedReachabilityFuel
import FiniteBridge.FiniteSearchState

namespace FiniteBridge
namespace SearchState

section

variable {n : Nat} {r : Transition n} {start target current : State n}

/-- Every discovered state's outgoing transitions are either already discovered or
still represented by the current frontier. This is the invariant that connects the
visited set to one-step expansion. -/
def SearchInvariant (state : SearchState n r) : Prop :=
  ∀ ⦃s t : State n⦄,
    s ∈ state.visited → r s t →
      t ∈ state.visited ∨ s ∈ state.frontier

/-- A frontier state exposes every undiscovered successor to the next visited set. -/
theorem mem_step_visited_of_frontier
    {state : SearchState n r}
    (hs : s ∈ state.frontier)
    (hst : r s t) :
    t ∈ (step (r := r) state).visited := by
  classical
  by_cases ht : t ∈ state.visited
  · exact Finset.mem_union_left _ ht
  · apply Finset.mem_union_right state.visited
    unfold nextFrontier
    rw [Finset.mem_sdiff]
    constructor
    · simp only [Finset.mem_biUnion]
      exact ⟨s, hs, by simp [successors, hst]⟩
    · exact ht

/-- The initial state satisfies the search invariant. -/
theorem searchInvariant_initial (start : State n) :
    SearchInvariant (initial (r := r) start) := by
  intro s t hs hst
  have hs' : s = start := by simpa [initial] using hs
  subst s
  exact Or.inr (by simp [initial])

/-- One search step preserves the invariant. -/
theorem searchInvariant_step
    {state : SearchState n r}
    (hinv : SearchInvariant state) :
    SearchInvariant (step (r := r) state) := by
  intro s t hs hst
  rcases Finset.mem_union.mp hs with hsold | hsnew
  · rcases hinv hsold hst with htold | hsfront
    · exact Or.inl (Finset.mem_union_left _ htold)
    · exact Or.inl (mem_step_visited_of_frontier hsfront hst)
  · exact Or.inr hsnew

/-- The invariant holds at every round from the initial state. -/
theorem searchInvariant_run_initial (start : State n) :
    ∀ fuel, SearchInvariant (run (r := r) fuel (initial start)) := by
  intro fuel
  induction fuel with
  | zero => exact searchInvariant_initial start
  | succ fuel ih =>
      simpa [run] using searchInvariant_step ih

/-- Visited sets are monotone as the search is run for more rounds. -/
theorem run_visited_mono_of_le (start : State n) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') :
    (run (r := r) fuel (initial start)).visited ⊆
      (run (r := r) fuel' (initial start)).visited := by
  induction hle with
  | refl => exact subset_rfl
  | @step fuel fuel' hle ih =>
      intro x hx
      exact step_visited_monotone (run (r := r) fuel' (initial start)) (ih hx)

/-- A non-empty finite transition chain is witnessed by `ReachWithin` at its exact
number of edges. This is the bridge from the witness representation to the runner's fuel. -/
theorem reachWithin_of_nonempty_chain
    {xs : List (State n)}
    (hne : xs ≠ [])
    (hchain : List.IsChain r xs) :
    ReachWithin r (xs.head hne) (xs.length - 1) (xs.getLast hne) := by
  cases xs with
  | nil => contradiction
  | cons a rest =>
      cases rest with
      | nil =>
          simp at hne ⊢
          exact ReachWithin.self
      | cons b rest =>
          have hab : r a b := hchain.head
          have htail : List.IsChain r (b :: rest) := hchain.tail
          have hneTail : (b :: rest) ≠ [] := by simp
          have hrec := reachWithin_of_nonempty_chain hneTail htail
          have hfirst : ReachWithin r a 1 b := by
            have hself : ReachWithin r a 0 a := ReachWithin.self
            simpa using ReachWithin.step hself hab
          have hconcat := ReachWithin.trans hfirst hrec
          convert hconcat using 1 <;> simp <;> omega

/-- Every `ReachWithin` target is discovered after the corresponding number of
finite expansion rounds. This is the core coverage theorem for the concrete search state. -/
theorem reachWithin_mem_run
    {fuel : Nat}
    (hreach : ReachWithin r start fuel target) :
    target ∈ (run (r := r) fuel (initial start)).visited := by
  induction hreach with
  | self =>
      simp [initial]
  | @step fuel current target hreach hstep ih =>
      have hinv := searchInvariant_run_initial (r := r) start fuel
      rcases hinv ih hstep with ht | hfront
      · exact step_visited_monotone (run (r := r) fuel (initial start)) ht
      · simpa [run] using mem_step_visited_of_frontier hfront hstep

/-- Every reachable target in the finite state space is discovered within `n - 1`
rounds. This closes the ReachWithin-to-boundary coverage implication required by G6. -/
theorem reachable_mem_run_n_sub_one
    (hreach : Relation.ReflTransGen r start target) :
    target ∈ (run (r := r) (n - 1) (initial start)).visited := by
  rcases reachable_has_edge_bound hreach with ⟨xs, hw⟩
  rcases hw with ⟨hne, hhead, hlast, hsimple, hvalid, hbound⟩
  have hchain : List.IsChain r xs := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        cases xs with
        | nil => simp
        | cons y ys =>
            exact ⟨by simpa [TransitionValid] using hvalid |>.1, by
              exact ih (by simpa [TransitionValid] using hvalid |>.2)⟩
  have hwithin : ReachWithin r start (xs.length - 1) target := by
    have htmp := reachWithin_of_nonempty_chain (r := r) hne hchain
    simpa [hhead, hlast] using htmp
  have hfound := reachWithin_mem (r := r) hwithin
  exact run_visited_mono_of_le (r := r) start hbound hfound

end
end SearchState
end FiniteBridge
