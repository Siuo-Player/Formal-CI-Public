import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.SimpleWitness
import FiniteBridge.BoundedReachabilityFuel
import FiniteBridge.FiniteSearchState

namespace FiniteBridge
namespace SearchState

section

variable {n : Nat} {r : Transition n} {start target current : State n}

def SearchInvariant (state : SearchState n r) : Prop :=
  ∀ ⦃s t : State n⦄,
    s ∈ state.visited → r s t →
      t ∈ state.visited ∨ s ∈ state.frontier

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

theorem searchInvariant_initial (start : State n) :
    SearchInvariant (initial (r := r) start) := by
  intro s t hs hst
  have hs' : s = start := by simpa [initial] using hs
  subst s
  exact Or.inr (by simp [initial])

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

theorem searchInvariant_run_initial (start : State n) :
    ∀ fuel, SearchInvariant (run (r := r) fuel (initial start)) := by
  intro fuel
  induction fuel with
  | zero => exact searchInvariant_initial start
  | succ fuel ih =>
      simpa [run] using searchInvariant_step ih

theorem run_visited_mono_of_le (start : State n) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') :
    (run (r := r) fuel (initial start)).visited ⊆
      (run (r := r) fuel' (initial start)).visited := by
  induction fuel' generalizing fuel with
  | zero =>
      have : fuel = 0 := Nat.eq_zero_of_le_zero hle
      subst fuel
      exact subset_rfl
  | succ fuel' ih =>
      cases hle with
      | refl =>
          exact step_visited_monotone (run (r := r) fuel' (initial start))
      | step hle =>
          intro x hx
          exact step_visited_monotone (run (r := r) fuel' (initial start))
            (ih hle hx)

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
          have hab : r a b := List.IsChain.rel_head hchain
          have htail : List.IsChain r (b :: rest) := hchain.tail
          have hneTail : (b :: rest) ≠ [] := by simp
          have hrec := reachWithin_of_nonempty_chain hneTail htail
          have hfirst : ReachWithin r a 1 b := by
            have hself : ReachWithin r a 0 a := ReachWithin.self
            simpa using ReachWithin.step hself hab
          have hconcat := ReachWithin.trans hfirst hrec
          convert hconcat using 1 <;> simp <;> omega

theorem reachWithin_mem_run
    {fuel : Nat}
    (hreach : ReachWithin r start fuel target) :
    target ∈ (run (r := r) fuel (initial start)).visited := by
  induction hreach with
  | self =>
      change start ∈ ({start} : Finset (State n))
      simp
  | @step fuel current target hreach hstep ih =>
      have hinv := searchInvariant_run_initial (r := r) start fuel
      rcases hinv ih hstep with ht | hfront
      · exact step_visited_monotone (run (r := r) fuel (initial start)) ht
      · simpa [run] using mem_step_visited_of_frontier hfront hstep

theorem reachable_mem_run_n_sub_one
    (hreach : Relation.ReflTransGen r start target) :
    target ∈ (run (r := r) (n - 1) (initial start)).visited := by
  rcases reflTransGen_to_simpleChainWitness hreach with
    ⟨xs, hne, hhead, hlast, hsimple, hchain⟩
  have hbound : xs.length - 1 ≤ n - 1 :=
    simplePath_edge_count_le_state_count_sub_one hsimple hne
  have htmp := reachWithin_of_nonempty_chain (r := r) hne hchain
  have hwithin : ReachWithin r start (xs.length - 1) target := by
    simpa [hhead, hlast] using htmp
  have hfound := reachWithin_mem_run (r := r) hwithin
  exact run_visited_mono_of_le (r := r) start hbound hfound

end
end SearchState
end FiniteBridge
