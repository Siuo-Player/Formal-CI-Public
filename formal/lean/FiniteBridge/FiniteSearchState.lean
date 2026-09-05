import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- The finite search frontier contains states discovered for the first time.
`visited` contains every state already discovered, including the current frontier. -/
structure SearchState (n : Nat) (r : Transition n) where
  frontier : Finset (State n)
  visited : Finset (State n)
  frontier_subset_visited : frontier ⊆ visited

namespace SearchState

section

variable {n : Nat} {r : Transition n}

/-- All one-step successors of a state in the finite universe.
This semantic relation is arbitrary, so enumeration uses classical decidability and is
therefore intentionally noncomputable until an executable transition representation is introduced. -/
noncomputable def successors (s : State n) : Finset (State n) := by
  classical
  exact Finset.univ.filter (fun t => r s t)

/-- States discovered from the current frontier but not visited before. -/
noncomputable def nextFrontier (state : SearchState n r) : Finset (State n) := by
  classical
  exact state.frontier.biUnion (fun s => successors (r := r) s) \\ state.visited

/-- One breadth-oriented exploration step. -/
noncomputable def step (state : SearchState n r) : SearchState n r := by
  classical
  let frontier' := nextFrontier (r := r) state
  let visited' := state.visited ∪ frontier'
  have hsubset : frontier' ⊆ visited' := by
    intro x hx
    exact Finset.mem_union_right _ hx
  exact ⟨frontier', visited', hsubset⟩

/-- Initial search state: the start state is both frontier and visited. -/
def initial (start : State n) : SearchState n r := by
  exact ⟨{start}, {start}, by intro x hx; simpa using hx⟩

theorem step_frontier_subset_visited (state : SearchState n r) :
    (step (r := r) state).frontier ⊆ (step (r := r) state).visited := by
  exact (step (r := r) state).frontier_subset_visited

theorem step_visited_monotone (state : SearchState n r) :
    state.visited ⊆ (step (r := r) state).visited := by
  intro x hx
  exact Finset.mem_union_left _ hx

theorem step_frontier_disjoint_old_visited (state : SearchState n r) :
    Disjoint (step (r := r) state).frontier state.visited := by
  classical
  unfold step nextFrontier
  simp [Finset.disjoint_left]

theorem initial_frontier_subset_visited (start : State n) :
    (initial (r := r) start).frontier ⊆ (initial (r := r) start).visited := by
  exact (initial (r := r) start).frontier_subset_visited

end

end SearchState

end FiniteBridge
