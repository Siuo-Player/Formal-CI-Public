import Mathlib
import FiniteBridge.ConcreteSearchAdapter

namespace FiniteBridge
namespace ConcreteSearchAdapter

section

variable {ConcreteState : Type*} {n : Nat} {r : Transition n}
  [DecidableRel r] [Fintype ConcreteState] [DecidableEq ConcreteState]
  (adapter : ConcreteSearchAdapter ConcreteState n r)

/-- Concrete search state over the implementation state space. -/
structure ConcreteSearchState (ConcreteState : Type*) where
  frontier : Finset ConcreteState
  visited : Finset ConcreteState
  frontier_subset_visited : frontier ⊆ visited

/-- Initial concrete search state containing exactly the start state. -/
def concreteInitial (start : ConcreteState) : ConcreteSearchState ConcreteState :=
  ⟨{start}, {start}, by intro x hx; simpa using hx⟩

/-- One concrete frontier expansion using the adapter-provided successor
enumerator. -/
def concreteNextFrontier
    (adapter : ConcreteSearchAdapter ConcreteState n r)
    (state : ConcreteSearchState ConcreteState) : Finset ConcreteState :=
  state.frontier.biUnion adapter.successors \ state.visited

/-- Concrete one-step search. -/
def concreteStep
    (adapter : ConcreteSearchAdapter ConcreteState n r)
    (state : ConcreteSearchState ConcreteState) : ConcreteSearchState ConcreteState := by
  let frontier' := concreteNextFrontier adapter state
  let visited' := state.visited ∪ frontier'
  have hsubset : frontier' ⊆ visited' := by
    intro x hx
    exact Finset.mem_union_right _ hx
  exact ⟨frontier', visited', hsubset⟩

/-- Encode a concrete search state into the abstract `SearchState` used by
G6. The frontier and visited sets are transported through the equivalence. -/
def encodedSearchState
    (adapter : ConcreteSearchAdapter ConcreteState n r)
    (state : ConcreteSearchState ConcreteState) : SearchState n r := by
  let frontier' := state.frontier.image adapter.encode
  let visited' := state.visited.image adapter.encode
  have hsubset : frontier' ⊆ visited' := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    exact Finset.mem_image.mpr ⟨u, state.frontier_subset_visited hu, rfl⟩
  exact ⟨frontier', visited', hsubset⟩

/-- Encoding the concrete initial state gives the abstract initial search
state for the encoded start. -/
theorem encoded_concreteInitial_eq_initial (start : ConcreteState) :
    encodedSearchState adapter (concreteInitial start) =
      SearchState.initial (r := r) (adapter.encode start) := by
  ext x <;> simp [encodedSearchState, concreteInitial, SearchState.initial]

/-- Encoding the frontier produced by one concrete step agrees with the
abstract executable expansion. -/
theorem encoded_concreteNextFrontier_eq_executable
    (state : ConcreteSearchState ConcreteState) :
    (encodedSearchState adapter (concreteStep adapter state)).frontier =
      SearchState.executableNextFrontier (r := r)
        (encodedSearchState adapter state) := by
  unfold encodedSearchState concreteStep concreteNextFrontier
  ext t
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨u, hu, _⟩
    rcases Finset.mem_sdiff.mp hu with ⟨hbi, hnew⟩
    rcases Finset.mem_biUnion.mp hbi with ⟨s, hs, hsu⟩
    rcases Finset.mem_image.mp hs with ⟨cs, hcs, hcsenc⟩
    rcases Finset.mem_biUnion.mp hsu with ⟨ct, hct, hctenc⟩
    have hsenc : s = adapter.encode cs := by
      simpa using hcsenc
    have htenc : u = adapter.encode ct := by
      simpa using hctenc
    have hst : r (adapter.encode cs) (adapter.encode ct) := by
      rw [← adapter.mem_successors_iff]
      simpa [hsenc, htenc] using hct.1
    have hfront : adapter.encode cs ∈
        (encodedSearchState adapter state).frontier := by
      exact Finset.mem_image.mpr ⟨cs, hcs, rfl⟩
    have htarget : adapter.encode ct ∉
        (encodedSearchState adapter state).visited := by
      intro hvisited
      rcases Finset.mem_image.mp hvisited with ⟨v, hv, hvenc⟩
      have hvc : adapter.encode ct = adapter.encode v := by
        calc
          adapter.encode ct = u := htenc.symm
          _ = v := by
            simpa [hvenc] using hnew
      have : ct = v := adapter.encode.injective hvc
      exact hct.2 (by simpa [this])
    exact Finset.mem_sdiff.mpr ⟨
      Finset.mem_biUnion.mpr ⟨adapter.encode cs, hfront, by simpa [hsenc, htenc] using hst⟩,
      htarget⟩
  · intro ht
    rcases Finset.mem_sdiff.mp ht with ⟨hnext, hnotvisited⟩
    rcases Finset.mem_biUnion.mp hnext with ⟨s, hs, hst⟩
    rcases Finset.mem_image.mp hs with ⟨cs, hcs, hcsenc⟩
    have hcsenc' : s = adapter.encode cs := by
      simpa using hcsenc
    have hrt : r (adapter.encode cs) t := by
      simpa [hcsenc'] using (SearchState.mem_executableSuccessors_iff (r := r) s t).mp hst
    have hct : adapter.encode.symm t ∈ adapter.successors cs := by
      rw [adapter.mem_successors_iff]
      simpa using hrt
    have hnotconcrete : adapter.encode.symm t ∉ state.visited := by
      intro hv
      apply hnotvisited
      exact Finset.mem_image.mpr ⟨adapter.encode.symm t, hv, by simp⟩
    exact Finset.mem_image.mpr ⟨adapter.encode.symm t,
      Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨cs, hcs,
        by exact Finset.mem_image.mpr ⟨adapter.encode.symm t, hct, by simp⟩⟩,
        hnotconcrete⟩,
      by simp⟩

/-- Encoding the entire concrete one-step state agrees with the abstract
executable one-step search. -/
theorem encoded_concreteStep_eq_executableStep
    (state : ConcreteSearchState ConcreteState) :
    encodedSearchState adapter (concreteStep adapter state) =
      SearchState.executableStep (r := r) (encodedSearchState adapter state) := by
  let a := encodedSearchState adapter (concreteStep adapter state)
  let b := SearchState.executableStep (r := r) (encodedSearchState adapter state)
  have hfront : a.frontier = b.frontier := by
    exact encoded_concreteNextFrontier_eq_executable adapter state
  have hvisited : a.visited = b.visited := by
    dsimp [a, b, encodedSearchState, concreteStep]
    rw [encoded_concreteNextFrontier_eq_executable adapter state]
  cases a with
  | mk afrontier avisited asubset =>
      cases b with
      | mk bfrontier bvisited bsubset =>
          dsimp at hfront hvisited
          cases hfront
          cases hvisited
          rfl

/-- Concrete bounded runner. -/
def concreteRun
    (adapter : ConcreteSearchAdapter ConcreteState n r) :
    Nat → ConcreteSearchState ConcreteState → ConcreteSearchState ConcreteState
  | 0, state => state
  | fuel + 1, state => concreteStep adapter (concreteRun adapter fuel state)

/-- Every concrete bounded run, after encoding, equals the abstract executable
runner. This is the refinement theorem needed to transport G6 coverage and
exhaustion to an implementation satisfying the adapter contract. -/
theorem encoded_concreteRun_eq_executableRun :
    ∀ fuel (state : ConcreteSearchState ConcreteState),
      encodedSearchState adapter (concreteRun adapter fuel state) =
        SearchState.executableRun fuel (encodedSearchState adapter state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      rfl
  | succ fuel ih =>
      intro state
      simp [concreteRun, encoded_concreteStep_eq_executableStep, ih]

end

end ConcreteSearchAdapter
end FiniteBridge
