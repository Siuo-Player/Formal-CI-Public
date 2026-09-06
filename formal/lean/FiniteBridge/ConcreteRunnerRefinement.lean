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
  simp [encodedSearchState, concreteInitial, SearchState.initial]

/-- Encoding the frontier produced by one concrete step agrees with the
abstract executable expansion. -/
theorem encoded_concreteNextFrontier_eq_executable
    (state : ConcreteSearchState ConcreteState) :
    (encodedSearchState adapter (concreteStep adapter state)).frontier =
      SearchState.executableNextFrontier (r := r)
        (encodedSearchState adapter state) := by
  ext t
  constructor
  · intro ht
    change t ∈ (concreteNextFrontier adapter state).image adapter.encode at ht
    rcases Finset.mem_image.mp ht with ⟨u, hu, rfl⟩
    change u ∈ concreteNextFrontier adapter state at hu
    rcases Finset.mem_sdiff.mp hu with ⟨hu, hu_notvisited⟩
    rcases Finset.mem_biUnion.mp hu with ⟨cs, hcs, hsucc⟩
    have hcs_encoded : adapter.encode cs ∈
        (encodedSearchState adapter state).frontier := by
      exact Finset.mem_image.mpr ⟨cs, hcs, rfl⟩
    have hsuccessor : r (adapter.encode cs) (adapter.encode u) := by
      rw [← adapter.mem_successors_iff]
      exact hsucc
    have hencoded_notvisited : adapter.encode u ∉
        (encodedSearchState adapter state).visited := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨v, hv, hvenc⟩
      have huv : u = v := by simpa using hvenc
      exact hu_notvisited (by simpa [huv] using hv)
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_biUnion.mpr ⟨adapter.encode cs, hcs_encoded, by
          simpa [SearchState.executableSuccessors] using hsuccessor⟩,
        hencoded_notvisited⟩
  · intro ht
    change t ∈
      SearchState.executableNextFrontier (r := r)
        (encodedSearchState adapter state) at ht
    rcases Finset.mem_sdiff.mp ht with ⟨ht_next, ht_notvisited⟩
    rcases Finset.mem_biUnion.mp ht_next with ⟨s, hs, hst⟩
    rcases Finset.mem_image.mp hs with ⟨cs, hcs, hcsenc⟩
    have hst' : r (adapter.encode cs) t := by
      simpa [SearchState.executableSuccessors] using hst
    have hct : adapter.encode.symm t ∈ adapter.successors cs := by
      rw [adapter.mem_successors_iff]
      simpa using hst'
    have hnotconcrete : adapter.encode.symm t ∉ state.visited := by
      intro hv
      apply ht_notvisited
      exact Finset.mem_image.mpr ⟨adapter.encode.symm t, hv, by simp⟩
    have hconcrete_next : adapter.encode.symm t ∈ concreteNextFrontier adapter state := by
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_biUnion.mpr ⟨cs, hcs,
          Finset.mem_image.mpr ⟨adapter.encode.symm t, hct, by simp⟩⟩,
          hnotconcrete⟩
    exact Finset.mem_image.mpr ⟨adapter.encode.symm t, hconcrete_next, by simp⟩

/-- Encoding the entire concrete one-step state agrees with the abstract
executable one-step search. -/
theorem encoded_concreteStep_eq_executableStep
    (state : ConcreteSearchState ConcreteState) :
    encodedSearchState adapter (concreteStep adapter state) =
      SearchState.executableStep (r := r) (encodedSearchState adapter state) := by
  ext t
  · exact encoded_concreteNextFrontier_eq_executable adapter state
  · simp only [encodedSearchState, concreteStep, SearchState.executableStep]
    rw [encoded_concreteNextFrontier_eq_executable adapter state]
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
      simp only [concreteRun]
      rw [encoded_concreteStep_eq_executableStep]
      exact congrArg (SearchState.executableStep (r := r)) (ih state)

end

end ConcreteSearchAdapter
end FiniteBridge
