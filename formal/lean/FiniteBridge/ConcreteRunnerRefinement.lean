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
    rcases Finset.mem_image.mp ht with ⟨u, hu, hut⟩
    change u ∈ concreteNextFrontier adapter state at hu
    rcases Finset.mem_sdiff.mp hu with ⟨hbi, hnotvis⟩
    rcases Finset.mem_biUnion.mp hbi with ⟨s, hs, hsu⟩
    rcases Finset.mem_image.mp hs with ⟨cs, hcs, hcsenc⟩
    rcases Finset.mem_biUnion.mp hsu with ⟨ct, hct, hctenc⟩
    have hs_eq : s = adapter.encode cs := hcsenc.symm
    have hu_eq : u = adapter.encode ct := hut.symm
    subst s
    subst u
    have hrel : r (adapter.encode cs) (adapter.encode ct) :=
      (adapter.mem_successors_iff cs ct).mp hct
    have hfront : adapter.encode cs ∈
        (encodedSearchState adapter state).frontier := by
      exact Finset.mem_image.mpr ⟨cs, hcs, rfl⟩
    have hnotencoded : adapter.encode ct ∉
        (encodedSearchState adapter state).visited := by
      intro hv
      rcases Finset.mem_image.mp hv with ⟨v, hv', hvenc⟩
      have hev : adapter.encode ct = adapter.encode v := by
        exact hvenc.symm
      have hctv : ct = v := adapter.encode.injective hev
      exact hnotvis (by simpa [hctv])
    exact Finset.mem_sdiff.mpr ⟨
      Finset.mem_biUnion.mpr ⟨adapter.encode cs, hfront,
        (SearchState.mem_executableSuccessors_iff (r := r)
          (adapter.encode cs) (adapter.encode ct)).mpr hrel⟩,
      hnotencoded⟩
  · intro ht
    rcases Finset.mem_sdiff.mp ht with ⟨hbi, hnotvis⟩
    rcases Finset.mem_biUnion.mp hbi with ⟨s, hs, hst⟩
    rcases Finset.mem_image.mp hs with ⟨cs, hcs, hcsenc⟩
    have hrel : r (adapter.encode cs) t := by
      rw [hcsenc]
      exact (SearchState.mem_executableSuccessors_iff (r := r) s t).mp hst
    have hct : adapter.encode.symm t ∈ adapter.successors cs := by
      rw [adapter.mem_successors_iff]
      simpa using hrel
    have hnotconcrete : adapter.encode.symm t ∉ state.visited := by
      intro hv
      apply hnotvis
      exact Finset.mem_image.mpr ⟨adapter.encode.symm t, hv,
        adapter.encode.apply_symm_apply t⟩
    exact Finset.mem_image.mpr ⟨
      adapter.encode.symm t,
      Finset.mem_sdiff.mpr ⟨
        Finset.mem_biUnion.mpr ⟨cs, hcs,
          Finset.mem_image.mpr ⟨adapter.encode.symm t, hct,
            adapter.encode.apply_symm_apply t⟩⟩,
        hnotconcrete⟩,
      adapter.encode.apply_symm_apply t⟩

/-- Encoding the entire concrete one-step state agrees with the abstract
executable one-step search. -/
theorem encoded_concreteStep_eq_executableStep
    (state : ConcreteSearchState ConcreteState) :
    encodedSearchState adapter (concreteStep adapter state) =
      SearchState.executableStep (r := r) (encodedSearchState adapter state) := by
  have hfront := encoded_concreteNextFrontier_eq_executable adapter state
  have hvisited :
      (encodedSearchState adapter (concreteStep adapter state)).visited =
        (SearchState.executableStep (r := r) (encodedSearchState adapter state)).visited := by
    change (encodedSearchState adapter state).visited ∪
        (encodedSearchState adapter (concreteStep adapter state)).frontier =
      (encodedSearchState adapter state).visited ∪
        SearchState.executableNextFrontier (r := r)
          (encodedSearchState adapter state)
    rw [hfront]
  cases hleft : encodedSearchState adapter (concreteStep adapter state) with
  | mk lfront lvisited lsub =>
      cases hright : SearchState.executableStep (r := r) (encodedSearchState adapter state) with
      | mk rfront rvisited rsub =>
          have hfront' : lfront = rfront := by
            simpa [hleft, hright] using hfront
          have hvisited' : lvisited = rvisited := by
            simpa [hleft, hright] using hvisited
          subst rfront
          subst rvisited
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
      rw [concreteRun, encoded_concreteStep_eq_executableStep]
      simpa [SearchState.executableRun] using congrArg
        (SearchState.executableStep (r := r)) (ih state)

end

end ConcreteSearchAdapter
end FiniteBridge