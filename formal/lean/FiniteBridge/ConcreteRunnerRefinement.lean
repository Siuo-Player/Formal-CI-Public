import Mathlib
import FiniteBridge.ConcreteSearchAdapter

namespace FiniteBridge
namespace ConcreteSearchAdapter

section

variable {ConcreteState : Type*} {n : Nat} {r : Transition n}
  [DecidableRel r] [Fintype ConcreteState] [DecidableEq ConcreteState]
  (adapter : ConcreteSearchAdapter ConcreteState n r)

structure ConcreteSearchState (ConcreteState : Type*) where
  frontier : Finset ConcreteState
  visited : Finset ConcreteState
  frontier_subset_visited : frontier ⊆ visited

def concreteInitial (start : ConcreteState) : ConcreteSearchState ConcreteState :=
  ⟨{start}, {start}, by intro x hx; simpa using hx⟩

def concreteNextFrontier
    (adapter : ConcreteSearchAdapter ConcreteState n r)
    (state : ConcreteSearchState ConcreteState) : Finset ConcreteState :=
  state.frontier.biUnion adapter.successors \ state.visited

def concreteStep
    (adapter : ConcreteSearchAdapter ConcreteState n r)
    (state : ConcreteSearchState ConcreteState) : ConcreteSearchState ConcreteState := by
  let frontier' := concreteNextFrontier adapter state
  let visited' := state.visited ∪ frontier'
  have hsubset : frontier' ⊆ visited' := by
    intro x hx
    exact Finset.mem_union_right _ hx
  exact ⟨frontier', visited', hsubset⟩

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

theorem encoded_concreteInitial_eq_initial (start : ConcreteState) :
    encodedSearchState adapter (concreteInitial start) =
      SearchState.initial (r := r) (adapter.encode start) := by
  simp [encodedSearchState, concreteInitial, SearchState.initial]

theorem encoded_concreteNextFrontier_eq_executable
    (state : ConcreteSearchState ConcreteState) :
    (encodedSearchState adapter (concreteStep adapter state)).frontier =
      SearchState.executableNextFrontier (r := r)
        (encodedSearchState adapter state) := by
  ext t
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨u, hu, hut⟩
    rcases Finset.mem_sdiff.mp hu with ⟨hbi, hnotvis⟩
    rcases Finset.mem_biUnion.mp hbi with ⟨cs, hcs, hct⟩
    have hrel : r (adapter.encode cs) (adapter.encode u) :=
      (adapter.mem_successors_iff cs u).mp hct
    have htarget : adapter.encode u = t := hut
    have hfront : adapter.encode cs ∈
        (encodedSearchState adapter state).frontier := by
      exact Finset.mem_image.mpr ⟨cs, hcs, rfl⟩
    have hnotencoded : adapter.encode u ∉
        (encodedSearchState adapter state).visited := by
      intro hv
      rcases Finset.mem_image.mp hv with ⟨v, hv', hvenc⟩
      have hcu : u = v := adapter.encode.injective hvenc.symm
      exact hnotvis (by simpa [hcu])
    subst t
    exact Finset.mem_sdiff.mpr ⟨
      Finset.mem_biUnion.mpr ⟨adapter.encode cs, hfront,
        (SearchState.mem_executableSuccessors_iff (r := r)
          (adapter.encode cs) (adapter.encode u)).mpr hrel⟩,
      hnotencoded⟩
  · intro ht
    rcases Finset.mem_sdiff.mp ht with ⟨hbi, hnotvis⟩
    rcases Finset.mem_biUnion.mp hbi with ⟨s, hs, hst⟩
    rcases Finset.mem_image.mp hs with ⟨cs, hcs, hcsenc⟩
    have hrel : r s t :=
      (SearchState.mem_executableSuccessors_iff (r := r) s t).mp hst
    have hct : adapter.encode.symm t ∈ adapter.successors cs := by
      rw [adapter.mem_successors_iff]
      simpa [hcsenc] using hrel
    have hnotconcrete : adapter.encode.symm t ∉ state.visited := by
      intro hv
      apply hnotvis
      exact Finset.mem_image.mpr ⟨adapter.encode.symm t, hv, by simp⟩
    exact Finset.mem_image.mpr ⟨
      adapter.encode.symm t,
      Finset.mem_sdiff.mpr ⟨
        Finset.mem_biUnion.mpr ⟨cs, hcs, hct⟩,
        hnotconcrete⟩,
      by simp⟩

theorem encoded_concreteStep_eq_executableStep
    (state : ConcreteSearchState ConcreteState) :
    encodedSearchState adapter (concreteStep adapter state) =
      SearchState.executableStep (r := r) (encodedSearchState adapter state) := by
  have hfront := encoded_concreteNextFrontier_eq_executable adapter state
  have hvisited :
      (encodedSearchState adapter (concreteStep adapter state)).visited =
        (SearchState.executableStep (r := r) (encodedSearchState adapter state)).visited := by
    change state.visited.image adapter.encode ∪
        (concreteNextFrontier adapter state).image adapter.encode =
      (encodedSearchState adapter state).visited ∪
        SearchState.executableNextFrontier (r := r)
          (encodedSearchState adapter state)
    rw [← hfront]
    rfl
  have hstate_front :
      (encodedSearchState adapter (concreteStep adapter state)).frontier =
        (SearchState.executableStep (r := r) (encodedSearchState adapter state)).frontier := by
    exact hfront
  cases hleft : encodedSearchState adapter (concreteStep adapter state) with
  | mk lfront lvisited lsub =>
      cases hright : SearchState.executableStep (r := r) (encodedSearchState adapter state) with
      | mk rfront rvisited rsub =>
          have hf : lfront = rfront := by
            simpa [hleft, hright] using hstate_front
          have hv : lvisited = rvisited := by
            simpa [hleft, hright] using hvisited
          subst rfront
          subst rvisited
          rfl

def concreteRun
    (adapter : ConcreteSearchAdapter ConcreteState n r) :
    Nat → ConcreteSearchState ConcreteState → ConcreteSearchState ConcreteState
  | 0, state => state
  | fuel + 1, state => concreteStep adapter (concreteRun adapter fuel state)

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