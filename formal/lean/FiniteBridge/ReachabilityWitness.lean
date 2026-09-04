import Mathlib
import FiniteBridge.Dependency

namespace FiniteBridge

def ChainWitness {α : Type} (r : α → α → Prop) (start target : α) (xs : List α) : Prop :=
  ∃ hne : xs ≠ [],
    xs.head hne = start ∧
    xs.getLast hne = target ∧
    List.IsChain r xs

theorem reflTransGen_to_chainWitness
    {α : Type} {r : α → α → Prop} {start target : α}
    (h : Relation.ReflTransGen r start target) :
    ∃ xs : List α, ChainWitness r start target xs := by
  rcases List.exists_isChain_ne_nil_of_relationReflTransGen h with
    ⟨xs, hne, hchain, hhead, hlast⟩
  exact ⟨xs, hne, hhead, hlast, hchain⟩

/-- A non-empty explicit chain witness induces the reflexive-transitive relation closure. -/
theorem chainWitness_to_reflTransGen
    {α : Type} {r : α → α → Prop} {start target : α} {xs : List α}
    (h : ChainWitness r start target xs) :
    Relation.ReflTransGen r start target := by
  rcases h with ⟨hne, hhead, hlast, hchain⟩
  cases xs with
  | nil => contradiction
  | cons a rest =>
      have hhead' : a = start := by simpa using hhead
      subst start
      exact List.relationReflTransGen_of_exists_isChain_cons rest hchain hlast

/-- Reachability is equivalent to existence of an explicit non-empty list
witness. Simplicity is deliberately not claimed here. -/
theorem reflTransGen_iff_chainWitness
    {α : Type} {r : α → α → Prop} {start target : α} :
    Relation.ReflTransGen r start target ↔
      ∃ xs : List α, ChainWitness r start target xs := by
  constructor
  · exact reflTransGen_to_chainWitness
  · rintro ⟨xs, hxs⟩
    exact chainWitness_to_reflTransGen hxs

example :
    ∃ xs : List Nat, ChainWitness (fun a b : Nat => a < b) 2 5 xs := by
  refine ⟨[2, 5], ?_⟩
  simp [ChainWitness]

end FiniteBridge
