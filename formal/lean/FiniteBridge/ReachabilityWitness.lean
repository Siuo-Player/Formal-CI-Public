import Mathlib
import FiniteBridge

namespace FiniteBridge

def ChainWitness {α : Type} (r : α → α → Prop) (start target : α) (xs : List α) : Prop :=
  xs ≠ [] ∧
  xs.head ‹xs ≠ []› = start ∧
  xs.getLast ‹xs ≠ []› = target ∧
  TransitionValid (fun a b => r a b) xs

theorem reflTransGen_to_chainWitness
    {α : Type} {r : α → α → Prop} {start target : α}
    (h : Relation.ReflTransGen r start target) :
    ∃ xs : List α, ChainWitness r start target xs := by
  induction h with
  | refl =>
      refine ⟨[start], ?_⟩
      simp [ChainWitness, TransitionValid]
  | tail hrel hstep ih =>
      rcases ih with ⟨xs, hxs⟩
      have hne : xs ≠ [] := hxs.1
      have hlast : xs.getLast hne = _ := hxs.2.2.1
      refine ⟨xs.concat target, ?_⟩
      simp [ChainWitness, TransitionValid, hne, hlast, hstep, hxs.2.2.2]

/-- A non-empty list witness induces the reflexive-transitive relation closure. -/
theorem chainWitness_to_reflTransGen
    {α : Type} {r : α → α → Prop} {start target : α} {xs : List α}
    (h : ChainWitness r start target xs) :
    Relation.ReflTransGen r start target := by
  have hne : xs ≠ [] := h.1
  have hhead : xs.head hne = start := h.2.1
  have hlast : xs.getLast hne = target := h.2.2.1
  have hvalid : TransitionValid (fun a b => r a b) xs := h.2.2.2
  subst start
  induction xs with
  | nil => contradiction
  | cons a rest ih =>
      cases rest with
      | nil =>
          simpa using (show target = a from hlast.symm)
      | cons b rest =>
          have hab : r a b := hvalid.1
          have htail : TransitionValid (fun x y => r x y) (b :: rest) := hvalid.2
          have hrest : Relation.ReflTransGen r b target := by
            apply chainWitness_to_reflTransGen
            refine ⟨by simp, ?_, hlast, htail⟩
            rfl
          exact Relation.ReflTransGen.head hab hrest

/-- Reachability is equivalent to existence of an explicit non-empty list
witness. This is a representation theorem; simplicity is intentionally not
claimed yet. -/
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
  simp [ChainWitness, TransitionValid]

end FiniteBridge
