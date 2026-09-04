import Mathlib
import FiniteBridge.Dependency

namespace FiniteBridge

def ChainWitness {α : Type} (r : α → α → Prop) (start target : α) (xs : List α) : Prop :=
  ∃ hne : xs ≠ [],
    xs.head hne = start ∧
    xs.getLast hne = target ∧
    match xs with
    | [] => True
    | [_] => True
    | a :: b :: rest => r a b ∧ ChainWitness r b target (b :: rest)

theorem reflTransGen_to_chainWitness
    {α : Type} {r : α → α → Prop} {start target : α}
    (h : Relation.ReflTransGen r start target) :
    ∃ xs : List α, ChainWitness r start target xs := by
  induction h with
  | refl =>
      refine ⟨[start], ?_⟩
      simp [ChainWitness]
  | tail hrel hstep ih =>
      rcases ih with ⟨xs, hxs⟩
      refine ⟨xs.concat target, ?_⟩
      rcases hxs with ⟨hne, hhead, hlast, hchain⟩
      refine ⟨by simp [hne], ?_, ?_, ?_⟩
      · simpa using hhead
      · simp [List.getLast_concat, hlast]
      · cases xs with
        | nil => contradiction
        | cons a rest =>
            cases rest with
            | nil => simp [hchain, hstep]
            | cons b rest =>
                simp [hchain, hstep]

/-- A non-empty explicit list witness induces the reflexive-transitive relation closure. -/
theorem chainWitness_to_reflTransGen
    {α : Type} {r : α → α → Prop} {start target : α} {xs : List α}
    (h : ChainWitness r start target xs) :
    Relation.ReflTransGen r start target := by
  rcases h with ⟨hne, hhead, hlast, hchain⟩
  subst start
  induction xs with
  | nil => contradiction
  | cons a rest =>
      cases rest with
      | nil =>
          simpa using hlast.symm
      | cons b rest =>
          have hab : r a b := hchain.1
          have hrest : Relation.ReflTransGen r b target := by
            apply chainWitness_to_reflTransGen
            refine ⟨by simp, ?_, hlast, hchain.2⟩
            rfl
          exact Relation.ReflTransGen.head hab hrest

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
