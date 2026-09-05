import Mathlib
import FiniteBridge.ReachabilityWitness
import FiniteBridge.CycleSplice

namespace FiniteBridge

/-- Duplicate decomposition by structural induction on the ambient list.
This is the standard walk-to-cycle decomposition pattern used in graph
formalizations; the project only adapts it to `List.Duplicate`. -/
theorem duplicate_decomposition
    {α : Type} {x : α} {xs : List α}
    (hdup : List.Duplicate x xs) :
    ∃ pre middle suffix : List α,
      xs = pre ++ x :: middle ++ x :: suffix := by
  induction xs with
  | nil =>
      cases hdup
  | cons y ys ih =>
      cases hdup with
      | cons_mem hx =>
          rcases List.mem_iff_append.mp hx with ⟨pre, suffix, hys⟩
          exact ⟨[], pre, suffix, by
            rw [hys]
            simp⟩
      | cons_duplicate hdup' =>
          rcases ih hdup' with ⟨pre, middle, suffix, hrepr⟩
          exact ⟨y :: pre, middle, suffix, by
            rw [hrepr]
            simp [List.cons_append, List.append_assoc]⟩

/-- The cycle-splice operation preserves non-emptiness and the first endpoint. -/
theorem chainWitness_splice_preserves_start
    {α : Type} {r : α → α → Prop} {start target : α}
    {pre middle suffix : List α} {a : α}
    (hhead : (pre ++ a :: middle ++ a :: suffix).head (by aesop) = start) :
    (pre ++ a :: suffix).head (by aesop) = start := by
  cases pre with
  | nil => simpa using hhead
  | cons p pre => simpa using hhead

/-- The cycle-splice operation preserves the final endpoint. -/
theorem chainWitness_splice_preserves_target
    {α : Type} {r : α → α → Prop} {start target : α}
    {pre middle suffix : List α} {a : α}
    (hlast : (pre ++ a :: middle ++ a :: suffix).getLast (by aesop) = target) :
    (pre ++ a :: suffix).getLast (by aesop) = target := by
  cases suffix with
  | nil => simpa [List.append_assoc] using hlast
  | cons b suffix => simpa [List.append_assoc] using hlast

/-- Removing a repeated-state cycle from a non-empty chain preserves its
endpoints and strictly decreases its length. -/
theorem chainWitness_splice_shorter
    {α : Type} {r : α → α → Prop} {start target : α}
    {xs : List α}
    (hxs : ChainWitness r start target xs)
    (hnodup : ¬xs.Nodup) :
    ∃ ys : List α,
      ChainWitness r start target ys ∧ ys.length < xs.length := by
  rcases hxs with ⟨hne, hhead, hlast, hchain⟩
  rcases (List.exists_duplicate_iff_not_nodup.mpr hnodup) with ⟨a, hdup⟩
  rcases duplicate_decomposition hdup with ⟨pre, middle, suffix, rfl⟩
  let ys := pre ++ a :: suffix
  have hchain' : List.IsChain r ys := by
    dsimp [ys]
    exact isChain_cycle_splice hchain
  have hne' : ys ≠ [] := by
    unfold ys
    cases pre <;> simp
  have hhead' : ys.head hne' = start := by
    dsimp [ys]
    cases pre <;> simpa using hhead
  have hlast' : ys.getLast hne' = target := by
    dsimp [ys]
    cases suffix with
    | nil => simpa [List.append_assoc] using hlast
    | cons b suffix => simpa [List.append_assoc] using hlast
  refine ⟨ys, ⟨hne', hhead', hlast', hchain'⟩, ?_⟩
  simp [ys]

/-- Every explicit finite chain has an endpoint-preserving simple witness. -/
theorem chainWitness_to_simpleChainWitness
    {α : Type} {r : α → α → Prop} {start target : α}
    {xs : List α}
    (hxs : ChainWitness r start target xs) :
    ∃ ys : List α,
      ChainWitness r start target ys ∧ ys.Nodup := by
  induction hlen : xs.length using Nat.strong_induction_on generalizing xs start target with
  | h n ih =>
      by_cases hnodup : xs.Nodup
      · exact ⟨xs, hxs, hnodup⟩
      · rcases chainWitness_splice_shorter hxs hnodup with ⟨ys, hys, hlt⟩
        have hlt' : ys.length < n := by
          simpa [hlen] using hlt
        exact ih ys.length hlt' hys

/-- Reachability over any relation admits a simple non-empty chain witness. -/
theorem reflTransGen_to_simpleChainWitness
    {α : Type} {r : α → α → Prop} {start target : α}
    (h : Relation.ReflTransGen r start target) :
    ∃ xs : List α, ∃ hne : xs ≠ [],
      xs.head hne = start ∧
      xs.getLast hne = target ∧
      xs.Nodup ∧
      List.IsChain r xs := by
  rcases reflTransGen_to_chainWitness h with ⟨xs, hxs⟩
  rcases chainWitness_to_simpleChainWitness hxs with ⟨ys, hys, hsimple⟩
  rcases hys with ⟨hne, hhead, hlast, hchain⟩
  exact ⟨ys, hne, hhead, hlast, hsimple, hchain⟩

end FiniteBridge
