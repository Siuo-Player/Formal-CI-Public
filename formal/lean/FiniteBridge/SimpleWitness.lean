import Mathlib
import FiniteBridge.ReachabilityWitness
import FiniteBridge.CycleSplice

namespace FiniteBridge

/-- Any duplicate in a list admits an explicit decomposition into two occurrences
of the same element, with an arbitrary middle segment between them. -/
theorem duplicate_decomposition
    {α : Type} {x : α} {xs : List α}
    (hdup : List.Duplicate x xs) :
    ∃ prefix middle suffix : List α,
      xs = prefix ++ x :: middle ++ x :: suffix := by
  induction hdup with
  | cons_mem hx ih =>
      cases ih with
      | intro prefix middle suffix hrepr =>
          exact ⟨[], [], x :: suffix, by simp [hrepr]⟩
  | cons_duplicate hdup ih y =>
      cases ih with
      | intro prefix middle suffix hrepr =>
          exact ⟨y :: prefix, middle, suffix, by simp [hrepr, List.cons_append]⟩

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
  rcases (List.exists_duplicate_iff_not_nodup.mp hnodup) with ⟨a, hdup⟩
  rcases duplicate_decomposition hdup with ⟨prefix, middle, suffix, rfl⟩
  let ys := prefix ++ a :: suffix
  have hchain' : List.IsChain r ys := by
    dsimp [ys]
    exact isChain_cycle_splice hchain
  have hne' : ys ≠ [] := by
    intro hy
    have : prefix = [] := by
      simpa [ys] using hy
    subst this
    simp at hhead
  have hhead' : ys.head hne' = start := by
    simpa [ys] using hhead
  have hlast' : ys.getLast hne' = target := by
    have hsuffix : suffix = [] ∨ suffix ≠ [] := classical exact em _
    cases hsuffix with
    | inl hs =>
        subst hs
        simpa [ys, List.getLast] using hhead
    | inr hs =>
        simpa [ys, List.getLast, hs] using hlast
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
        exact ih ys.length hlt ys start target hys

/-- Reachability over any relation admits a simple non-empty chain witness. -/
theorem reflTransGen_to_simpleChainWitness
    {α : Type} {r : α → α → Prop} {start target : α}
    (h : Relation.ReflTransGen r start target) :
    ∃ xs : List α,
      xs ≠ [] ∧
      xs.head (by aesop) = start ∧
      xs.getLast (by aesop) = target ∧
      xs.Nodup ∧
      List.IsChain r xs := by
  rcases reflTransGen_to_chainWitness h with ⟨xs, hxs⟩
  rcases chainWitness_to_simpleChainWitness hxs with ⟨ys, hys, hsimple⟩
  rcases hys with ⟨hne, hhead, hlast, hchain⟩
  exact ⟨ys, hne, hhead, hlast, hsimple, hchain⟩

end FiniteBridge
