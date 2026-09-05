import Mathlib
import FiniteBridge.ReachabilityWitness

namespace FiniteBridge

/-- A chain remains a chain when a repeated endpoint and everything between
its two occurrences are removed. -/
theorem isChain_cycle_splice
    {α : Type} {r : α → α → Prop}
    {pre middle suffix : List α} {a : α}
    (hchain : List.IsChain r (pre ++ a :: middle ++ a :: suffix)) :
    List.IsChain r (pre ++ a :: suffix) := by
  induction pre with
  | nil =>
      cases middle with
      | nil =>
          simpa using hchain
      | cons b middle =>
          simpa only [List.nil_append, List.cons_append] at hchain ⊢
          exact hchain.2
  | cons p pre ih =>
      have hchain' : List.IsChain r (p :: (pre ++ a :: middle ++ a :: suffix)) := by
        simpa only [List.cons_append] using hchain
      have ih' : List.IsChain r (pre ++ a :: suffix) := by
        apply ih
        simpa only [List.cons_append] using hchain'
      simpa only [List.cons_append] using (List.IsChain.cons_of_ne_nil (by simp) (by exact ih') hchain')

end FiniteBridge
