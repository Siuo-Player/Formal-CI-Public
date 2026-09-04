import FiniteBridge.SemanticDependency

namespace FiniteBridge

def InputChangeSet
    (InputBefore InputAfter : α → Prop) : Set α :=
  {node | ¬ (InputBefore node ↔ InputAfter node)}

def LocalCompositionalSemantics
    (Edge : α → α → Prop)
    (InputBefore InputAfter Before After : α → Prop)
    (Eval : (node : α) → Prop →
      ((pred : α) → Edge pred node → Prop) → Prop) : Prop :=
  ∀ node,
    (Before node ↔
        Eval node (InputBefore node) (fun pred _ => Before pred)) ∧
    (After node ↔
        Eval node (InputAfter node) (fun pred _ => After pred))

theorem locallyPropagatesChange_of_localCompositionalSemantics
    {α : Type}
    {Edge : α → α → Prop}
    {InputBefore InputAfter Before After : α → Prop}
    {Eval : (node : α) → Prop →
      ((pred : α) → Edge pred node → Prop) → Prop}
    (hsem : LocalCompositionalSemantics
      Edge InputBefore InputAfter Before After Eval) :
    LocallyPropagatesChange
      Edge Before After (InputChangeSet InputBefore InputAfter) := by
  intro node hchanged
  by_cases hseed : ¬ (InputBefore node ↔ InputAfter node)
  · exact Or.inl hseed
  · right
    by_contra hno
    apply hchanged
    have hinput : InputBefore node ↔ InputAfter node := by
      exact not_not.mp hseed
    have hpredEq :
        (fun (pred : α) (_hpred : Edge pred node) => Before pred) =
        (fun (pred : α) (_hpred : Edge pred node) => After pred) := by
      funext pred
      funext hpred
      apply propext
      by_contra hnot
      exact hno ⟨pred, hpred, hnot⟩
    have heval :
        Eval node (InputBefore node)
            (fun (pred : α) (hpred : Edge pred node) => Before pred) =
        Eval node (InputAfter node)
            (fun (pred : α) (hpred : Edge pred node) => After pred) := by
      rw [propext hinput, hpredEq]
    have heval_iff :
        Eval node (InputBefore node)
            (fun (pred : α) (hpred : Edge pred node) => Before pred) ↔
        Eval node (InputAfter node)
            (fun (pred : α) (hpred : Edge pred node) => After pred) := by
      rw [heval]
    exact (hsem node).1.trans (heval_iff.trans (hsem node).2.symm)

theorem semantically_changed_affected_of_localCompositionalSemantics
    {α : Type}
    {Edge : α → α → Prop}
    (hWF : WellFounded Edge)
    {InputBefore InputAfter Before After : α → Prop}
    {Eval : (node : α) → Prop →
      ((pred : α) → Edge pred node → Prop) → Prop}
    (hsem : LocalCompositionalSemantics
      Edge InputBefore InputAfter Before After Eval) :
    ∀ {node},
      SemanticallyChanged Before After node →
        Affected Edge (InputChangeSet InputBefore InputAfter) node := by
  exact semantically_changed_affected_of_wellFounded hWF
    (locallyPropagatesChange_of_localCompositionalSemantics hsem)

end FiniteBridge
