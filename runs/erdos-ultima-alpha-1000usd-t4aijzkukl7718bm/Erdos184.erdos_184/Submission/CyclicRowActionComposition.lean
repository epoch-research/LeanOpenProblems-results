import Submission.CyclicRowActions

/-! Composition of color/row relabellings, including their endpoint certificates. -/
namespace Erdos184Work.CyclicRowActions.Action
set_option maxHeartbeats 1000000
variable {I W : Type*} {length choices : I → ℕ} [∀ i, NeZero (length i)]
    {word : ∀ i, Fin (choices i) → Fin (length i) → W}

def identity : Action length choices word where
  color := Equiv.refl _
  vertex := Function.Embedding.refl _
  row := fun _ q => q
  edge := fun _ _ => Equiv.refl _
  endpoints := fun _ _ _ => rfl

/-- First apply `a`, then `b`. -/
def comp (a b : Action length choices word) : Action length choices word where
  color := a.color.trans b.color
  vertex := a.vertex.trans b.vertex
  row := fun i q => b.row (a.color i) (a.row i q)
  edge := fun i q => (a.edge i q).trans (b.edge (a.color i) (a.row i q))
  endpoints i q j := by
    have ha := congrArg (Sym2.map b.vertex) (a.endpoints i q j)
    exact ha.trans (b.endpoints (a.color i) (a.row i q) (a.edge i q j))

lemma identity_apply (q : Rows choices) : (identity : Action length choices word).apply q = q := by
  funext i
  exact (identity : Action length choices word).apply_color q i

lemma comp_apply (a b : Action length choices word) (q : Rows choices) :
    (a.comp b).apply q = b.apply (a.apply q) := by
  funext j
  obtain ⟨i,rfl⟩ := (a.comp b).color.surjective j
  rw [apply_color]
  change b.row (a.color i) (a.row i (q i)) = b.apply (a.apply q) (b.color (a.color i))
  rw [apply_color,apply_color]

lemma apply_eq_of_rows (a b : Action length choices word)
    (hc : ∀ i, a.color i = b.color i)
    (hr : ∀ i q, (a.row i q).val = (b.row i q).val) (q : Rows choices) :
    a.apply q = b.apply q := by
  funext j
  apply Fin.ext
  obtain ⟨i,rfl⟩ := a.color.surjective j
  have hb : (b.apply q (a.color i)).val = (b.row i (q i)).val := by
    rw [hc,apply_color]
  rw [apply_color,hb]
  exact hr i (q i)

def sequence {K : Type*} (gen : K → Action length choices word) :
    List K → Action length choices word
  | [] => identity
  | g :: gs => (gen g).comp (sequence gen gs)

lemma sequence_apply_nil {K : Type*} (gen : K → Action length choices word)
    (q : Rows choices) : (sequence gen []).apply q = q := identity_apply q

lemma sequence_apply_cons {K : Type*} (gen : K → Action length choices word)
    (g : K) (gs : List K) (q : Rows choices) :
    (sequence gen (g :: gs)).apply q = (sequence gen gs).apply ((gen g).apply q) :=
  comp_apply _ _ _

#print axioms comp
#print axioms apply_eq_of_rows
end Erdos184Work.CyclicRowActions.Action
