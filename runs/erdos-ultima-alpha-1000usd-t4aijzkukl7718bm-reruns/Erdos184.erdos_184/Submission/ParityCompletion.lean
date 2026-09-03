import Submission.CycleMixing

/-! Completing prescribed degree parities using a connected spanning graph.
These lemmas are auxiliary; they do not settle Erdos 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.ParityCompletion

variable {V : Type*} [Fintype V]

noncomputable def boundary (u v : V) : V → ZMod 2 :=
  fun x => (if x = u then 1 else 0) + (if x = v then 1 else 0)

lemma boundary_self (u : V) : boundary u u = 0 := by
  funext x
  exact CharTwo.add_self_eq_zero _

lemma boundary_add (u v w : V) : boundary u v + boundary v w = boundary u w := by
  funext x
  dsimp only [boundary,Pi.add_apply]
  rw [add_assoc, ← add_assoc (if x = v then 1 else 0) (if x = v then 1 else 0)
    (if x = w then 1 else 0), CharTwo.add_self_eq_zero, zero_add]

lemma column_eq_boundary (R : SimpleGraph V) {u v : V} (h : R.Adj u v) :
    (fun x => R.incMatrix (ZMod 2) x s(u,v)) = boundary u v := by
  funext x
  by_cases hu : x = u
  · subst x
    simp [boundary,incMatrix_apply',mk'_mem_incidenceSet_iff,h,h.ne]
  · by_cases hv : x = v
    · subst x
      simp [boundary,incMatrix_apply',mk'_mem_incidenceSet_iff,h,h.ne,h.ne.symm]
    · simp [boundary,incMatrix_apply',mk'_mem_incidenceSet_iff,h,hu,hv]

noncomputable def redSpan (R : SimpleGraph V) : Submodule (ZMod 2) (V → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun e x => R.incMatrix (ZMod 2) x e))

lemma boundary_mem_span (R : SimpleGraph V) {u v : V} (p : R.Walk u v) :
    boundary u v ∈ redSpan R := by
  induction p with
  | nil => rw [boundary_self]; exact (redSpan R).zero_mem
  | @cons u v w h p ih =>
    rw [← boundary_add u v w]
    apply (redSpan R).add_mem _ ih
    rw [← column_eq_boundary R h]
    exact Submodule.subset_span ⟨s(u,v),rfl⟩

lemma all_columns_mem_span (R B : SimpleGraph V) (hc : R.Connected) (e : Sym2 V) :
    (fun x => B.incMatrix (ZMod 2) x e) ∈ redSpan R := by
  induction e using Sym2.ind with
  | h u v =>
    by_cases h : B.Adj u v
    · rw [column_eq_boundary B h]
      obtain ⟨p⟩ := hc.preconnected u v
      exact boundary_mem_span R p
    · have hz : (fun x => B.incMatrix (ZMod 2) x s(u,v)) = 0 := by
        funext x
        apply incMatrix_of_notMem_incidenceSet
        intro he
        exact h he.1
      rw [hz]
      exact (redSpan R).zero_mem

lemma zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hval := x.val_lt
  have hh : x.val = 0 ∨ x.val = 1 := by omega
  rcases hh with h | h
  · left; apply ZMod.val_injective; simpa using h
  · right; apply ZMod.val_injective; simpa using h

/-- Any graph's degree parities can be realized by a subgraph of any
connected spanning graph on the same vertex type. -/
theorem exists_parity_subgraph (R B : SimpleGraph V) (hc : R.Connected) :
    ∃ X : SimpleGraph V, X ≤ R ∧
      ∀ v, (X.degree v : ZMod 2) = (B.degree v : ZMod 2) := by
  have hm : (∑ e : Sym2 V, (fun x => B.incMatrix (ZMod 2) x e)) ∈ redSpan R := by
    exact Submodule.sum_mem _ (fun e _ => all_columns_mem_span R B hc e)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hm
  let X := R.deleteEdges {e | c e = 0}
  refine ⟨X,R.deleteEdges_le _,?_⟩
  intro v
  have hinc (e : Sym2 V) :
      X.incMatrix (ZMod 2) v e = c e * R.incMatrix (ZMod 2) v e := by
    rcases zmod_two_cases (c e) with h | h <;>
      simp [X,incMatrix_apply',SimpleGraph.incidenceSet,SimpleGraph.edgeSet_deleteEdges,h]
  have hv := congrFun hc v
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hv
  have hfinal : (X.degree v : ZMod 2) = (B.degree v : ZMod 2) := by
    calc
      (X.degree v : ZMod 2) = ∑ e, X.incMatrix (ZMod 2) v e := (sum_incMatrix_apply X).symm
      _ = ∑ e, c e * R.incMatrix (ZMod 2) v e := Finset.sum_congr rfl (fun e _ => hinc e)
      _ = ∑ e, B.incMatrix (ZMod 2) v e := hv
      _ = (B.degree v : ZMod 2) := sum_incMatrix_apply B
  simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hfinal

end Erdos184.ParityCompletion
