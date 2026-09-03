import Submission.BinarySumFilter

/-!
An obstruction to characteristic-two, point-translation-invariant bipartite
graphs, including weight-dependent thinnings. Not a solution of Erdős714.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714BinaryTranslation
variable {E A : Type*} [Field E] [CharP E 2] [Fintype E] [Fintype A]

/-- Translate both point coordinates without changing labels or parts. -/
def shift (z : E) (v : Bool × (E × A)) : Bool × (E × A) :=
  (v.1, (v.2.1+z, v.2.2))

/-- This symmetry is a genuine restriction on the retained graph. -/
def Invariant (H : SimpleGraph (Bool × (E × A))) : Prop :=
  ∀ z u v, H.Adj (shift z u) (shift z v) ↔ H.Adj u v

/-- Edges join the designated different Boolean parts. -/
def Bipartite (H : SimpleGraph (Bool × (E × A))) : Prop :=
  ∀ ⦃u v⦄, H.Adj u v → u.1 ≠ v.1

/-- A separate connection set is allowed for every ordered label pair. -/
def connection (H : SimpleGraph (Bool × (E × A))) (a b : A) : Finset E :=
  univ.filter (fun s => H.Adj (false,(0,a)) (true,(s,b)))

omit [Fintype A] in
lemma cross_adj_iff (H : SimpleGraph (Bool × (E × A))) (hI : Invariant H)
    (x y : E) (a b : A) :
    H.Adj (false,(x,a)) (true,(y,b)) ↔ x+y ∈ connection H a b := by
  have h := hI x (false,(x,a)) (true,(y,b))
  simpa [shift, connection, CharTwo.add_self_eq_zero, add_comm] using h.symm

/-- Each connection sum graph actually embeds in H. -/
def connectionCopy (H : SimpleGraph (Bool × (E × A))) (hI : Invariant H) (a b : A) :
    (Erdos714BinarySumFilter.graph (connection H a b)).Copy H where
  toHom := {
    toFun v := (v.1, (v.2, if v.1 then b else a))
    map_rel' := by
      rintro ⟨bu,x⟩ ⟨bv,y⟩ h
      change bu ≠ bv ∧ x+y ∈ connection H a b at h
      cases bu <;> cases bv
      · exact False.elim (h.1 rfl)
      · exact (cross_adj_iff H hI x y a b).mpr h.2
      · exact ((cross_adj_iff H hI y x a b).mpr (by simpa [add_comm] using h.2)).symm
      · exact False.elim (h.1 rfl)
  }
  injective' := by
    rintro ⟨bu,x⟩ ⟨bv,y⟩ h
    exact Prod.ext (congrArg (fun v : Bool × (E × A) => v.1) h)
      (congrArg (fun v : Bool × (E × A) => v.2.1) h)

omit [Fintype A] in
/-- K44-freeness bounds every weight-pair connection set. -/
theorem connection_sq_bound (H : SimpleGraph (Bool × (E × A))) (hI : Invariant H)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) (a b : A) :
    ((connection H a b).card : ℝ)^2 ≤ 3 * Fintype.card E := by
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714BinarySumFilter.graph (connection H a b)) := by
    rintro ⟨f⟩
    exact hfree ⟨(connectionCopy H hI a b).comp f⟩
  have h := Erdos714BinarySumFilter.sq_card_le _ hf
  have hc : ((connection H a b).card : ℝ) ≤ Fintype.card E := by
    exact_mod_cast card_le_univ (connection H a b)
  linarith

/-- The neighbor set of a left vertex is a disjoint union of translated
connection sets. -/
def leftNeighborEquiv (H : SimpleGraph (Bool × (E × A)))
    (hI : Invariant H) (hB : Bipartite H) (x : E) (a : A) :
    H.neighborSet (false,(x,a)) ≃ Σ b : A, connection H a b where
  toFun v := ⟨v.val.2.2, x+v.val.2.1, by
    have hs : v.val.1 = true := by
      have h := hB v.property
      cases hv : v.val.1 <;> simp_all
    have h := v.property
    have hv : v.val = (true,(v.val.2.1,v.val.2.2)) := by exact Prod.ext hs rfl
    rw [hv] at h
    exact (cross_adj_iff H hI _ _ _ _).mp h⟩
  invFun v := ⟨(true,((v.2 : E)-x,v.1)), by
    apply (cross_adj_iff H hI _ _ _ _).mpr
    simp⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · change true = v.val.1
      have h := hB v.property
      cases hv : v.val.1 <;> simp_all
    · apply Prod.ext
      · change x+v.val.2.1-x = v.val.2.1
        ring
      · rfl
  right_inv v := by
    rcases v with ⟨b,s⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    apply Subtype.ext
    change x+((s : E)-x) = s
    ring

lemma left_degree (H : SimpleGraph (Bool × (E × A)))
    (hI : Invariant H) (hB : Bipartite H) (x : E) (a : A) :
    H.degree (false,(x,a)) = ∑ b, (connection H a b).card := by
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (leftNeighborEquiv H hI hB x a)]
  simp

/-- Exact edge count for all such invariant bipartite graphs. -/
theorem edge_count (H : SimpleGraph (Bool × (E × A)))
    (hI : Invariant H) (hB : Bipartite H) :
    H.edgeFinset.card = Fintype.card E * ∑ a, ∑ b, (connection H a b).card := by
  let L := (univ : Finset (Bool × (E × A))).filter (fun v => v.1 = false)
  let R := (univ : Finset (Bool × (E × A))).filter (fun v => v.1 = true)
  have hbi : H.IsBipartiteWith L R := by
    constructor
    · rw [Set.disjoint_left]
      intro v hv hw
      have h1 : v.1 = false := (mem_filter.mp hv).2
      have h2 : v.1 = true := (mem_filter.mp hw).2
      exact Bool.false_ne_true (h1.symm.trans h2)
    · intro u v huv
      have h := hB huv
      cases hu : u.1 <;> cases hv : v.1 <;> simp_all [L,R]
  have h := H.isBipartiteWith_sum_degrees_eq_card_edges hbi
  rw [← h]
  simp only [L, sum_filter, Fintype.sum_prod_type]
  simp [left_degree H hI hB, mul_sum]

/-- Every translation-invariant K44-free bipartite graph with Q point
coordinates and W labels satisfies e² <= 3*Q³*W⁴. -/
theorem edge_sq_bound (H : SimpleGraph (Bool × (E × A)))
    (hI : Invariant H) (hB : Bipartite H)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    (H.edgeFinset.card : ℝ)^2 ≤
      3*(Fintype.card E : ℝ)^3*(Fintype.card A : ℝ)^4 := by
  let s : A × A → ℝ := fun p => (connection H p.1 p.2).card
  have hsq : ∑ p : A × A, s p ^ 2 ≤
      3 * Fintype.card E * (Fintype.card A : ℝ)^2 := by
    calc
      ∑ p : A × A, s p ^ 2 ≤ ∑ _ : A × A, 3 * (Fintype.card E : ℝ) := by
        apply sum_le_sum
        intro p _
        exact connection_sq_bound H hI hfree p.1 p.2
      _ = _ := by simp [Fintype.card_prod]; ring
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset (A × A)) (fun _ => (1 : ℝ)) s
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_prod,
    nsmul_eq_mul, mul_one, Nat.cast_mul] at hcs
  have hb : (∑ p : A × A, s p)^2 ≤
      3 * Fintype.card E * (Fintype.card A : ℝ)^4 := by
    have hm := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ (Fintype.card A : ℝ)*(Fintype.card A : ℝ) by positivity)
    exact hcs.trans (by convert hm using 1; ring)
  rw [edge_count H hI hB]
  push_cast
  have hs : (∑ a, ∑ b, ((connection H a b).card : ℝ)) = ∑ p : A × A, s p := by
    simp [s, Fintype.sum_prod_type]
  rw [hs,mul_pow]
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (Fintype.card E : ℝ))
  convert hm using 1; ring

/-- The original cubic scale suffers a strict exponent loss even if the
retained sum set depends arbitrarily on both weights. -/
theorem cubic_scale_bound (H : SimpleGraph (Bool × (E × A)))
    (hI : Invariant H) (hB : Bipartite H)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q : ℕ) (hE : Fintype.card E = q^3) (hA : Fintype.card A ≤ q) :
    (H.edgeFinset.card : ℝ)^2 ≤ 3*(q : ℝ)^13 := by
  have h := edge_sq_bound H hI hB hfree
  have hER : (Fintype.card E : ℝ) = (q : ℝ)^3 := by exact_mod_cast hE
  have hAR : (Fintype.card A : ℝ) ≤ q := by exact_mod_cast hA
  rw [hER] at h
  calc
    (H.edgeFinset.card : ℝ)^2 ≤ 3*((q : ℝ)^3)^3*(Fintype.card A : ℝ)^4 := h
    _ ≤ 3*((q : ℝ)^3)^3*(q : ℝ)^4 := by gcongr
    _ = _ := by ring

#print axioms connection_sq_bound
#print axioms edge_count
#print axioms edge_sq_bound
#print axioms cubic_scale_bound
end Erdos714BinaryTranslation
