import FormalConjecturesUtil
import Submission.TensorEdgeSelection

/-! A vertex-sensitive bound for H-free subgraphs of categorical products.
This is an auxiliary obstruction to amplification, not a proof of Erdős 713. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713TensorVertexSelection
open Erdos713ProductCover Erdos713TensorEdgeSelection
variable {V U W : Type*}
set_option maxHeartbeats 1000000

noncomputable def active [Fintype V] [Fintype U] (G : SimpleGraph V) (F : SimpleGraph U)
    (S : Finset (V × U)) (v : V) (u : U) : Finset (F.neighborSet u ⊕ G.neighborSet v) :=
  univ.filter (fun w => starRectangle G F v u w ∈ S)

lemma active_card [Fintype V] [Fintype U] (G : SimpleGraph V) (F : SimpleGraph U)
    (S : Finset (V × U)) (v : V) (u : U) :
    (active G F S v u).card =
      (∑ y : F.neighborSet u, if (v,y.val) ∈ S then 1 else 0) +
      (∑ x : G.neighborSet v, if (x.val,u) ∈ S then 1 else 0) := by
  simp only [active,card_filter,Fintype.sum_sum_type]
  rfl

lemma active_card_le [Fintype V] [Fintype U] (G : SimpleGraph V) (F : SimpleGraph U)
    (S : Finset (V × U)) (v : V) (u : U) :
    (active G F S v u).card ≤ F.degree u + G.degree v := by
  have hh := card_filter_le (univ : Finset (F.neighborSet u ⊕ G.neighborSet v))
    (fun w => starRectangle G F v u w ∈ S)
  simpa only [active,card_univ,Fintype.card_sum,card_neighborSet_eq_degree] using hh

lemma sum_active_card [Fintype V] [Fintype U] (G : SimpleGraph V) (F : SimpleGraph U)
    (S : Finset (V × U)) :
    (∑ v : V, ∑ u : U, (active G F S v u).card) =
      ∑ p ∈ S, (G.degree p.1 + F.degree p.2) := by
  have hcard (v : V) (u : U) : (active G F S v u).card =
      (∑ y : U, if F.Adj u y then (if (v,y) ∈ S then 1 else 0) else 0) +
      (∑ x : V, if G.Adj v x then (if (x,u) ∈ S then 1 else 0) else 0) := by
    rw [active_card, Erdos713TensorEdgeSelection.sum_neighbors F u
      (fun y => if (v,y) ∈ S then 1 else 0),
      Erdos713TensorEdgeSelection.sum_neighbors G v
      (fun x => if (x,u) ∈ S then 1 else 0)]
  simp_rw [hcard,sum_add_distrib]
  have hF : (∑ v : V, ∑ u : U, ∑ y : U,
      if F.Adj u y then (if (v,y) ∈ S then 1 else 0) else 0) =
      ∑ p : V × U, if p ∈ S then F.degree p.2 else 0 := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro v _
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    by_cases hy : (v,y) ∈ S
    · simp only [hy,ite_true]
      rw [← card_filter,← card_neighborFinset_eq_degree]
      congr 1
      ext u
      simp only [mem_filter,mem_univ,true_and,mem_neighborFinset]
      exact F.adj_comm _ _
    · simp [hy]
  have hG : (∑ v : V, ∑ u : U, ∑ x : V,
      if G.Adj v x then (if (x,u) ∈ S then 1 else 0) else 0) =
      ∑ p : V × U, if p ∈ S then G.degree p.1 else 0 := by
    rw [sum_comm]
    conv_lhs => arg 2; ext u; rw [sum_comm]
    rw [sum_comm, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro u _
    by_cases hx : (x,u) ∈ S
    · simp only [hx,ite_true]
      rw [← card_filter,← card_neighborFinset_eq_degree]
      congr 1
      ext v
      simp only [mem_filter,mem_univ,true_and,mem_neighborFinset]
      exact G.adj_comm _ _
    · simp [hx]
  rw [hF,hG,← sum_add_distrib]
  calc
    _ = ∑ p : V × U, if p ∈ S then G.degree p.1 + F.degree p.2 else 0 := by
      apply sum_congr rfl
      intro p _
      split_ifs <;> omega
    _ = _ := by rw [← sum_filter]; simp [sum_add_distrib]

lemma rectangle_adj (G : SimpleGraph V) (F : SimpleGraph U) (J : SimpleGraph (V × U))
    (v : V) (u : U) {w z : F.neighborSet u ⊕ G.neighborSet v}
    (h : (rectangle G F J v u).Adj w z) :
    J.Adj (starRectangle G F v u w) (starRectangle G F v u z) := by
  rcases w with w|w <;> rcases z with z|z
  · exact h.elim
  · exact h
  · change J.Adj (v,z.val) (w.val,u) at h
    exact h.symm
  · exact h.elim

lemma rectangle_support [Fintype V] [Fintype U] (G : SimpleGraph V) (F : SimpleGraph U)
    (J : SimpleGraph (V × U)) (S : Finset (V × U)) (hs : J.support ⊆ S)
    (v : V) (u : U) :
    (rectangle G F J v u).support ⊆ (active G F S v u : Set _) := by
  intro w hw
  obtain ⟨z,hz⟩ := (mem_support _).mp hw
  exact mem_filter.mpr ⟨mem_univ _,hs ((mem_support J).mpr
    ⟨_,rectangle_adj G F J v u hz⟩)⟩

lemma rectangle_induce_copy [Fintype V] [Fintype U]
    (G : SimpleGraph V) (F : SimpleGraph U) (J : SimpleGraph (V × U))
    (S : Finset (V × U)) (v : V) (u : U) :
    (rectangle G F J v u).induce (active G F S v u : Set _) ⊑ J.induce (S : Set _) := by
  refine ⟨⟨⟨fun w => ⟨starRectangle G F v u w.val,(mem_filter.mp w.property).2⟩,?_⟩,?_⟩⟩
  · intro w z h
    exact rectangle_adj G F J v u h
  · intro w z h
    exact Subtype.ext ((starRectangle G F v u).injective (congrArg Subtype.val h))

lemma support_bound_of_induce_free [Fintype V] (H : SimpleGraph W) (R : SimpleGraph V)
    (S : Finset V) (hs : R.support ⊆ S) (hf : H.Free (R.induce (S : Set V))) :
    Nat.card R.edgeSet ≤ extremalNumber S.card H := by
  have hc : Fintype.card (S : Set V) = S.card := by simp
  have hh := card_edgeFinset_le_extremalNumber hf
  rw [hc] at hh
  have he := card_edgeFinset_induce_of_support_subset hs
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card] at he hh
  rw [he] at hh
  exact hh

lemma support_bound [Fintype V] (H : SimpleGraph W) (R : SimpleGraph V)
    (S : Finset V) (hs : R.support ⊆ S) (hf : H.Free R) :
    Nat.card R.edgeSet ≤ extremalNumber S.card H :=
  support_bound_of_induce_free H R S hs
    (fun h => hf (h.trans ⟨SimpleGraph.Copy.induce R (S : Set V)⟩))

lemma rectangle_bound [Fintype V] [Fintype U] (H : SimpleGraph W)
    (G : SimpleGraph V) (F : SimpleGraph U) (J : SimpleGraph (V × U))
    (S : Finset (V × U)) (hs : J.support ⊆ S) (hf : H.Free (J.induce (S : Set _)))
    (v : V) (u : U) :
    Nat.card (rectangle G F J v u).edgeSet ≤ extremalNumber (active G F S v u).card H := by
  exact support_bound_of_induce_free H _ _ (rectangle_support G F J S hs v u)
    (fun h => hf (h.trans (rectangle_induce_copy G F J S v u)))

lemma rpow_eq_linear {x α : ℝ} (hx : 0 ≤ x) (ha : 1 ≤ α) :
    x^α = x^(α-1)*x := by
  by_cases hz : x = 0
  · subst x
    rw [Real.zero_rpow (show α ≠ 0 by linarith),mul_zero]
  · have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    calc
      _ = x^((α-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hp,Real.rpow_one]

lemma rpow_linear_bound {s D α : ℝ} (hs : 0 ≤ s) (hD : s ≤ D) (ha : 1 ≤ α) :
    s^α ≤ D^(α-1)*s := by
  rw [rpow_eq_linear hs ha]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs hD (by linarith)) hs

/-- A support-sensitive version of the rectangle extremal bound. No degree
assumptions are needed at this stage, and the factors need not be H-free. -/
theorem edge_bound [Fintype V] [Fintype U] (H : SimpleGraph W)
    (G : SimpleGraph V) (F : SimpleGraph U) (J : SimpleGraph (V × U))
    (S : Finset (V × U)) (hJ : J ≤ tensor G F) (hs : J.support ⊆ S) (hf : H.Free (J.induce (S : Set _))) :
    2*Nat.card J.edgeSet ≤ ∑ v : V, ∑ u : U, extremalNumber (active G F S v u).card H := by
  rw [← sum_rectangle_edges G F J hJ]
  exact sum_le_sum (fun v _ => sum_le_sum (fun u _ => rectangle_bound H G F J S hs hf v u))

/-- The bound scales with the selected support size rather than the full
product order. Freeness is required only on the selected vertices, so the
forbidden graph may have isolated vertices. -/
theorem bounded_degrees [Fintype V] [Fintype U] (H : SimpleGraph W)
    (G : SimpleGraph V) (F : SimpleGraph U) (J : SimpleGraph (V × U))
    (S : Finset (V × U)) (hJ : J ≤ tensor G F) (hs : J.support ⊆ S) (hf : H.Free (J.induce (S : Set _)))
    {α C B DG DF : ℝ} (ha : 1 ≤ α) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hDG : 0 ≤ DG) (hDF : 0 ≤ DF)
    (hUpper : ∀ s : ℕ, (extremalNumber s H : ℝ) ≤ C*(s : ℝ)^α+B*s)
    (hG : ∀ v, (G.degree v : ℝ) ≤ DG) (hF : ∀ u, (F.degree u : ℝ) ≤ DF) :
    2*(Nat.card J.edgeSet : ℝ) ≤ (C*(DG+DF)^α+B*(DG+DF))*S.card := by
  let M := C*(DG+DF)^(α-1)+B
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hlocal (v : V) (u : U) :
      (extremalNumber (active G F S v u).card H : ℝ) ≤ M*(active G F S v u).card := by
    apply (hUpper _).trans
    have hd : ((active G F S v u).card : ℝ) ≤ DG+DF := by
      have hh : ((active G F S v u).card : ℝ) ≤ (F.degree u : ℝ)+G.degree v := by
        exact_mod_cast active_card_le G F S v u
      linarith [hG v,hF u]
    have hp := mul_le_mul_of_nonneg_left
      (rpow_linear_bound (Nat.cast_nonneg _) hd ha) hC
    dsimp [M]
    nlinarith only [hp]
  have hsum : (∑ v : V, ∑ u : U, ((active G F S v u).card : ℝ)) =
      ∑ p ∈ S, ((G.degree p.1 : ℝ)+F.degree p.2) := by
    exact_mod_cast sum_active_card G F S
  have hR : 2*(Nat.card J.edgeSet : ℝ) ≤
      ∑ v : V, ∑ u : U, (extremalNumber (active G F S v u).card H : ℝ) := by
    exact_mod_cast edge_bound H G F J S hJ hs hf
  calc
    _ ≤ ∑ v : V, ∑ u : U, M*(active G F S v u).card :=
      hR.trans (sum_le_sum (fun v _ => sum_le_sum (fun u _ => hlocal v u)))
    _ = M * (∑ p ∈ S, ((G.degree p.1 : ℝ)+F.degree p.2)) := by
      simp_rw [← mul_sum]
      rw [hsum]
    _ ≤ M*((DG+DF)*S.card) := by
      apply mul_le_mul_of_nonneg_left _ hM
      calc
        _ ≤ ∑ _p ∈ S, (DG+DF) := sum_le_sum (fun p _ => add_le_add (hG p.1) (hF p.2))
        _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
    _ = _ := by
      rw [rpow_eq_linear (add_nonneg hDG hDF) ha]
      dsimp [M]
      ring

lemma self_bound {n : ℕ} (H : SimpleGraph W) (G : SimpleGraph (Fin n))
    (J : SimpleGraph (Fin n × Fin n)) (S : Finset (Fin n × Fin n))
    (hn : 1 ≤ n) (hJ : J ≤ tensor G G) (hs : J.support ⊆ S) (hf : H.Free (J.induce (S : Set _)))
    {α C B D : ℝ} (ha : 1 ≤ α) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hUpper : ∀ s : ℕ, (extremalNumber s H : ℝ) ≤ C*(s : ℝ)^α+B*s)
    (hG : ∀ v, (G.degree v : ℝ) ≤ D*(n : ℝ)^(α-1)) :
    2*(Nat.card J.edgeSet : ℝ) ≤
      (C*(2*D)^α+2*B*D)*(n : ℝ)^(α*(α-1))*S.card := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := bounded_degrees H G G J S hJ hs hf ha hC hB
    (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hUpper hG hG
  have he : (D*(n : ℝ)^(α-1)+D*(n : ℝ)^(α-1))^α =
      (2*D)^α*(n : ℝ)^(α*(α-1)) := by
    rw [show D*(n : ℝ)^(α-1)+D*(n : ℝ)^(α-1) = (2*D)*(n : ℝ)^(α-1) by ring,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 2
    ring
  have hp : (n : ℝ)^(α-1) ≤ (n : ℝ)^(α*(α-1)) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith [sq_nonneg (α-1)])
  have hBD := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*B*D by positivity)
  rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  nlinarith only [hBD]

lemma self_ratio_bound {n : ℕ} (H : SimpleGraph W) (G : SimpleGraph (Fin n))
    (J : SimpleGraph (Fin n × Fin n)) (S : Finset (Fin n × Fin n))
    (hn : 1 ≤ n) (hJ : J ≤ tensor G G) (hs : J.support ⊆ S) (hf : H.Free (J.induce (S : Set _)))
    {α C B D : ℝ} (ha : 1 < α) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hUpper : ∀ s : ℕ, (extremalNumber s H : ℝ) ≤ C*(s : ℝ)^α+B*s)
    (hG : ∀ v, (G.degree v : ℝ) ≤ D*(n : ℝ)^(α-1)) :
    (Nat.card J.edgeSet : ℝ)/(S.card : ℝ)^α ≤
      (C*(2*D)^α+2*B*D)*((n : ℝ)^α/S.card)^(α-1) := by
  by_cases hz : S.card = 0
  · simp only [hz,Nat.cast_zero,Real.zero_rpow (show α ≠ 0 by linarith),
      div_zero,Real.zero_rpow (show α-1 ≠ 0 by linarith),mul_zero,le_refl]
  have hm : (0 : ℝ) < S.card := by exact_mod_cast (Nat.pos_of_ne_zero hz)
  have hh := self_bound H G J S hn hJ hs hf ha.le hC hB hD hUpper hG
  have he : (Nat.card J.edgeSet : ℝ) ≤
      (C*(2*D)^α+2*B*D)*(n : ℝ)^(α*(α-1))*S.card := by
    linarith [Nat.cast_nonneg (α := ℝ) (Nat.card J.edgeSet)]
  apply (div_le_div_of_nonneg_right he (Real.rpow_nonneg hm.le _)).trans_eq
  rw [Real.div_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hm.le,
    ← Real.rpow_mul (Nat.cast_nonneg _), rpow_eq_linear hm.le ha.le]
  field_simp

open Filter in
/-- If the support order grows faster than n^alpha, the retained edge count
is negligible at that support's alpha-power scale. The remaining range
of order O(n^alpha) is not excluded by this theorem. -/
theorem power_scale_loss (H : SimpleGraph W) {α C B D : ℝ}
    (ha : 1 < α) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hUpper : ∀ s : ℕ, (extremalNumber s H : ℝ) ≤ C*(s : ℝ)^α+B*s)
    (G : (n : ℕ) → SimpleGraph (Fin n))
    (J : (n : ℕ) → SimpleGraph (Fin n × Fin n))
    (S : (n : ℕ) → Finset (Fin n × Fin n))
    (hG : ∀ n v, ((G n).degree v : ℝ) ≤ D*(n : ℝ)^(α-1))
    (hJ : ∀ n, J n ≤ tensor (G n) (G n))
    (hs : ∀ n, (J n).support ⊆ S n) (hf : ∀ n, H.Free ((J n).induce (S n : Set _)))
    (hSize : Tendsto (fun n : ℕ => (n : ℝ)^α/(S n).card) atTop (nhds 0)) :
    Tendsto (fun n => (Nat.card (J n).edgeSet : ℝ)/((S n).card : ℝ)^α) atTop (nhds 0) := by
  have hP := hSize.rpow_const (Or.inr (show 0 ≤ α-1 by linarith))
  rw [Real.zero_rpow (show α-1 ≠ 0 by linarith)] at hP
  have hK := hP.const_mul (C*(2*D)^α+2*B*D)
  rw [mul_zero] at hK
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hK
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact self_ratio_bound H (G n) (J n) (S n) hn (hJ n) (hs n) (hf n)
    ha hC hB hD hUpper (hG n)

/-- The zero-edge extension of a graph on a selected vertex set. We do not
assert that extension preserves H-freeness on the enlarged universe. -/
def extend (S : Finset V) (R : SimpleGraph S) : SimpleGraph V :=
  R.map ⟨Subtype.val,Subtype.val_injective⟩

lemma extend_support (S : Finset V) (R : SimpleGraph S) : (extend S R).support ⊆ S := by
  rw [extend,support_map]
  rintro _ ⟨x,_,rfl⟩
  exact x.property

lemma extend_induce (S : Finset V) (R : SimpleGraph S) :
    (extend S R).induce (S : Set V) = R := by
  ext x y
  exact map_adj_apply

lemma extend_le {T : SimpleGraph V} (S : Finset V) (R : SimpleGraph S)
    (h : R ≤ T.induce (S : Set V)) : extend S R ≤ T := by
  rintro _ _ ⟨x,y,hxy,rfl,rfl⟩
  exact h hxy

lemma extend_edge_card [Fintype V] (S : Finset V) (R : SimpleGraph S) :
    Nat.card (extend S R).edgeSet = Nat.card R.edgeSet := by
  have h := card_edgeFinset_map (⟨Subtype.val,Subtype.val_injective⟩ : S ↪ V) R
  simpa only [extend,edgeFinset_card,← Nat.card_eq_fintype_card] using h

/-- The same finite bound stated directly for a graph whose vertex type is
the selected subset. This includes forbidden graphs with isolated vertices. -/
theorem bounded_degrees_on_subset [Fintype V] [Fintype U] (H : SimpleGraph W)
    (G : SimpleGraph V) (F : SimpleGraph U) (S : Finset (V × U)) (R : SimpleGraph S)
    (hR : R ≤ (tensor G F).induce (S : Set _)) (hf : H.Free R)
    {α C B DG DF : ℝ} (ha : 1 ≤ α) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hDG : 0 ≤ DG) (hDF : 0 ≤ DF)
    (hUpper : ∀ s : ℕ, (extremalNumber s H : ℝ) ≤ C*(s : ℝ)^α+B*s)
    (hG : ∀ v, (G.degree v : ℝ) ≤ DG) (hF : ∀ u, (F.degree u : ℝ) ≤ DF) :
    2*(Nat.card R.edgeSet : ℝ) ≤ (C*(DG+DF)^α+B*(DG+DF))*S.card := by
  have hf' : H.Free ((extend S R).induce (S : Set _)) := by rwa [extend_induce]
  have hh := bounded_degrees H G F (extend S R) S (extend_le S R hR)
    (extend_support S R) hf' ha hC hB hDG hDF hUpper hG hF
  rwa [extend_edge_card] at hh

#print axioms active_card
#print axioms sum_active_card
#print axioms rectangle_induce_copy
#print axioms support_bound_of_induce_free
#print axioms support_bound
#print axioms rectangle_bound
#print axioms edge_bound
#print axioms bounded_degrees
#print axioms self_bound
#print axioms self_ratio_bound
#print axioms power_scale_loss
#print axioms extend_edge_card
#print axioms bounded_degrees_on_subset
end Erdos713TensorVertexSelection
