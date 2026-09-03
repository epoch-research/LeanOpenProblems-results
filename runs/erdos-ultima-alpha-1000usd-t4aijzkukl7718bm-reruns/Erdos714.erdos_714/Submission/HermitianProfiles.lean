import Submission.Profiles

/-!
An edge bound for graphs whose restrictions to affine slices are Hermitian
quadratic equations. This is a model obstruction, not a solution of Erdős 714.
-/

open SimpleGraph Finset Polynomial Classical
open Erdos714Packing Erdos714Profiles

namespace Erdos714HermitianProfiles

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- A Hermitian quadratic in one extension-field variable. -/
noncomputable def equation (a : F) (b : E) (c : F) : E[X] :=
  C (algebraMap F E a) * X ^ (Fintype.card F + 1) + C b * X ^ Fintype.card F +
    C (b ^ Fintype.card F) * X + C (algebraMap F E c)

/-- The finite zero set, including the whole field when the polynomial is zero. -/
noncomputable def zeros (p : E[X]) : Finset E := univ.filter (fun x => p.eval x = 0)

lemma zeros_bound {p : E[X]} (hp : p ≠ 0) : (zeros p).card ≤ p.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  exact (Polynomial.mem_roots hp).mpr (mem_filter.mp hx).2

omit [Fintype E] in
lemma equation_degree (a : F) (b : E) (c : F) :
    (equation a b c).natDegree ≤ Fintype.card F + 1 := by
  unfold equation
  compute_degree

omit [Fintype E] in
lemma equation_coeff_top (a : F) (b : E) (c : F) :
    (equation a b c).coeff (Fintype.card F + 1) = algebraMap F E a := by
  have hq := Fintype.one_lt_card (α := F)
  simp only [equation, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  simp

omit [Fintype E] in
lemma quadratic_nonzero (b : E) (c : F) : equation (1 : F) b c ≠ 0 := by
  intro h
  have hc := congrArg (fun p : E[X] => p.coeff (Fintype.card F + 1)) h
  simp [equation_coeff_top] at hc

omit [Fintype E] in
lemma linear_nonzero (b : E) (c : F) (h : (b,c) ≠ (0,0)) :
    equation (0 : F) b c ≠ 0 := by
  have hq := Fintype.one_lt_card (α := F)
  by_cases hb : b = 0
  · subst b
    have hc : c ≠ 0 := by simpa using h
    simpa [equation] using ((_root_.map_ne_zero (algebraMap F E)).mpr hc)
  · intro he
    have hc := congrArg (fun p : E[X] => p.coeff (Fintype.card F)) he
    have hcoeff : (equation (0 : F) b c).coeff (Fintype.card F) = b := by
      simp only [equation, map_zero, zero_mul, zero_add, coeff_add, coeff_C_mul,
        coeff_X_pow, coeff_X, coeff_C]
      split_ifs <;> simp_all
    exact hb (by simpa [hcoeff] using hc)

/-- Two coefficient families suffice: linear equations and monic quadratics. -/
noncomputable def profile : (E × F) ⊕ (E × F) → Finset E
  | .inl p => zeros (equation (0 : F) p.1 p.2)
  | .inr p => zeros (equation (1 : F) p.1 p.2)

/-- Every profile has at most q+1 zeros, except for the single zero polynomial. -/
lemma profile_sum_bound :
    ∑ p : (E × F) ⊕ (E × F), (profile p).card ≤
      2 * Fintype.card E * Fintype.card F * (Fintype.card F + 1) + Fintype.card E := by
  have hquad (p : E × F) : (profile (.inr p)).card ≤ Fintype.card F + 1 :=
    (zeros_bound (quadratic_nonzero p.1 p.2)).trans (equation_degree 1 p.1 p.2)
  have hlin (p : E × F) : (profile (.inl p)).card ≤
      (Fintype.card F+1) + if p = (0,0) then Fintype.card E else 0 := by
    by_cases hp : p = (0,0)
    · subst p
      simp [profile, zeros, equation]
    · simp only [hp, if_false, add_zero]
      exact (zeros_bound (linear_nonzero p.1 p.2 hp)).trans (equation_degree 0 p.1 p.2)
  rw [Fintype.sum_sum_type]
  calc
    _ ≤ (∑ p : E × F, ((Fintype.card F+1) +
          if p = (0,0) then Fintype.card E else 0)) +
        ∑ _p : E × F, (Fintype.card F+1) :=
      Nat.add_le_add (sum_le_sum (fun p _ => hlin p)) (sum_le_sum (fun p _ => hquad p))
    _ = _ := by simp [sum_add_distrib]; ring

/-- Normalize a nonzero norm coefficient; leave a linear equation unchanged. -/
noncomputable def label (a : F) (b : E) (c : F) : (E × F) ⊕ (E × F) :=
  if a = 0 then .inl (b,c) else .inr (b / algebraMap F E a, c / a)

omit [Fintype E] in
lemma normalized_eval (a : F) (ha : a ≠ 0) (b x : E) (c : F) :
    (equation a b c).eval x = algebraMap F E a *
      (equation (1 : F) (b / algebraMap F E a) (c / a)).eval x := by
  have haE : algebraMap F E a ≠ 0 := (_root_.map_ne_zero (algebraMap F E)).mpr ha
  have hpow : (algebraMap F E a) ^ Fintype.card F = algebraMap F E a := by
    rw [← map_pow, FiniteField.pow_card]
  simp only [equation, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    map_one, one_mul, map_div₀, div_pow, hpow]
  field_simp

lemma zeros_eq_profile (a : F) (b : E) (c : F) :
    zeros (equation a b c) = profile (label a b c) := by
  ext x
  by_cases ha : a = 0
  · subst a
    simp [label, profile]
  · simp only [label, ha, if_false, profile, zeros, mem_filter, mem_univ, true_and]
    rw [normalized_eval a ha b x c]
    simp [(_root_.map_ne_zero (algebraMap F E)).mpr ha]

variable {R T : Type*} [Fintype R] [Fintype T]

/-- Arbitrary column-dependent Hermitian equations on each coordinate slice. -/
noncomputable def neighbors (A C : T → R → F) (B : T → R → E) (v : R) : Finset (T × E) :=
  univ.filter (fun p => (equation (A p.1 v) (B p.1 v) (C p.1 v)).eval p.2 = 0)

omit [Fintype R] in
lemma neighbors_eq_slices (A C : T → R → F) (B : T → R → E) :
    neighbors A C B = slices (fun _ : T => profile)
      (fun t v => label (A t v) (B t v) (C t v)) := by
  funext v
  ext p
  simp only [neighbors, slices, mem_filter, mem_univ, true_and]
  have h := congrArg (fun s : Finset E => p.2 ∈ s)
    (zeros_eq_profile (A p.1 v) (B p.1 v) (C p.1 v))
  simpa [zeros] using h

/-- A Krr-free graph in this model has few edges, irrespective of how its
coefficients vary between slices and columns. -/
theorem edge_bound (A C : T → R → F) (B : T → R → E) {r : ℕ} (hr : 0 < r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence (neighbors A C B))) :
    (incidence (neighbors A C B)).edgeFinset.card ≤
      Fintype.card T * ((r-1)*(Fintype.card R +
        2*Fintype.card E*Fintype.card F*(Fintype.card F+1) + Fintype.card E)) := by
  rw [neighbors_eq_slices] at hfree ⊢
  have h := sliced_edge_bound (fun _ : T => (profile (F := F) (E := E)))
    (fun t v => label (A t v) (B t v) (C t v)) hr (fun _ => profile_sum_bound) hfree
  simpa only [add_assoc] using h

/-- With q^4 columns and q^2 slices in a quadratic extension, the edge bound
is O(q^6), not the q^7 required by the conjectured fourth-case construction. -/
theorem fourth_case_bound (A C : T → R → F) (B : T → R → E)
    (hE : Module.finrank F E = 2) (hT : Fintype.card T = Fintype.card F ^ 2)
    (hR : Fintype.card R = Fintype.card F ^ 4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (neighbors A C B))) :
    (incidence (neighbors A C B)).edgeFinset.card ≤ 18 * Fintype.card F ^ 6 := by
  have h := edge_bound A C B (by decide : 0 < 4) hfree
  have hcE : Fintype.card E = Fintype.card F ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E), hE]
  rw [hT, hR, hcE] at h
  norm_num only [Nat.reduceSub] at h
  apply h.trans
  have hq : 1 ≤ Fintype.card F := (Fintype.one_lt_card (α := F)).le
  have h45 : Fintype.card F ^ 4 ≤ Fintype.card F ^ 6 := pow_le_pow_right' hq (by decide)
  have h56 : Fintype.card F ^ 5 ≤ Fintype.card F ^ 6 := pow_le_pow_right' hq (by decide)
  nlinarith

/-- Arbitrary row-vertex selections can be described independently on each slice. -/
noncomputable def neighborsOn (W : T → Finset E) (A C : T → R → F) (B : T → R → E)
    (v : R) : Finset (T × E) :=
  univ.filter (fun p => p.2 ∈ W p.1 ∧
    (equation (A p.1 v) (B p.1 v) (C p.1 v)).eval p.2 = 0)

omit [Fintype R] in
lemma neighborsOn_eq_slices (W : T → Finset E) (A C : T → R → F) (B : T → R → E) :
    neighborsOn W A C B = slices (fun t p => W t ∩ profile p)
      (fun t v => label (A t v) (B t v) (C t v)) := by
  funext v
  ext p
  simp only [neighborsOn, slices, mem_filter, mem_univ, true_and, mem_inter]
  have h := congrArg (fun s : Finset E => p.2 ∈ s)
    (zeros_eq_profile (A p.1 v) (B p.1 v) (C p.1 v))
  simpa [zeros] using and_congr_right (fun _ => Iff.of_eq h)

/-- The profile estimate survives every row-vertex selection. The column type
is arbitrary too, so column selections can be represented by subtypes. -/
theorem selected_edge_bound (W : T → Finset E) (A C : T → R → F) (B : T → R → E)
    {r : ℕ} (hr : 0 < r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free
      (incidence (neighborsOn W A C B))) :
    (incidence (neighborsOn W A C B)).edgeFinset.card ≤
      Fintype.card T * ((r-1)*(Fintype.card R +
        2*Fintype.card E*Fintype.card F*(Fintype.card F+1) + Fintype.card E)) := by
  rw [neighborsOn_eq_slices] at hfree ⊢
  have hbound (t : T) : ∑ p : (E × F) ⊕ (E × F), (W t ∩ profile p).card ≤
      2*Fintype.card E*Fintype.card F*(Fintype.card F+1) + Fintype.card E := by
    exact (sum_le_sum (fun _ _ => card_le_card inter_subset_right)).trans profile_sum_bound
  have h := sliced_edge_bound (fun t p => W t ∩ profile p)
    (fun t v => label (A t v) (B t v) (C t v)) hr hbound hfree
  simpa only [add_assoc] using h

/-- The same O(q^6) bound holds for all induced vertex selections in the model. -/
theorem selected_fourth_case_bound (W : T → Finset E) (A C : T → R → F)
    (B : T → R → E) (hE : Module.finrank F E = 2)
    (hT : Fintype.card T ≤ Fintype.card F ^ 2) (hR : Fintype.card R ≤ Fintype.card F ^ 4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (incidence (neighborsOn W A C B))) :
    (incidence (neighborsOn W A C B)).edgeFinset.card ≤ 18 * Fintype.card F ^ 6 := by
  have h := selected_edge_bound W A C B (by decide : 0 < 4) hfree
  have hcE : Fintype.card E = Fintype.card F ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E), hE]
  rw [hcE] at h
  norm_num only [Nat.reduceSub] at h
  apply h.trans
  calc
    _ ≤ Fintype.card F ^ 2 * (3*(Fintype.card F ^ 4 +
        2*Fintype.card F ^ 2*Fintype.card F*(Fintype.card F+1) + Fintype.card F ^ 2)) := by
      exact Nat.mul_le_mul hT (Nat.mul_le_mul_left _ (by omega))
    _ ≤ _ := by
      have hq : 1 ≤ Fintype.card F := (Fintype.one_lt_card (α := F)).le
      have h45 : Fintype.card F ^ 4 ≤ Fintype.card F ^ 6 := pow_le_pow_right' hq (by decide)
      have h56 : Fintype.card F ^ 5 ≤ Fintype.card F ^ 6 := pow_le_pow_right' hq (by decide)
      nlinarith

/-- The polynomial expression is precisely a Hermitian norm-and-trace expression
in a quadratic extension, not just a formal polynomial family. -/
lemma equation_eval_norm_trace (hE : Module.finrank F E = 2) (a c : F) (b x : E) :
    (equation a b c).eval x = algebraMap F E
      (a * Algebra.norm F x + Algebra.trace F E (b * x ^ Fintype.card F) + c) := by
  have hcard : Fintype.card E = Fintype.card F ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E), hE]
  have hx : x ^ (Fintype.card F ^ 2) = x := by
    rw [← hcard, FiniteField.pow_card]
  have hn := FiniteField.algebraMap_norm_eq_pow_sum F E x
  have ht := FiniteField.algebraMap_trace_eq_sum_pow F E (b*x^Fintype.card F)
  rw [hE] at hn ht
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add,
    Nat.card_eq_fintype_card] at hn ht
  simp only [equation, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    map_add, map_mul]
  rw [hn, ht, mul_pow, ← pow_mul]
  rw [show Fintype.card F * Fintype.card F = Fintype.card F ^ 2 by ring, hx]
  ring

/-- Selected-row neighborhoods written using the actual algebra norm and trace. -/
noncomputable def normTraceNeighborsOn (W : T → Finset E) (A C : T → R → F)
    (B : T → R → E) (v : R) : Finset (T × E) :=
  univ.filter (fun p => p.2 ∈ W p.1 ∧
    A p.1 v * Algebra.norm F p.2 +
      Algebra.trace F E (B p.1 v * p.2 ^ Fintype.card F) + C p.1 v = 0)

omit [Fintype R] in
lemma normTraceNeighborsOn_eq (W : T → Finset E) (A C : T → R → F) (B : T → R → E)
    (hE : Module.finrank F E = 2) : normTraceNeighborsOn W A C B = neighborsOn W A C B := by
  funext v
  ext p
  simp only [normTraceNeighborsOn, neighborsOn, mem_filter, mem_univ, true_and,
    equation_eval_norm_trace hE, _root_.map_eq_zero]

/-- A bound for the actual norm/trace version with arbitrary vertex selections. -/
theorem norm_trace_fourth_case_bound (W : T → Finset E) (A C : T → R → F)
    (B : T → R → E) (hE : Module.finrank F E = 2)
    (hT : Fintype.card T ≤ Fintype.card F ^ 2) (hR : Fintype.card R ≤ Fintype.card F ^ 4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (incidence (normTraceNeighborsOn W A C B))) :
    (incidence (normTraceNeighborsOn W A C B)).edgeFinset.card ≤ 18 * Fintype.card F ^ 6 := by
  rw [normTraceNeighborsOn_eq W A C B hE] at hfree ⊢
  exact selected_fourth_case_bound W A C B hE hT hR hfree

end Erdos714HermitianProfiles

#print axioms Erdos714HermitianProfiles.profile_sum_bound
#print axioms Erdos714HermitianProfiles.normalized_eval
#print axioms Erdos714HermitianProfiles.edge_bound
#print axioms Erdos714HermitianProfiles.fourth_case_bound

#print axioms Erdos714HermitianProfiles.selected_edge_bound
#print axioms Erdos714HermitianProfiles.selected_fourth_case_bound
#print axioms Erdos714HermitianProfiles.equation_eval_norm_trace
#print axioms Erdos714HermitianProfiles.norm_trace_fourth_case_bound
