import Submission.SmoothHarmonic

/-!
Finite truncation and prime-set extension for the smooth harmonic criterion.
These lemmas do not give the vanishing estimate needed to settle the conjecture.
-/

namespace Erdos1206
open Finset
open scoped Classical

noncomputable def smoothReciprocalMass (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P with Nat.Prime p, (1 - (p : ℝ)⁻¹)⁻¹

lemma smooth_reciprocals_hasSum (P : Finset ℕ) :
    HasSum ((Nat.factoredNumbers P).indicator (fun n : ℕ => (1 : ℝ) / n))
      (smoothReciprocalMass P) := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ)⁻¹
      map_one' := by simp
      map_mul' := by intros; simp [mul_inv_rev, mul_comm] }
  have hp {p : ℕ} (h : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast h.one_lt)
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := f) hp P).2
  have hh' := hasSum_subtype_iff_indicator.mp hh
  simpa [f, smoothReciprocalMass, one_div] using hh'

lemma finite_smooth_reciprocal_bound {P S : Finset ℕ}
    (hS : ∀ s ∈ S, s ∈ Nat.factoredNumbers P) :
    (∑ s ∈ S, (1 : ℝ) / s) ≤ smoothReciprocalMass P := by
  have hh := smooth_reciprocals_hasSum P
  calc
    _ = ∑ s ∈ S, (Nat.factoredNumbers P).indicator (fun n : ℕ => (1 : ℝ) / n) s := by
      apply sum_congr rfl
      intro s hs
      simp [hS s hs]
    _ ≤ ∑' s, (Nat.factoredNumbers P).indicator (fun n : ℕ => (1 : ℝ) / n) s :=
      hh.summable.sum_le_tsum S (fun n _ => by simp only [Set.indicator_apply]; split_ifs <;> positivity)
    _ = _ := hh.tsum_eq

/-- Finite-prefix optimization plus an explicit reciprocal tail gives a bound
for every finite smooth-root set, not just sets in the computed prefix. -/
lemma smooth_harmonic_bound_of_finite_prefix (P : Finset ℕ) (T : ℕ) (B : ℝ)
    (hB : ∀ S : Finset ℕ, S ⊆ (Icc 1 T).filter (fun n => n ∈ Nat.factoredNumbers P) →
      (∀ s ∈ S, s ∈ Nat.factoredNumbers P) →
      IsSidon ((fun n : ℕ => n ^ 3) '' (S : Set ℕ)) → (∑ s ∈ S, (1 : ℝ) / s) ≤ B) :
    SmoothCubeHarmonicBound P
      (B + smoothReciprocalMass P -
        ∑ s ∈ (Icc 1 T).filter (fun n => n ∈ Nat.factoredNumbers P), (1 : ℝ) / s) := by
  intro S hS hsid
  let U := (Icc 1 T).filter (fun n => n ∈ Nat.factoredNumbers P)
  have hpre : (∑ s ∈ S ∩ U, (1 : ℝ) / s) ≤ B := by
    apply hB
    · exact inter_subset_right
    · intro s hs; exact hS s (mem_inter.mp hs).1
    · apply Set.IsSidon.subset hsid
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨s, (mem_inter.mp hs).1, rfl⟩
  have hall : (∑ s ∈ (S \ U) ∪ U, (1 : ℝ) / s) ≤ smoothReciprocalMass P := by
    apply finite_smooth_reciprocal_bound
    intro s hs
    rcases mem_union.mp hs with hs | hs
    · exact hS s (mem_sdiff.mp hs).1
    · exact (mem_filter.mp hs).2
  have hdis : Disjoint (S \ U) U := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp hx).2 hy
  rw [sum_union hdis] at hall
  have hsplit : (∑ s ∈ S \ U, (1 : ℝ) / s) + ∑ s ∈ S ∩ U, (1 : ℝ) / s =
      ∑ s ∈ S, (1 : ℝ) / s := by
    rw [← sum_union (disjoint_sdiff_inter S U)]
    congr 1
    exact sdiff_union_inter S U
  dsimp [U] at hpre hall hsplit ⊢
  linarith

/-- Adding primes to the smooth universe cannot increase the best bound
normalized by its total reciprocal mass. -/
lemma SmoothCubeHarmonicBound.extend {P Q : Finset ℕ} {B : ℝ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hB : SmoothCubeHarmonicBound P B) :
    SmoothCubeHarmonicBound Q (B * smoothReciprocalMass (Q \ P)) := by
  classical
  intro S hS hsid
  have hB0 : 0 ≤ B := by
    have hh := hB ∅ (by simp) (by simp [IsSidon]); simpa using hh
  have hd (n : ℕ) : ∃ r s : ℕ, n ∈ S →
      primeRough P r ∧ s ∈ Nat.factoredNumbers P ∧ r * s = n := by
    by_cases hn : n ∈ S
    · obtain ⟨r, s, hh⟩ := factored_rough_decomposition P hP
        (Nat.pos_of_ne_zero (hS n hn).1)
      exact ⟨r, s, fun _ => hh⟩
    · exact ⟨1, 1, fun hh => (hn hh).elim⟩
  choose r s hrs using hd
  let R := S.image r
  let V (q : ℕ) := (S.filter (fun n => r n = q)).image s
  have hR (q : ℕ) (hq : q ∈ R) : q ∈ Nat.factoredNumbers (Q \ P) := by
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
    have hh := hrs n hn
    have hrd : r n ∣ n := ⟨s n, hh.2.2.symm⟩
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpr
    refine mem_sdiff.mpr ⟨Nat.mem_factoredNumbers'.mp (hS n hn) p hp (hpr.trans hrd), ?_⟩
    intro hpP
    exact hh.1.2 p hpP hpr
  have hV (q : ℕ) (hq : q ∈ R) : (∑ t ∈ V q, (1 : ℝ) / t) ≤ B := by
    apply hB
    · intro t ht
      obtain ⟨n, hn, rfl⟩ := mem_image.mp ht
      exact (hrs n (mem_filter.mp hn).1).2.1
    · apply Set.IsSidon.subset (cube_sidon_dilation_preimage hsid
        (Nat.pos_of_ne_zero (hR q hq).1))
      rintro _ ⟨t, ht, rfl⟩
      change t ∈ V q at ht
      obtain ⟨n, hn, rfl⟩ := mem_image.mp ht
      have hh := hrs n (mem_filter.mp hn).1
      refine ⟨s n, ?_, rfl⟩
      change q * s n ∈ S
      rw [← (mem_filter.mp hn).2, hh.2.2]
      exact (mem_filter.mp hn).1
  have he : (∑ n ∈ S, (1 : ℝ) / n) =
      ∑ q ∈ R, ((1 : ℝ) / q) * ∑ t ∈ V q, (1 : ℝ) / t := by
    rw [← sum_fiberwise_of_maps_to (fun n hn => mem_image.mpr ⟨n, hn, rfl⟩ :
      ∀ n ∈ S, r n ∈ R) (fun n : ℕ => (1 : ℝ) / n)]
    apply sum_congr rfl
    intro q hq
    have hi : Set.InjOn s ((S.filter (fun n => r n = q)) : Set ℕ) := by
      intro n hn m hm he
      change n ∈ S.filter (fun n => r n = q) at hn
      change m ∈ S.filter (fun n => r n = q) at hm
      have hn' := hrs n (mem_filter.mp hn).1
      have hm' := hrs m (mem_filter.mp hm).1
      rw [← hn'.2.2, ← hm'.2.2, (mem_filter.mp hn).2, (mem_filter.mp hm).2, he]
    dsimp only [V]
    rw [sum_image hi, mul_sum]
    apply sum_congr rfl
    intro n hn
    have hh := hrs n (mem_filter.mp hn).1
    have he' : q * s n = n := by
      rw [← (mem_filter.mp hn).2]
      exact hh.2.2
    calc
      (1 : ℝ) / n = (1 : ℝ) / (q * s n : ℕ) :=
        congrArg (fun t : ℕ => (1 : ℝ) / t) he'.symm
      _ = ((1 : ℝ) / q) * ((1 : ℝ) / s n) := by
        simp [Nat.cast_mul, one_div, mul_inv_rev, mul_comm]
  rw [he]
  calc
    _ ≤ ∑ q ∈ R, ((1 : ℝ) / q) * B :=
      sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hV q hq) (by positivity)
    _ = B * ∑ q ∈ R, (1 : ℝ) / q := by rw [← sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_smooth_reciprocal_bound hR) hB0

#print axioms smooth_reciprocals_hasSum
#print axioms smooth_harmonic_bound_of_finite_prefix
#print axioms SmoothCubeHarmonicBound.extend

end Erdos1206
