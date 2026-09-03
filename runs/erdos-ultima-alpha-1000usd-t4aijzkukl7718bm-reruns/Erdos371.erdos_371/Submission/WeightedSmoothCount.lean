import FormalConjecturesUtil

/-! A weighted squarefree-part bound for smooth integers.
This file contains only counting estimates, not a proof of Erdős 371. -/

namespace Erdos371WeightedSmoothCount

lemma reciprocal_sqrt_step (k : ℕ) :
    1 / Real.sqrt (k + 1 : ℕ) ≤ 2 * (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) := by
  have hx : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have hy : 0 < Real.sqrt (k + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hx2 := Real.sq_sqrt (Nat.cast_nonneg k)
  have hy2 := Real.sq_sqrt (Nat.cast_nonneg (k + 1))
  apply (div_le_iff₀ hy).mpr
  have hz := sq_nonneg (Real.sqrt (k + 1 : ℕ) - Real.sqrt k)
  push_cast at *
  nlinarith

lemma reciprocal_sqrt_sum (K : ℕ) :
    (∑ p ∈ Finset.Icc 1 K, 1 / Real.sqrt p) ≤ 2 * Real.sqrt K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs := reciprocal_sqrt_step K
    push_cast at hs ⊢
    linarith

lemma smooth_product_bound (K : ℕ) :
    (∏ p ∈ Finset.Icc 1 K, (1 + 1 / Real.sqrt p)) ≤ Real.exp (2 * Real.sqrt K) := by
  calc
    _ ≤ ∏ p ∈ Finset.Icc 1 K, Real.exp (1 / Real.sqrt p) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa [add_comm] using Real.add_one_le_exp (1 / Real.sqrt p)
    _ = Real.exp (∑ p ∈ Finset.Icc 1 K, 1 / Real.sqrt p) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (reciprocal_sqrt_sum K)

lemma weighted_sqrt_quotient (N : ℕ) {a : ℕ} (_ha : 0 < a) :
    ((Nat.sqrt (N / a) : ℕ) : ℝ) ≤ Real.sqrt N / Real.sqrt a := by
  calc
    _ ≤ Real.sqrt (N / a : ℕ) := Real.nat_sqrt_le_real_sqrt
    _ ≤ Real.sqrt ((N : ℝ) / a) := Real.sqrt_le_sqrt Nat.cast_div_le
    _ = _ := Real.sqrt_div (Nat.cast_nonneg N) _

lemma positive_smooth_weighted_count (K N : ℕ) :
    (((Finset.range N).filter (fun n => n ≠ 0 ∧ Nat.maxPrimeFac n ≤ K)).card : ℝ) ≤
      Real.sqrt N * (∏ p ∈ Finset.Icc 1 K, (1 + 1 / Real.sqrt p)) := by
  let S := Finset.Icc 1 K
  let F (t : Finset ℕ) := (Finset.Icc 1 (Nat.sqrt (N / (∏ p ∈ t, p)))).image
    (fun b => b ^ 2 * (∏ p ∈ t, p))
  let G := (Finset.range N).filter (fun n => n ≠ 0 ∧ Nat.maxPrimeFac n ≤ K)
  have htpos (t : Finset ℕ) (ht : t ∈ S.powerset) : 0 < ∏ p ∈ t, p := by
    apply Finset.prod_pos
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_powerset.mp ht hp)).1
  have hsub : G ⊆ S.powerset.biUnion F := by
    intro n hn
    obtain ⟨hnN, hn0, hnK⟩ := Finset.mem_filter.mp hn
    obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
    have hadvd : a ∣ n := hab ▸ dvd_mul_left a (b ^ 2)
    have hsuba : a.primeFactors ⊆ S := by
      intro p hp
      obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
      exact Finset.mem_Icc.mpr ⟨hpp.one_lt.le,
        (Nat.le_maxPrimeFac hn0 hpp (hpd.trans hadvd)).trans hnK⟩
    have hprod : (∏ p ∈ a.primeFactors, p) = a := Nat.prod_primeFactors_of_squarefree ha
    have hbpos : 0 < b := by
      by_contra hh
      have hb0 : b = 0 := by omega
      simp [hb0] at hab
      exact hn0 hab.symm
    have hbnd : b ≤ Nat.sqrt (N / a) := by
      apply Nat.le_sqrt'.mpr
      apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero ha.ne_zero)).mpr
      rw [hab]
      exact (Finset.mem_range.mp hnN).le
    apply Finset.mem_biUnion.mpr
    refine ⟨a.primeFactors, Finset.mem_powerset.mpr hsuba, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨b, ?_, ?_⟩
    · rw [hprod]
      exact Finset.mem_Icc.mpr ⟨hbpos, hbnd⟩
    · simpa [hprod] using hab
  have hcount : G.card ≤ ∑ t ∈ S.powerset, Nat.sqrt (N / (∏ p ∈ t, p)) := by
    calc
      G.card ≤ (S.powerset.biUnion F).card := Finset.card_le_card hsub
      _ ≤ ∑ t ∈ S.powerset, (F t).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ S.powerset, Nat.sqrt (N / (∏ p ∈ t, p)) := by
        apply Finset.sum_le_sum
        intro t ht
        simpa [F] using Finset.card_image_le (s := Finset.Icc 1 (Nat.sqrt (N / (∏ p ∈ t, p))))
  change (G.card : ℝ) ≤ _
  calc
    _ ≤ ∑ t ∈ S.powerset, ((Nat.sqrt (N / (∏ p ∈ t, p)) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    _ ≤ ∑ t ∈ S.powerset, Real.sqrt N / Real.sqrt (∏ p ∈ t, p : ℕ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact weighted_sqrt_quotient N (htpos t ht)
    _ = Real.sqrt N * ∑ t ∈ S.powerset, ∏ p ∈ t, (1 / Real.sqrt p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const_one, mul_one_div]
      congr 2
      push_cast
      exact Real.sqrt_prod t (fun p hp => Nat.cast_nonneg p)
    _ = _ := by rw [← Finset.prod_one_add]

lemma smooth_count_exp_bound (K N : ℕ) :
    (((Finset.range N).filter (fun n => Nat.maxPrimeFac n ≤ K)).card : ℝ) ≤
      1 + Real.sqrt N * Real.exp (2 * Real.sqrt K) := by
  let G := (Finset.range N).filter (fun n => n ≠ 0 ∧ Nat.maxPrimeFac n ≤ K)
  have hsub : (Finset.range N).filter (fun n => Nat.maxPrimeFac n ≤ K) ⊆ insert 0 G := by
    intro n hn
    by_cases hz : n = 0
    · simp [hz]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hn).1, hz, (Finset.mem_filter.mp hn).2⟩)
  have hc : ((Finset.range N).filter (fun n => Nat.maxPrimeFac n ≤ K)).card ≤ 1 + G.card := by
    have hh := (Finset.card_le_card hsub).trans (Finset.card_insert_le 0 G)
    omega
  have hc' : (((Finset.range N).filter (fun n => Nat.maxPrimeFac n ≤ K)).card : ℝ) ≤ 1 + G.card := by
    exact_mod_cast hc
  have hg : (G.card : ℝ) ≤ Real.sqrt N * Real.exp (2 * Real.sqrt K) :=
    (positive_smooth_weighted_count K N).trans
      (mul_le_mul_of_nonneg_left (smooth_product_bound K) (Real.sqrt_nonneg _))
  linarith

end Erdos371WeightedSmoothCount

#print axioms Erdos371WeightedSmoothCount.smooth_count_exp_bound
