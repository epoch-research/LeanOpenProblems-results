import Submission.DoubleCoverLinearCertificate

/-! A linear bound at thirtieth-power lengths for double covers. -/
namespace Erdos970.DoubleCover
open Finset Real WeightedMertens CoreTailSieve

/-- No triple hit implies a uniform linear bound once the scale exceeds fixed
analytic thresholds. Nothing here removes the multiplicity hypothesis. -/
theorem prime_double_cover_thirtieth (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (t : ℕ) (ht : 2 ≤ t)
    (hl : 2000 * (boundConstant + 1) ≤ log (t : ℝ))
    (hcount : ∀ n : ℕ, t ≤ n → ((n + 1).primesBelow.card : ℝ) ≤ (n : ℝ) / 100)
    (hcover : ∀ x < t ^ 30, ∃ p ∈ P, x ≡ r p [MOD p])
    (hdouble : ∀ x < t ^ 30, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ 2) :
    t ^ 30 ≤ 6000 * P.card := by
  classical
  let Q := P.filter (fun p => p ≤ t ^ 10)
  let R := P.filter (fun p => t ^ 10 < p)
  let A := P.filter (fun p => t ^ 10 < p ∧ p ≤ t ^ 12)
  let B := P.filter (fun p => t ^ 12 < p ∧ p ≤ t ^ 15)
  let C := P.filter (fun p => t ^ 15 < p ∧ p ≤ t ^ 18)
  let D := P.filter (fun p => t ^ 18 < p ∧ p ≤ t ^ 30)
  let E := P.filter (fun p => t ^ 30 < p)
  let H := P.filter (fun p => t ^ 10 < p ∧ p ≤ t ^ 15)
  let F := selectedPairFamily H A C
  let w := fun p : ℕ => 1 / (p : ℝ)
  have ht1 : 1 ≤ t := by omega
  have h1012 : t ^ 10 ≤ t ^ 12 := Nat.pow_le_pow_right ht1 (by omega)
  have h1215 : t ^ 12 ≤ t ^ 15 := Nat.pow_le_pow_right ht1 (by omega)
  have h1518 : t ^ 15 ≤ t ^ 18 := Nat.pow_le_pow_right ht1 (by omega)
  have h1830 : t ^ 18 ≤ t ^ 30 := Nat.pow_le_pow_right ht1 (by omega)
  have hQR : Q ∪ R = P := by
    simpa only [Q, R, not_le] using filter_union_filter_not_eq (fun p => p ≤ t ^ 10) P
  have hQRdis : Disjoint Q R := by
    apply disjoint_left.mpr
    intro p hp hq
    have := (mem_filter.mp hp).2
    have := (mem_filter.mp hq).2
    omega
  have hAH : A ⊆ H := by
    intro p hp
    obtain ⟨hpP, hp10, hp12⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hpP, hp10, hp12.trans h1215⟩
  have hHR : H ⊆ R := fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.1⟩
  have hCR : C ⊆ R := by
    intro p hp
    obtain ⟨hpP, hp15, hp18⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hpP, (h1012.trans h1215).trans_lt hp15⟩
  have hHC : Disjoint H C := by
    apply disjoint_left.mpr
    intro p hp hq
    have := (mem_filter.mp hp).2.2
    have := (mem_filter.mp hq).2.1
    omega
  have hF : F ⊆ R.powersetCard 2 := selectedPairFamily_subset R H A C hHR hAH hCR hHC
  have hQcard : Q.card ≤ 2 :=
    small_core_card_le_two hP hdouble (by simp only [← pow_mul]; norm_num)
  have hm : 0 < t ^ 30 := Nat.pow_pos (by omega)
  have hk : 0 < P.card := by
    obtain ⟨p, hp, _⟩ := hcover 0 hm
    exact card_pos.mpr ⟨p,hp⟩
  have hcaps := four_band_caps P hP t ht hl
  change (∑ p ∈ A, w p) ≤ 184 / 1000 ∧ (∑ p ∈ B, w p) ≤ 225 / 1000 ∧
    (∑ p ∈ C, w p) ≤ 184 / 1000 ∧ (∑ p ∈ D, w p) ≤ 512 / 1000 at hcaps
  have hw0 : ∀ p, 0 ≤ w p := fun p => by dsimp [w]; positivity
  have hHsum : (∑ p ∈ H, w p) = (∑ p ∈ A, w p) + (∑ p ∈ B, w p) :=
    band_sum_split P w _ _ _ h1012 h1215
  have hRsum : (∑ p ∈ R, w p) = (∑ p ∈ A, w p) + (∑ p ∈ B, w p) +
      (∑ p ∈ C, w p) + (∑ p ∈ D, w p) + (∑ p ∈ E, w p) :=
    band_sum_partition P w _ _ _ _ _ h1012 h1215 h1518 h1830
  have htail : (∑ p ∈ E, w p) ≤ (P.card : ℝ) / (t ^ 30 : ℕ) := by
    have hh := tail_sum_le_card_div P (t ^ 30 : ℕ) (by exact_mod_cast hm)
    simpa only [E, w, Nat.cast_lt, one_div] using hh
  have hdiag : (∑ p ∈ H, (w p) ^ 2) ≤ 1 / 1000 := by
    have hlarge : 1000 ≤ t ^ 10 :=
      (by norm_num : 1000 ≤ 2 ^ 10).trans (Nat.pow_le_pow_left ht 10)
    have hs : (∑ p ∈ H, (w p) ^ 2) ≤ (1 / 1000 : ℝ) * ∑ p ∈ H, w p := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hpR : (1000 : ℝ) ≤ p := by
        exact_mod_cast hlarge.trans (mem_filter.mp hp).2.1.le
      have hh : w p ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) hpR
      nlinarith only [mul_le_mul_of_nonneg_right hh (hw0 p)]
    rw [hHsum] at hs
    linarith [hcaps.1, hcaps.2.1]
  have hpoly := four_band_margin (∑ p ∈ A, w p) (∑ p ∈ B, w p)
    (∑ p ∈ C, w p) (∑ p ∈ D, w p)
    (sum_nonneg (fun p _ => hw0 p)) hcaps.1 (sum_nonneg (fun p _ => hw0 p)) hcaps.2.1
    (sum_nonneg (fun p _ => hw0 p)) hcaps.2.2.1 hcaps.2.2.2
  have hmass : (∑ T ∈ F, 1 / ∏ p ∈ T, (p : ℝ)) =
      ((∑ p ∈ H, w p) ^ 2 - ∑ p ∈ H, (w p) ^ 2) / 2 +
        (∑ p ∈ A, w p) * (∑ p ∈ C, w p) := by
    simpa only [w, one_div, prod_inv_distrib] using selectedPairFamily_mass H A C hAH hHC w
  have hmargin : 1 / 100 - (P.card : ℝ) / (t ^ 30 : ℕ) ≤
      1 - (∑ p ∈ R, 1 / (p : ℝ)) + ∑ T ∈ F, 1 / ∏ p ∈ T, (p : ℝ) := by
    change 1 / 100 - (P.card : ℝ) / (t ^ 30 : ℕ) ≤
      1 - (∑ p ∈ R, w p) + ∑ T ∈ F, 1 / ∏ p ∈ T, (p : ℝ)
    rw [hmass, hHsum, hRsum]
    nlinarith only [hpoly, hdiag, htail]
  have hsmall (S : Finset ℕ) (u : ℕ) (hu : 0 < u) (hS : S ⊆ P)
      (huS : ∀ p ∈ S, p ≤ t ^ u) : (S.card : ℝ) ≤ (t : ℝ) ^ u / 100 := by
    have hsub : S ⊆ (t ^ u + 1).primesBelow := by
      intro p hp
      exact WeightedMertens.mem_primes.mpr ⟨hP p (hS hp), huS p hp⟩
    have hs : (S.card : ℝ) ≤ ((t ^ u + 1).primesBelow.card : ℝ) := by exact_mod_cast card_le_card hsub
    exact hs.trans (by simpa only [Nat.cast_pow] using hcount (t ^ u) (Nat.le_pow hu))
  have hHcard := hsmall H 15 (by omega) (filter_subset _ P) (fun p hp => (mem_filter.mp hp).2.2)
  have hAcard := hsmall A 12 (by omega) (filter_subset _ P) (fun p hp => (mem_filter.mp hp).2.2)
  have hCcard := hsmall C 18 (by omega) (filter_subset _ P) (fun p hp => (mem_filter.mp hp).2.2)
  have hFcard : (F.card : ℝ) ≤ (t ^ 30 : ℕ) / 5000 := by
    have hh := selectedPairFamily_card_le H A C
    have hs := mul_self_le_mul_self (Nat.cast_nonneg H.card) hHcard
    have hac := mul_le_mul hAcard hCcard (Nat.cast_nonneg C.card) (by positivity)
    have he1 : ((t : ℝ) ^ 15 / 100) * ((t : ℝ) ^ 15 / 100) = (t : ℝ) ^ 30 / 10000 := by ring
    have he2 : ((t : ℝ) ^ 12 / 100) * ((t : ℝ) ^ 18 / 100) = (t : ℝ) ^ 30 / 10000 := by ring
    rw [he1] at hs
    rw [he2] at hac
    push_cast
    change (F.card : ℝ) ≤ (t : ℝ) ^ 30 / 5000
    change (F.card : ℝ) ≤ _ at hh
    nlinarith only [hh, hs, hac, pow_nonneg (Nat.cast_nonneg (α := ℝ) t) 30]
  exact linear_of_selected_certificate Q R F (fun p hp => hP p (mem_filter.mp hp).1)
    (fun p hp => hP p (mem_filter.mp hp).1) hQRdis hF r (t ^ 30) P.card hm hk hQcard
    (card_filter_le P _) (by simpa only [hQR] using hcover)
    (fun x hx => (card_le_card (filter_subset_filter _ (filter_subset _ P))).trans (hdouble x hx))
    hFcard hmargin

#print axioms prime_double_cover_thirtieth
end Erdos970.DoubleCover
