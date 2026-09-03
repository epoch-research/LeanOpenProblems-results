import FormalConjecturesUtil

/-! Checked reductions for the largest-prime-factor comparison problem. -/

namespace Erdos371Development

open Filter
open scoped Topology

/-- Consecutive natural numbers have distinct largest prime factors, including zero and one. -/
theorem maxPrimeFac_succ_ne (n : ℕ) :
    Nat.maxPrimeFac (n + 1) ≠ Nat.maxPrimeFac n := by
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · norm_num [Nat.prime_two.maxPrimeFac_eq_self]
  intro h
  have hp : (Nat.maxPrimeFac (n + 2)).Prime :=
    Nat.prime_maxPrimeFac_of_one_lt _ (by omega)
  have hd : Nat.maxPrimeFac (n + 2) ∣ n + 2 + 1 := by
    rw [← h]
    exact Nat.maxPrimeFac_dvd
  have hd' : Nat.maxPrimeFac (n + 2) ∣ (n + 2 + 1) - (n + 2) :=
    Nat.dvd_sub hd Nat.maxPrimeFac_dvd
  exact hp.not_dvd_one (by simpa using hd')

def rises (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)

def falls (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n

theorem fall_iff_not_rise (n : ℕ) :
    Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n ↔
      ¬ Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) := by
  have h := maxPrimeFac_succ_ne n
  omega

/-- Every number below a cutoff belongs to exactly one orientation. -/
theorem rises_card_add_falls_card (N : ℕ) :
    (rises N).card + (falls N).card = N := by
  simpa only [rises, falls, fall_iff_not_rise, Finset.card_range] using
    (Finset.card_filter_add_card_filter_not (s := Finset.range N)
      (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)))

theorem coe_rises (N : ℕ) :
    (rises N : Set ℕ) =
      { n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n } ∩ Set.Iio N := by
  ext n
  simp [rises, and_comm]

theorem partialDensity_eq_rises (N : ℕ) :
    { n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.partialDensity Set.univ N =
      ((rises N).card : ℝ) / N := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  rw [← coe_rises, Set.ncard_coe_finset]

/-- The normalized difference of the two orientation counts. -/
noncomputable def signedMean (N : ℕ) : ℝ :=
  (((rises N).card : ℝ) - (falls N).card) / N

theorem signedMean_eq (N : ℕ) (hN : N ≠ 0) :
    signedMean N = 2 * (((rises N).card : ℝ) / N) - 1 := by
  have hsum : ((rises N).card : ℝ) + (falls N).card = N := by
    exact_mod_cast rises_card_add_falls_card N
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  dsimp [signedMean]
  field_simp
  nlinarith

/-- The conjecture is exactly cancellation of the normalized signed count. -/
theorem hasDensity_iff_signedMean :
    { n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.HasDensity (1 / 2) ↔
      Tendsto signedMean atTop (𝓝 0) := by
  change Tendsto (fun N =>
    { n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.partialDensity Set.univ N)
      atTop (𝓝 (1 / 2)) ↔ _
  simp only [partialDensity_eq_rises]
  have heq : signedMean =ᶠ[atTop]
      (fun N => 2 * (((rises N).card : ℝ) / N) - 1) := by
    exact eventually_atTop.2 ⟨1, fun N hN => signedMean_eq N (by omega)⟩
  constructor
  · intro h
    have ht := (h.const_mul (2 : ℝ)).sub_const 1
    norm_num at ht
    exact ht.congr' heq.symm
  · intro h
    have ht := (h.add_const 1).div_const (2 : ℝ)
    norm_num at ht
    apply ht.congr'
    filter_upwards [heq] with N hN
    rw [hN]
    ring

end Erdos371Development
