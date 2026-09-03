import Submission.SieveMassLower
import Submission.DivisorPairCount

/-! A two-coordinate Selberg upper sieve for genuine prime pairs. -/
namespace Erdos972PairSieve

open Finset Erdos972SelbergWeights Erdos972SieveMassLower Erdos972DivisorPairCount

noncomputable def majorant (R n : ℕ) : ℝ :=
  (∑ d ∈ Ioc 0 R, if d ∣ n then selbergWeight R d else 0)^2

lemma majorant_nonneg (R n : ℕ) : 0 ≤ majorant R n := sq_nonneg _

lemma majorant_eq_one_of_prime {R p : ℕ} (hR : 1 ≤ R) (hp : p.Prime) (hRp : R < p) :
    majorant R p = 1 := by
  have hs : (∑ d ∈ Ioc 0 R, if d ∣ p then selbergWeight R d else 0) = 1 := by
    rw [sum_eq_single 1]
    · simp only [one_dvd, if_true, selbergWeight_one hR]
    · intro d hd hd1
      apply if_neg
      intro hdp
      have he := (Nat.dvd_prime hp).mp hdp
      rcases he with h | h
      · exact hd1 h
      · have := (mem_Ioc.mp hd).2
        omega
    · intro h
      exact (h (mem_Ioc.mpr ⟨by omega, hR⟩)).elim
  simp only [majorant, hs, one_pow]

def weightIndices (R : ℕ) : Finset (ℕ × ℕ) := Ioc 0 R ×ˢ Ioc 0 R

def weightDivisor (z : ℕ × ℕ) : ℕ := z.1.lcm z.2

noncomputable def weightCoeff (R : ℕ) (z : ℕ × ℕ) : ℝ :=
  selbergWeight R z.1 * selbergWeight R z.2

lemma majorant_expansion (R n : ℕ) :
    majorant R n = ∑ z ∈ weightIndices R,
      if weightDivisor z ∣ n then weightCoeff R z else 0 := by
  classical
  simp only [majorant, pow_two, sum_mul_sum, weightIndices, sum_product]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  dsimp [weightDivisor, weightCoeff]
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [Nat.lcm_dvd_iff, hd, he]

noncomputable def pairMoment (α : ℝ) (N R : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, majorant R n * majorant R ⌊α * n⌋₊

lemma pairMoment_expansion (α : ℝ) (N R : ℕ) :
    pairMoment α N R = ∑ z ∈ weightIndices R, ∑ w ∈ weightIndices R,
      weightCoeff R z * weightCoeff R w *
        (divisorPairs α N (weightDivisor z) (weightDivisor w)).card := by
  classical
  have hterm (n : ℕ) : majorant R n * majorant R ⌊α * n⌋₊ =
      ∑ z ∈ weightIndices R, ∑ w ∈ weightIndices R,
        if weightDivisor z ∣ n ∧ weightDivisor w ∣ ⌊α * n⌋₊ then
          weightCoeff R z * weightCoeff R w else 0 := by
    rw [majorant_expansion, majorant_expansion, sum_mul_sum]
    apply sum_congr rfl
    intro z _
    apply sum_congr rfl
    intro w _
    split_ifs <;> simp_all
  unfold pairMoment
  simp_rw [hterm]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  rw [← sum_filter]
  simp only [divisorPairs, sum_const, nsmul_eq_mul]
  ring

lemma weightDivisor_bounds {R : ℕ} {z : ℕ × ℕ} (hz : z ∈ weightIndices R) :
    0 < weightDivisor z ∧ weightDivisor z ≤ R^2 := by
  obtain ⟨hz₁, hz₂⟩ := mem_product.mp hz
  obtain ⟨hd0, hdR⟩ := mem_Ioc.mp hz₁
  obtain ⟨he0, heR⟩ := mem_Ioc.mp hz₂
  refine ⟨Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd0.ne' he0.ne'), ?_⟩
  exact (Nat.lcm_le_mul hd0 he0).trans (by nlinarith)

lemma weightCoeff_main (R : ℕ) :
    (∑ z ∈ weightIndices R, weightCoeff R z / weightDivisor z) =
      quadraticMain R (selbergWeight R) := by
  simp only [weightIndices, sum_product, weightCoeff, weightDivisor, quadraticMain]

lemma weightCoeff_abs_sum {R : ℕ} (hR : 1 ≤ R) :
    (∑ z ∈ weightIndices R, |weightCoeff R z|) ≤ (R : ℝ)^4 := by
  have hs : (∑ d ∈ Ioc 0 R, |selbergWeight R d|) ≤ (R : ℝ)^2 := by
    calc
      _ ≤ ∑ d ∈ Ioc 0 R, (R : ℝ) := by
        apply sum_le_sum
        intro d hd
        exact (abs_selbergWeight_le hR d).trans (Nat.cast_le.mpr (mem_Ioc.mp hd).2)
      _ = (R : ℝ)^2 := by simp [pow_two]
  have heq : (∑ z ∈ weightIndices R, |weightCoeff R z|) =
      (∑ d ∈ Ioc 0 R, |selbergWeight R d|)^2 := by
    simp only [weightIndices, sum_product, weightCoeff, abs_mul, pow_two, sum_mul_sum]
  rw [heq]
  have hn : 0 ≤ ∑ d ∈ Ioc 0 R, |selbergWeight R d| := sum_nonneg (fun _ _ => abs_nonneg _)
  nlinarith [sq_nonneg ((R : ℝ)^2 - ∑ d ∈ Ioc 0 R, |selbergWeight R d|)]

lemma mul_le_main_add_error {c x m E : ℝ} (h : |x - m| ≤ E) :
    c * x ≤ c * m + |c| * E := by
  have hh := (le_abs_self (c * (x - m))).trans
    (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left h (abs_nonneg c))
  nlinarith

/-- The two-coordinate Selberg moment, with an arbitrary uniform local error. -/
theorem pairMoment_upper {α : ℝ} {N R : ℕ} (hR : 1 ≤ R) {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ d e : ℕ, 0 < d → d ≤ R^2 → 0 < e → e ≤ R^2 →
      |((divisorPairs α N d e).card : ℝ) - (N : ℝ) / (d * e)| ≤ B) :
    pairMoment α N R ≤ (N : ℝ) / (sieveMass R)^2 + B * (R : ℝ)^8 := by
  rw [pairMoment_expansion]
  have hterm (z : ℕ × ℕ) (hz : z ∈ weightIndices R)
      (w : ℕ × ℕ) (hw : w ∈ weightIndices R) :
      weightCoeff R z * weightCoeff R w *
          (divisorPairs α N (weightDivisor z) (weightDivisor w)).card ≤
        (N : ℝ) * (weightCoeff R z / weightDivisor z) * (weightCoeff R w / weightDivisor w) +
          B * |weightCoeff R z| * |weightCoeff R w| := by
    obtain ⟨hd, hdR⟩ := weightDivisor_bounds hz
    obtain ⟨he, heR⟩ := weightDivisor_bounds hw
    have h := mul_le_main_add_error (c := weightCoeff R z * weightCoeff R w)
      (hlocal _ _ hd hdR he heR)
    convert h using 1
    rw [abs_mul]
    ring
  have hb := sum_le_sum (fun z hz => sum_le_sum (fun w hw => hterm z hz w hw))
  have heq : (∑ z ∈ weightIndices R, ∑ w ∈ weightIndices R,
      ((N : ℝ) * (weightCoeff R z / weightDivisor z) * (weightCoeff R w / weightDivisor w) +
        B * |weightCoeff R z| * |weightCoeff R w|)) =
      (N : ℝ) * (∑ z ∈ weightIndices R, weightCoeff R z / weightDivisor z)^2 +
        B * (∑ z ∈ weightIndices R, |weightCoeff R z|)^2 := by
    simp_rw [sum_add_distrib, ← mul_sum, ← sum_mul, ← mul_sum]
    ring
  rw [heq, weightCoeff_main, quadraticMain_selbergWeight hR] at hb
  apply hb.trans
  have hC := weightCoeff_abs_sum hR
  have hC0 : 0 ≤ ∑ z ∈ weightIndices R, |weightCoeff R z| :=
    sum_nonneg (fun _ _ => abs_nonneg _)
  have hs : (∑ z ∈ weightIndices R, |weightCoeff R z|)^2 ≤ (R : ℝ)^8 := by
    nlinarith [sq_nonneg ((R : ℝ)^4 - ∑ z ∈ weightIndices R, |weightCoeff R z|)]
  have he : (N : ℝ) * (1 / sieveMass R)^2 = (N : ℝ) / (sieveMass R)^2 := by ring
  rw [he]
  linarith [mul_le_mul_of_nonneg_left hs hB]

noncomputable def primeInputs (α : ℝ) (N : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n => n.Prime ∧ (⌊α * n⌋₊).Prime

lemma primeInputs_card_le_moment {α : ℝ} (hα : 1 ≤ α) (N R : ℕ) (hR : 1 ≤ R) :
    ((primeInputs α N).card : ℝ) ≤ R + pairMoment α N R := by
  classical
  let A := (primeInputs α N).filter fun n => n ≤ R
  let C := (primeInputs α N).filter fun n => ¬ n ≤ R
  have hpart : A.card + C.card = (primeInputs α N).card := card_filter_add_card_filter_not _
  have hA : A.card ≤ R := by
    have hsub : A ⊆ Ioc 0 R := by
      intro n hn
      obtain ⟨hnP, hnR⟩ := mem_filter.mp hn
      have hn0 := (mem_Ioc.mp (mem_filter.mp hnP).1).1
      exact mem_Ioc.mpr ⟨hn0, hnR⟩
    simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card hsub
  have hC : (C.card : ℝ) ≤ pairMoment α N R := by
    have hsub : C ⊆ Ioc 0 N := fun _ hn => (mem_filter.mp (mem_filter.mp hn).1).1
    have hterm (n : ℕ) (hn : n ∈ C) : majorant R n * majorant R ⌊α * n⌋₊ = 1 := by
      obtain ⟨hnP, hnR⟩ := mem_filter.mp hn
      obtain ⟨_, hp, hq⟩ := mem_filter.mp hnP
      have hnR' : R < n := Nat.lt_of_not_ge hnR
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hnle : n ≤ ⌊α * n⌋₊ := Nat.le_floor (by nlinarith)
      rw [majorant_eq_one_of_prime hR hp hnR',
        majorant_eq_one_of_prime hR hq (hnR'.trans_le hnle), mul_one]
    calc
      (C.card : ℝ) = ∑ n ∈ C, majorant R n * majorant R ⌊α * n⌋₊ := by
        calc
          (C.card : ℝ) = ∑ n ∈ C, (1 : ℝ) := by simp
          _ = _ := sum_congr rfl (fun n hn => (hterm n hn).symm)
      _ ≤ pairMoment α N R := sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => mul_nonneg (majorant_nonneg R n) (majorant_nonneg R ⌊α * n⌋₊))
  have hAR : (A.card : ℝ) ≤ R := Nat.cast_le.mpr hA
  have hpartR : (A.card : ℝ) + C.card = (primeInputs α N).card := by exact_mod_cast hpart
  linarith

/-- A genuine prime-pair upper bound with the expected logarithmic main-term
scale once `R` is a fixed power of the input cutoff. It is not a lower bound. -/
theorem primeInputs_upper {α : ℝ} (hα : 1 ≤ α) (N R : ℕ) (hR : 1 ≤ R)
    {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ d e : ℕ, 0 < d → d ≤ R^2 → 0 < e → e ≤ R^2 →
      |((divisorPairs α N d e).card : ℝ) - (N : ℝ) / (d * e)| ≤ B) :
    ((primeInputs α N).card : ℝ) ≤ R + (N : ℝ) / (sieveMass R)^2 + B * (R : ℝ)^8 := by
  have h := pairMoment_upper hR hB hlocal
  have hc := primeInputs_card_le_moment hα N R hR
  linarith

lemma sieve_main_le_log {R : ℕ} (hR : 1 ≤ R) (N : ℕ) :
    (N : ℝ) / (sieveMass R)^2 ≤ 4 * N / (Real.log (R + 1))^2 := by
  have hR0 : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hL : 0 < Real.log (R + 1) := Real.log_pos (by linarith)
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  have hLG := log_le_two_sieveMass R
  have hsq : (Real.log (R + 1))^2 ≤ 4 * (sieveMass R)^2 := by nlinarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hG) (sq_pos_of_pos hL)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) N)]

/-- Explicit upper bound on every prime pair at a common rational-approximation
scale. The error is uniform across all the divisors used in the sieve. -/
theorem primeInputs_common_scale {α : ℝ} (hα : 1 ≤ α) (r : ℚ) (hr : 0 ≤ r)
    (u R : ℕ) (hR : 1 ≤ R) (hRN : R^2 ≤ r.den * u)
    (hu2 : 2 * u ≤ r.den) (husq : u^2 ≤ r.den)
    (happrox : |α - r| * (r.den : ℝ)^2 ≤ 1) :
    ((primeInputs α (r.den * u)).card : ℝ) ≤
      R + 4 * (r.den * u : ℝ) / (Real.log (R + 1))^2 + 15 * (R : ℝ)^10 * r.den := by
  have hR0 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hlocal : ∀ d e : ℕ, 0 < d → d ≤ R^2 → 0 < e → e ≤ R^2 →
      |((divisorPairs α (r.den * u) d e).card : ℝ) - (r.den * u : ℕ) / (d * e : ℝ)| ≤
        15 * (R : ℝ)^2 * r.den := by
    intro d e hd hdR he heR
    have hc := divisorPairs_common_scale (show 0 ≤ α by linarith) r hr u d e hd
      (hdR.trans hRN) he hu2 husq happrox
    push_cast at hc ⊢
    apply hc.trans
    have heR' : (e : ℝ) ≤ (R : ℝ)^2 := by exact_mod_cast heR
    have hcoef : (3 * e + 12 : ℝ) ≤ 15 * (R : ℝ)^2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg r.den)
  have hc := primeInputs_upper hα (r.den * u) R hR (by positivity) hlocal
  have hm := sieve_main_le_log hR (r.den * u)
  push_cast at hc hm
  nlinarith

/-- A general-cutoff version, useful for averaging over slopes. -/
theorem primeInputs_rational_upper {α : ℝ} (hα : 1 ≤ α) (r : ℚ) (hr : 0 ≤ r)
    (N R : ℕ) (hR : 1 ≤ R) (hRN : R^2 ≤ N)
    (hsmall : 2 * N * |α - r| ≤ 1) :
    ((primeInputs α N).card : ℝ) ≤
      R + 4 * N / (Real.log (R + 1))^2 +
        (8 * (N : ℝ)^2 * |α - r| + 2 * N / (r.den : ℝ) + 3 * (R : ℝ)^2 * r.den + 2) * (R : ℝ)^8 := by
  let B : ℝ := 8 * (N : ℝ)^2 * |α - r| + 2 * N / (r.den : ℝ) + 3 * (R : ℝ)^2 * r.den + 2
  have hlocal : ∀ d e : ℕ, 0 < d → d ≤ R^2 → 0 < e → e ≤ R^2 →
      |((divisorPairs α N d e).card : ℝ) - (N : ℝ) / (d * e)| ≤ B := by
    intro d e hd hdR he heR
    have hc := divisorPairs_discrepancy (show 0 ≤ α by linarith) r hr N d e hd (hdR.trans hRN) he hsmall
    apply hc.trans
    have hh : (e : ℝ) ≤ (R : ℝ)^2 := by exact_mod_cast heR
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) r.den)]
  have hc := primeInputs_upper hα N R hR (show 0 ≤ B by dsimp [B]; positivity) hlocal
  have hm := sieve_main_le_log hR N
  dsimp [B] at hc
  linarith

#print axioms pairMoment_upper
#print axioms primeInputs_common_scale
#print axioms primeInputs_rational_upper

end Erdos972PairSieve
