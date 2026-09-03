import Submission.HigherDivisorSubpower
import Submission.CompositeCharacterErrors

/-!
# A lower bound for full-range absolute progression errors

Large odd moduli have at most one nontrivial candidate in the residue-one
class, and that candidate is even. They force a substantial absolute error
when all moduli up to the input scale are included. This does not address
signed errors or cutoffs of the form X^theta with theta<1, and is not a
disproof of Erdős 821.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta

namespace Erdos821.FullRangeError

open AnalyticSieve HigherDivisors

lemma residueOneMangoldt_large_modulus (d X : ℕ) (hd : 0 < d)
    (hdX : d < X) (hXd : X ≤ 2*d) :
    residueOneMangoldt d X = vonMangoldt (d+1) := by
  unfold residueOneMangoldt
  rw [Finset.sum_eq_single (d+1)]
  · rw [(residue_one_iff_dvd_pred (by omega : 1 ≤ d+1)).mpr (by simp)]
    simp
  · intro n hn hne
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnX := (Finset.mem_Icc.mp hn).2
    by_cases hn' : n = 1
    · subst n
      simp [vonMangoldt_apply_one]
    have hnd : ¬d ∣ n-1 := by
      rintro ⟨j, hj⟩
      have hj0 : 1 ≤ j := by
        by_contra h
        have : j = 0 := by omega
        simp [this] at hj
        omega
      have hj2 : j < 2 := by
        by_contra h
        have hm := Nat.mul_le_mul_left d (show 2 ≤ j by omega)
        have hpred : n-1 < n := by omega
        nlinarith
      have : j = 1 := by omega
      simp [this] at hj
      omega
    rw [if_neg (fun h => hnd ((residue_one_iff_dvd_pred hn1).mp h))]
  · intro h
    exact (h (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).elim

lemma large_odd_progression_sum_le (P : Finset ℕ) (X : ℕ)
    (hP : ∀ d ∈ P, 0 < d ∧ d < X ∧ X ≤ 2*d ∧ ¬(d+1).Coprime 2) :
    (∑ d ∈ P, residueOneMangoldt d X) ≤ characterLiftError 2 X := by
  let f : ℕ → ℝ := fun n => if ¬n.Coprime 2 then vonMangoldt n else 0
  have he : (∑ d ∈ P, residueOneMangoldt d X) =
      ∑ n ∈ P.image (fun d => d+1), f n := by
    rw [Finset.sum_image (by intro a ha b hb h; exact Nat.add_right_cancel h)]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd0, hdX, hXd, hnc⟩ := hP d hd
    rw [residueOneMangoldt_large_modulus d X hd0 hdX hXd]
    change _ = if ¬(d+1).Coprime 2 then vonMangoldt (d+1) else 0
    rw [if_pos hnc]
  have hsub : P.image (fun d => d+1) ⊆ Finset.Icc 1 X := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by have := (hP d hd).2.1; omega⟩
  rw [he]
  apply le_trans _ (nonunitMangoldt_le_liftError 2 X (by decide))
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n hn hnP => by dsimp [f]; split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl)

lemma error_one_eq (Q X : ℕ) :
    divisorProgressionError 1 Q X = ∑ d ∈ Finset.Icc 1 Q,
      |residueOneMangoldt d X - mangoldtSum X/(d.totient : ℝ)| := by
  unfold divisorProgressionError
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
  simp [tau, zeta_apply_ne hd0]

lemma main_minus_actual_le_error (P : Finset ℕ) (X : ℕ) (hX : 0 < X)
    (hP : P ⊆ Finset.Icc 1 X) :
    mangoldtSum X * (P.card : ℝ)/(X : ℝ) -
      (∑ d ∈ P, residueOneMangoldt d X) ≤ divisorProgressionError 1 X X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hmain : mangoldtSum X * (P.card : ℝ)/(X : ℝ) ≤
      ∑ d ∈ P, mangoldtSum X/(d.totient : ℝ) := by
    calc
      _ = ∑ _d ∈ P, mangoldtSum X/(X : ℝ) := by simp [mul_div_assoc, mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp (hP hd)
        have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd1
        have hφX : (d.totient : ℝ) ≤ X := by exact_mod_cast (Nat.totient_le d).trans hdX
        exact div_le_div_of_nonneg_left (mangoldtSum_nonneg X) hφ hφX
  have herror : (∑ d ∈ P, mangoldtSum X/(d.totient : ℝ)) -
      (∑ d ∈ P, residueOneMangoldt d X) ≤ divisorProgressionError 1 X X := by
    rw [← Finset.sum_sub_distrib, error_one_eq]
    apply le_trans (Finset.sum_le_sum (fun d _ =>
      (by simpa only [neg_sub] using
        neg_le_abs (residueOneMangoldt d X - mangoldtSum X/(d.totient : ℝ)))))
    exact Finset.sum_le_sum_of_subset_of_nonneg hP (fun d hd hdP => abs_nonneg _)
  linarith

def oddLargeModuli (N : ℕ) : Finset ℕ :=
  (Finset.range N).image (fun j => 2*N+2*j+1)

lemma oddLargeModuli_card (N : ℕ) : (oddLargeModuli N).card = N := by
  have hi : Function.Injective (fun j : ℕ => 2*N+2*j+1) := by
    intro a b h
    change 2*N+2*a+1 = 2*N+2*b+1 at h
    omega
  unfold oddLargeModuli
  exact (Finset.card_image_of_injOn (fun a ha b hb h => hi h)).trans (Finset.card_range N)

lemma oddLargeModuli_properties (N : ℕ) :
    ∀ d ∈ oddLargeModuli N,
      0 < d ∧ d < 4*N ∧ 4*N ≤ 2*d ∧ ¬(d+1).Coprime 2 := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
  have hjN := Finset.mem_range.mp hj
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro h
  apply (Nat.prime_two.coprime_iff_not_dvd.mp h.symm)
  exact ⟨N+j+1, by ring⟩

/-- Full-range absolute discrepancy has an unavoidable contribution from
large odd moduli. The prime-power contamination is explicitly retained. -/
theorem full_error_lower (N : ℕ) (hN : 0 < N) :
    mangoldtSum (4*N)/4 - characterLiftError 2 (4*N) ≤
      divisorProgressionError 1 (4*N) (4*N) := by
  have hP := oddLargeModuli_properties N
  have he := main_minus_actual_le_error (oddLargeModuli N) (4*N) (by omega)
    (fun d hd => Finset.mem_Icc.mpr ⟨(hP d hd).1, (hP d hd).2.1.le⟩)
  have ha := large_odd_progression_sum_le (oddLargeModuli N) (4*N) hP
  rw [oddLargeModuli_card] at he
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : mangoldtSum (4*N) * (N : ℝ)/((4*N : ℕ) : ℝ) = mangoldtSum (4*N)/4 := by
    push_cast
    field_simp
  rw [hid] at he
  linarith

lemma error_one_le_higher (k Q X : ℕ) (hk : 1 ≤ k) :
    divisorProgressionError 1 Q X ≤ divisorProgressionError k Q X := by
  rw [error_one_eq]
  apply Finset.sum_le_sum
  intro d hd
  have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have ht : (1 : ℝ) ≤ tau (j+1) d := by exact_mod_cast tau_succ_pos j d hd0
  exact le_mul_of_one_le_left (abs_nonneg _) ht

lemma full_error_dyadic_lower (L : ℕ) :
    mangoldtSum (2^(L+2))/4 - ((L : ℝ)+2)*Real.log 2 ≤
      divisorProgressionError 1 (2^(L+2)) (2^(L+2)) := by
  have h := full_error_lower (2^L) (by positivity)
  have he : 4*2^L = 2^(L+2) := by rw [pow_add]; ring
  rw [he] at h
  simpa only [characterLiftError, Nat.log_pow (by decide : 1 < 2),
    Nat.cast_add, Nat.cast_ofNat] using h

/-- The lower bound is uniform in the positive divisor order. -/
theorem eventually_full_error_ge_psi :
    ∀ᶠ L : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
      mangoldtSum (2^(L+2))/8 ≤ divisorProgressionError k (2^(L+2)) (2^(L+2)) := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 32 2] with L hpoly k hk
  have hpolyR : (32 : ℝ)*((L : ℝ)+1)^2 ≤ (2 : ℝ)^L := by
    exact_mod_cast (by simpa only [one_mul] using hpoly)
  have hψ := dyadic_mangoldt_lower (L+2) (by omega)
  have hcast : ((2^(L+2) : ℕ) : ℝ) = 4*(2 : ℝ)^L := by
    push_cast
    rw [pow_add]
    ring
  rw [hcast] at hψ
  push_cast at hψ
  have hL0 : (0 : ℝ) < 4*((L : ℝ)+2) := by positivity
  have hsq : ((L : ℝ)+2)^2 ≤ 4*((L : ℝ)+1)^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hbig : 8*((L : ℝ)+2) ≤ mangoldtSum (2^(L+2)) := by
    apply (mul_le_mul_iff_left₀ hL0).mp
    nlinarith only [hpolyR, hψ, hsq]
  have hlog : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ)-1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hsmall : ((L : ℝ)+2)*Real.log 2 ≤ mangoldtSum (2^(L+2))/8 := by
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (L : ℝ)+2 by positivity)
    linarith
  have he := full_error_dyadic_lower L
  have hhigh := error_one_le_higher k (2^(L+2)) (2^(L+2)) hk
  linarith

/-- An explicit X/log(X)-scale obstruction, using only the elementary
Chebyshev lower bound already available in this development. -/
theorem eventually_full_error_ge_dyadic_scale :
    ∀ᶠ L : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
      ((2^(L+2) : ℕ) : ℝ)/(32*((L : ℝ)+2)) ≤
        divisorProgressionError k (2^(L+2)) (2^(L+2)) := by
  filter_upwards [eventually_full_error_ge_psi] with L hL k hk
  have hψ := dyadic_mangoldt_lower (L+2) (by omega)
  have hden : (0 : ℝ) < 32*((L : ℝ)+2) := by positivity
  have hmain : ((2^(L+2) : ℕ) : ℝ)/(32*((L : ℝ)+2)) ≤
      mangoldtSum (2^(L+2))/8 := by
    apply (div_le_iff₀ hden).mpr
    push_cast at hψ ⊢
    nlinarith only [hψ]
  exact hmain.trans (hL k hk)

/-- In particular, a full-range absolute error with every logarithmic
saving cannot hold. This does not rule out signed errors or shorter ranges. -/
theorem eventually_full_error_gt_log_square :
    ∀ᶠ L : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
      ((2^(L+2) : ℕ) : ℝ)/((L : ℝ)+1)^2 <
        divisorProgressionError k (2^(L+2)) (2^(L+2)) := by
  filter_upwards [eventually_full_error_ge_dyadic_scale, eventually_ge_atTop 64]
    with L hL h64 k hk
  have h64R : (64 : ℝ) ≤ L := by exact_mod_cast h64
  have hden : 32*((L : ℝ)+2) < ((L : ℝ)+1)^2 := by nlinarith
  have hlt := div_lt_div_of_pos_left
    (by positivity : (0 : ℝ) < (2^(L+2) : ℕ))
    (by positivity : (0 : ℝ) < 32*((L : ℝ)+2)) hden
  exact hlt.trans_le (hL k hk)

/-- On the established progression scales the stronger Chebyshev bound
makes the obstruction linear in X, uniformly in every positive divisor order. -/
theorem eventually_full_error_ge_linear :
    ∀ᶠ s : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
      (progressionScaleN s : ℝ)/64 ≤
        divisorProgressionError k (progressionScaleN s) (progressionScaleN s) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp eventually_full_error_ge_psi
  filter_upwards [eventually_ge_atTop (M+1)] with s hs k hk
  have hs1 : 1 ≤ s := by omega
  have he : 64*s-2+2 = 64*s := by omega
  have herr := hM (64*s-2) (by omega) k hk
  rw [he] at herr
  change mangoldtSum (progressionScaleN s)/8 ≤
    divisorProgressionError k (progressionScaleN s) (progressionScaleN s) at herr
  have hψ := progression_scale_mangoldt_lower hs1
  linarith

end Erdos821.FullRangeError
