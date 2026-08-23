import Submission.Positive
open Nat Finset BigOperators Int Polynomial
open Core

noncomputable abbrev BS (z : ℤ) : PowerSeries ℤ :=
  PowerSeries.binomialSeries ℤ z

noncomputable def U : PowerSeries ℤ := PowerSeries.X * BS (-2)

noncomputable def geomPS (N : ℕ) : PowerSeries ℤ :=
  ∑ t ∈ Finset.range (N+1), U^t

noncomputable def ballotSeries (A N : ℕ) : PowerSeries ℤ :=
  (1-PowerSeries.X) * BS ((A : ℤ)-1) * geomPS N

lemma BS_add (x y : ℤ) : BS (x+y) = BS x * BS y := by
  exact PowerSeries.binomialSeries_add x y

lemma cyclo_mul_BS_neg_two :
    (Core.cyclo3 : PowerSeries ℤ) * BS (-2) = 1-U := by
  have h : BS (-2) * BS 2 = 1 := by
    rw [← BS_add]
    norm_num [BS]
  have h2 : BS 2 = (1+PowerSeries.X)^2 := by
    simpa [BS] using (PowerSeries.binomialSeries_nat (A := ℤ) (R := ℤ) 2)
  rw [h2] at h
  rw [show (Core.cyclo3 : PowerSeries ℤ) =
      (1+PowerSeries.X)^2 - PowerSeries.X by
        simp [Core.cyclo3]; ring]
  dsimp [U]
  linear_combination h

lemma cyclo_mul_ballotSeries (A N : ℕ) :
    (Core.cyclo3 : PowerSeries ℤ) * ballotSeries A N =
      (1-PowerSeries.X^2) * BS (A : ℤ) * (1-U^(N+1)) := by
  have hneg : BS ((A : ℤ)-1) = BS (-2) * BS ((A : ℤ)+1) := by
    rw [← BS_add]
    congr 1
    ring
  have hone : BS 1 = (1+PowerSeries.X) := by
    simpa [BS] using (PowerSeries.binomialSeries_nat (A := ℤ) (R := ℤ) 1)
  have hsucc : BS ((A : ℤ)+1) = BS (A : ℤ) * (1+PowerSeries.X) := by
    calc
      BS ((A : ℤ)+1) = BS (A : ℤ) * BS 1 := BS_add _ _
      _ = _ := by rw [hone]
  have hgeom := geom_sum_mul_neg U (N+1)
  change geomPS N * (1-U) = 1-U^(N+1) at hgeom
  rw [ballotSeries, hneg, hsucc]
  rw [show (Core.cyclo3 : PowerSeries ℤ) *
      ((1-PowerSeries.X) * (BS (-2) * (BS (A : ℤ) * (1+PowerSeries.X))) * geomPS N) =
      (1-PowerSeries.X) * BS (A : ℤ) * (1+PowerSeries.X) *
        (((Core.cyclo3 : PowerSeries ℤ) * BS (-2)) * geomPS N) by ring]
  rw [cyclo_mul_BS_neg_two]
  rw [show (1-U) * geomPS N = 1-U^(N+1) by
    rw [mul_comm]; exact hgeom]
  ring

lemma coeff_cyclo_mul (S : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n ((Core.cyclo3 : PowerSeries ℤ) * S) =
      PowerSeries.coeff n S +
        (if 1 ≤ n then PowerSeries.coeff (n-1) S else 0) +
        (if 2 ≤ n then PowerSeries.coeff (n-2) S else 0) := by
  rw [show (Core.cyclo3 : PowerSeries ℤ) =
      PowerSeries.X^2 + PowerSeries.X + 1 by simp [Core.cyclo3]]
  rw [add_mul, add_mul, map_add, map_add]
  rw [PowerSeries.coeff_X_pow_mul']
  rw [show PowerSeries.X * S = PowerSeries.X^1 * S by simp,
    PowerSeries.coeff_X_pow_mul']
  simp only [one_mul]
  ring

lemma coeff_eq_of_cyclo_mul_eq {S T : PowerSeries ℤ} {N : ℕ}
    (h : ∀ n, n ≤ N →
      PowerSeries.coeff n ((Core.cyclo3 : PowerSeries ℤ)*S) =
        PowerSeries.coeff n ((Core.cyclo3 : PowerSeries ℤ)*T)) :
    ∀ n, n ≤ N → PowerSeries.coeff n S = PowerSeries.coeff n T := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have heq := h n hn
      rw [coeff_cyclo_mul, coeff_cyclo_mul] at heq
      have hi1 : (if 1 ≤ n then PowerSeries.coeff (n-1) S else 0) =
          (if 1 ≤ n then PowerSeries.coeff (n-1) T else 0) := by
        by_cases h1 : 1 ≤ n
        · simp only [if_pos h1]
          exact ih (n-1) (by omega) (by omega)
        · simp only [if_neg h1]
      have hi2 : (if 2 ≤ n then PowerSeries.coeff (n-2) S else 0) =
          (if 2 ≤ n then PowerSeries.coeff (n-2) T else 0) := by
        by_cases h2 : 2 ≤ n
        · simp only [if_pos h2]
          exact ih (n-2) (by omega) (by omega)
        · simp only [if_neg h2]
      rw [hi1, hi2] at heq
      omega

lemma coeff_remainder_zero (A N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n
      ((1-PowerSeries.X^2) * BS (A : ℤ) * U^(N+1)) = 0 := by
  rw [U, mul_pow]
  rw [show (1-PowerSeries.X^2) * BS (A : ℤ) *
      (PowerSeries.X^(N+1) * BS (-2)^(N+1)) =
      PowerSeries.X^(N+1) *
        ((1-PowerSeries.X^2) * BS (A : ℤ) * BS (-2)^(N+1)) by ring]
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

lemma ballotSeries_coeff_eq_target (A N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (ballotSeries A N) =
      PowerSeries.coeff n (Core.Qseries * BS (A : ℤ)) := by
  apply coeff_eq_of_cyclo_mul_eq
  intro d hd
  rw [cyclo_mul_ballotSeries]
  have htarget : (Core.cyclo3 : PowerSeries ℤ) *
      (Core.Qseries * BS (A : ℤ)) =
      (1-PowerSeries.X^2) * BS (A : ℤ) := by
    rw [show (Core.cyclo3 : PowerSeries ℤ) *
        (Core.Qseries * BS (A : ℤ)) =
        ((Core.cyclo3 : PowerSeries ℤ) * Core.Qseries) * BS (A : ℤ) by ring,
      Core.cyclo3_mul_Qseries]
  rw [htarget]
  rw [mul_sub, mul_one, map_sub]
  rw [coeff_remainder_zero A N d hd, sub_zero]
  exact hn

lemma BS_neg_two_pow (t : ℕ) : BS (-2)^t = BS (-(2*(t : ℤ))) := by
  induction t with
  | zero => simp [BS]
  | succ t ih =>
      rw [pow_succ, ih, ← BS_add]
      congr 1
      push_cast
      ring

noncomputable def formalCatalanCoeff (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1 else
    Ring.choose (r + 2*(k : ℤ)-1) k -
      Ring.choose (r + 2*(k : ℤ)-1) (k-1)

noncomputable def formalPartial (r : ℤ) (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (N+1), formalCatalanCoeff r k

lemma coeff_one_sub_X_mul_BS (z : ℤ) (k : ℕ) :
    PowerSeries.coeff k ((1-PowerSeries.X)*BS z) =
      if k=0 then 1 else Ring.choose z k - Ring.choose z (k-1) := by
  rw [sub_mul, one_mul, map_sub]
  rw [show PowerSeries.X * BS z = PowerSeries.X^1 * BS z by simp,
    PowerSeries.coeff_X_pow_mul']
  rw [PowerSeries.binomialSeries_coeff]
  by_cases hk : k=0
  · subst k
    simp [Ring.choose_zero_right]
  · rw [if_neg hk, if_pos (show 1 ≤ k by omega)]
    simp

lemma coeff_ballotSeries_eq_formalPartial (A N : ℕ) :
    PowerSeries.coeff N (ballotSeries A N) =
      formalPartial ((A : ℤ)-2*(N : ℤ)) N := by
  rw [ballotSeries, geomPS, Finset.mul_sum, map_sum]
  rw [← Finset.sum_flip]
  unfold formalPartial
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
  let t := N-k
  have htN : t ≤ N := Nat.sub_le _ _
  change PowerSeries.coeff N
      ((1-PowerSeries.X) * BS ((A : ℤ)-1) * U^t) =
    formalCatalanCoeff ((A : ℤ)-2*(N : ℤ)) k
  rw [U, mul_pow, BS_neg_two_pow]
  rw [show (1-PowerSeries.X) * BS ((A : ℤ)-1) *
      (PowerSeries.X^t * BS (-(2*(t : ℤ)))) =
      PowerSeries.X^t * ((1-PowerSeries.X) *
        (BS ((A : ℤ)-1) * BS (-(2*(t : ℤ))))) by ring]
  rw [← BS_add]
  rw [PowerSeries.coeff_X_pow_mul', if_pos htN]
  rw [coeff_one_sub_X_mul_BS]
  unfold formalCatalanCoeff
  have hNk : N-t=k := by dsimp [t]; omega
  rw [hNk]
  have hz : (A : ℤ)-1 + -(2*(t : ℤ)) =
      ((A : ℤ)-2*(N : ℤ)) + 2*(k : ℤ)-1 := by
    dsimp [t]
    rw [Nat.cast_sub hkN]
    ring
  rw [hz]

lemma formalPartial_eq_FNat (A N : ℕ) :
    formalPartial ((A : ℤ)-2*(N : ℤ)) N = FNat A N := by
  rw [← coeff_ballotSeries_eq_formalPartial]
  rw [ballotSeries_coeff_eq_target A N N le_rfl]
  unfold FNat
  have hnat : BS (A : ℤ) = (1+PowerSeries.X)^A := by
    simpa [BS] using (PowerSeries.binomialSeries_nat (A := ℤ) (R := ℤ) A)
  rw [hnat]
  simp

