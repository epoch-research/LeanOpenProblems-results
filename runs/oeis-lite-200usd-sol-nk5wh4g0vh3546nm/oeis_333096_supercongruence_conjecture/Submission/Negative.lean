import Submission.Actual
open Nat Finset BigOperators Int Polynomial
open Core

noncomputable def V : PowerSeries ℤ :=
  -(PowerSeries.X * (1+PowerSeries.X))

noncomputable def geomV (N : ℕ) : PowerSeries ℤ :=
  ∑ t ∈ Finset.range (N+1), V^t

noncomputable def negSeries (A N : ℕ) : PowerSeries ℤ :=
  (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) * geomV N

lemma cyclo_eq_one_sub_V :
    (Core.cyclo3 : PowerSeries ℤ) = 1-V := by
  rw [V]
  simp [Core.cyclo3]
  ring

lemma cyclo_mul_negSeries (A N : ℕ) :
    (Core.cyclo3 : PowerSeries ℤ) * negSeries A N =
      (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) * (1-V^(N+1)) := by
  have hg := geom_sum_mul_neg V (N+1)
  change geomV N * (1-V) = 1-V^(N+1) at hg
  rw [negSeries]
  rw [show (Core.cyclo3 : PowerSeries ℤ) *
      ((1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) * geomV N) =
    (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) *
      (geomV N * (Core.cyclo3 : PowerSeries ℤ)) by ring]
  rw [cyclo_eq_one_sub_V, hg]

lemma coeff_neg_remainder_zero (A N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n
      ((1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) * V^(N+1)) = 0 := by
  rw [V, neg_pow, mul_pow]
  rw [show (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) *
      ((-1 : PowerSeries ℤ)^(N+1) *
        (PowerSeries.X^(N+1) * (1+PowerSeries.X)^(N+1))) =
      PowerSeries.X^(N+1) *
        ((-1 : PowerSeries ℤ)^(N+1) * (1+2*PowerSeries.X) *
          (1+PowerSeries.X)^(A-1) * (1+PowerSeries.X)^(N+1)) by ring]
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

lemma cyclo_mul_neg_target (A : ℕ) (hA : 0 < A) :
    (Core.cyclo3 : PowerSeries ℤ) *
      (Core.Qseries * (1+PowerSeries.X)^A +
        PowerSeries.X * (1+PowerSeries.X)^(A-1)) =
      (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) := by
  have hpow : (1+PowerSeries.X : PowerSeries ℤ)^A =
      (1+PowerSeries.X : PowerSeries ℤ)^(A-1) *
        (1+PowerSeries.X : PowerSeries ℤ) := by
    conv_lhs => rw [show A=(A-1)+1 by omega, pow_succ]
  have hDQ := Core.cyclo3_mul_Qseries
  change (Core.cyclo3 : PowerSeries ℤ) * Core.Qseries =
    1-PowerSeries.X^2 at hDQ
  have hD : (Core.cyclo3 : PowerSeries ℤ) =
      PowerSeries.X^2+PowerSeries.X+1 := by simp [Core.cyclo3]
  calc
    (Core.cyclo3 : PowerSeries ℤ) *
        (Core.Qseries * (1+PowerSeries.X)^A +
          PowerSeries.X * (1+PowerSeries.X)^(A-1)) =
      ((Core.cyclo3 : PowerSeries ℤ) * Core.Qseries) *
          (1+PowerSeries.X)^A +
        (Core.cyclo3 : PowerSeries ℤ) * PowerSeries.X *
          (1+PowerSeries.X)^(A-1) := by ring
    _ = (1-PowerSeries.X^2) *
          ((1+PowerSeries.X)^(A-1) * (1+PowerSeries.X)) +
        (PowerSeries.X^2+PowerSeries.X+1) * PowerSeries.X *
          (1+PowerSeries.X)^(A-1) := by rw [hDQ, hpow, hD]
    _ = _ := by ring

lemma negSeries_coeff_eq_target (A N : ℕ) (hA : 0 < A) :
    PowerSeries.coeff N (negSeries A N) =
      PowerSeries.coeff N
        (Core.Qseries * (1+PowerSeries.X)^A +
          PowerSeries.X * (1+PowerSeries.X)^(A-1)) := by
  apply coeff_eq_of_cyclo_mul_eq
  intro d hd
  rw [cyclo_mul_negSeries, cyclo_mul_neg_target A hA]
  rw [mul_sub, mul_one, map_sub]
  rw [coeff_neg_remainder_zero A N d hd, sub_zero]
  exact le_rfl


noncomputable def negDiagTerm (R k : ℕ) : ℤ :=
  if k=0 then 1 else
    (-1 : ℤ)^k * ((R-k).choose k : ℤ) +
      (-1 : ℤ)^k * ((R-k-1).choose (k-1) : ℤ)

lemma formalCoeff_neg_eq (R k : ℕ) (h2k : 2*k ≤ R) :
    formalCatalanCoeff (-(R : ℤ)) k = negDiagTerm R k := by
  by_cases hk0 : k=0
  · subst k
    simp [formalCatalanCoeff, negDiagTerm]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [formalCatalanCoeff, if_neg hk0, negDiagTerm, if_neg hk0]
    let a := R-2*k+1
    have ha : 0 < a := by dsimp [a]; omega
    have hu : -(R : ℤ)+2*(k : ℤ)-1 = -(a : ℤ) := by
      dsimp [a]
      rw [Nat.cast_sub h2k]
      push_cast
      ring
    rw [hu, Ring.choose_neg, Ring.choose_neg]
    have hfirst : (a : ℤ)+(k : ℤ)-1 = ((R-k : ℕ) : ℤ) := by
      dsimp [a]
      rw [Nat.cast_sub h2k, Nat.cast_sub (by omega : k ≤ R)]
      push_cast
      ring
    have hsecond : (a : ℤ)+(k-1 : ℕ)-1 = ((R-k-1 : ℕ) : ℤ) := by
      dsimp [a]
      rw [Nat.cast_sub h2k, Nat.cast_sub (by omega : 1 ≤ k),
        Nat.cast_sub (by omega : 1 ≤ R-k), Nat.cast_sub (by omega : k ≤ R)]
      push_cast
      ring
    rw [hfirst, hsecond, Ring.choose_natCast, Ring.choose_natCast]
    simp only [Units.smul_def, Int.cast_negOnePow_natCast, zsmul_eq_mul]
    have hs : (-1 : ℤ)^k = -((-1 : ℤ)^(k-1)) := by
      conv_lhs => rw [show k=(k-1)+1 by omega, pow_succ]
      ring
    rw [hs]
    ring

lemma coeff_one_add_X_pow_int (L k : ℕ) :
    PowerSeries.coeff k ((1+PowerSeries.X : PowerSeries ℤ)^L) = (L.choose k : ℤ) := by
  rw [← PowerSeries.binomialSeries_nat (A := ℤ) (R := ℤ) L,
    PowerSeries.binomialSeries_coeff, Ring.choose_natCast]
  simp

lemma coeff_prefactor (L k : ℕ) :
    PowerSeries.coeff k
      ((1+2*PowerSeries.X) * (1+PowerSeries.X : PowerSeries ℤ)^L) =
      (L.choose k : ℤ) +
        (if 1 ≤ k then 2*(L.choose (k-1) : ℤ) else 0) := by
  rw [add_mul]
  rw [map_add]
  simp only [one_mul]
  rw [coeff_one_add_X_pow_int]
  rw [show (2 : PowerSeries ℤ) * PowerSeries.X *
      (1+PowerSeries.X : PowerSeries ℤ)^L =
      PowerSeries.C (2:ℤ) *
        (PowerSeries.X^1 * (1+PowerSeries.X : PowerSeries ℤ)^L) by simp; ring]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, if_pos hk, coeff_one_add_X_pow_int]
  · rw [if_neg hk, if_neg hk]
    ring

lemma neg_one_pow_mul_self (k : ℕ) :
    (-1 : ℤ)^k * (-1 : ℤ)^k = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      calc
        ((-1 : ℤ)^k * -1) * ((-1 : ℤ)^k * -1) =
            ((-1 : ℤ)^k * (-1 : ℤ)^k) * ((-1)*(-1)) := by ring
        _ = 1 := by rw [ih]; norm_num

lemma coeff_negSeries_eq_negDiagSum (A N : ℕ) (hA : 0 < A) :
    PowerSeries.coeff N (negSeries A N) =
      (-1 : ℤ)^N * ∑ k ∈ Finset.range (N+1), negDiagTerm (A+N) k := by
  rw [negSeries, geomV, Finset.mul_sum, map_sum]
  rw [← Finset.sum_flip]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
  let t := N-k
  have htN : t ≤ N := Nat.sub_le _ _
  rw [V, neg_pow, mul_pow]
  rw [show (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) *
      ((-1 : PowerSeries ℤ)^t *
        (PowerSeries.X^t * (1+PowerSeries.X : PowerSeries ℤ)^t)) =
      (-1 : PowerSeries ℤ)^t * PowerSeries.X^t *
        ((1+2*PowerSeries.X) *
          (1+PowerSeries.X : PowerSeries ℤ)^((A-1)+t)) by
            rw [pow_add]; ring]
  rw [show (-1 : PowerSeries ℤ)^t * PowerSeries.X^t *
      ((1+2*PowerSeries.X) *
        (1+PowerSeries.X : PowerSeries ℤ)^(A-1+t)) =
      PowerSeries.C ((-1 : ℤ)^t) *
        (PowerSeries.X^t * ((1+2*PowerSeries.X) *
          (1+PowerSeries.X : PowerSeries ℤ)^(A-1+t))) by simp; ring]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos htN]
  rw [coeff_prefactor]
  have hNt : N-t=k := by dsimp [t]; omega
  rw [hNt]
  by_cases hk0 : k=0
  · have ht : t=N := by dsimp [t]; omega
    simp [hk0, negDiagTerm, ht]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rw [negDiagTerm, if_neg hk0, if_pos (show 1 ≤ k by omega)]
    have hL : A-1+t+1=A+t := by omega
    have hchoose : (A+t).choose k =
        (A-1+t).choose (k-1) + (A-1+t).choose k := by
      obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      simpa [hL] using Nat.choose_succ_succ (A-1+t) q
    have hRk : A+N-k=A+t := by dsimp [t]; omega
    rw [hRk, hchoose]
    rw [show A+t-1=A-1+t by omega]
    have hsign : (-1 : ℤ)^t = (-1 : ℤ)^N * (-1 : ℤ)^k := by
      rw [show N=t+k by dsimp [t]; omega, pow_add]
      rw [mul_assoc, neg_one_pow_mul_self, mul_one]
    rw [hsign]
    push_cast
    ring

lemma negSeries_coeff_value (A N : ℕ) (hA : 0 < A) (hN : 0 < N) :
    PowerSeries.coeff N (negSeries A N) =
      FNat A N + ((A-1).choose (N-1) : ℤ) := by
  rw [negSeries_coeff_eq_target A N hA]
  rw [map_add]
  have hF : PowerSeries.coeff N
      (Core.Qseries * (1+PowerSeries.X : PowerSeries ℤ)^A) = FNat A N := by
    unfold FNat
    simp
  rw [hF]
  rw [show PowerSeries.X * (1+PowerSeries.X : PowerSeries ℤ)^(A-1) =
      PowerSeries.X^1 * (1+PowerSeries.X : PowerSeries ℤ)^(A-1) by simp,
    PowerSeries.coeff_X_pow_mul', if_pos (show 1 ≤ N by omega),
    coeff_one_add_X_pow_int]

lemma formalPartial_negative_involution (A N : ℕ) (hA : 0 < A) (hN : 0 < N)
    (hNA : N ≤ A) :
    formalPartial (-((A+N : ℕ) : ℤ)) N =
      (-1 : ℤ)^N * (FNat A N + ((A-1).choose (N-1) : ℤ)) := by
  have hsum : formalPartial (-((A+N : ℕ) : ℤ)) N =
      ∑ k ∈ Finset.range (N+1), negDiagTerm (A+N) k := by
    unfold formalPartial
    apply Finset.sum_congr rfl
    intro k hk
    apply formalCoeff_neg_eq
    have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
    omega
  rw [hsum]
  have hc := coeff_negSeries_eq_negDiagSum A N hA
  rw [negSeries_coeff_value A N hA hN] at hc
  let S : ℤ := ∑ k ∈ Finset.range (N+1), negDiagTerm (A+N) k
  change FNat A N + ((A-1).choose (N-1) : ℤ) = (-1 : ℤ)^N * S at hc
  change S = (-1 : ℤ)^N * (FNat A N + ((A-1).choose (N-1) : ℤ))
  calc
    S = 1*S := by ring
    _ = (((-1 : ℤ)^N * (-1 : ℤ)^N) * S) := by rw [neg_one_pow_mul_self]
    _ = (-1 : ℤ)^N * ((-1 : ℤ)^N * S) := by ring
    _ = _ := by rw [← hc]

lemma a_gen_negative_involution (S N : ℕ) (hS : 2 ≤ S) (hN : 0 < N) :
    a_gen (-((S+1 : ℕ) : ℤ)) N =
      (-1 : ℤ)^N *
        (a_gen ((S-2 : ℕ) : ℤ) N + ((S*N-1).choose (N-1) : ℤ)) := by
  rw [a_gen, if_neg (Nat.ne_of_gt hN)]
  have hr : -((S+1 : ℕ) : ℤ) * (N : ℤ) = -(((S*N)+N : ℕ) : ℤ) := by
    push_cast
    ring
  change (∑ k ∈ Finset.range (N+1),
      generalized_catalan_coefficient (-((S+1 : ℕ) : ℤ)*(N:ℤ)) k) = _
  rw [hr]
  rw [show (∑ k ∈ Finset.range (N+1),
      generalized_catalan_coefficient (-(((S*N)+N : ℕ) : ℤ)) k) =
      formalPartial (-(((S*N)+N : ℕ) : ℤ)) N by
    unfold formalPartial
    apply Finset.sum_congr rfl
    intro k hk
    apply generalized_catalan_eq_formal
    by_cases hk0 : k=0
    · exact Or.inl hk0
    · right
      have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
      have hSN : 2*N ≤ S*N := Nat.mul_le_mul_right N hS
      push_cast
      omega]
  rw [formalPartial_negative_involution (S*N) N (mul_pos (by omega) hN) hN
    (by nlinarith)]
  rw [a_gen_nat_eq_FNat (S-2) N hN]
  rw [show S-2+2=S by omega]


