import Submission.SmallSignJets

/-!
High-order binary digit moments force additional congruences. In particular,
efficient signed-block multipliers all have the factor three, irrespective of
block length. This does not settle the square-Sidon conjecture.
-/
namespace Erdos773.MomentCongruence
open Polynomial Finset
noncomputable section
set_option maxHeartbeats 1000000

lemma eval_neg_one_abs_le {V : ℤ[X]} {D : ℕ} (hdeg : V.natDegree < D)
    (hc : ∀ i, -1 ≤ V.coeff i ∧ V.coeff i ≤ 1) :
    |V.eval (-1)| ≤ (D : ℤ) := by
  rw [eval_eq_sum_range' hdeg]
  calc
    _ ≤ ∑ i ∈ range D, |V.coeff i * (-1 : ℤ) ^ i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range D, (1 : ℤ) := by
      apply sum_le_sum
      intro i hi
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one] using
        abs_le.mpr (hc i)
    _ = _ := by simp

/-- A small signed polynomial with a high-order zero at one must also vanish
at minus one. -/
theorem neg_one_vanishes {V : ℤ[X]} {D k : ℕ} (hdeg : V.natDegree < D)
    (hc : ∀ i, -1 ≤ V.coeff i ∧ V.coeff i ≤ 1)
    (hj : (X - 1 : ℤ[X]) ^ k ∣ V) (hsize : D < 2 ^ k) :
    V.eval (-1) = 0 := by
  have hb := eval_neg_one_abs_le hdeg hc
  obtain ⟨W, hW⟩ := hj
  have hd : (-2 : ℤ) ^ k ∣ V.eval (-1) := by
    refine ⟨W.eval (-1), ?_⟩
    rw [hW]
    simp
  by_contra hn
  have hh := Int.le_of_dvd (abs_pos.mpr hn) ((abs_dvd_abs _ _).mpr hd)
  have hh' : (2 : ℤ) ^ k ≤ |V.eval (-1)| := by
    simpa [abs_pow] using hh
  have hs : (D : ℤ) < (2 : ℤ) ^ k := by exact_mod_cast hsize
  omega

lemma quadratic_factor_of_vanishes {V : ℤ[X]}
    (h1 : V.eval 1 = 0) (hm1 : V.eval (-1) = 0) :
    (X ^ 2 - 1 : ℤ[X]) ∣ V := by
  have hdiv : (X - 1 : ℤ[X]) ∣ V := by
    simpa only [← C_1] using (dvd_iff_isRoot).mpr h1
  obtain ⟨W, hW⟩ := hdiv
  have hWm : W.eval (-1) = 0 := by
    rw [hW] at hm1
    simp only [eval_mul, eval_sub, eval_X, eval_one] at hm1
    norm_num at hm1
    exact hm1
  have hdivW : (X + 1 : ℤ[X]) ∣ W := by
    simpa using (dvd_iff_isRoot (p := W) (a := (-1 : ℤ))).mpr hWm
  obtain ⟨T, hT⟩ := hdivW
  refine ⟨T, ?_⟩
  rw [hW, hT]
  ring

/-- Every power-of-two specialization of an efficient signed jet polynomial
is divisible by three. Varying the block length does not remove this factor. -/
theorem three_dvd_every_block_multiplier {V : ℤ[X]} {D k : ℕ}
    (hdeg : V.natDegree < D) (hc : ∀ i, -1 ≤ V.coeff i ∧ V.coeff i ≤ 1)
    (hj : (X - 1 : ℤ[X]) ^ k ∣ V) (hk : 0 < k) (hsize : D < 2 ^ k)
    (L : ℕ) : 3 ∣ V.eval ((2 : ℤ) ^ L) := by
  have hm := neg_one_vanishes hdeg hc hj hsize
  have h1 : V.eval 1 = 0 := by
    obtain ⟨W, hW⟩ := hj
    rw [hW]
    simp [Nat.ne_of_gt hk]
  obtain ⟨T, hT⟩ := quadratic_factor_of_vanishes h1 hm
  rw [hT, eval_mul, eval_sub, eval_pow, eval_X, eval_one]
  apply dvd_mul_of_dvd_left
  have hh := sub_dvd_pow_sub_pow (4 : ℤ) 1 L
  norm_num only [show (4 : ℤ) - 1 = 3 by norm_num, one_pow] at hh
  convert hh using 1
  rw [← pow_mul, Nat.mul_comm L 2, pow_mul]
  norm_num

/-- A direct consequence for binary words: sufficiently many matching jets
force the represented integers into the same residue class modulo three.
The common residue can be a unit, so this alone does not exclude prime roots. -/
theorem binary_jet_congruence_three {P Q : ℤ[X]} {D k : ℕ}
    (hP : ∀ i, P.coeff i = 0 ∨ P.coeff i = 1)
    (hQ : ∀ i, Q.coeff i = 0 ∨ Q.coeff i = 1)
    (hD : (P - Q).natDegree < D)
    (hj : (X - 1 : ℤ[X]) ^ k ∣ P - Q) (hsize : D < 2 ^ k) :
    3 ∣ P.eval 2 - Q.eval 2 := by
  have hc (i : ℕ) : -1 ≤ (P-Q).coeff i ∧ (P-Q).coeff i ≤ 1 := by
    rw [coeff_sub]
    rcases hP i with hp | hp <;> rcases hQ i with hq | hq <;> omega
  have hm := neg_one_vanishes hD hc hj hsize
  have hd : (X + 1 : ℤ[X]) ∣ P - Q := by
    simpa using (dvd_iff_isRoot (p := P-Q) (a := (-1 : ℤ))).mpr hm
  obtain ⟨W,hW⟩ := hd
  have he := congrArg (fun V : ℤ[X] => V.eval 2) hW
  refine ⟨W.eval 2, ?_⟩
  simpa using he

lemma cubic_lt_two_pow (k : ℕ) (hk : 17 ≤ k) : 16 * k ^ 3 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h4 : 4 ≤ k := by omega
    have hcube : (k + 1) ^ 3 < 2 * k ^ 3 := by
      nlinarith [Nat.mul_le_mul_right (k ^ 2) h4, Nat.mul_le_mul_right k h4]
    rw [pow_succ (2 : ℕ) k]
    nlinarith only [ih, hcube]

/-- In particular, every signed polynomial of the cubic length used by the
pigeonhole construction has a factor-three specialization once k>=17. -/
theorem three_dvd_cubic_jet_specializations {V : ℤ[X]} {k : ℕ}
    (hk : 17 ≤ k) (hdeg : V.natDegree < 16 * k ^ 3)
    (hc : ∀ i, -1 ≤ V.coeff i ∧ V.coeff i ≤ 1)
    (hj : (X - 1 : ℤ[X]) ^ k ∣ V) (L : ℕ) :
    3 ∣ V.eval ((2 : ℤ) ^ L) :=
  three_dvd_every_block_multiplier hdeg hc hj (by omega) (cubic_lt_two_pow k hk) L

/-- Two efficient signed-block multipliers cannot be made coprime merely by
choosing different block lengths or different signed polynomials. -/
theorem efficient_block_multipliers_not_coprime {V W : ℤ[X]} {k : ℕ}
    (hk : 17 ≤ k) (hV : V.natDegree < 16 * k ^ 3)
    (hW : W.natDegree < 16 * k ^ 3)
    (hcV : ∀ i, -1 ≤ V.coeff i ∧ V.coeff i ≤ 1)
    (hcW : ∀ i, -1 ≤ W.coeff i ∧ W.coeff i ≤ 1)
    (hjV : (X - 1 : ℤ[X]) ^ k ∣ V)
    (hjW : (X - 1 : ℤ[X]) ^ k ∣ W) (L M : ℕ) :
    ¬ Nat.Coprime (V.eval ((2 : ℤ) ^ L)).natAbs (W.eval ((2 : ℤ) ^ M)).natAbs := by
  have hdV : (3 : ℕ) ∣ (V.eval ((2 : ℤ) ^ L)).natAbs :=
    Int.natCast_dvd.mp (three_dvd_cubic_jet_specializations hk hV hcV hjV L)
  have hdW : (3 : ℕ) ∣ (W.eval ((2 : ℤ) ^ M)).natAbs :=
    Int.natCast_dvd.mp (three_dvd_cubic_jet_specializations hk hW hcW hjW M)
  intro hcop
  have hh := Nat.dvd_gcd hdV hdW
  rw [hcop.gcd_eq_one] at hh
  norm_num at hh

#print axioms efficient_block_multipliers_not_coprime

#print axioms neg_one_vanishes
#print axioms three_dvd_every_block_multiplier
#print axioms binary_jet_congruence_three
end
end Erdos773.MomentCongruence
