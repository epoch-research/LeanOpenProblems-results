import FormalConjecturesUtil

/-! Exact coefficient-energy constraints and reciprocal factor flips for
integer polynomials with coefficients in {0,1}. These results do not settle
Erdős 406: no degree bound for the candidate polynomials is asserted. -/
namespace Erdos406ReciprocalFlip
open Polynomial

/-- The coefficient condition, without a normalization at either end. -/
def Binary (P : ℤ[X]) : Prop := ∀ i, P.coeff i = 0 ∨ P.coeff i = 1

lemma int_energy_nonneg (a : ℤ) : 0 ≤ a ^ 2 - a := by
  rcases le_or_gt a 0 with ha | ha
  · nlinarith [sq_nonneg a]
  · have ha1 : 1 ≤ a := ha
    nlinarith

lemma int_energy_zero_iff (a : ℤ) : a ^ 2 - a = 0 ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro h
    have hh : a * (a - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by omega)
  · rintro (rfl | rfl) <;> norm_num

lemma binary_iff_energy_zero (P : ℤ[X]) (N : ℕ) (hN : P.natDegree ≤ N) :
    Binary P ↔ (∑ i ∈ Finset.range (N + 1), P.coeff i ^ 2) = P.eval 1 := by
  have heval : P.eval 1 = ∑ i ∈ Finset.range (N + 1), P.coeff i := by
    simpa using eval_eq_sum_range' (by omega : P.natDegree < N + 1) (1 : ℤ)
  rw [heval]
  constructor
  · intro hb
    apply Finset.sum_congr rfl
    intro i _
    rcases hb i with hi | hi <;> simp [hi]
  · intro he
    have hs : ∑ i ∈ Finset.range (N + 1), (P.coeff i ^ 2 - P.coeff i) = 0 := by
      rw [Finset.sum_sub_distrib, he, sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.range (N + 1)) => int_energy_nonneg (P.coeff i))).mp hs
    intro i
    by_cases hi : i ≤ N
    · exact (int_energy_zero_iff _).mp (hz i (by simp; omega))
    · left
      exact coeff_eq_zero_of_natDegree_lt (by omega)

lemma middle_coeff_reflect (P : ℤ[X]) (N : ℕ) :
    (P * P.reflect N).coeff N = ∑ i ∈ Finset.range (N + 1), P.coeff i ^ 2 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => P.coeff i * (P.reflect N).coeff j) N]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i ≤ N := by simpa using hi
  rw [coeff_reflect, revAt_le (Nat.sub_le N i), Nat.sub_sub_self hiN, pow_two]

lemma eval_one_reflect (P : ℤ[X]) (N : ℕ) (hN : P.natDegree ≤ N) :
    (P.reflect N).eval 1 = P.eval 1 := by
  have hr : (P.reflect N).natDegree ≤ N := by
    exact natDegree_reflect_le.trans (max_le le_rfl hN)
  rw [eval_eq_sum_range' (by omega : (P.reflect N).natDegree < N + 1),
    eval_eq_sum_range' (by omega : P.natDegree < N + 1)]
  simp only [one_pow, mul_one, coeff_reflect]
  calc
    _ = ∑ i ∈ Finset.range (N + 1), P.coeff (N - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [revAt_le (by simpa using hi)]
    _ = _ := by simpa using Finset.sum_range_reflect (fun i => P.coeff i) (N + 1)

/-- Flipping one factor preserves the full autocorrelation polynomial when
reflection is taken in the common degree bound. -/
lemma factor_flip_autocorrelation (Q R : ℤ[X]) :
    (Q * R) * (Q * R).reflect (Q.natDegree + R.natDegree) =
      (Q.reverse * R) * (Q.reverse * R).reflect (Q.natDegree + R.natDegree) := by
  have hqr : Q.reverse.natDegree ≤ Q.natDegree := Q.reverse_natDegree_le
  rw [reflect_mul Q R le_rfl le_rfl, reflect_mul Q.reverse R hqr le_rfl]
  change Q * R * (Q.reverse * R.reflect R.natDegree) =
    Q.reverse * R * ((Q.reflect Q.natDegree).reflect Q.natDegree * R.reflect R.natDegree)
  rw [reflect_reflect]
  ring

/-- An integer polynomial factor of a binary polynomial may be replaced by
its reciprocal without leaving the binary coefficient class. This uses the
exact energy equality, not merely a Mahler-measure upper bound. -/
theorem binary_factor_flip (Q R : ℤ[X]) (hP : Binary (Q * R)) :
    Binary (Q.reverse * R) := by
  let N := Q.natDegree + R.natDegree
  have hPdeg : (Q * R).natDegree ≤ N := natDegree_mul_le
  have hSdeg : (Q.reverse * R).natDegree ≤ N :=
    natDegree_mul_le.trans (Nat.add_le_add_right Q.reverse_natDegree_le _)
  have he := (binary_iff_energy_zero (Q * R) N hPdeg).mp hP
  apply (binary_iff_energy_zero (Q.reverse * R) N hSdeg).mpr
  have ha := congrArg (fun P : ℤ[X] => P.coeff N) (factor_flip_autocorrelation Q R)
  change ((Q * R) * (Q * R).reflect N).coeff N =
    ((Q.reverse * R) * (Q.reverse * R).reflect N).coeff N at ha
  rw [middle_coeff_reflect, middle_coeff_reflect] at ha
  have hv : (Q.reverse * R).eval 1 = (Q * R).eval 1 := by
    simp only [eval_mul]
    rw [show Q.reverse.eval 1 = Q.eval 1 from eval_one_reflect Q Q.natDegree le_rfl]
  rw [← ha, he, hv]

lemma binary_eval_three_injective_bound (N : ℕ) (P S : ℤ[X])
    (hP : Binary P) (hS : Binary S) (hdP : P.natDegree ≤ N)
    (hdS : S.natDegree ≤ N) (he : P.eval 3 = S.eval 3) : P = S := by
  induction N generalizing P S with
  | zero =>
    have hp := eq_C_of_natDegree_eq_zero (show P.natDegree = 0 by omega)
    have hs := eq_C_of_natDegree_eq_zero (show S.natDegree = 0 by omega)
    rw [hp, hs] at he ⊢
    simpa using congrArg C he
  | succ N ih =>
    have hp := congrArg (fun p : ℤ[X] => p.eval 3) (divX_mul_X_add P)
    have hs := congrArg (fun p : ℤ[X] => p.eval 3) (divX_mul_X_add S)
    simp only [eval_add, eval_mul, eval_X, eval_C] at hp hs
    have hbP := hP 0
    have hbS := hS 0
    have hc : P.coeff 0 = S.coeff 0 := by omega
    have hv : P.divX.eval 3 = S.divX.eval 3 := by omega
    have hdP' : P.divX.natDegree ≤ N := by
      rw [natDegree_divX_eq_natDegree_tsub_one]; omega
    have hdS' : S.divX.natDegree ≤ N := by
      rw [natDegree_divX_eq_natDegree_tsub_one]; omega
    have hh := ih P.divX S.divX (fun i => by simpa using hP (i + 1))
      (fun i => by simpa using hS (i + 1)) hdP' hdS' hv
    rw [← divX_mul_X_add P, ← divX_mul_X_add S, hh, hc]

lemma binary_eval_three_injective (P S : ℤ[X]) (hP : Binary P) (hS : Binary S)
    (he : P.eval 3 = S.eval 3) : P = S :=
  binary_eval_three_injective_bound (max P.natDegree S.natDegree) P S hP hS
    (le_max_left ..) (le_max_right ..) he

lemma binary_eval_three_bounds (P : ℤ[X]) (hP : Binary P) (hm : P.Monic) :
    (3 : ℤ) ^ P.natDegree ≤ P.eval 3 ∧
      2 * P.eval 3 < (3 : ℤ) ^ (P.natDegree + 1) := by
  have hnonneg (i : ℕ) : 0 ≤ P.coeff i := by rcases hP i with hi | hi <;> simp [hi]
  have hupper (i : ℕ) : P.coeff i ≤ 1 := by rcases hP i with hi | hi <;> simp [hi]
  have hgeom := geom_sum_mul (3 : ℤ) (P.natDegree + 1)
  have hsum : P.eval 3 ≤ ∑ i ∈ Finset.range (P.natDegree + 1), (3 : ℤ) ^ i := by
    rw [eval_eq_sum_range]
    apply Finset.sum_le_sum
    intro i _
    simpa using mul_le_mul_of_nonneg_right (hupper i) (by positivity : 0 ≤ (3 : ℤ) ^ i)
  constructor
  · rw [eval_eq_sum_range]
    have hh := Finset.single_le_sum (s := Finset.range (P.natDegree + 1))
      (f := fun i => P.coeff i * (3 : ℤ) ^ i)
      (fun i _ => mul_nonneg (hnonneg i) (by positivity))
      (show P.natDegree ∈ Finset.range (P.natDegree + 1) by simp)
    simpa [hm.coeff_natDegree] using hh
  · nlinarith

/-- There is at most one binary monic polynomial of a given degree whose
value at three is a power of two. This does not bound the allowed degrees. -/
lemma binary_power_unique_of_degree (P S : ℤ[X]) (hP : Binary P) (hS : Binary S)
    (hmP : P.Monic) (hmS : S.Monic) (hd : P.natDegree = S.natDegree)
    (k l : ℕ) (hk : P.eval 3 = (2 : ℤ) ^ k) (hl : S.eval 3 = (2 : ℤ) ^ l) : P = S := by
  have hp := binary_eval_three_bounds P hP hmP
  have hs := binary_eval_three_bounds S hS hmS
  rw [← hd, pow_succ] at hs
  rw [pow_succ] at hp
  have hpos : 0 < (3 : ℤ) ^ P.natDegree := by positivity
  have hkl : k = l := by
    rcases lt_trichotomy k l with hh | hh | hh
    · have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show k + 1 ≤ l by omega)
      rw [pow_succ, ← hk, ← hl] at hpow
      nlinarith
    · exact hh
    · have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show l + 1 ≤ k by omega)
      rw [pow_succ, ← hk, ← hl] at hpow
      nlinarith
  apply binary_eval_three_injective P S hP hS
  rw [hk, hl, hkl]

lemma monic_reverse_of_constant_one (Q : ℤ[X]) (_hQ : Q.Monic) (h0 : Q.coeff 0 = 1) :
    Q.reverse.Monic ∧ Q.reverse.natDegree = Q.natDegree := by
  have hc : Q.reverse.coeff Q.natDegree = 1 := by
    rw [coeff_reverse, revAt_le le_rfl, Nat.sub_self, h0]
  have hd : Q.reverse.natDegree = Q.natDegree := by
    exact le_antisymm Q.reverse_natDegree_le (le_natDegree_of_ne_zero (by rw [hc]; norm_num))
  refine ⟨?_, hd⟩
  change Q.reverse.coeff Q.reverse.natDegree = 1
  rwa [hd]

lemma binary_common_degree_ratio (P S : ℤ[X]) (hP : Binary P) (hS : Binary S)
    (hmP : P.Monic) (hmS : S.Monic) (hd : P.natDegree = S.natDegree) :
    2 * P.eval 3 < 3 * S.eval 3 ∧ 2 * S.eval 3 < 3 * P.eval 3 := by
  have hp := binary_eval_three_bounds P hP hmP
  have hs := binary_eval_three_bounds S hS hmS
  rw [← hd, pow_succ] at hs
  rw [pow_succ] at hp
  constructor <;> nlinarith

/-- A uniform, exact necessary condition on reciprocal values of a Newman
divisor. The factor need not itself have nonnegative coefficients. -/
theorem reciprocal_eval_ratio (Q R : ℤ[X]) (hP : Binary (Q * R))
    (hQ : Q.Monic) (hR : R.Monic) (h0 : Q.coeff 0 = 1) (hr : 0 < R.eval 3) :
    2 * Q.eval 3 < 3 * Q.reverse.eval 3 ∧
      2 * Q.reverse.eval 3 < 3 * Q.eval 3 := by
  have hs := binary_factor_flip Q R hP
  obtain ⟨hrm, hrd⟩ := monic_reverse_of_constant_one Q hQ h0
  have hd : (Q * R).natDegree = (Q.reverse * R).natDegree := by
    rw [hQ.natDegree_mul hR, hrm.natDegree_mul hR, hrd]
  have hh := binary_common_degree_ratio (Q * R) (Q.reverse * R) hP hs
    (hQ.mul hR) (hrm.mul hR) hd
  simp only [eval_mul, ← mul_assoc] at hh
  exact ⟨(mul_lt_mul_iff_of_pos_right hr).mp hh.1,
    (mul_lt_mul_iff_of_pos_right hr).mp hh.2⟩

/-- For an actual binary product whose two factors have pure-power values,
a nonreciprocal factor cannot also have a pure-power reciprocal value. -/
theorem reciprocal_power_iff_reciprocal (Q R : ℤ[X]) (hP : Binary (Q * R))
    (hQ : Q.Monic) (hR : R.Monic) (h0 : Q.coeff 0 = 1)
    (k l : ℕ) (hk : Q.eval 3 = (2 : ℤ) ^ k) (hl : R.eval 3 = (2 : ℤ) ^ l) :
    (∃ j : ℕ, Q.reverse.eval 3 = (2 : ℤ) ^ j) ↔ Q.reverse = Q := by
  constructor
  · rintro ⟨j, hj⟩
    have hs := binary_factor_flip Q R hP
    obtain ⟨hrm, hrd⟩ := monic_reverse_of_constant_one Q hQ h0
    have he : Q * R = Q.reverse * R := by
      refine binary_power_unique_of_degree (Q * R) (Q.reverse * R) hP hs
        (hQ.mul hR) (hrm.mul hR) ?_ (k + l) (j + l) ?_ ?_
      · rw [hQ.natDegree_mul hR, hrm.natDegree_mul hR, hrd]
      · rw [eval_mul, hk, hl, pow_add]
      · rw [eval_mul, hj, hl, pow_add]
    exact (mul_right_cancel₀ hR.ne_zero he).symm
  · intro he
    exact ⟨k, by rw [he, hk]⟩

#print axioms binary_power_unique_of_degree
#print axioms reciprocal_power_iff_reciprocal
#print axioms reciprocal_eval_ratio
#print axioms binary_iff_energy_zero
#print axioms factor_flip_autocorrelation
#print axioms binary_factor_flip
end Erdos406ReciprocalFlip
