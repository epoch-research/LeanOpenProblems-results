import Submission.NewmanReciprocalCandidate

/-! Evaluation and derivative congruences for even-degree reciprocal factors.
These are necessary conditions, not a degree bound or a solution of Erdős406. -/

namespace Erdos406ReciprocalCongruence
open Polynomial Erdos406ReciprocalFlip Erdos406ReciprocalCandidate
open Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorCount

lemma symmetric_weighted_sum (D : ℕ) (f : ℕ → ℤ)
    (hf : ∀ i ≤ D, f (D - i) = f i) :
    2 * (∑ i ∈ Finset.range (D + 1), (i : ℤ) * f i) =
      (D : ℤ) * ∑ i ∈ Finset.range (D + 1), f i := by
  have hr := Finset.sum_range_reflect (fun i => (i : ℤ) * f i) (D + 1)
  have he : (∑ i ∈ Finset.range (D + 1), ((D - i : ℕ) : ℤ) * f (D - i)) =
      (D : ℤ) * (∑ i ∈ Finset.range (D + 1), f i) -
        ∑ i ∈ Finset.range (D + 1), (i : ℤ) * f i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hiD : i ≤ D := by simpa using hi
    rw [hf i hiD, Nat.cast_sub hiD]
    ring
  simp only [Nat.add_sub_cancel] at hr
  rw [he] at hr
  omega

lemma euler_eval_sum (Q : ℤ[X]) (x : ℤ) :
    x * Q.derivative.eval x =
      ∑ i ∈ Finset.range (Q.natDegree + 1), (i : ℤ) * (Q.coeff i * x ^ i) := by
  rw [derivative_eval, sum_over_range' _ _ (Q.natDegree + 1) (by omega)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases i with
    | zero => simp
    | succ i => simp only [Nat.succ_sub_one, pow_succ]; ring
  · intro i
    simp

lemma reciprocal_coeff (Q : ℤ[X]) (hQ : Q.reverse = Q) (i : ℕ)
    (hi : i ≤ Q.natDegree) : Q.coeff (Q.natDegree - i) = Q.coeff i := by
  have hh := congrArg (fun P : ℤ[X] => P.coeff i) hQ
  change Q.reverse.coeff i = Q.coeff i at hh
  rwa [coeff_reverse, revAt_le hi] at hh

lemma unit_pow_reflect (x : ℤ) (hx : x ^ 2 = 1) (D i : ℕ)
    (hD : x ^ D = 1) (hi : i ≤ D) : x ^ (D - i) = x ^ i := by
  have hmul : x ^ (D - i) * x ^ i = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hi, hD]
  have hs : x ^ i * x ^ i = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm i 2, pow_mul, hx, one_pow]
  have hh := congrArg (fun a : ℤ => a * x ^ i) hmul
  simpa only [mul_assoc, hs, mul_one, one_mul] using hh

lemma reciprocal_euler_at_unit (Q : ℤ[X]) (hQ : Q.reverse = Q) (x : ℤ)
    (hx : x ^ 2 = 1) (hD : x ^ Q.natDegree = 1) :
    2 * (x * Q.derivative.eval x) = (Q.natDegree : ℤ) * Q.eval x := by
  rw [euler_eval_sum, eval_eq_sum_range]
  apply symmetric_weighted_sum
  intro i hi
  rw [reciprocal_coeff Q hQ i hi, unit_pow_reflect x hx Q.natDegree i hD hi]

lemma reciprocal_even_derivative_one (Q : ℤ[X]) (m : ℕ)
    (hQ : Q.reverse = Q) (hD : Q.natDegree = 2 * m) :
    Q.derivative.eval 1 = (m : ℤ) * Q.eval 1 := by
  have hh := reciprocal_euler_at_unit Q hQ 1 (by norm_num) (by simp)
  rw [hD] at hh
  push_cast at hh
  nlinarith

lemma reciprocal_even_derivative_neg_one (Q : ℤ[X]) (m : ℕ)
    (hQ : Q.reverse = Q) (hD : Q.natDegree = 2 * m) :
    Q.derivative.eval (-1) = -(m : ℤ) * Q.eval (-1) := by
  have hp : (-1 : ℤ) ^ Q.natDegree = 1 := by rw [hD, pow_mul]; norm_num
  have hh := reciprocal_euler_at_unit Q hQ (-1) (by norm_num) hp
  rw [hD] at hh
  push_cast at hh
  nlinarith

lemma second_order_eval_divisibility (Q : ℤ[X]) (a b : ℤ) :
    (b - a) ^ 2 ∣ Q.eval b - Q.eval a - (b - a) * Q.derivative.eval a := by
  let T := taylor a Q
  have h0 := congrArg (eval (b - a)) (divX_mul_X_add T)
  have h1 := congrArg (eval (b - a)) (divX_mul_X_add T.divX)
  simp only [eval_add, eval_mul, eval_X, eval_C, coeff_divX] at h0 h1
  have ht0 : T.coeff 0 = Q.eval a := taylor_coeff_zero a Q
  have ht1 : T.coeff 1 = Q.derivative.eval a := taylor_coeff_one a Q
  have hte : T.eval (b - a) = Q.eval b := taylor_eval_sub a Q b
  rw [ht0, hte] at h0
  rw [show 0 + 1 = 1 by rfl, ht1] at h1
  refine ⟨T.divX.divX.eval (b - a), ?_⟩
  nlinarith [h0, congrArg (fun c : ℤ => c * (b - a)) h1]

/-- Reciprocity doubles the generic modulus-four comparison at minus one
up to modulus sixteen. -/
theorem reciprocal_even_eval_congruence (Q : ℤ[X]) (m : ℕ)
    (hQ : Q.reverse = Q) (hD : Q.natDegree = 2 * m) :
    (16 : ℤ) ∣ Q.eval 3 - (1 - 4 * (m : ℤ)) * Q.eval (-1) := by
  have hh := second_order_eval_divisibility Q (-1) 3
  rw [reciprocal_even_derivative_neg_one Q m hQ hD] at hh
  norm_num only at hh
  convert hh using 1
  ring

lemma sixteen_dvd_odd_factor_iff (m v : ℤ) :
    16 ∣ (1 - 4 * m) * v ↔ 16 ∣ v := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(1 + 4 * m) * s + m ^ 2 * v, ?_⟩
    calc
      v = (1 + 4 * m) * ((1 - 4 * m) * v) + 16 * (m ^ 2 * v) := by ring
      _ = _ := by rw [hs]; ring
  · intro h
    exact dvd_mul_of_dvd_right h _

theorem reciprocal_even_sixteen_dvd_iff (Q : ℤ[X]) (m : ℕ)
    (hQ : Q.reverse = Q) (hD : Q.natDegree = 2 * m) :
    (16 : ℤ) ∣ Q.eval 3 ↔ (16 : ℤ) ∣ Q.eval (-1) := by
  have hc := reciprocal_even_eval_congruence Q m hQ hD
  constructor
  · intro hh
    apply (sixteen_dvd_odd_factor_iff (m : ℤ) _).mp
    have ht := dvd_sub hh hc
    convert ht using 1
    ring
  · intro hh
    have ht := dvd_add hc ((sixteen_dvd_odd_factor_iff (m : ℤ) _).mpr hh)
    simpa using ht

lemma four_dvd_odd_factor_iff (m v : ℤ) :
    4 ∣ (1 + 2 * m) * v ↔ 4 ∣ v := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(1 - 2 * m) * s + m ^ 2 * v, ?_⟩
    calc
      v = (1 - 2 * m) * ((1 + 2 * m) * v) + 4 * (m ^ 2 * v) := by ring
      _ = _ := by rw [hs]; ring
  · intro h
    exact dvd_mul_of_dvd_right h _

theorem reciprocal_even_four_dvd_iff (Q : ℤ[X]) (m : ℕ)
    (hQ : Q.reverse = Q) (hD : Q.natDegree = 2 * m) :
    (4 : ℤ) ∣ Q.eval 3 ↔ (4 : ℤ) ∣ Q.eval 1 := by
  have hc : (4 : ℤ) ∣ Q.eval 3 - (1 + 2 * (m : ℤ)) * Q.eval 1 := by
    have hh := second_order_eval_divisibility Q 1 3
    rw [reciprocal_even_derivative_one Q m hQ hD] at hh
    norm_num only at hh
    convert hh using 1
    ring
  constructor
  · intro hh
    apply (four_dvd_odd_factor_iff (m : ℤ) _).mp
    have ht := dvd_sub hh hc
    convert ht using 1
    ring
  · intro hh
    have ht := dvd_add hc ((four_dvd_odd_factor_iff (m : ℤ) _).mpr hh)
    simpa using ht

/-- A reciprocal irreducible polynomial other than a linear polynomial has
an even degree. This is independent of the numerical evaluation at three. -/
lemma irreducible_reciprocal_degree_even (Q : ℤ[X]) (hQ : Q.reverse = Q)
    (hI : Irreducible Q) (hlin : Q.natDegree ≠ 1) : Even Q.natDegree := by
  rcases Nat.even_or_odd Q.natDegree with he | ho
  · exact he
  · letI : Invertible (-1 : ℤ) := ⟨-1, by ring, by ring⟩
    have hh := eval₂_reflect_mul_pow (RingHom.id ℤ) (-1 : ℤ) Q.natDegree Q le_rfl
    change Q.reverse.eval (-1) * (-1 : ℤ) ^ Q.natDegree = Q.eval (-1) at hh
    rw [hQ, ho.neg_one_pow] at hh
    have hz : Q.IsRoot (-1) := by change Q.eval (-1) = 0; omega
    exact (hI.not_isRoot_of_natDegree_ne_one hlin hz).elim

lemma map_mod_two_eval_one (Q : ℤ[X]) :
    (Q.map (Int.castRingHom (ZMod 2))).eval 1 = ((Q.eval 1 : ℤ) : ZMod 2) := by
  rw [eval_map]
  simpa using eval₂_at_apply (Int.castRingHom (ZMod 2)) (1 : ℤ) (p := Q)

/-- An even value at one, together with even-degree reciprocity, forces a
double root at one after reduction modulo two. -/
theorem reciprocal_even_mod_two_double_root (Q : ℤ[X]) (m : ℕ)
    (hQ : Q.reverse = Q) (hD : Q.natDegree = 2 * m) (he : (2 : ℤ) ∣ Q.eval 1) :
    (X + 1 : (ZMod 2)[X]) ^ 2 ∣ Q.map (Int.castRingHom (ZMod 2)) := by
  let F := Q.map (Int.castRingHom (ZMod 2))
  have h0 : F.eval 1 = 0 := by
    rw [map_mod_two_eval_one]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr he
  have hd : (2 : ℤ) ∣ Q.derivative.eval 1 := by
    rw [reciprocal_even_derivative_one Q m hQ hD]
    exact dvd_mul_of_dvd_right he _
  have h1 : F.derivative.eval 1 = 0 := by
    dsimp only [F]
    rw [derivative_map, map_mod_two_eval_one]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hd
  have hs : (X - C (1 : ZMod 2)) ^ 2 ∣ F := by
    apply X_sub_C_pow_dvd_iff.mpr
    apply X_pow_dvd_iff.mpr
    intro i hi
    change (taylor (1 : ZMod 2) F).coeff i = 0
    interval_cases i <;> simp [h0, h1]
  have hx : (X - C (1 : ZMod 2)) = X + 1 := by
    rw [sub_eq_add_neg, ← C_neg, show -(1 : ZMod 2) = 1 by decide, C_1]
  rwa [hx] at hs

theorem nonlinear_reciprocal_candidate_mod_two (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hI : Irreducible Q)
    (hr : Q.reverse = Q) (hlin : Q.natDegree ≠ 1) :
    (X + 1 : (ZMod 2)[X]) ^ 2 ∣ Q.map (Int.castRingHom (ZMod 2)) := by
  obtain ⟨m, hm⟩ := irreducible_reciprocal_degree_even Q hr hI hlin
  have hp : 0 < Q.natDegree := hQ.natDegree_pos_of_not_isUnit hI.not_isUnit
  exact reciprocal_even_mod_two_double_root Q m hr (by omega)
    (candidate_factor_eval_one_even k hg Q hQ hd hp).1

/-- Nonlinear reciprocal irreducible candidate factors consume at least
four in the product of evaluations at one, rather than merely two. -/
theorem reciprocal_candidate_eval_one_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hI : Irreducible Q)
    (hr : Q.reverse = Q) (hlin : Q.natDegree ≠ 1) :
    (4 : ℤ) ∣ Q.eval 1 ∧ 4 ≤ Q.eval 1 := by
  obtain ⟨m, hm⟩ := irreducible_reciprocal_degree_even Q hr hI hlin
  have hp : 0 < Q.natDegree := hQ.natDegree_pos_of_not_isUnit hI.not_isUnit
  obtain ⟨t, ht, _, he⟩ := candidate_factor_four_exponent_positive k hg Q hQ hd hp
  have h4 : (4 : ℤ) ∣ Q.eval 3 := by rw [he]; exact dvd_pow_self 4 (by omega)
  have hb := (reciprocal_even_four_dvd_iff Q m hr (by omega)).mp h4
  have hpos := (candidate_factor_eval_one_even k hg Q hQ hd hp).2
  refine ⟨hb, ?_⟩
  obtain ⟨u, hu⟩ := hb
  omega

/-- A nonlinear reciprocal irreducible candidate factor whose value at
three is not four has a nonzero multiple of sixteen as its value at -1.
This constrains values, not degrees. -/
theorem reciprocal_candidate_neg_one_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hI : Irreducible Q)
    (hr : Q.reverse = Q) (hlin : Q.natDegree ≠ 1) (hfour : Q.eval 3 ≠ 4) :
    (16 : ℤ) ∣ Q.eval (-1) ∧ 16 ≤ |Q.eval (-1)| := by
  obtain ⟨m, hm⟩ := irreducible_reciprocal_degree_even Q hr hI hlin
  have hp : 0 < Q.natDegree := hQ.natDegree_pos_of_not_isUnit hI.not_isUnit
  obtain ⟨t, ht, _, he⟩ := candidate_factor_four_exponent_positive k hg Q hQ hd hp
  have ht2 : 2 ≤ t := by
    by_contra hh
    have h1 : t = 1 := by omega
    simp [h1] at he
    exact hfour he
  have h16 : (16 : ℤ) ∣ Q.eval 3 := by
    rw [he]
    exact pow_dvd_pow (4 : ℤ) ht2
  have hb := (reciprocal_even_sixteen_dvd_iff Q m hr (by omega)).mp h16
  have hn : Q.eval (-1) ≠ 0 := hI.not_isRoot_of_natDegree_ne_one hlin
  exact ⟨hb, Int.le_abs_of_dvd hn hb⟩

#print axioms reciprocal_even_four_dvd_iff
#print axioms reciprocal_candidate_eval_one_bound
#print axioms reciprocal_even_mod_two_double_root
#print axioms nonlinear_reciprocal_candidate_mod_two
#print axioms reciprocal_candidate_neg_one_bound
#print axioms reciprocal_even_derivative_one
#print axioms reciprocal_even_derivative_neg_one
#print axioms reciprocal_even_eval_congruence
#print axioms reciprocal_even_sixteen_dvd_iff
end Erdos406ReciprocalCongruence
