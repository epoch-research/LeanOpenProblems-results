import Submission.RisingHalfIntegerRoots

/-! Positivity of the half-integer-root remainder construction. The needed
smallness after primitive integer normalization is NOT asserted here. -/

namespace HalfIntegerPositive

open Finset Polynomial RisingHalfIntegerRoots RisingMonicForms Erdos68Development

noncomputable def kernel (N : ℕ) : Polynomial ℤ :=
  ∏ j ∈ range N, (C 2*X+C (2*(j : ℤ)+3))

noncomputable def factor (x : ℝ) (j : ℕ) : ℝ := 2*x+2*(j : ℝ)+3

lemma kernel_eval (N : ℕ) (x : ℝ) :
    (kernel N).eval₂ (Int.castRingHom ℝ) x = ∏ j ∈ range N, factor x j := by
  simp [kernel, factor, eval₂_finset_prod, add_assoc]

lemma kernel_eval_one_pos (N : ℕ) : 0 < ((kernel N).eval 1 : ℤ) := by
  simp only [kernel, eval_prod, eval_add, eval_mul, eval_C, eval_X, mul_one]
  exact prod_pos (fun j _ => by positivity)

lemma kernel_natDegree (N : ℕ) : (kernel N).natDegree = N := by
  rw [kernel, natDegree_prod _ _ (fun j _ => by
    have h : (C 2*X+C (2*(j : ℤ)+3) : Polynomial ℤ).coeff 1 = 2 := by simp
    intro hz
    rw [hz] at h
    norm_num at h)]
  simp only [natDegree_add_C, natDegree_C_mul_X 2 (by norm_num : (2 : ℤ) ≠ 0)]
  simp

private lemma cells_strictAnti {k : ℕ} (r : Fin k → ℝ)
    (hc : ∀ i, -((i.val+1 : ℕ) : ℝ)-1/2 < r i ∧
      r i < -((i.val+1 : ℕ) : ℝ)+1/2) : StrictAnti r := by
  intro i j hij
  have hi := hc i
  have hj := hc j
  have he : (i.val : ℝ)+1 ≤ j.val := by
    exact_mod_cast (show i.val+1 ≤ j.val from hij)
  norm_num only [Nat.cast_add, Nat.cast_one] at hi hj
  linarith

private lemma factor_own_pos {k : ℕ} (r : Fin k → ℝ)
    (hc : ∀ i, -((i.val+1 : ℕ) : ℝ)-1/2 < r i ∧
      r i < -((i.val+1 : ℕ) : ℝ)+1/2) (i : Fin k) : 0 < factor (r i) i.val := by
  have h := (hc i).1
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  unfold factor
  linarith

private lemma paired_factor_pos {k : ℕ} (r : Fin k → ℝ)
    (hc : ∀ i, -((i.val+1 : ℕ) : ℝ)-1/2 < r i ∧
      r i < -((i.val+1 : ℕ) : ℝ)+1/2) (i j : Fin k) (hne : j ≠ i) :
    0 < factor (r i) j.val*(r i-r j) := by
  rcases lt_or_gt_of_ne hne with hji | hij
  · have hi := (hc i).2
    have he : (j.val : ℝ)+1 ≤ i.val := by
      exact_mod_cast (show j.val+1 ≤ i.val from hji)
    have hr := cells_strictAnti r hc hji
    have hf : factor (r i) j.val < 0 := by
      unfold factor
      norm_num only [Nat.cast_add, Nat.cast_one] at hi
      linarith
    exact mul_pos_of_neg_of_neg hf (by linarith)
  · have hi := (hc i).1
    have he : (i.val : ℝ)+1 ≤ j.val := by
      exact_mod_cast (show i.val+1 ≤ j.val from hij)
    have hr := cells_strictAnti r hc hij
    have hf : 0 < factor (r i) j.val := by
      unfold factor
      norm_num only [Nat.cast_add, Nat.cast_one] at hi
      linarith
    exact mul_pos hf (by linarith)

/-- The numerator and the interpolation denominator have the same sign.
Pairing their factors avoids any parity or derivative convention. -/
lemma kernel_times_node_den_pos (N k : ℕ) (hkN : k ≤ N) (r : Fin k → ℝ)
    (hc : ∀ i, -((i.val+1 : ℕ) : ℝ)-1/2 < r i ∧
      r i < -((i.val+1 : ℕ) : ℝ)+1/2) (i : Fin k) :
    0 < (kernel N).eval₂ (Int.castRingHom ℝ) (r i)*
      (∏ j ∈ univ.erase i, (r i-r j)) := by
  have hp : 0 < (∏ j : Fin k, factor (r i) j.val)*
      (∏ j ∈ univ.erase i, (r i-r j)) := by
    rw [← mul_prod_erase univ (fun j : Fin k => factor (r i) j.val) (mem_univ i)]
    rw [mul_assoc, ← prod_mul_distrib]
    exact mul_pos (factor_own_pos r hc i)
      (prod_pos (fun j hj => paired_factor_pos r hc i j (mem_erase.mp hj).1))
  have ht : 0 < ∏ j ∈ range (N-k), factor (r i) (k+j) := by
    apply prod_pos
    intro j _
    have hi := (hc i).1
    have he : (i.val : ℝ)+1 ≤ k := by exact_mod_cast i.isLt
    norm_num only [Nat.cast_add, Nat.cast_one] at hi
    unfold factor
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  rw [kernel_eval, ← Nat.add_sub_of_le hkN, prod_range_add,
    ← Fin.prod_univ_eq_prod_range]
  rw [mul_right_comm]
  exact mul_pos hp ht

lemma kernel_lagrange_term_pos (N k : ℕ) (hkN : k ≤ N) (r : Fin k → ℝ)
    (hc : ∀ i, -((i.val+1 : ℕ) : ℝ)-1/2 < r i ∧
      r i < -((i.val+1 : ℕ) : ℝ)+1/2) (i : Fin k) :
    0 < (kernel N).eval₂ (Int.castRingHom ℝ) (r i)*
      (Lagrange.basis univ r i).eval 1 := by
  have hn : 0 < ∏ j ∈ univ.erase i, (1-r j) := by
    apply prod_pos
    intro j _
    have hj := (hc j).2
    have hnat := Nat.cast_nonneg (α := ℝ) j.val
    norm_num only [Nat.cast_add, Nat.cast_one] at hj
    linarith
  have hd := kernel_times_node_den_pos N k hkN r hc i
  have hq : 0 < (kernel N).eval₂ (Int.castRingHom ℝ) (r i) /
      (∏ j ∈ univ.erase i, (r i-r j)) := div_pos_iff.mpr (mul_pos_iff.mp hd)
  have he : (Lagrange.basis univ r i).eval 1 =
      (∏ j ∈ univ.erase i, (1-r j))/(∏ j ∈ univ.erase i, (r i-r j)) := by
    simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_mul,
      eval_C, eval_sub, eval_X]
    simp_rw [mul_comm (r i-r _ )⁻¹, ← div_eq_mul_inv]
    rw [prod_div_distrib]
  rw [he]
  convert mul_pos hq hn using 1
  ring

theorem remainder_eval_pos (N k : ℕ) (hk : 5 ≤ k) (hkN : k ≤ N) :
    0 < ((kernel N %ₘ rowPolynomial (k-1)).eval 1 : ℤ) := by
  classical
  obtain ⟨r, hinj, hc, hroots⟩ := root_enumeration k hk
  let T : Polynomial ℝ := (kernel N %ₘ rowPolynomial (k-1)).map (Int.castRingHom ℝ)
  have hrow1 : rowPolynomial (k-1) ≠ 1 := by
    intro h
    have hd := rowPolynomial_natDegree (k-1)
    rw [h, natDegree_one] at hd
    omega
  have hnat : T.natDegree < k := by
    have hd := natDegree_modByMonic_lt (kernel N) (rowPolynomial_monic (k-1)) hrow1
    rw [rowPolynomial_natDegree] at hd
    have hm := natDegree_map_le (p := kernel N %ₘ rowPolynomial (k-1))
      (f := Int.castRingHom ℝ)
    dsimp [T]
    omega
  have hdeg : T.degree < ((univ : Finset (Fin k)).card : WithBot ℕ) := by
    simp only [card_univ, Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hnat)
  have heval (i : Fin k) : T.eval (r i) = (kernel N).eval₂ (Int.castRingHom ℝ) (r i) := by
    have hm : r i ∈ ((rowPolynomial (k-1)).map (Int.castRingHom ℝ)).roots := by
      rw [hroots]
      simp
    have hp := (rowPolynomial_monic (k-1)).map (Int.castRingHom ℝ)
    have hr := (mem_roots hp.ne_zero).mp hm
    simp only [IsRoot, eval_map] at hr
    dsimp [T]
    rw [eval_map]
    exact eval₂_modByMonic_eq_self_of_root (rowPolynomial_monic (k-1)) hr
  have ht : 0 < T.eval 1 := by
    rw [Lagrange.eq_interpolate hinj.injOn hdeg, Lagrange.interpolate_apply,
      eval_finset_sum]
    simp only [eval_mul, eval_C]
    apply sum_pos
    · intro i _
      rw [heval]
      exact kernel_lagrange_term_pos N k hkN r hc i
    · exact ⟨⟨0, by omega⟩, mem_univ _⟩
  have he : T.eval 1 = (((kernel N %ₘ rowPolynomial (k-1)).eval 1 : ℤ) : ℝ) := by
    dsimp [T]
    rw [eval_map]
    simpa only [map_one] using eval₂_at_apply (p := kernel N %ₘ rowPolynomial (k-1))
      (Int.castRingHom ℝ) (1 : ℤ)
  rw [he] at ht
  exact_mod_cast ht

/-- Every row after the four exceptional initial row polynomials is strictly
positive, including all the rows beyond the kernel degree. -/
theorem residueRow_pos (N n : ℕ) (hn : 4 ≤ n) : 0 < residueRow (kernel N) n := by
  by_cases h : n+1 ≤ N
  · have hp := remainder_eval_pos N (n+1) (by omega) h
    simp only [Nat.add_sub_cancel] at hp
    exact mul_pos (by exact_mod_cast hp) (term_pos n)
  · rw [residueRow_of_large_index (kernel N) n (by rw [kernel_natDegree]; omega)]
    exact mul_pos (by exact_mod_cast kernel_eval_one_pos N) (term_pos n)

noncomputable def headBoundary (N : ℕ) : ℤ :=
  ∑ n ∈ range 4, (kernel N /ₘ rowPolynomial n).eval 1

noncomputable def retained (N : ℕ) : ℤ := 13685*(kernel N).eval 1

noncomputable def integralBoundary (N : ℕ) : ℤ :=
  13685*(RisingMonicForms.boundary (kernel N)-headBoundary N)+17132*(kernel N).eval 1

lemma first_four_terms : (∑ n ∈ range 4, term n) = (17132/13685 : ℝ) := by
  norm_num [sum_range_succ, term, Nat.factorial]

lemma head_residue_sum (N : ℕ) :
    (∑ n ∈ range 4, residueRow (kernel N) n) =
      (((kernel N).eval 1 : ℤ) : ℝ)*(17132/13685) - (headBoundary N : ℝ) := by
  simp_rw [row_identity]
  rw [sum_sub_distrib, ← mul_sum, first_four_terms]
  simp [headBoundary]

/-- Exact integer form for the full original target. No omitted tail is
dropped; the right side includes every row beginning with original 6!-1. -/
theorem integer_form_identity (N : ℕ) :
    (retained N : ℝ)*(∑' n : ℕ, term n)-(integralBoundary N : ℝ) =
      13685*(∑' n : ℕ, residueRow (kernel N) (n+4)) := by
  have hs := (hasSum_residueRows (kernel N)).summable.sum_add_tsum_nat_add 4
  rw [(hasSum_residueRows (kernel N)).tsum_eq, head_residue_sum] at hs
  unfold retained integralBoundary
  push_cast
  linear_combination -13685*hs

/-- This is a positive family of integer forms, not a family proved small.
The primitive normalized errors have no asymptotic bound in this file. -/
theorem integer_form_pos (N : ℕ) :
    0 < (retained N : ℝ)*(∑' n : ℕ, term n)-(integralBoundary N : ℝ) := by
  rw [integer_form_identity]
  have hs : Summable (fun n => residueRow (kernel N) (n+4)) :=
    (summable_nat_add_iff 4).mpr (hasSum_residueRows (kernel N)).summable
  exact mul_pos (by norm_num) (hs.tsum_pos (fun n => (residueRow_pos N (n+4) (by omega)).le)
    0 (residueRow_pos N (0+4) (by omega)))

/-- Even before estimating growth, the first retained positive integral
remainder excludes smallness of the unreduced forms. This statement is not
about the pair after division by its gcd. -/
theorem unreduced_error_gt_nineteen (N : ℕ) :
    19 < (retained N : ℝ)*(∑' n : ℕ, term n)-(integralBoundary N : ℝ) := by
  have hpos := residueRow_pos N 4 (by omega)
  have hp : (0 : ℝ) < (((kernel N %ₘ rowPolynomial 4).eval 1 : ℤ) : ℝ) :=
    pos_of_mul_pos_left hpos (term_pos 4).le
  have hpZ : (0 : ℤ) < (kernel N %ₘ rowPolynomial 4).eval 1 := by exact_mod_cast hp
  have hge : (1 : ℝ) ≤ (((kernel N %ₘ rowPolynomial 4).eval 1 : ℤ) : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ (kernel N %ₘ rowPolynomial 4).eval 1 by omega)
  have hrow : (1/719 : ℝ) ≤ residueRow (kernel N) 4 := by
    have h := mul_le_mul_of_nonneg_right hge (term_pos 4).le
    simpa only [one_mul, residueRow, term, show 4+2=6 by omega,
      show (6 : ℕ).factorial=720 by decide, Nat.cast_ofNat, show (720 : ℝ)-1=719 by norm_num]
      using h
  have hs : Summable (fun n => residueRow (kernel N) (n+4)) :=
    (summable_nat_add_iff 4).mpr (hasSum_residueRows (kernel N)).summable
  have ht := hs.le_tsum 0 (fun n _ => (residueRow_pos N (n+4) (by omega)).le)
  rw [integer_form_identity]
  norm_num only [zero_add] at ht
  linarith

end HalfIntegerPositive

#print axioms HalfIntegerPositive.kernel_times_node_den_pos
#print axioms HalfIntegerPositive.kernel_lagrange_term_pos

#print axioms HalfIntegerPositive.remainder_eval_pos
#print axioms HalfIntegerPositive.residueRow_pos
#print axioms HalfIntegerPositive.integer_form_identity
#print axioms HalfIntegerPositive.integer_form_pos
#print axioms HalfIntegerPositive.unreduced_error_gt_nineteen
