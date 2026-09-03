import Submission.LambertQuadraticWindow

/-!
Exact zero-pair vectors in enlarged quadratic Lambert windows.
This is an obstruction to an indiscriminate nonvanishing claim, not a proof
or disproof of the conjecture in Spec.lean.
-/
namespace LambertZeroPairWindow

open Finset BoundaryPigeonhole LambertBoundaryClearing LambertBoundaryForms
  LambertQuadraticWindow Erdos68Development

/-- A bounded relation among differences of boundaries lifts to a nonzero
weight vector whose sum and aggregate boundary are both exactly zero. -/
theorem zero_pair_of_difference_clearing
    (D C Q : ℕ) (hC : 0 < C) (hcard : C < (Q+1)^D)
    (x η : ℝ) (A : ℤ) (B : Fin (D+1) → ℝ)
    (hB : ∀ i, ∃ z : ℤ, (C:ℝ)*B i = z)
    (he : ∀ i, |(A:ℝ)*x-B i| ≤ η)
    (hsmall : 2*(D:ℝ)*Q*η < 1) :
    ∃ w : Fin (D+1) → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ D*Q) ∧
      (∑ i, w i) = 0 ∧ (∑ i, (w i:ℝ)*B i) = 0 := by
  classical
  let Δ : Fin D → ℝ := fun i => B i.succ-B 0
  have hΔ : ∀ i, ∃ z : ℤ, (C:ℝ)*Δ i = z := by
    intro i
    obtain ⟨z, hz⟩ := hB i.succ
    obtain ⟨t, ht⟩ := hB 0
    refine ⟨z-t, ?_⟩
    simp only [Δ, mul_sub, hz, ht, Int.cast_sub]
  have heΔ : ∀ i, |(0:ℤ)*(0:ℝ)-Δ i| ≤ 2*η := by
    intro i
    simp only [Int.cast_zero, zero_mul, zero_sub, abs_neg, Δ]
    calc
      _ = |((A:ℝ)*x-B 0)-((A:ℝ)*x-B i.succ)| := by congr 1; ring
      _ ≤ |(A:ℝ)*x-B 0|+|(A:ℝ)*x-B i.succ| := abs_sub _ _
      _ ≤ η+η := add_le_add (he 0) (he i.succ)
      _ = _ := by ring
  obtain ⟨v, hv, hsize, z, hz, herr⟩ :=
    small_integral_form D C Q hC hcard 0 (2*η) 0 Δ hΔ heΔ
  have hz0 : z = 0 := by
    have hlt : |(z:ℝ)| < 1 := by
      have hb : (D:ℝ)*Q*(2*η) < 1 := by nlinarith [hsmall]
      simpa using herr.trans_lt hb
    have hi : |z| < (1:ℤ) := by exact_mod_cast hlt
    have := abs_lt.mp hi
    omega
  have hD : 0 < D := by
    by_contra h
    have hd : D = 0 := by omega
    subst D
    exact hv (Subsingleton.elim _ _)
  let w : Fin (D+1) → ℤ := Fin.cons (-(∑ i, v i)) v
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro hw
    apply hv
    funext i
    have hi := congrFun hw i.succ
    simpa only [w, Fin.cons_succ, Pi.zero_apply] using hi
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [w, Fin.cons_zero, abs_neg]
      calc
        _ ≤ ∑ j, |v j| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin D, (Q:ℤ) := sum_le_sum (fun j _ => hsize j)
        _ = _ := by simp
    · simp only [w, Fin.cons_succ]
      exact (hsize j).trans (by
        have hd : (1:ℤ) ≤ D := by omega
        nlinarith)
  · simp [w, Fin.sum_univ_succ]
  · have heq : ∑ i, (w i:ℝ)*B i = ∑ i, (v i:ℝ)*Δ i := by
      simp only [Fin.sum_univ_succ, w, Fin.cons_zero, Fin.cons_succ,
        Int.cast_neg, Int.cast_sum, Δ, mul_sub, sum_sub_distrib, ← sum_mul]
      ring
    rw [heq, hz, hz0, Int.cast_zero]

lemma enlarged_window_card (K : ℕ) (hK : 1 ≤ K) :
    commonMultiplier (List.range' 2 K) (2*K^2) <
      ((4*K^2)^4+1)^(K^2) := by
  have hn : 2*K^2+(List.range' 2 K).sum ≤ 4*K^2 := by
    have hs := shift_sum_bound K hK
    omega
  calc
    _ ≤ (2*K^2+(List.range' 2 K).sum).factorial := Nat.div_le_self _ _
    _ ≤ (4*K^2).factorial := Nat.factorial_le hn
    _ ≤ (4*K^2)^(4*K^2) := Nat.factorial_le_pow _
    _ = ((4*K^2)^4)^(K^2) := by rw [pow_mul]
    _ < _ := Nat.pow_lt_pow_left (by omega) (by positivity)

/-- Nonzero polynomially bounded weights can give the identically zero
coefficient pair. This holds unconditionally for every K at least 32. -/
theorem quadratic_zero_pair (K : ℕ) (hK : 32 ≤ K) :
    ∃ w : Fin (K^2+1) → ℤ, w ≠ 0 ∧
      (∀ i, |w i| ≤ (K:ℤ)^2*(4*(K:ℤ)^2)^4) ∧
      (∑ i, w i) = 0 ∧
      (∑ i, (w i:ℝ)*(boundary (List.range' 2 K) (K^2+i):ℝ)) = 0 := by
  let η : ℝ := 2^(K+1)/((K+1:ℕ):ℝ)^(K^2/2-1)
  have hsmall : 2*((K^2:ℕ):ℝ)*(((4*K^2)^4:ℕ):ℝ)*η < 1 := by
    have he := quadratic_window_error_bound K (by omega)
    have hk : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hb : (512:ℝ)/(K:ℝ)^2 < 1 := by
      apply (div_lt_one (sq_pos_of_pos hk)).mpr
      have hn : (32:ℝ) ≤ K := by exact_mod_cast hK
      nlinarith
    calc
      _ = 2*(((K^2:ℕ):ℝ)*(((4*K^2)^4:ℕ):ℝ)*η) := by ring
      _ ≤ 2*(256/(K:ℝ)^2) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = 512/(K:ℝ)^2 := by ring
      _ < 1 := hb
  have hB : ∀ i : Fin (K^2+1), ∃ z : ℤ,
      (commonMultiplier (List.range' 2 K) (2*K^2):ℝ)*
        (boundary (List.range' 2 K) (K^2+i):ℝ) = z := by
    intro i
    rw [boundary_cast]
    apply commonMultiplier_boundary_integral
    have hi := i.isLt
    omega
  have he : ∀ i : Fin (K^2+1),
      |(coefficient (List.range' 2 K):ℝ)*(∑' k:ℕ, term k)-
        (boundary (List.range' 2 K) (K^2+i):ℝ)| ≤ η := by
    intro i
    exact window_error_bound K (K^2) (K^2+i) (by nlinarith) (by omega)
  obtain ⟨w, hw, hs, hz, hb⟩ := zero_pair_of_difference_clearing
    (K^2) (commonMultiplier (List.range' 2 K) (2*K^2)) ((4*K^2)^4)
    (commonMultiplier_pos _ _) (enlarged_window_card K (by omega))
    (∑' k:ℕ, term k) η (coefficient (List.range' 2 K))
    (fun i => (boundary (List.range' 2 K) (K^2+i):ℝ)) hB he hsmall
  refine ⟨w, hw, ?_, hz, hb⟩
  intro i
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hs i

end LambertZeroPairWindow

#print axioms LambertZeroPairWindow.zero_pair_of_difference_clearing
#print axioms LambertZeroPairWindow.quadratic_zero_pair
