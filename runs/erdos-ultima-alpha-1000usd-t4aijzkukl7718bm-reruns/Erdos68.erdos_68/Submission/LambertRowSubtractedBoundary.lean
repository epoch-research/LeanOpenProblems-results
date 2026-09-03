import Submission.LambertUnfilteredDetection
import Submission.RankOneBoundaryCounting
import Submission.LambertBoundaryClearing

/-!
Exact factorial-grid boundaries after subtracting initial original rows.
This is auxiliary work; it does not settle the conjecture in Spec.lean.
-/
namespace LambertRowSubtractedBoundary

open Finset Erdos68Development LambertDifferenceOperators LambertRawBounds
  LambertTailRows LambertUnfilteredDetection

noncomputable section

def rowPartial (d n : ℕ) : ℝ := geometricRowTail d 0-geometricRowTail d n

def value (d : ℕ) : ℝ := (∑' k : ℕ, term k)-∑ k ∈ range (d-2), term k

def boundary (d n : ℕ) : ℝ := (prefixQ n : ℝ)-∑ k ∈ range (d-2), rowPartial (k+2) n

lemma tail_eq_shifted_rows (d n : ℕ) (hd : 2 ≤ d) :
    tail d n = ∑' k : ℕ, row n (k+(d-2)) := by
  have hs : Summable (fun k => row n (k+(d-2))) :=
    (summable_nat_add_iff (d-2)).mpr (summable_row n)
  have he := hs.sum_add_tsum_nat_add 1
  rw [tail_eq]
  simpa only [Finset.sum_range_one, Nat.zero_add, row,
    show d-2+2=d by omega,
    show ∀ k : ℕ, k+1+(d-2)+2=k+d+1 by omega] using he

/-- The detected tails have coefficient one on the original target. -/
theorem tail_affine (d n : ℕ) (hd : 2 ≤ d) : tail d n = value d-boundary d n := by
  have he := (summable_row n).sum_add_tsum_nat_add (d-2)
  rw [tsum_row, ← tail_eq_shifted_rows d n hd] at he
  have hfirst : (∑ k ∈ range (d-2), rowPartial (k+2) n) =
      (∑ k ∈ range (d-2), term k)-(∑ k ∈ range (d-2), row n k) := by
    simp only [rowPartial, geometricRowTail, Nat.zero_div, pow_zero, one_mul,
      term, row, sum_sub_distrib]
  rw [value, boundary, hfirst]
  linarith

lemma rowPartial_integral (d n : ℕ) (hd : 2 ≤ d) :
    ∃ z : ℤ, (n.factorial : ℝ)*rowPartial d n = z := by
  induction n with
  | zero => exact ⟨0, by simp [rowPartial]⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    have he : rowPartial d (n+1) = rowPartial d n +
        (if d ∣ n+1 then 1/(d.factorial : ℝ)^((n+1)/d) else 0) := by
      have hh := row_step d n hd
      dsimp only [rowPartial]
      linarith
    by_cases hdiv : d ∣ n+1
    · have hmul : d*((n+1)/d)=n+1 := Nat.mul_div_cancel' hdiv
      have hpow : d.factorial^((n+1)/d) ∣ (n+1).factorial := by
        simpa only [hmul] using factorial_pow_dvd_factorial_mul d ((n+1)/d)
      refine ⟨(n+1 : ℤ)*z+((n+1).factorial/d.factorial^((n+1)/d) : ℕ), ?_⟩
      rw [he, if_pos hdiv, mul_add]
      have hfirst : ((n+1).factorial : ℝ)*rowPartial d n = (n+1 : ℝ)*z := by
        rw [Nat.factorial_succ, Nat.cast_mul, mul_assoc, hz]
        norm_cast
      rw [hfirst]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
      rw [Nat.cast_div hpow (by positivity : ((d.factorial^((n+1)/d) : ℕ) : ℝ) ≠ 0)]
      push_cast
      ring
    · refine ⟨(n+1 : ℤ)*z, ?_⟩
      rw [he, if_neg hdiv, add_zero, Nat.factorial_succ, Nat.cast_mul, mul_assoc, hz]
      push_cast
      ring

/-- Unlike a shift-product boundary, this boundary needs no quadratic shift
in its factorial clearing index. -/
theorem boundary_factorial_integral (d n : ℕ) :
    ∃ z : ℤ, (n.factorial : ℝ)*boundary d n = z := by
  obtain ⟨a, ha⟩ := LambertBoundaryClearing.prefixQ_factorial_integral n
  choose b hb using fun k => rowPartial_integral (k+2) n (by omega)
  refine ⟨a-∑ k ∈ range (d-2), b k, ?_⟩
  rw [boundary, mul_sub, ha, mul_sum]
  simp only [hb, Int.cast_sub, Int.cast_sum]

theorem boundary_common_integral (d n T : ℕ) (hn : n ≤ T) :
    ∃ z : ℤ, (T.factorial : ℝ)*boundary d n = z := by
  obtain ⟨z, hz⟩ := boundary_factorial_integral d n
  obtain ⟨a, ha⟩ := Nat.factorial_dvd_factorial hn
  refine ⟨(a : ℤ)*z, ?_⟩
  rw [ha]
  push_cast
  rw [mul_right_comm, hz]
  ring

def valueQ (d : ℕ) (q : ℚ) : ℚ :=
  q-∑ k ∈ range (d-2), 1/(((k+2).factorial : ℚ)-1)

lemma value_rational (d : ℕ) (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ)) :
    value d = (valueQ d q : ℝ) := by
  rw [value, hq]
  simp only [valueQ, Rat.cast_sub, Rat.cast_sum, Rat.cast_div,
    Rat.cast_one, Rat.cast_natCast, term]

#print axioms tail_affine
#print axioms rowPartial_integral
#print axioms boundary_common_integral
#print axioms value_rational

end
end LambertRowSubtractedBoundary
