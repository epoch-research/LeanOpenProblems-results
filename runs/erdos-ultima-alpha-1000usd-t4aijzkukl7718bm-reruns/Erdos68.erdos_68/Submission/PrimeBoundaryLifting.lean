import Submission.PrimeLeadingForms

/-!
An exact prime-endpoint lift for finite Lambert boundaries.
This is auxiliary arithmetic, not a proof or disproof of Erdos 68.
The explicit correction cost is retained; no small-error estimate is asserted.
-/

namespace PrimeBoundaryLifting

open Finset PrimeLeadingForms Erdos68Development

/-- Opposite endpoint weights preserve the retained constant coefficient. -/
def correct (w : ℕ → ℤ) (p : ℕ) (k : ℤ) (n : ℕ) : ℤ :=
  w n + (if n = p then k else 0) - (if n = p-1 then k else 0)

def boundary (c w : ℕ → ℤ) (p : ℕ) : ℚ :=
  ∑ n ∈ range (p+1), (w n : ℚ) * partialSum c n

lemma weighted_correction (w : ℕ → ℤ) (p : ℕ) (k : ℤ) (f : ℕ → ℚ) :
    (∑ n ∈ range (p+1), (correct w p k n : ℚ)*f n) =
      (∑ n ∈ range (p+1), (w n : ℚ)*f n) +
        (k : ℚ)*(f p-f (p-1)) := by
  simp only [correct, Int.cast_sub, Int.cast_add, Int.cast_ite, Int.cast_zero,
    sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [mem_range, Nat.lt_succ_self, if_true,
    show p-1 < p+1 by omega]
  ring

lemma retained_sum (w : ℕ → ℤ) (p : ℕ) (k : ℤ) :
    (∑ n ∈ range (p+1), correct w p k n) = ∑ n ∈ range (p+1), w n := by
  have h := weighted_correction w p k (fun _ => 1)
  simp only [mul_one, sub_self, mul_zero, add_zero, ← Int.cast_sum] at h
  exact_mod_cast h

lemma constraints_preserved (w : ℕ → ℤ) (p : ℕ) (k : ℤ) (f : ℕ → ℚ)
    (hf : f p = f (p-1)) :
    (∑ n ∈ range (p+1), (correct w p k n : ℚ)*f n) =
      ∑ n ∈ range (p+1), (w n : ℚ)*f n := by
  rw [weighted_correction, hf, sub_self, mul_zero, add_zero]

lemma unit_boundary_correction (c w : ℕ → ℤ) (p : ℕ) (hp : 0 < p)
    (hc : c p = 1) (k : ℤ) :
    boundary c (correct w p k) p = boundary c w p + (k : ℚ)/p.factorial := by
  rw [boundary, weighted_correction, partialSum_step c p hp, hc]
  simp only [Int.cast_one, add_sub_cancel_left, mul_one_div]
  rfl

lemma factorial_mul_boundary_integer (c w : ℕ → ℤ) (p : ℕ) :
    ∃ z : ℤ, (p.factorial : ℚ)*boundary c w p = z := by
  rw [boundary, Finset.mul_sum]
  apply integer_sum
  intro n hn
  obtain ⟨z, hz⟩ := factorial_mul_partialSum_integer c p n
    (by have := mem_range.mp hn; omega)
  refine ⟨w n*z, ?_⟩
  rw [mul_left_comm, hz, Int.cast_mul]

/-- Every prescribed integral boundary has an exact endpoint lift.
Its cost is exactly the factorial grid spacing times the required adjustment. -/
theorem lift_integer_boundary (c w : ℕ → ℤ) (p : ℕ) (hp : 0 < p)
    (hc : c p = 1) (b : ℤ) :
    ∃ k : ℤ,
      boundary c (correct w p k) p = b ∧
      (∑ n ∈ range (p+1), correct w p k n) =
        (∑ n ∈ range (p+1), w n) ∧
      (k : ℚ) = (p.factorial : ℚ)*((b : ℚ)-boundary c w p) := by
  obtain ⟨z, hz⟩ := factorial_mul_boundary_integer c w p
  let k : ℤ := (p.factorial : ℤ)*b-z
  have hk : (k : ℚ) = (p.factorial : ℚ)*((b : ℚ)-boundary c w p) := by
    simp only [k, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [mul_sub, hz]
  refine ⟨k, ?_, retained_sum w p k, hk⟩
  rw [unit_boundary_correction c w p hp hc, hk]
  have hfac : (p.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- An endpoint correction has this exact size, not merely a factorial upper bound. -/
lemma correction_cost (c w : ℕ → ℤ) (p : ℕ) (hp : 0 < p)
    (hc : c p = 1) (k b : ℤ)
    (hb : boundary c (correct w p k) p = b) :
    |(k : ℚ)| = (p.factorial : ℚ)*|(b : ℚ)-boundary c w p| := by
  have he := unit_boundary_correction c w p hp hc k
  rw [hb] at he
  have hfac : (p.factorial : ℚ) ≠ 0 := by positivity
  have hk : (k : ℚ) = (p.factorial : ℚ)*((b : ℚ)-boundary c w p) := by
    field_simp at he ⊢
    linear_combination -he
  rw [hk, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < p.factorial)]

lemma prime_row_constant {p d : ℕ} (hp : p.Prime) (hd : 2 ≤ d) (hdp : d < p) :
    (1 : ℚ)/((d.factorial : ℚ)^(p/d)*(d.factorial-1)) =
      1/((d.factorial : ℚ)^((p-1)/d)*(d.factorial-1)) := by
  have hn : ¬ d ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h
    · omega
    · omega
  have he := Nat.succ_div_of_not_dvd (show ¬ d ∣ (p-1)+1 by
    simpa only [Nat.sub_add_cancel hp.one_le] using hn)
  have hdiv : p/d = (p-1)/d := by
    simpa only [Nat.sub_add_cancel hp.one_le] using he
  rw [hdiv]

/-- The endpoint correction does not disturb any earlier factorial row. -/
theorem prime_correction_preserves_rows (w : ℕ → ℤ) (p : ℕ) (hp : p.Prime)
    (k : ℤ) (d : ℕ) (hd : 2 ≤ d) (hdp : d < p) :
    (∑ n ∈ range (p+1), (correct w p k n : ℚ) /
      ((d.factorial : ℚ)^(n/d)*(d.factorial-1))) =
    ∑ n ∈ range (p+1), (w n : ℚ) /
      ((d.factorial : ℚ)^(n/d)*(d.factorial-1)) := by
  simpa only [mul_one_div] using constraints_preserved w p k
    (fun n => (1 : ℚ)/((d.factorial : ℚ)^(n/d)*(d.factorial-1)))
    (prime_row_constant hp hd hdp)

/-- This applies to the exact Lambert prefixes, not a comparison sequence. -/
theorem lambert_lift (w : ℕ → ℤ) (p : ℕ) (hp : p.Prime) (b : ℤ) :
    ∃ k : ℤ,
      boundary (fun n => (lambertCoeff n : ℤ)) (correct w p k) p = b ∧
      (∑ n ∈ range (p+1), correct w p k n) =
        (∑ n ∈ range (p+1), w n) ∧
      (k : ℚ) = (p.factorial : ℚ)*
        ((b : ℚ)-boundary (fun n => (lambertCoeff n : ℤ)) w p) ∧
      ∀ d, 2 ≤ d → d < p →
        (∑ n ∈ range (p+1), (correct w p k n : ℚ) /
          ((d.factorial : ℚ)^(n/d)*(d.factorial-1))) =
        ∑ n ∈ range (p+1), (w n : ℚ) /
          ((d.factorial : ℚ)^(n/d)*(d.factorial-1)) := by
  obtain ⟨k, hb, hs, hk⟩ := lift_integer_boundary
    (fun n => (lambertCoeff n : ℤ)) w p hp.pos (by simp [lambertCoeff_prime hp]) b
  exact ⟨k, hb, hs, hk, fun d hd hdp =>
    prime_correction_preserves_rows w p hp k d hd hdp⟩

end PrimeBoundaryLifting

#print axioms PrimeBoundaryLifting.lift_integer_boundary
#print axioms PrimeBoundaryLifting.lambert_lift
