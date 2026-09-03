import FormalConjecturesUtil

/-!
Factorial-scaled difference operators that annihilate geometric Lambert rows.
These are auxiliary identities, not a proof of the conjecture in Spec.lean.
-/

namespace LambertDifferenceOperators

noncomputable section

def rowShift (d : ℕ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  r (n + d) - r n / d.factorial

def applyShifts : List ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | [], r => r
  | d :: ds, r => applyShifts ds (rowShift d r)

lemma rowShift_zero (d : ℕ) : rowShift d (fun _ => 0) = fun _ => 0 := by
  funext n
  simp [rowShift]

lemma applyShifts_zero (ds : List ℕ) : applyShifts ds (fun _ => 0) = fun _ => 0 := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [applyShifts, rowShift_zero, ih]

lemma rowShift_commute (d e : ℕ) (r : ℕ → ℝ) :
    rowShift d (rowShift e r) = rowShift e (rowShift d r) := by
  funext n
  simp only [rowShift, Nat.add_assoc, Nat.add_comm d e]
  ring

/-- The extra factorial after a shift clears its divisor through a binomial
coefficient, rather than through the denominator `d! - 1` of a whole row. -/
lemma scaled_rowShift (a d n : ℕ) (r : ℕ → ℝ) :
    ((n + a + d).factorial : ℝ) * rowShift d r n =
      ((n + d + a).factorial : ℝ) * r (n + d) -
        ((n + a + d).choose d : ℝ) * ((n + a).factorial : ℝ) * r n := by
  have hf : ((n + a + d).factorial : ℝ) =
      ((n + a + d).choose d : ℝ) * (n + a).factorial * d.factorial := by
    exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial (n + a) d).symm
  have hd : (d.factorial : ℝ) ≠ 0 := by positivity
  rw [show n + d + a = n + a + d by omega]
  unfold rowShift
  rw [mul_sub, hf]
  field_simp

/-- Finite iteration preserves integrality after increasing the factorial
index by the sum of the shifts. -/
theorem applyShifts_integral (ds : List ℕ) (r : ℕ → ℝ) (a N : ℕ)
    (h : ∀ n ≥ N, ∃ z : ℤ, ((n + a).factorial : ℝ) * r n = z) :
    ∀ n ≥ N, ∃ z : ℤ,
      ((n + a + ds.sum).factorial : ℝ) * applyShifts ds r n = z := by
  induction ds generalizing r a with
  | nil => simpa only [List.sum_nil, Nat.add_zero, applyShifts] using h
  | cons d ds ih =>
      have h' : ∀ n ≥ N, ∃ z : ℤ,
          ((n + (a + d)).factorial : ℝ) * rowShift d r n = z := by
        intro n hn
        obtain ⟨z₀, hz₀⟩ := h n hn
        obtain ⟨z₁, hz₁⟩ := h (n + d) (by omega)
        refine ⟨z₁ - ((n + a + d).choose d : ℤ) * z₀, ?_⟩
        rw [← Nat.add_assoc, scaled_rowShift, hz₁]
        rw [mul_assoc, hz₀]
        push_cast
        rfl
      have hi := ih (rowShift d r) (a + d) h'
      simpa only [applyShifts, List.sum_cons, Nat.add_assoc] using hi

lemma applyShifts_annihilate (ds : List ℕ) (d : ℕ) (r : ℕ → ℝ)
    (hd : d ∈ ds) (hr : rowShift d r = fun _ => 0) :
    applyShifts ds r = fun _ => 0 := by
  induction ds generalizing r with
  | nil => simp at hd
  | cons e ds ih =>
      rcases List.mem_cons.mp hd with he | ht
      · subst e
        simp only [applyShifts, hr, applyShifts_zero]
      · apply ih (rowShift e r) ht
        rw [rowShift_commute, hr, rowShift_zero]

/-- The unscaled remaining geometric tail of row `d`, after Lambert degrees
through `n` have been removed. -/
def geometricRowTail (d n : ℕ) : ℝ :=
  1 / (((d.factorial : ℝ) ^ (n / d)) * (d.factorial - 1))

lemma geometricRowTail_shift (d : ℕ) (hd : 0 < d) (n : ℕ) :
    geometricRowTail d (n + d) = geometricRowTail d n / d.factorial := by
  simp only [geometricRowTail, Nat.add_div_right _ hd, pow_succ,
    mul_inv_rev, div_eq_mul_inv]
  ring

lemma rowShift_geometricRowTail (d : ℕ) (hd : 0 < d) :
    rowShift d (geometricRowTail d) = fun _ => 0 := by
  funext n
  simp only [rowShift, geometricRowTail_shift d hd, sub_self]

theorem applyShifts_geometricRowTail (ds : List ℕ) (d : ℕ)
    (hd : 0 < d) (hm : d ∈ ds) :
    applyShifts ds (geometricRowTail d) = fun _ => 0 :=
  applyShifts_annihilate ds d _ hm (rowShift_geometricRowTail d hd)

end

end LambertDifferenceOperators

#print axioms LambertDifferenceOperators.applyShifts_integral
#print axioms LambertDifferenceOperators.applyShifts_geometricRowTail
