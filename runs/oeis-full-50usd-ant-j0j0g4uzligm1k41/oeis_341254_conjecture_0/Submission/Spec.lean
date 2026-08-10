import FormalConjectures.Util.ProblemImports

open Real

/-- The constant $r = (2 + \sqrt{5})/2$. -/
noncomputable def r_const : ℝ := (2 + sqrt 5) / 2

/-- The constant $r^2$. -/
noncomputable def r_sq : ℝ := r_const * r_const

/--
A341254: $a(n) = \lfloor r \cdot \lfloor r \cdot n \rfloor \rfloor$, where $r = (2 + \sqrt{5})/2$.
Note: The original OEIS definition has $n$ starting at 1. We define $a(n)$ for all $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let r := r_const
  let inner_floor : ℤ := Int.floor (r * n)
  (Int.floor (r * inner_floor.cast)).toNat

/-- A341254 Conjecture: $1/4 < n \cdot r^2 - a(n) < 3$ for $n \ge 1$. -/
theorem oeis_341254_conjecture_0 (n : ℕ) (hn : 1 ≤ n) :
  (1/4 : ℝ) < (n : ℝ) * r_sq - (a n : ℝ) ∧ (n : ℝ) * r_sq - (a n : ℝ) < 3 :=
by
  -- basic facts about √5
  have hs0 : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hlb : (2:ℝ) < Real.sqrt 5 := by nlinarith [hs2, hs0]
  have hub : Real.sqrt 5 < 5/2 := by nlinarith [hs2, hs0]
  -- facts about r_const
  have hr_pos : (0:ℝ) < r_const := by rw [r_const]; nlinarith [hlb]
  have hr_gt2 : (2:ℝ) < r_const := by rw [r_const]; linarith [hlb]
  have hr_lt : r_const < 9/4 := by rw [r_const]; linarith [hub]
  have hr2 : r_const * r_const = 2 * r_const + 1/4 := by
    rw [r_const]; linear_combination (1/4 : ℝ) * hs2
  have hrsq : r_sq = 2 * r_const + 1/4 := by rw [r_sq]; exact hr2
  -- n as a real
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by omega
  -- irrationality of r_const * n
  have h5irr : Irrational (Real.sqrt 5) := by
    have := Nat.Prime.irrational_sqrt (p := 5) (by norm_num)
    simpa using this
  have hirr : Irrational (r_const * (n:ℝ)) := by
    have h1 : Irrational (Real.sqrt 5 * (n:ℝ)) := h5irr.mul_natCast hn0
    have h2 : Irrational (Real.sqrt 5 * (n:ℝ) / 2) := h1.div_natCast (by norm_num)
    have h3 : Irrational (Real.sqrt 5 * (n:ℝ) / 2 + (n:ℝ)) := h2.add_natCast n
    have heq : r_const * (n:ℝ) = Real.sqrt 5 * (n:ℝ) / 2 + (n:ℝ) := by
      rw [r_const]; ring
    rwa [heq]
  -- abbreviations
  set m : ℤ := ⌊r_const * (n:ℝ)⌋ with hm_def
  set α : ℝ := Int.fract (r_const * (n:ℝ)) with hα_def
  have hα0 : (0:ℝ) ≤ α := Int.fract_nonneg _
  have hα1 : α < 1 := Int.fract_lt_one _
  have hMα : (m:ℝ) + α = r_const * (n:ℝ) := Int.floor_add_fract _
  -- α is strictly positive (r_const * n is irrational)
  have hαpos : 0 < α := by
    rcases lt_or_eq_of_le hα0 with h | h
    · exact h
    · exfalso
      have : r_const * (n:ℝ) = (m:ℝ) := by rw [← hMα, ← h]; ring
      exact hirr.ne_int m this
  -- m ≥ 2
  have hm2 : (2:ℤ) ≤ m := by
    rw [hm_def, Int.le_floor]
    push_cast
    nlinarith [hr_gt2, hn1, hr_pos]
  -- key identity: r_const * m = 2m + n/4 + (2 - r_const) α
  have key : r_const * (m:ℝ) = 2*(m:ℝ) + (n:ℝ)/4 + (2 - r_const)*α := by
    have hM : (m:ℝ) = r_const * (n:ℝ) - α := by linarith [hMα]
    rw [hM]
    linear_combination (n:ℝ) * hr2
  -- floor of r_const * m
  set K : ℤ := ⌊(n:ℝ)/4 + (2 - r_const)*α⌋ with hK_def
  have hfloor : ⌊r_const * (m:ℝ)⌋ = 2*m + K := by
    rw [key]
    have e : (2:ℝ)*(m:ℝ) + (n:ℝ)/4 + (2 - r_const)*α
        = ((n:ℝ)/4 + (2 - r_const)*α) + ((2*m : ℤ):ℝ) := by push_cast; ring
    rw [e, Int.floor_add_intCast, ← hK_def]
    ring
  -- r_const * m ≥ 0
  have hrM_nonneg : (0:ℝ) ≤ r_const * (m:ℝ) := by
    have hm2r : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
    nlinarith [hr_pos]
  have hfloor_nonneg : (0:ℤ) ≤ ⌊r_const * (m:ℝ)⌋ := Int.floor_nonneg.mpr hrM_nonneg
  -- value of a n
  have hnn : (0:ℤ) ≤ 2*m + K := by rw [← hfloor]; exact hfloor_nonneg
  have han : (a n : ℝ) = ((2*m + K : ℤ):ℝ) := by
    have h1 : a n = (⌊r_const * (m:ℝ)⌋).toNat := rfl
    rw [h1, hfloor]
    have h2 : (((2*m + K).toNat : ℤ)) = 2*m + K := Int.toNat_of_nonneg hnn
    exact_mod_cast h2
  -- main reduction: n * r_sq - a n = 2 α + (n/4 - K)
  have hmain : (n:ℝ) * r_sq - (a n:ℝ) = 2*α + ((n:ℝ)/4 - (K:ℝ)) := by
    rw [han, hrsq]
    push_cast
    have hM : (m:ℝ) = r_const * (n:ℝ) - α := by linarith [hMα]
    rw [hM]
    ring
  -- make the let-bound locals opaque to avoid heavy unfolding
  clear_value m α K
  -- bounds on (2 - r_const) * α
  have hc_ub : (2 - r_const)*α < 0 := mul_neg_of_neg_of_pos (by linarith [hr_gt2]) hαpos
  have hc_lb : -1/4 < (2 - r_const)*α := by nlinarith [hr_lt, hr_gt2, hα1, hαpos]
  -- helper: (n:ℝ) = 4 * (n/4) + (n%4)
  have hmod : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hqr : (n:ℝ) = 4 * ((n/4 : ℕ):ℝ) + ((n % 4 : ℕ):ℝ) := by
    exact_mod_cast (Nat.div_add_mod n 4).symm
  -- split n/4 + c using a natural-number cast
  have hsplit : (n:ℝ)/4 + (2 - r_const)*α
      = ((n/4:ℕ):ℝ) + (((n%4:ℕ):ℝ)/4 + (2 - r_const)*α) := by
    rw [hqr]; ring
  have hKint : K = (↑(n/4) : ℤ) + ⌊((n%4:ℕ):ℝ)/4 + (2 - r_const)*α⌋ := by
    rw [hK_def, hsplit, Int.floor_natCast_add]
  have hKr : (K:ℝ) = ((n/4:ℕ):ℝ)
      + (⌊((n%4:ℕ):ℝ)/4 + (2 - r_const)*α⌋ : ℝ) := by
    rw [hKint]; simp only [Int.cast_add, Int.cast_natCast]
  have hv : (n:ℝ)/4 - (K:ℝ)
      = ((n%4:ℕ):ℝ)/4 - (⌊((n%4:ℕ):ℝ)/4 + (2 - r_const)*α⌋ : ℝ) := by
    rw [hKr, hqr]; ring
  -- bound on v := n/4 - K
  have hvb : (1/4:ℝ) ≤ (n:ℝ)/4 - (K:ℝ) ∧ (n:ℝ)/4 - (K:ℝ) ≤ 1 := by
    rw [hv]
    rcases Nat.eq_zero_or_pos (n % 4) with h0 | hpos
    · have hnum : ((n%4:ℕ):ℝ) = 0 := by rw [h0]; norm_num
      have hF : ⌊((n%4:ℕ):ℝ)/4 + (2 - r_const)*α⌋ = -1 := by
        rw [Int.floor_eq_iff, hnum]
        refine ⟨?_, ?_⟩ <;> push_cast <;> linarith [hc_lb, hc_ub]
      rw [hF, hnum]; norm_num
    · have hs1 : (1:ℝ) ≤ ((n%4:ℕ):ℝ) := by exact_mod_cast hpos
      have hs3 : ((n%4:ℕ):ℝ) ≤ 3 := by
        have : n % 4 ≤ 3 := by omega
        exact_mod_cast this
      have hF : ⌊((n%4:ℕ):ℝ)/4 + (2 - r_const)*α⌋ = 0 := by
        rw [Int.floor_eq_iff]
        refine ⟨?_, ?_⟩ <;> push_cast <;> linarith [hc_lb, hc_ub, hs1, hs3]
      rw [hF]; push_cast
      constructor <;> linarith [hs1, hs3]
  -- conclude
  rw [hmain]
  refine ⟨?_, ?_⟩
  · linarith [hvb.1, hαpos]
  · linarith [hvb.2, hα1]
