import Submission.IntegerBlockExplore

/-! A binary high-block pattern transfers near-constant representation counts
through a fixed flat cyclic low pattern, with no error growing in the number
of high blocks. -/
namespace Erdos66BinaryBlockTransfer
open AdditiveCombinatorics Erdos66IntegerBlock
open scoped Classical
variable (M : ℕ) [NeZero M]

noncomputable def binaryBlocks (B : Finset (ZMod M)) (D : Set ℕ) : Set ℕ :=
  blockSet M (fun k ↦ if k ∈ D then B else ∅)

lemma binary_lower (B : Finset (ZMod M)) (D : Set ℕ) (i j t : ℕ) :
    lower M (if i ∈ D then B else ∅) (if j ∈ D then B else ∅) t =
      (if i ∈ D ∧ j ∈ D then 1 else 0) * lower M B B t := by
  by_cases hi : i ∈ D <;> by_cases hj : j ∈ D <;> simp [hi, hj, lower]

lemma binary_upper (B : Finset (ZMod M)) (D : Set ℕ) (i j t : ℕ) :
    upper M (if i ∈ D then B else ∅) (if j ∈ D then B else ∅) t =
      (if i ∈ D ∧ j ∈ D then 1 else 0) * upper M B B t := by
  by_cases hi : i ∈ D <;> by_cases hj : j ∈ D <;> simp [hi, hj, upper]

/-- The two consecutive high counts interpolate with nonnegative carry-fiber
weights whose sum is the original cyclic representation count. -/
theorem binary_block_formula (B : Finset (ZMod M)) (D : Set ℕ) (q t : ℕ)
    (hq : 0 < q) (ht : t < M) :
    sumRep (binaryBlocks M B D) (q * M + t) =
      sumRep D q * lower M B B t + sumRep D (q - 1) * upper M B B t := by
  rw [binaryBlocks, block_formula M _ q t ht]
  simp_rw [binary_lower, binary_upper]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← sumRep_range]
  congr 1
  congr 1
  rw [sumRep_range, show q - 1 + 1 = q by omega]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show q - k - 1 = q - 1 - k by omega]

lemma binary_block_formula_zero (B : Finset (ZMod M)) (D : Set ℕ) (t : ℕ) (ht : t < M) :
    sumRep (binaryBlocks M B D) t = (if 0 ∈ D then 1 else 0) * lower M B B t := by
  have hh := block_formula M (fun k ↦ if k ∈ D then B else ∅) 0 t ht
  simp only [Nat.zero_mul, Nat.zero_add, Finset.sum_range_one, Nat.sub_self, Finset.range_zero,
    Finset.sum_empty, Nat.add_zero] at hh
  rw [binary_lower] at hh
  simpa only [and_self, binaryBlocks] using hh

/-- A uniform bound on the high representation function gives a uniform bound
on the integer realization, including the first coarse block. -/
theorem binary_block_upper (B : Finset (ZMod M)) (D : Set ℕ) (β μ : ℝ)
    (hβ : 0 ≤ β) (hμ : 0 ≤ μ)
    (hB : ∀ z : ZMod M, ((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) ≤ β)
    (hD : ∀ n : ℕ, (sumRep D n : ℝ) ≤ μ) (n : ℕ) :
    (sumRep (binaryBlocks M B D) n : ℝ) ≤ β * μ := by
  let q := n / M
  let t := n % M
  have ht : t < M := Nat.mod_lt _ (NeZero.pos _)
  have heq : q * M + t = n := Nat.div_add_mod' _ _
  have hl0 : (0 : ℝ) ≤ lower M B B t := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ upper M B B t := Nat.cast_nonneg _
  have hlu : (lower M B B t : ℝ) + upper M B B t ≤ β := by
    have hh := hB (t : ZMod M)
    rw [← lower_add_upper M B B t] at hh
    exact_mod_cast hh
  by_cases hq : q = 0
  · have hn : n = t := by simpa only [hq, zero_mul, zero_add] using heq.symm
    rw [hn, binary_block_formula_zero M B D t ht]
    by_cases h0 : 0 ∈ D
    · simp only [if_pos h0, one_mul]
      have hh := hD 0
      have he : sumRep D 0 = 1 := by
        rw [sumRep_range]
        simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_self, h0, and_self, if_true]
      rw [he, Nat.cast_one] at hh
      nlinarith
    · simp only [if_neg h0, zero_mul, Nat.cast_zero]
      positivity
  · rw [← heq, binary_block_formula M B D q t (Nat.pos_of_ne_zero hq) ht]
    push_cast
    have h₁ := mul_le_mul_of_nonneg_right (hD q) hl0
    have h₂ := mul_le_mul_of_nonneg_right (hD (q - 1)) hu0
    have h₃ := mul_le_mul_of_nonneg_right hlu hμ
    nlinarith

/-- Relative cyclic and high-level errors combine multiplicatively, rather
than accumulating an absolute error for each coarse block. -/
theorem binary_block_error (B : Finset (ZMod M)) (D : Set ℕ) (β μ η ε : ℝ)
    (hβ : 0 ≤ β) (hμ : 0 ≤ μ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hB : ∀ z : ZMod M, |(((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - β)| ≤ η * β)
    (q t : ℕ) (hq : 0 < q) (ht : t < M)
    (hDq : |(sumRep D q : ℝ) - μ| ≤ ε * μ)
    (hDprev : |(sumRep D (q - 1) : ℝ) - μ| ≤ ε * μ) :
    |(sumRep (binaryBlocks M B D) (q * M + t) : ℝ) - β * μ| ≤
      β * μ * (η + ε + η * ε) := by
  let l : ℝ := lower M B B t
  let u : ℝ := upper M B B t
  have hl0 : 0 ≤ l := Nat.cast_nonneg _
  have hu0 : 0 ≤ u := Nat.cast_nonneg _
  have hcount : |l + u - β| ≤ η * β := by
    have hh := hB (t : ZMod M)
    rw [← lower_add_upper M B B t] at hh
    dsimp [l, u]
    exact_mod_cast hh
  have hmain : (sumRep (binaryBlocks M B D) (q * M + t) : ℝ) - β * μ =
      l * ((sumRep D q : ℝ) - μ) + u * ((sumRep D (q - 1) : ℝ) - μ) + (l + u - β) * μ := by
    rw [binary_block_formula M B D q t hq ht]
    dsimp [l, u]
    push_cast
    ring
  have h₁ : |l * ((sumRep D q : ℝ) - μ)| ≤ l * (ε * μ) := by
    rw [abs_mul, abs_of_nonneg hl0]
    exact mul_le_mul_of_nonneg_left hDq hl0
  have h₂ : |u * ((sumRep D (q - 1) : ℝ) - μ)| ≤ u * (ε * μ) := by
    rw [abs_mul, abs_of_nonneg hu0]
    exact mul_le_mul_of_nonneg_left hDprev hu0
  have h₃ : |(l + u - β) * μ| ≤ η * β * μ := by
    rw [abs_mul, abs_of_nonneg hμ]
    exact mul_le_mul_of_nonneg_right hcount hμ
  have hsumup := (abs_le.mp hcount).2
  have htotal := mul_le_mul_of_nonneg_right (show l + u ≤ β * (1 + η) by nlinarith)
    (mul_nonneg hε hμ)
  rw [hmain]
  calc
    _ ≤ |l * ((sumRep D q : ℝ) - μ)| + |u * ((sumRep D (q - 1) : ℝ) - μ)| +
        |(l + u - β) * μ| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ l * (ε * μ) + u * (ε * μ) + η * β * μ := add_le_add (add_le_add h₁ h₂) h₃
    _ ≤ _ := by nlinarith

end Erdos66BinaryBlockTransfer
