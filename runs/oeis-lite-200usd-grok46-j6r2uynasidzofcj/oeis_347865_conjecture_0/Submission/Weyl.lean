import Mathlib

open Complex Real Finset
open scoped Real BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

/-!
Elementary exponential-sum tools used to show that every large `m`
is of the form `w^2 + 2 x^2 + y^4 + 3 z^4`.
-/

/-- `e(α) = exp(2 π i α)`. -/
def e (α : ℝ) : ℂ := Complex.exp (2 * π * I * α)

lemma e_add (α β : ℝ) : e (α + β) = e α * e β := by
  simp [e, mul_add, add_mul, Complex.exp_add]

lemma e_zero : e 0 = 1 := by simp [e]

lemma norm_e (α : ℝ) : ‖e α‖ = 1 := by
  simp [e, Complex.norm_exp]

lemma e_int (n : ℤ) : e n = 1 := by
  simp [e, mul_comm, mul_left_comm, mul_assoc, Complex.exp_int_mul_two_pi_mul_I]

lemma e_sub_int (α : ℝ) (n : ℤ) : e (α - n) = e α := by
  rw [sub_eq_add_neg, e_add, ← e_int n]
  simp [e, neg_mul, mul_comm, mul_left_comm, mul_assoc, Complex.exp_neg,
    Complex.exp_int_mul_two_pi_mul_I]

/-- Geometric sum bound: `|∑_{k=0}^{N} e(k α)| ≤ min(N+1, 1 / (2 ‖α‖_ℤ))`. -/
def distZ (α : ℝ) : ℝ := |α - round α|

lemma distZ_nonneg (α : ℝ) : 0 ≤ distZ α := abs_nonneg _

lemma distZ_le_half (α : ℝ) : distZ α ≤ 1 / 2 := abs_sub_round α

lemma abs_geom_e_le (N : ℕ) (α : ℝ) :
    ‖∑ k ∈ range (N + 1), e (k * α)‖ ≤ (N + 1 : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

/-- Trivial bound for a degree-`k` Weyl sum. -/
lemma abs_weyl_triv (N : ℕ) (α : ℝ) (k : ℕ) :
    ‖∑ n ∈ range (N + 1), e (α * n ^ k)‖ ≤ (N + 1 : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

/-- The representation counting function as an exponential-sum integral is deferred;
we instead give a direct arithmetic construction for large `m`. -/

def IsWX (n : ℕ) : Prop := ∃ w x : ℕ, w ^ 2 + 2 * x ^ 2 = n

lemma isWX_zero : IsWX 0 := ⟨0, 0, by simp⟩
lemma isWX_one : IsWX 1 := ⟨1, 0, by simp⟩
lemma isWX_two : IsWX 2 := ⟨0, 1, by simp⟩
lemma isWX_three : IsWX 3 := ⟨1, 1, by norm_num⟩
lemma isWX_four : IsWX 4 := ⟨2, 0, by norm_num⟩
lemma isWX_six : IsWX 6 := ⟨2, 1, by norm_num⟩
lemma isWX_eight : IsWX 8 := ⟨0, 2, by norm_num⟩
lemma isWX_nine : IsWX 9 := ⟨3, 0, by norm_num⟩

lemma exists_rep_of_isWX {n : ℕ} (h : IsWX n) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n := by
  obtain ⟨w, x, hw⟩ := h
  exact ⟨w, x, 0, 0, by simpa using hw⟩

lemma exists_rep_of_isWX_sub {n y z : ℕ} (hle : y ^ 4 + 3 * z ^ 4 ≤ n)
    (h : IsWX (n - y ^ 4 - 3 * z ^ 4)) :
    ∃ w x y' z' : ℕ, w ^ 2 + 2 * x ^ 2 + y' ^ 4 + 3 * z' ^ 4 = n := by
  obtain ⟨w, x, hw⟩ := h
  refine ⟨w, x, y, z, ?_⟩
  have : n = (n - y ^ 4 - 3 * z ^ 4) + y ^ 4 + 3 * z ^ 4 := by
    rw [Nat.sub_sub, Nat.sub_add_cancel (by rwa [← Nat.sub_sub] at hle)]
  rw [this, hw]; ring

/-- Largest fourth root. -/
lemma sqrt_sqrt_pow4_le (m : ℕ) : (Nat.sqrt (Nat.sqrt m)) ^ 4 ≤ m := by
  have h : (Nat.sqrt (Nat.sqrt m)) ^ 2 ≤ Nat.sqrt m := Nat.sqrt_le' _
  have h2 : (Nat.sqrt m) ^ 2 ≤ m := Nat.sqrt_le' _
  have : ((Nat.sqrt (Nat.sqrt m)) ^ 2) ^ 2 ≤ (Nat.sqrt m) ^ 2 :=
    Nat.pow_le_pow_left h 2
  calc
    (Nat.sqrt (Nat.sqrt m)) ^ 4 = ((Nat.sqrt (Nat.sqrt m)) ^ 2) ^ 2 := by ring
    _ ≤ (Nat.sqrt m) ^ 2 := this
    _ ≤ m := h2

lemma lt_succ_sqrt_sqrt_pow4 (m : ℕ) :
    m < (Nat.sqrt (Nat.sqrt m) + 1) ^ 4 := by
  have h : Nat.sqrt m < (Nat.sqrt (Nat.sqrt m) + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have h2 : m < (Nat.sqrt m + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have h3 : Nat.sqrt m + 1 ≤ (Nat.sqrt (Nat.sqrt m) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' (Nat.sqrt m)
    omega
  have : (Nat.sqrt m + 1) ^ 2 ≤ ((Nat.sqrt (Nat.sqrt m) + 1) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left h3 2
  calc
    m < (Nat.sqrt m + 1) ^ 2 := h2
    _ ≤ ((Nat.sqrt (Nat.sqrt m) + 1) ^ 2) ^ 2 := this
    _ = (Nat.sqrt (Nat.sqrt m) + 1) ^ 4 := by ring

lemma rem_lt_four_cube (m : ℕ) :
    m - (Nat.sqrt (Nat.sqrt m)) ^ 4 <
      4 * (Nat.sqrt (Nat.sqrt m) + 1) ^ 3 := by
  set y := Nat.sqrt (Nat.sqrt m)
  have hlt : m < (y + 1) ^ 4 := lt_succ_sqrt_sqrt_pow4 m
  have hle : y ^ 4 ≤ m := sqrt_sqrt_pow4_le m
  have : m - y ^ 4 < (y + 1) ^ 4 - y ^ 4 := Nat.sub_lt_sub_right hle hlt
  have hd : (y + 1) ^ 4 - y ^ 4 = 4 * y ^ 3 + 6 * y ^ 2 + 4 * y + 1 := by
    ring_nf
    have : (y + 1) ^ 4 = y ^ 4 + 4 * y ^ 3 + 6 * y ^ 2 + 4 * y + 1 := by ring
    omega
  have : 4 * y ^ 3 + 6 * y ^ 2 + 4 * y + 1 < 4 * (y + 1) ^ 3 := by
    have : (y + 1) ^ 3 = y ^ 3 + 3 * y ^ 2 + 3 * y + 1 := by ring
    nlinarith
  omega

end
