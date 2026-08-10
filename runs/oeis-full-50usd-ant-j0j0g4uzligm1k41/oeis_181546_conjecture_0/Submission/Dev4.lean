import FormalConjectures.Util.ProblemImports
open scoped Nat

noncomputable section

def b (n k : ℕ) : ℕ := (n-k).choose k

theorem succ_choose_mul (a k : ℕ) :
    (a+1).choose k * (a+1-k) = (a+1) * a.choose k := by
  have h1 := Nat.choose_succ_right_eq (a+1) k
  have h2 := Nat.succ_mul_choose_eq a k
  simp only [Nat.succ_eq_add_one] at h2
  omega

theorem b_ratio_k_abstract (c j : ℕ) :
    c.choose (j+1) * (c+1) * (j+1) = (c+1).choose j * (c+1-j) * (c-j) := by
  have h1 := Nat.choose_succ_right_eq c j
  have h2 := succ_choose_mul c j
  nlinarith [h1, h2, Nat.zero_le (c.choose j), Nat.zero_le (c.choose (j+1))]

theorem b_ratio_k (n j : ℕ) (h : 2*j+1 ≤ n) :
    b n (j+1) * (n-j) * (j+1) = b n j * (n-2*j) * (n-2*j-1) := by
  have key := b_ratio_k_abstract (n-j-1) j
  have c1 : (n-j-1)+1 = n-j := by omega
  rw [c1] at key
  have c2 : n-j-j = n-2*j := by omega
  have c3 : n-j-1-j = n-2*j-1 := by omega
  rw [c2, c3] at key
  unfold b
  have e1 : n - (j+1) = n-j-1 := by omega
  rw [e1]
  exact key

-- real cast of b_ratio_k
theorem b_ratio_k_real (n j : ℕ) (h : 2*j+1 ≤ n) :
    (b n (j+1) : ℝ) * ((n:ℝ)-j) * ((j:ℝ)+1) = (b n j : ℝ) * ((n:ℝ)-2*j) * ((n:ℝ)-2*j-1) := by
  have key := b_ratio_k n j h
  have hc1 : ((n - j : ℕ) : ℝ) = (n:ℝ) - j := by rw [Nat.cast_sub (by omega : j ≤ n)]
  have hc2 : ((n - 2*j : ℕ) : ℝ) = (n:ℝ) - 2*j := by
    rw [Nat.cast_sub (by omega : 2*j ≤ n)]; push_cast; ring
  have hc3 : ((n - 2*j - 1 : ℕ) : ℝ) = (n:ℝ) - 2*j - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - 2*j), hc2]; push_cast; ring
  have : ((b n (j+1) * (n-j) * (j+1) : ℕ) : ℝ) = ((b n j * (n-2*j) * (n-2*j-1) : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast at this
  rw [hc1, hc2, hc3] at this
  linarith [this]
