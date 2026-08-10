import FormalConjectures.Util.ProblemImports
open scoped Nat

-- (a+1) choose k * (a+1-k) = (a+1) * (a choose k)
theorem succ_choose_mul (a k : ℕ) :
    (a+1).choose k * (a+1-k) = (a+1) * a.choose k := by
  have h1 := Nat.choose_succ_right_eq (a+1) k     -- (a+1).choose(k+1)*(k+1)=(a+1).choose k*(a+1-k)
  have h2 := Nat.succ_mul_choose_eq a k           -- (a+1)*a.choose k = (a+1).choose(k+1)*(k+1)
  simp only [Nat.succ_eq_add_one] at h2
  omega

def b (n k : ℕ) : ℕ := (n-k).choose k

-- n-direction ratio identity
theorem b_ratio_n (n k : ℕ) (h : 2*k ≤ n) :
    b (n+1) k * (n+1-2*k) = (n+1-k) * b n k := by
  unfold b
  have hnk : n+1-k = (n-k)+1 := by omega
  rw [hnk]
  have := succ_choose_mul (n-k) k
  -- (n-k+1).choose k * (n-k+1-k) = (n-k+1)*(n-k).choose k
  have e1 : n-k+1-k = n+1-2*k := by omega
  rw [e1] at this
  linarith [this]

-- abstract k-direction identity in c,j
theorem b_ratio_k_abstract (c j : ℕ) :
    c.choose (j+1) * (c+1) * (j+1) = (c+1).choose j * (c+1-j) * (c-j) := by
  have h1 := Nat.choose_succ_right_eq c j   -- c.choose(j+1)*(j+1)=c.choose j*(c-j)
  have h2 := succ_choose_mul c j            -- (c+1).choose j*(c+1-j)=(c+1)*c.choose j
  nlinarith [h1, h2, Nat.zero_le (c.choose j), Nat.zero_le (c.choose (j+1))]

-- k-direction ratio identity for b
theorem b_ratio_k (n j : ℕ) (h : 2*j+1 ≤ n) :
    b n (j+1) * (n-j) * (j+1) = b n j * (n-2*j) * (n-2*j-1) := by
  have key := b_ratio_k_abstract (n-j-1) j
  have c1 : (n-j-1)+1 = n-j := by omega
  rw [c1] at key
  have c2 : n-j-j = n-2*j := by omega
  have c3 : n-j-1-j = n-2*j-1 := by omega
  rw [c2, c3] at key
  -- key : (n-j-1).choose (j+1) * (n-j) * (j+1) = (n-j).choose j * (n-2*j) * (n-2*j-1)
  unfold b
  have e1 : n - (j+1) = n-j-1 := by omega
  rw [e1]
  exact key
