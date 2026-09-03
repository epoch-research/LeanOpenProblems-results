import FormalConjecturesUtil
#check Nat.le_self_pow
#check le_self_pow₀
#check Nat.le_mul_self
#check Nat.le_add_left
example (A K : ℕ) : K ≤ (A+K+1)^2 := by
  have h1 : K ≤ A+K+1 := by omega
  have h2 : A+K+1 ≤ (A+K+1)^2 := Nat.le_self_pow (by decide) _
  exact h1.trans h2
