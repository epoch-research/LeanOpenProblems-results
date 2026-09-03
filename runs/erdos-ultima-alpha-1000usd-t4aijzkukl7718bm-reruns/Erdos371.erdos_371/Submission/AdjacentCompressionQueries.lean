import FormalConjecturesUtil
#check Nat.dvd_sub
#check Nat.Coprime.self_succ
#check Nat.coprime_self_add_one
#check Nat.coprime_self_add_right
#check Nat.coprime_add_self_right
#check Nat.coprime_add_self_left
#check Nat.coprime_add_one_right
#check Nat.coprime_one_right
example (m : ℕ) : m.Coprime (m+1) := by simp
