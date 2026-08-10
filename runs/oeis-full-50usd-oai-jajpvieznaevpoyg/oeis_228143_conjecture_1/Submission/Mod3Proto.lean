import FormalConjectures.Util.ProblemImports
open BigOperators Nat Finset
open scoped Nat

def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

#check Choose.choose_modEq_choose_mod_mul_choose_div_nat
lemma choose_mod3_lucas1 (n k : ℕ) :
    n.choose k ≡ (n % 3).choose (k % 3) * (n / 3).choose (k / 3) [MOD 3] := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 3)

lemma choose_3m_3q_s_mod3 (m q s : ℕ) (hs : s < 3) :
    (3*m).choose (3*q+s) ≡ (if s=0 then m.choose q else 0) [MOD 3] := by
  have h := choose_mod3_lucas1 (3*m) (3*q+s)
  have hm : (3*m) % 3 = 0 := by simp [Nat.mul_mod_right]
  have hdivm : (3*m) / 3 = m := by omega
  have hsmod : (3*q+s) % 3 = s := by omega
  have hsdiv : (3*q+s) / 3 = q := by omega
  rw [hm, hdivm, hsmod, hsdiv] at h
  by_cases hsz : s = 0
  · simp [hsz] at h ⊢
    exact h
  · have hspos : 0 < s := Nat.pos_of_ne_zero hsz
    have hchoose0 : Nat.choose 0 s = 0 := by cases s <;> simp at hsz ⊢
    rw [hchoose0, zero_mul] at h
    rw [if_neg hsz]
    exact h
