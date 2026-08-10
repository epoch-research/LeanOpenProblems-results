import FormalConjectures.Util.ProblemImports
open BigOperators Nat Finset

def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

def T (n k : ℕ) : ℕ := (n.choose k)^2 * ((Nat.choose (n+k) k))^2

lemma choose_mod3_lucas1 (n k : ℕ) :
    n.choose k ≡ (n % 3).choose (k % 3) * (n / 3).choose (k / 3) [MOD 3] := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 3)

lemma zmod_choose_3m_3q_s (m q s : ℕ) (hs : s < 3) :
    ((3*m).choose (3*q+s) : ZMod 3) = (if s=0 then (m.choose q : ZMod 3) else 0) := by
  have h := choose_mod3_lucas1 (3*m) (3*q+s)
  have hm : (3*m) % 3 = 0 := by simp [Nat.mul_mod_right]
  have hdivm : (3*m) / 3 = m := by omega
  have hsmod : (3*q+s) % 3 = s := by omega
  have hsdiv : (3*q+s) / 3 = q := by omega
  rw [hm, hdivm, hsmod, hsdiv] at h
  apply (ZMod.natCast_eq_natCast_iff _ _ 3).2
  by_cases hsz : s = 0
  · simp [hsz] at h ⊢
    exact h
  · have hchoose0 : Nat.choose 0 s = 0 := by cases s <;> simp at hsz ⊢
    rw [hchoose0, zero_mul] at h
    rw [if_neg hsz]
    exact h

lemma zmod_choose_3sum (m q : ℕ) :
    ((3*m + 3*q).choose (3*q) : ZMod 3) = ((m+q).choose q : ZMod 3) := by
  have h := choose_mod3_lucas1 (3*m+3*q) (3*q)
  have hmodtop : (3*m+3*q) % 3 = 0 := by omega
  have hdivtop : (3*m+3*q) / 3 = m+q := by omega
  have hmodbot : (3*q) % 3 = 0 := by simp [Nat.mul_mod_right]
  have hdivbot : (3*q) / 3 = q := by omega
  rw [hmodtop, hdivtop, hmodbot, hdivbot] at h
  simp at h
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma zmod_T_3m_nondiv (m q s : ℕ) (hs : s < 3) (hs0 : s ≠ 0) :
    (T (3*m) (3*q+s) : ZMod 3) = 0 := by
  unfold T
  have h1 := zmod_choose_3m_3q_s m q s hs
  rw [h1]
  simp [hs0]

lemma zmod_T_3m_div (m q : ℕ) :
    (T (3*m) (3*q) : ZMod 3) = (T m q : ZMod 3) := by
  unfold T
  have h1 := zmod_choose_3m_3q_s m q 0 (by norm_num)
  have h2 := zmod_choose_3sum m q
  simp at h1
  rw [h1, h2]
  ring

lemma A3_eq_A_zmod (m : ℕ) : (A005259' (3*m) : ZMod 3) = (A005259' m : ZMod 3) := by
  induction m with
  | zero => native_decide
  | succ m ih =>
    unfold A005259'
    -- Need sum_range_succ grouping for 3m+3 and m+1
    rw [show 3*(m+1)+1 = (3*m+3)+1 by omega]
    rw [sum_range_succ]
    rw [sum_range_succ]
    rw [sum_range_succ]
    rw [show m+1+1 = (m+1)+1 by rfl]
    rw [sum_range_succ]
    change ((∑ x ∈ range (3 * m + 1), T (3*(m+1)) x) + T (3*(m+1)) (3*m+1) + T (3*(m+1)) (3*m+2) + T (3*(m+1)) (3*m+3) : ZMod 3)
      = ((∑ x ∈ range (m+1), T (m+1) x) + T (m+1) (m+1) : ZMod 3)
    sorry
