import FormalConjectures.Util.ProblemImports

/--
A231830: $a(0) = 1$; for $n > 0$, $a(n) = 1 + 4 \cdot \prod_{i=1}^{n-1} a(i)^2$.
The recurrence relation for $n > 1$ is $a(n) = (a(n-1) - 1) \cdot a(n-1)^2 + 1$.
-/
def a : ℕ → ℕ
| 0 => 1
| 1 => 5
| n + 2 => (a (n + 1) - 1) * (a (n + 1))^2 + 1

/--
OEIS A231830 conjecture: Similarly to Sylvester's sequence (A000058), it is unknown if all terms are squarefree.
-/
lemma a_pos (n : ℕ) : 0 < a n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases n with _ | n
    · decide
    · rw [a]
      omega

lemma a_succ_succ (j : ℕ) : a (j + 2) = (a (j + 1) - 1) * (a (j + 1))^2 + 1 := rfl

lemma a_mod_eq (p : ℕ) (hp : Nat.Prime p) {k : ℕ} (h_dvd : p ∣ a k) (m : ℕ) :
    a (k + 1 + m) ≡ 1 [MOD p] := by
  induction m with
  | zero =>
    rcases k with _ | k
    · -- k = 0
      rw [a] at h_dvd
      have : p ∣ 1 := h_dvd
      exact (Nat.Prime.not_dvd_one hp this).elim
    · -- k = k + 1, so k + 1 + 0 = k + 2
      rw [a_succ_succ]
      -- We want (a (k + 1) - 1) * a (k + 1)^2 + 1 ≡ 1 [MOD p]
      -- Since p ∣ a (k + 1)
      have h_div : p ∣ (a (k + 1) - 1) * (a (k + 1))^2 := by
        apply dvd_mul_of_dvd_right
        rw [pow_two]
        exact dvd_mul_of_dvd_left h_dvd _
      exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr h_div)
  | succ m ih =>
    -- We want a (k + 1 + (m + 1)) ≡ 1 [MOD p]
    have h_assoc : k + 1 + (m + 1) = k + 1 + m + 1 := by omega
    rw [h_assoc]
    -- We want a (k + 1 + m + 1) ≡ 1 [MOD p]
    -- Since k + 1 + m + 1 = (k + 1 + m) + 1, and k + 1 + m >= 1
    -- Let j = k + m
    -- Then k + 1 + m + 1 = j + 2
    have h_eq : a (k + 1 + m + 1) = (a (k + 1 + m) - 1) * (a (k + 1 + m))^2 + 1 := by
      have : k + 1 + m + 1 = (k + m) + 2 := by omega
      rw [this, a_succ_succ]
      have : k + 1 + m = (k + m) + 1 := by omega
      rw [this]
    rw [h_eq]
    have ih_sub : a (k + 1 + m) - 1 ≡ 0 [MOD p] := by
      have h_sub_add : a (k + 1 + m) - 1 + 1 = a (k + 1 + m) := Nat.sub_add_cancel (a_pos (k + 1 + m))
      have h_eq2 : (a (k + 1 + m) - 1 + 1) ≡ (0 + 1) [MOD p] := by
        rw [h_sub_add]
        exact ih
      exact Nat.ModEq.add_right_cancel rfl h_eq2
    have h_div : p ∣ (a (k + 1 + m) - 1) * (a (k + 1 + m))^2 := by
      apply dvd_mul_of_dvd_left
      exact Nat.modEq_zero_iff_dvd.mp ih_sub
    exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr h_div)

lemma not_dvd_a_of_dvd_a {p : ℕ} (hp : Nat.Prime p) {n : ℕ} (hp_dvd : p ∣ a n) {k : ℕ} (hk : k < n) : ¬ p ∣ a k := by
  intro h_dvd
  let m := n - (k + 1)
  have h_eq_n : k + 1 + m = n := by omega
  have h_modeq := a_mod_eq p hp h_dvd m
  rw [h_eq_n] at h_modeq
  -- h_modeq : a n ≡ 1 [MOD p]
  -- but hp_dvd : p ∣ a n, so a n ≡ 0 [MOD p]
  have h_zero : a n ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hp_dvd
  have h_one_zero : 1 ≡ 0 [MOD p] := Nat.ModEq.trans h_modeq.symm h_zero
  have h_dvd_one : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp h_one_zero
  exact Nat.Prime.not_dvd_one hp h_dvd_one

lemma a_mod_eq_sq (p : ℕ) (hp : Nat.Prime p) {k : ℕ} (h_dvd : p ∣ a k) (m : ℕ) :
    a (k + 1 + m) ≡ 1 [MOD p^2] := by
  induction m with
  | zero =>
    rcases k with _ | k
    · -- k = 0
      rw [a] at h_dvd
      have : p ∣ 1 := h_dvd
      exact (Nat.Prime.not_dvd_one hp this).elim
    · -- k = k + 1, so k + 1 + 0 = k + 2
      rw [a_succ_succ]
      -- We want (a (k + 1) - 1) * a (k + 1)^2 + 1 ≡ 1 [MOD p^2]
      -- Since p ∣ a (k + 1)
      have h_div : p^2 ∣ (a (k + 1) - 1) * (a (k + 1))^2 := by
        apply dvd_mul_of_dvd_right
        rw [pow_two p, pow_two (a (k + 1))]
        exact mul_dvd_mul h_dvd h_dvd
      exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr h_div)
  | succ m ih =>
    -- We want a (k + 1 + (m + 1)) ≡ 1 [MOD p^2]
    have h_assoc : k + 1 + (m + 1) = k + 1 + m + 1 := by omega
    rw [h_assoc]
    have h_eq : a (k + 1 + m + 1) = (a (k + 1 + m) - 1) * (a (k + 1 + m))^2 + 1 := by
      have : k + 1 + m + 1 = (k + m) + 2 := by omega
      rw [this, a_succ_succ]
      have : k + 1 + m = (k + m) + 1 := by omega
      rw [this]
    rw [h_eq]
    have ih_sub : a (k + 1 + m) - 1 ≡ 0 [MOD p^2] := by
      have h_sub_add : a (k + 1 + m) - 1 + 1 = a (k + 1 + m) := Nat.sub_add_cancel (a_pos (k + 1 + m))
      have h_eq2 : (a (k + 1 + m) - 1 + 1) ≡ (0 + 1) [MOD p^2] := by
        rw [h_sub_add]
        exact ih
      exact Nat.ModEq.add_right_cancel rfl h_eq2
    have h_div : p^2 ∣ (a (k + 1 + m) - 1) * (a (k + 1 + m))^2 := by
      apply dvd_mul_of_dvd_left
      exact Nat.modEq_zero_iff_dvd.mp ih_sub
    exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr h_div)

lemma smallest_index_eq_n (p : ℕ) (hp : Nat.Prime p) {n : ℕ} (hp2_dvd : p^2 ∣ a n) :
    ∀ k < n, ¬ p ∣ a k := by
  intro k hk hp_dvd
  let m := n - (k + 1)
  have h_eq_n : k + 1 + m = n := by omega
  have h_modeq := a_mod_eq_sq p hp hp_dvd m
  rw [h_eq_n] at h_modeq
  -- h_modeq : a n ≡ 1 [MOD p^2]
  -- but hp2_dvd : p^2 ∣ a n, so a n ≡ 0 [MOD p^2]
  have h_zero : a n ≡ 0 [MOD p^2] := Nat.modEq_zero_iff_dvd.mpr hp2_dvd
  have h_one_zero : 1 ≡ 0 [MOD p^2] := Nat.ModEq.trans h_modeq.symm h_zero
  have h_dvd_one : p^2 ∣ 1 := Nat.modEq_zero_iff_dvd.mp h_one_zero
  have h_p_dvd_one : p ∣ 1 := dvd_trans ⟨p, by rw [pow_two]⟩ h_dvd_one
  exact Nat.Prime.not_dvd_one hp h_p_dvd_one

lemma smallest_index_sq_not_dvd (p : ℕ) (hp : Nat.Prime p) {n : ℕ}
    (h_smallest : ∀ k < n, ¬ p ∣ a k) (h_dvd : p ∣ a n) : ¬ p^2 ∣ a n := by
  intro hp2_dvd
  rcases n with _ | n
  · -- n = 0
    rw [a] at h_dvd
    have : p ∣ 1 := h_dvd
    exact Nat.Prime.not_dvd_one hp this
  · rcases n with _ | n
    · -- n = 1
      rw [a] at h_dvd
      have hp5 : p = 5 := by
        have h_dvd5 : p ∣ 5 := h_dvd
        have hp_five : Nat.Prime 5 := by decide
        rcases Nat.Prime.eq_one_or_self_of_dvd hp_five p h_dvd5 with hp1 | hp5
        · subst hp1
          exact (Nat.Prime.ne_one hp rfl).elim
        · exact hp5
      rw [hp5] at hp2_dvd
      rw [a] at hp2_dvd
      have h25_dvd_5 : 25 ∣ 5 := hp2_dvd
      contradiction
    · -- n = n + 2
      have h_not_dvd_sub : ¬ p ∣ (a (n + 1) - 1) := by
        intro hp_dvd_sub
        have h_modeq : a (n + 1) ≡ 1 [MOD p] := by
          have h_sub_add : a (n + 1) - 1 + 1 = a (n + 1) := Nat.sub_add_cancel (a_pos (n + 1))
          have h_eq2 : (a (n + 1) - 1 + 1) ≡ (0 + 1) [MOD p] := by
            exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr hp_dvd_sub)
          rw [h_sub_add] at h_eq2
          exact h_eq2
        have h_eq : a (n + 2) = (a (n + 1) - 1) * (a (n + 1))^2 + 1 := rfl
        have h_modeq2 : a (n + 2) ≡ 1 [MOD p] := by
          have h_div : p ∣ (a (n + 1) - 1) * (a (n + 1))^2 := dvd_mul_of_dvd_left hp_dvd_sub _
          exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr h_div)
        have h_zero : a (n + 2) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h_dvd
        have h_one_zero : 1 ≡ 0 [MOD p] := Nat.ModEq.trans h_modeq2.symm h_zero
        have h_dvd_one : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp h_one_zero
        exact Nat.Prime.not_dvd_one hp h_dvd_one
      have h_not_dvd_sub_sq : ¬ p^2 ∣ (a (n + 1) - 1) := by
        intro hp2_dvd_sub
        have h_modeq : a (n + 1) ≡ 1 [MOD p^2] := by
          have h_sub_add : a (n + 1) - 1 + 1 = a (n + 1) := Nat.sub_add_cancel (a_pos (n + 1))
          have h_eq2 : (a (n + 1) - 1 + 1) ≡ (0 + 1) [MOD p^2] := by
            exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr hp2_dvd_sub)
          rw [h_sub_add] at h_eq2
          exact h_eq2
        have h_eq : a (n + 2) = (a (n + 1) - 1) * (a (n + 1))^2 + 1 := rfl
        have h_modeq2 : a (n + 2) ≡ 1 [MOD p^2] := by
          have h_div : p^2 ∣ (a (n + 1) - 1) * (a (n + 1))^2 := dvd_mul_of_dvd_left hp2_dvd_sub _
          exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr h_div)
        have h_zero : a (n + 2) ≡ 0 [MOD p^2] := Nat.modEq_zero_iff_dvd.mpr hp2_dvd
        have h_one_zero : 1 ≡ 0 [MOD p^2] := Nat.ModEq.trans h_modeq2.symm h_zero
        have h_dvd_one : p^2 ∣ 1 := Nat.modEq_zero_iff_dvd.mp h_one_zero
        have h_p_dvd_one : p ∣ 1 := dvd_trans ⟨p, by rw [pow_two]⟩ h_dvd_one
        exact Nat.Prime.not_dvd_one hp h_p_dvd_one
      sorry


/--
OEIS A231830 conjecture: Similarly to Sylvester's sequence (A000058), it is unknown if all terms are squarefree.
-/
theorem oeis_231830_conjecture_0 : ∀ n : ℕ, Squarefree (a n) := by
  intro n
  rcases n with _ | _ | n
  · -- n = 0
    exact squarefree_one
  · -- n = 1
    have h : Nat.Prime 5 := by decide
    exact h.squarefree
  · -- n = n + 2
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2_dvd
    have hp2_dvd_sq : p^2 ∣ a (n + 2) := by rwa [pow_two]
    have h_smallest := smallest_index_eq_n p hp hp2_dvd_sq
    have h_dvd : p ∣ a (n + 2) := dvd_trans ⟨p, by rw [pow_two]⟩ hp2_dvd_sq
    have h_not_dvd : ¬ p^2 ∣ a (n + 2) := smallest_index_sq_not_dvd p hp h_smallest h_dvd
    exact h_not_dvd hp2_dvd_sq
