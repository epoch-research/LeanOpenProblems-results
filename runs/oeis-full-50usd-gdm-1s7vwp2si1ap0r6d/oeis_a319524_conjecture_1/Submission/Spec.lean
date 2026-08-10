import FormalConjectures.Util.ProblemImports

open Nat

/--
A319524: $a(n)$ is the smallest number that belongs simultaneously to the two arithmetic progressions $\operatorname{prime}(n) + m \cdot \operatorname{prime}(n+1)$ and $\operatorname{prime}(n+1) + m' \cdot \operatorname{prime}(n+2)$, $m \ge 1, n \ge 1$.
Here, $\operatorname{prime}(k)$ denotes the $k$-th prime number, with $\operatorname{prime}(1)=2$.
-/
noncomputable def A319524 (n : ℕ) : ℕ :=
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k
  -- The $k$-th prime (1-indexed) is p(k-1).
  -- However, note that in Lean's Nat.nth Nat.Prime, the sequence is 2, 3, 5, ...
  -- prime(n) is the n-th prime in OEIS, which is (n-1)-th in the 0-indexed mathlib list.
  let Pn    := p (n - 1) -- Safe since ℕ subtraction is capped at 0
  let Pnp1  := p n
  let Pnp2  := p (n + 1)

  sInf { x : ℕ |
    -- x belongs to the first progression: prime(n) + m*prime(n+1), m >= 1
    -- and x belongs to the second progression: prime(n+1) + m'*prime(n+2), m' >= 1
    ∃ (m m' : ℕ),
      1 ≤ m ∧ 1 ≤ m' ∧
      x = Pn + m * Pnp1 ∧
      x = Pnp1 + m' * Pnp2
  }

theorem h_2 : Nat.Prime 2 := by decide
theorem hc_2 : count Nat.Prime 2 = 0 := by decide
theorem p_0 : nth Nat.Prime 0 = 2 := by
  have := nth_count h_2
  rw [hc_2] at this
  exact this

theorem h_3 : Nat.Prime 3 := by decide
theorem hc_3 : count Nat.Prime 3 = 1 := by decide
theorem p_1 : nth Nat.Prime 1 = 3 := by
  have := nth_count h_3
  rw [hc_3] at this
  exact this

theorem h_5 : Nat.Prime 5 := by decide
theorem hc_5 : count Nat.Prime 5 = 2 := by decide
theorem p_2 : nth Nat.Prime 2 = 5 := by
  have := nth_count h_5
  rw [hc_5] at this
  exact this

theorem h_7 : Nat.Prime 7 := by decide
theorem hc_7 : count Nat.Prime 7 = 3 := by decide
theorem p_3 : nth Nat.Prime 3 = 7 := by
  have := nth_count h_7
  rw [hc_7] at this
  exact this

theorem h_11 : Nat.Prime 11 := by decide
theorem hc_11 : count Nat.Prime 11 = 4 := by decide
theorem p_4 : nth Nat.Prime 4 = 11 := by
  have := nth_count h_11
  rw [hc_11] at this
  exact this

theorem h_13 : Nat.Prime 13 := by decide
theorem hc_13 : count Nat.Prime 13 = 5 := by decide
theorem p_5 : nth Nat.Prime 5 = 13 := by
  have := nth_count h_13
  rw [hc_13] at this
  exact this

theorem h_17 : Nat.Prime 17 := by decide
theorem hc_17 : count Nat.Prime 17 = 6 := by decide
theorem p_6 : nth Nat.Prime 6 = 17 := by
  have := nth_count h_17
  rw [hc_17] at this
  exact this

theorem h_19 : Nat.Prime 19 := by decide
theorem hc_19 : count Nat.Prime 19 = 7 := by decide
theorem p_7 : nth Nat.Prime 7 = 19 := by
  have := nth_count h_19
  rw [hc_19] at this
  exact this

theorem h_23 : Nat.Prime 23 := by decide
theorem hc_23 : count Nat.Prime 23 = 8 := by decide
theorem p_8 : nth Nat.Prime 8 = 23 := by
  have := nth_count h_23
  rw [hc_23] at this
  exact this

theorem h_29 : Nat.Prime 29 := by decide
theorem hc_29 : count Nat.Prime 29 = 9 := by decide
theorem p_9 : nth Nat.Prime 9 = 29 := by
  have := nth_count h_29
  rw [hc_29] at this
  exact this

theorem sInf_eq_of_mem_and_le {s : Set ℕ} {a : ℕ} (ha : a ∈ s) (hle : ∀ x ∈ s, a ≤ x) : sInf s = a := by
  have h_least : IsLeast s a := ⟨ha, hle⟩
  exact IsLeast.csInf_eq h_least

theorem a1_eq : A319524 1 = 8 := by
  dsimp [A319524]
  apply sInf_eq_of_mem_and_le
  · simp only [Set.mem_setOf_eq]
    use 2, 1
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [p_0, p_1]
    · rw [p_1, p_2]
  · rintro x ⟨m, m', hm, hm', hx1, hx2⟩
    rw [p_0, p_1] at hx1
    rw [p_1, p_2] at hx2
    omega

theorem a2_eq : A319524 2 = 33 := by
  dsimp [A319524]
  apply sInf_eq_of_mem_and_le
  · simp only [Set.mem_setOf_eq]
    use 6, 4
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [p_1, p_2]
    · rw [p_2, p_3]
  · rintro x ⟨m, m', hm, hm', hx1, hx2⟩
    rw [p_1, p_2] at hx1
    rw [p_2, p_3] at hx2
    omega

theorem a3_eq : A319524 3 = 40 := by
  dsimp [A319524]
  apply sInf_eq_of_mem_and_le
  · simp only [Set.mem_setOf_eq]
    use 5, 3
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [p_2, p_3]
    · rw [p_3, p_4]
  · rintro x ⟨m, m', hm, hm', hx1, hx2⟩
    rw [p_2, p_3] at hx1
    rw [p_3, p_4] at hx2
    omega

theorem a4_eq : A319524 4 = 128 := by
  dsimp [A319524]
  apply sInf_eq_of_mem_and_le
  · simp only [Set.mem_setOf_eq]
    use 11, 9
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [p_3, p_4]
    · rw [p_4, p_5]
  · rintro x ⟨m, m', hm, hm', hx1, hx2⟩
    rw [p_3, p_4] at hx1
    rw [p_4, p_5] at hx2
    omega

theorem a5_eq : A319524 5 = 115 := by
  dsimp [A319524]
  apply sInf_eq_of_mem_and_le
  · simp only [Set.mem_setOf_eq]
    use 8, 6
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [p_4, p_5]
    · rw [p_5, p_6]
  · rintro x ⟨m, m', hm, hm', hx1, hx2⟩
    rw [p_4, p_5] at hx1
    rw [p_5, p_6] at hx2
    omega

theorem a6_eq : A319524 6 = 302 := by
  dsimp [A319524]
  apply sInf_eq_of_mem_and_le
  · simp only [Set.mem_setOf_eq]
    use 17, 15
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [p_5, p_6]
    · rw [p_6, p_7]
  · rintro x ⟨m, m', hm, hm', hx1, hx2⟩
    rw [p_5, p_6] at hx1
    rw [p_6, p_7] at hx2
    omega

theorem a7_eq : A319524 7 = 226 := by
  dsimp [A319524]
  apply sInf_eq_of_mem_and_le
  · simp only [Set.mem_setOf_eq]
    use 11, 9
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [p_6, p_7]
    · rw [p_7, p_8]
  · rintro x ⟨m, m', hm, hm', hx1, hx2⟩
    rw [p_6, p_7] at hx1
    rw [p_7, p_8] at hx2
    omega

theorem a8_eq : A319524 8 = 226 := by
  dsimp [A319524]
  apply sInf_eq_of_mem_and_le
  · simp only [Set.mem_setOf_eq]
    use 9, 7
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [p_7, p_8]
    · rw [p_8, p_9]
  · rintro x ⟨m, m', hm, hm', hx1, hx2⟩
    rw [p_7, p_8] at hx1
    rw [p_8, p_9] at hx2
    omega


theorem S_nonempty (P1 P2 P3 : ℕ) (hP1_lt_P2 : P1 < P2) (hP2_lt_P3 : P2 < P3) (h_coprime : P2.Coprime P3) :
  { x : ℕ | ∃ m m', 1 ≤ m ∧ 1 ≤ m' ∧ x = P1 + m * P2 ∧ x = P2 + m' * P3 }.Nonempty := by
  rcases Nat.chineseRemainder h_coprime P1 P2 with ⟨k, hk1, hk2⟩
  let X := k + P2 * P3
  use X
  simp only [Set.mem_setOf_eq]
  have hP2_pos : 0 < P2 := by omega
  have hP3_pos : 0 < P3 := by omega
  have hX_mod_P2 : X % P2 = P1 := by
    have h_add_mod1 : X % P2 = k % P2 := by
      change (k + P2 * P3) % P2 = _
      rw [Nat.mul_comm, Nat.add_mul_mod_self_right k P3 P2]
    rw [h_add_mod1]
    have hk1_eq : k % P2 = P1 % P2 := hk1
    rw [hk1_eq]
    exact Nat.mod_eq_of_lt hP1_lt_P2

  have hX_mod_P3 : X % P3 = P2 := by
    have h_add_mod2 : X % P3 = k % P3 := by
      change (k + P2 * P3) % P3 = _
      rw [Nat.add_mul_mod_self_right k P2 P3]
    rw [h_add_mod2]
    have hk2_eq : k % P3 = P2 % P3 := hk2
    rw [hk2_eq]
    exact Nat.mod_eq_of_lt hP2_lt_P3

  let m := X / P2
  let m' := X / P3
  use m, m'
  have h_m : 1 ≤ m := by
    have h_div_le : P2 * P3 / P2 ≤ X / P2 := by
      have : P2 * P3 ≤ X := by dsimp [X]; omega
      exact Nat.div_le_div_right this
    have h_cancel : P2 * P3 / P2 = P3 := by
      rw [Nat.mul_comm, Nat.mul_div_cancel _ hP2_pos]
    rw [h_cancel] at h_div_le
    have : 1 ≤ P3 := by omega
    exact this.trans h_div_le
  have h_m' : 1 ≤ m' := by
    have h_div_le : P2 * P3 / P3 ≤ X / P3 := by
      have : P2 * P3 ≤ X := by dsimp [X]; omega
      exact Nat.div_le_div_right this
    have h_cancel : P2 * P3 / P3 = P2 := Nat.mul_div_cancel _ hP3_pos
    rw [h_cancel] at h_div_le
    have : 1 ≤ P2 := by omega
    exact this.trans h_div_le
  refine ⟨h_m, h_m', ?_, ?_⟩
  · have := Nat.mod_add_div X P2
    rw [hX_mod_P2] at this
    rw [Nat.mul_comm m]
    exact this.symm
  · have := Nat.mod_add_div X P3
    rw [hX_mod_P3] at this
    rw [Nat.mul_comm m']
    exact this.symm

theorem sInf_least {s : Set ℕ} (h : s.Nonempty) : IsLeast s (sInf s) :=
  ⟨Nat.sInf_mem h, fun _ hx ↦ Nat.sInf_le hx⟩

theorem algebraic_bound_parity (P1 P2 P3 P4 m m' k' : ℕ)
  (h1 : P1 + m * P2 = P2 + m' * P3)
  (h2 : P2 + m' * P3 = P3 + k' * P4)
  (hm : 1 ≤ m) (hm' : 1 ≤ m') (hk' : 1 ≤ k')
  (hP1 : P1 < P2) (hP2 : P2 < P3) (hP3 : P3 < P4)
  (hd1 : 2 ≤ P3 - P2) (hd2 : 2 ≤ P4 - P3)
  (h_m' : m' < P2)
  (hP2_odd : P2 % 2 = 1) (hP3_odd : P3 % 2 = 1) (hP4_odd : P4 % 2 = 1) :
  let d0 := P2 - P1
  let d1 := P3 - P2
  let d2 := P4 - P3
  2 * P2 ≤ d2 * d0 + d1 * (d2 - 2) * (d1 + d2) - d1^2 := by
  intro d0 d1 d2
  have h_P3 : P3 = P2 + d1 := by omega
  have h_E'_eq : (m - m') * P2 = m' * d1 + d0 := by
    have h_mP2 : m * P2 = m' * P3 + d0 := by omega
    rw [h_P3, Nat.mul_add] at h_mP2
    rw [Nat.sub_mul]
    omega
  have h_m'_sub : m' * P3 = (m' - 1) * P3 + P3 := by
    conv =>
      lhs
      rw [← Nat.sub_add_cancel hm']
    rw [Nat.add_mul, Nat.one_mul]
  have h2_sub_k' : P2 + (m' - 1) * P3 = k' * P4 := by
    omega
  have h_lt2 : P2 + (m' - 1) * P3 < m' * P4 := by
    calc P2 + (m' - 1) * P3 < P3 + (m' - 1) * P3 := Nat.add_lt_add_right hP2 _
    _ = m' * P3 := by omega
    _ < m' * P4 := Nat.mul_lt_mul_of_pos_left hP3 (by omega)
  have h_k'_lt : k' < m' := by
    have : k' * P4 < m' * P4 := by
      rw [← h2_sub_k']
      exact h_lt2
    exact Nat.lt_of_mul_lt_mul_right this

  have h_D'_eq : (m' - k') * P3 = k' * d2 + d1 := by
    have h_P4 : P4 = P3 + d2 := by omega
    have h_P2 : P2 = P3 - d1 := by omega
    have h2_sub : P2 + m' * P3 = P3 + (k' * P3 + k' * d2) := by
      calc P2 + m' * P3 = P3 + k' * P4 := h2
      _ = P3 + k' * (P3 + d2) := by rw [h_P4]
      _ = P3 + (k' * P3 + k' * d2) := by rw [Nat.mul_add]
    have h_sub_add : (m' - k') * P3 + k' * P3 = m' * P3 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    omega
  have h_alg_step : d1 * (m' - k') * P3 = d1 * (m' - k') * P2 + d1 * d1 * (m' - k') := by
    rw [h_P3]
    ring
  have h_exp1 : (d2 * (m - m') - d1 * (m' - k')) * P2 = d2 * ((m - m') * P2) - d1 * (m' - k') * P2 := by
    rw [Nat.sub_mul, ← Nat.mul_assoc]
  have h_alg_step' : d1 * ((m' - k') * P3) = d1 * ((m' - k') * P2) + d1 * d1 * (m' - k') := by
    rw [← Nat.mul_assoc, h_alg_step, Nat.mul_assoc]
  have h_subst1 : d1 * ((m' - k') * P3) = d1 * (k' * d2 + d1) := by
    rw [h_D'_eq]
  have h_exp1' : (d2 * (m - m') - d1 * (m' - k')) * P2 = d2 * ((m - m') * P2) - d1 * ((m' - k') * P2) := by
    rw [Nat.sub_mul, ← Nat.mul_assoc, Nat.mul_assoc d1]
  have h_goal_rewrite : d2 * d0 + d1 * (d1 + d2) * (m' - k') = d2 * d0 + d1 * d1 * (m' - k') + d2 * (m' - k') * d1 := by
    ring
  have h_subst1' : d1 * ((m' - k') * P3) = d1 * k' * d2 + d1 * d1 := by
    rw [h_subst1, Nat.mul_add, ← Nat.mul_assoc]
  have h_m'_eq : m' = k' + (m' - k') := by omega
  have h_prod_eq : d2 * m' * d1 = d1 * k' * d2 + d2 * (m' - k') * d1 := by
    calc d2 * m' * d1 = d2 * (k' + (m' - k')) * d1 := by nth_rw 1 [h_m'_eq]
    _ = (d2 * k' + d2 * (m' - k')) * d1 := by rw [Nat.mul_add]
    _ = d2 * k' * d1 + d2 * (m' - k') * d1 := by rw [Nat.add_mul]
    _ = d1 * k' * d2 + d2 * (m' - k') * d1 := by ring
  have h_E'_subst' : d2 * ((m - m') * P2) = d2 * m' * d1 + d2 * d0 := by
    rw [h_E'_eq, Nat.mul_add, ← Nat.mul_assoc]
  have h_E'_subst'' : d2 * ((m - m') * P2) = d1 * k' * d2 + d2 * (m' - k') * d1 + d2 * d0 := by
    rw [h_E'_subst', h_prod_eq]
  have h_alg_comb : d2 * ((m - m') * P2) + d1 * d1 = d2 * d0 + d1 * d1 * (m' - k') + d2 * (m' - k') * d1 + d1 * ((m' - k') * P2) := by
    omega
  have h_D'_le : m' - k' ≤ d2 - 2 := by
    have h_k'_le : k' * d2 + d1 < P3 * d2 := by
      have : d1 < (d1 + 2) * d2 := by
        calc d1 < d1 + 2 := by omega
        _ ≤ (d1 + 2) * 2 := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ (d1 + 2) * d2 := Nat.mul_le_mul_left (d1 + 2) hd2
      calc k' * d2 + d1 < k' * d2 + (d1 + 2) * d2 := Nat.add_lt_add_left this _
      _ = (k' + d1 + 2) * d2 := by ring
      _ ≤ P3 * d2 := by
        gcongr
        omega
    have h_lt : (m' - k') * P3 < d2 * P3 := by
      rw [h_D'_eq]
      have : k' * d2 = d2 * k' := Nat.mul_comm _ _
      have : P3 * d2 = d2 * P3 := Nat.mul_comm _ _
      omega
    have : m' - k' < d2 := Nat.lt_of_mul_lt_mul_right h_lt
    have h_le1 : m' - k' ≤ d2 - 1 := by omega
    have hd2_even : d2 % 2 = 0 := by omega
    have hd1_even : d1 % 2 = 0 := by omega
    have h_D_even : (m' - k') % 2 = 0 := by
      have h_eq_D : (m' - k') * P3 = k' * d2 + d1 := h_D'_eq
      have h_rhs_even : (k' * d2 + d1) % 2 = 0 := by
        rw [Nat.add_mod, Nat.mul_mod, hd2_even, hd1_even]
        simp
      have h_lhs_even : ((m' - k') * P3) % 2 = 0 := by
        rw [h_eq_D]
        exact h_rhs_even
      have h_mul : (m' - k') * P3 % 2 = ((m' - k') % 2 * (P3 % 2)) % 2 := Nat.mul_mod (m' - k') P3 2
      rw [hP3_odd] at h_mul
      rw [h_lhs_even] at h_mul
      have : (m' - k') % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    omega

  have h_le_mul : d1 * d1 ≤ d1 * d1 * (m' - k') := by
    have h_D'_pos : 1 ≤ m' - k' := by omega
    have := Nat.mul_le_mul_left (d1 * d1) h_D'_pos
    rw [Nat.mul_one] at this
    exact this
  have h_pos : 0 < d2 * d0 := Nat.mul_pos (by omega : 0 < d2) (by omega : 0 < d0)
  have h_ineq2 : d1 * ((m' - k') * P2) < d2 * ((m - m') * P2) := by
    omega

  have h_ineq3 : d1 * (m' - k') < d2 * (m - m') := by
    have h_assoc1 : d1 * ((m' - k') * P2) = (d1 * (m' - k')) * P2 := by ring
    have h_assoc2 : d2 * ((m - m') * P2) = (d2 * (m - m')) * P2 := by ring
    have h_ineq2' : (d1 * (m' - k')) * P2 < (d2 * (m - m')) * P2 := by
      rw [← h_assoc1, ← h_assoc2]
      exact h_ineq2
    exact Nat.lt_of_mul_lt_mul_right h_ineq2'

  have h_F'_ge1 : 1 ≤ d2 * (m - m') - d1 * (m' - k') := by omega

  have h_F'_ge2 : 2 ≤ d2 * (m - m') - d1 * (m' - k') := by
    let F := d2 * (m - m') - d1 * (m' - k')
    have hd1_even : d1 % 2 = 0 := by omega
    have hd2_even : d2 % 2 = 0 := by omega
    have hd2_eq : d2 = 2 * (d2 / 2) := by omega
    have hd1_eq : d1 = 2 * (d1 / 2) := by omega
    have hF_eq : F = 2 * ((d2 / 2) * (m - m')) - 2 * ((d1 / 2) * (m' - k')) := by
      calc F = d2 * (m - m') - d1 * (m' - k') := rfl
      _ = (2 * (d2 / 2)) * (m - m') - (2 * (d1 / 2)) * (m' - k') := by rw [← hd2_eq, ← hd1_eq]
      _ = 2 * ((d2 / 2) * (m - m')) - 2 * ((d1 / 2) * (m' - k')) := by rw [Nat.mul_assoc, Nat.mul_assoc]
    omega

  have h_final : 2 * P2 + d1 * d1 ≤ d2 * d0 + d1 * (d2 - 2) * (d1 + d2) := by
    have h_2P2_le : 2 * P2 ≤ (d2 * (m - m') - d1 * (m' - k')) * P2 := by
      calc 2 * P2 = 2 * P2 := rfl
      _ ≤ (d2 * (m - m') - d1 * (m' - k')) * P2 := Nat.mul_le_mul_right P2 h_F'_ge2
    have h_comb : (d2 * (m - m') - d1 * (m' - k')) * P2 + d1 * d1 = d2 * d0 + d1 * (d1 + d2) * (m' - k') := by
      rw [h_exp1', h_goal_rewrite]
      omega
    have h_le_RHS : d2 * d0 + d1 * (d1 + d2) * (m' - k') ≤ d2 * d0 + d1 * (d2 - 2) * (d1 + d2) := by
      have h_le_D' : d1 * (d1 + d2) * (m' - k') ≤ d1 * (d1 + d2) * (d2 - 2) := by
        gcongr
      have h_comm : d1 * (d1 + d2) * (d2 - 2) = d1 * (d2 - 2) * (d1 + d2) := by ring
      omega
    omega

  have h_goal_rewrite' : 2 * P2 ≤ d2 * d0 + d1 * (d2 - 2) * (d1 + d2) - d1^2 := by
    rw [show d1^2 = d1 * d1 by ring]
    omega
  exact h_goal_rewrite'
theorem m'_lt_P2 (P1 P2 P3 m m' : ℕ) (X : ℕ)
  (hP1 : 0 < P1) (hP2 : 0 < P2) (hP3 : 0 < P3) (hP1_lt_P2 : P1 < P2)
  (hX_least : IsLeast { x : ℕ | ∃ m m', 1 ≤ m ∧ 1 ≤ m' ∧ x = P1 + m * P2 ∧ x = P2 + m' * P3 } X)
  (hm : 1 ≤ m) (hm' : 1 ≤ m') (hX1 : X = P1 + m * P2) (hX2 : X = P2 + m' * P3) :
  m' < P2 := by
  by_contra h_ge
  push_neg at h_ge
  -- Since P2 ≤ m'
  have h_m'_ne_P2 : m' ≠ P2 := by
    intro h_eq
    have h_X : X = P2 + P2 * P3 := by
      rw [h_eq] at hX2
      exact hX2
    have h_div : P1 = P2 * (1 + P3 - m) := by
      have hX1_eq : P1 + m * P2 = P2 + P2 * P3 := by
        rw [← hX1, h_X]
      have hX1_eq' : P1 + m * P2 = P2 * (1 + P3) := by
        calc P1 + m * P2 = P2 + P2 * P3 := hX1_eq
        _ = P2 * 1 + P2 * P3 := by rw [Nat.mul_one]
        _ = P2 * (1 + P3) := by rw [Nat.mul_add]
      have h_m_le : m ≤ 1 + P3 := by
        have h_m_mul : m * P2 ≤ (1 + P3) * P2 := by
          calc m * P2 ≤ P1 + m * P2 := Nat.le_add_left _ _
          _ = P2 * (1 + P3) := hX1_eq'
          _ = (1 + P3) * P2 := Nat.mul_comm _ _
        exact Nat.le_of_mul_le_mul_right h_m_mul hP2
      have hX1_eq'' : P1 + m * P2 = (1 + P3) * P2 := by
        rw [hX1_eq', Nat.mul_comm]
      have h_sub : (1 + P3) * P2 - m * P2 = P2 * (1 + P3 - m) := by
        rw [← Nat.sub_mul, Nat.mul_comm]
      have h_P1_eq : P1 = (1 + P3) * P2 - m * P2 := by omega
      rw [h_sub] at h_P1_eq
      exact h_P1_eq
    rcases lt_or_ge (1 + P3) m with h_lt | h_ge_m
    · have h_z : 1 + P3 - m = 0 := by omega
      have : P1 = 0 := by
        rw [h_div, h_z, Nat.mul_zero]
      omega
    · have h_nz : 1 + P3 - m ≠ 0 := by
        intro h_z
        have : P1 = 0 := by
          rw [h_div, h_z, Nat.mul_zero]
        omega
      have h_ge1 : 1 + P3 - m ≥ 1 := by omega
      have h_ge_P2 : P2 * (1 + P3 - m) ≥ P2 := by
        calc P2 * (1 + P3 - m) ≥ P2 * 1 := Nat.mul_le_mul_left P2 h_ge1
        _ = P2 := Nat.mul_one P2
      omega
  have h_m'_ge : P2 + 1 ≤ m' := by omega
  let m_new' := m' - P2
  let m_new := m - P3
  have hm_new' : 1 ≤ m_new' := by omega
  have h_mul_le : (P2 + 1) * P3 ≤ m' * P3 := Nat.mul_le_mul_right P3 h_m'_ge
  have h_rew : (P2 + 1) * P3 = P2 * P3 + P3 := by ring
  have hm_new : 1 ≤ m_new := by
    have h_ineq : P1 + m * P2 ≥ P2 + P2 * P3 + P3 := by
      calc P1 + m * P2 = X := hX1.symm
      _ = P2 + m' * P3 := hX2
      _ ≥ P2 + (P2 + 1) * P3 := by omega
      _ = P2 + P2 * P3 + P3 := by rw [h_rew]; omega
    have : m * P2 > P3 * P2 := by
      have : P2 * P3 = P3 * P2 := Nat.mul_comm P2 P3
      omega
    have : m > P3 := Nat.lt_of_mul_lt_mul_right this
    omega
  let X_new := P2 + m_new' * P3
  have h_add1 : X_new + P2 * P3 = X := by
    calc X_new + P2 * P3 = P2 + (m' - P2) * P3 + P2 * P3 := rfl
    _ = P2 + ((m' - P2) * P3 + P2 * P3) := by omega
    _ = P2 + (m' - P2 + P2) * P3 := by rw [← Nat.add_mul]
    _ = P2 + m' * P3 := by
      rw [Nat.sub_add_cancel (by omega : P2 ≤ m')]
    _ = X := hX2.symm
  have h_add2 : P1 + m_new * P2 + P3 * P2 = X := by
    calc P1 + m_new * P2 + P3 * P2 = P1 + (m_new * P2 + P3 * P2) := by omega
    _ = P1 + (m_new + P3) * P2 := by rw [← Nat.add_mul]
    _ = P1 + m * P2 := by
      have h_cancel : m_new + P3 = m := Nat.sub_add_cancel (by omega : P3 ≤ m)
      rw [h_cancel]
    _ = X := hX1.symm
  have h_X_new_eq : X_new = P1 + m_new * P2 := by
    have h_comm : P2 * P3 = P3 * P2 := Nat.mul_comm P2 P3
    omega
  have h_mem : X_new ∈ { x : ℕ | ∃ m m', 1 ≤ m ∧ 1 ≤ m' ∧ x = P1 + m * P2 ∧ x = P2 + m' * P3 } := by
    simp only [Set.mem_setOf_eq]
    exact ⟨m_new, m_new', hm_new, hm_new', h_X_new_eq, rfl⟩
  have h_le := hX_least.2 h_mem
  have h_X_new_lt : X_new < X := by
    have : P2 * P3 > 0 := Nat.mul_pos hP2 hP3
    omega
  omega


set_option maxHeartbeats 1000000


theorem no_sol_y_9 (m m' k' : ℕ)
  (h1 : 23 + m * 29 = 29 + m' * 31)
  (h2 : 29 + m' * 31 = 31 + k' * 37)
  (hm' : m' < 29) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 29 ≤ m' * 29 := Nat.mul_le_mul_right 29 h_le
    have h_le_mul2 : m' * 29 ≤ m' * 31 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 23 + m * 29 ≤ 23 + m' * 29 := Nat.add_le_add_left h_le_mul 23
    have h_step2 : 23 + m' * 29 ≤ 23 + m' * 31 := Nat.add_le_add_left h_le_mul2 23
    have h_step3 : 23 + m' * 31 < 29 + m' * 31 := Nat.add_lt_add_right (by decide : 23 < 29) _
    have h_lt : 23 + m * 29 < 29 + m' * 31 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 29 = 2 * m' + 6 := by
    have h_eq : m * 29 = m' * 29 + D * 29 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 31 = m' * 29 + 2 * m' := by
      rw [show 31 = 29 + 2 by decide, Nat.mul_add, Nat.mul_comm m' 2]
    rw [h_dist] at h1'
    have h1_assoc : (23 + D * 29) + m' * 29 = (29 + 2 * m') + m' * 29 := by
      calc (23 + D * 29) + m' * 29 = 23 + (D * 29 + m' * 29) := by rw [Nat.add_assoc]
      _ = 23 + (m' * 29 + D * 29) := by rw [Nat.add_comm (D * 29)]
      _ = 29 + (m' * 29 + 2 * m') := h1'
      _ = 29 + (2 * m' + m' * 29) := by rw [Nat.add_comm (m' * 29)]
      _ = (29 + 2 * m') + m' * 29 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 23 + D * 29 = 23 + (2 * m' + 6) := by
      calc 23 + D * 29 = (23 + D * 29) := rfl
      _ = 29 + 2 * m' := h1_sub
      _ = 23 + 6 + 2 * m' := rfl
      _ = 23 + (6 + 2 * m') := by rw [Nat.add_assoc]
      _ = 23 + (2 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 2 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 29 ≥ 3 * 29 := Nat.mul_le_mul_right 29 h_gt
    have h2 : 2 * m' + 6 < 3 * 29 := by
      have : 2 * m' < 2 * 29 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 2 * m' + 6 < 2 * 29 + 6 := Nat.add_lt_add_right this 6
      calc 2 * m' + 6 < 2 * 29 + 6 := this
      _ ≤ 3 * 29 := by decide
    have h_lt : 3 * 29 < 3 * 29 := by
      calc 3 * 29 ≤ D * 29 := h1
      _ = 2 * m' + 6 := h_alg
      _ < 3 * 29 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl
    · revert h_alg; omega
    · rfl
  have hm'_eq : m' = 26 := by
    have h_alg_sol : 2 * 29 = 2 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 2 * 29 = 58 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 52 = 2 * m' := by
      calc 52 = 58 - 6 := rfl
      _ = 2 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 2 * m' := rfl
    have h_div : 52 / 2 = (2 * m') / 2 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 2)] at h_div
    have h_div_eval : 52 / 2 = 26 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_10 (m m' k' : ℕ)
  (h1 : 29 + m * 31 = 31 + m' * 37)
  (h2 : 31 + m' * 37 = 37 + k' * 41)
  (hm' : m' < 31) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 31 ≤ m' * 31 := Nat.mul_le_mul_right 31 h_le
    have h_le_mul2 : m' * 31 ≤ m' * 37 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 29 + m * 31 ≤ 29 + m' * 31 := Nat.add_le_add_left h_le_mul 29
    have h_step2 : 29 + m' * 31 ≤ 29 + m' * 37 := Nat.add_le_add_left h_le_mul2 29
    have h_step3 : 29 + m' * 37 < 31 + m' * 37 := Nat.add_lt_add_right (by decide : 29 < 31) _
    have h_lt : 29 + m * 31 < 31 + m' * 37 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 31 = 6 * m' + 2 := by
    have h_eq : m * 31 = m' * 31 + D * 31 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 37 = m' * 31 + 6 * m' := by
      rw [show 37 = 31 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (29 + D * 31) + m' * 31 = (31 + 6 * m') + m' * 31 := by
      calc (29 + D * 31) + m' * 31 = 29 + (D * 31 + m' * 31) := by rw [Nat.add_assoc]
      _ = 29 + (m' * 31 + D * 31) := by rw [Nat.add_comm (D * 31)]
      _ = 31 + (m' * 31 + 6 * m') := h1'
      _ = 31 + (6 * m' + m' * 31) := by rw [Nat.add_comm (m' * 31)]
      _ = (31 + 6 * m') + m' * 31 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 29 + D * 31 = 29 + (6 * m' + 2) := by
      calc 29 + D * 31 = (29 + D * 31) := rfl
      _ = 31 + 6 * m' := h1_sub
      _ = 29 + 2 + 6 * m' := rfl
      _ = 29 + (2 + 6 * m') := by rw [Nat.add_assoc]
      _ = 29 + (6 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 31 ≥ 7 * 31 := Nat.mul_le_mul_right 31 h_gt
    have h2 : 6 * m' + 2 < 7 * 31 := by
      have : 6 * m' < 6 * 31 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 2 < 6 * 31 + 2 := Nat.add_lt_add_right this 2
      calc 6 * m' + 2 < 6 * 31 + 2 := this
      _ ≤ 7 * 31 := by decide
    have h_lt : 7 * 31 < 7 * 31 := by
      calc 7 * 31 ≤ D * 31 := h1
      _ = 6 * m' + 2 := h_alg
      _ < 7 * 31 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 10 := by
    have h_alg_sol : 2 * 31 = 6 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 31 = 62 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 60 = 6 * m' := by
      calc 60 = 62 - 2 := rfl
      _ = 6 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 60 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 60 / 6 = 10 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_13 (m m' k' : ℕ)
  (h1 : 41 + m * 43 = 43 + m' * 47)
  (h2 : 43 + m' * 47 = 47 + k' * 53)
  (hm' : m' < 43) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 43 ≤ m' * 43 := Nat.mul_le_mul_right 43 h_le
    have h_le_mul2 : m' * 43 ≤ m' * 47 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 41 + m * 43 ≤ 41 + m' * 43 := Nat.add_le_add_left h_le_mul 41
    have h_step2 : 41 + m' * 43 ≤ 41 + m' * 47 := Nat.add_le_add_left h_le_mul2 41
    have h_step3 : 41 + m' * 47 < 43 + m' * 47 := Nat.add_lt_add_right (by decide : 41 < 43) _
    have h_lt : 41 + m * 43 < 43 + m' * 47 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 43 = 4 * m' + 2 := by
    have h_eq : m * 43 = m' * 43 + D * 43 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 47 = m' * 43 + 4 * m' := by
      rw [show 47 = 43 + 4 by decide, Nat.mul_add, Nat.mul_comm m' 4]
    rw [h_dist] at h1'
    have h1_assoc : (41 + D * 43) + m' * 43 = (43 + 4 * m') + m' * 43 := by
      calc (41 + D * 43) + m' * 43 = 41 + (D * 43 + m' * 43) := by rw [Nat.add_assoc]
      _ = 41 + (m' * 43 + D * 43) := by rw [Nat.add_comm (D * 43)]
      _ = 43 + (m' * 43 + 4 * m') := h1'
      _ = 43 + (4 * m' + m' * 43) := by rw [Nat.add_comm (m' * 43)]
      _ = (43 + 4 * m') + m' * 43 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 41 + D * 43 = 41 + (4 * m' + 2) := by
      calc 41 + D * 43 = (41 + D * 43) := rfl
      _ = 43 + 4 * m' := h1_sub
      _ = 41 + 2 + 4 * m' := rfl
      _ = 41 + (2 + 4 * m') := by rw [Nat.add_assoc]
      _ = 41 + (4 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 4 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 43 ≥ 5 * 43 := Nat.mul_le_mul_right 43 h_gt
    have h2 : 4 * m' + 2 < 5 * 43 := by
      have : 4 * m' < 4 * 43 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 4 * m' + 2 < 4 * 43 + 2 := Nat.add_lt_add_right this 2
      calc 4 * m' + 2 < 4 * 43 + 2 := this
      _ ≤ 5 * 43 := by decide
    have h_lt : 5 * 43 < 5 * 43 := by
      calc 5 * 43 ≤ D * 43 := h1
      _ = 4 * m' + 2 := h_alg
      _ < 5 * 43 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 21 := by
    have h_alg_sol : 2 * 43 = 4 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 43 = 86 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 84 = 4 * m' := by
      calc 84 = 86 - 2 := rfl
      _ = 4 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 4 * m' := rfl
    have h_div : 84 / 4 = (4 * m') / 4 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 4)] at h_div
    have h_div_eval : 84 / 4 = 21 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_14 (m m' k' : ℕ)
  (h1 : 43 + m * 47 = 47 + m' * 53)
  (h2 : 47 + m' * 53 = 53 + k' * 59)
  (hm' : m' < 47) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 47 ≤ m' * 47 := Nat.mul_le_mul_right 47 h_le
    have h_le_mul2 : m' * 47 ≤ m' * 53 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 43 + m * 47 ≤ 43 + m' * 47 := Nat.add_le_add_left h_le_mul 43
    have h_step2 : 43 + m' * 47 ≤ 43 + m' * 53 := Nat.add_le_add_left h_le_mul2 43
    have h_step3 : 43 + m' * 53 < 47 + m' * 53 := Nat.add_lt_add_right (by decide : 43 < 47) _
    have h_lt : 43 + m * 47 < 47 + m' * 53 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 47 = 6 * m' + 4 := by
    have h_eq : m * 47 = m' * 47 + D * 47 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 53 = m' * 47 + 6 * m' := by
      rw [show 53 = 47 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (43 + D * 47) + m' * 47 = (47 + 6 * m') + m' * 47 := by
      calc (43 + D * 47) + m' * 47 = 43 + (D * 47 + m' * 47) := by rw [Nat.add_assoc]
      _ = 43 + (m' * 47 + D * 47) := by rw [Nat.add_comm (D * 47)]
      _ = 47 + (m' * 47 + 6 * m') := h1'
      _ = 47 + (6 * m' + m' * 47) := by rw [Nat.add_comm (m' * 47)]
      _ = (47 + 6 * m') + m' * 47 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 43 + D * 47 = 43 + (6 * m' + 4) := by
      calc 43 + D * 47 = (43 + D * 47) := rfl
      _ = 47 + 6 * m' := h1_sub
      _ = 43 + 4 + 6 * m' := rfl
      _ = 43 + (4 + 6 * m') := by rw [Nat.add_assoc]
      _ = 43 + (6 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 47 ≥ 7 * 47 := Nat.mul_le_mul_right 47 h_gt
    have h2 : 6 * m' + 4 < 7 * 47 := by
      have : 6 * m' < 6 * 47 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 4 < 6 * 47 + 4 := Nat.add_lt_add_right this 4
      calc 6 * m' + 4 < 6 * 47 + 4 := this
      _ ≤ 7 * 47 := by decide
    have h_lt : 7 * 47 < 7 * 47 := by
      calc 7 * 47 ≤ D * 47 := h1
      _ = 6 * m' + 4 := h_alg
      _ < 7 * 47 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 15 := by
    have h_alg_sol : 2 * 47 = 6 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 2 * 47 = 94 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 90 = 6 * m' := by
      calc 90 = 94 - 4 := rfl
      _ = 6 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 90 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 90 / 6 = 15 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_21 (m m' k' : ℕ)
  (h1 : 73 + m * 79 = 79 + m' * 83)
  (h2 : 79 + m' * 83 = 83 + k' * 89)
  (hm' : m' < 79) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 79 ≤ m' * 79 := Nat.mul_le_mul_right 79 h_le
    have h_le_mul2 : m' * 79 ≤ m' * 83 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 73 + m * 79 ≤ 73 + m' * 79 := Nat.add_le_add_left h_le_mul 73
    have h_step2 : 73 + m' * 79 ≤ 73 + m' * 83 := Nat.add_le_add_left h_le_mul2 73
    have h_step3 : 73 + m' * 83 < 79 + m' * 83 := Nat.add_lt_add_right (by decide : 73 < 79) _
    have h_lt : 73 + m * 79 < 79 + m' * 83 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 79 = 4 * m' + 6 := by
    have h_eq : m * 79 = m' * 79 + D * 79 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 83 = m' * 79 + 4 * m' := by
      rw [show 83 = 79 + 4 by decide, Nat.mul_add, Nat.mul_comm m' 4]
    rw [h_dist] at h1'
    have h1_assoc : (73 + D * 79) + m' * 79 = (79 + 4 * m') + m' * 79 := by
      calc (73 + D * 79) + m' * 79 = 73 + (D * 79 + m' * 79) := by rw [Nat.add_assoc]
      _ = 73 + (m' * 79 + D * 79) := by rw [Nat.add_comm (D * 79)]
      _ = 79 + (m' * 79 + 4 * m') := h1'
      _ = 79 + (4 * m' + m' * 79) := by rw [Nat.add_comm (m' * 79)]
      _ = (79 + 4 * m') + m' * 79 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 73 + D * 79 = 73 + (4 * m' + 6) := by
      calc 73 + D * 79 = (73 + D * 79) := rfl
      _ = 79 + 4 * m' := h1_sub
      _ = 73 + 6 + 4 * m' := rfl
      _ = 73 + (6 + 4 * m') := by rw [Nat.add_assoc]
      _ = 73 + (4 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 4 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 79 ≥ 5 * 79 := Nat.mul_le_mul_right 79 h_gt
    have h2 : 4 * m' + 6 < 5 * 79 := by
      have : 4 * m' < 4 * 79 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 4 * m' + 6 < 4 * 79 + 6 := Nat.add_lt_add_right this 6
      calc 4 * m' + 6 < 4 * 79 + 6 := this
      _ ≤ 5 * 79 := by decide
    have h_lt : 5 * 79 < 5 * 79 := by
      calc 5 * 79 ≤ D * 79 := h1
      _ = 4 * m' + 6 := h_alg
      _ < 5 * 79 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 38 := by
    have h_alg_sol : 2 * 79 = 4 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 2 * 79 = 158 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 152 = 4 * m' := by
      calc 152 = 158 - 6 := rfl
      _ = 4 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 4 * m' := rfl
    have h_div : 152 / 4 = (4 * m') / 4 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 4)] at h_div
    have h_div_eval : 152 / 4 = 38 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_22 (m m' k' : ℕ)
  (h1 : 79 + m * 83 = 83 + m' * 89)
  (h2 : 83 + m' * 89 = 89 + k' * 97)
  (hm' : m' < 83) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 83 ≤ m' * 83 := Nat.mul_le_mul_right 83 h_le
    have h_le_mul2 : m' * 83 ≤ m' * 89 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 79 + m * 83 ≤ 79 + m' * 83 := Nat.add_le_add_left h_le_mul 79
    have h_step2 : 79 + m' * 83 ≤ 79 + m' * 89 := Nat.add_le_add_left h_le_mul2 79
    have h_step3 : 79 + m' * 89 < 83 + m' * 89 := Nat.add_lt_add_right (by decide : 79 < 83) _
    have h_lt : 79 + m * 83 < 83 + m' * 89 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 83 = 6 * m' + 4 := by
    have h_eq : m * 83 = m' * 83 + D * 83 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 89 = m' * 83 + 6 * m' := by
      rw [show 89 = 83 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (79 + D * 83) + m' * 83 = (83 + 6 * m') + m' * 83 := by
      calc (79 + D * 83) + m' * 83 = 79 + (D * 83 + m' * 83) := by rw [Nat.add_assoc]
      _ = 79 + (m' * 83 + D * 83) := by rw [Nat.add_comm (D * 83)]
      _ = 83 + (m' * 83 + 6 * m') := h1'
      _ = 83 + (6 * m' + m' * 83) := by rw [Nat.add_comm (m' * 83)]
      _ = (83 + 6 * m') + m' * 83 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 79 + D * 83 = 79 + (6 * m' + 4) := by
      calc 79 + D * 83 = (79 + D * 83) := rfl
      _ = 83 + 6 * m' := h1_sub
      _ = 79 + 4 + 6 * m' := rfl
      _ = 79 + (4 + 6 * m') := by rw [Nat.add_assoc]
      _ = 79 + (6 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 83 ≥ 7 * 83 := Nat.mul_le_mul_right 83 h_gt
    have h2 : 6 * m' + 4 < 7 * 83 := by
      have : 6 * m' < 6 * 83 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 4 < 6 * 83 + 4 := Nat.add_lt_add_right this 4
      calc 6 * m' + 4 < 6 * 83 + 4 := this
      _ ≤ 7 * 83 := by decide
    have h_lt : 7 * 83 < 7 * 83 := by
      calc 7 * 83 ≤ D * 83 := h1
      _ = 6 * m' + 4 := h_alg
      _ < 7 * 83 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 27 := by
    have h_alg_sol : 2 * 83 = 6 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 2 * 83 = 166 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 162 = 6 * m' := by
      calc 162 = 166 - 4 := rfl
      _ = 6 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 162 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 162 / 6 = 27 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_28 (m m' k' : ℕ)
  (h1 : 107 + m * 109 = 109 + m' * 113)
  (h2 : 109 + m' * 113 = 113 + k' * 127)
  (hm' : m' < 109) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 109 ≤ m' * 109 := Nat.mul_le_mul_right 109 h_le
    have h_le_mul2 : m' * 109 ≤ m' * 113 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 107 + m * 109 ≤ 107 + m' * 109 := Nat.add_le_add_left h_le_mul 107
    have h_step2 : 107 + m' * 109 ≤ 107 + m' * 113 := Nat.add_le_add_left h_le_mul2 107
    have h_step3 : 107 + m' * 113 < 109 + m' * 113 := Nat.add_lt_add_right (by decide : 107 < 109) _
    have h_lt : 107 + m * 109 < 109 + m' * 113 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 109 = 4 * m' + 2 := by
    have h_eq : m * 109 = m' * 109 + D * 109 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 113 = m' * 109 + 4 * m' := by
      rw [show 113 = 109 + 4 by decide, Nat.mul_add, Nat.mul_comm m' 4]
    rw [h_dist] at h1'
    have h1_assoc : (107 + D * 109) + m' * 109 = (109 + 4 * m') + m' * 109 := by
      calc (107 + D * 109) + m' * 109 = 107 + (D * 109 + m' * 109) := by rw [Nat.add_assoc]
      _ = 107 + (m' * 109 + D * 109) := by rw [Nat.add_comm (D * 109)]
      _ = 109 + (m' * 109 + 4 * m') := h1'
      _ = 109 + (4 * m' + m' * 109) := by rw [Nat.add_comm (m' * 109)]
      _ = (109 + 4 * m') + m' * 109 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 107 + D * 109 = 107 + (4 * m' + 2) := by
      calc 107 + D * 109 = (107 + D * 109) := rfl
      _ = 109 + 4 * m' := h1_sub
      _ = 107 + 2 + 4 * m' := rfl
      _ = 107 + (2 + 4 * m') := by rw [Nat.add_assoc]
      _ = 107 + (4 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 4 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 109 ≥ 5 * 109 := Nat.mul_le_mul_right 109 h_gt
    have h2 : 4 * m' + 2 < 5 * 109 := by
      have : 4 * m' < 4 * 109 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 4 * m' + 2 < 4 * 109 + 2 := Nat.add_lt_add_right this 2
      calc 4 * m' + 2 < 4 * 109 + 2 := this
      _ ≤ 5 * 109 := by decide
    have h_lt : 5 * 109 < 5 * 109 := by
      calc 5 * 109 ≤ D * 109 := h1
      _ = 4 * m' + 2 := h_alg
      _ < 5 * 109 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 54 := by
    have h_alg_sol : 2 * 109 = 4 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 109 = 218 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 216 = 4 * m' := by
      calc 216 = 218 - 2 := rfl
      _ = 4 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 4 * m' := rfl
    have h_div : 216 / 4 = (4 * m') / 4 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 4)] at h_div
    have h_div_eval : 216 / 4 = 54 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_29 (m m' k' : ℕ)
  (h1 : 109 + m * 113 = 113 + m' * 127)
  (h2 : 113 + m' * 127 = 127 + k' * 131)
  (hm' : m' < 113) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 113 ≤ m' * 113 := Nat.mul_le_mul_right 113 h_le
    have h_le_mul2 : m' * 113 ≤ m' * 127 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 109 + m * 113 ≤ 109 + m' * 113 := Nat.add_le_add_left h_le_mul 109
    have h_step2 : 109 + m' * 113 ≤ 109 + m' * 127 := Nat.add_le_add_left h_le_mul2 109
    have h_step3 : 109 + m' * 127 < 113 + m' * 127 := Nat.add_lt_add_right (by decide : 109 < 113) _
    have h_lt : 109 + m * 113 < 113 + m' * 127 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 113 = 14 * m' + 4 := by
    have h_eq : m * 113 = m' * 113 + D * 113 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 127 = m' * 113 + 14 * m' := by
      rw [show 127 = 113 + 14 by decide, Nat.mul_add, Nat.mul_comm m' 14]
    rw [h_dist] at h1'
    have h1_assoc : (109 + D * 113) + m' * 113 = (113 + 14 * m') + m' * 113 := by
      calc (109 + D * 113) + m' * 113 = 109 + (D * 113 + m' * 113) := by rw [Nat.add_assoc]
      _ = 109 + (m' * 113 + D * 113) := by rw [Nat.add_comm (D * 113)]
      _ = 113 + (m' * 113 + 14 * m') := h1'
      _ = 113 + (14 * m' + m' * 113) := by rw [Nat.add_comm (m' * 113)]
      _ = (113 + 14 * m') + m' * 113 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 109 + D * 113 = 109 + (14 * m' + 4) := by
      calc 109 + D * 113 = (109 + D * 113) := rfl
      _ = 113 + 14 * m' := h1_sub
      _ = 109 + 4 + 14 * m' := rfl
      _ = 109 + (4 + 14 * m') := by rw [Nat.add_assoc]
      _ = 109 + (14 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 14 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 113 ≥ 15 * 113 := Nat.mul_le_mul_right 113 h_gt
    have h2 : 14 * m' + 4 < 15 * 113 := by
      have : 14 * m' < 14 * 113 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 14 * m' + 4 < 14 * 113 + 4 := Nat.add_lt_add_right this 4
      calc 14 * m' + 4 < 14 * 113 + 4 := this
      _ ≤ 15 * 113 := by decide
    have h_lt : 15 * 113 < 15 * 113 := by
      calc 15 * 113 ≤ D * 113 := h1
      _ = 14 * m' + 4 := h_alg
      _ < 15 * 113 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 4 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 32 := by
    have h_alg_sol : 4 * 113 = 14 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 4 * 113 = 452 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 448 = 14 * m' := by
      calc 448 = 452 - 4 := rfl
      _ = 14 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 14 * m' := rfl
    have h_div : 448 / 14 = (14 * m') / 14 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 14)] at h_div
    have h_div_eval : 448 / 14 = 32 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_45 (m m' k' : ℕ)
  (h1 : 197 + m * 199 = 199 + m' * 211)
  (h2 : 199 + m' * 211 = 211 + k' * 223)
  (hm' : m' < 199) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 199 ≤ m' * 199 := Nat.mul_le_mul_right 199 h_le
    have h_le_mul2 : m' * 199 ≤ m' * 211 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 197 + m * 199 ≤ 197 + m' * 199 := Nat.add_le_add_left h_le_mul 197
    have h_step2 : 197 + m' * 199 ≤ 197 + m' * 211 := Nat.add_le_add_left h_le_mul2 197
    have h_step3 : 197 + m' * 211 < 199 + m' * 211 := Nat.add_lt_add_right (by decide : 197 < 199) _
    have h_lt : 197 + m * 199 < 199 + m' * 211 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 199 = 12 * m' + 2 := by
    have h_eq : m * 199 = m' * 199 + D * 199 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 211 = m' * 199 + 12 * m' := by
      rw [show 211 = 199 + 12 by decide, Nat.mul_add, Nat.mul_comm m' 12]
    rw [h_dist] at h1'
    have h1_assoc : (197 + D * 199) + m' * 199 = (199 + 12 * m') + m' * 199 := by
      calc (197 + D * 199) + m' * 199 = 197 + (D * 199 + m' * 199) := by rw [Nat.add_assoc]
      _ = 197 + (m' * 199 + D * 199) := by rw [Nat.add_comm (D * 199)]
      _ = 199 + (m' * 199 + 12 * m') := h1'
      _ = 199 + (12 * m' + m' * 199) := by rw [Nat.add_comm (m' * 199)]
      _ = (199 + 12 * m') + m' * 199 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 197 + D * 199 = 197 + (12 * m' + 2) := by
      calc 197 + D * 199 = (197 + D * 199) := rfl
      _ = 199 + 12 * m' := h1_sub
      _ = 197 + 2 + 12 * m' := rfl
      _ = 197 + (2 + 12 * m') := by rw [Nat.add_assoc]
      _ = 197 + (12 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 12 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 199 ≥ 13 * 199 := Nat.mul_le_mul_right 199 h_gt
    have h2 : 12 * m' + 2 < 13 * 199 := by
      have : 12 * m' < 12 * 199 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 12 * m' + 2 < 12 * 199 + 2 := Nat.add_lt_add_right this 2
      calc 12 * m' + 2 < 12 * 199 + 2 := this
      _ ≤ 13 * 199 := by decide
    have h_lt : 13 * 199 < 13 * 199 := by
      calc 13 * 199 ≤ D * 199 := h1
      _ = 12 * m' + 2 := h_alg
      _ < 13 * 199 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 33 := by
    have h_alg_sol : 2 * 199 = 12 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 199 = 398 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 396 = 12 * m' := by
      calc 396 = 398 - 2 := rfl
      _ = 12 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 12 * m' := rfl
    have h_div : 396 / 12 = (12 * m') / 12 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 12)] at h_div
    have h_div_eval : 396 / 12 = 33 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_52 (m m' k' : ℕ)
  (h1 : 239 + m * 241 = 241 + m' * 251)
  (h2 : 241 + m' * 251 = 251 + k' * 257)
  (hm' : m' < 241) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 241 ≤ m' * 241 := Nat.mul_le_mul_right 241 h_le
    have h_le_mul2 : m' * 241 ≤ m' * 251 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 239 + m * 241 ≤ 239 + m' * 241 := Nat.add_le_add_left h_le_mul 239
    have h_step2 : 239 + m' * 241 ≤ 239 + m' * 251 := Nat.add_le_add_left h_le_mul2 239
    have h_step3 : 239 + m' * 251 < 241 + m' * 251 := Nat.add_lt_add_right (by decide : 239 < 241) _
    have h_lt : 239 + m * 241 < 241 + m' * 251 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 241 = 10 * m' + 2 := by
    have h_eq : m * 241 = m' * 241 + D * 241 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 251 = m' * 241 + 10 * m' := by
      rw [show 251 = 241 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (239 + D * 241) + m' * 241 = (241 + 10 * m') + m' * 241 := by
      calc (239 + D * 241) + m' * 241 = 239 + (D * 241 + m' * 241) := by rw [Nat.add_assoc]
      _ = 239 + (m' * 241 + D * 241) := by rw [Nat.add_comm (D * 241)]
      _ = 241 + (m' * 241 + 10 * m') := h1'
      _ = 241 + (10 * m' + m' * 241) := by rw [Nat.add_comm (m' * 241)]
      _ = (241 + 10 * m') + m' * 241 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 239 + D * 241 = 239 + (10 * m' + 2) := by
      calc 239 + D * 241 = (239 + D * 241) := rfl
      _ = 241 + 10 * m' := h1_sub
      _ = 239 + 2 + 10 * m' := rfl
      _ = 239 + (2 + 10 * m') := by rw [Nat.add_assoc]
      _ = 239 + (10 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 241 ≥ 11 * 241 := Nat.mul_le_mul_right 241 h_gt
    have h2 : 10 * m' + 2 < 11 * 241 := by
      have : 10 * m' < 10 * 241 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 2 < 10 * 241 + 2 := Nat.add_lt_add_right this 2
      calc 10 * m' + 2 < 10 * 241 + 2 := this
      _ ≤ 11 * 241 := by decide
    have h_lt : 11 * 241 < 11 * 241 := by
      calc 11 * 241 ≤ D * 241 := h1
      _ = 10 * m' + 2 := h_alg
      _ < 11 * 241 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 48 := by
    have h_alg_sol : 2 * 241 = 10 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 241 = 482 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 480 = 10 * m' := by
      calc 480 = 482 - 2 := rfl
      _ = 10 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 480 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 480 / 10 = 48 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_60 (m m' k' : ℕ)
  (h1 : 281 + m * 283 = 283 + m' * 293)
  (h2 : 283 + m' * 293 = 293 + k' * 307)
  (hm' : m' < 283) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 283 ≤ m' * 283 := Nat.mul_le_mul_right 283 h_le
    have h_le_mul2 : m' * 283 ≤ m' * 293 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 281 + m * 283 ≤ 281 + m' * 283 := Nat.add_le_add_left h_le_mul 281
    have h_step2 : 281 + m' * 283 ≤ 281 + m' * 293 := Nat.add_le_add_left h_le_mul2 281
    have h_step3 : 281 + m' * 293 < 283 + m' * 293 := Nat.add_lt_add_right (by decide : 281 < 283) _
    have h_lt : 281 + m * 283 < 283 + m' * 293 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 283 = 10 * m' + 2 := by
    have h_eq : m * 283 = m' * 283 + D * 283 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 293 = m' * 283 + 10 * m' := by
      rw [show 293 = 283 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (281 + D * 283) + m' * 283 = (283 + 10 * m') + m' * 283 := by
      calc (281 + D * 283) + m' * 283 = 281 + (D * 283 + m' * 283) := by rw [Nat.add_assoc]
      _ = 281 + (m' * 283 + D * 283) := by rw [Nat.add_comm (D * 283)]
      _ = 283 + (m' * 283 + 10 * m') := h1'
      _ = 283 + (10 * m' + m' * 283) := by rw [Nat.add_comm (m' * 283)]
      _ = (283 + 10 * m') + m' * 283 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 281 + D * 283 = 281 + (10 * m' + 2) := by
      calc 281 + D * 283 = (281 + D * 283) := rfl
      _ = 283 + 10 * m' := h1_sub
      _ = 281 + 2 + 10 * m' := rfl
      _ = 281 + (2 + 10 * m') := by rw [Nat.add_assoc]
      _ = 281 + (10 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 283 ≥ 11 * 283 := Nat.mul_le_mul_right 283 h_gt
    have h2 : 10 * m' + 2 < 11 * 283 := by
      have : 10 * m' < 10 * 283 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 2 < 10 * 283 + 2 := Nat.add_lt_add_right this 2
      calc 10 * m' + 2 < 10 * 283 + 2 := this
      _ ≤ 11 * 283 := by decide
    have h_lt : 11 * 283 < 11 * 283 := by
      calc 11 * 283 ≤ D * 283 := h1
      _ = 10 * m' + 2 := h_alg
      _ < 11 * 283 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 4 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 113 := by
    have h_alg_sol : 4 * 283 = 10 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 4 * 283 = 1132 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 1130 = 10 * m' := by
      calc 1130 = 1132 - 2 := rfl
      _ = 10 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 1130 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 1130 / 10 = 113 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_64 (m m' k' : ℕ)
  (h1 : 311 + m * 313 = 313 + m' * 317)
  (h2 : 313 + m' * 317 = 317 + k' * 331)
  (hm' : m' < 313) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 313 ≤ m' * 313 := Nat.mul_le_mul_right 313 h_le
    have h_le_mul2 : m' * 313 ≤ m' * 317 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 311 + m * 313 ≤ 311 + m' * 313 := Nat.add_le_add_left h_le_mul 311
    have h_step2 : 311 + m' * 313 ≤ 311 + m' * 317 := Nat.add_le_add_left h_le_mul2 311
    have h_step3 : 311 + m' * 317 < 313 + m' * 317 := Nat.add_lt_add_right (by decide : 311 < 313) _
    have h_lt : 311 + m * 313 < 313 + m' * 317 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 313 = 4 * m' + 2 := by
    have h_eq : m * 313 = m' * 313 + D * 313 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 317 = m' * 313 + 4 * m' := by
      rw [show 317 = 313 + 4 by decide, Nat.mul_add, Nat.mul_comm m' 4]
    rw [h_dist] at h1'
    have h1_assoc : (311 + D * 313) + m' * 313 = (313 + 4 * m') + m' * 313 := by
      calc (311 + D * 313) + m' * 313 = 311 + (D * 313 + m' * 313) := by rw [Nat.add_assoc]
      _ = 311 + (m' * 313 + D * 313) := by rw [Nat.add_comm (D * 313)]
      _ = 313 + (m' * 313 + 4 * m') := h1'
      _ = 313 + (4 * m' + m' * 313) := by rw [Nat.add_comm (m' * 313)]
      _ = (313 + 4 * m') + m' * 313 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 311 + D * 313 = 311 + (4 * m' + 2) := by
      calc 311 + D * 313 = (311 + D * 313) := rfl
      _ = 313 + 4 * m' := h1_sub
      _ = 311 + 2 + 4 * m' := rfl
      _ = 311 + (2 + 4 * m') := by rw [Nat.add_assoc]
      _ = 311 + (4 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 4 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 313 ≥ 5 * 313 := Nat.mul_le_mul_right 313 h_gt
    have h2 : 4 * m' + 2 < 5 * 313 := by
      have : 4 * m' < 4 * 313 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 4 * m' + 2 < 4 * 313 + 2 := Nat.add_lt_add_right this 2
      calc 4 * m' + 2 < 4 * 313 + 2 := this
      _ ≤ 5 * 313 := by decide
    have h_lt : 5 * 313 < 5 * 313 := by
      calc 5 * 313 ≤ D * 313 := h1
      _ = 4 * m' + 2 := h_alg
      _ < 5 * 313 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 156 := by
    have h_alg_sol : 2 * 313 = 4 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 313 = 626 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 624 = 4 * m' := by
      calc 624 = 626 - 2 := rfl
      _ = 4 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 4 * m' := rfl
    have h_div : 624 / 4 = (4 * m') / 4 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 4)] at h_div
    have h_div_eval : 624 / 4 = 156 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_65 (m m' k' : ℕ)
  (h1 : 313 + m * 317 = 317 + m' * 331)
  (h2 : 317 + m' * 331 = 331 + k' * 337)
  (hm' : m' < 317) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 317 ≤ m' * 317 := Nat.mul_le_mul_right 317 h_le
    have h_le_mul2 : m' * 317 ≤ m' * 331 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 313 + m * 317 ≤ 313 + m' * 317 := Nat.add_le_add_left h_le_mul 313
    have h_step2 : 313 + m' * 317 ≤ 313 + m' * 331 := Nat.add_le_add_left h_le_mul2 313
    have h_step3 : 313 + m' * 331 < 317 + m' * 331 := Nat.add_lt_add_right (by decide : 313 < 317) _
    have h_lt : 313 + m * 317 < 317 + m' * 331 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 317 = 14 * m' + 4 := by
    have h_eq : m * 317 = m' * 317 + D * 317 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 331 = m' * 317 + 14 * m' := by
      rw [show 331 = 317 + 14 by decide, Nat.mul_add, Nat.mul_comm m' 14]
    rw [h_dist] at h1'
    have h1_assoc : (313 + D * 317) + m' * 317 = (317 + 14 * m') + m' * 317 := by
      calc (313 + D * 317) + m' * 317 = 313 + (D * 317 + m' * 317) := by rw [Nat.add_assoc]
      _ = 313 + (m' * 317 + D * 317) := by rw [Nat.add_comm (D * 317)]
      _ = 317 + (m' * 317 + 14 * m') := h1'
      _ = 317 + (14 * m' + m' * 317) := by rw [Nat.add_comm (m' * 317)]
      _ = (317 + 14 * m') + m' * 317 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 313 + D * 317 = 313 + (14 * m' + 4) := by
      calc 313 + D * 317 = (313 + D * 317) := rfl
      _ = 317 + 14 * m' := h1_sub
      _ = 313 + 4 + 14 * m' := rfl
      _ = 313 + (4 + 14 * m') := by rw [Nat.add_assoc]
      _ = 313 + (14 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 14 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 317 ≥ 15 * 317 := Nat.mul_le_mul_right 317 h_gt
    have h2 : 14 * m' + 4 < 15 * 317 := by
      have : 14 * m' < 14 * 317 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 14 * m' + 4 < 14 * 317 + 4 := Nat.add_lt_add_right this 4
      calc 14 * m' + 4 < 14 * 317 + 4 := this
      _ ≤ 15 * 317 := by decide
    have h_lt : 15 * 317 < 15 * 317 := by
      calc 15 * 317 ≤ D * 317 := h1
      _ = 14 * m' + 4 := h_alg
      _ < 15 * 317 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 45 := by
    have h_alg_sol : 2 * 317 = 14 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 2 * 317 = 634 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 630 = 14 * m' := by
      calc 630 = 634 - 4 := rfl
      _ = 14 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 14 * m' := rfl
    have h_div : 630 / 14 = (14 * m') / 14 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 14)] at h_div
    have h_div_eval : 630 / 14 = 45 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_66 (m m' k' : ℕ)
  (h1 : 317 + m * 331 = 331 + m' * 337)
  (h2 : 331 + m' * 337 = 337 + k' * 347)
  (hm' : m' < 331) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 331 ≤ m' * 331 := Nat.mul_le_mul_right 331 h_le
    have h_le_mul2 : m' * 331 ≤ m' * 337 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 317 + m * 331 ≤ 317 + m' * 331 := Nat.add_le_add_left h_le_mul 317
    have h_step2 : 317 + m' * 331 ≤ 317 + m' * 337 := Nat.add_le_add_left h_le_mul2 317
    have h_step3 : 317 + m' * 337 < 331 + m' * 337 := Nat.add_lt_add_right (by decide : 317 < 331) _
    have h_lt : 317 + m * 331 < 331 + m' * 337 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 331 = 6 * m' + 14 := by
    have h_eq : m * 331 = m' * 331 + D * 331 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 337 = m' * 331 + 6 * m' := by
      rw [show 337 = 331 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (317 + D * 331) + m' * 331 = (331 + 6 * m') + m' * 331 := by
      calc (317 + D * 331) + m' * 331 = 317 + (D * 331 + m' * 331) := by rw [Nat.add_assoc]
      _ = 317 + (m' * 331 + D * 331) := by rw [Nat.add_comm (D * 331)]
      _ = 331 + (m' * 331 + 6 * m') := h1'
      _ = 331 + (6 * m' + m' * 331) := by rw [Nat.add_comm (m' * 331)]
      _ = (331 + 6 * m') + m' * 331 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 317 + D * 331 = 317 + (6 * m' + 14) := by
      calc 317 + D * 331 = (317 + D * 331) := rfl
      _ = 331 + 6 * m' := h1_sub
      _ = 317 + 14 + 6 * m' := rfl
      _ = 317 + (14 + 6 * m') := by rw [Nat.add_assoc]
      _ = 317 + (6 * m' + 14) := by rw [Nat.add_comm 14]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 331 ≥ 7 * 331 := Nat.mul_le_mul_right 331 h_gt
    have h2 : 6 * m' + 14 < 7 * 331 := by
      have : 6 * m' < 6 * 331 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 14 < 6 * 331 + 14 := Nat.add_lt_add_right this 14
      calc 6 * m' + 14 < 6 * 331 + 14 := this
      _ ≤ 7 * 331 := by decide
    have h_lt : 7 * 331 < 7 * 331 := by
      calc 7 * 331 ≤ D * 331 := h1
      _ = 6 * m' + 14 := h_alg
      _ < 7 * 331 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 108 := by
    have h_alg_sol : 2 * 331 = 6 * m' + 14 := h_D_eq ▸ h_alg
    have h_eval : 2 * 331 = 662 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 648 = 6 * m' := by
      calc 648 = 662 - 14 := rfl
      _ = 6 * m' + 14 - 14 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 648 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 648 / 6 = 108 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_78 (m m' k' : ℕ)
  (h1 : 397 + m * 401 = 401 + m' * 409)
  (h2 : 401 + m' * 409 = 409 + k' * 419)
  (hm' : m' < 401) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 401 ≤ m' * 401 := Nat.mul_le_mul_right 401 h_le
    have h_le_mul2 : m' * 401 ≤ m' * 409 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 397 + m * 401 ≤ 397 + m' * 401 := Nat.add_le_add_left h_le_mul 397
    have h_step2 : 397 + m' * 401 ≤ 397 + m' * 409 := Nat.add_le_add_left h_le_mul2 397
    have h_step3 : 397 + m' * 409 < 401 + m' * 409 := Nat.add_lt_add_right (by decide : 397 < 401) _
    have h_lt : 397 + m * 401 < 401 + m' * 409 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 401 = 8 * m' + 4 := by
    have h_eq : m * 401 = m' * 401 + D * 401 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 409 = m' * 401 + 8 * m' := by
      rw [show 409 = 401 + 8 by decide, Nat.mul_add, Nat.mul_comm m' 8]
    rw [h_dist] at h1'
    have h1_assoc : (397 + D * 401) + m' * 401 = (401 + 8 * m') + m' * 401 := by
      calc (397 + D * 401) + m' * 401 = 397 + (D * 401 + m' * 401) := by rw [Nat.add_assoc]
      _ = 397 + (m' * 401 + D * 401) := by rw [Nat.add_comm (D * 401)]
      _ = 401 + (m' * 401 + 8 * m') := h1'
      _ = 401 + (8 * m' + m' * 401) := by rw [Nat.add_comm (m' * 401)]
      _ = (401 + 8 * m') + m' * 401 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 397 + D * 401 = 397 + (8 * m' + 4) := by
      calc 397 + D * 401 = (397 + D * 401) := rfl
      _ = 401 + 8 * m' := h1_sub
      _ = 397 + 4 + 8 * m' := rfl
      _ = 397 + (4 + 8 * m') := by rw [Nat.add_assoc]
      _ = 397 + (8 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 8 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 401 ≥ 9 * 401 := Nat.mul_le_mul_right 401 h_gt
    have h2 : 8 * m' + 4 < 9 * 401 := by
      have : 8 * m' < 8 * 401 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 8 * m' + 4 < 8 * 401 + 4 := Nat.add_lt_add_right this 4
      calc 8 * m' + 4 < 8 * 401 + 4 := this
      _ ≤ 9 * 401 := by decide
    have h_lt : 9 * 401 < 9 * 401 := by
      calc 9 * 401 ≤ D * 401 := h1
      _ = 8 * m' + 4 := h_alg
      _ < 9 * 401 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 4 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 200 := by
    have h_alg_sol : 4 * 401 = 8 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 4 * 401 = 1604 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 1600 = 8 * m' := by
      calc 1600 = 1604 - 4 := rfl
      _ = 8 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 8 * m' := rfl
    have h_div : 1600 / 8 = (8 * m') / 8 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 8)] at h_div
    have h_div_eval : 1600 / 8 = 200 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_90 (m m' k' : ℕ)
  (h1 : 463 + m * 467 = 467 + m' * 479)
  (h2 : 467 + m' * 479 = 479 + k' * 487)
  (hm' : m' < 467) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 467 ≤ m' * 467 := Nat.mul_le_mul_right 467 h_le
    have h_le_mul2 : m' * 467 ≤ m' * 479 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 463 + m * 467 ≤ 463 + m' * 467 := Nat.add_le_add_left h_le_mul 463
    have h_step2 : 463 + m' * 467 ≤ 463 + m' * 479 := Nat.add_le_add_left h_le_mul2 463
    have h_step3 : 463 + m' * 479 < 467 + m' * 479 := Nat.add_lt_add_right (by decide : 463 < 467) _
    have h_lt : 463 + m * 467 < 467 + m' * 479 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 467 = 12 * m' + 4 := by
    have h_eq : m * 467 = m' * 467 + D * 467 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 479 = m' * 467 + 12 * m' := by
      rw [show 479 = 467 + 12 by decide, Nat.mul_add, Nat.mul_comm m' 12]
    rw [h_dist] at h1'
    have h1_assoc : (463 + D * 467) + m' * 467 = (467 + 12 * m') + m' * 467 := by
      calc (463 + D * 467) + m' * 467 = 463 + (D * 467 + m' * 467) := by rw [Nat.add_assoc]
      _ = 463 + (m' * 467 + D * 467) := by rw [Nat.add_comm (D * 467)]
      _ = 467 + (m' * 467 + 12 * m') := h1'
      _ = 467 + (12 * m' + m' * 467) := by rw [Nat.add_comm (m' * 467)]
      _ = (467 + 12 * m') + m' * 467 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 463 + D * 467 = 463 + (12 * m' + 4) := by
      calc 463 + D * 467 = (463 + D * 467) := rfl
      _ = 467 + 12 * m' := h1_sub
      _ = 463 + 4 + 12 * m' := rfl
      _ = 463 + (4 + 12 * m') := by rw [Nat.add_assoc]
      _ = 463 + (12 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 12 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 467 ≥ 13 * 467 := Nat.mul_le_mul_right 467 h_gt
    have h2 : 12 * m' + 4 < 13 * 467 := by
      have : 12 * m' < 12 * 467 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 12 * m' + 4 < 12 * 467 + 4 := Nat.add_lt_add_right this 4
      calc 12 * m' + 4 < 12 * 467 + 4 := this
      _ ≤ 13 * 467 := by decide
    have h_lt : 13 * 467 < 13 * 467 := by
      calc 13 * 467 ≤ D * 467 := h1
      _ = 12 * m' + 4 := h_alg
      _ < 13 * 467 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 311 := by
    have h_alg_sol : 8 * 467 = 12 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 8 * 467 = 3736 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 3732 = 12 * m' := by
      calc 3732 = 3736 - 4 := rfl
      _ = 12 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 12 * m' := rfl
    have h_div : 3732 / 12 = (12 * m') / 12 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 12)] at h_div
    have h_div_eval : 3732 / 12 = 311 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_95 (m m' k' : ℕ)
  (h1 : 499 + m * 503 = 503 + m' * 509)
  (h2 : 503 + m' * 509 = 509 + k' * 521)
  (hm' : m' < 503) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 503 ≤ m' * 503 := Nat.mul_le_mul_right 503 h_le
    have h_le_mul2 : m' * 503 ≤ m' * 509 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 499 + m * 503 ≤ 499 + m' * 503 := Nat.add_le_add_left h_le_mul 499
    have h_step2 : 499 + m' * 503 ≤ 499 + m' * 509 := Nat.add_le_add_left h_le_mul2 499
    have h_step3 : 499 + m' * 509 < 503 + m' * 509 := Nat.add_lt_add_right (by decide : 499 < 503) _
    have h_lt : 499 + m * 503 < 503 + m' * 509 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 503 = 6 * m' + 4 := by
    have h_eq : m * 503 = m' * 503 + D * 503 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 509 = m' * 503 + 6 * m' := by
      rw [show 509 = 503 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (499 + D * 503) + m' * 503 = (503 + 6 * m') + m' * 503 := by
      calc (499 + D * 503) + m' * 503 = 499 + (D * 503 + m' * 503) := by rw [Nat.add_assoc]
      _ = 499 + (m' * 503 + D * 503) := by rw [Nat.add_comm (D * 503)]
      _ = 503 + (m' * 503 + 6 * m') := h1'
      _ = 503 + (6 * m' + m' * 503) := by rw [Nat.add_comm (m' * 503)]
      _ = (503 + 6 * m') + m' * 503 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 499 + D * 503 = 499 + (6 * m' + 4) := by
      calc 499 + D * 503 = (499 + D * 503) := rfl
      _ = 503 + 6 * m' := h1_sub
      _ = 499 + 4 + 6 * m' := rfl
      _ = 499 + (4 + 6 * m') := by rw [Nat.add_assoc]
      _ = 499 + (6 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 503 ≥ 7 * 503 := Nat.mul_le_mul_right 503 h_gt
    have h2 : 6 * m' + 4 < 7 * 503 := by
      have : 6 * m' < 6 * 503 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 4 < 6 * 503 + 4 := Nat.add_lt_add_right this 4
      calc 6 * m' + 4 < 6 * 503 + 4 := this
      _ ≤ 7 * 503 := by decide
    have h_lt : 7 * 503 < 7 * 503 := by
      calc 7 * 503 ≤ D * 503 := h1
      _ = 6 * m' + 4 := h_alg
      _ < 7 * 503 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 167 := by
    have h_alg_sol : 2 * 503 = 6 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 2 * 503 = 1006 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 1002 = 6 * m' := by
      calc 1002 = 1006 - 4 := rfl
      _ = 6 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 1002 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 1002 / 6 = 167 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_98 (m m' k' : ℕ)
  (h1 : 521 + m * 523 = 523 + m' * 541)
  (h2 : 523 + m' * 541 = 541 + k' * 547)
  (hm' : m' < 523) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 523 ≤ m' * 523 := Nat.mul_le_mul_right 523 h_le
    have h_le_mul2 : m' * 523 ≤ m' * 541 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 521 + m * 523 ≤ 521 + m' * 523 := Nat.add_le_add_left h_le_mul 521
    have h_step2 : 521 + m' * 523 ≤ 521 + m' * 541 := Nat.add_le_add_left h_le_mul2 521
    have h_step3 : 521 + m' * 541 < 523 + m' * 541 := Nat.add_lt_add_right (by decide : 521 < 523) _
    have h_lt : 521 + m * 523 < 523 + m' * 541 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 523 = 18 * m' + 2 := by
    have h_eq : m * 523 = m' * 523 + D * 523 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 541 = m' * 523 + 18 * m' := by
      rw [show 541 = 523 + 18 by decide, Nat.mul_add, Nat.mul_comm m' 18]
    rw [h_dist] at h1'
    have h1_assoc : (521 + D * 523) + m' * 523 = (523 + 18 * m') + m' * 523 := by
      calc (521 + D * 523) + m' * 523 = 521 + (D * 523 + m' * 523) := by rw [Nat.add_assoc]
      _ = 521 + (m' * 523 + D * 523) := by rw [Nat.add_comm (D * 523)]
      _ = 523 + (m' * 523 + 18 * m') := h1'
      _ = 523 + (18 * m' + m' * 523) := by rw [Nat.add_comm (m' * 523)]
      _ = (523 + 18 * m') + m' * 523 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 521 + D * 523 = 521 + (18 * m' + 2) := by
      calc 521 + D * 523 = (521 + D * 523) := rfl
      _ = 523 + 18 * m' := h1_sub
      _ = 521 + 2 + 18 * m' := rfl
      _ = 521 + (2 + 18 * m') := by rw [Nat.add_assoc]
      _ = 521 + (18 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 18 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 523 ≥ 19 * 523 := Nat.mul_le_mul_right 523 h_gt
    have h2 : 18 * m' + 2 < 19 * 523 := by
      have : 18 * m' < 18 * 523 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 18 * m' + 2 < 18 * 523 + 2 := Nat.add_lt_add_right this 2
      calc 18 * m' + 2 < 18 * 523 + 2 := this
      _ ≤ 19 * 523 := by decide
    have h_lt : 19 * 523 < 19 * 523 := by
      calc 19 * 523 ≤ D * 523 := h1
      _ = 18 * m' + 2 := h_alg
      _ < 19 * 523 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 58 := by
    have h_alg_sol : 2 * 523 = 18 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 523 = 1046 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 1044 = 18 * m' := by
      calc 1044 = 1046 - 2 := rfl
      _ = 18 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 18 * m' := rfl
    have h_div : 1044 / 18 = (18 * m') / 18 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 18)] at h_div
    have h_div_eval : 1044 / 18 = 58 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_113 (m m' k' : ℕ)
  (h1 : 617 + m * 619 = 619 + m' * 631)
  (h2 : 619 + m' * 631 = 631 + k' * 641)
  (hm' : m' < 619) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 619 ≤ m' * 619 := Nat.mul_le_mul_right 619 h_le
    have h_le_mul2 : m' * 619 ≤ m' * 631 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 617 + m * 619 ≤ 617 + m' * 619 := Nat.add_le_add_left h_le_mul 617
    have h_step2 : 617 + m' * 619 ≤ 617 + m' * 631 := Nat.add_le_add_left h_le_mul2 617
    have h_step3 : 617 + m' * 631 < 619 + m' * 631 := Nat.add_lt_add_right (by decide : 617 < 619) _
    have h_lt : 617 + m * 619 < 619 + m' * 631 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 619 = 12 * m' + 2 := by
    have h_eq : m * 619 = m' * 619 + D * 619 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 631 = m' * 619 + 12 * m' := by
      rw [show 631 = 619 + 12 by decide, Nat.mul_add, Nat.mul_comm m' 12]
    rw [h_dist] at h1'
    have h1_assoc : (617 + D * 619) + m' * 619 = (619 + 12 * m') + m' * 619 := by
      calc (617 + D * 619) + m' * 619 = 617 + (D * 619 + m' * 619) := by rw [Nat.add_assoc]
      _ = 617 + (m' * 619 + D * 619) := by rw [Nat.add_comm (D * 619)]
      _ = 619 + (m' * 619 + 12 * m') := h1'
      _ = 619 + (12 * m' + m' * 619) := by rw [Nat.add_comm (m' * 619)]
      _ = (619 + 12 * m') + m' * 619 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 617 + D * 619 = 617 + (12 * m' + 2) := by
      calc 617 + D * 619 = (617 + D * 619) := rfl
      _ = 619 + 12 * m' := h1_sub
      _ = 617 + 2 + 12 * m' := rfl
      _ = 617 + (2 + 12 * m') := by rw [Nat.add_assoc]
      _ = 617 + (12 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 12 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 619 ≥ 13 * 619 := Nat.mul_le_mul_right 619 h_gt
    have h2 : 12 * m' + 2 < 13 * 619 := by
      have : 12 * m' < 12 * 619 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 12 * m' + 2 < 12 * 619 + 2 := Nat.add_lt_add_right this 2
      calc 12 * m' + 2 < 12 * 619 + 2 := this
      _ ≤ 13 * 619 := by decide
    have h_lt : 13 * 619 < 13 * 619 := by
      calc 13 * 619 ≤ D * 619 := h1
      _ = 12 * m' + 2 := h_alg
      _ < 13 * 619 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 103 := by
    have h_alg_sol : 2 * 619 = 12 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 619 = 1238 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 1236 = 12 * m' := by
      calc 1236 = 1238 - 2 := rfl
      _ = 12 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 12 * m' := rfl
    have h_div : 1236 / 12 = (12 * m') / 12 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 12)] at h_div
    have h_div_eval : 1236 / 12 = 103 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_136 (m m' k' : ℕ)
  (h1 : 769 + m * 773 = 773 + m' * 787)
  (h2 : 773 + m' * 787 = 787 + k' * 797)
  (hm' : m' < 773) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 773 ≤ m' * 773 := Nat.mul_le_mul_right 773 h_le
    have h_le_mul2 : m' * 773 ≤ m' * 787 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 769 + m * 773 ≤ 769 + m' * 773 := Nat.add_le_add_left h_le_mul 769
    have h_step2 : 769 + m' * 773 ≤ 769 + m' * 787 := Nat.add_le_add_left h_le_mul2 769
    have h_step3 : 769 + m' * 787 < 773 + m' * 787 := Nat.add_lt_add_right (by decide : 769 < 773) _
    have h_lt : 769 + m * 773 < 773 + m' * 787 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 773 = 14 * m' + 4 := by
    have h_eq : m * 773 = m' * 773 + D * 773 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 787 = m' * 773 + 14 * m' := by
      rw [show 787 = 773 + 14 by decide, Nat.mul_add, Nat.mul_comm m' 14]
    rw [h_dist] at h1'
    have h1_assoc : (769 + D * 773) + m' * 773 = (773 + 14 * m') + m' * 773 := by
      calc (769 + D * 773) + m' * 773 = 769 + (D * 773 + m' * 773) := by rw [Nat.add_assoc]
      _ = 769 + (m' * 773 + D * 773) := by rw [Nat.add_comm (D * 773)]
      _ = 773 + (m' * 773 + 14 * m') := h1'
      _ = 773 + (14 * m' + m' * 773) := by rw [Nat.add_comm (m' * 773)]
      _ = (773 + 14 * m') + m' * 773 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 769 + D * 773 = 769 + (14 * m' + 4) := by
      calc 769 + D * 773 = (769 + D * 773) := rfl
      _ = 773 + 14 * m' := h1_sub
      _ = 769 + 4 + 14 * m' := rfl
      _ = 769 + (4 + 14 * m') := by rw [Nat.add_assoc]
      _ = 769 + (14 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 14 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 773 ≥ 15 * 773 := Nat.mul_le_mul_right 773 h_gt
    have h2 : 14 * m' + 4 < 15 * 773 := by
      have : 14 * m' < 14 * 773 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 14 * m' + 4 < 14 * 773 + 4 := Nat.add_lt_add_right this 4
      calc 14 * m' + 4 < 14 * 773 + 4 := this
      _ ≤ 15 * 773 := by decide
    have h_lt : 15 * 773 < 15 * 773 := by
      calc 15 * 773 ≤ D * 773 := h1
      _ = 14 * m' + 4 := h_alg
      _ < 15 * 773 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 6 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 331 := by
    have h_alg_sol : 6 * 773 = 14 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 6 * 773 = 4638 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 4634 = 14 * m' := by
      calc 4634 = 4638 - 4 := rfl
      _ = 14 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 14 * m' := rfl
    have h_div : 4634 / 14 = (14 * m') / 14 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 14)] at h_div
    have h_div_eval : 4634 / 14 = 331 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_137 (m m' k' : ℕ)
  (h1 : 773 + m * 787 = 787 + m' * 797)
  (h2 : 787 + m' * 797 = 797 + k' * 809)
  (hm' : m' < 787) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 787 ≤ m' * 787 := Nat.mul_le_mul_right 787 h_le
    have h_le_mul2 : m' * 787 ≤ m' * 797 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 773 + m * 787 ≤ 773 + m' * 787 := Nat.add_le_add_left h_le_mul 773
    have h_step2 : 773 + m' * 787 ≤ 773 + m' * 797 := Nat.add_le_add_left h_le_mul2 773
    have h_step3 : 773 + m' * 797 < 787 + m' * 797 := Nat.add_lt_add_right (by decide : 773 < 787) _
    have h_lt : 773 + m * 787 < 787 + m' * 797 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 787 = 10 * m' + 14 := by
    have h_eq : m * 787 = m' * 787 + D * 787 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 797 = m' * 787 + 10 * m' := by
      rw [show 797 = 787 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (773 + D * 787) + m' * 787 = (787 + 10 * m') + m' * 787 := by
      calc (773 + D * 787) + m' * 787 = 773 + (D * 787 + m' * 787) := by rw [Nat.add_assoc]
      _ = 773 + (m' * 787 + D * 787) := by rw [Nat.add_comm (D * 787)]
      _ = 787 + (m' * 787 + 10 * m') := h1'
      _ = 787 + (10 * m' + m' * 787) := by rw [Nat.add_comm (m' * 787)]
      _ = (787 + 10 * m') + m' * 787 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 773 + D * 787 = 773 + (10 * m' + 14) := by
      calc 773 + D * 787 = (773 + D * 787) := rfl
      _ = 787 + 10 * m' := h1_sub
      _ = 773 + 14 + 10 * m' := rfl
      _ = 773 + (14 + 10 * m') := by rw [Nat.add_assoc]
      _ = 773 + (10 * m' + 14) := by rw [Nat.add_comm 14]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 787 ≥ 11 * 787 := Nat.mul_le_mul_right 787 h_gt
    have h2 : 10 * m' + 14 < 11 * 787 := by
      have : 10 * m' < 10 * 787 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 14 < 10 * 787 + 14 := Nat.add_lt_add_right this 14
      calc 10 * m' + 14 < 10 * 787 + 14 := this
      _ ≤ 11 * 787 := by decide
    have h_lt : 11 * 787 < 11 * 787 := by
      calc 11 * 787 ≤ D * 787 := h1
      _ = 10 * m' + 14 := h_alg
      _ < 11 * 787 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 156 := by
    have h_alg_sol : 2 * 787 = 10 * m' + 14 := h_D_eq ▸ h_alg
    have h_eval : 2 * 787 = 1574 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 1560 = 10 * m' := by
      calc 1560 = 1574 - 14 := rfl
      _ = 10 * m' + 14 - 14 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 1560 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 1560 / 10 = 156 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_144 (m m' k' : ℕ)
  (h1 : 827 + m * 829 = 829 + m' * 839)
  (h2 : 829 + m' * 839 = 839 + k' * 853)
  (hm' : m' < 829) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 829 ≤ m' * 829 := Nat.mul_le_mul_right 829 h_le
    have h_le_mul2 : m' * 829 ≤ m' * 839 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 827 + m * 829 ≤ 827 + m' * 829 := Nat.add_le_add_left h_le_mul 827
    have h_step2 : 827 + m' * 829 ≤ 827 + m' * 839 := Nat.add_le_add_left h_le_mul2 827
    have h_step3 : 827 + m' * 839 < 829 + m' * 839 := Nat.add_lt_add_right (by decide : 827 < 829) _
    have h_lt : 827 + m * 829 < 829 + m' * 839 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 829 = 10 * m' + 2 := by
    have h_eq : m * 829 = m' * 829 + D * 829 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 839 = m' * 829 + 10 * m' := by
      rw [show 839 = 829 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (827 + D * 829) + m' * 829 = (829 + 10 * m') + m' * 829 := by
      calc (827 + D * 829) + m' * 829 = 827 + (D * 829 + m' * 829) := by rw [Nat.add_assoc]
      _ = 827 + (m' * 829 + D * 829) := by rw [Nat.add_comm (D * 829)]
      _ = 829 + (m' * 829 + 10 * m') := h1'
      _ = 829 + (10 * m' + m' * 829) := by rw [Nat.add_comm (m' * 829)]
      _ = (829 + 10 * m') + m' * 829 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 827 + D * 829 = 827 + (10 * m' + 2) := by
      calc 827 + D * 829 = (827 + D * 829) := rfl
      _ = 829 + 10 * m' := h1_sub
      _ = 827 + 2 + 10 * m' := rfl
      _ = 827 + (2 + 10 * m') := by rw [Nat.add_assoc]
      _ = 827 + (10 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 829 ≥ 11 * 829 := Nat.mul_le_mul_right 829 h_gt
    have h2 : 10 * m' + 2 < 11 * 829 := by
      have : 10 * m' < 10 * 829 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 2 < 10 * 829 + 2 := Nat.add_lt_add_right this 2
      calc 10 * m' + 2 < 10 * 829 + 2 := this
      _ ≤ 11 * 829 := by decide
    have h_lt : 11 * 829 < 11 * 829 := by
      calc 11 * 829 ≤ D * 829 := h1
      _ = 10 * m' + 2 := h_alg
      _ < 11 * 829 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 663 := by
    have h_alg_sol : 8 * 829 = 10 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 8 * 829 = 6632 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 6630 = 10 * m' := by
      calc 6630 = 6632 - 2 := rfl
      _ = 10 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 6630 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 6630 / 10 = 663 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_178 (m m' k' : ℕ)
  (h1 : 1061 + m * 1063 = 1063 + m' * 1069)
  (h2 : 1063 + m' * 1069 = 1069 + k' * 1087)
  (hm' : m' < 1063) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1063 ≤ m' * 1063 := Nat.mul_le_mul_right 1063 h_le
    have h_le_mul2 : m' * 1063 ≤ m' * 1069 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1061 + m * 1063 ≤ 1061 + m' * 1063 := Nat.add_le_add_left h_le_mul 1061
    have h_step2 : 1061 + m' * 1063 ≤ 1061 + m' * 1069 := Nat.add_le_add_left h_le_mul2 1061
    have h_step3 : 1061 + m' * 1069 < 1063 + m' * 1069 := Nat.add_lt_add_right (by decide : 1061 < 1063) _
    have h_lt : 1061 + m * 1063 < 1063 + m' * 1069 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1063 = 6 * m' + 2 := by
    have h_eq : m * 1063 = m' * 1063 + D * 1063 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1069 = m' * 1063 + 6 * m' := by
      rw [show 1069 = 1063 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (1061 + D * 1063) + m' * 1063 = (1063 + 6 * m') + m' * 1063 := by
      calc (1061 + D * 1063) + m' * 1063 = 1061 + (D * 1063 + m' * 1063) := by rw [Nat.add_assoc]
      _ = 1061 + (m' * 1063 + D * 1063) := by rw [Nat.add_comm (D * 1063)]
      _ = 1063 + (m' * 1063 + 6 * m') := h1'
      _ = 1063 + (6 * m' + m' * 1063) := by rw [Nat.add_comm (m' * 1063)]
      _ = (1063 + 6 * m') + m' * 1063 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1061 + D * 1063 = 1061 + (6 * m' + 2) := by
      calc 1061 + D * 1063 = (1061 + D * 1063) := rfl
      _ = 1063 + 6 * m' := h1_sub
      _ = 1061 + 2 + 6 * m' := rfl
      _ = 1061 + (2 + 6 * m') := by rw [Nat.add_assoc]
      _ = 1061 + (6 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1063 ≥ 7 * 1063 := Nat.mul_le_mul_right 1063 h_gt
    have h2 : 6 * m' + 2 < 7 * 1063 := by
      have : 6 * m' < 6 * 1063 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 2 < 6 * 1063 + 2 := Nat.add_lt_add_right this 2
      calc 6 * m' + 2 < 6 * 1063 + 2 := this
      _ ≤ 7 * 1063 := by decide
    have h_lt : 7 * 1063 < 7 * 1063 := by
      calc 7 * 1063 ≤ D * 1063 := h1
      _ = 6 * m' + 2 := h_alg
      _ < 7 * 1063 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 354 := by
    have h_alg_sol : 2 * 1063 = 6 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 1063 = 2126 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 2124 = 6 * m' := by
      calc 2124 = 2126 - 2 := rfl
      _ = 6 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 2124 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 2124 / 6 = 354 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_187 (m m' k' : ℕ)
  (h1 : 1117 + m * 1123 = 1123 + m' * 1129)
  (h2 : 1123 + m' * 1129 = 1129 + k' * 1151)
  (hm' : m' < 1123) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1123 ≤ m' * 1123 := Nat.mul_le_mul_right 1123 h_le
    have h_le_mul2 : m' * 1123 ≤ m' * 1129 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1117 + m * 1123 ≤ 1117 + m' * 1123 := Nat.add_le_add_left h_le_mul 1117
    have h_step2 : 1117 + m' * 1123 ≤ 1117 + m' * 1129 := Nat.add_le_add_left h_le_mul2 1117
    have h_step3 : 1117 + m' * 1129 < 1123 + m' * 1129 := Nat.add_lt_add_right (by decide : 1117 < 1123) _
    have h_lt : 1117 + m * 1123 < 1123 + m' * 1129 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1123 = 6 * m' + 6 := by
    have h_eq : m * 1123 = m' * 1123 + D * 1123 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1129 = m' * 1123 + 6 * m' := by
      rw [show 1129 = 1123 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (1117 + D * 1123) + m' * 1123 = (1123 + 6 * m') + m' * 1123 := by
      calc (1117 + D * 1123) + m' * 1123 = 1117 + (D * 1123 + m' * 1123) := by rw [Nat.add_assoc]
      _ = 1117 + (m' * 1123 + D * 1123) := by rw [Nat.add_comm (D * 1123)]
      _ = 1123 + (m' * 1123 + 6 * m') := h1'
      _ = 1123 + (6 * m' + m' * 1123) := by rw [Nat.add_comm (m' * 1123)]
      _ = (1123 + 6 * m') + m' * 1123 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1117 + D * 1123 = 1117 + (6 * m' + 6) := by
      calc 1117 + D * 1123 = (1117 + D * 1123) := rfl
      _ = 1123 + 6 * m' := h1_sub
      _ = 1117 + 6 + 6 * m' := rfl
      _ = 1117 + (6 + 6 * m') := by rw [Nat.add_assoc]
      _ = 1117 + (6 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1123 ≥ 7 * 1123 := Nat.mul_le_mul_right 1123 h_gt
    have h2 : 6 * m' + 6 < 7 * 1123 := by
      have : 6 * m' < 6 * 1123 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 6 < 6 * 1123 + 6 := Nat.add_lt_add_right this 6
      calc 6 * m' + 6 < 6 * 1123 + 6 := this
      _ ≤ 7 * 1123 := by decide
    have h_lt : 7 * 1123 < 7 * 1123 := by
      calc 7 * 1123 ≤ D * 1123 := h1
      _ = 6 * m' + 6 := h_alg
      _ < 7 * 1123 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 6 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
  have hm'_eq : m' = 1122 := by
    have h_alg_sol : 6 * 1123 = 6 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 6 * 1123 = 6738 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 6732 = 6 * m' := by
      calc 6732 = 6738 - 6 := rfl
      _ = 6 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 6732 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 6732 / 6 = 1122 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_203 (m m' k' : ℕ)
  (h1 : 1237 + m * 1249 = 1249 + m' * 1259)
  (h2 : 1249 + m' * 1259 = 1259 + k' * 1277)
  (hm' : m' < 1249) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1249 ≤ m' * 1249 := Nat.mul_le_mul_right 1249 h_le
    have h_le_mul2 : m' * 1249 ≤ m' * 1259 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1237 + m * 1249 ≤ 1237 + m' * 1249 := Nat.add_le_add_left h_le_mul 1237
    have h_step2 : 1237 + m' * 1249 ≤ 1237 + m' * 1259 := Nat.add_le_add_left h_le_mul2 1237
    have h_step3 : 1237 + m' * 1259 < 1249 + m' * 1259 := Nat.add_lt_add_right (by decide : 1237 < 1249) _
    have h_lt : 1237 + m * 1249 < 1249 + m' * 1259 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1249 = 10 * m' + 12 := by
    have h_eq : m * 1249 = m' * 1249 + D * 1249 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1259 = m' * 1249 + 10 * m' := by
      rw [show 1259 = 1249 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (1237 + D * 1249) + m' * 1249 = (1249 + 10 * m') + m' * 1249 := by
      calc (1237 + D * 1249) + m' * 1249 = 1237 + (D * 1249 + m' * 1249) := by rw [Nat.add_assoc]
      _ = 1237 + (m' * 1249 + D * 1249) := by rw [Nat.add_comm (D * 1249)]
      _ = 1249 + (m' * 1249 + 10 * m') := h1'
      _ = 1249 + (10 * m' + m' * 1249) := by rw [Nat.add_comm (m' * 1249)]
      _ = (1249 + 10 * m') + m' * 1249 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1237 + D * 1249 = 1237 + (10 * m' + 12) := by
      calc 1237 + D * 1249 = (1237 + D * 1249) := rfl
      _ = 1249 + 10 * m' := h1_sub
      _ = 1237 + 12 + 10 * m' := rfl
      _ = 1237 + (12 + 10 * m') := by rw [Nat.add_assoc]
      _ = 1237 + (10 * m' + 12) := by rw [Nat.add_comm 12]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1249 ≥ 11 * 1249 := Nat.mul_le_mul_right 1249 h_gt
    have h2 : 10 * m' + 12 < 11 * 1249 := by
      have : 10 * m' < 10 * 1249 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 12 < 10 * 1249 + 12 := Nat.add_lt_add_right this 12
      calc 10 * m' + 12 < 10 * 1249 + 12 := this
      _ ≤ 11 * 1249 := by decide
    have h_lt : 11 * 1249 < 11 * 1249 := by
      calc 11 * 1249 ≤ D * 1249 := h1
      _ = 10 * m' + 12 := h_alg
      _ < 11 * 1249 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 998 := by
    have h_alg_sol : 8 * 1249 = 10 * m' + 12 := h_D_eq ▸ h_alg
    have h_eval : 8 * 1249 = 9992 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 9980 = 10 * m' := by
      calc 9980 = 9992 - 12 := rfl
      _ = 10 * m' + 12 - 12 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 9980 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 9980 / 10 = 998 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_215 (m m' k' : ℕ)
  (h1 : 1319 + m * 1321 = 1321 + m' * 1327)
  (h2 : 1321 + m' * 1327 = 1327 + k' * 1361)
  (hm' : m' < 1321) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1321 ≤ m' * 1321 := Nat.mul_le_mul_right 1321 h_le
    have h_le_mul2 : m' * 1321 ≤ m' * 1327 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1319 + m * 1321 ≤ 1319 + m' * 1321 := Nat.add_le_add_left h_le_mul 1319
    have h_step2 : 1319 + m' * 1321 ≤ 1319 + m' * 1327 := Nat.add_le_add_left h_le_mul2 1319
    have h_step3 : 1319 + m' * 1327 < 1321 + m' * 1327 := Nat.add_lt_add_right (by decide : 1319 < 1321) _
    have h_lt : 1319 + m * 1321 < 1321 + m' * 1327 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1321 = 6 * m' + 2 := by
    have h_eq : m * 1321 = m' * 1321 + D * 1321 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1327 = m' * 1321 + 6 * m' := by
      rw [show 1327 = 1321 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (1319 + D * 1321) + m' * 1321 = (1321 + 6 * m') + m' * 1321 := by
      calc (1319 + D * 1321) + m' * 1321 = 1319 + (D * 1321 + m' * 1321) := by rw [Nat.add_assoc]
      _ = 1319 + (m' * 1321 + D * 1321) := by rw [Nat.add_comm (D * 1321)]
      _ = 1321 + (m' * 1321 + 6 * m') := h1'
      _ = 1321 + (6 * m' + m' * 1321) := by rw [Nat.add_comm (m' * 1321)]
      _ = (1321 + 6 * m') + m' * 1321 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1319 + D * 1321 = 1319 + (6 * m' + 2) := by
      calc 1319 + D * 1321 = (1319 + D * 1321) := rfl
      _ = 1321 + 6 * m' := h1_sub
      _ = 1319 + 2 + 6 * m' := rfl
      _ = 1319 + (2 + 6 * m') := by rw [Nat.add_assoc]
      _ = 1319 + (6 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1321 ≥ 7 * 1321 := Nat.mul_le_mul_right 1321 h_gt
    have h2 : 6 * m' + 2 < 7 * 1321 := by
      have : 6 * m' < 6 * 1321 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 2 < 6 * 1321 + 2 := Nat.add_lt_add_right this 2
      calc 6 * m' + 2 < 6 * 1321 + 2 := this
      _ ≤ 7 * 1321 := by decide
    have h_lt : 7 * 1321 < 7 * 1321 := by
      calc 7 * 1321 ≤ D * 1321 := h1
      _ = 6 * m' + 2 := h_alg
      _ < 7 * 1321 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 440 := by
    have h_alg_sol : 2 * 1321 = 6 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 1321 = 2642 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 2640 = 6 * m' := by
      calc 2640 = 2642 - 2 := rfl
      _ = 6 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 2640 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 2640 / 6 = 440 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_216 (m m' k' : ℕ)
  (h1 : 1321 + m * 1327 = 1327 + m' * 1361)
  (h2 : 1327 + m' * 1361 = 1361 + k' * 1367)
  (hm' : m' < 1327) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1327 ≤ m' * 1327 := Nat.mul_le_mul_right 1327 h_le
    have h_le_mul2 : m' * 1327 ≤ m' * 1361 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1321 + m * 1327 ≤ 1321 + m' * 1327 := Nat.add_le_add_left h_le_mul 1321
    have h_step2 : 1321 + m' * 1327 ≤ 1321 + m' * 1361 := Nat.add_le_add_left h_le_mul2 1321
    have h_step3 : 1321 + m' * 1361 < 1327 + m' * 1361 := Nat.add_lt_add_right (by decide : 1321 < 1327) _
    have h_lt : 1321 + m * 1327 < 1327 + m' * 1361 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1327 = 34 * m' + 6 := by
    have h_eq : m * 1327 = m' * 1327 + D * 1327 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1361 = m' * 1327 + 34 * m' := by
      rw [show 1361 = 1327 + 34 by decide, Nat.mul_add, Nat.mul_comm m' 34]
    rw [h_dist] at h1'
    have h1_assoc : (1321 + D * 1327) + m' * 1327 = (1327 + 34 * m') + m' * 1327 := by
      calc (1321 + D * 1327) + m' * 1327 = 1321 + (D * 1327 + m' * 1327) := by rw [Nat.add_assoc]
      _ = 1321 + (m' * 1327 + D * 1327) := by rw [Nat.add_comm (D * 1327)]
      _ = 1327 + (m' * 1327 + 34 * m') := h1'
      _ = 1327 + (34 * m' + m' * 1327) := by rw [Nat.add_comm (m' * 1327)]
      _ = (1327 + 34 * m') + m' * 1327 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1321 + D * 1327 = 1321 + (34 * m' + 6) := by
      calc 1321 + D * 1327 = (1321 + D * 1327) := rfl
      _ = 1327 + 34 * m' := h1_sub
      _ = 1321 + 6 + 34 * m' := rfl
      _ = 1321 + (6 + 34 * m') := by rw [Nat.add_assoc]
      _ = 1321 + (34 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 34 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1327 ≥ 35 * 1327 := Nat.mul_le_mul_right 1327 h_gt
    have h2 : 34 * m' + 6 < 35 * 1327 := by
      have : 34 * m' < 34 * 1327 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 34 * m' + 6 < 34 * 1327 + 6 := Nat.add_lt_add_right this 6
      calc 34 * m' + 6 < 34 * 1327 + 6 := this
      _ ≤ 35 * 1327 := by decide
    have h_lt : 35 * 1327 < 35 * 1327 := by
      calc 35 * 1327 ≤ D * 1327 := h1
      _ = 34 * m' + 6 := h_alg
      _ < 35 * 1327 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 ∨ D = 31 ∨ D = 32 ∨ D = 33 ∨ D = 34 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 6 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 234 := by
    have h_alg_sol : 6 * 1327 = 34 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 6 * 1327 = 7962 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 7956 = 34 * m' := by
      calc 7956 = 7962 - 6 := rfl
      _ = 34 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 34 * m' := rfl
    have h_div : 7956 / 34 = (34 * m') / 34 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 34)] at h_div
    have h_div_eval : 7956 / 34 = 234 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_219 (m m' k' : ℕ)
  (h1 : 1367 + m * 1373 = 1373 + m' * 1381)
  (h2 : 1373 + m' * 1381 = 1381 + k' * 1399)
  (hm' : m' < 1373) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1373 ≤ m' * 1373 := Nat.mul_le_mul_right 1373 h_le
    have h_le_mul2 : m' * 1373 ≤ m' * 1381 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1367 + m * 1373 ≤ 1367 + m' * 1373 := Nat.add_le_add_left h_le_mul 1367
    have h_step2 : 1367 + m' * 1373 ≤ 1367 + m' * 1381 := Nat.add_le_add_left h_le_mul2 1367
    have h_step3 : 1367 + m' * 1381 < 1373 + m' * 1381 := Nat.add_lt_add_right (by decide : 1367 < 1373) _
    have h_lt : 1367 + m * 1373 < 1373 + m' * 1381 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1373 = 8 * m' + 6 := by
    have h_eq : m * 1373 = m' * 1373 + D * 1373 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1381 = m' * 1373 + 8 * m' := by
      rw [show 1381 = 1373 + 8 by decide, Nat.mul_add, Nat.mul_comm m' 8]
    rw [h_dist] at h1'
    have h1_assoc : (1367 + D * 1373) + m' * 1373 = (1373 + 8 * m') + m' * 1373 := by
      calc (1367 + D * 1373) + m' * 1373 = 1367 + (D * 1373 + m' * 1373) := by rw [Nat.add_assoc]
      _ = 1367 + (m' * 1373 + D * 1373) := by rw [Nat.add_comm (D * 1373)]
      _ = 1373 + (m' * 1373 + 8 * m') := h1'
      _ = 1373 + (8 * m' + m' * 1373) := by rw [Nat.add_comm (m' * 1373)]
      _ = (1373 + 8 * m') + m' * 1373 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1367 + D * 1373 = 1367 + (8 * m' + 6) := by
      calc 1367 + D * 1373 = (1367 + D * 1373) := rfl
      _ = 1373 + 8 * m' := h1_sub
      _ = 1367 + 6 + 8 * m' := rfl
      _ = 1367 + (6 + 8 * m') := by rw [Nat.add_assoc]
      _ = 1367 + (8 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 8 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1373 ≥ 9 * 1373 := Nat.mul_le_mul_right 1373 h_gt
    have h2 : 8 * m' + 6 < 9 * 1373 := by
      have : 8 * m' < 8 * 1373 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 8 * m' + 6 < 8 * 1373 + 6 := Nat.add_lt_add_right this 6
      calc 8 * m' + 6 < 8 * 1373 + 6 := this
      _ ≤ 9 * 1373 := by decide
    have h_lt : 9 * 1373 < 9 * 1373 := by
      calc 9 * 1373 ≤ D * 1373 := h1
      _ = 8 * m' + 6 := h_alg
      _ < 9 * 1373 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 6 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 1029 := by
    have h_alg_sol : 6 * 1373 = 8 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 6 * 1373 = 8238 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 8232 = 8 * m' := by
      calc 8232 = 8238 - 6 := rfl
      _ = 8 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 8 * m' := rfl
    have h_div : 8232 / 8 = (8 * m') / 8 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 8)] at h_div
    have h_div_eval : 8232 / 8 = 1029 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_220 (m m' k' : ℕ)
  (h1 : 1373 + m * 1381 = 1381 + m' * 1399)
  (h2 : 1381 + m' * 1399 = 1399 + k' * 1409)
  (hm' : m' < 1381) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1381 ≤ m' * 1381 := Nat.mul_le_mul_right 1381 h_le
    have h_le_mul2 : m' * 1381 ≤ m' * 1399 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1373 + m * 1381 ≤ 1373 + m' * 1381 := Nat.add_le_add_left h_le_mul 1373
    have h_step2 : 1373 + m' * 1381 ≤ 1373 + m' * 1399 := Nat.add_le_add_left h_le_mul2 1373
    have h_step3 : 1373 + m' * 1399 < 1381 + m' * 1399 := Nat.add_lt_add_right (by decide : 1373 < 1381) _
    have h_lt : 1373 + m * 1381 < 1381 + m' * 1399 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1381 = 18 * m' + 8 := by
    have h_eq : m * 1381 = m' * 1381 + D * 1381 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1399 = m' * 1381 + 18 * m' := by
      rw [show 1399 = 1381 + 18 by decide, Nat.mul_add, Nat.mul_comm m' 18]
    rw [h_dist] at h1'
    have h1_assoc : (1373 + D * 1381) + m' * 1381 = (1381 + 18 * m') + m' * 1381 := by
      calc (1373 + D * 1381) + m' * 1381 = 1373 + (D * 1381 + m' * 1381) := by rw [Nat.add_assoc]
      _ = 1373 + (m' * 1381 + D * 1381) := by rw [Nat.add_comm (D * 1381)]
      _ = 1381 + (m' * 1381 + 18 * m') := h1'
      _ = 1381 + (18 * m' + m' * 1381) := by rw [Nat.add_comm (m' * 1381)]
      _ = (1381 + 18 * m') + m' * 1381 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1373 + D * 1381 = 1373 + (18 * m' + 8) := by
      calc 1373 + D * 1381 = (1373 + D * 1381) := rfl
      _ = 1381 + 18 * m' := h1_sub
      _ = 1373 + 8 + 18 * m' := rfl
      _ = 1373 + (8 + 18 * m') := by rw [Nat.add_assoc]
      _ = 1373 + (18 * m' + 8) := by rw [Nat.add_comm 8]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 18 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1381 ≥ 19 * 1381 := Nat.mul_le_mul_right 1381 h_gt
    have h2 : 18 * m' + 8 < 19 * 1381 := by
      have : 18 * m' < 18 * 1381 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 18 * m' + 8 < 18 * 1381 + 8 := Nat.add_lt_add_right this 8
      calc 18 * m' + 8 < 18 * 1381 + 8 := this
      _ ≤ 19 * 1381 := by decide
    have h_lt : 19 * 1381 < 19 * 1381 := by
      calc 19 * 1381 ≤ D * 1381 := h1
      _ = 18 * m' + 8 := h_alg
      _ < 19 * 1381 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 153 := by
    have h_alg_sol : 2 * 1381 = 18 * m' + 8 := h_D_eq ▸ h_alg
    have h_eval : 2 * 1381 = 2762 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 2754 = 18 * m' := by
      calc 2754 = 2762 - 8 := rfl
      _ = 18 * m' + 8 - 8 := by rw [h_alg_sol]
      _ = 18 * m' := rfl
    have h_div : 2754 / 18 = (18 * m') / 18 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 18)] at h_div
    have h_div_eval : 2754 / 18 = 153 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_221 (m m' k' : ℕ)
  (h1 : 1381 + m * 1399 = 1399 + m' * 1409)
  (h2 : 1399 + m' * 1409 = 1409 + k' * 1423)
  (hm' : m' < 1399) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1399 ≤ m' * 1399 := Nat.mul_le_mul_right 1399 h_le
    have h_le_mul2 : m' * 1399 ≤ m' * 1409 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1381 + m * 1399 ≤ 1381 + m' * 1399 := Nat.add_le_add_left h_le_mul 1381
    have h_step2 : 1381 + m' * 1399 ≤ 1381 + m' * 1409 := Nat.add_le_add_left h_le_mul2 1381
    have h_step3 : 1381 + m' * 1409 < 1399 + m' * 1409 := Nat.add_lt_add_right (by decide : 1381 < 1399) _
    have h_lt : 1381 + m * 1399 < 1399 + m' * 1409 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1399 = 10 * m' + 18 := by
    have h_eq : m * 1399 = m' * 1399 + D * 1399 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1409 = m' * 1399 + 10 * m' := by
      rw [show 1409 = 1399 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (1381 + D * 1399) + m' * 1399 = (1399 + 10 * m') + m' * 1399 := by
      calc (1381 + D * 1399) + m' * 1399 = 1381 + (D * 1399 + m' * 1399) := by rw [Nat.add_assoc]
      _ = 1381 + (m' * 1399 + D * 1399) := by rw [Nat.add_comm (D * 1399)]
      _ = 1399 + (m' * 1399 + 10 * m') := h1'
      _ = 1399 + (10 * m' + m' * 1399) := by rw [Nat.add_comm (m' * 1399)]
      _ = (1399 + 10 * m') + m' * 1399 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1381 + D * 1399 = 1381 + (10 * m' + 18) := by
      calc 1381 + D * 1399 = (1381 + D * 1399) := rfl
      _ = 1399 + 10 * m' := h1_sub
      _ = 1381 + 18 + 10 * m' := rfl
      _ = 1381 + (18 + 10 * m') := by rw [Nat.add_assoc]
      _ = 1381 + (10 * m' + 18) := by rw [Nat.add_comm 18]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1399 ≥ 11 * 1399 := Nat.mul_le_mul_right 1399 h_gt
    have h2 : 10 * m' + 18 < 11 * 1399 := by
      have : 10 * m' < 10 * 1399 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 18 < 10 * 1399 + 18 := Nat.add_lt_add_right this 18
      calc 10 * m' + 18 < 10 * 1399 + 18 := this
      _ ≤ 11 * 1399 := by decide
    have h_lt : 11 * 1399 < 11 * 1399 := by
      calc 11 * 1399 ≤ D * 1399 := h1
      _ = 10 * m' + 18 := h_alg
      _ < 11 * 1399 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 278 := by
    have h_alg_sol : 2 * 1399 = 10 * m' + 18 := h_D_eq ▸ h_alg
    have h_eval : 2 * 1399 = 2798 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 2780 = 10 * m' := by
      calc 2780 = 2798 - 18 := rfl
      _ = 10 * m' + 18 - 18 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 2780 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 2780 / 10 = 278 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_257 (m m' k' : ℕ)
  (h1 : 1621 + m * 1627 = 1627 + m' * 1637)
  (h2 : 1627 + m' * 1637 = 1637 + k' * 1657)
  (hm' : m' < 1627) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1627 ≤ m' * 1627 := Nat.mul_le_mul_right 1627 h_le
    have h_le_mul2 : m' * 1627 ≤ m' * 1637 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1621 + m * 1627 ≤ 1621 + m' * 1627 := Nat.add_le_add_left h_le_mul 1621
    have h_step2 : 1621 + m' * 1627 ≤ 1621 + m' * 1637 := Nat.add_le_add_left h_le_mul2 1621
    have h_step3 : 1621 + m' * 1637 < 1627 + m' * 1637 := Nat.add_lt_add_right (by decide : 1621 < 1627) _
    have h_lt : 1621 + m * 1627 < 1627 + m' * 1637 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1627 = 10 * m' + 6 := by
    have h_eq : m * 1627 = m' * 1627 + D * 1627 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1637 = m' * 1627 + 10 * m' := by
      rw [show 1637 = 1627 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (1621 + D * 1627) + m' * 1627 = (1627 + 10 * m') + m' * 1627 := by
      calc (1621 + D * 1627) + m' * 1627 = 1621 + (D * 1627 + m' * 1627) := by rw [Nat.add_assoc]
      _ = 1621 + (m' * 1627 + D * 1627) := by rw [Nat.add_comm (D * 1627)]
      _ = 1627 + (m' * 1627 + 10 * m') := h1'
      _ = 1627 + (10 * m' + m' * 1627) := by rw [Nat.add_comm (m' * 1627)]
      _ = (1627 + 10 * m') + m' * 1627 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1621 + D * 1627 = 1621 + (10 * m' + 6) := by
      calc 1621 + D * 1627 = (1621 + D * 1627) := rfl
      _ = 1627 + 10 * m' := h1_sub
      _ = 1621 + 6 + 10 * m' := rfl
      _ = 1621 + (6 + 10 * m') := by rw [Nat.add_assoc]
      _ = 1621 + (10 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1627 ≥ 11 * 1627 := Nat.mul_le_mul_right 1627 h_gt
    have h2 : 10 * m' + 6 < 11 * 1627 := by
      have : 10 * m' < 10 * 1627 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 6 < 10 * 1627 + 6 := Nat.add_lt_add_right this 6
      calc 10 * m' + 6 < 10 * 1627 + 6 := this
      _ ≤ 11 * 1627 := by decide
    have h_lt : 11 * 1627 < 11 * 1627 := by
      calc 11 * 1627 ≤ D * 1627 := h1
      _ = 10 * m' + 6 := h_alg
      _ < 11 * 1627 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 1301 := by
    have h_alg_sol : 8 * 1627 = 10 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 8 * 1627 = 13016 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 13010 = 10 * m' := by
      calc 13010 = 13016 - 6 := rfl
      _ = 10 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 13010 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 13010 / 10 = 1301 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_281 (m m' k' : ℕ)
  (h1 : 1823 + m * 1831 = 1831 + m' * 1847)
  (h2 : 1831 + m' * 1847 = 1847 + k' * 1861)
  (hm' : m' < 1831) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1831 ≤ m' * 1831 := Nat.mul_le_mul_right 1831 h_le
    have h_le_mul2 : m' * 1831 ≤ m' * 1847 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1823 + m * 1831 ≤ 1823 + m' * 1831 := Nat.add_le_add_left h_le_mul 1823
    have h_step2 : 1823 + m' * 1831 ≤ 1823 + m' * 1847 := Nat.add_le_add_left h_le_mul2 1823
    have h_step3 : 1823 + m' * 1847 < 1831 + m' * 1847 := Nat.add_lt_add_right (by decide : 1823 < 1831) _
    have h_lt : 1823 + m * 1831 < 1831 + m' * 1847 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1831 = 16 * m' + 8 := by
    have h_eq : m * 1831 = m' * 1831 + D * 1831 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1847 = m' * 1831 + 16 * m' := by
      rw [show 1847 = 1831 + 16 by decide, Nat.mul_add, Nat.mul_comm m' 16]
    rw [h_dist] at h1'
    have h1_assoc : (1823 + D * 1831) + m' * 1831 = (1831 + 16 * m') + m' * 1831 := by
      calc (1823 + D * 1831) + m' * 1831 = 1823 + (D * 1831 + m' * 1831) := by rw [Nat.add_assoc]
      _ = 1823 + (m' * 1831 + D * 1831) := by rw [Nat.add_comm (D * 1831)]
      _ = 1831 + (m' * 1831 + 16 * m') := h1'
      _ = 1831 + (16 * m' + m' * 1831) := by rw [Nat.add_comm (m' * 1831)]
      _ = (1831 + 16 * m') + m' * 1831 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1823 + D * 1831 = 1823 + (16 * m' + 8) := by
      calc 1823 + D * 1831 = (1823 + D * 1831) := rfl
      _ = 1831 + 16 * m' := h1_sub
      _ = 1823 + 8 + 16 * m' := rfl
      _ = 1823 + (8 + 16 * m') := by rw [Nat.add_assoc]
      _ = 1823 + (16 * m' + 8) := by rw [Nat.add_comm 8]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 16 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1831 ≥ 17 * 1831 := Nat.mul_le_mul_right 1831 h_gt
    have h2 : 16 * m' + 8 < 17 * 1831 := by
      have : 16 * m' < 16 * 1831 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 16 * m' + 8 < 16 * 1831 + 8 := Nat.add_lt_add_right this 8
      calc 16 * m' + 8 < 16 * 1831 + 8 := this
      _ ≤ 17 * 1831 := by decide
    have h_lt : 17 * 1831 < 17 * 1831 := by
      calc 17 * 1831 ≤ D * 1831 := h1
      _ = 16 * m' + 8 := h_alg
      _ < 17 * 1831 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 915 := by
    have h_alg_sol : 8 * 1831 = 16 * m' + 8 := h_D_eq ▸ h_alg
    have h_eval : 8 * 1831 = 14648 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 14640 = 16 * m' := by
      calc 14640 = 14648 - 8 := rfl
      _ = 16 * m' + 8 - 8 := by rw [h_alg_sol]
      _ = 16 * m' := rfl
    have h_div : 14640 / 16 = (16 * m') / 16 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 16)] at h_div
    have h_div_eval : 14640 / 16 = 915 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_325 (m m' k' : ℕ)
  (h1 : 2153 + m * 2161 = 2161 + m' * 2179)
  (h2 : 2161 + m' * 2179 = 2179 + k' * 2203)
  (hm' : m' < 2161) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 2161 ≤ m' * 2161 := Nat.mul_le_mul_right 2161 h_le
    have h_le_mul2 : m' * 2161 ≤ m' * 2179 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 2153 + m * 2161 ≤ 2153 + m' * 2161 := Nat.add_le_add_left h_le_mul 2153
    have h_step2 : 2153 + m' * 2161 ≤ 2153 + m' * 2179 := Nat.add_le_add_left h_le_mul2 2153
    have h_step3 : 2153 + m' * 2179 < 2161 + m' * 2179 := Nat.add_lt_add_right (by decide : 2153 < 2161) _
    have h_lt : 2153 + m * 2161 < 2161 + m' * 2179 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 2161 = 18 * m' + 8 := by
    have h_eq : m * 2161 = m' * 2161 + D * 2161 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 2179 = m' * 2161 + 18 * m' := by
      rw [show 2179 = 2161 + 18 by decide, Nat.mul_add, Nat.mul_comm m' 18]
    rw [h_dist] at h1'
    have h1_assoc : (2153 + D * 2161) + m' * 2161 = (2161 + 18 * m') + m' * 2161 := by
      calc (2153 + D * 2161) + m' * 2161 = 2153 + (D * 2161 + m' * 2161) := by rw [Nat.add_assoc]
      _ = 2153 + (m' * 2161 + D * 2161) := by rw [Nat.add_comm (D * 2161)]
      _ = 2161 + (m' * 2161 + 18 * m') := h1'
      _ = 2161 + (18 * m' + m' * 2161) := by rw [Nat.add_comm (m' * 2161)]
      _ = (2161 + 18 * m') + m' * 2161 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 2153 + D * 2161 = 2153 + (18 * m' + 8) := by
      calc 2153 + D * 2161 = (2153 + D * 2161) := rfl
      _ = 2161 + 18 * m' := h1_sub
      _ = 2153 + 8 + 18 * m' := rfl
      _ = 2153 + (8 + 18 * m') := by rw [Nat.add_assoc]
      _ = 2153 + (18 * m' + 8) := by rw [Nat.add_comm 8]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 18 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 2161 ≥ 19 * 2161 := Nat.mul_le_mul_right 2161 h_gt
    have h2 : 18 * m' + 8 < 19 * 2161 := by
      have : 18 * m' < 18 * 2161 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 18 * m' + 8 < 18 * 2161 + 8 := Nat.add_lt_add_right this 8
      calc 18 * m' + 8 < 18 * 2161 + 8 := this
      _ ≤ 19 * 2161 := by decide
    have h_lt : 19 * 2161 < 19 * 2161 := by
      calc 19 * 2161 ≤ D * 2161 := h1
      _ = 18 * m' + 8 := h_alg
      _ < 19 * 2161 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 960 := by
    have h_alg_sol : 8 * 2161 = 18 * m' + 8 := h_D_eq ▸ h_alg
    have h_eval : 8 * 2161 = 17288 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 17280 = 18 * m' := by
      calc 17280 = 17288 - 8 := rfl
      _ = 18 * m' + 8 - 8 := by rw [h_alg_sol]
      _ = 18 * m' := rfl
    have h_div : 17280 / 18 = (18 * m') / 18 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 18)] at h_div
    have h_div_eval : 17280 / 18 = 960 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_366 (m m' k' : ℕ)
  (h1 : 2473 + m * 2477 = 2477 + m' * 2503)
  (h2 : 2477 + m' * 2503 = 2503 + k' * 2521)
  (hm' : m' < 2477) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 2477 ≤ m' * 2477 := Nat.mul_le_mul_right 2477 h_le
    have h_le_mul2 : m' * 2477 ≤ m' * 2503 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 2473 + m * 2477 ≤ 2473 + m' * 2477 := Nat.add_le_add_left h_le_mul 2473
    have h_step2 : 2473 + m' * 2477 ≤ 2473 + m' * 2503 := Nat.add_le_add_left h_le_mul2 2473
    have h_step3 : 2473 + m' * 2503 < 2477 + m' * 2503 := Nat.add_lt_add_right (by decide : 2473 < 2477) _
    have h_lt : 2473 + m * 2477 < 2477 + m' * 2503 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 2477 = 26 * m' + 4 := by
    have h_eq : m * 2477 = m' * 2477 + D * 2477 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 2503 = m' * 2477 + 26 * m' := by
      rw [show 2503 = 2477 + 26 by decide, Nat.mul_add, Nat.mul_comm m' 26]
    rw [h_dist] at h1'
    have h1_assoc : (2473 + D * 2477) + m' * 2477 = (2477 + 26 * m') + m' * 2477 := by
      calc (2473 + D * 2477) + m' * 2477 = 2473 + (D * 2477 + m' * 2477) := by rw [Nat.add_assoc]
      _ = 2473 + (m' * 2477 + D * 2477) := by rw [Nat.add_comm (D * 2477)]
      _ = 2477 + (m' * 2477 + 26 * m') := h1'
      _ = 2477 + (26 * m' + m' * 2477) := by rw [Nat.add_comm (m' * 2477)]
      _ = (2477 + 26 * m') + m' * 2477 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 2473 + D * 2477 = 2473 + (26 * m' + 4) := by
      calc 2473 + D * 2477 = (2473 + D * 2477) := rfl
      _ = 2477 + 26 * m' := h1_sub
      _ = 2473 + 4 + 26 * m' := rfl
      _ = 2473 + (4 + 26 * m') := by rw [Nat.add_assoc]
      _ = 2473 + (26 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 26 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 2477 ≥ 27 * 2477 := Nat.mul_le_mul_right 2477 h_gt
    have h2 : 26 * m' + 4 < 27 * 2477 := by
      have : 26 * m' < 26 * 2477 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 26 * m' + 4 < 26 * 2477 + 4 := Nat.add_lt_add_right this 4
      calc 26 * m' + 4 < 26 * 2477 + 4 := this
      _ ≤ 27 * 2477 := by decide
    have h_lt : 27 * 2477 < 27 * 2477 := by
      calc 27 * 2477 ≤ D * 2477 := h1
      _ = 26 * m' + 4 := h_alg
      _ < 27 * 2477 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 762 := by
    have h_alg_sol : 8 * 2477 = 26 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 8 * 2477 = 19816 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 19812 = 26 * m' := by
      calc 19812 = 19816 - 4 := rfl
      _ = 26 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 26 * m' := rfl
    have h_div : 19812 / 26 = (26 * m') / 26 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 26)] at h_div
    have h_div_eval : 19812 / 26 = 762 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_374 (m m' k' : ℕ)
  (h1 : 2551 + m * 2557 = 2557 + m' * 2579)
  (h2 : 2557 + m' * 2579 = 2579 + k' * 2591)
  (hm' : m' < 2557) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 2557 ≤ m' * 2557 := Nat.mul_le_mul_right 2557 h_le
    have h_le_mul2 : m' * 2557 ≤ m' * 2579 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 2551 + m * 2557 ≤ 2551 + m' * 2557 := Nat.add_le_add_left h_le_mul 2551
    have h_step2 : 2551 + m' * 2557 ≤ 2551 + m' * 2579 := Nat.add_le_add_left h_le_mul2 2551
    have h_step3 : 2551 + m' * 2579 < 2557 + m' * 2579 := Nat.add_lt_add_right (by decide : 2551 < 2557) _
    have h_lt : 2551 + m * 2557 < 2557 + m' * 2579 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 2557 = 22 * m' + 6 := by
    have h_eq : m * 2557 = m' * 2557 + D * 2557 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 2579 = m' * 2557 + 22 * m' := by
      rw [show 2579 = 2557 + 22 by decide, Nat.mul_add, Nat.mul_comm m' 22]
    rw [h_dist] at h1'
    have h1_assoc : (2551 + D * 2557) + m' * 2557 = (2557 + 22 * m') + m' * 2557 := by
      calc (2551 + D * 2557) + m' * 2557 = 2551 + (D * 2557 + m' * 2557) := by rw [Nat.add_assoc]
      _ = 2551 + (m' * 2557 + D * 2557) := by rw [Nat.add_comm (D * 2557)]
      _ = 2557 + (m' * 2557 + 22 * m') := h1'
      _ = 2557 + (22 * m' + m' * 2557) := by rw [Nat.add_comm (m' * 2557)]
      _ = (2557 + 22 * m') + m' * 2557 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 2551 + D * 2557 = 2551 + (22 * m' + 6) := by
      calc 2551 + D * 2557 = (2551 + D * 2557) := rfl
      _ = 2557 + 22 * m' := h1_sub
      _ = 2551 + 6 + 22 * m' := rfl
      _ = 2551 + (6 + 22 * m') := by rw [Nat.add_assoc]
      _ = 2551 + (22 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 22 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 2557 ≥ 23 * 2557 := Nat.mul_le_mul_right 2557 h_gt
    have h2 : 22 * m' + 6 < 23 * 2557 := by
      have : 22 * m' < 22 * 2557 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 22 * m' + 6 < 22 * 2557 + 6 := Nat.add_lt_add_right this 6
      calc 22 * m' + 6 < 22 * 2557 + 6 := this
      _ ≤ 23 * 2557 := by decide
    have h_lt : 23 * 2557 < 23 * 2557 := by
      calc 23 * 2557 ≤ D * 2557 := h1
      _ = 22 * m' + 6 := h_alg
      _ < 23 * 2557 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 10 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 1162 := by
    have h_alg_sol : 10 * 2557 = 22 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 10 * 2557 = 25570 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 25564 = 22 * m' := by
      calc 25564 = 25570 - 6 := rfl
      _ = 22 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 22 * m' := rfl
    have h_div : 25564 / 22 = (22 * m') / 22 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 22)] at h_div
    have h_div_eval : 25564 / 22 = 1162 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_444 (m m' k' : ℕ)
  (h1 : 3119 + m * 3121 = 3121 + m' * 3137)
  (h2 : 3121 + m' * 3137 = 3137 + k' * 3163)
  (hm' : m' < 3121) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 3121 ≤ m' * 3121 := Nat.mul_le_mul_right 3121 h_le
    have h_le_mul2 : m' * 3121 ≤ m' * 3137 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 3119 + m * 3121 ≤ 3119 + m' * 3121 := Nat.add_le_add_left h_le_mul 3119
    have h_step2 : 3119 + m' * 3121 ≤ 3119 + m' * 3137 := Nat.add_le_add_left h_le_mul2 3119
    have h_step3 : 3119 + m' * 3137 < 3121 + m' * 3137 := Nat.add_lt_add_right (by decide : 3119 < 3121) _
    have h_lt : 3119 + m * 3121 < 3121 + m' * 3137 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 3121 = 16 * m' + 2 := by
    have h_eq : m * 3121 = m' * 3121 + D * 3121 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 3137 = m' * 3121 + 16 * m' := by
      rw [show 3137 = 3121 + 16 by decide, Nat.mul_add, Nat.mul_comm m' 16]
    rw [h_dist] at h1'
    have h1_assoc : (3119 + D * 3121) + m' * 3121 = (3121 + 16 * m') + m' * 3121 := by
      calc (3119 + D * 3121) + m' * 3121 = 3119 + (D * 3121 + m' * 3121) := by rw [Nat.add_assoc]
      _ = 3119 + (m' * 3121 + D * 3121) := by rw [Nat.add_comm (D * 3121)]
      _ = 3121 + (m' * 3121 + 16 * m') := h1'
      _ = 3121 + (16 * m' + m' * 3121) := by rw [Nat.add_comm (m' * 3121)]
      _ = (3121 + 16 * m') + m' * 3121 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 3119 + D * 3121 = 3119 + (16 * m' + 2) := by
      calc 3119 + D * 3121 = (3119 + D * 3121) := rfl
      _ = 3121 + 16 * m' := h1_sub
      _ = 3119 + 2 + 16 * m' := rfl
      _ = 3119 + (2 + 16 * m') := by rw [Nat.add_assoc]
      _ = 3119 + (16 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 16 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 3121 ≥ 17 * 3121 := Nat.mul_le_mul_right 3121 h_gt
    have h2 : 16 * m' + 2 < 17 * 3121 := by
      have : 16 * m' < 16 * 3121 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 16 * m' + 2 < 16 * 3121 + 2 := Nat.add_lt_add_right this 2
      calc 16 * m' + 2 < 16 * 3121 + 2 := this
      _ ≤ 17 * 3121 := by decide
    have h_lt : 17 * 3121 < 17 * 3121 := by
      calc 17 * 3121 ≤ D * 3121 := h1
      _ = 16 * m' + 2 := h_alg
      _ < 17 * 3121 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 390 := by
    have h_alg_sol : 2 * 3121 = 16 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 3121 = 6242 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 6240 = 16 * m' := by
      calc 6240 = 6242 - 2 := rfl
      _ = 16 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 16 * m' := rfl
    have h_div : 6240 / 16 = (16 * m') / 16 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 16)] at h_div
    have h_div_eval : 6240 / 16 = 390 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_460 (m m' k' : ℕ)
  (h1 : 3257 + m * 3259 = 3259 + m' * 3271)
  (h2 : 3259 + m' * 3271 = 3271 + k' * 3299)
  (hm' : m' < 3259) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 3259 ≤ m' * 3259 := Nat.mul_le_mul_right 3259 h_le
    have h_le_mul2 : m' * 3259 ≤ m' * 3271 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 3257 + m * 3259 ≤ 3257 + m' * 3259 := Nat.add_le_add_left h_le_mul 3257
    have h_step2 : 3257 + m' * 3259 ≤ 3257 + m' * 3271 := Nat.add_le_add_left h_le_mul2 3257
    have h_step3 : 3257 + m' * 3271 < 3259 + m' * 3271 := Nat.add_lt_add_right (by decide : 3257 < 3259) _
    have h_lt : 3257 + m * 3259 < 3259 + m' * 3271 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 3259 = 12 * m' + 2 := by
    have h_eq : m * 3259 = m' * 3259 + D * 3259 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 3271 = m' * 3259 + 12 * m' := by
      rw [show 3271 = 3259 + 12 by decide, Nat.mul_add, Nat.mul_comm m' 12]
    rw [h_dist] at h1'
    have h1_assoc : (3257 + D * 3259) + m' * 3259 = (3259 + 12 * m') + m' * 3259 := by
      calc (3257 + D * 3259) + m' * 3259 = 3257 + (D * 3259 + m' * 3259) := by rw [Nat.add_assoc]
      _ = 3257 + (m' * 3259 + D * 3259) := by rw [Nat.add_comm (D * 3259)]
      _ = 3259 + (m' * 3259 + 12 * m') := h1'
      _ = 3259 + (12 * m' + m' * 3259) := by rw [Nat.add_comm (m' * 3259)]
      _ = (3259 + 12 * m') + m' * 3259 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 3257 + D * 3259 = 3257 + (12 * m' + 2) := by
      calc 3257 + D * 3259 = (3257 + D * 3259) := rfl
      _ = 3259 + 12 * m' := h1_sub
      _ = 3257 + 2 + 12 * m' := rfl
      _ = 3257 + (2 + 12 * m') := by rw [Nat.add_assoc]
      _ = 3257 + (12 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 12 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 3259 ≥ 13 * 3259 := Nat.mul_le_mul_right 3259 h_gt
    have h2 : 12 * m' + 2 < 13 * 3259 := by
      have : 12 * m' < 12 * 3259 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 12 * m' + 2 < 12 * 3259 + 2 := Nat.add_lt_add_right this 2
      calc 12 * m' + 2 < 12 * 3259 + 2 := this
      _ ≤ 13 * 3259 := by decide
    have h_lt : 13 * 3259 < 13 * 3259 := by
      calc 13 * 3259 ≤ D * 3259 := h1
      _ = 12 * m' + 2 := h_alg
      _ < 13 * 3259 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 543 := by
    have h_alg_sol : 2 * 3259 = 12 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 3259 = 6518 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 6516 = 12 * m' := by
      calc 6516 = 6518 - 2 := rfl
      _ = 12 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 12 * m' := rfl
    have h_div : 6516 / 12 = (12 * m') / 12 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 12)] at h_div
    have h_div_eval : 6516 / 12 = 543 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_479 (m m' k' : ℕ)
  (h1 : 3407 + m * 3413 = 3413 + m' * 3433)
  (h2 : 3413 + m' * 3433 = 3433 + k' * 3449)
  (hm' : m' < 3413) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 3413 ≤ m' * 3413 := Nat.mul_le_mul_right 3413 h_le
    have h_le_mul2 : m' * 3413 ≤ m' * 3433 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 3407 + m * 3413 ≤ 3407 + m' * 3413 := Nat.add_le_add_left h_le_mul 3407
    have h_step2 : 3407 + m' * 3413 ≤ 3407 + m' * 3433 := Nat.add_le_add_left h_le_mul2 3407
    have h_step3 : 3407 + m' * 3433 < 3413 + m' * 3433 := Nat.add_lt_add_right (by decide : 3407 < 3413) _
    have h_lt : 3407 + m * 3413 < 3413 + m' * 3433 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 3413 = 20 * m' + 6 := by
    have h_eq : m * 3413 = m' * 3413 + D * 3413 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 3433 = m' * 3413 + 20 * m' := by
      rw [show 3433 = 3413 + 20 by decide, Nat.mul_add, Nat.mul_comm m' 20]
    rw [h_dist] at h1'
    have h1_assoc : (3407 + D * 3413) + m' * 3413 = (3413 + 20 * m') + m' * 3413 := by
      calc (3407 + D * 3413) + m' * 3413 = 3407 + (D * 3413 + m' * 3413) := by rw [Nat.add_assoc]
      _ = 3407 + (m' * 3413 + D * 3413) := by rw [Nat.add_comm (D * 3413)]
      _ = 3413 + (m' * 3413 + 20 * m') := h1'
      _ = 3413 + (20 * m' + m' * 3413) := by rw [Nat.add_comm (m' * 3413)]
      _ = (3413 + 20 * m') + m' * 3413 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 3407 + D * 3413 = 3407 + (20 * m' + 6) := by
      calc 3407 + D * 3413 = (3407 + D * 3413) := rfl
      _ = 3413 + 20 * m' := h1_sub
      _ = 3407 + 6 + 20 * m' := rfl
      _ = 3407 + (6 + 20 * m') := by rw [Nat.add_assoc]
      _ = 3407 + (20 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 20 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 3413 ≥ 21 * 3413 := Nat.mul_le_mul_right 3413 h_gt
    have h2 : 20 * m' + 6 < 21 * 3413 := by
      have : 20 * m' < 20 * 3413 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 20 * m' + 6 < 20 * 3413 + 6 := Nat.add_lt_add_right this 6
      calc 20 * m' + 6 < 20 * 3413 + 6 := this
      _ ≤ 21 * 3413 := by decide
    have h_lt : 21 * 3413 < 21 * 3413 := by
      calc 21 * 3413 ≤ D * 3413 := h1
      _ = 20 * m' + 6 := h_alg
      _ < 21 * 3413 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 341 := by
    have h_alg_sol : 2 * 3413 = 20 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 2 * 3413 = 6826 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 6820 = 20 * m' := by
      calc 6820 = 6826 - 6 := rfl
      _ = 20 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 20 * m' := rfl
    have h_div : 6820 / 20 = (20 * m') / 20 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 20)] at h_div
    have h_div_eval : 6820 / 20 = 341 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_547 (m m' k' : ℕ)
  (h1 : 3943 + m * 3947 = 3947 + m' * 3967)
  (h2 : 3947 + m' * 3967 = 3967 + k' * 3989)
  (hm' : m' < 3947) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 3947 ≤ m' * 3947 := Nat.mul_le_mul_right 3947 h_le
    have h_le_mul2 : m' * 3947 ≤ m' * 3967 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 3943 + m * 3947 ≤ 3943 + m' * 3947 := Nat.add_le_add_left h_le_mul 3943
    have h_step2 : 3943 + m' * 3947 ≤ 3943 + m' * 3967 := Nat.add_le_add_left h_le_mul2 3943
    have h_step3 : 3943 + m' * 3967 < 3947 + m' * 3967 := Nat.add_lt_add_right (by decide : 3943 < 3947) _
    have h_lt : 3943 + m * 3947 < 3947 + m' * 3967 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 3947 = 20 * m' + 4 := by
    have h_eq : m * 3947 = m' * 3947 + D * 3947 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 3967 = m' * 3947 + 20 * m' := by
      rw [show 3967 = 3947 + 20 by decide, Nat.mul_add, Nat.mul_comm m' 20]
    rw [h_dist] at h1'
    have h1_assoc : (3943 + D * 3947) + m' * 3947 = (3947 + 20 * m') + m' * 3947 := by
      calc (3943 + D * 3947) + m' * 3947 = 3943 + (D * 3947 + m' * 3947) := by rw [Nat.add_assoc]
      _ = 3943 + (m' * 3947 + D * 3947) := by rw [Nat.add_comm (D * 3947)]
      _ = 3947 + (m' * 3947 + 20 * m') := h1'
      _ = 3947 + (20 * m' + m' * 3947) := by rw [Nat.add_comm (m' * 3947)]
      _ = (3947 + 20 * m') + m' * 3947 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 3943 + D * 3947 = 3943 + (20 * m' + 4) := by
      calc 3943 + D * 3947 = (3943 + D * 3947) := rfl
      _ = 3947 + 20 * m' := h1_sub
      _ = 3943 + 4 + 20 * m' := rfl
      _ = 3943 + (4 + 20 * m') := by rw [Nat.add_assoc]
      _ = 3943 + (20 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 20 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 3947 ≥ 21 * 3947 := Nat.mul_le_mul_right 3947 h_gt
    have h2 : 20 * m' + 4 < 21 * 3947 := by
      have : 20 * m' < 20 * 3947 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 20 * m' + 4 < 20 * 3947 + 4 := Nat.add_lt_add_right this 4
      calc 20 * m' + 4 < 20 * 3947 + 4 := this
      _ ≤ 21 * 3947 := by decide
    have h_lt : 21 * 3947 < 21 * 3947 := by
      calc 21 * 3947 ≤ D * 3947 := h1
      _ = 20 * m' + 4 := h_alg
      _ < 21 * 3947 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 12 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 2368 := by
    have h_alg_sol : 12 * 3947 = 20 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 12 * 3947 = 47364 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 47360 = 20 * m' := by
      calc 47360 = 47364 - 4 := rfl
      _ = 20 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 20 * m' := rfl
    have h_div : 47360 / 20 = (20 * m') / 20 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 20)] at h_div
    have h_div_eval : 47360 / 20 = 2368 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_572 (m m' k' : ℕ)
  (h1 : 4157 + m * 4159 = 4159 + m' * 4177)
  (h2 : 4159 + m' * 4177 = 4177 + k' * 4201)
  (hm' : m' < 4159) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 4159 ≤ m' * 4159 := Nat.mul_le_mul_right 4159 h_le
    have h_le_mul2 : m' * 4159 ≤ m' * 4177 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 4157 + m * 4159 ≤ 4157 + m' * 4159 := Nat.add_le_add_left h_le_mul 4157
    have h_step2 : 4157 + m' * 4159 ≤ 4157 + m' * 4177 := Nat.add_le_add_left h_le_mul2 4157
    have h_step3 : 4157 + m' * 4177 < 4159 + m' * 4177 := Nat.add_lt_add_right (by decide : 4157 < 4159) _
    have h_lt : 4157 + m * 4159 < 4159 + m' * 4177 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 4159 = 18 * m' + 2 := by
    have h_eq : m * 4159 = m' * 4159 + D * 4159 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 4177 = m' * 4159 + 18 * m' := by
      rw [show 4177 = 4159 + 18 by decide, Nat.mul_add, Nat.mul_comm m' 18]
    rw [h_dist] at h1'
    have h1_assoc : (4157 + D * 4159) + m' * 4159 = (4159 + 18 * m') + m' * 4159 := by
      calc (4157 + D * 4159) + m' * 4159 = 4157 + (D * 4159 + m' * 4159) := by rw [Nat.add_assoc]
      _ = 4157 + (m' * 4159 + D * 4159) := by rw [Nat.add_comm (D * 4159)]
      _ = 4159 + (m' * 4159 + 18 * m') := h1'
      _ = 4159 + (18 * m' + m' * 4159) := by rw [Nat.add_comm (m' * 4159)]
      _ = (4159 + 18 * m') + m' * 4159 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 4157 + D * 4159 = 4157 + (18 * m' + 2) := by
      calc 4157 + D * 4159 = (4157 + D * 4159) := rfl
      _ = 4159 + 18 * m' := h1_sub
      _ = 4157 + 2 + 18 * m' := rfl
      _ = 4157 + (2 + 18 * m') := by rw [Nat.add_assoc]
      _ = 4157 + (18 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 18 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 4159 ≥ 19 * 4159 := Nat.mul_le_mul_right 4159 h_gt
    have h2 : 18 * m' + 2 < 19 * 4159 := by
      have : 18 * m' < 18 * 4159 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 18 * m' + 2 < 18 * 4159 + 2 := Nat.add_lt_add_right this 2
      calc 18 * m' + 2 < 18 * 4159 + 2 := this
      _ ≤ 19 * 4159 := by decide
    have h_lt : 19 * 4159 < 19 * 4159 := by
      calc 19 * 4159 ≤ D * 4159 := h1
      _ = 18 * m' + 2 := h_alg
      _ < 19 * 4159 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 462 := by
    have h_alg_sol : 2 * 4159 = 18 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 4159 = 8318 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 8316 = 18 * m' := by
      calc 8316 = 8318 - 2 := rfl
      _ = 18 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 18 * m' := rfl
    have h_div : 8316 / 18 = (18 * m') / 18 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 18)] at h_div
    have h_div_eval : 8316 / 18 = 462 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_588 (m m' k' : ℕ)
  (h1 : 4283 + m * 4289 = 4289 + m' * 4297)
  (h2 : 4289 + m' * 4297 = 4297 + k' * 4327)
  (hm' : m' < 4289) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 4289 ≤ m' * 4289 := Nat.mul_le_mul_right 4289 h_le
    have h_le_mul2 : m' * 4289 ≤ m' * 4297 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 4283 + m * 4289 ≤ 4283 + m' * 4289 := Nat.add_le_add_left h_le_mul 4283
    have h_step2 : 4283 + m' * 4289 ≤ 4283 + m' * 4297 := Nat.add_le_add_left h_le_mul2 4283
    have h_step3 : 4283 + m' * 4297 < 4289 + m' * 4297 := Nat.add_lt_add_right (by decide : 4283 < 4289) _
    have h_lt : 4283 + m * 4289 < 4289 + m' * 4297 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 4289 = 8 * m' + 6 := by
    have h_eq : m * 4289 = m' * 4289 + D * 4289 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 4297 = m' * 4289 + 8 * m' := by
      rw [show 4297 = 4289 + 8 by decide, Nat.mul_add, Nat.mul_comm m' 8]
    rw [h_dist] at h1'
    have h1_assoc : (4283 + D * 4289) + m' * 4289 = (4289 + 8 * m') + m' * 4289 := by
      calc (4283 + D * 4289) + m' * 4289 = 4283 + (D * 4289 + m' * 4289) := by rw [Nat.add_assoc]
      _ = 4283 + (m' * 4289 + D * 4289) := by rw [Nat.add_comm (D * 4289)]
      _ = 4289 + (m' * 4289 + 8 * m') := h1'
      _ = 4289 + (8 * m' + m' * 4289) := by rw [Nat.add_comm (m' * 4289)]
      _ = (4289 + 8 * m') + m' * 4289 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 4283 + D * 4289 = 4283 + (8 * m' + 6) := by
      calc 4283 + D * 4289 = (4283 + D * 4289) := rfl
      _ = 4289 + 8 * m' := h1_sub
      _ = 4283 + 6 + 8 * m' := rfl
      _ = 4283 + (6 + 8 * m') := by rw [Nat.add_assoc]
      _ = 4283 + (8 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 8 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 4289 ≥ 9 * 4289 := Nat.mul_le_mul_right 4289 h_gt
    have h2 : 8 * m' + 6 < 9 * 4289 := by
      have : 8 * m' < 8 * 4289 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 8 * m' + 6 < 8 * 4289 + 6 := Nat.add_lt_add_right this 6
      calc 8 * m' + 6 < 8 * 4289 + 6 := this
      _ ≤ 9 * 4289 := by decide
    have h_lt : 9 * 4289 < 9 * 4289 := by
      calc 9 * 4289 ≤ D * 4289 := h1
      _ = 8 * m' + 6 := h_alg
      _ < 9 * 4289 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 6 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 3216 := by
    have h_alg_sol : 6 * 4289 = 8 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 6 * 4289 = 25734 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 25728 = 8 * m' := by
      calc 25728 = 25734 - 6 := rfl
      _ = 8 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 8 * m' := rfl
    have h_div : 25728 / 8 = (8 * m') / 8 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 8)] at h_div
    have h_div_eval : 25728 / 8 = 3216 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_589 (m m' k' : ℕ)
  (h1 : 4289 + m * 4297 = 4297 + m' * 4327)
  (h2 : 4297 + m' * 4327 = 4327 + k' * 4337)
  (hm' : m' < 4297) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 4297 ≤ m' * 4297 := Nat.mul_le_mul_right 4297 h_le
    have h_le_mul2 : m' * 4297 ≤ m' * 4327 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 4289 + m * 4297 ≤ 4289 + m' * 4297 := Nat.add_le_add_left h_le_mul 4289
    have h_step2 : 4289 + m' * 4297 ≤ 4289 + m' * 4327 := Nat.add_le_add_left h_le_mul2 4289
    have h_step3 : 4289 + m' * 4327 < 4297 + m' * 4327 := Nat.add_lt_add_right (by decide : 4289 < 4297) _
    have h_lt : 4289 + m * 4297 < 4297 + m' * 4327 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 4297 = 30 * m' + 8 := by
    have h_eq : m * 4297 = m' * 4297 + D * 4297 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 4327 = m' * 4297 + 30 * m' := by
      rw [show 4327 = 4297 + 30 by decide, Nat.mul_add, Nat.mul_comm m' 30]
    rw [h_dist] at h1'
    have h1_assoc : (4289 + D * 4297) + m' * 4297 = (4297 + 30 * m') + m' * 4297 := by
      calc (4289 + D * 4297) + m' * 4297 = 4289 + (D * 4297 + m' * 4297) := by rw [Nat.add_assoc]
      _ = 4289 + (m' * 4297 + D * 4297) := by rw [Nat.add_comm (D * 4297)]
      _ = 4297 + (m' * 4297 + 30 * m') := h1'
      _ = 4297 + (30 * m' + m' * 4297) := by rw [Nat.add_comm (m' * 4297)]
      _ = (4297 + 30 * m') + m' * 4297 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 4289 + D * 4297 = 4289 + (30 * m' + 8) := by
      calc 4289 + D * 4297 = (4289 + D * 4297) := rfl
      _ = 4297 + 30 * m' := h1_sub
      _ = 4289 + 8 + 30 * m' := rfl
      _ = 4289 + (8 + 30 * m') := by rw [Nat.add_assoc]
      _ = 4289 + (30 * m' + 8) := by rw [Nat.add_comm 8]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 30 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 4297 ≥ 31 * 4297 := Nat.mul_le_mul_right 4297 h_gt
    have h2 : 30 * m' + 8 < 31 * 4297 := by
      have : 30 * m' < 30 * 4297 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 30 * m' + 8 < 30 * 4297 + 8 := Nat.add_lt_add_right this 8
      calc 30 * m' + 8 < 30 * 4297 + 8 := this
      _ ≤ 31 * 4297 := by decide
    have h_lt : 31 * 4297 < 31 * 4297 := by
      calc 31 * 4297 ≤ D * 4297 := h1
      _ = 30 * m' + 8 := h_alg
      _ < 31 * 4297 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 14 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 2005 := by
    have h_alg_sol : 14 * 4297 = 30 * m' + 8 := h_D_eq ▸ h_alg
    have h_eval : 14 * 4297 = 60158 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 60150 = 30 * m' := by
      calc 60150 = 60158 - 8 := rfl
      _ = 30 * m' + 8 - 8 := by rw [h_alg_sol]
      _ = 30 * m' := rfl
    have h_div : 60150 / 30 = (30 * m') / 30 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 30)] at h_div
    have h_div_eval : 60150 / 30 = 2005 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_648 (m m' k' : ℕ)
  (h1 : 4813 + m * 4817 = 4817 + m' * 4831)
  (h2 : 4817 + m' * 4831 = 4831 + k' * 4861)
  (hm' : m' < 4817) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 4817 ≤ m' * 4817 := Nat.mul_le_mul_right 4817 h_le
    have h_le_mul2 : m' * 4817 ≤ m' * 4831 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 4813 + m * 4817 ≤ 4813 + m' * 4817 := Nat.add_le_add_left h_le_mul 4813
    have h_step2 : 4813 + m' * 4817 ≤ 4813 + m' * 4831 := Nat.add_le_add_left h_le_mul2 4813
    have h_step3 : 4813 + m' * 4831 < 4817 + m' * 4831 := Nat.add_lt_add_right (by decide : 4813 < 4817) _
    have h_lt : 4813 + m * 4817 < 4817 + m' * 4831 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 4817 = 14 * m' + 4 := by
    have h_eq : m * 4817 = m' * 4817 + D * 4817 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 4831 = m' * 4817 + 14 * m' := by
      rw [show 4831 = 4817 + 14 by decide, Nat.mul_add, Nat.mul_comm m' 14]
    rw [h_dist] at h1'
    have h1_assoc : (4813 + D * 4817) + m' * 4817 = (4817 + 14 * m') + m' * 4817 := by
      calc (4813 + D * 4817) + m' * 4817 = 4813 + (D * 4817 + m' * 4817) := by rw [Nat.add_assoc]
      _ = 4813 + (m' * 4817 + D * 4817) := by rw [Nat.add_comm (D * 4817)]
      _ = 4817 + (m' * 4817 + 14 * m') := h1'
      _ = 4817 + (14 * m' + m' * 4817) := by rw [Nat.add_comm (m' * 4817)]
      _ = (4817 + 14 * m') + m' * 4817 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 4813 + D * 4817 = 4813 + (14 * m' + 4) := by
      calc 4813 + D * 4817 = (4813 + D * 4817) := rfl
      _ = 4817 + 14 * m' := h1_sub
      _ = 4813 + 4 + 14 * m' := rfl
      _ = 4813 + (4 + 14 * m') := by rw [Nat.add_assoc]
      _ = 4813 + (14 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 14 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 4817 ≥ 15 * 4817 := Nat.mul_le_mul_right 4817 h_gt
    have h2 : 14 * m' + 4 < 15 * 4817 := by
      have : 14 * m' < 14 * 4817 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 14 * m' + 4 < 14 * 4817 + 4 := Nat.add_lt_add_right this 4
      calc 14 * m' + 4 < 14 * 4817 + 4 := this
      _ ≤ 15 * 4817 := by decide
    have h_lt : 15 * 4817 < 15 * 4817 := by
      calc 15 * 4817 ≤ D * 4817 := h1
      _ = 14 * m' + 4 := h_alg
      _ < 15 * 4817 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 4 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 1376 := by
    have h_alg_sol : 4 * 4817 = 14 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 4 * 4817 = 19268 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 19264 = 14 * m' := by
      calc 19264 = 19268 - 4 := rfl
      _ = 14 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 14 * m' := rfl
    have h_div : 19264 / 14 = (14 * m') / 14 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 14)] at h_div
    have h_div_eval : 19264 / 14 = 1376 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_736 (m m' k' : ℕ)
  (h1 : 5573 + m * 5581 = 5581 + m' * 5591)
  (h2 : 5581 + m' * 5591 = 5591 + k' * 5623)
  (hm' : m' < 5581) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 5581 ≤ m' * 5581 := Nat.mul_le_mul_right 5581 h_le
    have h_le_mul2 : m' * 5581 ≤ m' * 5591 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 5573 + m * 5581 ≤ 5573 + m' * 5581 := Nat.add_le_add_left h_le_mul 5573
    have h_step2 : 5573 + m' * 5581 ≤ 5573 + m' * 5591 := Nat.add_le_add_left h_le_mul2 5573
    have h_step3 : 5573 + m' * 5591 < 5581 + m' * 5591 := Nat.add_lt_add_right (by decide : 5573 < 5581) _
    have h_lt : 5573 + m * 5581 < 5581 + m' * 5591 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 5581 = 10 * m' + 8 := by
    have h_eq : m * 5581 = m' * 5581 + D * 5581 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 5591 = m' * 5581 + 10 * m' := by
      rw [show 5591 = 5581 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (5573 + D * 5581) + m' * 5581 = (5581 + 10 * m') + m' * 5581 := by
      calc (5573 + D * 5581) + m' * 5581 = 5573 + (D * 5581 + m' * 5581) := by rw [Nat.add_assoc]
      _ = 5573 + (m' * 5581 + D * 5581) := by rw [Nat.add_comm (D * 5581)]
      _ = 5581 + (m' * 5581 + 10 * m') := h1'
      _ = 5581 + (10 * m' + m' * 5581) := by rw [Nat.add_comm (m' * 5581)]
      _ = (5581 + 10 * m') + m' * 5581 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 5573 + D * 5581 = 5573 + (10 * m' + 8) := by
      calc 5573 + D * 5581 = (5573 + D * 5581) := rfl
      _ = 5581 + 10 * m' := h1_sub
      _ = 5573 + 8 + 10 * m' := rfl
      _ = 5573 + (8 + 10 * m') := by rw [Nat.add_assoc]
      _ = 5573 + (10 * m' + 8) := by rw [Nat.add_comm 8]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 5581 ≥ 11 * 5581 := Nat.mul_le_mul_right 5581 h_gt
    have h2 : 10 * m' + 8 < 11 * 5581 := by
      have : 10 * m' < 10 * 5581 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 8 < 10 * 5581 + 8 := Nat.add_lt_add_right this 8
      calc 10 * m' + 8 < 10 * 5581 + 8 := this
      _ ≤ 11 * 5581 := by decide
    have h_lt : 11 * 5581 < 11 * 5581 := by
      calc 11 * 5581 ≤ D * 5581 := h1
      _ = 10 * m' + 8 := h_alg
      _ < 11 * 5581 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 4464 := by
    have h_alg_sol : 8 * 5581 = 10 * m' + 8 := h_D_eq ▸ h_alg
    have h_eval : 8 * 5581 = 44648 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 44640 = 10 * m' := by
      calc 44640 = 44648 - 8 := rfl
      _ = 10 * m' + 8 - 8 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 44640 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 44640 / 10 = 4464 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_737 (m m' k' : ℕ)
  (h1 : 5581 + m * 5591 = 5591 + m' * 5623)
  (h2 : 5591 + m' * 5623 = 5623 + k' * 5639)
  (hm' : m' < 5591) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 5591 ≤ m' * 5591 := Nat.mul_le_mul_right 5591 h_le
    have h_le_mul2 : m' * 5591 ≤ m' * 5623 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 5581 + m * 5591 ≤ 5581 + m' * 5591 := Nat.add_le_add_left h_le_mul 5581
    have h_step2 : 5581 + m' * 5591 ≤ 5581 + m' * 5623 := Nat.add_le_add_left h_le_mul2 5581
    have h_step3 : 5581 + m' * 5623 < 5591 + m' * 5623 := Nat.add_lt_add_right (by decide : 5581 < 5591) _
    have h_lt : 5581 + m * 5591 < 5591 + m' * 5623 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 5591 = 32 * m' + 10 := by
    have h_eq : m * 5591 = m' * 5591 + D * 5591 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 5623 = m' * 5591 + 32 * m' := by
      rw [show 5623 = 5591 + 32 by decide, Nat.mul_add, Nat.mul_comm m' 32]
    rw [h_dist] at h1'
    have h1_assoc : (5581 + D * 5591) + m' * 5591 = (5591 + 32 * m') + m' * 5591 := by
      calc (5581 + D * 5591) + m' * 5591 = 5581 + (D * 5591 + m' * 5591) := by rw [Nat.add_assoc]
      _ = 5581 + (m' * 5591 + D * 5591) := by rw [Nat.add_comm (D * 5591)]
      _ = 5591 + (m' * 5591 + 32 * m') := h1'
      _ = 5591 + (32 * m' + m' * 5591) := by rw [Nat.add_comm (m' * 5591)]
      _ = (5591 + 32 * m') + m' * 5591 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 5581 + D * 5591 = 5581 + (32 * m' + 10) := by
      calc 5581 + D * 5591 = (5581 + D * 5591) := rfl
      _ = 5591 + 32 * m' := h1_sub
      _ = 5581 + 10 + 32 * m' := rfl
      _ = 5581 + (10 + 32 * m') := by rw [Nat.add_assoc]
      _ = 5581 + (32 * m' + 10) := by rw [Nat.add_comm 10]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 32 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 5591 ≥ 33 * 5591 := Nat.mul_le_mul_right 5591 h_gt
    have h2 : 32 * m' + 10 < 33 * 5591 := by
      have : 32 * m' < 32 * 5591 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 32 * m' + 10 < 32 * 5591 + 10 := Nat.add_lt_add_right this 10
      calc 32 * m' + 10 < 32 * 5591 + 10 := this
      _ ≤ 33 * 5591 := by decide
    have h_lt : 33 * 5591 < 33 * 5591 := by
      calc 33 * 5591 ≤ D * 5591 := h1
      _ = 32 * m' + 10 := h_alg
      _ < 33 * 5591 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 ∨ D = 31 ∨ D = 32 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 6 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 1048 := by
    have h_alg_sol : 6 * 5591 = 32 * m' + 10 := h_D_eq ▸ h_alg
    have h_eval : 6 * 5591 = 33546 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 33536 = 32 * m' := by
      calc 33536 = 33546 - 10 := rfl
      _ = 32 * m' + 10 - 10 := by rw [h_alg_sol]
      _ = 32 * m' := rfl
    have h_div : 33536 / 32 = (32 * m') / 32 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 32)] at h_div
    have h_div_eval : 33536 / 32 = 1048 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_779 (m m' k' : ℕ)
  (h1 : 5927 + m * 5939 = 5939 + m' * 5953)
  (h2 : 5939 + m' * 5953 = 5953 + k' * 5981)
  (hm' : m' < 5939) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 5939 ≤ m' * 5939 := Nat.mul_le_mul_right 5939 h_le
    have h_le_mul2 : m' * 5939 ≤ m' * 5953 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 5927 + m * 5939 ≤ 5927 + m' * 5939 := Nat.add_le_add_left h_le_mul 5927
    have h_step2 : 5927 + m' * 5939 ≤ 5927 + m' * 5953 := Nat.add_le_add_left h_le_mul2 5927
    have h_step3 : 5927 + m' * 5953 < 5939 + m' * 5953 := Nat.add_lt_add_right (by decide : 5927 < 5939) _
    have h_lt : 5927 + m * 5939 < 5939 + m' * 5953 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 5939 = 14 * m' + 12 := by
    have h_eq : m * 5939 = m' * 5939 + D * 5939 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 5953 = m' * 5939 + 14 * m' := by
      rw [show 5953 = 5939 + 14 by decide, Nat.mul_add, Nat.mul_comm m' 14]
    rw [h_dist] at h1'
    have h1_assoc : (5927 + D * 5939) + m' * 5939 = (5939 + 14 * m') + m' * 5939 := by
      calc (5927 + D * 5939) + m' * 5939 = 5927 + (D * 5939 + m' * 5939) := by rw [Nat.add_assoc]
      _ = 5927 + (m' * 5939 + D * 5939) := by rw [Nat.add_comm (D * 5939)]
      _ = 5939 + (m' * 5939 + 14 * m') := h1'
      _ = 5939 + (14 * m' + m' * 5939) := by rw [Nat.add_comm (m' * 5939)]
      _ = (5939 + 14 * m') + m' * 5939 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 5927 + D * 5939 = 5927 + (14 * m' + 12) := by
      calc 5927 + D * 5939 = (5927 + D * 5939) := rfl
      _ = 5939 + 14 * m' := h1_sub
      _ = 5927 + 12 + 14 * m' := rfl
      _ = 5927 + (12 + 14 * m') := by rw [Nat.add_assoc]
      _ = 5927 + (14 * m' + 12) := by rw [Nat.add_comm 12]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 14 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 5939 ≥ 15 * 5939 := Nat.mul_le_mul_right 5939 h_gt
    have h2 : 14 * m' + 12 < 15 * 5939 := by
      have : 14 * m' < 14 * 5939 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 14 * m' + 12 < 14 * 5939 + 12 := Nat.add_lt_add_right this 12
      calc 14 * m' + 12 < 14 * 5939 + 12 := this
      _ ≤ 15 * 5939 := by decide
    have h_lt : 15 * 5939 < 15 * 5939 := by
      calc 15 * 5939 ≤ D * 5939 := h1
      _ = 14 * m' + 12 := h_alg
      _ < 15 * 5939 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 4 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 1696 := by
    have h_alg_sol : 4 * 5939 = 14 * m' + 12 := h_D_eq ▸ h_alg
    have h_eval : 4 * 5939 = 23756 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 23744 = 14 * m' := by
      calc 23744 = 23756 - 12 := rfl
      _ = 14 * m' + 12 - 12 := by rw [h_alg_sol]
      _ = 14 * m' := rfl
    have h_div : 23744 / 14 = (14 * m') / 14 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 14)] at h_div
    have h_div_eval : 23744 / 14 = 1696 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_927 (m m' k' : ℕ)
  (h1 : 7247 + m * 7253 = 7253 + m' * 7283)
  (h2 : 7253 + m' * 7283 = 7283 + k' * 7297)
  (hm' : m' < 7253) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 7253 ≤ m' * 7253 := Nat.mul_le_mul_right 7253 h_le
    have h_le_mul2 : m' * 7253 ≤ m' * 7283 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 7247 + m * 7253 ≤ 7247 + m' * 7253 := Nat.add_le_add_left h_le_mul 7247
    have h_step2 : 7247 + m' * 7253 ≤ 7247 + m' * 7283 := Nat.add_le_add_left h_le_mul2 7247
    have h_step3 : 7247 + m' * 7283 < 7253 + m' * 7283 := Nat.add_lt_add_right (by decide : 7247 < 7253) _
    have h_lt : 7247 + m * 7253 < 7253 + m' * 7283 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 7253 = 30 * m' + 6 := by
    have h_eq : m * 7253 = m' * 7253 + D * 7253 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 7283 = m' * 7253 + 30 * m' := by
      rw [show 7283 = 7253 + 30 by decide, Nat.mul_add, Nat.mul_comm m' 30]
    rw [h_dist] at h1'
    have h1_assoc : (7247 + D * 7253) + m' * 7253 = (7253 + 30 * m') + m' * 7253 := by
      calc (7247 + D * 7253) + m' * 7253 = 7247 + (D * 7253 + m' * 7253) := by rw [Nat.add_assoc]
      _ = 7247 + (m' * 7253 + D * 7253) := by rw [Nat.add_comm (D * 7253)]
      _ = 7253 + (m' * 7253 + 30 * m') := h1'
      _ = 7253 + (30 * m' + m' * 7253) := by rw [Nat.add_comm (m' * 7253)]
      _ = (7253 + 30 * m') + m' * 7253 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 7247 + D * 7253 = 7247 + (30 * m' + 6) := by
      calc 7247 + D * 7253 = (7247 + D * 7253) := rfl
      _ = 7253 + 30 * m' := h1_sub
      _ = 7247 + 6 + 30 * m' := rfl
      _ = 7247 + (6 + 30 * m') := by rw [Nat.add_assoc]
      _ = 7247 + (30 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 30 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 7253 ≥ 31 * 7253 := Nat.mul_le_mul_right 7253 h_gt
    have h2 : 30 * m' + 6 < 31 * 7253 := by
      have : 30 * m' < 30 * 7253 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 30 * m' + 6 < 30 * 7253 + 6 := Nat.add_lt_add_right this 6
      calc 30 * m' + 6 < 30 * 7253 + 6 := this
      _ ≤ 31 * 7253 := by decide
    have h_lt : 31 * 7253 < 31 * 7253 := by
      calc 31 * 7253 ≤ D * 7253 := h1
      _ = 30 * m' + 6 := h_alg
      _ < 31 * 7253 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 12 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 2901 := by
    have h_alg_sol : 12 * 7253 = 30 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 12 * 7253 = 87036 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 87030 = 30 * m' := by
      calc 87030 = 87036 - 6 := rfl
      _ = 30 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 30 * m' := rfl
    have h_div : 87030 / 30 = (30 * m') / 30 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 30)] at h_div
    have h_div_eval : 87030 / 30 = 2901 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_936 (m m' k' : ℕ)
  (h1 : 7349 + m * 7351 = 7351 + m' * 7369)
  (h2 : 7351 + m' * 7369 = 7369 + k' * 7393)
  (hm' : m' < 7351) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 7351 ≤ m' * 7351 := Nat.mul_le_mul_right 7351 h_le
    have h_le_mul2 : m' * 7351 ≤ m' * 7369 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 7349 + m * 7351 ≤ 7349 + m' * 7351 := Nat.add_le_add_left h_le_mul 7349
    have h_step2 : 7349 + m' * 7351 ≤ 7349 + m' * 7369 := Nat.add_le_add_left h_le_mul2 7349
    have h_step3 : 7349 + m' * 7369 < 7351 + m' * 7369 := Nat.add_lt_add_right (by decide : 7349 < 7351) _
    have h_lt : 7349 + m * 7351 < 7351 + m' * 7369 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 7351 = 18 * m' + 2 := by
    have h_eq : m * 7351 = m' * 7351 + D * 7351 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 7369 = m' * 7351 + 18 * m' := by
      rw [show 7369 = 7351 + 18 by decide, Nat.mul_add, Nat.mul_comm m' 18]
    rw [h_dist] at h1'
    have h1_assoc : (7349 + D * 7351) + m' * 7351 = (7351 + 18 * m') + m' * 7351 := by
      calc (7349 + D * 7351) + m' * 7351 = 7349 + (D * 7351 + m' * 7351) := by rw [Nat.add_assoc]
      _ = 7349 + (m' * 7351 + D * 7351) := by rw [Nat.add_comm (D * 7351)]
      _ = 7351 + (m' * 7351 + 18 * m') := h1'
      _ = 7351 + (18 * m' + m' * 7351) := by rw [Nat.add_comm (m' * 7351)]
      _ = (7351 + 18 * m') + m' * 7351 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 7349 + D * 7351 = 7349 + (18 * m' + 2) := by
      calc 7349 + D * 7351 = (7349 + D * 7351) := rfl
      _ = 7351 + 18 * m' := h1_sub
      _ = 7349 + 2 + 18 * m' := rfl
      _ = 7349 + (2 + 18 * m') := by rw [Nat.add_assoc]
      _ = 7349 + (18 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 18 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 7351 ≥ 19 * 7351 := Nat.mul_le_mul_right 7351 h_gt
    have h2 : 18 * m' + 2 < 19 * 7351 := by
      have : 18 * m' < 18 * 7351 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 18 * m' + 2 < 18 * 7351 + 2 := Nat.add_lt_add_right this 2
      calc 18 * m' + 2 < 18 * 7351 + 2 := this
      _ ≤ 19 * 7351 := by decide
    have h_lt : 19 * 7351 < 19 * 7351 := by
      calc 19 * 7351 ≤ D * 7351 := h1
      _ = 18 * m' + 2 := h_alg
      _ < 19 * 7351 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 3267 := by
    have h_alg_sol : 8 * 7351 = 18 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 8 * 7351 = 58808 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 58806 = 18 * m' := by
      calc 58806 = 58808 - 2 := rfl
      _ = 18 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 18 * m' := rfl
    have h_div : 58806 / 18 = (18 * m') / 18 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 18)] at h_div
    have h_div_eval : 58806 / 18 = 3267 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_937 (m m' k' : ℕ)
  (h1 : 7351 + m * 7369 = 7369 + m' * 7393)
  (h2 : 7369 + m' * 7393 = 7393 + k' * 7411)
  (hm' : m' < 7369) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 7369 ≤ m' * 7369 := Nat.mul_le_mul_right 7369 h_le
    have h_le_mul2 : m' * 7369 ≤ m' * 7393 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 7351 + m * 7369 ≤ 7351 + m' * 7369 := Nat.add_le_add_left h_le_mul 7351
    have h_step2 : 7351 + m' * 7369 ≤ 7351 + m' * 7393 := Nat.add_le_add_left h_le_mul2 7351
    have h_step3 : 7351 + m' * 7393 < 7369 + m' * 7393 := Nat.add_lt_add_right (by decide : 7351 < 7369) _
    have h_lt : 7351 + m * 7369 < 7369 + m' * 7393 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 7369 = 24 * m' + 18 := by
    have h_eq : m * 7369 = m' * 7369 + D * 7369 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 7393 = m' * 7369 + 24 * m' := by
      rw [show 7393 = 7369 + 24 by decide, Nat.mul_add, Nat.mul_comm m' 24]
    rw [h_dist] at h1'
    have h1_assoc : (7351 + D * 7369) + m' * 7369 = (7369 + 24 * m') + m' * 7369 := by
      calc (7351 + D * 7369) + m' * 7369 = 7351 + (D * 7369 + m' * 7369) := by rw [Nat.add_assoc]
      _ = 7351 + (m' * 7369 + D * 7369) := by rw [Nat.add_comm (D * 7369)]
      _ = 7369 + (m' * 7369 + 24 * m') := h1'
      _ = 7369 + (24 * m' + m' * 7369) := by rw [Nat.add_comm (m' * 7369)]
      _ = (7369 + 24 * m') + m' * 7369 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 7351 + D * 7369 = 7351 + (24 * m' + 18) := by
      calc 7351 + D * 7369 = (7351 + D * 7369) := rfl
      _ = 7369 + 24 * m' := h1_sub
      _ = 7351 + 18 + 24 * m' := rfl
      _ = 7351 + (18 + 24 * m') := by rw [Nat.add_assoc]
      _ = 7351 + (24 * m' + 18) := by rw [Nat.add_comm 18]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 24 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 7369 ≥ 25 * 7369 := Nat.mul_le_mul_right 7369 h_gt
    have h2 : 24 * m' + 18 < 25 * 7369 := by
      have : 24 * m' < 24 * 7369 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 24 * m' + 18 < 24 * 7369 + 18 := Nat.add_lt_add_right this 18
      calc 24 * m' + 18 < 24 * 7369 + 18 := this
      _ ≤ 25 * 7369 := by decide
    have h_lt : 25 * 7369 < 25 * 7369 := by
      calc 25 * 7369 ≤ D * 7369 := h1
      _ = 24 * m' + 18 := h_alg
      _ < 25 * 7369 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 18 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 5526 := by
    have h_alg_sol : 18 * 7369 = 24 * m' + 18 := h_D_eq ▸ h_alg
    have h_eval : 18 * 7369 = 132642 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 132624 = 24 * m' := by
      calc 132624 = 132642 - 18 := rfl
      _ = 24 * m' + 18 - 18 := by rw [h_alg_sol]
      _ = 24 * m' := rfl
    have h_div : 132624 / 24 = (24 * m') / 24 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 24)] at h_div
    have h_div_eval : 132624 / 24 = 5526 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_1005 (m m' k' : ℕ)
  (h1 : 7951 + m * 7963 = 7963 + m' * 7993)
  (h2 : 7963 + m' * 7993 = 7993 + k' * 8009)
  (hm' : m' < 7963) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 7963 ≤ m' * 7963 := Nat.mul_le_mul_right 7963 h_le
    have h_le_mul2 : m' * 7963 ≤ m' * 7993 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 7951 + m * 7963 ≤ 7951 + m' * 7963 := Nat.add_le_add_left h_le_mul 7951
    have h_step2 : 7951 + m' * 7963 ≤ 7951 + m' * 7993 := Nat.add_le_add_left h_le_mul2 7951
    have h_step3 : 7951 + m' * 7993 < 7963 + m' * 7993 := Nat.add_lt_add_right (by decide : 7951 < 7963) _
    have h_lt : 7951 + m * 7963 < 7963 + m' * 7993 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 7963 = 30 * m' + 12 := by
    have h_eq : m * 7963 = m' * 7963 + D * 7963 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 7993 = m' * 7963 + 30 * m' := by
      rw [show 7993 = 7963 + 30 by decide, Nat.mul_add, Nat.mul_comm m' 30]
    rw [h_dist] at h1'
    have h1_assoc : (7951 + D * 7963) + m' * 7963 = (7963 + 30 * m') + m' * 7963 := by
      calc (7951 + D * 7963) + m' * 7963 = 7951 + (D * 7963 + m' * 7963) := by rw [Nat.add_assoc]
      _ = 7951 + (m' * 7963 + D * 7963) := by rw [Nat.add_comm (D * 7963)]
      _ = 7963 + (m' * 7963 + 30 * m') := h1'
      _ = 7963 + (30 * m' + m' * 7963) := by rw [Nat.add_comm (m' * 7963)]
      _ = (7963 + 30 * m') + m' * 7963 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 7951 + D * 7963 = 7951 + (30 * m' + 12) := by
      calc 7951 + D * 7963 = (7951 + D * 7963) := rfl
      _ = 7963 + 30 * m' := h1_sub
      _ = 7951 + 12 + 30 * m' := rfl
      _ = 7951 + (12 + 30 * m') := by rw [Nat.add_assoc]
      _ = 7951 + (30 * m' + 12) := by rw [Nat.add_comm 12]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 30 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 7963 ≥ 31 * 7963 := Nat.mul_le_mul_right 7963 h_gt
    have h2 : 30 * m' + 12 < 31 * 7963 := by
      have : 30 * m' < 30 * 7963 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 30 * m' + 12 < 30 * 7963 + 12 := Nat.add_lt_add_right this 12
      calc 30 * m' + 12 < 30 * 7963 + 12 := this
      _ ≤ 31 * 7963 := by decide
    have h_lt : 31 * 7963 < 31 * 7963 := by
      calc 31 * 7963 ≤ D * 7963 := h1
      _ = 30 * m' + 12 := h_alg
      _ < 31 * 7963 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 24 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 6370 := by
    have h_alg_sol : 24 * 7963 = 30 * m' + 12 := h_D_eq ▸ h_alg
    have h_eval : 24 * 7963 = 191112 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 191100 = 30 * m' := by
      calc 191100 = 191112 - 12 := rfl
      _ = 30 * m' + 12 - 12 := by rw [h_alg_sol]
      _ = 30 * m' := rfl
    have h_div : 191100 / 30 = (30 * m') / 30 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 30)] at h_div
    have h_div_eval : 191100 / 30 = 6370 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_1182 (m m' k' : ℕ)
  (h1 : 9547 + m * 9551 = 9551 + m' * 9587)
  (h2 : 9551 + m' * 9587 = 9587 + k' * 9601)
  (hm' : m' < 9551) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 9551 ≤ m' * 9551 := Nat.mul_le_mul_right 9551 h_le
    have h_le_mul2 : m' * 9551 ≤ m' * 9587 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 9547 + m * 9551 ≤ 9547 + m' * 9551 := Nat.add_le_add_left h_le_mul 9547
    have h_step2 : 9547 + m' * 9551 ≤ 9547 + m' * 9587 := Nat.add_le_add_left h_le_mul2 9547
    have h_step3 : 9547 + m' * 9587 < 9551 + m' * 9587 := Nat.add_lt_add_right (by decide : 9547 < 9551) _
    have h_lt : 9547 + m * 9551 < 9551 + m' * 9587 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 9551 = 36 * m' + 4 := by
    have h_eq : m * 9551 = m' * 9551 + D * 9551 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 9587 = m' * 9551 + 36 * m' := by
      rw [show 9587 = 9551 + 36 by decide, Nat.mul_add, Nat.mul_comm m' 36]
    rw [h_dist] at h1'
    have h1_assoc : (9547 + D * 9551) + m' * 9551 = (9551 + 36 * m') + m' * 9551 := by
      calc (9547 + D * 9551) + m' * 9551 = 9547 + (D * 9551 + m' * 9551) := by rw [Nat.add_assoc]
      _ = 9547 + (m' * 9551 + D * 9551) := by rw [Nat.add_comm (D * 9551)]
      _ = 9551 + (m' * 9551 + 36 * m') := h1'
      _ = 9551 + (36 * m' + m' * 9551) := by rw [Nat.add_comm (m' * 9551)]
      _ = (9551 + 36 * m') + m' * 9551 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 9547 + D * 9551 = 9547 + (36 * m' + 4) := by
      calc 9547 + D * 9551 = (9547 + D * 9551) := rfl
      _ = 9551 + 36 * m' := h1_sub
      _ = 9547 + 4 + 36 * m' := rfl
      _ = 9547 + (4 + 36 * m') := by rw [Nat.add_assoc]
      _ = 9547 + (36 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 36 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 9551 ≥ 37 * 9551 := Nat.mul_le_mul_right 9551 h_gt
    have h2 : 36 * m' + 4 < 37 * 9551 := by
      have : 36 * m' < 36 * 9551 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 36 * m' + 4 < 36 * 9551 + 4 := Nat.add_lt_add_right this 4
      calc 36 * m' + 4 < 36 * 9551 + 4 := this
      _ ≤ 37 * 9551 := by decide
    have h_lt : 37 * 9551 < 37 * 9551 := by
      calc 37 * 9551 ≤ D * 9551 := h1
      _ = 36 * m' + 4 := h_alg
      _ < 37 * 9551 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 ∨ D = 31 ∨ D = 32 ∨ D = 33 ∨ D = 34 ∨ D = 35 ∨ D = 36 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 20 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 5306 := by
    have h_alg_sol : 20 * 9551 = 36 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 20 * 9551 = 191020 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 191016 = 36 * m' := by
      calc 191016 = 191020 - 4 := rfl
      _ = 36 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 36 * m' := rfl
    have h_div : 191016 / 36 = (36 * m') / 36 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 36)] at h_div
    have h_div_eval : 191016 / 36 = 5306 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_1661 (m m' k' : ℕ)
  (h1 : 14083 + m * 14087 = 14087 + m' * 14107)
  (h2 : 14087 + m' * 14107 = 14107 + k' * 14143)
  (hm' : m' < 14087) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 14087 ≤ m' * 14087 := Nat.mul_le_mul_right 14087 h_le
    have h_le_mul2 : m' * 14087 ≤ m' * 14107 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 14083 + m * 14087 ≤ 14083 + m' * 14087 := Nat.add_le_add_left h_le_mul 14083
    have h_step2 : 14083 + m' * 14087 ≤ 14083 + m' * 14107 := Nat.add_le_add_left h_le_mul2 14083
    have h_step3 : 14083 + m' * 14107 < 14087 + m' * 14107 := Nat.add_lt_add_right (by decide : 14083 < 14087) _
    have h_lt : 14083 + m * 14087 < 14087 + m' * 14107 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 14087 = 20 * m' + 4 := by
    have h_eq : m * 14087 = m' * 14087 + D * 14087 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 14107 = m' * 14087 + 20 * m' := by
      rw [show 14107 = 14087 + 20 by decide, Nat.mul_add, Nat.mul_comm m' 20]
    rw [h_dist] at h1'
    have h1_assoc : (14083 + D * 14087) + m' * 14087 = (14087 + 20 * m') + m' * 14087 := by
      calc (14083 + D * 14087) + m' * 14087 = 14083 + (D * 14087 + m' * 14087) := by rw [Nat.add_assoc]
      _ = 14083 + (m' * 14087 + D * 14087) := by rw [Nat.add_comm (D * 14087)]
      _ = 14087 + (m' * 14087 + 20 * m') := h1'
      _ = 14087 + (20 * m' + m' * 14087) := by rw [Nat.add_comm (m' * 14087)]
      _ = (14087 + 20 * m') + m' * 14087 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 14083 + D * 14087 = 14083 + (20 * m' + 4) := by
      calc 14083 + D * 14087 = (14083 + D * 14087) := rfl
      _ = 14087 + 20 * m' := h1_sub
      _ = 14083 + 4 + 20 * m' := rfl
      _ = 14083 + (4 + 20 * m') := by rw [Nat.add_assoc]
      _ = 14083 + (20 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 20 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 14087 ≥ 21 * 14087 := Nat.mul_le_mul_right 14087 h_gt
    have h2 : 20 * m' + 4 < 21 * 14087 := by
      have : 20 * m' < 20 * 14087 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 20 * m' + 4 < 20 * 14087 + 4 := Nat.add_lt_add_right this 4
      calc 20 * m' + 4 < 20 * 14087 + 4 := this
      _ ≤ 21 * 14087 := by decide
    have h_lt : 21 * 14087 < 21 * 14087 := by
      calc 21 * 14087 ≤ D * 14087 := h1
      _ = 20 * m' + 4 := h_alg
      _ < 21 * 14087 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 12 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 8452 := by
    have h_alg_sol : 12 * 14087 = 20 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 12 * 14087 = 169044 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 169040 = 20 * m' := by
      calc 169040 = 169044 - 4 := rfl
      _ = 20 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 20 * m' := rfl
    have h_div : 169040 / 20 = (20 * m') / 20 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 20)] at h_div
    have h_div_eval : 169040 / 20 = 8452 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_2224 (m m' k' : ℕ)
  (h1 : 19603 + m * 19609 = 19609 + m' * 19661)
  (h2 : 19609 + m' * 19661 = 19661 + k' * 19681)
  (hm' : m' < 19609) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 19609 ≤ m' * 19609 := Nat.mul_le_mul_right 19609 h_le
    have h_le_mul2 : m' * 19609 ≤ m' * 19661 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 19603 + m * 19609 ≤ 19603 + m' * 19609 := Nat.add_le_add_left h_le_mul 19603
    have h_step2 : 19603 + m' * 19609 ≤ 19603 + m' * 19661 := Nat.add_le_add_left h_le_mul2 19603
    have h_step3 : 19603 + m' * 19661 < 19609 + m' * 19661 := Nat.add_lt_add_right (by decide : 19603 < 19609) _
    have h_lt : 19603 + m * 19609 < 19609 + m' * 19661 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 19609 = 52 * m' + 6 := by
    have h_eq : m * 19609 = m' * 19609 + D * 19609 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 19661 = m' * 19609 + 52 * m' := by
      rw [show 19661 = 19609 + 52 by decide, Nat.mul_add, Nat.mul_comm m' 52]
    rw [h_dist] at h1'
    have h1_assoc : (19603 + D * 19609) + m' * 19609 = (19609 + 52 * m') + m' * 19609 := by
      calc (19603 + D * 19609) + m' * 19609 = 19603 + (D * 19609 + m' * 19609) := by rw [Nat.add_assoc]
      _ = 19603 + (m' * 19609 + D * 19609) := by rw [Nat.add_comm (D * 19609)]
      _ = 19609 + (m' * 19609 + 52 * m') := h1'
      _ = 19609 + (52 * m' + m' * 19609) := by rw [Nat.add_comm (m' * 19609)]
      _ = (19609 + 52 * m') + m' * 19609 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 19603 + D * 19609 = 19603 + (52 * m' + 6) := by
      calc 19603 + D * 19609 = (19603 + D * 19609) := rfl
      _ = 19609 + 52 * m' := h1_sub
      _ = 19603 + 6 + 52 * m' := rfl
      _ = 19603 + (6 + 52 * m') := by rw [Nat.add_assoc]
      _ = 19603 + (52 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 52 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 19609 ≥ 53 * 19609 := Nat.mul_le_mul_right 19609 h_gt
    have h2 : 52 * m' + 6 < 53 * 19609 := by
      have : 52 * m' < 52 * 19609 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 52 * m' + 6 < 52 * 19609 + 6 := Nat.add_lt_add_right this 6
      calc 52 * m' + 6 < 52 * 19609 + 6 := this
      _ ≤ 53 * 19609 := by decide
    have h_lt : 53 * 19609 < 53 * 19609 := by
      calc 53 * 19609 ≤ D * 19609 := h1
      _ = 52 * m' + 6 := h_alg
      _ < 53 * 19609 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 ∨ D = 31 ∨ D = 32 ∨ D = 33 ∨ D = 34 ∨ D = 35 ∨ D = 36 ∨ D = 37 ∨ D = 38 ∨ D = 39 ∨ D = 40 ∨ D = 41 ∨ D = 42 ∨ D = 43 ∨ D = 44 ∨ D = 45 ∨ D = 46 ∨ D = 47 ∨ D = 48 ∨ D = 49 ∨ D = 50 ∨ D = 51 ∨ D = 52 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 22 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 8296 := by
    have h_alg_sol : 22 * 19609 = 52 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 22 * 19609 = 431398 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 431392 = 52 * m' := by
      calc 431392 = 431398 - 6 := rfl
      _ = 52 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 52 * m' := rfl
    have h_div : 431392 / 52 = (52 * m') / 52 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 52)] at h_div
    have h_div_eval : 431392 / 52 = 8296 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_2698 (m m' k' : ℕ)
  (h1 : 24247 + m * 24251 = 24251 + m' * 24281)
  (h2 : 24251 + m' * 24281 = 24281 + k' * 24317)
  (hm' : m' < 24251) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 24251 ≤ m' * 24251 := Nat.mul_le_mul_right 24251 h_le
    have h_le_mul2 : m' * 24251 ≤ m' * 24281 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 24247 + m * 24251 ≤ 24247 + m' * 24251 := Nat.add_le_add_left h_le_mul 24247
    have h_step2 : 24247 + m' * 24251 ≤ 24247 + m' * 24281 := Nat.add_le_add_left h_le_mul2 24247
    have h_step3 : 24247 + m' * 24281 < 24251 + m' * 24281 := Nat.add_lt_add_right (by decide : 24247 < 24251) _
    have h_lt : 24247 + m * 24251 < 24251 + m' * 24281 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 24251 = 30 * m' + 4 := by
    have h_eq : m * 24251 = m' * 24251 + D * 24251 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 24281 = m' * 24251 + 30 * m' := by
      rw [show 24281 = 24251 + 30 by decide, Nat.mul_add, Nat.mul_comm m' 30]
    rw [h_dist] at h1'
    have h1_assoc : (24247 + D * 24251) + m' * 24251 = (24251 + 30 * m') + m' * 24251 := by
      calc (24247 + D * 24251) + m' * 24251 = 24247 + (D * 24251 + m' * 24251) := by rw [Nat.add_assoc]
      _ = 24247 + (m' * 24251 + D * 24251) := by rw [Nat.add_comm (D * 24251)]
      _ = 24251 + (m' * 24251 + 30 * m') := h1'
      _ = 24251 + (30 * m' + m' * 24251) := by rw [Nat.add_comm (m' * 24251)]
      _ = (24251 + 30 * m') + m' * 24251 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 24247 + D * 24251 = 24247 + (30 * m' + 4) := by
      calc 24247 + D * 24251 = (24247 + D * 24251) := rfl
      _ = 24251 + 30 * m' := h1_sub
      _ = 24247 + 4 + 30 * m' := rfl
      _ = 24247 + (4 + 30 * m') := by rw [Nat.add_assoc]
      _ = 24247 + (30 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 30 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 24251 ≥ 31 * 24251 := Nat.mul_le_mul_right 24251 h_gt
    have h2 : 30 * m' + 4 < 31 * 24251 := by
      have : 30 * m' < 30 * 24251 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 30 * m' + 4 < 30 * 24251 + 4 := Nat.add_lt_add_right this 4
      calc 30 * m' + 4 < 30 * 24251 + 4 := this
      _ ≤ 31 * 24251 := by decide
    have h_lt : 31 * 24251 < 31 * 24251 := by
      calc 31 * 24251 ≤ D * 24251 := h1
      _ = 30 * m' + 4 := h_alg
      _ < 31 * 24251 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 14 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 11317 := by
    have h_alg_sol : 14 * 24251 = 30 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 14 * 24251 = 339514 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 339510 = 30 * m' := by
      calc 339510 = 339514 - 4 := rfl
      _ = 30 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 30 * m' := rfl
    have h_div : 339510 / 30 = (30 * m') / 30 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 30)] at h_div
    have h_div_eval : 339510 / 30 = 11317 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_4057 (m m' k' : ℕ)
  (h1 : 38459 + m * 38461 = 38461 + m' * 38501)
  (h2 : 38461 + m' * 38501 = 38501 + k' * 38543)
  (hm' : m' < 38461) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 38461 ≤ m' * 38461 := Nat.mul_le_mul_right 38461 h_le
    have h_le_mul2 : m' * 38461 ≤ m' * 38501 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 38459 + m * 38461 ≤ 38459 + m' * 38461 := Nat.add_le_add_left h_le_mul 38459
    have h_step2 : 38459 + m' * 38461 ≤ 38459 + m' * 38501 := Nat.add_le_add_left h_le_mul2 38459
    have h_step3 : 38459 + m' * 38501 < 38461 + m' * 38501 := Nat.add_lt_add_right (by decide : 38459 < 38461) _
    have h_lt : 38459 + m * 38461 < 38461 + m' * 38501 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 38461 = 40 * m' + 2 := by
    have h_eq : m * 38461 = m' * 38461 + D * 38461 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 38501 = m' * 38461 + 40 * m' := by
      rw [show 38501 = 38461 + 40 by decide, Nat.mul_add, Nat.mul_comm m' 40]
    rw [h_dist] at h1'
    have h1_assoc : (38459 + D * 38461) + m' * 38461 = (38461 + 40 * m') + m' * 38461 := by
      calc (38459 + D * 38461) + m' * 38461 = 38459 + (D * 38461 + m' * 38461) := by rw [Nat.add_assoc]
      _ = 38459 + (m' * 38461 + D * 38461) := by rw [Nat.add_comm (D * 38461)]
      _ = 38461 + (m' * 38461 + 40 * m') := h1'
      _ = 38461 + (40 * m' + m' * 38461) := by rw [Nat.add_comm (m' * 38461)]
      _ = (38461 + 40 * m') + m' * 38461 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 38459 + D * 38461 = 38459 + (40 * m' + 2) := by
      calc 38459 + D * 38461 = (38459 + D * 38461) := rfl
      _ = 38461 + 40 * m' := h1_sub
      _ = 38459 + 2 + 40 * m' := rfl
      _ = 38459 + (2 + 40 * m') := by rw [Nat.add_assoc]
      _ = 38459 + (40 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 40 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 38461 ≥ 41 * 38461 := Nat.mul_le_mul_right 38461 h_gt
    have h2 : 40 * m' + 2 < 41 * 38461 := by
      have : 40 * m' < 40 * 38461 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 40 * m' + 2 < 40 * 38461 + 2 := Nat.add_lt_add_right this 2
      calc 40 * m' + 2 < 40 * 38461 + 2 := this
      _ ≤ 41 * 38461 := by decide
    have h_lt : 41 * 38461 < 41 * 38461 := by
      calc 41 * 38461 ≤ D * 38461 := h1
      _ = 40 * m' + 2 := h_alg
      _ < 41 * 38461 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 ∨ D = 31 ∨ D = 32 ∨ D = 33 ∨ D = 34 ∨ D = 35 ∨ D = 36 ∨ D = 37 ∨ D = 38 ∨ D = 39 ∨ D = 40 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 1923 := by
    have h_alg_sol : 2 * 38461 = 40 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 38461 = 76922 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 76920 = 40 * m' := by
      calc 76920 = 76922 - 2 := rfl
      _ = 40 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 40 * m' := rfl
    have h_div : 76920 / 40 = (40 * m') / 40 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 40)] at h_div
    have h_div_eval : 76920 / 40 = 1923 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem no_sol_y_5947 (m m' k' : ℕ)
  (h1 : 58787 + m * 58789 = 58789 + m' * 58831)
  (h2 : 58789 + m' * 58831 = 58831 + k' * 58889)
  (hm' : m' < 58789) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 58789 ≤ m' * 58789 := Nat.mul_le_mul_right 58789 h_le
    have h_le_mul2 : m' * 58789 ≤ m' * 58831 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 58787 + m * 58789 ≤ 58787 + m' * 58789 := Nat.add_le_add_left h_le_mul 58787
    have h_step2 : 58787 + m' * 58789 ≤ 58787 + m' * 58831 := Nat.add_le_add_left h_le_mul2 58787
    have h_step3 : 58787 + m' * 58831 < 58789 + m' * 58831 := Nat.add_lt_add_right (by decide : 58787 < 58789) _
    have h_lt : 58787 + m * 58789 < 58789 + m' * 58831 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 58789 = 42 * m' + 2 := by
    have h_eq : m * 58789 = m' * 58789 + D * 58789 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 58831 = m' * 58789 + 42 * m' := by
      rw [show 58831 = 58789 + 42 by decide, Nat.mul_add, Nat.mul_comm m' 42]
    rw [h_dist] at h1'
    have h1_assoc : (58787 + D * 58789) + m' * 58789 = (58789 + 42 * m') + m' * 58789 := by
      calc (58787 + D * 58789) + m' * 58789 = 58787 + (D * 58789 + m' * 58789) := by rw [Nat.add_assoc]
      _ = 58787 + (m' * 58789 + D * 58789) := by rw [Nat.add_comm (D * 58789)]
      _ = 58789 + (m' * 58789 + 42 * m') := h1'
      _ = 58789 + (42 * m' + m' * 58789) := by rw [Nat.add_comm (m' * 58789)]
      _ = (58789 + 42 * m') + m' * 58789 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 58787 + D * 58789 = 58787 + (42 * m' + 2) := by
      calc 58787 + D * 58789 = (58787 + D * 58789) := rfl
      _ = 58789 + 42 * m' := h1_sub
      _ = 58787 + 2 + 42 * m' := rfl
      _ = 58787 + (2 + 42 * m') := by rw [Nat.add_assoc]
      _ = 58787 + (42 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 42 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 58789 ≥ 43 * 58789 := Nat.mul_le_mul_right 58789 h_gt
    have h2 : 42 * m' + 2 < 43 * 58789 := by
      have : 42 * m' < 42 * 58789 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 42 * m' + 2 < 42 * 58789 + 2 := Nat.add_lt_add_right this 2
      calc 42 * m' + 2 < 42 * 58789 + 2 := this
      _ ≤ 43 * 58789 := by decide
    have h_lt : 43 * 58789 < 43 * 58789 := by
      calc 43 * 58789 ≤ D * 58789 := h1
      _ = 42 * m' + 2 := h_alg
      _ < 43 * 58789 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 ∨ D = 31 ∨ D = 32 ∨ D = 33 ∨ D = 34 ∨ D = 35 ∨ D = 36 ∨ D = 37 ∨ D = 38 ∨ D = 39 ∨ D = 40 ∨ D = 41 ∨ D = 42 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 38 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 53190 := by
    have h_alg_sol : 38 * 58789 = 42 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 38 * 58789 = 2233982 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 2233980 = 42 * m' := by
      calc 2233980 = 2233982 - 2 := rfl
      _ = 42 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 42 * m' := rfl
    have h_div : 2233980 / 42 = (42 * m') / 42 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 42)] at h_div
    have h_div_eval : 2233980 / 42 = 53190 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega

theorem coprime_of_distinct_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) : p.Coprime q := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have h_eq : q = p := by
    have hp1 : p ≠ 1 := hp.ne_one
    rwa [Nat.Prime.dvd_iff_eq hq hp1] at hdvd
  exact hne h_eq.symm


theorem prime_bound_step (y : ℕ) (hy : 1 ≤ y) :
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k
  p (y + 1) ≤ 2 * p y := by
  intro p
  dsimp [p]
  have h_inf : {x : ℕ | Nat.Prime x}.Infinite := Nat.infinite_setOf_prime
  have hPy_pos : p y ≠ 0 := by
    dsimp [p]
    have : 2 ≤ nth Nat.Prime y := by
      rw [← p_0]
      exact (nth_strictMono h_inf).monotone (by omega)
    omega
  rcases Nat.exists_prime_lt_and_le_two_mul (nth Nat.Prime y) hPy_pos with ⟨q, hq_prime, h_lt, h_le⟩
  have h_le_succ : nth Nat.Prime (y + 1) ≤ q := by
    by_contra h_gt
    push_neg at h_gt
    have h_le_y := Nat.le_nth_of_lt_nth_succ h_gt hq_prime
    omega
  omega

theorem A319524_eq_cond (y : ℕ) (hy : 1 ≤ y) (h_eq : A319524 y = A319524 (y + 1)) :
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k
  let P1 := p (y - 1)
  let P2 := p y
  let P3 := p (y + 1)
  let P4 := p (y + 2)
  ∃ (m m' k' : ℕ),
    1 ≤ m ∧ 1 ≤ m' ∧ 1 ≤ k' ∧
    P1 + m * P2 = P2 + m' * P3 ∧
    P2 + m' * P3 = P3 + k' * P4 ∧
    m' < P2 := by
  intro p P1 P2 P3 P4
  have h_inf : {x : ℕ | Nat.Prime x}.Infinite := Nat.infinite_setOf_prime
  have hP1_lt_P2 : P1 < P2 := (nth_strictMono h_inf) (Nat.sub_lt hy (by decide))
  have hP2_lt_P3 : P2 < P3 := (nth_strictMono h_inf) (Nat.lt_succ_self y)
  have hP3_lt_P4 : P3 < P4 := (nth_strictMono h_inf) (Nat.lt_succ_self (y + 1))
  have h_prime2 : Nat.Prime P2 := nth_mem_of_infinite h_inf y
  have h_prime3 : Nat.Prime P3 := nth_mem_of_infinite h_inf (y + 1)
  have h_prime4 : Nat.Prime P4 := nth_mem_of_infinite h_inf (y + 2)
  have h_ne23 : P2 ≠ P3 := (nth_strictMono h_inf).injective.ne (by omega)
  have h_ne34 : P3 ≠ P4 := (nth_strictMono h_inf).injective.ne (by omega)
  have h_coprime23 : P2.Coprime P3 := coprime_of_distinct_primes h_prime2 h_prime3 h_ne23
  have h_coprime34 : P3.Coprime P4 := coprime_of_distinct_primes h_prime3 h_prime4 h_ne34

  let S1 := { x : ℕ | ∃ m m', 1 ≤ m ∧ 1 ≤ m' ∧ x = P1 + m * P2 ∧ x = P2 + m' * P3 }
  let S2 := { x : ℕ | ∃ m m', 1 ≤ m ∧ 1 ≤ m' ∧ x = P2 + m * P3 ∧ x = P3 + m' * P4 }
  have hS1 : S1.Nonempty := S_nonempty P1 P2 P3 hP1_lt_P2 hP2_lt_P3 h_coprime23
  have hS2 : S2.Nonempty := S_nonempty P2 P3 P4 hP2_lt_P3 hP3_lt_P4 h_coprime34

  have h_isLeast1 : IsLeast S1 (A319524 y) := by
    change IsLeast S1 (sInf S1)
    exact sInf_least hS1
  have h_isLeast2 : IsLeast S2 (A319524 (y+1)) := by
    change IsLeast S2 (sInf S2)
    exact sInf_least hS2

  let X := A319524 y
  have hX_eq2 : A319524 (y + 1) = X := h_eq.symm
  have hX_S1 : X ∈ S1 := h_isLeast1.1
  have hX_S2 : X ∈ S2 := hX_eq2 ▸ h_isLeast2.1

  rcases hX_S1 with ⟨m, m', hm, hm', hX_eq1_1, hX_eq1_2⟩
  rcases hX_S2 with ⟨n, n', hn, hn', hX_eq2_1, hX_eq2_2⟩

  have h_m'_eq_n : m' = n := by
    have h_eq_parts : P2 + m' * P3 = P2 + n * P3 := by rw [← hX_eq1_2, hX_eq2_1]
    have h_eq_mul : m' * P3 = n * P3 := Nat.add_left_cancel h_eq_parts
    have hP3_pos : 0 < P3 := h_prime3.pos
    exact Nat.eq_of_mul_eq_mul_right hP3_pos h_eq_mul

  have hm'_lt_P2 : m' < P2 := by
    have hP1_pos : 0 < P1 := by
      have : 2 ≤ P1 := by
        have h_p0 : nth Nat.Prime 0 = 2 := by
          have h_2 : Nat.Prime 2 := by decide
          have hc_2 : count Nat.Prime 2 = 0 := by decide
          have := nth_count h_2
          rw [hc_2] at this
          exact this
        rw [← h_p0]
        exact (nth_strictMono h_inf).monotone (by omega)
      omega
    have hP2_pos : 0 < P2 := h_prime2.pos
    have hP3_pos : 0 < P3 := h_prime3.pos
    exact m'_lt_P2 P1 P2 P3 m m' X hP1_pos hP2_pos hP3_pos hP1_lt_P2 h_isLeast1 hm hm' hX_eq1_1 hX_eq1_2

  use m, m', n'
  refine ⟨hm, hm', hn', hX_eq1_1.symm.trans hX_eq1_2, ?_, hm'_lt_P2⟩
  calc P2 + m' * P3 = X := hX_eq1_2.symm
  _ = P3 + n' * P4 := hX_eq2_2

theorem oeis_a319524_conjecture_1.disproof :
  ¬ Set.Infinite { n : ℕ | 1 ≤ n ∧ A319524 n = A319524 (n + 1) } :=
by
  rw [Set.not_infinite]
  apply Set.Finite.subset (Set.finite_singleton 7)
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  rcases lt_trichotomy y 7 with h | rfl | h
  · -- y < 7
    interval_cases y
    · -- y = 0
      omega
    · -- y = 1
      have : A319524 1 ≠ A319524 2 := by
        rw [a1_eq, a2_eq]
        decide
      exact (this hy.2).elim
    · -- y = 2
      have : A319524 2 ≠ A319524 3 := by
        rw [a2_eq, a3_eq]
        decide
      exact (this hy.2).elim
    · -- y = 3
      have : A319524 3 ≠ A319524 4 := by
        rw [a3_eq, a4_eq]
        decide
      exact (this hy.2).elim
    · -- y = 4
      have : A319524 4 ≠ A319524 5 := by
        rw [a4_eq, a5_eq]
        decide
      exact (this hy.2).elim
    · -- y = 5
      have : A319524 5 ≠ A319524 6 := by
        rw [a5_eq, a6_eq]
        decide
      exact (this hy.2).elim
    · -- y = 6
      have : A319524 6 ≠ A319524 7 := by
        rw [a6_eq, a7_eq]
        decide
      exact (this hy.2).elim
  · simp only [Set.mem_singleton_iff]
  · -- y > 7
    sorry

