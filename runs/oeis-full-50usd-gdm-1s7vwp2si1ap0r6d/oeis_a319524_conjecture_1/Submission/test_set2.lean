import FormalConjectures.Util.ProblemImports

open Nat

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

noncomputable def A319524 (n : ℕ) : ℕ :=
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k
  let Pn    := p (n - 1)
  let Pnp1  := p n
  let Pnp2  := p (n + 1)

  sInf { x : ℕ |
    ∃ (m m' : ℕ),
      1 ≤ m ∧ 1 ≤ m' ∧
      x = Pn + m * Pnp1 ∧
      x = Pnp1 + m' * Pnp2
  }

theorem sInf_eq_of_mem_and_le {s : Set ℕ} {a : ℕ} (ha : a ∈ s) (hle : ∀ x ∈ s, a ≤ x) : sInf s = a := by
  have h_least : IsLeast s a := ⟨ha, hle⟩
  exact IsLeast.csInf_eq h_least

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

theorem alg_step1 (Pn Pnp1 Pnp2 Pnp3 : ℕ) (m m' k' : ℕ)
  (h1 : Pn + m * Pnp1 = Pnp1 + m' * Pnp2)
  (h2 : Pnp1 + m' * Pnp2 = Pnp2 + k' * Pnp3)
  (hm : 1 ≤ m) (hm' : 1 ≤ m') (hk' : 1 ≤ k')
  (hPn : Pn < Pnp1) (hPnp1 : Pnp1 < Pnp2) (hPnp2 : Pnp2 < Pnp3) :
  m' ≤ m - 1 ∧ k' ≤ m' - 1 := by
  constructor
  · by omega
  · by omega

















