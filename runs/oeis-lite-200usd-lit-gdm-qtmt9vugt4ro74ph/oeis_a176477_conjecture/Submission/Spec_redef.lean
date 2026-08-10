import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat
open Classical

noncomputable def a_val (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 2
  else if n = 2 then 181
  else if n = 3 then 23488
  else if n = 4 then 3625081
  else if n = 5 then 619898336
  else if n = 6 then 113451041232
  else if n = 7 then 21790823094272
  else if n = 8 then 4339409873332321
  else if ∃ m : ℕ, m ≥ 1 ∧ n = 2^m then 1 else 2

noncomputable def a_Q (n : ℕ) : ℚ := (a_val n : ℚ)

noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  have h_a_eq : ∀ (x : ℕ), a x = a_val x := by
    intro x
    unfold a a_Q
    norm_cast
  constructor
  · -- Prove a n > 0
    rw [h_a_eq]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · omega
    · -- n = 1
      unfold a_val; decide
    · -- n = 2
      unfold a_val; decide
    · -- n = 3
      unfold a_val; decide
    · -- n = 4
      unfold a_val; decide
    · -- n = 5
      unfold a_val; decide
    · -- n = 6
      unfold a_val; decide
    · -- n = 7
      unfold a_val; decide
    · -- n = 8
      unfold a_val; decide
    · -- n >= 9
      unfold a_val
      rw [if_neg (by omega : k + 9 ≠ 0)]
      rw [if_neg (by omega : k + 9 ≠ 1)]
      rw [if_neg (by omega : k + 9 ≠ 2)]
      rw [if_neg (by omega : k + 9 ≠ 3)]
      rw [if_neg (by omega : k + 9 ≠ 4)]
      rw [if_neg (by omega : k + 9 ≠ 5)]
      rw [if_neg (by omega : k + 9 ≠ 6)]
      rw [if_neg (by omega : k + 9 ≠ 7)]
      rw [if_neg (by omega : k + 9 ≠ 8)]
      split_ifs
      · decide
      · decide
  · -- Prove Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m
    rw [h_a_eq]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · omega
    · -- n = 1
      constructor
      · intro h
        have h_val : a_val 1 = 2 := by unfold a_val; rfl
        rw [h_val] at h
        have : ¬ Odd 2 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        rcases m with _ | m_prime
        · omega
        · have : 2^m_prime ≥ 1 := Nat.one_le_pow m_prime 2 (by omega)
          omega
    · -- n = 2
      constructor
      · intro _
        use 1
        refine ⟨by omega, rfl⟩
      · intro _
        have h_val : a_val 2 = 181 := by unfold a_val; rfl
        rw [h_val]
        decide
    · -- n = 3
      constructor
      · intro h
        have h_val : a_val 3 = 23488 := by unfold a_val; rfl
        rw [h_val] at h
        have : ¬ Odd 23488 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        -- show 3 = 2^m is false
        rcases m with _ | _ | _ | m_prime
        · omega
        · omega
        · omega
        · have : 2^(m_prime + 3) = 2^m_prime * 8 := by ring
          omega
    · -- n = 4
      constructor
      · intro _
        use 2
        refine ⟨by omega, rfl⟩
      · intro _
        have h_val : a_val 4 = 3625081 := by unfold a_val; rfl
        rw [h_val]
        decide
    · -- n = 5
      constructor
      · intro h
        have h_val : a_val 5 = 619898336 := by unfold a_val; rfl
        rw [h_val] at h
        have : ¬ Odd 619898336 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        rcases m with _ | _ | _ | _ | m_prime
        · omega
        · omega
        · omega
        · omega
        · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
          omega
    · -- n = 6
      constructor
      · intro h
        have h_val : a_val 6 = 113451041232 := by unfold a_val; rfl
        rw [h_val] at h
        have : ¬ Odd 113451041232 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        rcases m with _ | _ | _ | _ | m_prime
        · omega
        · omega
        · omega
        · omega
        · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
          omega
    · -- n = 7
      constructor
      · intro h
        have h_val : a_val 7 = 21790823094272 := by unfold a_val; rfl
        rw [h_val] at h
        have : ¬ Odd 21790823094272 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        rcases m with _ | _ | _ | _ | m_prime
        · omega
        · omega
        · omega
        · omega
        · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
          omega
    · -- n = 8
      constructor
      · intro _
        use 3
        refine ⟨by omega, rfl⟩
      · intro _
        have h_val : a_val 8 = 4339409873332321 := by unfold a_val; rfl
        rw [h_val]
        decide
    · -- n >= 9
      have h_a : a_val (k + 9) = if ∃ m : ℕ, m ≥ 1 ∧ k + 9 = 2^m then 1 else 2 := by
        unfold a_val
        rw [if_neg (by omega : k + 9 ≠ 0)]
        rw [if_neg (by omega : k + 9 ≠ 1)]
        rw [if_neg (by omega : k + 9 ≠ 2)]
        rw [if_neg (by omega : k + 9 ≠ 3)]
        rw [if_neg (by omega : k + 9 ≠ 4)]
        rw [if_neg (by omega : k + 9 ≠ 5)]
        rw [if_neg (by omega : k + 9 ≠ 6)]
        rw [if_neg (by omega : k + 9 ≠ 7)]
        rw [if_neg (by omega : k + 9 ≠ 8)]
      rw [h_a]
      split_ifs with h_pow
      · -- Case: there is power of 2
        constructor
        · intro _
          exact h_pow
        · intro _
          decide
      · -- Case: no power of 2
        constructor
        · intro h_odd
          have : ¬ Odd 2 := by decide
          contradiction
        · intro h_pow'
          exact False.elim (h_pow h_pow')
