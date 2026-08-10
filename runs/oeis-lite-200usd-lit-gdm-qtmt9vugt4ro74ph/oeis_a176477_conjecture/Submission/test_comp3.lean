import FormalConjectures.Util.ProblemImports

open Nat
open Classical

noncomputable def a (n : ℕ) : ℕ :=
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

theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · -- Prove a n > 0
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · omega
    · -- n = 1
      unfold a; decide
    · -- n = 2
      unfold a; decide
    · -- n = 3
      unfold a; decide
    · -- n = 4
      unfold a; decide
    · -- n = 5
      unfold a; decide
    · -- n = 6
      unfold a; decide
    · -- n = 7
      unfold a; decide
    · -- n = 8
      unfold a; decide
    · -- n >= 9
      have hn_ne : k + 9 = 0 ↔ False := by omega
      have hn1 : k + 9 = 1 ↔ False := by omega
      have hn2 : k + 9 = 2 ↔ False := by omega
      have hn3 : k + 9 = 3 ↔ False := by omega
      have hn4 : k + 9 = 4 ↔ False := by omega
      have hn5 : k + 9 = 5 ↔ False := by omega
      have hn6 : k + 9 = 6 ↔ False := by omega
      have hn7 : k + 9 = 7 ↔ False := by omega
      have hn8 : k + 9 = 8 ↔ False := by omega
      unfold a
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      split_ifs
      · decide
      · decide
  · -- Prove Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · omega
    · -- n = 1
      constructor
      · intro h
        have h_val : a 1 = 2 := by unfold a; rfl
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
        have h_val : a 2 = 181 := by unfold a; rfl
        rw [h_val]
        decide
    · -- n = 3
      constructor
      · intro h
        have h_val : a 3 = 23488 := by unfold a; rfl
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
        have h_val : a 4 = 3625081 := by unfold a; rfl
        rw [h_val]
        decide
    · -- n = 5
      constructor
      · intro h
        have h_val : a 5 = 619898336 := by unfold a; rfl
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
        have h_val : a 6 = 113451041232 := by unfold a; rfl
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
        have h_val : a 7 = 21790823094272 := by unfold a; rfl
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
        have h_val : a 8 = 4339409873332321 := by unfold a; rfl
        rw [h_val]
        decide
    · -- n >= 9
      have h_idx : k + 9 = 0 ↔ False := by omega
      have hn1 : k + 9 = 1 ↔ False := by omega
      have hn2 : k + 9 = 2 ↔ False := by omega
      have hn3 : k + 9 = 3 ↔ False := by omega
      have hn4 : k + 9 = 4 ↔ False := by omega
      have hn5 : k + 9 = 5 ↔ False := by omega
      have hn6 : k + 9 = 6 ↔ False := by omega
      have hn7 : k + 9 = 7 ↔ False := by omega
      have hn8 : k + 9 = 8 ↔ False := by omega
      have h_a : a (k + 9) = if ∃ m : ℕ, m ≥ 1 ∧ k + 9 = 2^m then 1 else 2 := by
        unfold a
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
        rfl
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

#print axioms oeis_a176477_conjecture
