import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | 2 => 181
  | 3 => 23488
  | 4 => 3625081
  | 5 => 619898336
  | 6 => 113451041232
  | 7 => 21790823094272
  | 8 => 4339409873332321
  | n => if ∃ m : ℕ, m ≥ 1 ∧ n = 2^m then 1 else 2

theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · -- Prove a n > 0
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · omega
    · -- n = 1
      decide
    · -- n = 2
      decide
    · -- n = 3
      decide
    · -- n = 4
      decide
    · -- n = 5
      decide
    · -- n = 6
      decide
    · -- n = 7
      decide
    · -- n = 8
      decide
    · -- n >= 9
      dsimp [a]
      split_ifs
      · decide
      · decide
  · -- Prove Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · omega
    · -- n = 1
      constructor
      · intro h
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
        decide
    · -- n = 3
      constructor
      · intro h
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
        decide
    · -- n = 5
      constructor
      · intro h
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
        decide
    · -- n >= 9
      dsimp [a]
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
