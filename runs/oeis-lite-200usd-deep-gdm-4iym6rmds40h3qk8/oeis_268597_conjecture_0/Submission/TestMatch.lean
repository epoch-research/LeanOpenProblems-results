import Mathlib

open Nat

theorem spec_lt_5 : (n : ℕ) → n < 5 → ∃ x > 0, (x - 1) % Nat.totient x = n
  | 0, _ => ⟨1, by decide⟩
  | 1, _ => ⟨4, by decide⟩
  | 2, _ => ⟨9, by decide⟩
  | 3, _ => ⟨8, by decide⟩
  | 4, _ => ⟨25, by decide⟩
  | n + 5, h => by omega
