import FormalConjectures.Util.ProblemImports
open Rat Nat

example (p : ℕ) (hp : p.Prime) (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : IsSquare (5 : ZMod p) := by
  have hp2 : p ≠ 2 := by
    intro h; subst h; norm_num [Nat.ModEq] at hmod
  have hp5 : p ≠ 5 := by
    intro h; subst h; norm_num [Nat.ModEq] at hmod
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs : IsSquare ((p : ℕ) : ZMod 5) := by
    rcases hmod with h1 | h9
    · have hpmod5 : p % 5 = 1 := by
        rw [Nat.ModEq] at h1
        omega
      use (1 : ZMod 5)
      rw [← ZMod.natCast_mod p 5, hpmod5]
      norm_num
    · have hpmod5 : p % 5 = 4 := by
        rw [Nat.ModEq] at h9
        omega
      use (2 : ZMod 5)
      rw [← ZMod.natCast_mod p 5, hpmod5]
      norm_num
  have hiff := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p:=5) (q:=p) (by norm_num) hp2)
  exact hiff.mp hs
