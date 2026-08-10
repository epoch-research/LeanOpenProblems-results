import FormalConjectures.Util.ProblemImports

instance : CharP PUnit 1 where
  cast_eq_zero_iff x := by
    constructor
    · intro _; exact one_dvd x
    · intro _; cases (x : PUnit); rfl

section
local instance instBadOfNat4 : OfNat Nat 4 := ⟨1⟩
#eval (4 : Nat)
example : Nat.Prime (4 : Nat) := by
  exact CharP.char_is_prime_of_two_le PUnit (4 : Nat) (by norm_num)

example : False := by
  have hp : Nat.Prime (4 : Nat) := by
    exact CharP.char_is_prime_of_two_le PUnit (4 : Nat) (by norm_num)
  have h4 : (4 : Nat) = 1 := rfl
  exact Nat.not_prime_one (by simpa [h4] using hp)
end
