import FormalConjectures.Util.ProblemImports

instance : CharP PUnit 1 where
  cast_eq_zero_iff x := by
    constructor
    · intro _; exact one_dvd x
    · intro _; cases (x : PUnit); rfl

section
local instance instBadOfNat4 : OfNat Nat 4 := ⟨1⟩
#check ((4 : Nat) : Nat)
#eval (4 : Nat)
-- This theorem's type is actually Nat.Prime 1 if local instance is used.
example : Nat.Prime (4 : Nat) := by
  -- Need standard 2 ≤ (4:Nat), but (4:Nat)=1 under local instance, so impossible.
  fail_if_success exact CharP.char_is_prime_of_two_le PUnit (4 : Nat) (by norm_num)
  admit
-- Could a contradiction result from the printed expression reducing to 1?
example : False := by
  have hp : Nat.Prime (4 : Nat) := by
    fail_if_success exact CharP.char_is_prime_of_two_le PUnit (4 : Nat) (by norm_num)
    admit
  have h4 : (4 : Nat) = 1 := rfl
  exact Nat.not_prime_one (by simpa [h4] using hp)
end
