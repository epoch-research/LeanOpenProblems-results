import FormalConjectures.Util.ProblemImports

#print CharP.char_is_prime_of_two_le

instance : CharP PUnit 1 where
  cast_eq_zero_iff x := by
    constructor
    · intro _; exact one_dvd x
    · intro _; cases (x : PUnit); rfl

section
local instance instBadTwo : OfNat Nat 2 := ⟨0⟩
#check (show (2 : Nat) ≤ 1 from by norm_num)
#eval (2 : Nat)
-- Try applying theorem with bad local numeral instance.
#check (CharP.char_is_prime_of_two_le PUnit 1 (show (2 : Nat) ≤ 1 from by norm_num) : Nat.Prime 1)
theorem prime_one_via_bad_two : Nat.Prime 1 :=
  CharP.char_is_prime_of_two_le PUnit 1 (show (2 : Nat) ≤ 1 from by norm_num)
#print prime_one_via_bad_two
#print axioms prime_one_via_bad_two
theorem false_via_bad_two : False := Nat.not_prime_one prime_one_via_bad_two
#print axioms false_via_bad_two
end
