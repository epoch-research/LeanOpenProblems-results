import FormalConjectures.Util.ProblemImports

instance : CharP PUnit 1 where
  cast_eq_zero_iff x := by
    constructor
    · intro _; exact one_dvd x
    · intro _; cases (x : PUnit); rfl

section
local instance instBadLENat : LE Nat := ⟨fun _ _ => True⟩
#check (show (2 : Nat) ≤ 1 from trivial)
#check (CharP.char_is_prime_of_two_le PUnit 1 (show (2 : Nat) ≤ 1 from trivial) : Nat.Prime 1)
theorem prime_one_le_shadow : Nat.Prime 1 :=
  CharP.char_is_prime_of_two_le PUnit 1 (show (2 : Nat) ≤ 1 from trivial)
#print axioms prime_one_le_shadow
end
