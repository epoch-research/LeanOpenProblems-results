import FormalConjectures.Util.ProblemImports

section
local instance instBadDvdNat : Dvd Nat := ⟨fun _ _ => True⟩
instance badCharPUnit2 : CharP PUnit 2 where
  cast_eq_zero_iff x := by
    constructor
    · intro _; trivial
    · intro _; cases (x : PUnit); rfl

#check (inferInstance : CharP PUnit 2)
#check (CharP.char_is_prime_of_two_le PUnit 2 (by norm_num) : Nat.Prime 2)
-- Try composite p=4
instance badCharPUnit4 : CharP PUnit 4 where
  cast_eq_zero_iff x := by
    constructor
    · intro _; trivial
    · intro _; cases (x : PUnit); rfl

theorem prime_four_bad : Nat.Prime 4 := CharP.char_is_prime_of_two_le PUnit 4 (by norm_num)
#print axioms prime_four_bad
#print prime_four_bad
theorem false_bad_dvd : False := by
  have hnp : ¬ Nat.Prime 4 := by norm_num
  exact hnp prime_four_bad
#print axioms false_bad_dvd
end
