import FormalConjectures.Util.ProblemImports
open Matrix Nat
#check Rat.intCast_eq_mk
#check Rat.coe_int_num_of_den_eq_one
#check Rat.num_div_den
#check Int.cast_surjective
#check Rat.exists_eq_num_div_den
#check Rat.den_nz
#check Rat.den_ne_zero
#check Set.mem_range
example (q : ℚ) : q ∈ Set.range (Int.cast : ℤ → ℚ) ↔ q.den = 1 := by
  constructor
  · rintro ⟨z, hz⟩; rw [← hz]; simp
  · intro h; exact ⟨q.num, Rat.coe_int_num_of_den_eq_one h⟩
