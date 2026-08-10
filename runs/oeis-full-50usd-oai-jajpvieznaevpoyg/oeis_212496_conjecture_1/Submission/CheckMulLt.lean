import FormalConjectures.Util.ProblemImports
#check mul_lt_mul_right
#check mul_lt_mul_left
#check (mul_lt_mul_right : ∀ {α} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α] {a b c : α}, 0 < c → (a * c < b * c ↔ a < b))
