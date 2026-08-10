import FormalConjectures.Util.ProblemImports

lemma Nat.sq_add_two_sq_mul {a b x y u v : ℕ}
    (ha : a = x^2 + 2*y^2) (hb : b = u^2 + 2*v^2) :
    ∃ r s : ℕ, a*b = r^2 + 2*s^2 := by
  have hz : ((a:ℤ) * (b:ℤ)) = ((x:ℤ)*u - 2*(y:ℤ)*v)^2 + 2*((x:ℤ)*v + (y:ℤ)*u)^2 := by
    rw [ha, hb]
    norm_num
    ring
  refine ⟨Int.natAbs ((x:ℤ)*u - 2*(y:ℤ)*v), Int.natAbs ((x:ℤ)*v + (y:ℤ)*u), ?_⟩
  rw [← Nat.cast_inj (R:=ℤ)]
  push_cast
  rw [hz]
  simp only [Int.natCast_natAbs, sq_abs]

#check ZMod.exists_sq_eq_neg_two_iff
#check ZMod.exists_sq_eq_neg_one_iff
