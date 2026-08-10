import FormalConjectures.Util.ProblemImports

lemma sq_add_two_sq_mul {a b u v : ℤ} :
    (a^2 + 2*b^2) * (u^2 + 2*v^2) = (a*u - 2*b*v)^2 + 2*(a*v + b*u)^2 := by
  ring

lemma Nat.sq_add_two_sq_mul {a b x y u v : ℕ}
    (ha : a = x^2 + 2*y^2) (hb : b = u^2 + 2*v^2) :
    ∃ r s : ℕ, a*b = r^2 + 2*s^2 := by
  zify at ha hb ⊢
  refine ⟨(x*u - 2*y*v).natAbs, (x*v + y*u).natAbs, ?_⟩
  simp only [Int.natCast_natAbs, sq_abs]
  rw [ha, hb]
  ring
