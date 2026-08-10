import FormalConjectures.Util.ProblemImports
open scoped Pointwise

-- Check concrete forms
#eval decide ((Finset.image (fun k : ℕ => 2 * k) (Finset.Iio 3)) = Finset.Iio (3+1))
#eval decide ((Finset.image (fun k : ℕ => 2 * k) (Finset.Iio 2)) = ((Finset.Iio 2).filter Even))

example : False := by
  have h := Nat.image_mul_two_Iio (n:=3)
  norm_num at h

#print axioms Nat.image_mul_two_Iio
