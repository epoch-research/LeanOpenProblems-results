import FormalConjecturesUtil
example {F : Type*} [Field F] (x y z : F) : ![x, y, z] (2 : Fin 3) = z := by rfl
example {F : Type*} [Field F] (x y z : F) :
  Matrix.det !![x, y, z; y, x, z; z, y, x] =
  x*x*x-x*z*y-y*y*x+y*z*z+z*y*y-z*x*z := by
  rw [Matrix.det_fin_three]
  rfl
