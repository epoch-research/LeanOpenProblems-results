import FormalConjectures.Util.ProblemImports

namespace Test

def N : Nat := 201886 * 3 ^ 39101 - 1

structure M2 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving BEq

def mmul (m : Nat) (x y : M2) : M2 :=
  ⟨(x.a*y.a + x.b*y.c) % m, (x.a*y.b + x.b*y.d) % m,
   (x.c*y.a + x.d*y.c) % m, (x.c*y.b + x.d*y.d) % m⟩

def mpowBinAux (m : Nat) (base acc : M2) (e : Nat) : M2 :=
  match e with
  | 0 => acc
  | k + 1 =>
      if (k + 1) % 2 = 1 then
        mpowBinAux m (mmul m base base) (mmul m acc base) ((k + 1) / 2)
      else
        mpowBinAux m (mmul m base base) acc ((k + 1) / 2)
termination_by e
decreasing_by
  all_goals omega

def mpowBin (m : Nat) (base : M2) (e : Nat) : M2 :=
  mpowBinAux m base ⟨1 % m,0,0,1 % m⟩ e

def Umod (e m : Nat) : Nat :=
  if e = 0 then 0 else
    let M := mpowBin m ⟨1 % m, 5 % m, 1 % m, 0⟩ (e-1)
    M.a % m

example : Umod (N+1) N = 0 := by native_decide

end Test
