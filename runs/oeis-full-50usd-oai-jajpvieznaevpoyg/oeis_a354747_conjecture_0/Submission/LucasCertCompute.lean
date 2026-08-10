import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

namespace LucasCert

def N : Nat := 201886 * 3 ^ 39101 - 1

structure M2 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving BEq, Repr, DecidableEq

def mmul (m : Nat) (x y : M2) : M2 :=
  ⟨(x.a*y.a + x.b*y.c) % m, (x.a*y.b + x.b*y.d) % m,
   (x.c*y.a + x.d*y.c) % m, (x.c*y.b + x.d*y.d) % m⟩

def mpowAux (m : Nat) (base acc : M2) (e : Nat) : M2 :=
  match e with
  | 0 => acc
  | k+1 =>
      if (k+1) % 2 = 1 then
        mpowAux m (mmul m base base) (mmul m acc base) ((k+1)/2)
      else
        mpowAux m (mmul m base base) acc ((k+1)/2)
termination_by e
decreasing_by all_goals omega

def mpow (m : Nat) (base : M2) (e : Nat) : M2 :=
  mpowAux m base ⟨1 % m,0,0,1 % m⟩ e

-- Companion matrix for Lucas U(P=1,Q=-5): [[1,5],[1,0]].
def A (m : Nat) : M2 := ⟨1 % m, 5 % m, 1 % m, 0⟩

def Umod (e m : Nat) : Nat :=
  if e = 0 then 0 else (mpow m (A m) (e-1)).a % m

-- These are the Lucas certificate computations for D=21, P=1, Q=-5.
theorem certU : Umod (N+1) N = 0 := by native_decide

theorem cert2 : Nat.gcd (Umod ((N+1)/2) N) N = 1 := by native_decide

theorem cert3 : Nat.gcd (Umod ((N+1)/3) N) N = 1 := by native_decide

theorem cert100943 : Nat.gcd (Umod ((N+1)/100943) N) N = 1 := by native_decide

end LucasCert
