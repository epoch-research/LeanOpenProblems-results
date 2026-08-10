import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

namespace LucasFast

def N : Nat := 201886 * 3 ^ 39101 - 1

structure Elt where
  u : Nat -- coefficient of alpha
  v : Nat -- constant term
  deriving BEq, Repr, DecidableEq

-- (u α + v)(u' α + v') with α^2 = α + 5
def emul (m : Nat) (x y : Elt) : Elt :=
  ⟨(x.u*y.u + x.u*y.v + x.v*y.u) % m,
   (5*x.u*y.u + x.v*y.v) % m⟩

def epowAux (m : Nat) (base acc : Elt) (e : Nat) : Elt :=
  match e with
  | 0 => acc
  | k+1 =>
      if (k+1) % 2 = 1 then
        epowAux m (emul m base base) (emul m acc base) ((k+1)/2)
      else
        epowAux m (emul m base base) acc ((k+1)/2)
termination_by e
decreasing_by all_goals omega

def epow (m : Nat) (e : Nat) : Elt :=
  epowAux m ⟨1 % m, 0⟩ ⟨0, 1 % m⟩ e

def Umod (e m : Nat) : Nat := (epow m e).u % m

theorem certU : Umod (N+1) N = 0 := by native_decide

theorem cert3 : Nat.gcd (Umod ((N+1)/3) N) N = 1 := by native_decide

theorem cert100943 : Nat.gcd (Umod ((N+1)/100943) N) N = 1 := by native_decide


theorem cert2 : Nat.gcd (Umod ((N+1)/2) N) N = 1 := by native_decide

end LucasFast
