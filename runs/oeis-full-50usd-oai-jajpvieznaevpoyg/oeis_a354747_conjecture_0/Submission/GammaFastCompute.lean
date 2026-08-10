import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

namespace GammaFast

def N : Nat := 201886 * 3 ^ 39101 - 1

def inv5 : Nat := (2*N + 1) / 5

structure Elt where
  u : Nat
  v : Nat
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

def epow (m : Nat) (a : Elt) (e : Nat) : Elt :=
  epowAux m a ⟨0, 1 % m⟩ e

-- gamma = -inv5 * alpha - 1
def gamma (m : Nat) : Elt := ⟨(m - (inv5 % m)) % m, (m - (1 % m)) % m⟩

def diffGcd (x : Elt) (m : Nat) : Nat :=
  Nat.gcd (Nat.gcd (x.u % m) ((x.v + m - 1) % m)) m

theorem certPow : epow N (gamma N) (N+1) = ⟨0,1 % N⟩ := by native_decide

theorem cert2 : diffGcd (epow N (gamma N) ((N+1)/2)) N = 1 := by native_decide

theorem cert3 : diffGcd (epow N (gamma N) ((N+1)/3)) N = 1 := by native_decide

theorem cert100943 : diffGcd (epow N (gamma N) ((N+1)/100943)) N = 1 := by native_decide

end GammaFast
