import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

namespace XNCompute

def N : ℕ := 201886 * 3 ^ 39101 - 1

def X (m : ℕ) := ZMod m × ZMod m

instance (m) : One (X m) := inferInstanceAs (One (ZMod m × ZMod m))
instance (m) : Add (X m) := inferInstanceAs (Add (ZMod m × ZMod m))
instance (m) : Neg (X m) := inferInstanceAs (Neg (ZMod m × ZMod m))
instance (m) : Sub (X m) := inferInstanceAs (Sub (ZMod m × ZMod m))

instance (m) : Mul (X m) where
  mul a b := (a.1*b.1 + 21*a.2*b.2, a.1*b.2 + a.2*b.1)


def pmul (m : ℕ) (a b : X m) : X m :=
  (a.1*b.1 + 21*a.2*b.2, a.1*b.2 + a.2*b.1)

def ppowAux (m : ℕ) (base acc : X m) (e : ℕ) : X m :=
  match e with
  | 0 => acc
  | k+1 =>
      if (k+1) % 2 = 1 then
        ppowAux m (pmul m base base) (pmul m acc base) ((k+1)/2)
      else
        ppowAux m (pmul m base base) acc ((k+1)/2)
termination_by e
decreasing_by
  all_goals omega

def ppow (m : ℕ) (a : X m) (e : ℕ) : X m :=
  ppowAux m a (1 : X m) e

def inv10 : ℕ := (7*N+1)/10

def rho : X N := (-(11 : ZMod N) * (inv10 : ZMod N), -(inv10 : ZMod N))

def diffgcd (a : X N) : ℕ := Nat.gcd (Nat.gcd ((a.1 - 1).val) (a.2.val)) N

example : ppow N rho (N+1) = (1 : X N) := by native_decide
--example : diffgcd (ppow N rho ((N+1)/2)) = 1 := by native_decide

end XNCompute
