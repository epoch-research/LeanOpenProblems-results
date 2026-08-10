import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000


open Nat Set

noncomputable def a354747 (n : ℕ) : ℕ :=
  let prime_steps : Set ℕ :=
    { m : ℕ | m > 0 ∧ Nat.Prime (2 * n * 3 ^ m - 1) }
  sInf prime_steps

namespace Cert39101

def N : ℕ := 201886 * 3 ^ 39101 - 1

def inv10 : ℕ := (7 * N + 1) / 10

structure P where
  x : ℕ
  y : ℕ
  deriving BEq, Repr, DecidableEq

def pmul (m : ℕ) (a b : P) : P :=
  ⟨(a.x*b.x + 21*a.y*b.y) % m, (a.x*b.y + a.y*b.x) % m⟩

def pone (m : ℕ) : P := ⟨1 % m, 0⟩

def rho (m : ℕ) : P :=
  let i := inv10 % m
  ⟨((m - (11 % m)) * i) % m, ((m - (1 % m)) * i) % m⟩

def ppowAux (m : ℕ) (base acc : P) (e : ℕ) : P :=
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

def ppow (m : ℕ) (a : P) (e : ℕ) : P :=
  ppowAux m a (pone m) e

def pdiffgcd (a : P) (m : ℕ) : ℕ :=
  Nat.gcd (Nat.gcd ((a.x + m - 1) % m) (a.y % m)) m

-- The three computational certificate checks.  Each is a closed native computation.
theorem cert_pow : ppow N (rho N) (N + 1) = pone N := by native_decide

theorem cert_2 : pdiffgcd (ppow N (rho N) ((N + 1) / 2)) N = 1 := by native_decide

theorem cert_3 : pdiffgcd (ppow N (rho N) ((N + 1) / 3)) N = 1 := by native_decide

theorem cert_100943 : pdiffgcd (ppow N (rho N) ((N + 1) / 100943)) N = 1 := by native_decide

end Cert39101
