import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace PIT

def N : Nat := 201886 * 3 ^ 39101 - 1
def inv5 : Nat := (2*N + 1) / 5

structure Elt where
  u : Nat
  v : Nat
  deriving BEq, Repr, DecidableEq

def emul (m : Nat) (x y : Elt) : Elt :=
  ⟨(x.u*y.u + x.u*y.v + x.v*y.u) % m,
   (5*x.u*y.u + x.v*y.v) % m⟩

def stepAcc (m : Nat) (base acc : Elt) (e : Nat) : Elt :=
  if e % 2 = 1 then emul m acc base else acc

def one (m : Nat) : Elt := ⟨0,1 % m⟩
def gamma (m : Nat) : Elt := ⟨(m - (inv5 % m)) % m, (m - (1 % m)) % m⟩

structure State where
  base : Elt
  a1 : Elt
  a2 : Elt
  a3 : Elt
  a4 : Elt
  e1 : Nat
  e2 : Nat
  e3 : Nat
  e4 : Nat

def advStep (m : Nat) (s : State) : State :=
  { base := emul m s.base s.base,
    a1 := stepAcc m s.base s.a1 s.e1,
    a2 := stepAcc m s.base s.a2 s.e2,
    a3 := stepAcc m s.base s.a3 s.e3,
    a4 := stepAcc m s.base s.a4 s.e4,
    e1 := s.e1/2, e2 := s.e2/2, e3 := s.e3/2, e4 := s.e4/2 }

def advPow : Nat → Nat → State → State
| 0, m, s => advStep m s
| k+1, m, s => advPow k m (advPow k m s)

def adv70000 (m : Nat) (s : State) : State :=
  advPow 4 m (advPow 5 m (advPow 6 m (advPow 8 m (advPow 12 m (advPow 16 m s)))))
-- 2^16+2^12+2^8+2^6+2^5+2^4 = 70000

def epow4 (m e1 e2 e3 e4 : Nat) : Elt × Elt × Elt × Elt :=
  let s := adv70000 m { base := gamma m, a1 := one m, a2 := one m, a3 := one m, a4 := one m, e1 := e1, e2 := e2, e3 := e3, e4 := e4 }
  (s.a1,s.a2,s.a3,s.a4)

def certTuple : Elt × Elt × Elt × Elt := epow4 N (N+1) ((N+1)/2) ((N+1)/3) ((N+1)/100943)

def diffGcd (x : Elt) (m : Nat) : Nat :=
  Nat.gcd (Nat.gcd (x.u % m) ((x.v + m - 1) % m)) m

def good : Bool :=
  let t := certTuple
  t.1 == one N &&
  diffGcd t.2.1 N == 1 &&
  diffGcd t.2.2.1 N == 1 &&
  diffGcd t.2.2.2 N == 1

theorem certAll : good = true := by decide +kernel

end PIT
