import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def N : Nat := 201886 * 3 ^ 39101 - 1
def inv5 : Nat := (2*N + 1) / 5
structure Elt where
  u : Nat
  v : Nat
  deriving BEq, DecidableEq

def emul (m : Nat) (x y : Elt) : Elt :=
  ⟨(x.u*y.u + x.u*y.v + x.v*y.u) % m, (5*x.u*y.u + x.v*y.v) % m⟩
def gamma (m : Nat) : Elt := ⟨(m - (inv5 % m)) % m, (m - (1 % m)) % m⟩

def testBool : Bool := (emul N (gamma N) (gamma N)).u == (emul N (gamma N) (gamma N)).u

theorem one_big_op : testBool = true := by decide +kernel
