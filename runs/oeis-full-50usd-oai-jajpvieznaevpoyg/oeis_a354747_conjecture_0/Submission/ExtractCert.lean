import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
namespace E

def N : Nat := 201886 * 3 ^ 39101 - 1
def inv5 : Nat := (2*N + 1) / 5
structure Elt where
  u : Nat
  v : Nat
  deriving BEq, Repr, DecidableEq

def emul (m : Nat) (x y : Elt) : Elt := ⟨(x.u*y.u + x.u*y.v + x.v*y.u) % m, (5*x.u*y.u + x.v*y.v) % m⟩
def stepAcc (m : Nat) (base acc : Elt) (e : Nat) : Elt := if e % 2 = 1 then emul m acc base else acc
def one (m : Nat) : Elt := ⟨0,1 % m⟩
def gamma (m : Nat) : Elt := ⟨(m - (inv5 % m)) % m, (m - (1 % m)) % m⟩
def epow4Aux : Nat → Nat → Elt → Elt → Elt → Elt → Elt → Nat → Nat → Nat → Nat → Elt × Elt × Elt × Elt
| 0,m,base,a1,a2,a3,a4,e1,e2,e3,e4 => (a1,a2,a3,a4)
| f+1,m,base,a1,a2,a3,a4,e1,e2,e3,e4 =>
 let b:=emul m base base
 epow4Aux f m b (stepAcc m base a1 e1) (stepAcc m base a2 e2) (stepAcc m base a3 e3) (stepAcc m base a4 e4) (e1/2) (e2/2) (e3/2) (e4/2)
def certTuple := epow4Aux 70000 N (gamma N) (one N) (one N) (one N) (one N) (N+1) ((N+1)/2) ((N+1)/3) ((N+1)/100943)
def diffGcd (x : Elt) (m : Nat) := Nat.gcd (Nat.gcd (x.u % m) ((x.v + m - 1) % m)) m

def summary : String :=
 let t:=certTuple
 let xs := [t.1,t.2.1,t.2.2.1,t.2.2.2]
 toString (xs.map (fun x => (x.u == 0, x.v == 1, diffGcd x N, Nat.gcd x.u N, Nat.gcd ((x.v+N-1)%N) N)))
#eval summary
end E
