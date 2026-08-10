import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
set_option linter.unusedVariables false
namespace GS

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

def stepState (s : State) : State :=
  { base := emul N s.base s.base,
    a1 := stepAcc N s.base s.a1 s.e1,
    a2 := stepAcc N s.base s.a2 s.e2,
    a3 := stepAcc N s.base s.a3 s.e3,
    a4 := stepAcc N s.base s.a4 s.e4,
    e1 := s.e1/2, e2 := s.e2/2, e3 := s.e3/2, e4 := s.e4/2 }

def adv : Nat -> State -> State
| 0, s => s
| n+1, s => adv n (stepState s)

def init : State := { base := gamma N, a1 := one N, a2 := one N, a3 := one N, a4 := one N, e1 := N+1, e2 := (N+1)/2, e3 := (N+1)/3, e4 := (N+1)/100943 }

def statesAux : Nat -> State -> List State
| 0, s => [s]
| n+1, s => s :: statesAux n (adv 5000 s)

def states := statesAux 14 init

def fmtE (x : Elt) : String := "{ u := " ++ toString x.u ++ ", v := " ++ toString x.v ++ " }"
def fmtS (s : State) : String :=
  "{ base := " ++ fmtE s.base ++ ", a1 := " ++ fmtE s.a1 ++ ", a2 := " ++ fmtE s.a2 ++ ", a3 := " ++ fmtE s.a3 ++ ", a4 := " ++ fmtE s.a4 ++ ", e1 := " ++ toString s.e1 ++ ", e2 := " ++ toString s.e2 ++ ", e3 := " ++ toString s.e3 ++ ", e4 := " ++ toString s.e4 ++ " }"

def defsAux : Nat -> List State -> List String
| _, [] => []
| i, s :: ss => ("def runState" ++ toString i ++ " : RunState := " ++ fmtS s) :: defsAux (i+1) ss

def defs : String := String.intercalate "\n" (defsAux 0 states)

def lastState : List State -> State
| [] => init
| [s] => s
| _ :: ss => lastState ss

def finalState : State := lastState states

def coords : String :=
  toString ((finalState.a2.v + N - 1) % N) ++ "\n" ++ toString finalState.a3.u ++ "\n" ++ toString finalState.a4.u

#eval IO.FS.writeFile "/tmp/states_part.lean" defs
#eval IO.FS.writeFile "/tmp/coords_part.txt" coords

end GS
