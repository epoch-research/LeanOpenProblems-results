import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 20000000

def powMod (a e m : Nat) : Nat :=
  match e with
  | 0 => 1 % m
  | e+1 =>
      let r := powMod ((a*a)%m) ((e+1)/2) m
      if (e+1) % 2 = 0 then r else (r*a)%m
termination_by e

def NN : Nat := 550172
def DD : Nat := 29400
def GG : Nat := 196
def QQ : Nat := 2807
def INV : Nat := 131

def baseList : List Nat := [36,143,2,349,308,3,26,225,332,191,50,81,4,31,58,85,48,139,98,193,220,15,122,237,328,287,146,5,204,311,170,29,60,171,10,37,64,27,118,77,172,199,226,101,216,307,266,125,72,183,290,149,8,39,150,173,16,43,6,97,56,151,178,205,80,195,286,245,104,51,162,269,128,475,18,129,152,11,22,49,76,35,130,157,184,59,174,265,224,83,30,141,248,107,454,413,108,131,330,437,28,55,14,109,136,163,38,153,244,203,62,9,120,227,86,433,392,87,110,309,416,7,34,61,88,115,142,17,132,223,182,41,304,99,206,65,412,371,66,89,288,395,254,13,40,67,94,121,148,111,202,161,20,283,78,185,44,391,350,45,68,267,374,233,12,19,46,73,100,127,90,181,140,235,262,57,164,23,370,329,24,47,246,353,212,71,102,25,52,79,106,69,160,119,214,241]

def base (c : Nat) : Nat := baseList.getD c 0

def residueAt (k : Nat) : Nat := ((powMod 2 k NN + NN - (k % NN)) % NN)

def residueSmall (a k : Nat) : Nat := ((powMod 2 a NN + NN - (k % NN)) % NN)

def wit (r : Nat) : Nat :=
  let a := base (r % GG)
  let b := residueSmall a a
  let q := ((b + NN - (r % NN)) % NN) / GG
  let t := (q * INV) % QQ
  a + t * DD

def goodWitFull (r : Nat) : Bool :=
  let k := wit r
  (1 <= k) && (k <= 82496875) && (residueAt k == r)

def checkWitsFull : Nat → Nat → Bool
  | r, 0 => true
  | r, fuel+1 => goodWitFull r && checkWitsFull (r+1) fuel

#eval goodWitFull 13573
#eval checkWitsFull 0 1000

theorem checkWitsFull_true : checkWitsFull 0 550172 = true := by native_decide
#print axioms checkWitsFull_true
