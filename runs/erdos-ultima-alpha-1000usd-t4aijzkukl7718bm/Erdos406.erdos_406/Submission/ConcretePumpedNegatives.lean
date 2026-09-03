import Submission.PumpedNegativeFamilies

/-! Concrete local certificates for learned regular negative families.
No invariant or proof of Erdős406 is asserted. -/
namespace Erdos406ConcretePumpedNegative
open Erdos406PumpedNegative

def pump0 : Data where
  j := 1
  L := 4
  R := 8
  b := 2431
  m := 4
  v := [0, 2, 0, 2]
  w := [1, 0, 0, 0, 2, 0, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump0

def pump1 : Data where
  j := 1
  L := 4
  R := 8
  b := 3007
  m := 4
  v := [0, 2, 0, 2]
  w := [1, 0, 0, 2, 1, 1, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump1

def pump2 : Data where
  j := 1
  L := 4
  R := 10
  b := 9559
  m := 4
  v := [0, 2, 0, 2]
  w := [0, 2, 1, 2, 1, 1, 2, 0, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump2

def pump3 : Data where
  j := 2
  L := 16
  R := 10
  b := 9559
  m := 4
  v := [0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2]
  w := [0, 0, 1, 2, 2, 1, 2, 2, 1, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump3

def pump4 : Data where
  j := 3
  L := 64
  R := 10
  b := 9559
  m := 4
  v := [0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2]
  w := [0, 0, 0, 1, 1, 1, 0, 2, 0, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump4

def pump5 : Data where
  j := 1
  L := 4
  R := 8
  b := 31
  m := 4
  v := [0, 2, 0, 2]
  w := [0, 2, 0, 2, 1, 0, 0, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump5

def pump6 : Data where
  j := 2
  L := 16
  R := 8
  b := 31
  m := 4
  v := [0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2]
  w := [0, 0, 1, 2, 0, 0, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump6

def pump7 : Data where
  j := 1
  L := 4
  R := 9
  b := 2461
  m := 4
  v := [0, 2, 0, 2]
  w := [0, 2, 1, 1, 2, 1, 0, 0, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump7

def pump8 : Data where
  j := 2
  L := 16
  R := 9
  b := 2461
  m := 4
  v := [0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2]
  w := [0, 0, 1, 2, 2, 0, 0, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump8

def pump9 : Data where
  j := 1
  L := 4
  R := 10
  b := 19927
  m := 4
  v := [0, 2, 0, 2]
  w := [1, 0, 0, 0, 0, 0, 2, 0, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump9

def pump10 : Data where
  j := 2
  L := 16
  R := 10
  b := 19927
  m := 4
  v := [0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2]
  w := [0, 0, 2, 0, 2, 0, 2, 2, 1, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump10

def pump11 : Data where
  j := 1
  L := 4
  R := 7
  b := 757
  m := 4
  v := [0, 2, 0, 2]
  w := [1, 0, 0, 0, 0, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump11

def pump12 : Data where
  j := 2
  L := 16
  R := 7
  b := 757
  m := 4
  v := [0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2]
  w := [0, 0, 2, 0, 2, 1, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump12

def pump13 : Data where
  j := 1
  L := 4
  R := 7
  b := 85
  m := 4
  v := [0, 2, 0, 2]
  w := [0, 2, 1, 0, 0, 0, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump13

def pump14 : Data where
  j := 1
  L := 4
  R := 8
  b := 271
  m := 4
  v := [0, 2, 0, 2]
  w := [0, 2, 1, 0, 0, 0, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump14

def pump15 : Data where
  j := 1
  L := 4
  R := 9
  b := 2269
  m := 4
  v := [0, 2, 0, 2]
  w := [0, 2, 1, 1, 1, 2, 0, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump15

def pump16 : Data where
  j := 1
  L := 4
  R := 14
  b := 787591
  m := 4
  v := [0, 2, 0, 2]
  w := [0, 2, 1, 2, 1, 2, 0, 2, 1, 0, 0, 0, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump16

def pump17 : Data where
  j := 2
  L := 16
  R := 14
  b := 787591
  m := 4
  v := [0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2]
  w := [0, 0, 1, 2, 2, 2, 0, 0, 1, 2, 0, 2, 1, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump17

def pump18 : Data where
  j := 3
  L := 64
  R := 14
  b := 787591
  m := 4
  v := [0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2]
  w := [0, 0, 0, 1, 1, 1, 0, 2, 1, 0, 1, 2, 0, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump18

def pump19 : Data where
  j := 1
  L := 4
  R := 10
  b := 20503
  m := 4
  v := [0, 2, 0, 2]
  w := [1, 0, 0, 0, 0, 2, 1, 1, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump19

def pump20 : Data where
  j := 2
  L := 16
  R := 10
  b := 20503
  m := 4
  v := [0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2]
  w := [0, 0, 2, 0, 2, 1, 1, 0, 1, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump20

def pump21 : Data where
  j := 1
  L := 4
  R := 9
  b := 253
  m := 4
  v := [0, 2, 0, 2]
  w := [0, 2, 0, 2, 1, 1, 1, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump21

def pump22 : Data where
  j := 1
  L := 4
  R := 9
  b := 3037
  m := 4
  v := [0, 2, 0, 2]
  w := [0, 2, 1, 2, 1, 0, 1, 0, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump22

def pump23 : Data where
  j := 2
  L := 16
  R := 9
  b := 3037
  m := 4
  v := [0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2]
  w := [0, 0, 1, 2, 2, 1, 1, 2, 1]
  residues := {4}
  hR := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hb := by decide +kernel
  good_b := by decide +kernel
  period := by decide +kernel
  seed_guard := by decide +kernel
  guard_closed := by decide +kernel

#print axioms pump23

def allPumps : List Data := [pump0, pump1, pump2, pump3, pump4, pump5, pump6, pump7, pump8, pump9, pump10, pump11, pump12, pump13, pump14, pump15, pump16, pump17, pump18, pump19, pump20, pump21, pump22, pump23]

theorem all_long_enough : ∀ D ∈ allPumps, 7 ≤ D.R + 1 := by decide +kernel

#print axioms allPumps
#print axioms all_long_enough
end Erdos406ConcretePumpedNegative
