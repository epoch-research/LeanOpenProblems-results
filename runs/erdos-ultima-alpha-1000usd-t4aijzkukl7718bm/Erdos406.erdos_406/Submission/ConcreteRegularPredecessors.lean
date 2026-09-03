import Submission.RegularPredecessorFamilies

/-! The five infinite regular negative languages used in the two current
searches, with their arithmetic and guard obligations checked in Lean.
These are necessary rejections, not a witness for the original conjecture. -/
namespace Erdos406ConcreteRegularPredecessor
open Erdos406RegularPredecessor

structure Family where
  j : ℕ
  C : ℕ
  L : ℕ
  m : ℕ
  r : ℕ
  residues : Finset ℕ
  u : List ℕ
  v : List ℕ
  w : List ℕ
  hL : 0 < L
  coprime : Nat.Coprime 3 m
  hv : v.length = L
  hw : w.length = L
  hprefix : 4 ^ j * wordValue u + C = 243
  hloop : 4 ^ j * wordValue v + C = C * 3 ^ L
  htail : 4 ^ j * wordValue w = C * 3 ^ L + 13
  hbase : 4 ^ j * r = 256
  hperiod : Nat.ModEq (4 ^ j * m) (3 ^ L) 1
  root_mem : r % (3 * m) ∈ residues
  closed : ∀ a ∈ residues, (4 * a) % (3 * m) ∈ residues

namespace Family
variable (F : Family)

def input (t : ℕ) : ℕ := wordValue (F.u ++ tailWord F.v F.w t)

lemma good (t : ℕ) : Nat.digits 3 (4 ^ F.j * F.input t) ⊆ [0, 1] :=
  scaled_word_good _ _ _ _ _ _ F.hv F.hw F.hprefix F.hloop F.htail t

lemma length (t : ℕ) :
    (Nat.digits 3 (4 ^ F.j * F.input t)).length = F.L * (t + 1) + 6 :=
  scaled_word_length _ _ _ _ _ _ F.hv F.hw F.hprefix F.hloop F.htail t

lemma residue (t : ℕ) : Nat.ModEq F.m (F.input t) F.r :=
  scaled_word_residue _ _ _ _ _ (by positivity) _ _ _ F.hv F.hw
    F.hprefix F.hloop F.htail F.hbase F.hperiod t

lemma mod_three (t : ℕ) : F.input t % 3 = 1 := by
  exact scaled_word_mod_three _ _ _ _ _ _ F.hv F.hw F.hprefix F.hloop F.htail
    (by simp [Nat.pow_mod]) t

lemma root_mod_three : F.r % 3 = 1 := by
  have hh := congrArg (fun n : ℕ => n % 3) F.hbase
  simpa [Nat.mul_mod, Nat.pow_mod] using hh

lemma full_residue (t : ℕ) : Nat.ModEq (3 * F.m) (F.input t) F.r := by
  apply (Nat.modEq_and_modEq_iff_modEq_mul F.coprime).mp
  refine ⟨?_, F.residue t⟩
  change F.input t % 3 = F.r % 3
  rw [F.mod_three, F.root_mod_three]

lemma guard (t : ℕ) : F.input t % (3 * F.m) ∈ F.residues := by
  have hh := F.full_residue t
  change F.input t % (3 * F.m) = F.r % (3 * F.m) at hh
  rw [hh]
  exact F.root_mem

lemma guard_mul (n : ℕ) (hn : n % (3 * F.m) ∈ F.residues) :
    (4 * n) % (3 * F.m) ∈ F.residues := by
  have hh := F.closed _ hn
  simpa [Nat.mul_mod] using hh

/-- Every member of the concrete regular family must be rejected. The
seven-digit cutoff is the explicit bound of the current search template. -/
theorem rejected (P : ℕ → Prop)
    (hP : ∀ n, n % (3 * F.m) ∈ F.residues → P n → P (4 * n))
    (hbound : ∀ n, P n → Nat.digits 3 n ⊆ [0, 1] → (Nat.digits 3 n).length < 7)
    (t : ℕ) : ¬ P (F.input t) := by
  apply family_rejected F.j F.C F.L 7 F.u F.v F.w F.hv F.hw
    F.hprefix F.hloop F.htail P (fun n => n % (3 * F.m) ∈ F.residues)
    F.guard_mul hP hbound t (F.guard t)
  have hh := F.hL
  nlinarith
end Family

def familyQ1J1 : Family where
  j := 1
  C := 3
  L := 4
  m := 4
  r := 64
  residues := {4}
  u := [2, 0, 2, 0]
  v := [2, 0, 2, 0]
  w := [2, 1, 0, 1]
  hL := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hprefix := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hbase := by decide +kernel
  hperiod := by decide +kernel
  root_mem := by decide +kernel
  closed := by decide +kernel

#print axioms familyQ1J1

def familyQ1J2 : Family where
  j := 2
  C := 3
  L := 16
  m := 4
  r := 16
  residues := {4}
  u := [1, 2, 0]
  v := [0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0]
  w := [0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 1]
  hL := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hprefix := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hbase := by decide +kernel
  hperiod := by decide +kernel
  root_mem := by decide +kernel
  closed := by decide +kernel

#print axioms familyQ1J2

def familyQ1J3 : Family where
  j := 3
  C := 51
  L := 64
  m := 4
  r := 4
  residues := {4}
  u := [1, 0]
  v := [2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0]
  w := [2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 0, 1, 1]
  hL := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hprefix := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hbase := by decide +kernel
  hperiod := by decide +kernel
  root_mem := by decide +kernel
  closed := by decide +kernel

#print axioms familyQ1J3

def familyQ19J1 : Family where
  j := 1
  C := 3
  L := 36
  m := 76
  r := 64
  residues := {4, 16, 28, 64, 100, 112, 172, 196, 220}
  u := [2, 0, 2, 0]
  v := [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0]
  w := [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 1, 0, 1]
  hL := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hprefix := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hbase := by decide +kernel
  hperiod := by decide +kernel
  root_mem := by decide +kernel
  closed := by decide +kernel

#print axioms familyQ19J1

def familyQ19J2 : Family where
  j := 2
  C := 3
  L := 144
  m := 76
  r := 16
  residues := {4, 16, 28, 64, 100, 112, 172, 196, 220}
  u := [1, 2, 0]
  v := [0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0]
  w := [0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2, 1]
  hL := by decide +kernel
  coprime := by decide +kernel
  hv := by decide +kernel
  hw := by decide +kernel
  hprefix := by decide +kernel
  hloop := by decide +kernel
  htail := by decide +kernel
  hbase := by decide +kernel
  hperiod := by decide +kernel
  root_mem := by decide +kernel
  closed := by decide +kernel

#print axioms familyQ19J2

#print axioms Family.rejected
end Erdos406ConcreteRegularPredecessor
