import Submission.AntipodalCoreExample

/-! Exact comparison of independent-lift and antipodal restrictions on the
previous period-225 partial family. Neither restriction settles the integer
covering problem. -/
namespace Erdos7IndependentCoreExample
open Erdos7AntipodalCoreExample
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- The six unordered pairs of nonzero first-digit branches modulo five. -/
def branches : Fin 6 → Fin 5 × Fin 5 := ![(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

abbrev Sample := Fin 2 × Fin 3 × Fin 5 × Fin 5

def lift3 (x : Sample) (r : Fin 2) : ℤ :=
  if r = 0 then (![1,7] : Fin 2 → ℤ) x.1 else (![2,5,8] : Fin 3 → ℤ) x.2.1

def lift5 (k : Fin 6) (x : Sample) (r : Fin 2) : ℤ :=
  if r = 0 then (branches k).1.val+5*x.2.2.1.val
  else (branches k).2.val+5*x.2.2.2.val

/-- Higher digits in the four lifts are chosen independently. The only
remaining pure exclusion is the residue two modulo twenty-five. -/
def admissible (k : Fin 6) (x : Sample) : Prop :=
  ∀ r : Fin 2, ¬ (25 : ℤ) ∣ lift5 k x r-2

instance (k : Fin 6) (x : Sample) : Decidable (admissible k x) := by
  unfold admissible
  infer_instance

def covers (k : Fin 6) (x : Sample) : Prop :=
  ∀ r s : Fin 2, ∃ j : Fin 4,
    ((3^exponent3 j : ℕ) : ℤ) ∣ lift3 x r-residues (coreIndex j) ∧
    ((5^exponent5 j : ℕ) : ℤ) ∣ lift5 k x s-residues (coreIndex j)

instance (k : Fin 6) (x : Sample) : Decidable (covers k x) := by
  unfold covers
  infer_instance

/-- All admissible choices really avoid all pure classes, and each selected
pair lies in different nonzero first-digit branches. -/
theorem valid_lifts : ∀ k x, admissible k x →
    (∀ r : Fin 2, ¬ (3 : ℤ) ∣ lift3 x r ∧ ¬ (9 : ℤ) ∣ lift3 x r-4 ∧
      ¬ (5 : ℤ) ∣ lift5 k x r ∧ ¬ (25 : ℤ) ∣ lift5 k x r-2) ∧
    ¬ (3 : ℤ) ∣ lift3 x 0-lift3 x 1 ∧
    ¬ (5 : ℤ) ∣ lift5 k x 0-lift5 k x 1 := by
  decide +kernel

/-- Six possible branch pairs, each followed by its own exact uniform product
law on the surviving lifts. Only the pair (1,4) can support this core. -/
theorem counts : ∀ k : Fin 6,
    (Finset.univ.filter (admissible k)).card =
      (![120,150,150,120,120,150] : Fin 6 → ℕ) k ∧
    (Finset.univ.filter (fun x => admissible k x ∧ covers k x)).card =
      (![0,0,10,0,0,0] : Fin 6 → ℕ) k := by
  decide +kernel

/-- For the fixed pair of branches 1 and -1 at both primes, the independent
higher-digit experiment has core fraction 1/15. -/
theorem fixed_branch_fraction :
    ((Finset.univ.filter (fun x => admissible 2 x ∧ covers 2 x)).card : ℚ) /
      (Finset.univ.filter (admissible 2)).card = 1/15 := by
  rw [(counts 2).1, (counts 2).2]
  decide +kernel

/-- Choosing the six branch pairs uniformly and then independently choosing
their pure-avoiding lifts gives core probability 1/90, rather than the 1/18
of the earlier antipodal experiment. This is a comparison of two explicitly
different sampling laws on a noncovering family. -/
theorem uniform_branch_fraction :
    (∑ k : Fin 6,
      ((Finset.univ.filter (fun x => admissible k x ∧ covers k x)).card : ℚ) /
        (Finset.univ.filter (admissible k)).card)/6 = 1/90 := by
  simp_rw [fun k => (counts k).1, fun k => (counts k).2]
  norm_num [Fin.sum_univ_succ]

#print axioms valid_lifts
#print axioms counts
#print axioms uniform_branch_fraction
end Erdos7IndependentCoreExample
