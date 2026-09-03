import FormalConjecturesUtil

/-!
An arithmetic test case for antipodal core extraction. The moduli are distinct,
odd and divisor-closed, and every class has a private point. A nonunary Boolean
cover nevertheless occurs on a selected pair in each prime coordinate.
The integer 7 is uncovered, so this is NOT an odd covering system.
-/
namespace Erdos7AntipodalCoreExample
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def moduli : Fin 8 → ℕ := ![3, 5, 9, 15, 25, 45, 75, 225]
def residues : Fin 8 → ℤ := ![0, 0, 4, 1, 2, 26, 49, 224]
def privatePoint : Fin 8 → ℤ := ![3, 5, 4, 1, 2, 26, 124, 224]

def coreIndex : Fin 4 → Fin 8 := ![3, 5, 6, 7]
def exponent3 : Fin 4 → ℕ := ![1, 2, 1, 2]
def exponent5 : Fin 4 → ℕ := ![1, 1, 2, 2]
def opposite (u : ℤ) (r : Fin 2) : ℤ := if r = 0 then u else -u

def selected (u : Fin 9) (v : Fin 25) (signs : Fin 2 → Fin 2) (j : Fin 4) : Prop :=
  ((3^exponent3 j : ℕ) : ℤ) ∣ opposite u.val (signs 0)-residues (coreIndex j) ∧
    ((5^exponent5 j : ℕ) : ℤ) ∣ opposite v.val (signs 1)-residues (coreIndex j)

instance (u : Fin 9) (v : Fin 25) (signs : Fin 2 → Fin 2) (j : Fin 4) :
    Decidable (selected u v signs j) := by unfold selected; infer_instance

def good3 (u : Fin 9) : Prop :=
  ∀ r : Fin 2, ¬ (3 : ℤ) ∣ opposite u.val r ∧ ¬ (9 : ℤ) ∣ opposite u.val r-4

def good5 (v : Fin 25) : Prop :=
  ∀ r : Fin 2, ¬ (5 : ℤ) ∣ opposite v.val r ∧ ¬ (25 : ℤ) ∣ opposite v.val r-2

instance (u : Fin 9) : Decidable (good3 u) := by unfold good3; infer_instance
instance (v : Fin 25) : Decidable (good5 v) := by unfold good5; infer_instance

def coversPair (u : Fin 9) (v : Fin 25) : Prop :=
  ∀ signs : Fin 2 → Fin 2, ∃ j : Fin 4, selected u v signs j

instance (u : Fin 9) (v : Fin 25) : Decidable (coversPair u v) := by
  unfold coversPair
  infer_instance

/-- Genuine distinct, nontrivial, odd integer moduli. -/
theorem distinct_odd : Function.Injective moduli ∧ ∀ j, 1 < moduli j ∧ Odd (moduli j) := by
  decide +kernel

/-- Every nontrivial divisor of a listed modulus is listed. -/
theorem divisor_closed :
    ∀ j, ∀ d ∈ (moduli j).divisors, 1 < d → ∃ k, moduli k = d := by
  decide +kernel

/-- Every congruence class has a point not in any other listed class. -/
theorem private_points :
    ∀ j k, ((moduli k : ℤ) ∣ privatePoint j-residues k) ↔ k = j := by
  decide +kernel

/-- The necessary disjointness of comparable distinct classes also holds. -/
theorem comparable_disjoint :
    ∀ j k, j ≠ k → moduli j ∣ moduli k →
      ¬ (moduli j : ℤ) ∣ residues k-residues j := by
  decide +kernel

/-- The four selected classes have distinct exponent patterns but all have
exactly the same two-prime support. -/
theorem core_moduli :
    Function.Injective coreIndex ∧ ∀ j,
      moduli (coreIndex j) = 3^exponent3 j*5^exponent5 j ∧
      0 < exponent3 j ∧ 0 < exponent5 j := by
  decide +kernel

/-- The pair ±1 avoids every pure class. The four mixed classes partition
its Boolean sign cube, so this is a genuine nonunary Boolean covering core. -/
theorem selected_pair_core : good3 1 ∧ good5 1 ∧
    ∀ signs : Fin 2 → Fin 2, ∃! j : Fin 4, selected 1 1 signs j := by
  unfold ExistsUnique
  decide +kernel

/-- Exact accounting of ALL pure-avoiding opposite-pair choices. -/
theorem pair_counts :
    (Finset.univ.filter good3).card = 4 ∧
    (Finset.univ.filter good5).card = 18 ∧
    (Finset.univ.filter (fun uv : Fin 9 × Fin 25 =>
      good3 uv.1 ∧ good5 uv.2 ∧ coversPair uv.1 uv.2)).card = 4 := by
  decide +kernel

/-- Among the 72 ordered choices, exactly four produce a Boolean cover.
Counting opposite orientations twice in each coordinate cancels in the ratio. -/
theorem core_fraction :
    ((Finset.univ.filter (fun uv : Fin 9 × Fin 25 =>
      good3 uv.1 ∧ good5 uv.2 ∧ coversPair uv.1 uv.2)).card : ℚ) /
      ((Finset.univ.filter good3).card*(Finset.univ.filter good5).card) = 1/18 := by
  rw [pair_counts.1, pair_counts.2.1, pair_counts.2.2]
  norm_num

theorem seven_uncovered : ∀ j, ¬ (moduli j : ℤ) ∣ 7-residues j := by
  decide +kernel

/-- The example is not a covering system of integers. -/
theorem not_integer_cover :
    ¬ (∀ x : ℤ, ∃ j, (moduli j : ℤ) ∣ x-residues j) := by
  intro h
  obtain ⟨j, hj⟩ := h 7
  exact seven_uncovered j hj

#print axioms selected_pair_core
#print axioms pair_counts
#print axioms core_fraction
#print axioms not_integer_cover
end Erdos7AntipodalCoreExample
