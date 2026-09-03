import FormalConjecturesUtil

/-! Nonuniform core-cell budget certificates for a restricted one-event model.
These are conditional budget obstructions, NOT a disproof of the odd-cover
conjecture. An arbitrary congruence class need not satisfy the one-event bound. -/
namespace Erdos7SelectiveCellBudget
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
open Finset

def singleWeight (x : Fin 9) : ℚ :=
  if x.val = 2 ∨ x.val = 4 ∨ x.val = 7 ∨ x.val = 8 then 1/70 else 0

def tripleWeight (i : Fin 3) (x : Fin 9) : ℚ :=
  if (i.val = 0 ∧ x.val = 5) ∨ (i.val = 1 ∧ (x.val = 2 ∨ x.val = 7)) ∨
    (i.val = 2 ∧ (x.val = 4 ∨ x.val = 8)) then 1/49 else 0

def singleCoeff : Fin 3 → ℚ := ![4/70, 2/70, 1/70]
def sharedCoeff : Fin 3 → ℚ := ![5/49, 3/49, 1/49]
def separateCoeff : Fin 3 → ℚ := ![2/49, 1/49, 1/49]

lemma weights_nonnegative :
    (∀ x, 0 ≤ singleWeight x) ∧ (∀ i x, 0 ≤ tripleWeight i x) := by
  decide +kernel

lemma normalized_demand :
    5 * (∑ x, singleWeight x) + 7 * (∑ i, ∑ x, tripleWeight i x) = 1 := by
  decide +kernel

lemma single_prefix_bound : ∀ (a : Fin 3) (r : Fin 9),
    (∑ x : Fin 9, if x.val % 3^a.val = r.val then singleWeight x else 0) ≤
      singleCoeff a := by
  decide +kernel

lemma shared_prefix_bound : ∀ (a : Fin 3) (r : Fin 9),
    (∑ i : Fin 3, ∑ x : Fin 9,
      if x.val % 3^a.val = r.val then tripleWeight i x else 0) ≤ sharedCoeff a := by
  decide +kernel

lemma separate_prefix_bound : ∀ (i a : Fin 3) (r : Fin 9),
    (∑ x : Fin 9, if x.val % 3^a.val = r.val then tripleWeight i x else 0) ≤
      separateCoeff a := by
  decide +kernel

/-- Weighted capacity of the cofactor 5^a * 7^b before multiplying by its
5,7-free tail factor. This expression uses the one-event maximum, not a sum
of contributions from independently reused events. -/
def coreTerm (a b : ℕ) : ℚ :=
  let u := (5:ℚ)^(min a 2)
  let v := (5:ℚ)^(min a 1) * 7^(min b 1)
  (∑ k : Fin 3, max (singleCoeff k * u)
    ((if a = 0 then sharedCoeff k else separateCoeff k) * v)) / (5^a * 7^b)

def coreSum : ℚ := ∑ a : Fin 7, ∑ b : Fin 3, coreTerm a.val b.val

def removedRoot : ℚ := coreTerm 0 0 + coreTerm 1 0

def budget (β : ℚ) : ℚ := β * coreSum - removedRoot

lemma coreSum_value : coreSum = 1589117/2143750 := by
  decide +kernel

lemma removedRoot_value : removedRoot = 71/245 := by
  decide +kernel

lemma budget_formula (β : ℚ) : budget β = β * (1589117/2143750) - 71/245 := by
  simp only [budget, coreSum_value, removedRoot_value]

lemma budget_below_one (β : ℚ) (hβ : β < 2765000/1589117) : budget β < 1 := by
  rw [budget_formula]
  linarith

def tailPrimes : Fin 17 → ℚ :=
  ![11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73]

def beta73 : ℚ := 1 + (∑ i, 1 / tailPrimes i) +
  ((∑ i, 1 / tailPrimes i)^2 - (∑ i, (1 / tailPrimes i)^2)) / 2

/-- The quadratic expression is exactly the reciprocal sum of tail products
with at most two distinct primes, including the empty product. -/
lemma beta73_pair_sum : beta73 = 1 + (∑ i, 1 / tailPrimes i) +
    (∑ i : Fin 17, ∑ j : Fin 17,
      if i.val < j.val then 1 / (tailPrimes i * tailPrimes j) else 0) := by
  decide +kernel

lemma beta73_value : beta73 =
    336428496927782564917846232 / 193950859996423924526768207 := by
  decide +kernel

lemma budget73_value : budget beta73 =
    4405662467868177479811684064451 / 4423214426780146683024035571875 := by
  rw [budget_formula, beta73_value]
  norm_num

lemma budget73_lt_one : budget beta73 < 1 := by
  rw [budget73_value]
  norm_num

/-- General finite accounting lemma. Its per-resource cap hypothesis is an
essential extra restriction and is not asserted for arbitrary odd covers. -/
theorem finite_budget_obstruction {I R : Type*} [Fintype I] [Fintype R]
    (demand : I → ℚ) (flow : R → I → ℚ) (cap : R → ℚ)
    (hc : ∀ i, demand i ≤ ∑ r, flow r i)
    (hb : ∀ r, (∑ i, flow r i) ≤ cap r)
    (hgap : (∑ r, cap r) < ∑ i, demand i) : False := by
  have h : (∑ i, demand i) ≤ ∑ r, cap r := calc
    (∑ i, demand i) ≤ ∑ i, ∑ r, flow r i := sum_le_sum (fun i _ => hc i)
    _ = ∑ r, ∑ i, flow r i := sum_comm
    _ ≤ ∑ r, cap r := sum_le_sum (fun r _ => hb r)
  exact (not_lt_of_ge h) hgap

theorem no_normalized_allocation {I R : Type*} [Fintype I] [Fintype R]
    (demand : I → ℚ) (flow : R → I → ℚ) (cap : R → ℚ)
    (hn : (∑ i, demand i) = 1)
    (hc : ∀ i, demand i ≤ ∑ r, flow r i)
    (hb : ∀ r, (∑ i, flow r i) ≤ cap r)
    (ht : (∑ r, cap r) ≤ budget beta73) : False := by
  apply finite_budget_obstruction demand flow cap hc hb
  rw [hn]
  exact lt_of_le_of_lt ht budget73_lt_one

/-- Negative control for extending the one-event bound to arbitrary classes:
modulo6, the class0 modulo2 hits all three fibres modulo3. -/
def evenPoints : Finset (Fin 6) := univ.filter (fun x => x.val % 2 = 0)

lemma evenPoints_card : evenPoints.card = 3 := by decide +kernel

lemma evenPoints_per_fibre : ∀ r : Fin 3,
    (evenPoints.filter (fun x => x.val % 3 = r.val)).card = 1 := by
  decide +kernel

lemma one_fibre_bound_not_global :
    ¬ evenPoints.card ≤ (evenPoints.filter (fun x => x.val % 3 = 0)).card := by
  decide +kernel

#print axioms normalized_demand
#print axioms single_prefix_bound
#print axioms shared_prefix_bound
#print axioms separate_prefix_bound
#print axioms coreSum_value
#print axioms beta73_pair_sum
#print axioms beta73_value
#print axioms budget73_lt_one
#print axioms no_normalized_allocation
#print axioms one_fibre_bound_not_global
end Erdos7SelectiveCellBudget
