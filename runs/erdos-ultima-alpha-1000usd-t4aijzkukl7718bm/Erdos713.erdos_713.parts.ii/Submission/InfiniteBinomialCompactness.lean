import FormalConjecturesUtil
import Submission.BinomialRelaxationEquivalence

/-! A fixed infinite family of coefficient-height-one binomial inequalities
can be exactly sharp at an irrational power, although no finite subfamily is
constant-factor sharp uniformly in the order. This is not a graph example. -/

open Filter Asymptotics
open scoped Topology
namespace Erdos713InfiniteBinomialCompactness
open Erdos713PolynomialInequality Erdos713BinomialRelaxation

set_option maxHeartbeats 1000000

/-- The index set is fixed once `α` is fixed; it does not depend on `n`. -/
def UpperPair (α : ℝ) (r : ℕ × ℕ) : Prop :=
  0 < r.2 ∧ α * r.2 < r.1

noncomputable def floorPower (α : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ α⌋₊

lemma power_le_binomial {α x y : ℝ} {p q : ℕ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) (hya : y ≤ x ^ α) (hpq : α * q ≤ p) :
    y ^ q ≤ x ^ p := by
  calc
    y ^ q ≤ (x ^ α) ^ q := pow_le_pow_left₀ hy hya q
    _ = x ^ (α * q) := (Real.rpow_mul_natCast (by linarith : 0 ≤ x) α q).symm
    _ ≤ x ^ (p : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hpq
    _ = x ^ p := Real.rpow_natCast x p

/-- A strict upper gap at a fixed positive base contains a rational power. -/
lemma exists_upper_pair_below {α x y : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hy : x ^ α < y) :
    ∃ p q : ℕ, UpperPair α (p, q) ∧ x ^ ((p : ℝ) / q) < y := by
  have hevent : ∀ᶠ β : ℝ in 𝓝 α, x ^ β < y :=
    (Real.continuousAt_const_rpow hx.ne').tendsto.eventually_lt_const hy
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  obtain ⟨r, har, hr⟩ := exists_rat_btwn (show α < α + ε by linarith)
  have hrpos : (0 : ℝ) < r := hα.trans har
  obtain ⟨p, q, hq, hpq⟩ := nat_fraction_of_positive_rational hrpos ⟨r, rfl⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrval : (r : ℝ) = (p : ℝ) / q := (eq_div_iff hqR.ne').mpr hpq
  refine ⟨p, q, ⟨hq, ?_⟩, ?_⟩
  · change α * (q : ℝ) < p
    rw [← hpq]
    exact mul_lt_mul_of_pos_right har hqR
  · rw [← hrval]
    apply hball
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr har)]
    linarith

/-- All of the fixed binomial inequalities give exactly the real power bound. -/
theorem all_binomials_iff {α x y : ℝ} (hα : 0 < α) (hx : 1 ≤ x)
    (hy : 0 ≤ y) :
    (∀ r : ℕ × ℕ, UpperPair α r → y ^ r.2 ≤ x ^ r.1) ↔ y ≤ x ^ α := by
  constructor
  · intro h
    by_contra hn
    have hxy : x ^ α < y := lt_of_not_ge hn
    obtain ⟨p, q, hpq, hpow⟩ := exists_upper_pair_below hα (by linarith) hxy
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hpq.1.ne'
    have he : (x ^ ((p : ℝ) / q)) ^ q = x ^ p := by
      rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ x), div_mul_cancel₀ _ hqR,
        Real.rpow_natCast]
    have hle : y ^ q ≤ (x ^ ((p : ℝ) / q)) ^ q := by
      rw [he]
      exact h (p, q) hpq
    have hy' := (pow_le_pow_iff_left₀ hy (by positivity) hpq.1.ne').mp hle
    exact (not_lt_of_ge hy') hpow
  · intro h r hr
    exact power_le_binomial hx hy h hr.2.le

/-- Over natural objectives the entire fixed family is sharp with factor one. -/
theorem all_nat_binomials_iff {α : ℝ} (hα : 0 < α) {n m : ℕ} (hn : 1 ≤ n) :
    (∀ r : ℕ × ℕ, UpperPair α r → m ^ r.2 ≤ n ^ r.1) ↔ m ≤ floorPower α n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [floorPower, Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ α)]
  rw [← all_binomials_iff hα hnR (Nat.cast_nonneg m)]
  constructor <;> intro h r hr
  · exact_mod_cast h r hr
  · exact_mod_cast h r hr

/-- At every fixed order a single member of the fixed family is already exact.
Its index need not be bounded independently of the order. -/
theorem one_exact_at_each_order {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r : ℕ × ℕ, UpperPair α r ∧
      ∀ m : ℕ, m ^ r.2 ≤ n ^ r.1 ↔ m ≤ floorPower α n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfloor : (n : ℝ) ^ α < (floorPower α n : ℝ) + 1 := by
    exact Nat.lt_floor_add_one ((n : ℝ) ^ α)
  obtain ⟨p, q, hpq, hsmall⟩ := exists_upper_pair_below hα (by linarith) hfloor
  refine ⟨(p, q), hpq, fun m => ⟨?_, ?_⟩⟩
  · intro hm
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hpq.1.ne'
    have hmr : (m : ℝ) ^ q ≤ (n : ℝ) ^ p := by exact_mod_cast hm
    have he : ((n : ℝ) ^ ((p : ℝ) / q)) ^ q = (n : ℝ) ^ p := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n), div_mul_cancel₀ _ hqR,
        Real.rpow_natCast]
    rw [← he] at hmr
    have hmle := (pow_le_pow_iff_left₀ (Nat.cast_nonneg m) (by positivity) hpq.1.ne').mp hmr
    have hlt : (m : ℝ) < (floorPower α n : ℝ) + 1 := hmle.trans_lt hsmall
    have hmnat : m < floorPower α n + 1 := by exact_mod_cast hlt
    omega
  · intro hm
    exact (all_nat_binomials_iff hα hn).mpr hm (p, q) hpq

lemma finite_upper_pairs_have_gap {α : ℝ} (S : Finset (ℕ × ℕ))
    (hS : ∀ r ∈ S, UpperPair α r) :
    ∃ β : ℝ, α < β ∧ ∀ r ∈ S, UpperPair β r := by
  have hevent : ∀ᶠ β : ℝ in 𝓝 α, ∀ r ∈ S, β * r.2 < r.1 := by
    rw [Filter.eventually_all_finset]
    intro r hr
    have hcont : Continuous (fun β : ℝ => β * r.2) := by fun_prop
    exact hcont.continuousAt.tendsto.eventually_lt_const (hS r hr).2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨α + ε / 2, by linarith, ?_⟩
  intro r hr
  refine ⟨(hS r hr).1, hball ?_ r hr⟩
  rw [Real.dist_eq]
  have he : α + ε / 2 - α = ε / 2 := by ring
  rw [he, abs_of_pos (by positivity : 0 < ε / 2)]
  linarith

/-- No finite subfamily is sharp within any fixed constant at large orders. -/
theorem finite_subfamily_not_sharp {α : ℝ} (hα : 0 < α)
    (S : Finset (ℕ × ℕ)) (hS : ∀ r ∈ S, UpperPair α r) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ,
      (∀ r ∈ S, m ^ r.2 ≤ n ^ r.1) ∧ K * floorPower α n < (m : ℝ) := by
  obtain ⟨β, hab, hβS⟩ := finite_upper_pairs_have_gap S hS
  have hβ : 0 < β := hα.trans hab
  have hgt := eventually_floor_rpow_gt (floor_rpow_asymptotic hα) hab hβ K
  filter_upwards [hgt, eventually_ge_atTop (1 : ℕ)] with n hn hnp
  refine ⟨floorPower β n, ?_, hn⟩
  intro r hr
  exact (all_nat_binomials_iff hβ hnp).mpr le_rfl r (hβS r hr)

/-- An explicit irrational exponent with an infinite fixed exact relaxation,
pointwise one-constraint certificates, and failure of every finite subfamily. -/
theorem irrational_example :
    ∃ α : ℝ, 1 < α ∧ α < 2 ∧ Irrational α ∧
      ((fun n : ℕ => (floorPower α n : ℝ)) ~[atTop]
        (fun n : ℕ => (1 : ℝ) * (n : ℝ) ^ α)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ m : ℕ,
        (∀ r : ℕ × ℕ, UpperPair α r → m ^ r.2 ≤ n ^ r.1) ↔ m ≤ floorPower α n) ∧
      (∀ n : ℕ, 1 ≤ n → ∃ r : ℕ × ℕ, UpperPair α r ∧
        ∀ m : ℕ, m ^ r.2 ≤ n ^ r.1 ↔ m ≤ floorPower α n) ∧
      (∀ S : Finset (ℕ × ℕ), (∀ r ∈ S, UpperPair α r) → ∀ K : ℝ,
        ∀ᶠ n : ℕ in atTop, ∃ m : ℕ,
          (∀ r ∈ S, m ^ r.2 ≤ n ^ r.1) ∧ K * floorPower α n < (m : ℝ)) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hlo : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hhi : Real.sqrt 2 < (2 : ℝ) := by nlinarith
  have hpos : (0 : ℝ) < Real.sqrt 2 := by positivity
  exact ⟨Real.sqrt 2, hlo, hhi, irrational_sqrt_two, floor_rpow_asymptotic hpos,
    fun _ hn _ => all_nat_binomials_iff hpos hn,
    fun _ hn => one_exact_at_each_order hpos hn,
    fun S hS K => finite_subfamily_not_sharp hpos S hS K⟩

#print axioms all_binomials_iff
#print axioms all_nat_binomials_iff
#print axioms one_exact_at_each_order
#print axioms finite_subfamily_not_sharp
#print axioms irrational_example
end Erdos713InfiniteBinomialCompactness
