import Submission.RecursiveSieveRational

/-! Exact shape properties of the recursive numerical sieve. These justify
second-order evaluation and scaling of existing certificates; they do not
supply positivity at a uniform quadratic interval length. -/
namespace Erdos970.RecursiveSieve
open Finset

section OrderedField
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Density of the independent prefix used only as an algebraic comparison. -/
def prefixDensity (q : ℕ → R) (k : ℕ) : R := ∏ i ∈ range k, (1-q i)

lemma prefixDensity_nonneg (q : ℕ → R) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) : 0 ≤ prefixDensity q k :=
  prod_nonneg (fun i hi => sub_nonneg.mpr (hq i (mem_range.mp hi)).2)

lemma prefixDensity_first_hit (q : ℕ → R) (k : ℕ) :
    prefixDensity q k = 1-∑ i : Fin k, q i.val * prefixDensity q i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun i => q i*prefixDensity q i) k]
  induction k with
  | zero => simp [prefixDensity]
  | succ k ih =>
    rw [sum_range_succ, show prefixDensity q (k+1) =
      prefixDensity q k*(1-q k) from prod_range_succ (fun i => 1-q i) k, ih]
    ring

lemma linearEnvelope_lower_nonneg (q : ℕ → R) (k : ℕ) (x : R) :
    0 ≤ (linearEnvelope q k x).1 := by
  rw [linearEnvelope]
  dsimp only
  split_ifs
  · rfl
  · exact le_max_left _ _

/-- The upper envelope is always at least one plus the independent mass.
In particular every upper child is at least one, even when its mass is tiny. -/
theorem linearEnvelope_density_bounds (q : ℕ → R) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) (x : R) (hx : 0 ≤ x) :
    (linearEnvelope q k x).1 ≤ x*prefixDensity q k ∧
      x*prefixDensity q k+1 ≤ (linearEnvelope q k x).2 := by
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    have hchild (i : Fin k) := ih i.val i.isLt
      (fun j hj => hq j (hj.trans i.isLt)) (x*q i.val)
      (mul_nonneg hx (hq i.val i.isLt).1)
    have hlo := sum_le_sum (s := (univ : Finset (Fin k)))
      (fun i _ => (hchild i).1)
    have hhi := sum_le_sum (s := (univ : Finset (Fin k)))
      (fun i _ => (hchild i).2)
    have hmass : (∑ i : Fin k, x*q i.val*prefixDensity q i.val) =
        x*(1-prefixDensity q k) := by
      rw [prefixDensity_first_hit q k]
      simp only [sub_sub_cancel]
      rw [mul_sum]
      exact sum_congr rfl (fun _ _ => mul_assoc _ _ _)
    rw [hmass] at hlo
    rw [sum_add_distrib, hmass] at hhi
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hhi
    have hd := mul_nonneg hx (prefixDensity_nonneg q k hq)
    rw [linearEnvelope]
    dsimp only
    constructor
    · split_ifs
      · exact hd
      · apply max_le hd
        have hk : (0 : R) ≤ k := Nat.cast_nonneg k
        linarith
    · linarith

/-- For valid marginals and nonnegative mass, the pruning test is redundant:
the unpruned lower expression is nonpositive whenever the test discards it. -/
theorem linearEnvelope_lower_eq_max (q : ℕ → R) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) (x : R) (hx : 0 ≤ x) :
    (linearEnvelope q k x).1 =
      max 0 (x-1-∑ i : Fin k, (linearEnvelope q i.val (x*q i.val)).2) := by
  conv_lhs => rw [linearEnvelope]
  dsimp only
  split_ifs with htest
  · have hc (i : Fin k) : 1 ≤ (linearEnvelope q i.val (x*q i.val)).2 := by
      have hh := (linearEnvelope_density_bounds q i.val
        (fun j hj => hq j (hj.trans i.isLt)) (x*q i.val)
        (mul_nonneg hx (hq i.val i.isLt).1)).2
      have hn := mul_nonneg (mul_nonneg hx (hq i.val i.isLt).1)
        (prefixDensity_nonneg q i.val (fun j hj => hq j (hj.trans i.isLt)))
      linarith
    have hs := sum_le_sum (s := (univ : Finset (Fin k))) (fun i _ => hc i)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
    exact (max_eq_left (by linarith)).symm
  · rfl

/-- Exact second-order positive-part recurrence. The constants include the
root unit error; no rounding or discarded constant is hidden in this formula. -/
theorem linearEnvelope_lower_second_order (q : ℕ → R) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) (x : R) (hx : 0 ≤ x) :
    (linearEnvelope q k x).1 = max 0
      (x*(1-∑ i : Fin k, q i.val)-(k : R)-1 +
        ∑ i : Fin k, ∑ j : Fin i.val,
          (linearEnvelope q j.val ((x*q i.val)*q j.val)).1) := by
  rw [linearEnvelope_lower_eq_max q k hq x hx]
  have hu (i : Fin k) : (linearEnvelope q i.val (x*q i.val)).2 =
      x*q i.val+1-∑ j : Fin i.val,
        (linearEnvelope q j.val ((x*q i.val)*q j.val)).1 := by
    rw [linearEnvelope]
  simp_rw [hu]
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  ring

lemma linearEnvelope_lower_zero (q : ℕ → R) (k : ℕ) :
    (linearEnvelope q k 0).1 = 0 := by
  rw [linearEnvelope]
  simp only [show (0 : R) ≤ (k : R)+1 by positivity, if_true]

/-- The exact lower envelope is convex in the nonnegative input mass. -/
theorem linearEnvelope_lower_convex (q : ℕ → R) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) :
    ConvexOn R (Set.Ici 0) (fun x => (linearEnvelope q k x).1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    change (linearEnvelope q k (a*x+b*y)).1 ≤
      a*(linearEnvelope q k x).1+b*(linearEnvelope q k y).1
    have hxy : 0 ≤ a*x+b*y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
    rw [linearEnvelope_lower_second_order q k hq _ hxy,
      linearEnvelope_lower_second_order q k hq x hx,
      linearEnvelope_lower_second_order q k hq y hy]
    let A : R := 1-∑ i : Fin k, q i.val
    let T (z : R) := ∑ i : Fin k, ∑ j : Fin i.val,
      (linearEnvelope q j.val ((z*q i.val)*q j.val)).1
    change max 0 ((a*x+b*y)*A-(k : R)-1+T (a*x+b*y)) ≤
      a*max 0 (x*A-(k : R)-1+T x)+b*max 0 (y*A-(k : R)-1+T y)
    have hT : T (a*x+b*y) ≤ a*T x+b*T y := by
      dsimp only [T]
      simp only [mul_sum, ← sum_add_distrib]
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hjk : j.val < k := j.isLt.trans i.isLt
      have hc := (ih j.val hjk (fun t ht => hq t (ht.trans hjk))).2
        (show x*q i.val*q j.val ∈ Set.Ici 0 from
          mul_nonneg (mul_nonneg hx (hq i.val i.isLt).1) (hq j.val hjk).1)
        (show y*q i.val*q j.val ∈ Set.Ici 0 from
          mul_nonneg (mul_nonneg hy (hq i.val i.isLt).1) (hq j.val hjk).1)
        ha hb hab
      simpa only [smul_eq_mul, add_mul, mul_assoc] using hc
    apply max_le
    · positivity
    · have ha' := mul_le_mul_of_nonneg_left
        (le_max_right 0 (x*A-(k : R)-1+T x)) ha
      have hb' := mul_le_mul_of_nonneg_left
        (le_max_right 0 (y*A-(k : R)-1+T y)) hb
      have he : (a*x+b*y)*A-(k : R)-1+a*T x+b*T y =
          a*(x*A-(k : R)-1+T x)+b*(y*A-(k : R)-1+T y) := by
        have hh := congrArg (fun z : R => z*((k : R)+1)) hab
        nlinarith only [hh]
      linarith

/-- Scaling an already certified mass cannot decrease the lower count per
unit mass. This does not compare different prime budgets. -/
theorem linearEnvelope_lower_scale (q : ℕ → R) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) (x c : R) (hx : 0 ≤ x) (hc : 1 ≤ c) :
    c*(linearEnvelope q k x).1 ≤ (linearEnvelope q k (c*x)).1 := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hf := linearEnvelope_lower_convex q k hq
  have hinv : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).mpr hc
  have hh := hf.2 (show c*x ∈ Set.Ici 0 from mul_nonneg hc0.le hx)
    (show (0 : R) ∈ Set.Ici 0 from le_rfl)
    (show 0 ≤ c⁻¹ from inv_nonneg.mpr hc0.le)
    (show 0 ≤ 1-c⁻¹ from sub_nonneg.mpr hinv)
    (show c⁻¹+(1-c⁻¹) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, linearEnvelope_lower_zero,
    inv_mul_cancel_left₀ hc0.ne'] at hh
  have hm := mul_le_mul_of_nonneg_left hh hc0.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul] using hm

/-- Monotonicity follows from convexity, nonnegativity, and the value at zero. -/
theorem linearEnvelope_lower_monotone (q : ℕ → R) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) :
    MonotoneOn (fun x => (linearEnvelope q k x).1) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  by_cases hx0 : x = 0
  · simp only [hx0, linearEnvelope_lower_zero]
    exact linearEnvelope_lower_nonneg q k y
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hc : 1 ≤ y/x := (le_div_iff₀ hxpos).mpr (by simpa using hxy)
    have hh := linearEnvelope_lower_scale q k hq x (y/x) hx hc
    rw [div_mul_cancel₀ _ hx0] at hh
    have hl := mul_le_mul_of_nonneg_right hc (linearEnvelope_lower_nonneg q k x)
    calc
      (linearEnvelope q k x).1 ≤ (y/x)*(linearEnvelope q k x).1 := by
        simpa only [one_mul] using hl
      _ ≤ (linearEnvelope q k y).1 := hh

end OrderedField

#print axioms linearEnvelope_lower_second_order
#print axioms linearEnvelope_lower_convex
#print axioms linearEnvelope_lower_scale
#print axioms linearEnvelope_lower_monotone
end Erdos970.RecursiveSieve
