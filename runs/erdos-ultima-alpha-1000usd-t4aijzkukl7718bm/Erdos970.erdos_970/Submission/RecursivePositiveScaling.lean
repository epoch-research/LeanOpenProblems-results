import Submission.RecursiveSourceRedundancy

/-! Positive branches retain their negative intercept under dilation. This
strengthens the purely numerical source-redundancy theorem. It does not apply
to arbitrary arithmetic bounds lacking a plain-envelope certificate. -/
namespace Erdos970.RecursiveSieve
open Finset

/-- Positive branches gain the root error cost in addition to convex scaling. -/
theorem linearEnvelope_positive_scale (q : ℕ → ℝ) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) (x c : ℝ) (hx : 0 ≤ x) (hc : 1 ≤ c)
    (hpos : 0 < (linearEnvelope q k x).1) :
    c*(linearEnvelope q k x).1+(c-1)*((k : ℝ)+1) ≤
      (linearEnvelope q k (c*x)).1 := by
  let A : ℝ := 1-∑ i : Fin k, q i.val
  let T (z : ℝ) := ∑ i : Fin k, ∑ j : Fin i.val,
    (linearEnvelope q j.val ((z*q i.val)*q j.val)).1
  have he : (linearEnvelope q k x).1 = max 0 (x*A-(k : ℝ)-1+T x) :=
    linearEnvelope_lower_second_order q k hq x hx
  have hr : 0 < x*A-(k : ℝ)-1+T x := by
    rw [he] at hpos
    by_contra hh
    rw [max_eq_left (le_of_not_gt hh)] at hpos
    exact lt_irrefl _ hpos
  rw [max_eq_right hr.le] at he
  have hT : c*T x ≤ T (c*x) := by
    dsimp only [T]
    simp only [mul_sum]
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    have hjk := j.isLt.trans i.isLt
    have hh := linearEnvelope_lower_scale q j.val (fun t ht => hq t (ht.trans hjk))
      (x*q i.val*q j.val) c
      (mul_nonneg (mul_nonneg hx (hq i.val i.isLt).1) (hq j.val hjk).1) hc
    simpa only [mul_assoc] using hh
  have hu : c*x*A-(k : ℝ)-1+T (c*x) ≤ (linearEnvelope q k (c*x)).1 := by
    rw [linearEnvelope_lower_second_order q k hq (c*x)
      (mul_nonneg (by linarith : 0 ≤ c) hx)]
    exact le_max_right _ _
  rw [he]
  nlinarith only [hT,hu]

/-- Any affine block gain up to j+1 is redundant at earlier prefixes when
its length g has a positive certificate at prefix j in the same envelope. -/
theorem affineSource_le_of_plain_positive (q : ℕ → ℝ) (i j : ℕ) (hij : i ≤ j)
    (hq : ∀ n < j, 0 ≤ q n ∧ q n ≤ 1) (g : ℝ) (hg : 0 < g)
    (hpos : 0 < (linearEnvelope q j g).1) (t : ℝ) (ht : 0 ≤ t) (htj : t ≤ (j : ℝ)+1)
    (x : ℝ) (hx : 0 ≤ x) :
    max 0 (t/g*(x-1)-t) ≤ (linearEnvelope q i x).1 := by
  apply max_le (linearEnvelope_lower_nonneg q i x)
  by_cases hxg : x ≤ g
  · have hm := mul_le_mul_of_nonneg_left (show x-1 ≤ g by linarith) (div_nonneg ht hg.le)
    rw [div_mul_cancel₀ _ hg.ne'] at hm
    exact (by linarith : t/g*(x-1)-t ≤ 0).trans (linearEnvelope_lower_nonneg q i x)
  · have hgap := linearEnvelope_positive_prefix_gap q i j hij hq g hg.le hpos
    rw [Nat.cast_sub hij] at hgap
    have hipos : 0 < (linearEnvelope q i g).1 := by
      have hji : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    have hc : 1 ≤ x/g := (one_le_div hg).mpr (le_of_not_ge hxg)
    have hc0 : 0 ≤ x/g := by linarith
    have hs := linearEnvelope_positive_scale q i (fun n hn => hq n (hn.trans_le hij))
      g (x/g) hg.le hc hipos
    rw [div_mul_cancel₀ _ hg.ne'] at hs
    have hmass : (j : ℝ)+1 ≤ (linearEnvelope q i g).1+((i : ℝ)+1) := by linarith
    have hm := mul_le_mul_of_nonneg_left hmass hc0
    have hu : (x/g)*((j : ℝ)+1)-((i : ℝ)+1) ≤ (linearEnvelope q i x).1 := by
      nlinarith only [hs,hm]
    have ht' := mul_le_mul_of_nonneg_right htj (show 0 ≤ x/g-1 by linarith)
    have hn : 0 ≤ t/g := div_nonneg ht hg.le
    have hji : (i : ℝ) ≤ j := by exact_mod_cast hij
    have he : t/g*(x-1)-t = t*(x/g-1)-t/g := by ring
    rw [he]
    nlinarith only [hu,ht',hn,hji]

/-- Dynamic equality for these more generous plain-certified affine gains. -/
theorem affine_seeded_eq_plain_of_plain_certificates (q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1) (j : ℕ → ℕ) (g t : ℕ → ℝ) (k : ℕ)
    (hg : ∀ n ≤ k, 0 < g n) (hj : ∀ n ≤ k, n ≤ j n)
    (ht : ∀ n ≤ k, 0 ≤ t n ∧ t n ≤ (j n : ℝ)+1)
    (hpos : ∀ n ≤ k, 0 < (linearEnvelope q (j n) (g n)).1)
    (x : ℝ) (hx : 0 ≤ x) :
    seededLinearEnvelope q (fun n y => max 0 (t n/g n*(y-1)-t n)) k x =
      linearEnvelope q k x := by
  apply seededLinearEnvelope_eq_plain q _ k (fun n _ => hq n) _ x hx
  intro n hn y hy
  exact affineSource_le_of_plain_positive q n (j n) (hj n hn) (fun s _ => hq s)
    (g n) (hg n hn) (hpos n hn) (t n) (ht n hn).1 (ht n hn).2 y hy

#print axioms linearEnvelope_positive_scale
#print axioms affineSource_le_of_plain_positive
#print axioms affine_seeded_eq_plain_of_plain_certificates
end Erdos970.RecursiveSieve
