import FormalConjecturesUtil

/-!
Symmetric nonnegative pair weights give a dissipative signless operator.
The result applies to arbitrary odd monotone test functions, not just
quadratic energy, and requires no graph expansion hypothesis.
-/
namespace Erdos773.GreedyWeightedDissipation
open Finset
set_option maxHeartbeats 1000000

lemma odd_mono_pair_nonneg (φ : ℝ → ℝ) (hmono : Monotone φ)
    (hodd : ∀ x, φ (-x) = -φ x) (a b : ℝ) :
    0 ≤ (φ a+φ b)*(a+b) := by
  by_cases hab : 0 ≤ a+b
  · have hm := hmono (show -b ≤ a by linarith)
    rw [hodd] at hm
    exact mul_nonneg (by linarith) hab
  · have hm := hmono (show a ≤ -b by linarith)
    rw [hodd] at hm
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- Symmetrization retains the whole self-plus-neighbor term. -/
theorem symmetrize {α : Type*} (S : Finset α) (W : α → α → ℝ) (e : α → ℝ)
    (φ : ℝ → ℝ) (hW : ∀ u ∈ S, ∀ v ∈ S, W u v = W v u) :
    (∑ u ∈ S, φ (e u)*((∑ v ∈ S, W u v)*e u+∑ v ∈ S, W u v*e v)) =
      (1/2:ℝ)*∑ u ∈ S, ∑ v ∈ S, W u v*(φ (e u)+φ (e v))*(e u+e v) := by
  have hleft : (∑ u ∈ S, φ (e u)*((∑ v ∈ S, W u v)*e u+∑ v ∈ S, W u v*e v)) =
      ∑ u ∈ S, ∑ v ∈ S, W u v*φ (e u)*(e u+e v) := by
    apply sum_congr rfl
    intro u hu
    rw [mul_add,sum_mul,mul_sum,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    ring
  rw [hleft]
  have hswap : (∑ u ∈ S, ∑ v ∈ S, W u v*φ (e v)*(e u+e v)) =
      ∑ u ∈ S, ∑ v ∈ S, W u v*φ (e u)*(e u+e v) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hv
    rw [hW v hv u hu]
    ring
  have hsplit : (∑ u ∈ S, ∑ v ∈ S, W u v*(φ (e u)+φ (e v))*(e u+e v)) =
      (∑ u ∈ S, ∑ v ∈ S, W u v*φ (e u)*(e u+e v))+
      (∑ u ∈ S, ∑ v ∈ S, W u v*φ (e v)*(e u+e v)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    ring
  rw [hsplit,hswap]
  ring

theorem nonnegative {α : Type*} (S : Finset α) (W : α → α → ℝ) (e : α → ℝ)
    (φ : ℝ → ℝ) (hW : ∀ u ∈ S, ∀ v ∈ S, W u v = W v u)
    (hW0 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W u v)
    (hmono : Monotone φ) (hodd : ∀ x, φ (-x) = -φ x) :
    0 ≤ ∑ u ∈ S, φ (e u)*((∑ v ∈ S, W u v)*e u+∑ v ∈ S, W u v*e v) := by
  rw [symmetrize S W e φ hW]
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro u hu
  apply sum_nonneg
  intro v hv
  rw [mul_assoc]
  exact mul_nonneg (hW0 u hu v hv) (odd_mono_pair_nonneg φ hmono hodd (e u) (e v))

/-- Quadratic specialization: no spectral gap or approximate independence
of neighbor errors is needed. -/
theorem quadratic_identity {α : Type*} (S : Finset α) (W : α → α → ℝ) (e : α → ℝ)
    (hW : ∀ u ∈ S, ∀ v ∈ S, W u v = W v u) :
    (∑ u ∈ S, e u*((∑ v ∈ S, W u v)*e u+∑ v ∈ S, W u v*e v)) =
      (1/2:ℝ)*∑ u ∈ S, ∑ v ∈ S, W u v*(e u+e v)^2 := by
  simpa only [id_eq,pow_two,mul_assoc] using symmetrize S W e id hW

/-- Every odd-power test has the dissipative sign. -/
theorem odd_power_nonnegative {α : Type*} (S : Finset α) (W : α → α → ℝ) (e : α → ℝ)
    (hW : ∀ u ∈ S, ∀ v ∈ S, W u v = W v u)
    (hW0 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W u v) (p : ℕ) (hp : Odd p) :
    0 ≤ ∑ u ∈ S, (e u)^p*((∑ v ∈ S, W u v)*e u+∑ v ∈ S, W u v*e v) := by
  exact nonnegative S W e (fun x => x^p) hW hW0 hp.strictMono_pow.monotone
    (fun x => hp.neg_pow x)

/-- A symmetric weighted Young inequality. Only row sums are bounded;
column bounds follow from symmetry. The parameter t permits a damping
term in one component to absorb its coupling to another component. -/
theorem bilinear_bound {α : Type*} (S : Finset α) (W : α → α → ℝ) (f g : α → ℝ)
    (hW : ∀ u ∈ S, ∀ v ∈ S, W u v = W v u)
    (hW0 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W u v)
    (B t : ℝ) (hrow : ∀ u ∈ S, (∑ v ∈ S, W u v) ≤ B) :
    2*t*(∑ u ∈ S, ∑ v ∈ S, W u v*f u*g v) ≤
      B*(t^2*(∑ u ∈ S, (f u)^2)+(∑ u ∈ S, (g u)^2)) := by
  have hpoint (u : α) (hu : u ∈ S) (v : α) (hv : v ∈ S) :
      2*t*(W u v*f u*g v) ≤ W u v*(t^2*(f u)^2+(g v)^2) := by
    nlinarith only [mul_nonneg (hW0 u hu v hv) (sq_nonneg (t*f u-g v))]
  have hsum := sum_le_sum (fun u hu => sum_le_sum (fun v hv => hpoint u hu v hv))
  simp only [← mul_sum] at hsum
  have hsplit : (∑ u ∈ S, ∑ v ∈ S, W u v*(t^2*(f u)^2+(g v)^2)) =
      (∑ u ∈ S, (∑ v ∈ S, W u v)*(t^2*(f u)^2))+
      (∑ u ∈ S, (∑ v ∈ S, W u v)*(g u)^2) := by
    simp_rw [mul_add,sum_add_distrib]
    congr 1
    · apply sum_congr rfl
      intro u hu
      rw [← sum_mul]
    · rw [sum_comm]
      apply sum_congr rfl
      intro u hu
      rw [← sum_mul]
      congr 1
      apply sum_congr rfl
      intro v hv
      exact hW v hv u hu
  rw [hsplit] at hsum
  apply hsum.trans
  have hf := sum_le_sum (fun u hu => mul_le_mul_of_nonneg_right (hrow u hu)
    (show 0 ≤ t^2*(f u)^2 by positivity))
  have hg := sum_le_sum (fun u hu => mul_le_mul_of_nonneg_right (hrow u hu) (sq_nonneg (g u)))
  have hh := add_le_add hf hg
  simpa only [← mul_sum,mul_add,mul_assoc] using hh

#print axioms odd_mono_pair_nonneg
#print axioms symmetrize
#print axioms nonnegative
#print axioms quadratic_identity
#print axioms odd_power_nonnegative
#print axioms bilinear_bound
end Erdos773.GreedyWeightedDissipation
