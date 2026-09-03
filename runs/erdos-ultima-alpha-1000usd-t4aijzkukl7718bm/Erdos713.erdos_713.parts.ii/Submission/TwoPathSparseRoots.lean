import FormalConjecturesUtil
import Submission.TwoPathRootCounting

/-! Subcritical maximum degree makes two-walk endpoint quadruples sparse.
No exact extremal graph with this degree cap is asserted. -/
open SimpleGraph Filter Finset
open scoped Topology
namespace Erdos713TwoPathSparseRoots
open Erdos713TwoPathRootCounting
set_option maxHeartbeats 1000000

open scoped Classical in
lemma eight_count_le {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) {ε : ℝ}
    (hε : 18*(D : ℝ)^8 ≤ ε*(Fintype.card V : ℝ)^2) :
    ((totalLengthRoots G 8).card : ℝ) ≤ ε*(Fintype.card V : ℝ)^4 := by
  classical
  have hb : ((totalLengthRoots G 8).card : ℝ) ≤
      18*(Fintype.card V : ℝ)^2*(D : ℝ)^8 := by
    exact_mod_cast card_totalLengthRoots_le G D hD 8
  have hm := mul_le_mul_of_nonneg_left hε (sq_nonneg (Fintype.card V : ℝ))
  nlinarith only [hb,hm]

open scoped Classical in
/-- Uniform over all graphs and degree caps at each sufficiently large order.
There is no forbidden-subgraph hypothesis in this counting bound. -/
theorem eventually_eight_roots_sparse {β C ε : ℝ} (hβ : β < 1/4) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : SimpleGraph (Fin n)) (D : ℕ),
      (∀ v, G.degree v ≤ D) → (D : ℝ) ≤ C*(n : ℝ)^β →
      ((totalLengthRoots G 8).card : ℝ) ≤ ε*(n : ℝ)^4 := by
  classical
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^(8*β-2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_sub] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 2-8*β)).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => 18*C^8*(n : ℝ)^(8*β-2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hpow.const_mul (18*C^8)
  filter_upwards [hlim.eventually_lt_const hε,eventually_gt_atTop (0 : ℕ)] with n hn hn0
  intro G D hD hDC
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hDp : (D : ℝ)^8 ≤ C^8*(n : ℝ)^(8*β) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) D) hDC 8
    rw [mul_pow,← Real.rpow_mul_natCast hnR.le] at hh
    convert hh using 1
    congr 2
    ring
  have hid : (n : ℝ)^2*(n : ℝ)^(8*β-2) = (n : ℝ)^(8*β) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hnR]
    congr 1
    norm_num
  have hm := mul_lt_mul_of_pos_left hn (sq_pos_of_pos hnR)
  have hx : 18*C^8*(n : ℝ)^(8*β) < ε*(n : ℝ)^2 := by
    calc
      _ = (n : ℝ)^2*(18*C^8*(n : ℝ)^(8*β-2)) := by rw [← hid]; ring
      _ < (n : ℝ)^2*ε := hm
      _ = _ := mul_comm _ _
  have heps : 18*(D : ℝ)^8 ≤ ε*(Fintype.card (Fin n) : ℝ)^2 := by
    simp only [Fintype.card_fin]
    calc
      18*(D : ℝ)^8 ≤ 18*(C^8*(n : ℝ)^(8*β)) :=
        mul_le_mul_of_nonneg_left hDp (by norm_num)
      _ = 18*C^8*(n : ℝ)^(8*β) := (mul_assoc _ _ _).symm
      _ ≤ ε*(n : ℝ)^2 := hx.le
  simpa only [Fintype.card_fin] using eight_count_le G D hD heps

#print axioms eight_count_le
#print axioms eventually_eight_roots_sparse
end Erdos713TwoPathSparseRoots
