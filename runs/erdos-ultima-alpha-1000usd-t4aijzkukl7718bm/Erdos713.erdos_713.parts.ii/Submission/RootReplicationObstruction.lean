import FormalConjecturesUtil
import Submission.CompactRate

/-! Replicating a rooted tree a fixed number of times need not preserve its
extremal exponent. This is an obstruction to one proposed reduction, not a
disproof of the conjecture in Spec.lean. No exact asymptotic is asserted. -/

open SimpleGraph Filter Asymptotics

namespace Erdos713RootReplicationObstruction

/-- `t` copies of a three-leaf star, glued along the three leaves.
The left summand contains the shared leaves, the right summand the centres. -/
abbrev replicatedStar (t : ℕ) := completeBipartiteGraph (Fin 3) (Fin t)

def swapTwo : replicatedStar 2 ≃g Erdos713K2t.K2t 3 := by
  refine ⟨Equiv.sumComm _ _, ?_⟩
  intro u v
  cases u <;> cases v <;>
    simp [replicatedStar, Erdos713K2t.K2t, completeBipartiteGraph]

/-- Adding one more centre changes the threshold from `3/2` to `5/3`. -/
theorem two_rate : Erdos713Rate.HasRate (replicatedStar 2) ((3 : ℝ)/2) :=
  Erdos713Rate.iso_rate swapTwo
    (Erdos713Rate.k2t_rate (Erdos713K2t.contains_K22 (by decide)) (.refl _))

theorem three_rate : Erdos713Rate.HasRate (replicatedStar 3) ((5 : ℝ)/3) :=
  Erdos713Rate.k3t_rate (.refl _) (.refl _)

/-- The obstruction persists even if an exponent loss smaller than `1/6`
is allowed. This is stronger than failure of constant-factor preservation. -/
theorem no_small_power_loss {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1/6) :
    ¬ (fun n : ℕ => (extremalNumber n (replicatedStar 3) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^ε * (extremalNumber n (replicatedStar 2) : ℝ)) := by
  intro h
  have hProd :
      (fun n : ℕ => (n : ℝ)^ε * (extremalNumber n (replicatedStar 2) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^(ε + 3/2)) := by
    have hp := (isBigO_refl (fun n : ℕ => (n : ℝ)^ε) atTop).mul two_rate.upper
    apply hp.congr' Filter.EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (Real.rpow_add (by exact_mod_cast hn : (0 : ℝ) < n) ε (3/2)).symm
  have hBound := three_rate.lower (ε+3/2) (by linarith) (h.trans hProd)
  linarith

theorem no_constant_loss :
    ¬ (fun n : ℕ => (extremalNumber n (replicatedStar 3) : ℝ)) =O[atTop]
      (fun n : ℕ => (extremalNumber n (replicatedStar 2) : ℝ)) := by
  simpa using no_small_power_loss (ε := 0) (by norm_num) (by norm_num)

open scoped Classical in
/-- In particular, no universal extraction of a two-replica-free subgraph
from a three-replica-free host can retain edges with loss `C*n^ε`, for
`0 ≤ ε < 1/6`. -/
theorem no_uniform_extraction {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1/6) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (replicatedStar 3).Free G → ∃ J : SimpleGraph (Fin n),
        J ≤ G ∧ (replicatedStar 2).Free J ∧
          (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ)^ε * J.edgeFinset.card := by
  classical
  rintro ⟨C, hC, hExtract⟩
  apply no_small_power_loss hε hε'
  apply IsBigO.of_bound C
  filter_upwards with n
  simp only [Real.norm_natCast, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  rw [← Fintype.card_fin n]
  apply (extremalNumber_le_iff_of_nonneg (replicatedStar 3) (by positivity)).mpr
  intro G _ hFree
  obtain ⟨J, _, hJ, hEdges⟩ := hExtract n G hFree
  have hBound : (J.edgeFinset.card : ℝ) ≤ extremalNumber n (replicatedStar 2) := by
    exact_mod_cast (show J.edgeFinset.card ≤ extremalNumber n (replicatedStar 2) by
      simpa only [Fintype.card_fin] using card_edgeFinset_le_extremalNumber hJ)
  calc
    (G.edgeFinset.card : ℝ) ≤ C*(n : ℝ)^ε*J.edgeFinset.card := by
      simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using hEdges
    _ ≤ C*(n : ℝ)^ε*extremalNumber n (replicatedStar 2) :=
      mul_le_mul_of_nonneg_left hBound (by positivity)
    _ = _ := by simp only [Fintype.card_fin]; ring

end Erdos713RootReplicationObstruction

#print axioms Erdos713RootReplicationObstruction.no_small_power_loss
#print axioms Erdos713RootReplicationObstruction.no_uniform_extraction
