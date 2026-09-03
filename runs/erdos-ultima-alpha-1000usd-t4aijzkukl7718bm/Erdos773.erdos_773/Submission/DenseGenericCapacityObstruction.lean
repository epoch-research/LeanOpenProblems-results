import Submission.DenseCapacityScales
import Submission.IntegerDifferenceCapacityGeneral

/-! An obstruction to black-box conversion of bounded difference capacity
into near-linear Sidon subsets for arbitrary integer sets. These sets are
not claimed to be sets of square values. -/
namespace Erdos773.DenseGenericCapacityObstruction
open Finset Filter DenseSidonSeedWitnesses BernoulliCarrier IntegerDifferenceCapacity
  IntegerDifferenceCapacityGeneral
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable

def reward (n R g : ℕ) (B : Finset ℕ) : ℝ :=
  B.card-((aps (R^100)).filter (· ⊆ B)).card-((obstructions (R^100) g).filter (· ⊆ B)).card-(R:ℝ)^100*penalty n R B

lemma expected_reward_of_scale {n R g : ℕ} (hn : 1000 ≤ n) (hR : 1000 ≤ R)
    (hlog : 5 ≤ Real.log (n:ℝ)) (M : ℝ)
    (hscale : M ≤ density n R*(R:ℝ)^100-(density n R)^3*(R:ℝ)^200-
      (density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2)-1) :
    M ≤ ∑ f : host R → Bool, trialWeight (density n R) f*reward n R g (sample (host R) f) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hR0 : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hp : 0 ≤ density n R := by unfold density; positivity
  have hAP := weighted_uniform_count (host R) (aps (R^100)) (fun I hI => aps_subset hI) 3
    (fun I hI => aps_size hI) (density n R)
  have hSix := weighted_uniform_count (host R) (obstructions (R^100) g) (fun I hI => obstructions_subset hI) (2*(g+1))
    (fun I hI => obstructions_size hI) (density n R)
  have hpen := mul_le_mul_of_nonneg_left (expected_penalty_small (by omega : 0<n) hR hlog) (pow_nonneg hR0.le 100)
  have hpen1 := hpen.trans (exponential_penalty_budget (by omega))
  have hAc : ((aps (R^100)).card:ℝ) ≤ (R:ℝ)^200 := by
    have hh : ((aps (R^100)).card:ℝ) ≤ ((R:ℝ)^100)^2 := by exact_mod_cast aps_card (R^100)
    simpa only [← pow_mul] using hh
  have hSc : ((obstructions (R^100) g).card:ℝ) ≤ ((R:ℝ)^100)^(g+2) := by
    exact_mod_cast obstructions_card (R^100) g
  have hAm := mul_le_mul_of_nonneg_left hAc (pow_nonneg hp 3)
  have hSm := mul_le_mul_of_nonneg_left hSc (pow_nonneg hp (2*(g+1)))
  have hreward : (∑ f : host R → Bool, trialWeight (density n R) f*reward n R g (sample (host R) f)) =
      density n R*(R:ℝ)^100-(density n R)^3*(aps (R^100)).card-(density n R)^(2*(g+1))*(obstructions (R^100) g).card-
      (R:ℝ)^100*(∑ f : host R → Bool, trialWeight (density n R) f*penalty n R (sample (host R) f)) := by
    simp only [reward,mul_sub,sum_sub_distrib,weighted_card,host_card,Nat.cast_pow,hAP,hSix]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro f hf
    ring
  rw [hreward]
  linarith only [hscale,hpen1,hAm,hSm]

/-- The generic obstruction permits an arbitrary positive capacity and
separate witness and ambient parameters satisfying the exact scale relation. -/
theorem finite_obstruction_of_reward {n R g : ℕ} (hn : 1000 ≤ n) (hR : 1000 ≤ R)
    (hlog : 5 ≤ Real.log (n:ℝ)) (M : ℝ) (hM : 0<M)
    (hscale : M ≤ density n R*(R:ℝ)^100-(density n R)^3*(R:ℝ)^200-
      (density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2)-1) :
    ∃ B ⊆ Icc 1 (R^100), M ≤ (B.card:ℝ) ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ g) ∧
      (∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<R^40) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hR0 : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hp : 0 ≤ density n R := by unfold density; positivity
  have hp1 : density n R ≤ 1 := by
    have hR1 : (1:ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpow := one_le_pow₀ hR1 (n := 50)
    have hh := mul_le_mul hpow hn1 (by positivity : (0:ℝ) ≤ 1) (by positivity)
    unfold density
    exact (div_le_one (by positivity)).mpr (by nlinarith only [hh])
  let cost (f : host R → Bool) := reward n R g (sample (host R) f)
  obtain ⟨f,hf,hmax⟩ := exists_max_image univ cost univ_nonempty
  have hmaxR : (∑ g : host R → Bool, trialWeight (density n R) g*cost g) ≤ cost f := by
    calc
      _ ≤ ∑ g : host R → Bool, trialWeight (density n R) g*cost f :=
        sum_le_sum (fun g hg => mul_le_mul_of_nonneg_left (hmax g hg) (trialWeight_nonneg hp hp1 g))
      _ = _ := by rw [← sum_mul,sum_trialWeight,one_mul]
  let A := sample (host R) f
  have hA : A ⊆ Icc 1 (R^100) := sample_subset (host R) f
  have hrew : M ≤ reward n R g A := (expected_reward_of_scale hn hR hlog M hscale).trans hmaxR
  have hpos : 0 < reward n R g A := lt_of_lt_of_le hM hrew
  have hnolarge (S : Finset ℕ) (hSA : S ⊆ A) (hS : IsSidon (S:Set ℕ)) : S.card<R^40 := by
    by_contra! hlarge
    have hpen := penalty_large (by omega : 1 ≤ n) (by omega : 1 ≤ R) hA hSA hS hlarge
    have hm := mul_le_mul_of_nonneg_left hpen (pow_nonneg hR0.le 100)
    have hc : (A.card:ℝ) ≤ (R:ℝ)^100 := by
      have hh := card_le_card hA
      simp only [Nat.card_Icc,Nat.add_sub_cancel] at hh
      exact_mod_cast hh
    have h₃ : (0:ℝ) ≤ ((aps (R^100)).filter (· ⊆ A)).card := Nat.cast_nonneg _
    have h₆ : (0:ℝ) ≤ ((obstructions (R^100) g).filter (· ⊆ A)).card := Nat.cast_nonneg _
    unfold reward at hpos
    linarith only [hm,hc,h₃,h₆,hpos]
  let H₃ := (aps (R^100)).filter (· ⊆ A)
  let H₆ := (obstructions (R^100) g).filter (· ⊆ A)
  obtain ⟨B,hBA,hcard,havoid⟩ := delete_forbidden_edges A (H₃ ∪ H₆) (by
    intro e he
    apply card_pos.mp
    rcases mem_union.mp he with he | he
    · rw [aps_size (mem_filter.mp he).1]; omega
    · rw [obstructions_size (mem_filter.mp he).1]; omega)
  have hBap : ∀ e ∈ aps (R^100), ¬e ⊆ B := by
    intro e he heB
    exact havoid e (mem_union_left _ (mem_filter.mpr ⟨he,heB.trans hBA⟩)) heB
  have hBsix : ∀ e ∈ obstructions (R^100) g, ¬e ⊆ B := by
    intro e he heB
    exact havoid e (mem_union_right _ (mem_filter.mpr ⟨he,heB.trans hBA⟩)) heB
  have hBAP := apFree_of_avoids (hBA.trans hA) hBap
  refine ⟨B,hBA.trans hA,?_,hBAP,IntegerDifferenceCapacityGeneral.capacity_of_avoids (hBA.trans hA) hBAP hBsix,
    fun S hSB hS => hnolarge S (hSB.trans hBA) hS⟩
  have hc : (A.card:ℝ) ≤ B.card+H₃.card+H₆.card := by
    have hh := card_union_le H₃ H₆
    have hhh : A.card ≤ B.card+H₃.card+H₆.card := by omega
    exact_mod_cast hhh
  have hpnon := mul_nonneg (pow_nonneg hR0.le 100) (penalty_nonneg n R A)
  dsimp [reward] at hrew
  dsimp [H₃,H₆] at hc
  linarith only [hc,hpnon,hrew]


lemma expected_reward {n R g : ℕ} (hn : 1000 ≤ n) (hR : 1000 ≤ R)
    (hg : 1≤g) (hlog : 5 ≤ Real.log (n:ℝ))
    (he : (R:ℝ)^50=(n:ℝ)^(2*g)) :
    (R:ℝ)^50/(8*n) ≤ ∑ f : host R → Bool,
      trialWeight (density n R) f*reward n R g (sample (host R) f) :=
  expected_reward_of_scale hn hR hlog _
    (DenseCapacityScales.reward_scales hn (by omega) hg he)

theorem finite_obstruction {n R g : ℕ} (hn : 1000 ≤ n) (hR : 1000 ≤ R)
    (hg : 1≤g) (hlog : 5 ≤ Real.log (n:ℝ))
    (he : (R:ℝ)^50=(n:ℝ)^(2*g)) :
    ∃ B ⊆ Icc 1 (R^100), (R:ℝ)^50/(8*n) ≤ (B.card:ℝ) ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ g) ∧
      (∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<R^40) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hR0 : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  exact finite_obstruction_of_reward hn hR hlog _ (by positivity)
    (DenseCapacityScales.reward_scales hn (by omega) hg he)

theorem finite_endpoint_obstruction {n R g : ℕ} (hn : 1000 ≤ n) (hR : 1000 ≤ R)
    (hg : 1≤g) (hlog : 5 ≤ Real.log (n:ℝ))
    (he : (R:ℝ)^50=(n:ℝ)^(2*g+1)) :
    ∃ B ⊆ Icc 1 (R^100), (R:ℝ)^50/(8*n) ≤ (B.card:ℝ) ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ g) ∧
      (∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<R^40) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hR0 : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  exact finite_obstruction_of_reward hn hR hlog _ (by positivity)
    (DenseCapacityScales.reward_scales_endpoint hn (by omega) hg he)

#print axioms expected_reward
#print axioms finite_obstruction
#print axioms finite_endpoint_obstruction
#print axioms finite_obstruction_of_reward
end
end Erdos773.DenseGenericCapacityObstruction
