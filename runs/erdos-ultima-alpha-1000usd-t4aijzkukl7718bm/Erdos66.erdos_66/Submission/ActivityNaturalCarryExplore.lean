import Submission.ActivityMassCarryExplore

/-! Actual two-carry transfer using active-pair budgets. -/
namespace Erdos66ActivityNaturalCarry
open Erdos66ActivityMassCarry Erdos66FiniteLogMassBudget
  Erdos66ShortOrbitCarry Erdos66ShortOrbitNatural Erdos66OriginRepair
  Erdos66DiscreteRotationBridge Erdos66IntegerBlock
open AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2000000
variable (M : ℕ) [NeZero M]

lemma upper_activity_budget (C D : ℕ → Finset (ZMod M))
    (hC : Antitone C) (hD : Antitone D) (q t : ℕ)
    (ht : t<M) (horizon : (q+1)^2 ≤ M) :
    |(∑ k∈Finset.range (q+1),
        (upper M (phasedRows M C (phase M) k) (phasedRows M D (phase M) (q-k)) t : ℝ))-
      (1-((t+1 : ℕ) : ℝ)/M)*mixedPhaseMass M C D (phase M) q t| ≤
      budget (supportCount M C D (phase M) q t)
        ((((t+1 : ℕ) : ℝ)/M)*mixedPhaseMass M C D (phase M) q t) := by
  have hl := lower_activity_budget M C D hC hD q t ht horizon
  have he : (∑ k∈Finset.range (q+1),
        (upper M (phasedRows M C (phase M) k) (phasedRows M D (phase M) (q-k)) t : ℝ))+
      (∑ k∈Finset.range (q+1),
        (lower M (phasedRows M C (phase M) k) (phasedRows M D (phase M) (q-k)) t : ℝ))=
      mixedPhaseMass M C D (phase M) q t := by
    rw [←Finset.sum_add_distrib,mixedPhaseMass]
    apply Finset.sum_congr rfl
    intro k hk
    have hh := lower_add_upper M (phasedRows M C (phase M) k)
      (phasedRows M D (phase M) (q-k)) t
    change _=pairCount _ _ (t : ZMod M) at hh
    rw [phased_pairCount M C D (phase M) q k (by simpa using Finset.mem_range.mp hk)] at hh
    exact_mod_cast (show upper M (phasedRows M C (phase M) k)
        (phasedRows M D (phase M) (q-k)) t+
      lower M (phasedRows M C (phase M) k) (phasedRows M D (phase M) (q-k)) t=_ by omega)
  rw [abs_le] at hl ⊢
  constructor <;> nlinarith

/-- Only the total mixed mass and the number of active old pairs enter the
error budget. No factor log(q) is charged uniformly to each pair. -/
theorem natural_activity_budget (C : ℕ → Finset (ZMod M)) (hC : Antitone C)
    (q t : ℕ) (hq : 0<q) (ht : t<M) (horizon : (q+1)^2 ≤ M) :
    |(sumRep (blockSet M (phasedRows M C (phase M))) (q*M+t) : ℝ)-
      (((t+1 : ℕ) : ℝ)/M*phaseMass M C (phase M) q t+
        (1-((t+1 : ℕ) : ℝ)/M)*phaseMass M C (phase M) (q-1) t)| ≤
      budget (supportCount M C C (phase M) q t) (phaseMass M C (phase M) q t)+
        budget (supportCount M C C (phase M) (q-1) t) (phaseMass M C (phase M) (q-1) t) := by
  have hpre : ((q-1)+1)^2 ≤ M := by
    calc
      _ ≤ (q+1)^2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ M := horizon
  have hl := lower_activity_budget M C C hC hC q t ht horizon
  have hu := upper_activity_budget M C C hC hC (q-1) t ht hpre
  have hM : (0 : ℝ)<M := by exact_mod_cast NeZero.pos M
  have hρ : ((t+1 : ℕ) : ℝ)/M ≤ 1 :=
    (div_le_one hM).mpr (by exact_mod_cast Nat.succ_le_iff.mpr ht)
  have weaken (j : ℕ) :
      budget (supportCount M C C (phase M) j t)
        ((((t+1 : ℕ) : ℝ)/M)*mixedPhaseMass M C C (phase M) j t) ≤
      budget (supportCount M C C (phase M) j t) (phaseMass M C (phase M) j t) := by
    apply budget_mono_mass _ _ _ (supportCount_nonneg M C C (phase M) j t)
    exact (mul_le_mul_of_nonneg_right hρ (mixedPhaseMass_nonneg M C C (phase M) j t)).trans_eq
      (one_mul _)
  have hl' := hl.trans (weaken q)
  have hu' := hu.trans (weaken (q-1))
  change |(∑ k∈Finset.range (q+1),
      (lower M (phasedRows M C (phase M) k) (phasedRows M C (phase M) (q-k)) t : ℝ))-
    (((t+1 : ℕ) : ℝ)/M)*phaseMass M C (phase M) q t| ≤ _ at hl'
  change |(∑ k∈Finset.range (q-1+1),
      (upper M (phasedRows M C (phase M) k) (phasedRows M C (phase M) (q-1-k)) t : ℝ))-
    (1-((t+1 : ℕ) : ℝ)/M)*phaseMass M C (phase M) (q-1) t| ≤ _ at hu'
  have hqe : q-1+1=q := by omega
  simp only [hqe,show ∀ k : ℕ, q-1-k=q-k-1 by omega] at hu'
  rw [block_formula M (phasedRows M C (phase M)) q t ht]
  push_cast
  have hid : ∀ x y u v : ℝ, x+y-(u+v)=(x-u)+(y-v) := by intros; ring
  rw [hid]
  push_cast at hl' hu'
  exact (abs_add_le _ _).trans (add_le_add hl' hu')

end Erdos66ActivityNaturalCarry
