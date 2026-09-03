import Submission.SidonSeedWitnesses
import Submission.IntegerSumCapacity

/-! Simultaneously bounded sum and difference multiplicities do not give
near-linear Sidon extraction for arbitrary integer sets. The sets below
are NOT asserted to consist of squares. This does not settle Erdos 773. -/
namespace Erdos773.JointCapacityObstruction
open Finset Filter SidonSeedWitnesses BernoulliCarrier IntegerDifferenceCapacity
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable

def sumSix (m : ℕ) : Finset (Finset ℕ) := IntegerSumCapacity.obstructions m 2

lemma sumSix_card (m : ℕ) : (sumSix m).card ≤ 2*m^4 :=
  IntegerSumCapacity.obstructions_card m 2
lemma sumSix_size {m : ℕ} {e : Finset ℕ} (he : e ∈ sumSix m) : e.card=6 :=
  IntegerSumCapacity.obstructions_size he
lemma sumSix_subset {m : ℕ} {e : Finset ℕ} (he : e ∈ sumSix m) : e ⊆ Icc 1 m :=
  IntegerSumCapacity.obstructions_subset he

def reward (n : ℕ) (B : Finset ℕ) : ℝ :=
  B.card-((aps (n^40)).filter (· ⊆ B)).card-((sixes (n^40)).filter (· ⊆ B)).card-((sumSix (n^40)).filter (· ⊆ B)).card-(n:ℝ)^40*penalty n B

lemma reward_scales {n : ℕ} (hn : 2 ≤ n) :
    (n:ℝ)^16/8 ≤ density n*(n:ℝ)^40-(density n)^3*(n:ℝ)^80-3*(density n)^6*(n:ℝ)^160-1 := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  have h₁ : density n*(n:ℝ)^40=(n:ℝ)^16/4 := by unfold density; field_simp
  have h₂ : (density n)^3*(n:ℝ)^80=(n:ℝ)^8/64 := by unfold density; field_simp; ring
  have h₃ : (density n)^6*(n:ℝ)^160=(n:ℝ)^16/4096 := by unfold density; field_simp; ring
  have hpow : (n:ℝ)^8 ≤ (n:ℝ)^16 := pow_le_pow_right₀ (by linarith only [hnR]) (by omega)
  have h16 : (16:ℝ) ≤ (n:ℝ)^16 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hnR 16
    norm_num at h
    linarith only [h]
  rw [h₁,h₂]
  have h₃' : 3*(density n)^6*(n:ℝ)^160 = 3*((n:ℝ)^16/4096) := by nlinarith only [h₃]
  rw [h₃']
  nlinarith only [hpow,h16]

lemma expected_reward {n : ℕ} (hn : 1000 ≤ n) (hlog : 5 ≤ Real.log (n:ℝ)) :
    (n:ℝ)^16/8 ≤ ∑ f : host n → Bool, trialWeight (density n) f*reward n (sample (host n) f) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp : 0 ≤ density n := by unfold density; positivity
  have hAP := weighted_uniform_count (host n) (aps (n^40)) (fun I hI => aps_subset hI) 3
    (fun I hI => aps_size hI) (density n)
  have hSix := weighted_uniform_count (host n) (sixes (n^40)) (fun I hI => sixes_subset hI) 6
    (fun I hI => sixes_size hI) (density n)
  have hSum := weighted_uniform_count (host n) (sumSix (n^40))
    (fun I hI => sumSix_subset hI) 6 (fun I hI => sumSix_size hI) (density n)
  have hpen := mul_le_mul_of_nonneg_left (expected_penalty_small hn hlog) (pow_nonneg hn0.le 40)
  have hpen1 := hpen.trans (exponential_penalty_budget (by omega))
  have hAc : ((aps (n^40)).card:ℝ) ≤ (n:ℝ)^80 := by
    have hh : ((aps (n^40)).card:ℝ) ≤ ((n:ℝ)^40)^2 := by exact_mod_cast aps_card (n^40)
    simpa only [← pow_mul] using hh
  have hSc : ((sixes (n^40)).card:ℝ) ≤ (n:ℝ)^160 := by
    have hh : ((sixes (n^40)).card:ℝ) ≤ ((n:ℝ)^40)^4 := by exact_mod_cast sixes_card (n^40)
    simpa only [← pow_mul] using hh
  have hSumC : ((sumSix (n^40)).card:ℝ) ≤ 2*(n:ℝ)^160 := by
    have hh : ((sumSix (n^40)).card:ℝ) ≤ 2*((n:ℝ)^40)^4 := by exact_mod_cast sumSix_card (n^40)
    simpa only [← pow_mul] using hh
  have hSumM := mul_le_mul_of_nonneg_left hSumC (pow_nonneg hp 6)
  have hAm := mul_le_mul_of_nonneg_left hAc (pow_nonneg hp 3)
  have hSm := mul_le_mul_of_nonneg_left hSc (pow_nonneg hp 6)
  have he : (∑ f : host n → Bool, trialWeight (density n) f*reward n (sample (host n) f)) =
      density n*(n:ℝ)^40-(density n)^3*(aps (n^40)).card-(density n)^6*(sixes (n^40)).card-(density n)^6*(sumSix (n^40)).card-
      (n:ℝ)^40*(∑ f : host n → Bool, trialWeight (density n) f*penalty n (sample (host n) f)) := by
    simp only [reward,mul_sub,sum_sub_distrib,weighted_card,host_card,Nat.cast_pow,hAP,hSix,hSum]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro f hf
    ring
  rw [he]
  have hb := reward_scales (by omega : 2 ≤ n)
  nlinarith only [hb,hpen1,hAm,hSm,hSumM]

/-- Capacity two does not force a near-linear Sidon subset for arbitrary
integer carriers: a fixed-power gap already occurs at the following scales. -/
theorem finite_obstruction {n : ℕ} (hn : 1000 ≤ n) (hlog : 5 ≤ Real.log (n:ℝ)) :
    ∃ B ⊆ Icc 1 (n^40), (n:ℝ)^16/8 ≤ (B.card:ℝ) ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ 2) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ 2) ∧
      (∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<n^15) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp : 0 ≤ density n := by unfold density; positivity
  have hp1 : density n ≤ 1 := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpow := one_le_pow₀ hn1 (n := 24)
    unfold density
    exact (div_le_one (by positivity)).mpr (by linarith only [hpow])
  let cost (f : host n → Bool) := reward n (sample (host n) f)
  obtain ⟨f,hf,hmax⟩ := exists_max_image univ cost univ_nonempty
  have hmaxR : (∑ g : host n → Bool, trialWeight (density n) g*cost g) ≤ cost f := by
    calc
      _ ≤ ∑ g : host n → Bool, trialWeight (density n) g*cost f :=
        sum_le_sum (fun g hg => mul_le_mul_of_nonneg_left (hmax g hg) (trialWeight_nonneg hp hp1 g))
      _ = _ := by rw [← sum_mul,sum_trialWeight,one_mul]
  let A := sample (host n) f
  have hA : A ⊆ Icc 1 (n^40) := sample_subset (host n) f
  have hrew : (n:ℝ)^16/8 ≤ reward n A := (expected_reward hn hlog).trans hmaxR
  have hpos : 0 < reward n A := lt_of_lt_of_le (by positivity) hrew
  have hnolarge (S : Finset ℕ) (hSA : S ⊆ A) (hS : IsSidon (S:Set ℕ)) : S.card<n^15 := by
    by_contra! hlarge
    have hpen := penalty_large (by omega : 1 ≤ n) hA hSA hS hlarge
    have hm := mul_le_mul_of_nonneg_left hpen (pow_nonneg hn0.le 40)
    have hc : (A.card:ℝ) ≤ (n:ℝ)^40 := by
      have hh := card_le_card hA
      simp only [Nat.card_Icc,Nat.add_sub_cancel] at hh
      exact_mod_cast hh
    have h₃ : (0:ℝ) ≤ ((aps (n^40)).filter (· ⊆ A)).card := Nat.cast_nonneg _
    have h₆ : (0:ℝ) ≤ ((sixes (n^40)).filter (· ⊆ A)).card := Nat.cast_nonneg _
    have hsum6 : (0:ℝ) ≤ ((sumSix (n^40)).filter (· ⊆ A)).card := Nat.cast_nonneg _
    unfold reward at hpos
    linarith only [hm,hc,h₃,h₆,hsum6,hpos]
  let H₃ := (aps (n^40)).filter (· ⊆ A)
  let H₆ := (sixes (n^40)).filter (· ⊆ A)
  let HS := (sumSix (n^40)).filter (· ⊆ A)
  obtain ⟨B,hBA,hcard,havoid⟩ := delete_forbidden_edges A ((H₃ ∪ H₆) ∪ HS) (by
    intro e he
    apply card_pos.mp
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · rw [aps_size (mem_filter.mp he).1]; omega
      · rw [sixes_size (mem_filter.mp he).1]; omega
    · rw [sumSix_size (mem_filter.mp he).1]; omega)
  have hBap : ∀ e ∈ aps (n^40), ¬e ⊆ B := by
    intro e he heB
    exact havoid e (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨he,heB.trans hBA⟩))) heB
  have hBsix : ∀ e ∈ sixes (n^40), ¬e ⊆ B := by
    intro e he heB
    exact havoid e (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨he,heB.trans hBA⟩))) heB
  have hBsum : ∀ e ∈ sumSix (n^40), ¬e ⊆ B := by
    intro e he heB
    exact havoid e (mem_union_right _ (mem_filter.mpr ⟨he,heB.trans hBA⟩)) heB
  have hBAP := apFree_of_avoids (hBA.trans hA) hBap
  refine ⟨B,hBA.trans hA,?_,hBAP,capacity_of_avoids (hBA.trans hA) hBAP hBsix,
    IntegerSumCapacity.unordered_capacity (by decide) hBAP
      (IntegerSumCapacity.capacity_of_avoids (hBA.trans hA) hBsum),
    fun S hSB hS => hnolarge S (hSB.trans hBA) hS⟩
  have hc : (A.card:ℝ) ≤ B.card+H₃.card+H₆.card+HS.card := by
    have hh := card_union_le H₃ H₆
    have hs := card_union_le (H₃ ∪ H₆) HS
    have hhh : A.card ≤ B.card+H₃.card+H₆.card+HS.card := by omega
    exact_mod_cast hhh
  have hpnon := mul_nonneg (pow_nonneg hn0.le 40) (penalty_nonneg n A)
  dsimp [reward] at hrew
  dsimp [H₃,H₆,HS] at hc
  linarith only [hc,hpnon,hrew]

/-- A convenient integral form of the fixed-power gap. -/
theorem finite_power_gap {n : ℕ} (hn : 1000 ≤ n) (hlog : 5 ≤ Real.log (n:ℝ)) :
    ∃ B ⊆ Icc 1 (n^40), n^16 ≤ 8*B.card ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ 2) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ 2) ∧
      (B.maxSidonSubsetCard)^16 ≤ 8^15*B.card^15 := by
  obtain ⟨B,hB,hcard,hAP,hcap,hsum,hSid⟩ := finite_obstruction hn hlog
  have hc : n^16 ≤ 8*B.card := by
    have hh : (n:ℝ)^16 ≤ 8*(B.card:ℝ) := by linarith only [hcard]
    exact_mod_cast hh
  have hmax : B.maxSidonSubsetCard ≤ n^15 := by
    apply Finset.sup_le
    intro S hS
    obtain ⟨hSsub,hSidon⟩ := mem_filter.mp hS
    exact (hSid S (mem_powerset.mp hSsub) hSidon).le
  refine ⟨B,hB,hc,hAP,hcap,hsum,?_⟩
  calc
    _ ≤ (n^15)^16 := Nat.pow_le_pow_left hmax _
    _ = (n^16)^15 := by ring
    _ ≤ (8*B.card)^15 := Nat.pow_le_pow_left hc _
    _ = _ := by rw [mul_pow]

/-- These counterexamples occur at unbounded polynomial scales. -/
theorem eventual_obstruction : ∀ᶠ n : ℕ in atTop,
    ∃ B ⊆ Icc 1 (n^40), n^16 ≤ 8*B.card ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ 2) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ 2) ∧
      (B.maxSidonSubsetCard)^16 ≤ 8^15*B.card^15 := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 5
  filter_upwards [eventually_ge_atTop 1000,hlog] with n hn hl
  exact finite_power_gap hn hl

#print axioms finite_power_gap
#print axioms eventual_obstruction
#print axioms reward_scales
#print axioms expected_reward
#print axioms finite_obstruction
end
end Erdos773.JointCapacityObstruction
