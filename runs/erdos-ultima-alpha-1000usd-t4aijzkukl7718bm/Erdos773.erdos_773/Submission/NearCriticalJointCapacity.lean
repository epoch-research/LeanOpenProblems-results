import Submission.NearCriticalCapacityObstruction
import Submission.IntegerSumCapacity

/-!
Ordinary integer carriers with both bounded sum and bounded difference
multiplicities at near-square-root ambient density. This file does not
assert that the carriers consist of squares, and does not settle Erdos 773.
-/
namespace Erdos773.NearCriticalJointCapacity
open Finset Filter IntegerDifferenceCapacity
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Supports

def obstructions (m g : ℕ) : Finset (Finset ℕ) :=
  IntegerDifferenceCapacityGeneral.obstructions m g ∪ IntegerSumCapacity.obstructions m g

lemma obstructions_card (m g : ℕ) : (obstructions m g).card ≤ 3*m^(g+2) := by
  have hd := IntegerDifferenceCapacityGeneral.obstructions_card m g
  have hs := IntegerSumCapacity.obstructions_card m g
  have hu := card_union_le (IntegerDifferenceCapacityGeneral.obstructions m g)
    (IntegerSumCapacity.obstructions m g)
  dsimp [obstructions]
  omega

lemma obstructions_size {m g : ℕ} {e : Finset ℕ}
    (he : e ∈ obstructions m g) : e.card=2*(g+1) := by
  rcases mem_union.mp he with he | he
  · exact IntegerDifferenceCapacityGeneral.obstructions_size he
  · exact IntegerSumCapacity.obstructions_size he

lemma obstructions_subset {m g : ℕ} {e : Finset ℕ}
    (he : e ∈ obstructions m g) : e ⊆ Icc 1 m := by
  rcases mem_union.mp he with he | he
  · exact IntegerDifferenceCapacityGeneral.obstructions_subset he
  · exact IntegerSumCapacity.obstructions_subset he

lemma capacity_of_avoids {m g : ℕ} {B : Finset ℕ} (hg : 1 ≤ g)
    (hB : B ⊆ Icc 1 m) (hAP : ThreeAPFree (B:Set ℕ))
    (havoid : ∀ e ∈ obstructions m g, ¬ e ⊆ B) :
    (∀ D, 0<D → (reps B D).card ≤ g) ∧
    (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ g) := by
  constructor
  · exact IntegerDifferenceCapacityGeneral.capacity_of_avoids hB hAP
      (fun e he => havoid e (mem_union_left _ he))
  · exact IntegerSumCapacity.unordered_capacity hg hAP
      (IntegerSumCapacity.capacity_of_avoids hB
        (fun e he => havoid e (mem_union_right _ he)))

end Supports

namespace Scales
open DenseSidonSeedWitnesses DenseCapacityScales
lemma reward_scales {n R g : ℕ} (hn : 1000 ≤ n) (hR : 0<R) (hg : 1≤g)
    (he : (R:ℝ)^50=(n:ℝ)^(2*g)) :
    (R:ℝ)^50/(8*n) ≤ density n R*(R:ℝ)^100-
      (density n R)^3*(R:ℝ)^200-
      3*((density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2))-1 := by
  have hnR : (1000:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  have hR0 : (0:ℝ)<R := by exact_mod_cast hR
  let u : ℝ := (R:ℝ)^50
  have hu : 0<u := by dsimp [u]; positivity
  have hu2 : (R:ℝ)^100=u^2 := by dsimp [u]; ring
  have hu4 : (R:ℝ)^200=u^4 := by dsimp [u]; ring
  have h₁ : density n R*(R:ℝ)^100=u/(4*n) := by
    unfold density
    rw [hu2]
    change 1/(4*u*n)*u^2=u/(4*n)
    field_simp
  have h₂ : (density n R)^3*(R:ℝ)^200=u/(64*(n:ℝ)^3) := by
    unfold density
    rw [hu4]
    change (1/(4*u*n))^3*u^4=u/(64*(n:ℝ)^3)
    field_simp
    ring
  have h₃ : (density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2) =
      u/((4:ℝ)^(2*(g+1))*(n:ℝ)^2) := by
    unfold density
    rw [hu2]
    exact capacity_cost (n:ℝ) u hn0 hu g he
  have hpow : (n:ℝ)^2 ≤ u := by
    rw [show u=(n:ℝ)^(2*g) from he]
    exact pow_le_pow_right₀ (by linarith only [hnR]) (by omega)
  have hn1 : (1:ℝ) ≤ n := by linarith only [hnR]
  have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := one_le_pow₀ hn1
  have h4 : (16:ℝ) ≤ (4:ℝ)^(2*(g+1)) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (show 2≤2*(g+1) by omega)
    norm_num at hh ⊢
    exact hh
  have hcost₂ : u/(64*(n:ℝ)^3) ≤ (u/(n:ℝ))/64 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hu.le (by positivity)
    have hh := mul_le_mul_of_nonneg_left hn2 hn0.le
    nlinarith only [hh]
  have hcost₃ : u/((4:ℝ)^(2*(g+1))*(n:ℝ)^2) ≤ (u/(n:ℝ))/64 := by
    have hden : (64:ℝ)*n ≤ (4:ℝ)^(2*(g+1))*(n:ℝ)^2 := by
      have hh := mul_le_mul_of_nonneg_right h4 (sq_nonneg (n:ℝ))
      have hn4 := mul_nonneg (show (0:ℝ) ≤ (n:ℝ)-4 by linarith only [hnR]) hn0.le
      nlinarith only [hh,hn4]
    rw [div_div]
    exact div_le_div_of_nonneg_left hu.le (by positivity) (by nlinarith only [hden])
  have hmass : (16:ℝ) ≤ u/(n:ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    have hh := mul_nonneg (show (0:ℝ) ≤ (n:ℝ)-16 by linarith only [hnR]) hn0.le
    nlinarith only [hh,hpow]
  rw [h₁,h₂,h₃]
  change u/(8*n) ≤ _
  have hm1 : u/(4*n)=(u/n)/4 := by ring
  have hm2 : u/(8*n)=(u/n)/8 := by ring
  rw [hm1,hm2]
  linarith only [hcost₂,hcost₃,hmass]


end Scales

namespace Selection
open DenseSidonSeedWitnesses BernoulliCarrier Supports
def reward (n R g : ℕ) (B : Finset ℕ) : ℝ :=
  B.card-((aps (R^100)).filter (· ⊆ B)).card-((obstructions (R^100) g).filter (· ⊆ B)).card-(R:ℝ)^100*penalty n R B

lemma expected_reward_of_scale {n R g : ℕ} (hn : 1000 ≤ n) (hR : 1000 ≤ R)
    (hlog : 5 ≤ Real.log (n:ℝ)) (M : ℝ)
    (hscale : M ≤ density n R*(R:ℝ)^100-(density n R)^3*(R:ℝ)^200-
      3*((density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2))-1) :
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
  have hSc : ((obstructions (R^100) g).card:ℝ) ≤ 3*((R:ℝ)^100)^(g+2) := by
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
theorem finite_obstruction_of_reward {n R g : ℕ} (hg : 1 ≤ g) (hn : 1000 ≤ n) (hR : 1000 ≤ R)
    (hlog : 5 ≤ Real.log (n:ℝ)) (M : ℝ) (hM : 0<M)
    (hscale : M ≤ density n R*(R:ℝ)^100-(density n R)^3*(R:ℝ)^200-
      3*((density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2))-1) :
    ∃ B ⊆ Icc 1 (R^100), M ≤ (B.card:ℝ) ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ g) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ g) ∧
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
  refine ⟨B,hBA.trans hA,?_,hBAP,(Supports.capacity_of_avoids hg (hBA.trans hA) hBAP hBsix).1,
    (Supports.capacity_of_avoids hg (hBA.trans hA) hBAP hBsix).2,
    fun S hSB hS => hnolarge S (hSB.trans hBA) hS⟩
  have hc : (A.card:ℝ) ≤ B.card+H₃.card+H₆.card := by
    have hh := card_union_le H₃ H₆
    have hhh : A.card ≤ B.card+H₃.card+H₆.card := by omega
    exact_mod_cast hhh
  have hpnon := mul_nonneg (pow_nonneg hR0.le 100) (penalty_nonneg n R A)
  dsimp [reward] at hrew
  dsimp [H₃,H₆] at hc
  linarith only [hc,hpnon,hrew]

 theorem finite_obstruction {n R g : ℕ} (hn : 1000 ≤ n) (hR : 1000 ≤ R)
    (hg : 1 ≤ g) (hlog : 5 ≤ Real.log (n:ℝ))
    (he : (R:ℝ)^50=(n:ℝ)^(2*g)) :
    ∃ B ⊆ Icc 1 (R^100), (R:ℝ)^50/(8*n) ≤ (B.card:ℝ) ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ g) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ g) ∧
      (∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<R^40) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hR0 : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  exact finite_obstruction_of_reward hg hn hR hlog _ (by positivity)
    (Scales.reward_scales hn (by omega) hg he)

end Selection
/-- The capacity is fixed as n grows. By taking k large, the carrier exponent
approaches one half of the ambient exponent, while the Sidon exponent stays
at two fifths of the ambient exponent. -/
theorem polynomial_obstruction {n k : ℕ} (hn : 1000 ≤ n) (hk : 1≤k)
    (hlog : 5 ≤ Real.log (n:ℝ)) :
    ∃ B ⊆ Icc 1 (n^(100*k)), n^(50*k-1) ≤ 8*B.card ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ 25*k) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ 25*k) ∧
      (∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<n^(40*k)) := by
  have hnk : n ≤ n^k := by
    simpa using Nat.pow_le_pow_right (by omega : 1≤n) hk
  have he : ((n^k:ℕ):ℝ)^50=(n:ℝ)^(2*(25*k)) := by
    push_cast
    rw [← pow_mul]
    congr 1
    omega
  obtain ⟨B,hB,hcard,hAP,hcap,hSum,hSid⟩ := Selection.finite_obstruction
    hn (hn.trans hnk) (show 1≤25*k by omega) hlog he
  have hB' : B ⊆ Icc 1 (n^(100*k)) := by
    simpa only [← pow_mul, Nat.mul_comm k 100] using hB
  have hS' : ∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<n^(40*k) := by
    simpa only [← pow_mul, Nat.mul_comm k 40] using hSid
  refine ⟨B,hB',?_,hAP,hcap,hSum,hS'⟩
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hcR := (div_le_iff₀ (show (0:ℝ)<8*n by positivity)).mp hcard
  have hc : (n^k)^50 ≤ 8*n*B.card := by
    exact_mod_cast (show ((n^k:ℕ):ℝ)^50 ≤ 8*n*(B.card:ℝ) by nlinarith only [hcR])
  have heN : (n^k)^50=n^(50*k-1)*n := by
    rw [← pow_mul,show k*50=(50*k-1)+1 by omega,pow_succ]
  rw [heN] at hc
  apply Nat.le_of_mul_le_mul_right (c := n) _ (by omega)
  nlinarith only [hc]

/-- A uniform fixed-power loss relative to carrier size at each displayed
polynomial scale. This is an ordinary-integer, not a square-value, example. -/
theorem polynomial_power_gap {n k : ℕ} (hn : 1000 ≤ n) (hk : 1≤k)
    (hlog : 5 ≤ Real.log (n:ℝ)) :
    ∃ B ⊆ Icc 1 (n^(100*k)), n^(50*k-1) ≤ 8*B.card ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ 25*k) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ 25*k) ∧
      B.maxSidonSubsetCard ≤ n^(40*k) ∧
      B.maxSidonSubsetCard^(50*k-1) ≤ 8^(40*k)*B.card^(40*k) := by
  obtain ⟨B,hB,hcard,hAP,hcap,hSum,hSid⟩ := polynomial_obstruction hn hk hlog
  have hmax : B.maxSidonSubsetCard ≤ n^(40*k) := by
    apply Finset.sup_le
    intro S hS
    obtain ⟨hSsub,hSidon⟩ := mem_filter.mp hS
    exact (hSid S (mem_powerset.mp hSsub) hSidon).le
  refine ⟨B,hB,hcard,hAP,hcap,hSum,hmax,?_⟩
  calc
    _ ≤ (n^(40*k))^(50*k-1) := Nat.pow_le_pow_left hmax _
    _ = (n^(50*k-1))^(40*k) := by rw [← pow_mul,← pow_mul, Nat.mul_comm (40*k)]
    _ ≤ (8*B.card)^(40*k) := Nat.pow_le_pow_left hcard _
    _ = _ := by rw [mul_pow]

/-- The examples exist at every sufficiently large parameter n. -/
theorem eventual_polynomial_obstruction (k : ℕ) (hk : 1≤k) :
    ∀ᶠ n : ℕ in atTop,
    ∃ B ⊆ Icc 1 (n^(100*k)), n^(50*k-1) ≤ 8*B.card ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ 25*k) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ 25*k) ∧
      B.maxSidonSubsetCard ≤ n^(40*k) ∧
      B.maxSidonSubsetCard^(50*k-1) ≤ 8^(40*k)*B.card^(40*k) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 5
  filter_upwards [eventually_ge_atTop 1000,hlog] with n hn hl
  exact polynomial_power_gap hn hk hl

lemma large_carrier {n k m : ℕ} (hn : 8≤n) (hk : 1≤k)
    (hc : n^(50*k-1) ≤ 8*m) : n^(50*k-2) ≤ m := by
  have he : n^(50*k-1)=n^(50*k-2)*n := by
    rw [show 50*k-1=(50*k-2)+1 by omega,pow_succ]
  rw [he] at hc
  apply Nat.le_of_mul_le_mul_right (c := 8) _ (by omega)
  simpa only [Nat.mul_comm m 8] using (Nat.mul_le_mul_left (n^(50*k-2)) hn).trans hc

lemma near_linear_scale {n k : ℕ} (hn : 1≤n) (hk : 1≤k) (ε : ℝ)
    (he : 2 ≤ (50:ℝ)*k*ε) :
    ((n^(50*k):ℕ):ℝ)^(1-ε) ≤ ((n^(50*k-2):ℕ):ℝ) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  push_cast
  rw [← Real.rpow_natCast (n:ℝ) (50*k),← Real.rpow_mul hn0.le,
    ← Real.rpow_natCast (n:ℝ) (50*k-2)]
  apply Real.rpow_le_rpow_of_exponent_le hnR
  rw [Nat.cast_sub (by omega : 2≤50*k)]
  push_cast
  nlinarith only [he]

/-- For every density loss ε, a FIXED capacity g admits ordinary integer
carriers in [1,N²] of size at least N^(1-ε), at unbounded heights N, whose
Sidon maximum obeys M^5 ≤ N^4. The square-specific hypothesis is absent. -/
theorem near_critical_obstruction (ε : ℝ) (hε : 0<ε) :
    ∃ g : ℕ, 0<g ∧ ∀ᶠ n : ℕ in atTop,
      ∃ N ≥ n, ∃ B ⊆ Icc 1 (N^2), (N:ℝ)^(1-ε) ≤ B.card ∧
        ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ g) ∧
        (∀ S, (IntegerSumCapacity.unorderedSumReps B S).card ≤ g) ∧
        B.maxSidonSubsetCard^5 ≤ N^4 := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (1:ℝ) (2/(50*ε)))
  have hk1 : (1:ℝ)<k := (le_max_left _ _).trans_lt hk
  have hkN : 1≤k := by exact_mod_cast hk1.le
  have hkε : 2 ≤ (50:ℝ)*k*ε := by
    have hh := (div_lt_iff₀ (show (0:ℝ)<50*ε by positivity)).mp ((le_max_right _ _).trans_lt hk)
    nlinarith only [hh]
  refine ⟨25*k,by omega,?_⟩
  filter_upwards [eventual_polynomial_obstruction k hkN,eventually_ge_atTop 1000]
    with n hex hn
  obtain ⟨B,hB,hcard,hAP,hcap,hSum,hmax,_⟩ := hex
  let N := n^(50*k)
  have hNn : n≤N := by
    simpa [N] using Nat.pow_le_pow_right (by omega : 1≤n) (show 1≤50*k by omega)
  have hB' : B ⊆ Icc 1 (N^2) := by
    simpa only [N,← pow_mul,show 50*k*2=100*k by omega] using hB
  refine ⟨N,hNn,B,hB',?_,hAP,hcap,hSum,?_⟩
  · exact (near_linear_scale (by omega) hkN ε hkε).trans
      (by exact_mod_cast large_carrier (by omega : 8≤n) hkN hcard)
  · apply (Nat.pow_le_pow_left hmax 5).trans_eq
    dsimp [N]
    rw [← pow_mul,← pow_mul]
    congr 1
    omega


#print axioms Supports.capacity_of_avoids
#print axioms Scales.reward_scales
#print axioms Selection.finite_obstruction
#print axioms polynomial_obstruction
#print axioms near_critical_obstruction
end
end Erdos773.NearCriticalJointCapacity
