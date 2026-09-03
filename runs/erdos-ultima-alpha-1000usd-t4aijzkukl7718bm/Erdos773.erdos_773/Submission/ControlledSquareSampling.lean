import Submission.FixedCardinalitySampling
import Submission.SquareProgressionSupports
import Submission.SquareSupportCounting
import Submission.AverageAPBound

/-!
Prescribed-size sampling followed by progression deletion, while retaining
an asymptotically sharp bound for four-root collisions. The selected square
values are progression-free, not necessarily Sidon.
-/
noncomputable section
namespace Erdos773.ControlledSquareSampling
open Finset Filter SquareProgressionSupports SquareCollisionCodegrees
set_option maxHeartbeats 1000000

lemma edges_restrict {A B : Finset ℕ} (hBA : B ⊆ A) :
    edges B = (edges A).filter (fun e => e ⊆ B) := by
  classical
  ext e
  simp only [edges,mem_filter,mem_powerset]
  constructor
  · rintro ⟨heB,h4,hs⟩
    exact ⟨⟨heB.trans hBA,h4,hs⟩,heB⟩
  · rintro ⟨⟨heA,h4,hs⟩,heB⟩
    exact ⟨heB,h4,hs⟩

/-- Simultaneous control of progression deletion and retained four-edges. -/
theorem finite_selection (A : Finset ℕ) (k : ℕ) (hk : k ≤ A.card)
    (T U : ℝ) (hT : 0 < T) (hU : 0 < U)
    (hcost : ((k:ℝ)/A.card)^3*(progressions A).card/T+
      ((k:ℝ)/A.card)^4*(edges A).card/U < 1) :
    ∃ B ⊆ A, ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (k:ℝ)-T ≤ B.card ∧ B.card ≤ k ∧ ((edges B).card : ℝ) ≤ U := by
  classical
  obtain ⟨C,hCA,hCk,h3,h4⟩ := FixedCardinalitySampling.simultaneous_selection A
    (progressions A) (edges A)
    (fun e he => (mem_progressions.mp he).1)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    3 4 (fun e he => (mem_progressions.mp he).2.1)
    (fun e he => (mem_filter.mp he).2.1) T U hT hU k hk hcost
  rw [← progressions_restrict hCA] at h3
  rw [← edges_restrict hCA] at h4
  obtain ⟨B,hBC,hcard,havoid⟩ := delete_forbidden_edges C (progressions C)
    (fun e he => card_pos.mp (by rw [(mem_progressions.mp he).2.1]; omega))
  have hcR : (C.card : ℝ) ≤ B.card+(progressions C).card := by exact_mod_cast hcard
  rw [hCk] at hcR
  have hm : (edges B).card ≤ (edges C).card := card_le_card (edges_mono hBC)
  refine ⟨B,hBC.trans hCA,ap_free_of_avoids hBC havoid,?_,?_,?_⟩
  · linarith
  · exact (card_le_card hBC).trans_eq hCk
  · have hmR : ((edges B).card : ℝ) ≤ (edges C).card := by exact_mod_cast hm
    exact hmR.trans h4.le

lemma progression_log_bound (N : ℕ) (hN : 0 < N) (hL : 2 ≤ Real.log (N:ℝ)) :
    ((progressions (Icc 1 N)).card : ℝ) ≤ 24*(N:ℝ)*Real.log N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hc : ((progressions (Icc 1 N)).card : ℝ) ≤ (squareAPs N).card := by
    exact_mod_cast progression_card_bound N
  have hb := AverageAP.squareAPs_log_bound N
  have hl4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  norm_num at hl4
  rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hN0.ne'] at hb
  have hh : 1+Real.log 4+Real.log N ≤ 3*Real.log N := by linarith
  have hmul := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ 8*N by positivity)
  nlinarith only [hc,hb,hmul]

/-- Quantitative sampling at the density 1/log N, with explicit sufficient
conditions for the two normalized costs to have sum below one. -/
theorem finite_log_sampling (N : ℕ) (δ : ℝ) (hN : 0 < N) (hδ : 0 < δ)
    (hL : 2 ≤ Real.log (N:ℝ))
    (hlarge : 192*(41/500+δ)/δ^2 ≤ Real.log (N:ℝ))
    (hsize : 2/δ ≤ (N:ℝ)/Real.log N)
    (hE : ((edges (Icc 1 N)).card : ℝ) ≤ (41/500+δ/2)*(N:ℝ)^2*Real.log N) :
    ∃ B ⊆ Icc 1 N,
      ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (1-δ)*(N:ℝ)/Real.log N ≤ B.card ∧
      (B.card : ℝ) ≤ (N:ℝ)/Real.log N ∧
      ((edges B).card : ℝ) ≤ (41/500+δ)*(N:ℝ)^2/(Real.log N)^3 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  let L : ℝ := Real.log N
  have hL0 : 0 < L := by dsimp [L]; linarith
  let k : ℕ := ⌊(N:ℝ)/L⌋₊
  let p : ℝ := (k:ℝ)/N
  let T : ℝ := (δ/2)*(N:ℝ)/L
  let U : ℝ := (41/500+δ)*(N:ℝ)^2/L^3
  have hT : 0 < T := by dsimp [T]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hfloor : (k:ℝ) ≤ (N:ℝ)/L := Nat.floor_le (by positivity)
  have hfloor' : (N:ℝ)/L < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hquot : (N:ℝ)/L ≤ N := (div_le_self hN0.le (by change 1 ≤ Real.log N; linarith))
  have hk : k ≤ (Icc 1 N).card := by
    simp only [Nat.card_Icc,Nat.add_sub_cancel]
    exact Nat.floor_le_of_le hquot
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hpup : p ≤ 1/L := by
    dsimp [p]
    apply (div_le_iff₀ hN0).mpr
    convert hfloor using 1
    ring
  have hp3 := pow_le_pow_left₀ hp hpup 3
  have hp4 := pow_le_pow_left₀ hp hpup 4
  have hAP := progression_log_bound N hN hL
  change ((progressions (Icc 1 N)).card : ℝ) ≤ 24*(N:ℝ)*L at hAP
  change ((edges (Icc 1 N)).card : ℝ) ≤ (41/500+δ/2)*(N:ℝ)^2*L at hE
  have h3 : p^3*(progressions (Icc 1 N)).card/T ≤ 48/(δ*L) := by
    calc
      _ ≤ (1/L)^3*(24*(N:ℝ)*L)/T := by
        apply div_le_div_of_nonneg_right _ hT.le
        exact mul_le_mul hp3 hAP (Nat.cast_nonneg _) (by positivity)
      _ = _ := by dsimp [T]; field_simp; ring
  have h4 : p^4*(edges (Icc 1 N)).card/U ≤ (41/500+δ/2)/(41/500+δ) := by
    calc
      _ ≤ (1/L)^4*((41/500+δ/2)*(N:ℝ)^2*L)/U := by
        apply div_le_div_of_nonneg_right _ hU.le
        exact mul_le_mul hp4 hE (Nat.cast_nonneg _) (by positivity)
      _ = _ := by dsimp [U]; field_simp
  have hD : (0:ℝ) < 41/500+δ := by linarith
  have hAPsmall : 48/(δ*L) ≤ δ/(4*(41/500+δ)) := by
    apply (div_le_div_iff₀ (by positivity : 0<δ*L) (by positivity : 0<4*(41/500+δ))).mpr
    have hh := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hlarge
    change 192*(41/500+δ) ≤ L*δ^2 at hh
    nlinarith only [hh]
  have hsumsmall : δ/(4*(41/500+δ))+(41/500+δ/2)/(41/500+δ) < 1 := by
    rw [div_mul_eq_div_div,← add_div]
    apply (div_lt_one hD).mpr
    linarith
  have hcost : p^3*(progressions (Icc 1 N)).card/T+
      p^4*(edges (Icc 1 N)).card/U < 1 := by
    linarith only [h3,h4,hAPsmall,hsumsmall]
  have hcost' : ((k:ℝ)/(Icc 1 N).card)^3*(progressions (Icc 1 N)).card/T+
      ((k:ℝ)/(Icc 1 N).card)^4*(edges (Icc 1 N)).card/U < 1 := by
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hcost
  obtain ⟨B,hB,hAPfree,hBc,hBk,hBE⟩ := finite_selection (Icc 1 N) k hk T U hT hU hcost'
  have hT1 : 1 ≤ (δ/2)*(N:ℝ)/L := by
    have hh := (div_le_iff₀ hδ).mp hsize
    change 2 ≤ (N:ℝ)/L*δ at hh
    rw [mul_div_assoc]
    nlinarith only [hh]
  have hlower : (1-δ)*(N:ℝ)/L ≤ B.card := by
    dsimp [T] at hBc
    rw [mul_div_assoc] at hBc hT1 ⊢
    nlinarith only [hBc,hfloor',hT1]
  have hupper : (B.card : ℝ) ≤ (N:ℝ)/L := by
    have hbkR : (B.card : ℝ) ≤ k := by exact_mod_cast hBk
    exact hbkR.trans hfloor
  exact ⟨B,hB,hAPfree,hlower,hupper,hBE⟩

/-- Near-linear progression-free roots with the fourth-order random-density
saving and with an arbitrarily small loss in the proved leading constant. -/
theorem logarithmic_sampling (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∃ B ⊆ Icc 1 N,
      ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (1-δ)*(N:ℝ)/Real.log N ≤ B.card ∧
      (B.card : ℝ) ≤ (N:ℝ)/Real.log N ∧
      ((edges B).card : ℝ) ≤ (41/500+δ)*(N:ℝ)^2/(Real.log N)^3 := by
  have ht : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlo := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (show 0 < δ/2 by positivity)
  filter_upwards [SquareSupportCounting.edges_eventually_bound (δ/2) (by positivity),
    ht.eventually_ge_atTop 2,ht.eventually_ge_atTop (192*(41/500+δ)/δ^2),
    eventually_ge_atTop 1,hlo] with N hE hL hlarge hN hsmall
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N:ℝ) := by linarith
  have hsmall' : Real.log (N:ℝ) ≤ (δ/2)*(N:ℝ) := by
    simpa only [Function.comp_apply,id_eq,Real.norm_eq_abs,
      abs_of_nonneg hL0.le,abs_of_nonneg hN0.le] using hsmall
  apply finite_log_sampling N δ hN hδ hL hlarge _ hE
  apply (le_div_iff₀ hL0).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hδ).mpr
  nlinarith only [hsmall']

/-- Normalize the fourth-order count by the actual retained cardinality.
All constants in this inequality are rational and checked explicitly. -/
lemma normalized_count (X L m E : ℝ) (hX : 0 < X) (hL : 0 < L) (_hm : 0 ≤ m)
    (hsize : (1999/2000:ℝ)*X/L ≤ m) (hcount : E ≤ (33/400:ℝ)*X^2/L^3) :
    E*X^2 ≤ (83/1000:ℝ)*m^4*L := by
  have hsize' := (div_le_iff₀ hL).mp hsize
  have hpow := pow_le_pow_left₀ (show 0 ≤ (1999/2000:ℝ)*X by positivity) hsize' 4
  have hpow' := mul_le_mul_of_nonneg_left hpow (show (0:ℝ) ≤ 83/1000 by norm_num)
  have hcount' := (le_div_iff₀ (pow_pos hL 3)).mp hcount
  have hcount'' := mul_le_mul_of_nonneg_right hcount' (sq_nonneg X)
  have hc : (33/400:ℝ) ≤ (83/1000)*(1999/2000)^4 := by norm_num
  have hc' := mul_le_mul_of_nonneg_right hc (pow_nonneg hX.le 4)
  apply (mul_le_mul_iff_left₀ (pow_pos hL 3)).mp
  nlinarith only [hpow',hcount'',hc']

/-- A progression-free carrier with a sharp normalized edge bound and the
uniform subpower pair-codegree bound. This still permits four-root edges. -/
theorem sharp_carrier (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ N : ℕ in atTop, ∃ B ⊆ Icc 1 N,
      ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (1999/2000:ℝ)*(N:ℝ)/Real.log N ≤ B.card ∧
      (B.card : ℝ) ≤ (N:ℝ)/Real.log N ∧
      ((edges B).card : ℝ)*(N:ℝ)^2 ≤ (83/1000:ℝ)*(B.card:ℝ)^4*Real.log N ∧
      ∀ a ∈ B, ∀ b ∈ B, a ≠ b →
        ((pairEdges B a b).card : ℝ) ≤ (N:ℝ)^γ := by
  have ht : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [logarithmic_sampling (1/2000) (by norm_num),
    eventually_pair_codegree_bound γ hγ,ht.eventually_ge_atTop 1,eventually_ge_atTop 1]
    with N hsample hcodeg hlog hN
  obtain ⟨B,hBA,hAP,hsize,hupper,hE⟩ := hsample
  norm_num at hsize hE
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hlog0 : 0 < Real.log (N:ℝ) := by linarith
  refine ⟨B,hBA,hAP,hsize,hupper,?_,?_⟩
  · exact normalized_count (N:ℝ) (Real.log N) B.card (edges B).card hN0 hlog0
      (Nat.cast_nonneg _) hsize hE
  · intro a ha b hb hab
    have hmono : ((pairEdges B a b).card : ℝ) ≤ (pairEdges (Icc 1 N) a b).card := by
      exact_mod_cast card_le_card (pairEdges_mono hBA a b)
    exact hmono.trans (hcodeg a (hBA ha) b (hBA hb) hab)

#print axioms finite_selection
#print axioms progression_log_bound
#print axioms finite_log_sampling
#print axioms logarithmic_sampling
#print axioms normalized_count
#print axioms sharp_carrier
end Erdos773.ControlledSquareSampling
