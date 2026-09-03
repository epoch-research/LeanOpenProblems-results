import Submission.No9BlockRounding
import Submission.No9PrefixSoundness

/-! Uniform loss and moment bounds within a rounded prime block. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7KilledSieve Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

noncomputable def blockOperator (b : BlockControl) : Module.End ℚ (Fin nodes → ℚ) :=
  blockAlpha b • (1:Module.End ℚ (Fin nodes → ℚ))+realOperator b.lo b.R 5 4

def blockCubicFactor (b : BlockControl) : ℚ :=
  1+(5/4)*(7*(b.lo:ℚ)^2-2*b.lo+1)/(b.lo-1)^3

lemma blockOperator_nonneg (b : BlockControl) (hb : BlockAnalyticBounds b) (h : ℕ → ℕ) (j : ℕ) :
    0 ≤ (blockOperator b^j) (realValues h) := by
  apply monotone_operator_pow_nonneg _ _ _ (realValues_nonneg h)
  exact scalar_add_operator_monotone _ (realOperator_monotone _ _ _ _ (by have := hb.lo_two; omega) hb.R_le)
    _ (blockAlpha_nonneg b hb.hi_two)

lemma rounded_block_prefix (b : BlockControl) (hb : BlockAnalyticBounds b)
    (h y1 y2 y3 : ℕ → ℕ) (hh0 : ∀ j,j < nodes → h j ≤ h 0)
    (hy1 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 h j=y1 j)
    (hy2 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y1 j=y2 j)
    (hy3 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y2 j=y3 j)
    (j : ℕ) (hj : j ≤ b.count) :
    (blockOperator b^j) (realValues h) ≤ realValues (blockUniform b h y1 y2 y3) := by
  have hT := realOperator_monotone b.lo b.R 5 4 (by have := hb.lo_two; omega) hb.R_le
  exact (scalar_add_operator_prefix_bound _ hT (blockAlpha b) (blockAlpha_nonneg b hb.hi_two)
    (blockAlpha_le_one b) (realValues h) (realValues_nonneg h) hj).trans
      (rounded_blockUniform b hb h y1 y2 y3 hh0 hy1 hy2 hy3)

lemma rounded_block_loss_chord (b : BlockControl) (hv : LossGeometry 5 4 (b.lo-1) b.lossIndex)
    (h y1 y2 y3 : ℕ → ℕ) :
    (5/4:ℚ)*(1/((b.lo:ℚ)-1))*gridChord realGrid (gridIndex b.lossIndex) (gridIndex (b.lossIndex+1))
      (((b.lo:ℚ)-1)/5) (realValues (blockUniform b h y1 y2 y3)) ≤ (blockLoss b h y1 y2 y3:ℚ)/scale := by
  have hq : 1 ≤ b.lo := by have := hv.q_pos; omega
  have hh := rounded_loss_chord 5 4 (b.lo-1) b.lossIndex hv (blockUniform b h y1 y2 y3)
  simpa only [blockLoss,Nat.cast_sub hq,Nat.cast_one,Nat.cast_ofNat,Nat.reduceSub,mul_one,
    show (5:ℚ)-4=1 by norm_num] using hh

lemma blockCubicFactor_nonneg (b : BlockControl) (hb : 2 ≤ b.lo) : 0 ≤ blockCubicFactor b := by
  have hp : (2:ℚ) ≤ b.lo := by exact_mod_cast hb
  have hden : (0:ℚ) < (b.lo:ℚ)-1 := by linarith
  have hnum : (0:ℚ) ≤ 7*(b.lo:ℚ)^2-2*b.lo+1 := by nlinarith
  dsimp [blockCubicFactor]
  positivity

lemma rounded_block_cubic (b : BlockControl) (hb : 2 ≤ b.lo) (C : ℕ) :
    (blockCubicFactor b)^b.count*((C:ℚ)/scale) ≤
    (ceilDiv (C*(4*(b.lo-1)^3+5*(7*b.lo*b.lo-2*b.lo+1))^b.count)
      ((4*(b.lo-1)^3)^b.count):ℚ)/scale := by
  have hp : (2:ℚ) ≤ b.lo := by exact_mod_cast hb
  have hden : (b.lo:ℚ)-1≠0 := by linarith
  have hq : 0 < b.lo-1 := by omega
  have hsub : 2*b.lo ≤ 7*b.lo*b.lo := by nlinarith
  have hratio : blockCubicFactor b=
      ((4*(b.lo-1)^3+5*(7*b.lo*b.lo-2*b.lo+1):ℕ):ℚ)/(4*(b.lo-1)^3:ℕ) := by
    dsimp [blockCubicFactor]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hsub,
      Nat.cast_sub (by omega : 1 ≤ b.lo),Nat.cast_one,Nat.cast_ofNat]
    field_simp
  rw [hratio]
  have hh := div_le_div_of_nonneg_right (ceilDiv_bound
    (C*(4*(b.lo-1)^3+5*(7*b.lo*b.lo-2*b.lo+1))^b.count)
    ((4*(b.lo-1)^3)^b.count) (by positivity)) scale_pos.le
  simp only [Nat.cast_mul,Nat.cast_pow] at hh
  convert hh using 1
  simp only [Nat.cast_mul,Nat.cast_pow,div_pow]
  ring

section Grid
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

lemma completeGridBound_block_resample (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (B : Finset (∀ i,A i))
    (H : Fin nodes → ℚ) (hH : 0 ≤ H) (hh : CompleteGridBound κ A E c q t μ realGrid H)
    (b : BlockControl) (hb : BlockAnalyticBounds b) (p : ℕ) (hp0 : b.lo ≤ p) (hp1 : p ≤ b.hi)
    (hci : c ⟨t,ht⟩=5/4) (hqi : q ⟨t,ht⟩=powerTail p (c ⟨t,ht⟩) (E ⟨t,ht⟩))
    (hE : b.R ≤ E ⟨t,ht⟩) :
    CompleteGridBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩)) realGrid (blockOperator b H) := by
  have hpQ : (2:ℚ) ≤ p := by exact_mod_cast hb.lo_two.trans hp0
  have hph : (p:ℚ) ≤ b.hi := by exact_mod_cast hp1
  have hc : 1 ≤ c ⟨t,ht⟩ := by rw [hci]; norm_num
  have hcp : c ⟨t,ht⟩ ≤ p := by rw [hci]; linarith
  have hα : 1-c ⟨t,ht⟩/(p:ℚ) ≤ blockAlpha b := by
    rw [hci]
    dsimp [blockAlpha]
    have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℚ) ≤ 5/4)
      (by linarith : (0:ℚ) < p) hph
    linarith
  have hr := completeGridBound_resample_majorant κ A E c q t ht μ hμ realGrid H
    (fun j => Nat.cast_nonneg _) hH hh gridZero (by change (grid 0:ℚ)=0; exact_mod_cast grid_zero)
    cellLo cellHi b.lo p (b.R-1) hb.lo_two hp0 (by have := hb.R_pos; omega)
    (grid_geometry _ (by have := hb.R_le; omega)) hqi hc hcp (blockAlpha b) hα B
  simpa only [hci,blockOperator,realOperator,LinearMap.add_apply,LinearMap.smul_apply,Pi.smul_apply,
    smul_eq_mul,Module.End.one_apply,Nat.cast_ofNat] using hr

lemma completeTestBound_residual_antitone (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (d s r L : ℚ) (hd : 0 ≤ d) (hsr : s ≤ r)
    (hh : CompleteTestBound κ A E c q t μ 1 (fun z => residual d (r*z)) L) :
    CompleteTestBound κ A E c q t μ 1 (fun z => residual d (s*z)) L := by
  intro K e X he hX hM
  apply le_trans _ (hh K e X he hX hM)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (hμ x)
  apply max_le_max le_rfl
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ hd
  apply mul_le_mul_of_nonneg_right hsr
  exact Finset.sum_nonneg (fun k hk => boxIndicator_nonneg A _ _ _)

lemma completeGridBound_rounded_block_loss (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (b : BlockControl) (hb : BlockAnalyticBounds b) (hv : LossGeometry 5 4 (b.lo-1) b.lossIndex)
    (h y1 y2 y3 : ℕ → ℕ) (hh0 : ∀ j,j < nodes → h j ≤ h 0)
    (hy1 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 h j=y1 j)
    (hy2 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y1 j=y2 j)
    (hy3 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y2 j=y3 j)
    (j : ℕ) (hj : j ≤ b.count)
    (hh : CompleteGridBound κ A E c q t μ realGrid ((blockOperator b^j) (realValues h)))
    (p : ℕ) (hp : b.lo ≤ p) :
    CompleteTestBound κ A E c q t μ 1 (fun z => residual (5/4) ((1/(p-1:ℚ))*z))
      ((blockLoss b h y1 y2 y3:ℚ)/scale) := by
  have hU := completeGridBound_mono κ A E c q t μ _ _ _ hh (rounded_block_prefix b hb h y1 y2 y3 hh0 hy1 hy2 hy3 j hj)
  have hgeom := loss_geometry 5 4 (b.lo-1) b.lossIndex hv
  have hcast : ((b.lo-1:ℕ):ℚ)=(b.lo:ℚ)-1 := by
    exact Nat.cast_sub (by have := hb.lo_two; omega)
  simp only [hcast,Nat.cast_ofNat,show (5:ℚ)-4=1 by norm_num,mul_one] at hgeom
  have hchord := completeGridBound_chord κ A E c q t μ hμ _ _ hU _ _ _ hgeom.1 hgeom.2.1 hgeom.2.2
  have hdenpos : (0:ℚ) < (b.lo:ℚ)-1 := by
    have hh : (2:ℚ) ≤ b.lo := by exact_mod_cast hb.lo_two
    linarith
  have hden : (b.lo:ℚ)-1≠0 := ne_of_gt hdenpos
  have hres := completeHingeBound_residual κ A E c q t μ _ _ hchord (5/4) (1/(b.lo-1:ℚ))
    (by norm_num) (by positivity) (by field_simp; ring)
  have hbase := completeTestBound_mono κ A E c q t μ 1 _ hres (rounded_block_loss_chord b hv h y1 y2 y3)
  apply completeTestBound_residual_antitone κ A E c q t μ hμ (5/4) _ _ _ (by norm_num) _ hbase
  have hpQ : (b.lo:ℚ) ≤ p := by exact_mod_cast hp
  have hloQ : (2:ℚ) ≤ b.lo := by exact_mod_cast hb.lo_two
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

lemma completeMomentBound_block_resample (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (B : Finset (∀ i,A i))
    (C : ℚ) (hC : 0 ≤ C) (hh : CompleteMomentBound κ A E c q t μ 3 C)
    (b : BlockControl) (hb : 2 ≤ b.lo) (p : ℕ) (hp0 : b.lo ≤ p)
    (hci : c ⟨t,ht⟩=5/4) (hqi : q ⟨t,ht⟩=powerTail p (c ⟨t,ht⟩) (E ⟨t,ht⟩)) :
    CompleteMomentBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩)) 3 (blockCubicFactor b*C) := by
  have hp : 1 < p := by omega
  have hpQ : (2:ℚ) ≤ p := by exact_mod_cast hb.trans hp0
  have hc : 1 ≤ c ⟨t,ht⟩ := by rw [hci]; norm_num
  have hc0 : 0 ≤ c ⟨t,ht⟩ := by linarith
  have hcp : c ⟨t,ht⟩ ≤ p := by rw [hci]; linarith
  have hr := completeMomentBound_resample κ A E c q t ht μ hμ 3 C hh B hc
    (by rw [hqi]; exact powerTail_zero_le_one p hp _ hcp _)
    (by intro g hg; rw [hqi]; exact powerTail_decreasing p hp _ hc0 _ g)
    (by rw [hqi]; exact powerTail_terminal p _ _)
  apply completeMomentBound_mono κ A E c q (t+1) _ 3 hr
  apply mul_le_mul_of_nonneg_right _ hC
  rw [hqi,hci]
  apply (geometric_cubic_factor p _ hp (5/4) (by norm_num)).trans
  have hloQ : (2:ℚ) ≤ b.lo := by exact_mod_cast hb
  have hpp : (b.lo:ℚ) ≤ p := by exact_mod_cast hp0
  have hfrac := cubic_fraction_antitone (b.lo:ℚ) p (by linarith) hpp
  simpa only [blockCubicFactor,mul_div_assoc] using
    add_le_add_right (mul_le_mul_of_nonneg_left hfrac (by norm_num : (0:ℚ) ≤ 5/4)) 1

lemma complete_rounded_block_substep (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (B : Finset (∀ i,A i))
    (b : BlockControl) (hb : BlockAnalyticBounds b) (p : ℕ) (hp0 : b.lo ≤ p) (hp1 : p ≤ b.hi)
    (hci : c ⟨t,ht⟩=5/4) (hqi : q ⟨t,ht⟩=powerTail p (c ⟨t,ht⟩) (E ⟨t,ht⟩))
    (hE : b.R ≤ E ⟨t,ht⟩) (h : ℕ → ℕ) (C : ℚ) (hC : 0 ≤ C) (j : ℕ)
    (hgrid : CompleteGridBound κ A E c q t μ realGrid ((blockOperator b^j) (realValues h)))
    (hmoment : CompleteMomentBound κ A E c q t μ 3 ((blockCubicFactor b)^j*C))
    (L : ℚ) (hLm : L ≤ ∑ x,μ x)
    (hL : (∑ x,μ x*residual (c ⟨t,ht⟩) (coordinateFraction A ⟨t,ht⟩ B x)) ≤ L) :
    let μ' := killedResample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩) L
    CompleteGridBound κ A E c q (t+1) μ' realGrid ((blockOperator b^(j+1)) (realValues h)) ∧
    CompleteMomentBound κ A E c q (t+1) μ' 3 ((blockCubicFactor b)^(j+1)*C) := by
  have hc : 1 ≤ c ⟨t,ht⟩ := by rw [hci]; norm_num
  constructor
  · have hr := completeGridBound_block_resample κ A E c q t ht μ hμ B _
      (blockOperator_nonneg b hb h j) hgrid b hb p hp0 hp1 hci hqi hE
    have hk := completeGridBound_kill κ A E c q (t+1) ⟨t,ht⟩ μ hμ B hc L hLm hL realGrid _ hr
    simpa only [pow_succ',Module.End.mul_apply] using hk
  · have hjC : 0 ≤ blockCubicFactor b^j*C :=
      mul_nonneg (pow_nonneg (blockCubicFactor_nonneg b hb.lo_two) j) hC
    have hr := completeMomentBound_block_resample κ A E c q t ht μ hμ B _ hjC hmoment b hb.lo_two p hp0 hci hqi
    have hk := completeMomentBound_kill κ A E c q (t+1) ⟨t,ht⟩ μ hμ B hc L hLm hL 3 _ hr
    convert hk using 1
    ring

lemma complete_rounded_block_finish (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (b : BlockControl) (hb : BlockAnalyticBounds b) (hcut : b.cut < nodes)
    (s : State) (y1 y2 y3 : ℕ → ℕ) (hh0 : ∀ j,j < nodes → s.values j ≤ s.values 0)
    (hy1 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 s.values j=y1 j)
    (hy2 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y1 j=y2 j)
    (hy3 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y2 j=y3 j)
    (hm : (∑ x,μ x)=((blockStep b s y1 y2 y3).mass:ℚ)/scale)
    (hgrid : CompleteGridBound κ A E c q t μ realGrid ((blockOperator b^b.count) (realValues s.values)))
    (hmoment : CompleteMomentBound κ A E c q t μ 3 ((blockCubicFactor b)^b.count*((s.cubic:ℚ)/scale))) :
    CompleteGridBound κ A E c q t μ realGrid (realValues (blockStep b s y1 y2 y3).values) ∧
    CompleteMomentBound κ A E c q t μ 3 (((blockStep b s y1 y2 y3).cubic:ℚ)/scale) := by
  constructor
  · have hr := completeGridBound_mono κ A E c q t μ _ _ _ hgrid (rounded_blockRaw b hb s.values y1 y2 y3 hh0 hy1 hy2 hy3)
    exact completeGridBound_pruneValues κ A E c q t μ hμ _ hr b.cut _ hcut hm
  · exact completeMomentBound_mono κ A E c q t μ 3 hmoment (rounded_block_cubic b hb.lo_two s.cubic)

end Grid
#print axioms completeGridBound_rounded_block_loss
#print axioms completeMomentBound_block_resample
#print axioms complete_rounded_block_finish
end Erdos7No9Certificate
