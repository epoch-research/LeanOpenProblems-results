import Submission.No9LossRounding
import Submission.BinaryGrid

/-! Soundness of individual rounded prime steps, including the binary prime 3. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7KilledSieve Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

lemma rounded_binary_term (p A B : ℕ) (hp : 0 < p) (hB : 0 < B)
    (h : ℕ → ℕ) (j : Fin nodes) :
    2*(((A:ℚ)/B)/p)*gridChord realGrid (cellLo 0 j) (cellHi 0 j) (realGrid j/2) (realValues h) ≤
    (ceilDiv (A*interpNumerator h 2 j.val) (B*p*(cells 2 j.val).width):ℚ)/scale := by
  have hv := cells_valid 2 j.val (by decide) (by decide) j.isLt
  have hw := hv.2.1
  have hpQ : (p:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hBq : (B:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hwQ : ((cells 2 j.val).width:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hw)
  have hh := cell_chord h 2 j.val (by decide) _ hv
  simp only [Nat.cast_ofNat] at hh
  change _*gridChord realGrid (gridIndex _) (gridIndex _) ((grid j.val:ℚ)/2) _ ≤ _
  rw [hh]
  have hr := div_le_div_of_nonneg_right
    (ceilDiv_bound (A*interpNumerator h 2 j.val) (B*p*(cells 2 j.val).width) (by positivity)) scale_pos.le
  simp only [Nat.cast_mul] at hr
  convert hr using 1
  dsimp [interpNumerator]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  field_simp

lemma rounded_rawValue_binary (a : PrefixControl) (hp : a.p=3) (hB : 0 < a.B)
    (hA : a.A ≤ a.B*a.p) (h : ℕ → ℕ) :
    (fun j => (1-((a.A:ℚ)/a.B)/a.p)*realValues h j+
      2*(((a.A:ℚ)/a.B)/a.p)*gridChord realGrid (cellLo 0 j) (cellHi 0 j) (realGrid j/2) (realValues h)) ≤
      realValues (rawValue a h) := by
  intro j
  have hpos : 0 < a.p := by omega
  have hh := add_le_add (rounded_diagonal a.p a.A a.B hpos hB hA h j)
    (rounded_binary_term a.p a.A a.B hpos hB h j)
  simpa only [rawValue,if_pos hp,realValues,Nat.cast_add,add_div] using hh

lemma rounded_binary_cubic (p A B C : ℕ) (hp : 0 < p) (hB : 0 < B) :
    (1+7*((A:ℚ)/B)/p)*((C:ℚ)/scale) ≤ (ceilDiv (C*(B*p+7*A)) (B*p):ℚ)/scale := by
  have hpQ : (p:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hBq : (B:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hh := div_le_div_of_nonneg_right (ceilDiv_bound (C*(B*p+7*A)) (B*p) (by positivity)) scale_pos.le
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
  convert hh using 1
  field_simp

lemma rounded_geometric_cubic (p A B C : ℕ) (hp : 1 < p) (hB : 0 < B) :
    (1+((A:ℚ)/B)*(7*(p:ℚ)^2-2*p+1)/(p-1)^3)*((C:ℚ)/scale) ≤
    (ceilDiv (C*(B*(p-1)^3+A*(7*p*p-2*p+1))) (B*(p-1)^3):ℚ)/scale := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hp1 : (p:ℚ)-1≠0 := by linarith
  have hBq : (B:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hq : 0 < p-1 := by omega
  have hsub : 2*p ≤ 7*p*p := by nlinarith
  have hh := div_le_div_of_nonneg_right
    (ceilDiv_bound (C*(B*(p-1)^3+A*(7*p*p-2*p+1))) (B*(p-1)^3) (by positivity)) scale_pos.le
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hsub,Nat.cast_sub (by omega : 1 ≤ p),
    Nat.cast_one,Nat.cast_ofNat] at hh
  convert hh using 1
  field_simp

section Grid
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

lemma completeGridBound_rounded_resample (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (B : Finset (∀ i,A i))
    (h : ℕ → ℕ) (hh : CompleteGridBound κ A E c q t μ realGrid (realValues h))
    (a : PrefixControl) (hp : 3 ≤ a.p) (hR0 : 1 ≤ a.R) (hR1 : a.R ≤ 18)
    (hB : 0 < a.B) (hBA : a.B ≤ a.A) (hA : a.A ≤ a.B*a.p)
    (hci : c ⟨t,ht⟩=(a.A:ℚ)/a.B)
    (hqi : q ⟨t,ht⟩=powerTail a.p (c ⟨t,ht⟩) (E ⟨t,ht⟩))
    (hE : if a.p=3 then E ⟨t,ht⟩=1 else a.R ≤ E ⟨t,ht⟩) :
    CompleteGridBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩)) realGrid
      (realValues (rawValue a h)) := by
  have hBQ : (0:ℚ) < a.B := by exact_mod_cast hB
  have hc : 1 ≤ c ⟨t,ht⟩ := by rw [hci]; exact (one_le_div hBQ).mpr (by exact_mod_cast hBA)
  have hcp : c ⟨t,ht⟩ ≤ a.p := by
    rw [hci]
    exact (div_le_iff₀ hBQ).mpr (by exact_mod_cast (hA.trans_eq (Nat.mul_comm _ _)))
  have hc0 : 0 ≤ c ⟨t,ht⟩ := by linarith
  have hpQ : (0:ℚ) < a.p := by exact_mod_cast (by omega : 0 < a.p)
  by_cases hp3 : a.p=3
  · rw [if_pos hp3] at hE
    apply completeGridBound_mono κ A E c q (t+1) _ _ _ _ _ (rounded_rawValue_binary a hp3 hB hA h)
    intro j
    have hgeom := grid_geometry 1 (by omega) 0 (by omega) j
    have hhalf := completeGridBound_chord κ A E c q t μ hμ _ _ hh _ _ _ hgeom.1 hgeom.2.1 hgeom.2.2
    simp only [Nat.cast_zero,zero_add] at hhalf
    have hr := completeHingeBound_binary_resample κ A E c q t ht μ hμ hE
      (c ⟨t,ht⟩/(a.p:ℚ)) (div_nonneg hc0 hpQ.le) ((div_le_one hpQ).mpr hcp)
      (by simp only [hqi,hE,powerTail,if_pos (by decide : 0 < 1),pow_one,Nat.zero_add,div_eq_mul_inv])
      (by simp only [hqi,hE,powerTail,if_neg (by decide : ¬1 < 1)]) hc _ _ _ (hh j) hhalf B
    simpa only [hci,Nat.cast_zero,zero_add] using hr
  · rw [if_neg hp3] at hE
    have hr := completeGridBound_resample_majorant κ A E c q t ht μ hμ realGrid (realValues h)
      (fun j => Nat.cast_nonneg _) (realValues_nonneg h) hh gridZero (by change (grid 0:ℚ)=0; exact_mod_cast grid_zero)
      cellLo cellHi a.p a.p (a.R-1) (by omega) le_rfl (by omega)
      (grid_geometry _ (by omega)) hqi hc hcp (1-c ⟨t,ht⟩/(a.p:ℚ)) le_rfl B
    apply completeGridBound_mono κ A E c q (t+1) _ _ _ _ hr
    simpa only [hci,realOperator] using rounded_rawValue a (by omega) hp3 hB hA hR0 hR1 h

lemma rounded_momentFactor (a : PrefixControl) (E C : ℕ) (hp : 3 ≤ a.p) (hB : 0 < a.B)
    (hE : a.p=3 → E=1) :
    momentFactor E (powerTail a.p ((a.A:ℚ)/a.B) E) 3*((C:ℚ)/scale) ≤
      ((step a ⟨0,C,fun _ => 0⟩).cubic:ℚ)/scale := by
  by_cases hp3 : a.p=3
  · have hE1 := hE hp3
    have hh := rounded_binary_cubic a.p a.A a.B C (by omega) hB
    convert hh using 1
    · simp only [hE1,momentFactor,Finset.sum_range_one,powerTail,
        if_pos (by decide : 0 < 1),Nat.zero_add,pow_one]
      norm_num
      ring <;> simp
    · simp only [step,if_pos hp3]
  · have hh := geometric_cubic_factor a.p E (by omega) ((a.A:ℚ)/a.B) (by positivity)
    apply (mul_le_mul_of_nonneg_right hh (by positivity : (0:ℚ) ≤ (C:ℚ)/scale)).trans
    simpa only [step,if_neg hp3,denominator] using rounded_geometric_cubic a.p a.A a.B C (by omega) hB

lemma complete_rounded_prefix_step (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (B : Finset (∀ i,A i)) (s : State)
    (hm : (∑ x,μ x)=(s.mass:ℚ)/scale)
    (hgrid : CompleteGridBound κ A E c q t μ realGrid (realValues s.values))
    (hmoment : CompleteMomentBound κ A E c q t μ 3 ((s.cubic:ℚ)/scale))
    (a : PrefixControl) (hp : 3 ≤ a.p) (hR0 : 1 ≤ a.R) (hR1 : a.R ≤ 18)
    (hB : 0 < a.B) (hBA : a.B ≤ a.A) (hA : a.A ≤ a.B*a.p) (hcut : a.cut < nodes)
    (hci : c ⟨t,ht⟩=(a.A:ℚ)/a.B)
    (hqi : q ⟨t,ht⟩=powerTail a.p (c ⟨t,ht⟩) (E ⟨t,ht⟩))
    (hE : if a.p=3 then E ⟨t,ht⟩=1 else a.R ≤ E ⟨t,ht⟩)
    (hLs : loss a s.values ≤ s.mass)
    (hL : (∑ x,μ x*residual (c ⟨t,ht⟩) (coordinateFraction A ⟨t,ht⟩ B x)) ≤ (loss a s.values:ℚ)/scale) :
    let μ' := killedResample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩) ((loss a s.values:ℚ)/scale)
    CompleteGridBound κ A E c q (t+1) μ' realGrid (realValues (step a s).values) ∧
    CompleteMomentBound κ A E c q (t+1) μ' 3 (((step a s).cubic:ℚ)/scale) := by
  have hBQ : (0:ℚ) < a.B := by exact_mod_cast hB
  have hc : 1 ≤ c ⟨t,ht⟩ := by rw [hci]; exact (one_le_div hBQ).mpr (by exact_mod_cast hBA)
  have hc0 : 0 ≤ c ⟨t,ht⟩ := by linarith
  have hcp : c ⟨t,ht⟩ ≤ a.p := by
    rw [hci]
    exact (div_le_iff₀ hBQ).mpr (by exact_mod_cast (hA.trans_eq (Nat.mul_comm _ _)))
  have hLm : (loss a s.values:ℚ)/scale ≤ ∑ x,μ x := by
    rw [hm]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hLs) scale_pos.le
  have hpos := killedResample_nonneg A ⟨t,ht⟩ μ hμ B (c ⟨t,ht⟩) ((loss a s.values:ℚ)/scale) hc hLm
  have htotal := killedResample_total A ⟨t,ht⟩ μ B (c ⟨t,ht⟩) ((loss a s.values:ℚ)/scale) hc hLm hL
  rw [hm] at htotal
  have htotal' : (∑ x,killedResample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩) ((loss a s.values:ℚ)/scale) x)=
      ((step a s).mass:ℚ)/scale := by
    simpa only [step,Nat.cast_sub hLs,sub_div] using htotal
  constructor
  · have hr := completeGridBound_rounded_resample κ A E c q t ht μ hμ B s.values hgrid a
      hp hR0 hR1 hB hBA hA hci hqi hE
    have hk := completeGridBound_kill κ A E c q (t+1) ⟨t,ht⟩ μ hμ B hc ((loss a s.values:ℚ)/scale)
      hLm hL realGrid _ hr
    have hh := completeGridBound_pruneValues κ A E c q (t+1) _ hpos _ hk a.cut (step a s).mass hcut htotal'
    exact hh
  · have hr := completeMomentBound_resample κ A E c q t ht μ hμ 3 ((s.cubic:ℚ)/scale) hmoment B hc
      (by rw [hqi]; exact powerTail_zero_le_one a.p (by omega) _ hcp _)
      (by intro g hg; rw [hqi]; exact powerTail_decreasing a.p (by omega) _ hc0 _ g)
      (by rw [hqi]; exact powerTail_terminal a.p _ _)
    have hround := rounded_momentFactor a (E ⟨t,ht⟩) s.cubic hp hB (by
      intro hp3
      simpa only [if_pos hp3] using hE)
    have hbound : momentFactor (E ⟨t,ht⟩) (q ⟨t,ht⟩) 3*((s.cubic:ℚ)/scale) ≤
        ((step a s).cubic:ℚ)/scale := by
      simpa only [hqi,hci,step] using hround
    exact completeMomentBound_kill κ A E c q (t+1) ⟨t,ht⟩ μ hμ B hc ((loss a s.values:ℚ)/scale)
      hLm hL 3 _ (completeMomentBound_mono κ A E c q (t+1) _ 3 hr hbound)

lemma initial_values_hinge (j : Fin nodes) : realValues initial.values j=max 0 (1-realGrid j) := by
  have hs := ne_of_gt scale_pos
  by_cases hj : grid j.val=0
  · simp only [realValues,initial,realGrid,hj,Nat.sub_zero,Nat.cast_mul,Nat.cast_one,
      one_mul,Nat.cast_zero,sub_zero,max_eq_right (by norm_num : (0:ℚ) ≤ 1),div_self hs]
  · have hg : 1 ≤ grid j.val := by omega
    have hgQ : (1:ℚ) ≤ grid j.val := by exact_mod_cast hg
    simp only [realValues,initial,realGrid,Nat.sub_eq_zero_of_le hg,zero_mul,Nat.cast_zero,zero_div,
      max_eq_left (sub_nonpos.mpr hgQ)]

lemma completeGridBound_initial (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (μ : (∀ i,A i) → ℚ) (hm : (∑ x,μ x)=1) :
    CompleteGridBound κ A E c q 0 μ realGrid (realValues initial.values) := by
  intro j M
  have hh := completeTestBound_initial κ A E c q μ hm M (fun z => max 0 (z-(M:ℚ)*realGrid j))
  convert hh using 1
  rw [initial_values_hinge,mul_max_of_nonneg _ _ (Nat.cast_nonneg M),mul_zero]
  congr 1
  ring

end Grid
#print axioms completeGridBound_rounded_resample
#print axioms rounded_momentFactor
#print axioms complete_rounded_prefix_step
#print axioms completeGridBound_initial
end Erdos7No9Certificate
