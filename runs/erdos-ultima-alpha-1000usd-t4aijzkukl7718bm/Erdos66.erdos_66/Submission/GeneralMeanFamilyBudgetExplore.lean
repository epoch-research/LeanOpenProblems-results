import Submission.ApproximateComplementarityExplore

/-! The family energy budget at arbitrary common mean, including logarithmic
means. It bounds the mixed mean-square error on the square-root-mean scale. -/
namespace Erdos66GeneralMeanFamilyBudget
open Erdos66MixedEnergy Erdos66CyclicVariance Erdos66CenteredMixedEnergy
  Erdos66ApproximateComplementarity
open scoped Classical
set_option maxHeartbeats 2400000

section Groups
variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I] [Nonempty I]

omit [Fintype I] [Nonempty I] in
lemma common_mean (B : I → Finset G) (k : ℕ) (μ : ℝ)
    (hB : ∀ i, (B i).card=k) (hμ : (Fintype.card G:ℝ)*μ=(k:ℝ)^2) (i j : I) :
    mixedMean (indicator (B i)) (indicator (B j))=μ := by
  rw [mixedMean,sum_indicator,sum_indicator,hB,hB]
  apply (div_eq_iff (card_pos (G:=G)).ne').mpr
  nlinarith

omit [Fintype I] [Nonempty I] in
lemma common_self_energy_cap (B : I → Finset G) (k : ℕ) (μ C : ℝ)
    (hB : ∀ i, (B i).card=k) (hμ : (Fintype.card G:ℝ)*μ=(k:ℝ)^2)
    (hself : ∀ i z, (((B i).filter (fun x ↦ z-x∈B i)).card:ℝ)≤ C) (i : I) :
    centeredEnergy (indicator (B i)) (indicator (B i))≤ (k:ℝ)^2*(C-μ) := by
  rw [centeredEnergy_eq,common_mean B k μ hB hμ]
  have he : energy (indicator (B i)) (indicator (B i))≤ C*(k:ℝ)^2 := by
    calc
      _ ≤ ∑ z : G, C*conv (indicator (B i)) (indicator (B i)) z := by
        apply Finset.sum_le_sum
        intro z hz
        rw [conv_indicator]
        have hh := mul_le_mul_of_nonneg_right (hself i z)
          (Nat.cast_nonneg (α:=ℝ) (((B i).filter (fun x ↦ z-x∈B i)).card))
        nlinarith
      _ = _ := by rw [←Finset.mul_sum,sum_conv,sum_indicator,hB]; ring
  nlinarith [congrArg (fun x : ℝ ↦ x*μ) hμ]

omit [Nonempty I] in
lemma total_common_energy_lower (B : I → Finset G) (k : ℕ) (μ : ℝ)
    (hB : ∀ i, (B i).card=k) (hμ : (Fintype.card G:ℝ)*μ=(k:ℝ)^2) :
    (Fintype.card G:ℝ)*((Fintype.card I:ℝ)*((k:ℝ)-μ))^2≤
      ((Fintype.card G:ℝ)-1)*
        (∑ i : I, ∑ j : I, centeredEnergy (indicator (B i)) (indicator (B j))) := by
  let v : I → G → ℝ := fun i ↦ centeredCorr (indicator (B i))
  have hz (i : I) : (∑ x, v i x)=0 := by
    simp only [v,centeredCorr,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,sum_corr_mean]
    ring
  have hv (i : I) : v i 0=(k:ℝ)-μ := by
    simp only [v,centeredCorr,corr_zero,sum_indicator_sq,hB,common_mean B k μ hB hμ]
  have hh := family_coordinate_bound v (0:G) hz
  simpa only [hv,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    v,←centeredEnergy_eq_corr_inner] using hh

/-- q equal-size sets, with mean μ and self cap C, cannot have arbitrarily
small distinct-pair mean-square errors E. No unit-mean hypothesis is used. -/
theorem common_mean_family_budget (B : I → Finset G) (k : ℕ) (μ C E : ℝ)
    (hB : ∀ i, (B i).card=k) (hμ : (Fintype.card G:ℝ)*μ=(k:ℝ)^2)
    (hmixed : ∀ i j, i≠j → centeredEnergy (indicator (B i)) (indicator (B j))≤
      (Fintype.card G:ℝ)*E)
    (hself : ∀ i z, (((B i).filter (fun x ↦ z-x∈B i)).card:ℝ)≤ C) :
    (Fintype.card I:ℝ)*((k:ℝ)-μ)^2≤
      ((Fintype.card G:ℝ)-1)*(μ*(C-μ)+((Fintype.card I:ℝ)-1)*E) := by
  have hM : (0:ℝ)<Fintype.card G := card_pos
  have hq : (0:ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos (α:=I)
  have hi (i : I) : (∑ j : I, centeredEnergy (indicator (B i)) (indicator (B j)))≤
      (Fintype.card G:ℝ)*(μ*(C-μ)+((Fintype.card I:ℝ)-1)*E) := by
    have hc : ((Finset.univ.erase i).card:ℝ)=(Fintype.card I:ℝ)-1 := by
      have hh := Finset.card_erase_add_one (s:=Finset.univ) (a:=i) (Finset.mem_univ i)
      have hh' : ((Finset.univ.erase i).card:ℝ)+1=Fintype.card I := by exact_mod_cast hh
      linarith
    have he := Finset.sum_erase_add (s:=Finset.univ) (a:=i)
      (f:=fun j ↦ centeredEnergy (indicator (B i)) (indicator (B j))) (Finset.mem_univ i)
    have hb : (∑ j∈Finset.univ.erase i, centeredEnergy (indicator (B i)) (indicator (B j)))≤
        ((Fintype.card I:ℝ)-1)*((Fintype.card G:ℝ)*E) := by
      calc
        _ ≤ ∑ _j∈Finset.univ.erase i, (Fintype.card G:ℝ)*E :=
          Finset.sum_le_sum (fun j hj ↦ hmixed i j (Ne.symm (Finset.mem_erase.mp hj).1))
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,hc]
    have hs := common_self_energy_cap B k μ C hB hμ hself i
    have heq := congrArg (fun x : ℝ ↦ x*(C-μ)) hμ
    nlinarith
  have htotal : (∑ i : I, ∑ j : I, centeredEnergy (indicator (B i)) (indicator (B j)))≤
      (Fintype.card I:ℝ)*(Fintype.card G:ℝ)*
        (μ*(C-μ)+((Fintype.card I:ℝ)-1)*E) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) ↦ hi i)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hh
  have hM1 : (1:ℝ)≤ Fintype.card G := by exact_mod_cast Fintype.card_pos (α:=G)
  have hl := total_common_energy_lower B k μ hB hμ
  have hu := mul_le_mul_of_nonneg_left htotal (sub_nonneg.mpr hM1)
  apply (mul_le_mul_iff_right₀ (mul_pos hM hq)).mp
  nlinarith [hl.trans hu]

/-- Pointwise relative mixed error ε costs E=ε²μ², not E=ε². -/
theorem relative_mixed_family_budget (B : I → Finset G) (k : ℕ) (μ C ε : ℝ)
    (hB : ∀ i, (B i).card=k) (hμ : (Fintype.card G:ℝ)*μ=(k:ℝ)^2)
    (hε : 0≤ ε*μ)
    (hmixed : ∀ i j, i≠j → ∀ z,
      |(((B i).filter (fun x ↦ z-x∈B j)).card:ℝ)-μ|≤ ε*μ)
    (hself : ∀ i z, (((B i).filter (fun x ↦ z-x∈B i)).card:ℝ)≤ C) :
    (Fintype.card I:ℝ)*((k:ℝ)-μ)^2≤
      ((Fintype.card G:ℝ)-1)*(μ*(C-μ)+((Fintype.card I:ℝ)-1)*(ε*μ)^2) := by
  apply common_mean_family_budget B k μ C ((ε*μ)^2) hB hμ ?_ hself
  intro i j hij
  unfold centeredEnergy
  rw [common_mean B k μ hB hμ]
  calc
    _ ≤ ∑ _z : G, (ε*μ)^2 := by
      apply Finset.sum_le_sum
      intro z hz
      rw [conv_indicators]
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hε).mpr (hmixed i j hij z)
    _ = _ := by simp

end Groups

lemma normalized_family_budget {M k q μ C E : ℝ}
    (hM : 0<M) (hq : 0<q) (hμp : 0<μ) (hμ : M*μ=k^2)
    (h : q*(k-μ)^2≤ (M-1)*(μ*(C-μ)+(q-1)*E)) :
    (1-k/M)^2≤ (1-1/M)*((C-μ)/q+(1-1/q)*(E/μ)) := by
  have hm : μ=k^2/M := (eq_div_iff hM.ne').mpr (by nlinarith)
  have he₁ : (M*μ*q)*(1-k/M)^2=q*(k-μ)^2 := by
    rw [hm]
    field_simp
  have he₂ : (M*μ*q)*((1-1/M)*((C-μ)/q+(1-1/q)*(E/μ)))=
      (M-1)*(μ*(C-μ)+(q-1)*E) := by
    field_simp
  apply (mul_le_mul_iff_right₀ (mul_pos (mul_pos hM hμp) hq)).mp
  simpa only [he₁,he₂] using h

section Limits
open Filter
open scoped Topology

/-- For a growing sparse family with sublinear self excess, the
mean-square mixed error is asymptotically at least one times its mean.
At logarithmic mean this is a square-root-log RMS threshold, not a
logarithmic-error contradiction. -/
theorem numeric_relative_error_floor (M k q μ C E : ℕ → ℝ) (e : ℝ)
    (hM : Tendsto M atTop atTop) (hq : Tendsto q atTop atTop)
    (hdensity : Tendsto (fun n ↦ k n/M n) atTop (𝓝 0))
    (hself : Tendsto (fun n ↦ (C n-μ n)/q n) atTop (𝓝 0))
    (herror : Tendsto (fun n ↦ E n/μ n) atTop (𝓝 e))
    (hμp : ∀ᶠ n in atTop, 0<μ n)
    (hμ : ∀ᶠ n in atTop, M n*μ n=(k n)^2)
    (hbudget : ∀ᶠ n in atTop,
      q n*(k n-μ n)^2≤ (M n-1)*(μ n*(C n-μ n)+(q n-1)*E n)) :
    1≤ e := by
  have hiM := hM.const_div_atTop (1:ℝ)
  have hiq := hq.const_div_atTop (1:ℝ)
  have hleft : Tendsto (fun n ↦ (1-k n/M n)^2) atTop (𝓝 (1:ℝ)) := by
    simpa only [sub_zero,one_pow] using (hdensity.const_sub 1).pow 2
  have hright : Tendsto
      (fun n ↦ (1-1/M n)*((C n-μ n)/q n+(1-1/q n)*(E n/μ n))) atTop (𝓝 e) := by
    simpa only [sub_zero,one_mul,zero_add] using
      (hiM.const_sub 1).mul (hself.add ((hiq.const_sub 1).mul herror))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hbudget,hμ,hμp,hM.eventually_gt_atTop 0,hq.eventually_gt_atTop 0] with
    n hn hmean hpos hMn hqn
  exact normalized_family_budget hMn hqn hpos hmean hn

/-- The same conclusion for actual finite sets, with common means allowed
to grow. The common mean is not normalized away before measuring errors. -/
theorem mixed_error_over_mean_limit_ge_one
    (G I : ℕ → Type*) [∀ n, AddCommGroup (G n)] [∀ n, Fintype (G n)]
    [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
    (B : (n : ℕ) → I n → Finset (G n)) (k : ℕ → ℕ) (μ C E : ℕ → ℝ) (e : ℝ)
    (hM : Tendsto (fun n ↦ Fintype.card (G n)) atTop atTop)
    (hq : Tendsto (fun n ↦ Fintype.card (I n)) atTop atTop)
    (hB : ∀ n i, (B n i).card=k n)
    (hμp : ∀ n, 0<μ n)
    (hμ : ∀ n, (Fintype.card (G n):ℝ)*μ n=(k n:ℝ)^2)
    (hself : ∀ n (i : I n) (z : G n),
      (((B n i).filter (fun x ↦ z-x∈B n i)).card:ℝ)≤ C n)
    (hmixed : ∀ n (i j : I n), i≠j →
      centeredEnergy (indicator (B n i)) (indicator (B n j))≤ (Fintype.card (G n):ℝ)*E n)
    (hdensity : Tendsto (fun n ↦ (k n:ℝ)/(Fintype.card (G n):ℝ)) atTop (𝓝 0))
    (hcap : Tendsto (fun n ↦ (C n-μ n)/(Fintype.card (I n):ℝ)) atTop (𝓝 0))
    (herror : Tendsto (fun n ↦ E n/μ n) atTop (𝓝 e)) : 1≤ e := by
  apply numeric_relative_error_floor (fun n ↦ (Fintype.card (G n):ℝ))
    (fun n ↦ (k n:ℝ)) (fun n ↦ (Fintype.card (I n):ℝ)) μ C E e
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hM)
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hq) hdensity hcap herror
    (Eventually.of_forall hμp) (Eventually.of_forall hμ)
  exact Eventually.of_forall (fun n ↦ common_mean_family_budget (B n) (k n) (μ n) (C n) (E n)
    (hB n) (hμ n) (hmixed n) (hself n))

end Limits
end Erdos66GeneralMeanFamilyBudget
