import Submission.ComplementaryFamilyBarrierExplore

/-! A mean-square version of the complementary-family obstruction. It
bounds the aggregate mixed energy, not just exact complementary pairs.
This is a finite construction restriction, not a disproof of Erdős 66. -/
namespace Erdos66ApproximateComplementarity
open Erdos66MixedEnergy Erdos66CyclicVariance Erdos66CenteredMixedEnergy
  Erdos66ComplementaryFamilyBarrier
open scoped Classical
set_option maxHeartbeats 2200000

section Vectors
variable {G I : Type*} [Fintype G] [Fintype I]

lemma family_square_expansion (v : I → G → ℝ) :
    (∑ x, (∑ i, v i x)^2)=∑ i, ∑ j, ∑ x, v i x*v j x := by
  have he (x : G) : (∑ i, v i x)^2=∑ i, ∑ j, v i x*v j x := by
    rw [pow_two,Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

lemma family_coordinate_bound (v : I → G → ℝ) (z : G)
    (hzero : ∀ i, ∑ x, v i x=0) :
    (Fintype.card G : ℝ)*(∑ i, v i z)^2 ≤
      ((Fintype.card G : ℝ)-1)*(∑ i, ∑ j, ∑ x, v i x*v j x) := by
  have hz : (∑ x, ∑ i, v i x)=0 := by
    rw [Finset.sum_comm]
    simp only [hzero,Finset.sum_const_zero]
  simpa only [family_square_expansion] using zero_mean_coordinate_bound (fun x ↦ ∑ i, v i x) z hz

end Vectors

section Groups
variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I] [Nonempty I]

lemma unit_mean (B : I → Finset G) (k : ℕ) (hk : 0<k)
    (hG : Fintype.card G=k^2) (hB : ∀ i, (B i).card=k) (i j : I) :
    mixedMean (indicator (B i)) (indicator (B j))=1 := by
  have hk' : (k : ℝ)≠0 := by exact_mod_cast hk.ne'
  simp only [mixedMean,sum_indicator,hB,hG,Nat.cast_pow]
  field_simp

lemma self_energy_cap (B : I → Finset G) (k : ℕ) (hk : 0<k)
    (hG : Fintype.card G=k^2) (hB : ∀ i, (B i).card=k) (C : ℝ)
    (hself : ∀ i z, (((B i).filter (fun x ↦ z-x∈B i)).card : ℝ) ≤ C) (i : I) :
    centeredEnergy (indicator (B i)) (indicator (B i)) ≤ (k : ℝ)^2*(C-1) := by
  rw [centeredEnergy_eq,unit_mean B k hk hG hB,one_pow,mul_one,hG,Nat.cast_pow]
  have he : energy (indicator (B i)) (indicator (B i)) ≤ C*(k : ℝ)^2 := by
    calc
      _ ≤ ∑ z : G, C*conv (indicator (B i)) (indicator (B i)) z := by
        apply Finset.sum_le_sum
        intro z hz
        rw [conv_indicator]
        have hh := mul_le_mul_of_nonneg_right (hself i z)
          (Nat.cast_nonneg (α := ℝ) (((B i).filter (fun x ↦ z-x∈B i)).card))
        nlinarith
      _ = _ := by rw [←Finset.mul_sum,sum_conv,sum_indicator,hB]; ring
  nlinarith

/-- Total centered mixed energy is constrained by the common autocorrelation
spike at zero, even when none of the mixed pairs is exact. -/
theorem total_centered_energy_lower (B : I → Finset G) (k : ℕ) (hk : 0<k)
    (hG : Fintype.card G=k^2) (hB : ∀ i, (B i).card=k) :
    (k : ℝ)^2*((Fintype.card I : ℝ)*((k : ℝ)-1))^2 ≤
      ((k : ℝ)^2-1)*
        (∑ i : I, ∑ j : I, centeredEnergy (indicator (B i)) (indicator (B j))) := by
  let v : I → G → ℝ := fun i ↦ centeredCorr (indicator (B i))
  have hz (i : I) : (∑ x, v i x)=0 := by
    simp only [v,centeredCorr,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,sum_corr_mean]
    ring
  have hv (i : I) : v i 0=(k : ℝ)-1 := by
    simp only [v,centeredCorr,corr_zero,sum_indicator_sq,hB,unit_mean B k hk hG hB]
  have hh := family_coordinate_bound v (0 : G) hz
  simpa only [hv,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hG,Nat.cast_pow,
    v,←centeredEnergy_eq_corr_inner] using hh

/-- If every distinct pair has mean-square error at most E about its unit
mean, then q(k-1) <= (k+1)(C-1+(q-1)E). In particular small average errors
cannot coexist with many colors and a sublinear-in-q self cap. -/
theorem approximate_complementary_family_bound (B : I → Finset G) (k : ℕ)
    (hk : 2≤k) (hG : Fintype.card G=k^2) (hB : ∀ i, (B i).card=k) (C E : ℝ)
    (hmixed : ∀ i j, i≠j →
      centeredEnergy (indicator (B i)) (indicator (B j)) ≤ (k : ℝ)^2*E)
    (hself : ∀ i z, (((B i).filter (fun x ↦ z-x∈B i)).card : ℝ) ≤ C) :
    (Fintype.card I : ℝ)*((k : ℝ)-1) ≤
      ((k : ℝ)+1)*(C-1+((Fintype.card I : ℝ)-1)*E) := by
  have hk0 : 0<k := by omega
  have hkr : (1 : ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hq : (0 : ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos (α := I)
  have hi (i : I) : (∑ j : I, centeredEnergy (indicator (B i)) (indicator (B j))) ≤
      (k : ℝ)^2*(C-1+((Fintype.card I : ℝ)-1)*E) := by
    have hc : ((Finset.univ.erase i).card : ℝ)=(Fintype.card I : ℝ)-1 := by
      have hh := Finset.card_erase_add_one (s := Finset.univ) (a := i) (Finset.mem_univ i)
      have hh' : ((Finset.univ.erase i).card : ℝ)+1=Fintype.card I := by exact_mod_cast hh
      linarith
    have he := Finset.sum_erase_add (s := Finset.univ) (a := i)
      (f := fun j ↦ centeredEnergy (indicator (B i)) (indicator (B j))) (Finset.mem_univ i)
    have hbound : (∑ j∈Finset.univ.erase i, centeredEnergy (indicator (B i)) (indicator (B j))) ≤
        ((Fintype.card I : ℝ)-1)*((k : ℝ)^2*E) := by
      calc
        _ ≤ ∑ _j∈Finset.univ.erase i, (k : ℝ)^2*E :=
          Finset.sum_le_sum (fun j hj ↦ hmixed i j (Ne.symm (Finset.mem_erase.mp hj).1))
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,hc]
    have hs := self_energy_cap B k hk0 hG hB C hself i
    nlinarith
  have htotal : (∑ i : I, ∑ j : I, centeredEnergy (indicator (B i)) (indicator (B j))) ≤
      (Fintype.card I : ℝ)*(k : ℝ)^2*(C-1+((Fintype.card I : ℝ)-1)*E) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) ↦ hi i)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hh
  have hl := total_centered_energy_lower B k hk0 hG hB
  have hu := mul_le_mul_of_nonneg_left htotal (show 0≤(k : ℝ)^2-1 by nlinarith)
  have hred : (Fintype.card I : ℝ)*((k : ℝ)-1)^2 ≤
      ((k : ℝ)^2-1)*(C-1+((Fintype.card I : ℝ)-1)*E) := by
    apply (mul_le_mul_iff_right₀ (mul_pos (sq_pos_of_pos (by linarith : (0 : ℝ)<k)) hq)).mp
    nlinarith [hl.trans hu]
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hkr)).mp
  nlinarith

/-- A strict violation of the budget produces an actual distinct pair with
large mean-square error. This is not a lower bound on its pointwise error
at every target. -/
theorem exists_large_mixed_energy (B : I → Finset G) (k : ℕ)
    (hk : 2≤k) (hG : Fintype.card G=k^2) (hB : ∀ i, (B i).card=k) (C E : ℝ)
    (hself : ∀ i z, (((B i).filter (fun x ↦ z-x∈B i)).card : ℝ) ≤ C)
    (hgap : ((k : ℝ)+1)*(C-1+((Fintype.card I : ℝ)-1)*E)<
      (Fintype.card I : ℝ)*((k : ℝ)-1)) :
    ∃ i j : I, i≠j ∧ (k : ℝ)^2*E<centeredEnergy (indicator (B i)) (indicator (B j)) := by
  by_contra h
  have hm (i j : I) (hij : i≠j) :
      centeredEnergy (indicator (B i)) (indicator (B j)) ≤ (k : ℝ)^2*E :=
    le_of_not_gt (fun hh ↦ h ⟨i,j,hij,hh⟩)
  exact not_lt_of_ge (approximate_complementary_family_bound B k hk hG hB C E hm hself) hgap

end Groups
end Erdos66ApproximateComplementarity
