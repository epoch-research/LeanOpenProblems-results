import Submission.CenteredMixedEnergyExplore

/-! Exact mixed-complementary digit families force large self-representation
peaks. This rules out one density-preserving smoothing mechanism; it does not
resolve the natural-number conjecture. -/
namespace Erdos66ComplementaryFamilyBarrier
open Erdos66MixedEnergy Erdos66CyclicVariance Erdos66CenteredMixedEnergy
open scoped Classical

section RealVectors
variable {G I : Type*} [Fintype G] [Fintype I]

lemma zero_mean_coordinate_bound (v : G → ℝ) (z : G) (hv : ∑ x, v x=0) :
    (Fintype.card G : ℝ)*(v z)^2 ≤ ((Fintype.card G : ℝ)-1)*(∑ x, (v x)^2) := by
  let S := Finset.univ.erase z
  have hcard : (S.card : ℝ)=(Fintype.card G : ℝ)-1 := by
    have hh := Finset.card_erase_add_one (s := Finset.univ) (a := z) (Finset.mem_univ _)
    have hh' : (S.card : ℝ)+1=Fintype.card G := by exact_mod_cast hh
    linarith
  have hs := Finset.sum_erase_add (s := Finset.univ) (a := z) (f := v) (Finset.mem_univ _)
  change (∑ x∈S, v x)+v z=∑ x, v x at hs
  rw [hv] at hs
  have hsq := Finset.sum_erase_add (s := Finset.univ) (a := z) (f := fun x ↦ (v x)^2) (Finset.mem_univ _)
  change (∑ x∈S, (v x)^2)+(v z)^2=∑ x, (v x)^2 at hsq
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := v)
  rw [hcard] at hcs
  have he : (∑ x∈S, v x) = -v z := by linarith
  rw [he,neg_sq] at hcs
  nlinarith

lemma orthogonal_family_square (v : I → G → ℝ)
    (horth : ∀ i j, i ≠ j → (∑ x, v i x*v j x)=0) :
    (∑ x, (∑ i, v i x)^2) = ∑ i, ∑ x, (v i x)^2 := by
  have hexp (x : G) : (∑ i, v i x)^2=∑ i, ∑ j, v i x*v j x := by
    rw [pow_two,Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  calc
    _ = ∑ x, v i x*v i x := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        exact horth i j (Ne.symm hji)
      · simp
    _ = _ := by simp only [pow_two]

lemma orthogonal_family_coordinate_bound (v : I → G → ℝ) (z : G)
    (hzero : ∀ i, ∑ x, v i x=0)
    (horth : ∀ i j, i ≠ j → (∑ x, v i x*v j x)=0) :
    (Fintype.card G : ℝ)*(∑ i, v i z)^2 ≤
      ((Fintype.card G : ℝ)-1)*(∑ i, ∑ x, (v i x)^2) := by
  have hz : (∑ x, ∑ i, v i x)=0 := by rw [Finset.sum_comm]; simp only [hzero,Finset.sum_const_zero]
  simpa only [orthogonal_family_square v horth] using zero_mean_coordinate_bound (fun x ↦ ∑ i, v i x) z hz

end RealVectors

section Groups
variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I] [Nonempty I]

/-- If q sets of cardinality k in a group of order k² have exactly one
representation of every target for every distinct pair of sets, and all
self-counts are at most C, then q(k-1) <= (k+1)(C-1). This is sharp for the
k+1 one-dimensional subspaces of a plane over a field of order k. -/
theorem complementary_family_self_peak_bound (B : I → Finset G) (k : ℕ)
    (hk : 2 ≤ k) (hG : Fintype.card G=k^2) (hB : ∀ i, (B i).card=k) (C : ℝ)
    (hmixed : ∀ i j, i ≠ j → ∀ z : G, ((B i).filter (fun x ↦ z-x∈B j)).card=1)
    (hself : ∀ i z, (((B i).filter (fun x ↦ z-x∈B i)).card : ℝ) ≤ C) :
    (Fintype.card I : ℝ)*((k : ℝ)-1) ≤ ((k : ℝ)+1)*(C-1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1<k by omega)
  have hM : (Fintype.card G : ℝ) = (k : ℝ)^2 := by exact_mod_cast hG
  have hq : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
  have hmean (i j : I) : mixedMean (indicator (B i)) (indicator (B j))=1 := by
    simp only [mixedMean,sum_indicator,hB,hM]
    field_simp
  let v : I → G → ℝ := fun i ↦ centeredCorr (indicator (B i))
  have hzero (i : I) : (∑ z, v i z)=0 := by
    simp only [v,centeredCorr,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,sum_corr_mean]
    ring
  have horth (i j : I) (hij : i ≠ j) : (∑ z, v i z*v j z)=0 := by
    rw [show (∑ z, v i z*v j z)=centeredEnergy (indicator (B i)) (indicator (B j)) from
      (centeredEnergy_eq_corr_inner _ _).symm]
    simp only [centeredEnergy,conv_indicators,hmixed i j hij,hmean,Nat.cast_one,sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
  have hv0 (i : I) : v i 0=(k : ℝ)-1 := by
    simp only [v,centeredCorr,corr_zero,sum_indicator_sq,hB,hmean]
  have henergy (i : I) : (∑ z, (v i z)^2) ≤ (k : ℝ)^2*(C-1) := by
    have he : (∑ z, (v i z)^2)=centeredEnergy (indicator (B i)) (indicator (B i)) := by
      simpa only [v,pow_two] using (centeredEnergy_eq_corr_inner (indicator (B i)) (indicator (B i))).symm
    rw [he,centeredEnergy_eq,hmean,one_pow,mul_one,hM]
    have hb : energy (indicator (B i)) (indicator (B i)) ≤ C*(k : ℝ)^2 := by
      calc
        _ ≤ ∑ z : G, C*conv (indicator (B i)) (indicator (B i)) z := by
          apply Finset.sum_le_sum
          intro z hz
          rw [conv_indicator]
          have hh := mul_le_mul_of_nonneg_right (hself i z)
            (Nat.cast_nonneg (α := ℝ) (((B i).filter (fun x ↦ z-x∈B i)).card))
          nlinarith
        _ = _ := by rw [← Finset.mul_sum,sum_conv,sum_indicator,hB]; ring
    nlinarith
  have htotal : (∑ i, ∑ z, (v i z)^2) ≤ (Fintype.card I : ℝ)*(k : ℝ)^2*(C-1) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) ↦ henergy i)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hh
  have hcoord := orthogonal_family_coordinate_bound v (0:G) hzero horth
  simp only [hv0,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hM] at hcoord
  have hnon : 0 ≤ (k : ℝ)^2-1 := by nlinarith
  have hu := mul_le_mul_of_nonneg_left htotal hnon
  have hred : (Fintype.card I : ℝ)*((k : ℝ)-1)^2 ≤ ((k : ℝ)^2-1)*(C-1) := by
    apply (mul_le_mul_iff_right₀ (mul_pos (sq_pos_of_pos hkpos) hq)).mp
    nlinarith [hcoord.trans hu]
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hk1)).mp
  nlinarith

end Groups
end Erdos66ComplementaryFamilyBarrier
