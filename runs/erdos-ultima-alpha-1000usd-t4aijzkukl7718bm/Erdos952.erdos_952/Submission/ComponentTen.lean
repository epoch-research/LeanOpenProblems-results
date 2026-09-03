import Submission.ComponentTenCheck0
import Submission.ComponentTenCheck1
import Submission.ComponentTenCheck2
import Submission.ComponentTenCheck3
import Submission.ComponentTenCheck4

/-! A kernel-checked finite moat around 3 for squared jumps strictly below 10.
This fixed-bound result is not a disproof for arbitrary jump bounds. -/
namespace Erdos952Investigation
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma component_rows10 : ∀ r : Fin 85, componentRow10 r := by
  intro r
  fin_cases r
  · exact component_row10_0
  · exact component_row10_1
  · exact component_row10_2
  · exact component_row10_3
  · exact component_row10_4
  · exact component_row10_5
  · exact component_row10_6
  · exact component_row10_7
  · exact component_row10_8
  · exact component_row10_9
  · exact component_row10_10
  · exact component_row10_11
  · exact component_row10_12
  · exact component_row10_13
  · exact component_row10_14
  · exact component_row10_15
  · exact component_row10_16
  · exact component_row10_17
  · exact component_row10_18
  · exact component_row10_19
  · exact component_row10_20
  · exact component_row10_21
  · exact component_row10_22
  · exact component_row10_23
  · exact component_row10_24
  · exact component_row10_25
  · exact component_row10_26
  · exact component_row10_27
  · exact component_row10_28
  · exact component_row10_29
  · exact component_row10_30
  · exact component_row10_31
  · exact component_row10_32
  · exact component_row10_33
  · exact component_row10_34
  · exact component_row10_35
  · exact component_row10_36
  · exact component_row10_37
  · exact component_row10_38
  · exact component_row10_39
  · exact component_row10_40
  · exact component_row10_41
  · exact component_row10_42
  · exact component_row10_43
  · exact component_row10_44
  · exact component_row10_45
  · exact component_row10_46
  · exact component_row10_47
  · exact component_row10_48
  · exact component_row10_49
  · exact component_row10_50
  · exact component_row10_51
  · exact component_row10_52
  · exact component_row10_53
  · exact component_row10_54
  · exact component_row10_55
  · exact component_row10_56
  · exact component_row10_57
  · exact component_row10_58
  · exact component_row10_59
  · exact component_row10_60
  · exact component_row10_61
  · exact component_row10_62
  · exact component_row10_63
  · exact component_row10_64
  · exact component_row10_65
  · exact component_row10_66
  · exact component_row10_67
  · exact component_row10_68
  · exact component_row10_69
  · exact component_row10_70
  · exact component_row10_71
  · exact component_row10_72
  · exact component_row10_73
  · exact component_row10_74
  · exact component_row10_75
  · exact component_row10_76
  · exact component_row10_77
  · exact component_row10_78
  · exact component_row10_79
  · exact component_row10_80
  · exact component_row10_81
  · exact component_row10_82
  · exact component_row10_83
  · exact component_row10_84

lemma inComponent10_coordinate_bound {z : GaussianInt} (hz : InComponent10 z) :
    -84 ≤ z.re ∧ z.re ≤ 84 ∧ -84 ≤ z.im ∧ z.im ≤ 84 := by
  have hh : max |z.re| |z.im| ≤ 84 := hz.2.2.1
  have hr := abs_le.mp ((le_max_left _ _).trans hh)
  have hi := abs_le.mp ((le_max_right _ _).trans hh)
  exact ⟨hr.1,hr.2,hi.1,hi.2⟩

lemma inComponent10_finite : {z | InComponent10 z}.Finite := by
  apply (norm_sublevel_finite 14112).subset
  intro z hz
  obtain ⟨hr0,hr1,hi0,hi1⟩ := inComponent10_coordinate_bound hz
  have hr : z.re^2 ≤ (84 : ℤ)^2 := sq_le_sq.mpr (by
    norm_num
    exact abs_le.mpr ⟨hr0,hr1⟩)
  have hi : z.im^2 ≤ (84 : ℤ)^2 := sq_le_sq.mpr (by
    norm_num
    exact abs_le.mpr ⟨hi0,hi1⟩)
  simp only [Set.mem_setOf_eq,gaussian_norm_sq]
  omega

lemma three_inComponent10 : InComponent10 (3 : GaussianInt) := by decide +kernel

lemma inOctantComponent10_closed {z w : GaussianInt} (hz : InOctantComponent10 z)
    (hw : Prime w) (hd : (w-z).norm < 10) (hwO : OctantReduction.InOctant w) :
    InOctantComponent10 w := by
  have hd' : (w.re-z.re)^2+(w.im-z.im)^2 < 10 := by
    simpa only [gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub] using hd
  have hdr : -3 ≤ w.re-z.re ∧ w.re-z.re ≤ 3 := by
    constructor <;> nlinarith [sq_nonneg (w.im-z.im)]
  have hdi : -3 ≤ w.im-z.im ∧ w.im-z.im ≤ 3 := by
    constructor <;> nlinarith [sq_nonneg (w.re-z.re)]
  have hi0 := hz.1
  have hir := hz.2.1
  have hr1 := hz.2.2.1
  let r : Fin 85 := ⟨z.re.toNat,by omega⟩
  let s : Fin 85 := ⟨z.im.toNat,by omega⟩
  let a : Fin 7 := ⟨(w.re-z.re+3).toNat,by omega⟩
  let b : Fin 7 := ⟨(w.im-z.im+3).toNat,by omega⟩
  have hr : (r : ℤ) = z.re := by dsimp [r]; omega
  have hs : (s : ℤ) = z.im := by dsimp [s]; omega
  have ha : (a : ℤ)-3 = w.re-z.re := by dsimp [a]; omega
  have hb : (b : ℤ)-3 = w.im-z.im := by dsimp [b]; omega
  have hrow := component_rows10 r s
  dsimp only at hrow
  rw [hr,hs] at hrow
  have hstep := hrow hz a b
  rw [ha,hb] at hstep
  have heq : (⟨z.re+(w.re-z.re),z.im+(w.im-z.im)⟩ : GaussianInt) = w := by
    ext <;> simp
  have hrow' : InOctantComponent10 w ∨ blocked10 w := by
    simpa only [heq] using hstep hd' (by simpa only [heq] using hwO)
  exact hrow'.resolve_right (prime_not_blocked10 hw)

lemma inComponent10_closed {z w : GaussianInt} (hz : InComponent10 z)
    (hw : Prime w) (hd : (w-z).norm < 10) : InComponent10 w :=
  inOctantComponent10_closed hz (OctantReduction.prime_fold hw)
    (lt_of_le_of_lt (OctantReduction.fold_contract _ _) hd)
    (OctantReduction.fold_in_octant _)

theorem component10_certificate : ∃ S : Finset GaussianInt, MoatCertificate 10 S := by
  classical
  refine ⟨inComponent10_finite.toFinset,?_,?_⟩
  · simpa only [Set.Finite.mem_toFinset,Set.mem_setOf_eq] using three_inComponent10
  · intro z hz w hw
    simp only [Set.Finite.mem_toFinset,Set.mem_setOf_eq] at hz ⊢
    exact inComponent10_closed hz hw.2.1 hw.2.2.2

theorem component10_finite :
    {w | (primeGraph 10).Reachable (3 : GaussianInt) w}.Finite :=
  (fixed_component_finite_iff_certificate 10).mpr component10_certificate

#print axioms component10_finite
end Erdos952Investigation
