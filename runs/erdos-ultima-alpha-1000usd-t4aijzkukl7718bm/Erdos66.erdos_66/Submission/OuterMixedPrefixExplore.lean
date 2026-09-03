import Submission.SaturatingCyclicFamilyExplore

/-! Outer repetition controls the location of mixed representation endpoints,
not just their total count. All statements here are in one finite modulus. -/
namespace Erdos66OuterMixedPrefix
open Erdos66OuterCarryProfile Erdos66CyclicThickening Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 2000000

variable (M : ℕ) [NeZero M]

noncomputable def prefixCount (C D : Finset (ZMod M)) (z : ZMod M) (u : ℕ) : ℕ :=
  (C.filter (fun a ↦ a.val < u ∧ z-a∈D)).card

lemma prefixCount_sum (C D : Finset (ZMod M)) (z : ZMod M) (u : ℕ) :
    prefixCount M C D z u = ∑ a : ZMod M, if a.val < u ∧ a∈C ∧ z-a∈D then 1 else 0 := by
  calc
    _ = ∑ a : ZMod M, if a∈C ∧ a.val < u ∧ z-a∈D then 1 else 0 := by
      simp only [prefixCount,Finset.card_filter,ite_and,Finset.sum_ite_mem,Finset.univ_inter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      exact propext and_left_comm

noncomputable def intervalCount (C D : Finset (ZMod M)) (z : ZMod M) (u v : ℕ) : ℕ :=
  (C.filter (fun a ↦ u ≤ a.val ∧ a.val < v ∧ z-a∈D)).card

lemma intervalCount_add_prefix (C D : Finset (ZMod M)) (z : ZMod M)
    (u v : ℕ) (huv : u ≤ v) :
    intervalCount M C D z u v+prefixCount M C D z u = prefixCount M C D z v := by
  let S := C.filter (fun a ↦ u ≤ a.val ∧ a.val < v ∧ z-a∈D)
  let T := C.filter (fun a ↦ a.val < u ∧ z-a∈D)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have ha' := (Finset.mem_filter.mp ha).2.1
    have hb' := (Finset.mem_filter.mp hb).2.1
    omega
  have he : S ∪ T = C.filter (fun a ↦ a.val < v ∧ z-a∈D) := by
    ext a
    by_cases ha : a∈C <;> by_cases hz : z-a∈D <;> simp [S,T,ha,hz] <;> omega
  have hh := Finset.card_union_of_disjoint hd
  rw [he] at hh
  exact hh.symm

lemma interval_error_of_prefix_error (C D : Finset (ZMod M)) (z : ZMod M)
    (u v : ℕ) (huv : u ≤ v) (μ E : ℝ)
    (hu : |(prefixCount M C D z u:ℝ)-(u:ℝ)/M*μ| ≤ E)
    (hv : |(prefixCount M C D z v:ℝ)-(v:ℝ)/M*μ| ≤ E) :
    |(intervalCount M C D z u v:ℝ)-((v:ℝ)-u)/M*μ| ≤ 2*E := by
  have hh : (intervalCount M C D z u v:ℝ)+prefixCount M C D z u = prefixCount M C D z v := by
    exact_mod_cast intervalCount_add_prefix M C D z u v huv
  have he : (intervalCount M C D z u v:ℝ)-((v:ℝ)-u)/M*μ =
      ((prefixCount M C D z v:ℝ)-(v:ℝ)/M*μ)-
      ((prefixCount M C D z u:ℝ)-(u:ℝ)/M*μ) := by
    rw [←hh]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

variable (K : ℕ) [NeZero K]

lemma outerLift_mono {C D : Finset (ZMod M)} (h : C ⊆ D) :
    outerLift M K C ⊆ outerLift M K D := by
  intro x hx
  exact (mem_outerLift M K D x).mpr (h ((mem_outerLift M K C x).mp hx))

lemma outerLift_univ : outerLift M K (Finset.univ : Finset (ZMod M)) = Finset.univ := by
  ext x
  simp [mem_outerLift]

lemma outerLift_card (C : Finset (ZMod M)) : (outerLift M K C).card = K*C.card := by
  have hh := outer_cyclicCount M K C Finset.univ 0
  rw [outerLift_univ,cyclicCount_full_right,cyclicCount_full_right] at hh
  exact hh

lemma outerLift_mean (C D : Finset (ZMod M)) :
    actualMean (M*K) (outerLift M K C) (outerLift M K D) = K*actualMean M C D := by
  simp only [actualMean,outerLift_card,Nat.cast_mul]
  have hK : (K:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  field_simp

lemma outer_prefix_sandwich (C D : Finset (ZMod M)) (z : ZMod (M*K))
    (u : ℕ) (hu : u ≤ M*K) :
    (u/M)*cyclicCount M C D (reduceDigit M K z) ≤
      prefixCount (M*K) (outerLift M K C) (outerLift M K D) z u ∧
    prefixCount (M*K) (outerLift M K C) (outerLift M K D) z u ≤
      (u/M+1)*cyclicCount M C D (reduceDigit M K z) := by
  have hM : 0<M := NeZero.pos M
  have hqK : u/M ≤ K := (Nat.div_le_div_right hu).trans_eq (Nat.mul_div_right K hM)
  have hlow (a : ZMod M) (i : Fin K) (hi : i.val < u/M) : a.val+M*i.val < u := by
    have ha := ZMod.val_lt a
    have hqu : M*(u/M) ≤ u := Nat.mul_div_le u M
    have hi' : i.val+1 ≤ u/M := hi
    nlinarith
  have hupp (a : ZMod M) (i : Fin K) (hi : a.val+M*i.val < u) : i.val < u/M+1 := by
    have hqu : u < M*(u/M+1) := Nat.lt_mul_div_succ u hM
    by_contra hh
    have hh' : u/M+1 ≤ i.val := by omega
    nlinarith
  have hcount (a : ZMod M) :
      u/M ≤ ((Finset.univ : Finset (Fin K)).filter (fun i ↦ a.val+M*i.val < u)).card ∧
      ((Finset.univ : Finset (Fin K)).filter (fun i ↦ a.val+M*i.val < u)).card ≤ u/M+1 := by
    constructor
    · rw [←card_fin_below K (u/M) hqK]
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlow a i (Finset.mem_filter.mp hi).2⟩
    · have hs : (Finset.univ : Finset (Fin K)).filter (fun i ↦ a.val+M*i.val < u) ⊆
          Finset.univ.filter (fun i ↦ i.val < min K (u/M+1)) := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_min i.isLt (hupp a i (Finset.mem_filter.mp hi).2)⟩
      exact (Finset.card_le_card hs).trans ((card_fin_below K (min K (u/M+1)) (min_le_left _ _)).le.trans (min_le_right _ _))
  rw [prefixCount_sum,←Equiv.sum_comp (blockEquiv M K),Fintype.sum_prod_type]
  simp only [blockEquiv,Equiv.ofBijective_apply,blockDigit_val,mem_outerLift,map_sub,reduce_block]
  have hin (a : ZMod M) :
      (∑ i : Fin K, if a.val+M*i.val < u ∧ a∈C ∧ reduceDigit M K z-a∈D then 1 else 0) =
      if a∈C ∧ reduceDigit M K z-a∈D then
        ((Finset.univ : Finset (Fin K)).filter (fun i ↦ a.val+M*i.val < u)).card else 0 := by
    by_cases ha : a∈C ∧ reduceDigit M K z-a∈D
    · simp only [ha,and_true,if_true,Finset.card_filter]
    · simp only [ha,and_false,if_false,Finset.sum_const_zero]
  simp_rw [hin]
  rw [cyclicCount_sum]
  simp_rw [Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro a ha <;>
    split_ifs <;> simp_all only [mul_one,mul_zero,le_refl,hcount]

/-- Every mixed endpoint prefix has its expected fraction of the outer mean,
up to the original relative error plus one boundary block. -/
theorem outer_prefix_error (C D : Finset (ZMod M)) (z : ZMod (M*K))
    (u : ℕ) (hu : u ≤ M*K) (μ σ : ℝ) (hμ : 0 ≤ μ) (hσ : 0 ≤ σ)
    (hflat : |(cyclicCount M C D (reduceDigit M K z):ℝ)-μ| ≤ σ*μ) :
    |(prefixCount (M*K) (outerLift M K C) (outerLift M K D) z u:ℝ)-
        ((u:ℝ)/(M*K))*(K*μ)| ≤ ((K+1)*σ+1)*μ := by
  have hMp : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hKp : (0:ℝ)<K := by exact_mod_cast NeZero.pos K
  have hqK : (u/M:ℕ) ≤ K := (Nat.div_le_div_right hu).trans_eq (Nat.mul_div_right K (NeZero.pos M))
  have hqKr : ((u/M:ℕ):ℝ) ≤ K := by exact_mod_cast hqK
  have hq0 : (0:ℝ) ≤ (u/M:ℕ) := by positivity
  have hq : ((u/M:ℕ):ℝ) ≤ (u:ℝ)/M := by
    apply (le_div_iff₀ hMp).mpr
    exact_mod_cast Nat.div_mul_le_self u M
  have hq' : (u:ℝ)/M ≤ (u/M:ℕ)+1 := by
    apply (div_le_iff₀ hMp).mpr
    exact_mod_cast (show u ≤ (u/M+1)*M by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ u (NeZero.pos M)).le)
  obtain ⟨hl,hu'⟩ := outer_prefix_sandwich M K C D z u hu
  have hl' : ((u/M:ℕ):ℝ)*(cyclicCount M C D (reduceDigit M K z):ℝ) ≤
      prefixCount (M*K) (outerLift M K C) (outerLift M K D) z u := by exact_mod_cast hl
  have hu'' : (prefixCount (M*K) (outerLift M K C) (outerLift M K D) z u:ℝ) ≤
      ((u/M:ℕ)+1:ℝ)*(cyclicCount M C D (reduceDigit M K z):ℝ) := by exact_mod_cast hu'
  obtain ⟨hflo,hfhi⟩ := abs_le.mp hflat
  have hb1 := mul_le_mul_of_nonneg_left hflo hq0
  have hb2 := mul_le_mul_of_nonneg_left hfhi (show (0:ℝ) ≤ (u/M:ℕ)+1 by positivity)
  have hb3 := mul_le_mul_of_nonneg_right hq hμ
  have hb4 := mul_le_mul_of_nonneg_right hq' hμ
  have hb5 := mul_le_mul_of_nonneg_right hqKr (mul_nonneg hσ hμ)
  have he : ((u:ℝ)/(M*K))*(K*μ)=(u:ℝ)/M*μ := by field_simp
  rw [he,abs_le]
  constructor <;> nlinarith only [hl',hu'',hb1,hb2,hb3,hb4,hb5,mul_nonneg hσ hμ]

theorem outer_prefix_relative_error (C D : Finset (ZMod M))
    (η σ : ℝ) (hη : 0 ≤ η) (hσ : 0 ≤ σ) (hση : σ ≤ η/4)
    (hK : 2 ≤ η*(K:ℝ))
    (hflat : ∀ z, |(cyclicCount M C D z:ℝ)-actualMean M C D| ≤ σ*actualMean M C D) :
    ∀ z u, u ≤ M*K →
      |(prefixCount (M*K) (outerLift M K C) (outerLift M K D) z u:ℝ)-
        ((u:ℝ)/(M*K))*actualMean (M*K) (outerLift M K C) (outerLift M K D)| ≤
        η*actualMean (M*K) (outerLift M K C) (outerLift M K D) := by
  intro z u hu
  rw [outerLift_mean]
  have hh := outer_prefix_error M K C D z u hu (actualMean M C D) σ
    (actualMean_nonneg M C D) hσ (hflat _)
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast NeZero.pos K
  have hbound : (K+1)*σ+1 ≤ η*K := by
    have h1 := mul_le_mul_of_nonneg_left hση (show (0:ℝ) ≤ K+1 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hK1 hη
    nlinarith
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hbound (actualMean_nonneg M C D)])

/-- Arbitrary endpoint intervals, uniformly in both palette members and target. -/
theorem outer_interval_relative_error (C D : Finset (ZMod M))
    (η σ : ℝ) (hη : 0 ≤ η) (hσ : 0 ≤ σ) (hση : σ ≤ η/4)
    (hK : 2 ≤ η*(K:ℝ))
    (hflat : ∀ z, |(cyclicCount M C D z:ℝ)-actualMean M C D| ≤ σ*actualMean M C D) :
    ∀ z u v, u ≤ v → v ≤ M*K →
      |(intervalCount (M*K) (outerLift M K C) (outerLift M K D) z u v:ℝ)-
        (((v:ℝ)-u)/(M*K))*actualMean (M*K) (outerLift M K C) (outerLift M K D)| ≤
        2*η*actualMean (M*K) (outerLift M K C) (outerLift M K D) := by
  intro z u v huv hv
  have hp := outer_prefix_relative_error M K C D η σ hη hσ hση hK hflat
  have hh := interval_error_of_prefix_error (M*K) (outerLift M K C) (outerLift M K D) z u v huv
    (actualMean (M*K) (outerLift M K C) (outerLift M K D))
    (η*actualMean (M*K) (outerLift M K C) (outerLift M K D))
    (by simpa only [Nat.cast_mul] using hp z u (huv.trans hv))
    (by simpa only [Nat.cast_mul] using hp z v hv)
  simpa only [Nat.cast_mul,mul_assoc] using hh

end Erdos66OuterMixedPrefix
