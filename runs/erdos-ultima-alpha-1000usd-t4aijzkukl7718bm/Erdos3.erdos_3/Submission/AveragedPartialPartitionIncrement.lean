import Submission.AveragedMaskedPhaseIncrement

/-! Density increments on good cells of an approximate finite partition.
A single exceptional cell is allowed, with a controlled average mass. -/
namespace Erdos3AveragedPartialPartitionIncrement
open Finset Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
  Erdos3AveragedMaskedPhaseIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {I V : Type*} [Fintype I] [Nonempty I] [Fintype V] [Nonempty V]

lemma partial_partition_correlation_bound (c : V → Option I) (f : V → ℝ)
    (q : V → ℂ) (w : I → ℂ) (hf : ∀ x, |f x| ≤ 1)
    (hq : ∀ x, ‖q x‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (happrox : ∀ x i, c x = some i → ‖q x-w i‖ ≤ ε) :
    ‖𝔼 x, (f x : ℂ)*q x‖ ≤ ε+cellMass c none+
      ∑ i : I, |cellCharge c f (some i)| := by
  let w' : Option I → ℂ := fun i ↦ i.elim 0 w
  have herr : ‖(𝔼 x, (f x : ℂ)*q x)-(𝔼 x, (f x : ℂ)*w' (c x))‖ ≤ ε+cellMass c none := by
    rw [← expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    have hp (x : V) : ‖(f x : ℂ)*q x-(f x : ℂ)*w' (c x)‖ ≤
        ε+(if c x = none then 1 else 0 : ℝ) := by
      rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply ((mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)).trans_eq (one_mul _)).trans
      cases hc : c x with
      | none => simpa only [w',Option.elim_none,sub_zero,hc,if_true] using (hq x).trans (by linarith : (1 : ℝ) ≤ ε+1)
      | some i => simpa only [w',Option.elim_some,hc,Option.some_ne_none,if_false,add_zero] using happrox x i hc
    have hh := expect_le_expect (s := univ) (fun x _ ↦ hp x)
    rw [expect_add_distrib,Fintype.expect_const] at hh
    convert hh using 1
    congr 1
    unfold cellMass
    apply expect_congr rfl
    intro x _
    split_ifs <;> rfl
  have hpair : ‖𝔼 x, (f x : ℂ)*w' (c x)‖ ≤ ∑ i : I, |cellCharge c f (some i)| := by
    rw [cellCharge_pairing,Fintype.sum_option]
    simp only [w',Option.elim_none,Option.elim_some,mul_zero,zero_add]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)).trans_eq (mul_one _)
  exact (norm_le_norm_sub_add _ _).trans (add_le_add herr hpair)

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- Averaged correlation survives an approximately constant partition after
paying once for phase oscillation and twice for the exceptional mass. Joint
centering, rather than centering separately at each center, suffices. -/
theorem averaged_partial_partition_increment (c : Z → V → Option I)
    (f : Z → V → ℝ) (q : Z → V → ℂ) (w : Z → I → ℂ)
    (hf : ∀ a x, |f a x| ≤ 1) (hf0 : (𝔼 a, 𝔼 x, f a x) = 0)
    (hq : ∀ a x, ‖q a x‖ ≤ 1) (hw : ∀ a i, ‖w a i‖ ≤ 1)
    {r ε τ : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hbudget : ε+2*τ ≤ r/2)
    (hbad : (𝔼 a, cellMass (c a) none) ≤ τ)
    (happrox : ∀ a x i, c a x = some i → ‖q a x-w a i‖ ≤ ε)
    (hcorr : r ≤ 𝔼 a, ‖𝔼 x, (f a x : ℂ)*q a x‖^2) :
    ∃ a : Z, ∃ i : I, (cell (c a) (some i)).Nonempty ∧
      r/(16*(Fintype.card I : ℝ)) ≤ cellMass (c a) (some i) ∧
      r/16 ≤ 𝔼 x : cell (c a) (some i), f a x := by
  let u : Z → I → ℝ := fun a i ↦ cellCharge (c a) (f a) (some i)
  let corr : Z → ℝ := fun a ↦ ‖𝔼 x, (f a x : ℂ)*q a x‖
  have hnorm (a : Z) : corr a ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le univ_nonempty
    intro x _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul (hf a x) (hq a x) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hsq (a : Z) : (corr a)^2 ≤ corr a := by
    have hh : 0 ≤ corr a := norm_nonneg _
    nlinarith [hnorm a]
  have hbound (a : Z) : corr a ≤ ε+cellMass (c a) none+∑ i, |u a i| :=
    partial_partition_correlation_bound (c a) (f a) (q a) (w a)
      (hf a) (hq a) (hw a) hε (happrox a)
  have hzero : (𝔼 a, cellCharge (c a) (f a) none)+(𝔼 a, ∑ i, u a i) = 0 := by
    rw [← expect_add_distrib]
    have he (a : Z) : cellCharge (c a) (f a) none+∑ i, u a i = 𝔼 x, f a x := by
      simpa only [Fintype.sum_option,u] using sum_cellCharge (c a) (f a)
    simp only [he,hf0]
  have hbadcharge : (𝔼 a, cellCharge (c a) (f a) none) ≤ τ :=
    (expect_le_expect (fun a _ ↦ (le_abs_self _).trans (abs_cellCharge_le (c a) (f a) (hf a) none))).trans hbad
  have hL : r/2 ≤ 𝔼 a, ((∑ i, |u a i|)+(∑ i, u a i)) := by
    have hh := hcorr.trans (expect_le_expect (fun a _ ↦ (hsq a).trans (hbound a)))
    rw [expect_add_distrib,expect_add_distrib,Fintype.expect_const] at hh
    rw [expect_add_distrib]
    linarith
  obtain ⟨a,_,ha⟩ := exists_max_image univ (fun a ↦ (∑ i, |u a i|)+(∑ i, u a i)) univ_nonempty
  have hLa := hL.trans (expect_le univ_nonempty ha)
  have hm : (∑ i : I, cellMass (c a) (some i)) ≤ 1 := by
    have hh := sum_cellMass (c a)
    rw [Fintype.sum_option] at hh
    linarith [cellMass_nonneg (c a) none]
  obtain ⟨i,hi,hinc⟩ := positive_cell_of_L1_plus_mean
    (fun i ↦ cellMass (c a) (some i)) (u a) (fun i ↦ cellMass_nonneg _ _) hm
    (fun i ↦ abs_cellCharge_le _ _ (hf a) _) (by positivity : 0 < r/2) hLa
  have hpos : 0 < cellMass (c a) (some i) :=
    (by positivity : 0 < (r/2)/(8*(Fintype.card I : ℝ))).trans_le hi
  have hcell : (cell (c a) (some i)).Nonempty := by
    by_contra hn
    rw [cellMass_eq_card,Finset.not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero,zero_div] at hpos
    exact (lt_irrefl 0) hpos
  change (r/2/8)*cellMass (c a) (some i) ≤ cellCharge (c a) (f a) (some i) at hinc
  rw [cellCharge_eq_mean (c a) (f a) (some i) hcell] at hinc
  refine ⟨a,i,hcell,?_,?_⟩
  · convert hi using 1 <;> ring
  · nlinarith only [hinc,hpos]

#print axioms averaged_partial_partition_increment
end Erdos3AveragedPartialPartitionIncrement
