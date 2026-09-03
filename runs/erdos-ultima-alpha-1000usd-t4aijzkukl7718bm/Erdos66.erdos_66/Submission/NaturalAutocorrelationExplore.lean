import Submission.AutocorrelationStabilityExplore

/-! Natural half-line autocorrelation stability, obtained from finite cyclic
identities by dominated convergence as the period tends to infinity. -/
namespace Erdos66NaturalAutocorrelation
open Erdos66AutocorrelationStability Erdos66MixedEnergy
  Erdos66WeightedSquareStability Erdos66ResidueSeries Erdos66Generating
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2200000

noncomputable def natCorr (f : ℕ → ℝ) (h : ℕ) : ℝ := ∑' n, f n*f (n+h)

lemma summable_pair_mul {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun ij : ℕ×ℕ ↦ f ij.1*f ij.2) :=
  summable_mul_of_summable_norm hf.norm hf.norm

lemma push_corr_pairs (m : ℕ) [NeZero m] {f : ℕ → ℝ} (hf : Summable f) (z : ZMod m) :
    corr (push m f) z = ∑' ij : ℕ×ℕ,
      if (ij.2 : ZMod m)=(ij.1 : ZMod m)+z then f ij.1*f ij.2 else 0 := by
  have hs (x : ZMod m) : Summable (fun ij : ℕ×ℕ ↦
      residueTerm m f x ij.1*residueTerm m f (x+z) ij.2) :=
    summable_mul_of_summable_norm (summable_residueTerm m hf x).norm
      (summable_residueTerm m hf (x+z)).norm
  calc
    _ = ∑ x : ZMod m, ∑' ij : ℕ×ℕ,
        residueTerm m f x ij.1*residueTerm m f (x+z) ij.2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(hs x).tsum_prod]
      simp only [push,tsum_mul_left,tsum_mul_right]
    _ = ∑' ij : ℕ×ℕ, ∑ x : ZMod m,
        residueTerm m f x ij.1*residueTerm m f (x+z) ij.2 :=
      (Summable.tsum_finsetSum (fun x _ ↦ hs x)).symm
    _ = _ := by
      apply tsum_congr
      intro ij
      have he (x : ZMod m) : residueTerm m f x ij.1*residueTerm m f (x+z) ij.2 =
          if (ij.1 : ZMod m)=x then
            (if (ij.2 : ZMod m)=(ij.1 : ZMod m)+z then f ij.1*f ij.2 else 0) else 0 := by
        by_cases hx : (ij.1 : ZMod m)=x
        · subst x
          simp only [residueTerm,ite_true,mul_ite,mul_zero]
        · simp [residueTerm,hx]
      simp_rw [he]
      simp

lemma natCorr_pairs {f : ℕ → ℝ} (hf : Summable f) (h : ℕ) :
    natCorr f h = ∑' ij : ℕ×ℕ, if ij.2=ij.1+h then f ij.1*f ij.2 else 0 := by
  have hs : Summable (fun ij : ℕ×ℕ ↦ if ij.2=ij.1+h then f ij.1*f ij.2 else 0) := by
    apply (summable_pair_mul hf).norm.of_norm_bounded
    intro ij
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (f ij.1*f ij.2)
  rw [hs.tsum_prod]
  simp only [tsum_ite_eq,natCorr]

lemma push_corr_tendsto {f : ℕ → ℝ} (hf : Summable f) (h : ℕ) :
    Tendsto (fun k : ℕ ↦ corr (push (k+1) f) (h : ZMod (k+1))) atTop (𝓝 (natCorr f h)) := by
  simp_rw [push_corr_pairs _ hf,natCorr_pairs hf h]
  apply tendsto_tsum_of_dominated_convergence (summable_pair_mul hf).norm
  · intro ij
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max ij.2 (ij.1+h))] with k hk
    have hj : ij.2<k+1 := by omega
    have hi : ij.1+h<k+1 := by omega
    have he : (ij.2 : ZMod (k+1))=(ij.1 : ZMod (k+1))+(h : ZMod (k+1)) ↔
        ij.2=ij.1+h := by
      rw [← Nat.cast_add,ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hi]
    simp only [he]
  · apply Eventually.of_forall
    intro k ij
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (f ij.1*f ij.2)

lemma partial_corr_le_cyclic (m H : ℕ) [NeZero m] (hm : H< m) (F G : ZMod m → ℝ) :
    (∑ h∈Finset.range (H+1), (corr F (h : ZMod m)-corr G (h : ZMod m))^2) ≤
      ∑ z : ZMod m, (corr F z-corr G z)^2 := by
  let S := (Finset.range (H+1)).image (fun h : ℕ ↦ (h : ZMod m))
  have hi : Set.InjOn (fun h : ℕ ↦ (h : ZMod m)) (Finset.range (H+1) : Set ℕ) := by
    intro a ha b hb he
    have ha' : a< m := by have := Finset.mem_range.mp ha; omega
    have hb' : b< m := by have := Finset.mem_range.mp hb; omega
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ha',Nat.mod_eq_of_lt hb']
      using congrArg ZMod.val he
  calc
    _ = ∑ z∈S, (corr F z-corr G z)^2 := (Finset.sum_image (fun a ha b hb he ↦ hi ha hb he)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ ↦ sq_nonneg _)

/-- The cyclic overhead disappears for each finite list of genuine natural
shifts. Neither f nor g is required to be nonnegative. -/
theorem partial_weighted_corr_error {f g : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r<1)
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n))
    (hE : Summable (fun n ↦ (sumConv f f n-sumConv g g n)^2*r^n)) (H : ℕ) :
    (∑ h∈Finset.range (H+1),
      (natCorr (fun n ↦ f n*r^n) h-natCorr (fun n ↦ g n*r^n) h)^2) ≤
      ∑' n, (sumConv f f n-sumConv g g n)^2*r^n := by
  have hl := tendsto_finset_sum (Finset.range (H+1))
    (fun h _ ↦ ((push_corr_tendsto hf h).sub (push_corr_tendsto hg h)).pow 2)
  have hp : Tendsto (fun k : ℕ ↦ (1-r^(k+1))⁻¹) atTop (𝓝 (1 : ℝ)) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      (tendsto_add_atTop_nat 1)).const_sub 1
    simpa only [sub_zero,inv_one] using hh.inv₀ (by norm_num : (1-0 : ℝ)≠0)
  have hu := hp.mul_const (∑' n, (sumConv f f n-sumConv g g n)^2*r^n)
  rw [one_mul] at hu
  apply le_of_tendsto_of_tendsto hl hu
  filter_upwards [eventually_ge_atTop H] with k hk
  exact (partial_corr_le_cyclic (k+1) H (by omega) _ _).trans
    (cyclic_weighted_corr_error (k+1) hr0 hr1 hf hg hE)

/-- The entire one-sided autocorrelation-error sequence is square summable,
with its squared norm bounded by the weighted representation error. -/
theorem weighted_corr_error {f g : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r<1)
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n))
    (hE : Summable (fun n ↦ (sumConv f f n-sumConv g g n)^2*r^n)) :
    Summable (fun h ↦ (natCorr (fun n ↦ f n*r^n) h-natCorr (fun n ↦ g n*r^n) h)^2) ∧
    (∑' h, (natCorr (fun n ↦ f n*r^n) h-natCorr (fun n ↦ g n*r^n) h)^2) ≤
      ∑' n, (sumConv f f n-sumConv g g n)^2*r^n := by
  let E := ∑' n, (sumConv f f n-sumConv g g n)^2*r^n
  let e := fun h ↦ (natCorr (fun n ↦ f n*r^n) h-natCorr (fun n ↦ g n*r^n) h)^2
  have hb (S : Finset ℕ) : (∑ h∈S, e h)≤E := by
    have hsub : S⊆Finset.range (S.sup id+1) := by
      intro x hx
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ sq_nonneg _)).trans
      (partial_weighted_corr_error hr0 hr1 hf hg hE (S.sup id))
  have he : Summable e := summable_of_sum_le (fun h ↦ sq_nonneg _) hb
  refine ⟨he,?_⟩
  apply le_of_tendsto he.hasSum
  exact Eventually.of_forall hb

noncomputable def weightedCorr (f : ℕ → ℝ) (r : ℝ) (h : ℕ) : ℝ :=
  ∑' n, f n*f (n+h)*r^(2*n+h)

lemma weightedCorr_eq (f : ℕ → ℝ) (r : ℝ) (h : ℕ) :
    weightedCorr f r h=natCorr (fun n ↦ f n*r^n) h := by
  apply tsum_congr
  intro n
  rw [show 2*n+h=n+(n+h) by omega,pow_add]
  ring

end Erdos66NaturalAutocorrelation
