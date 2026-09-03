import Submission.TwoIntervalMeanSelection
import Submission.U3ProgressionSpan

/-! A positive relative mean on a short-span cyclic AP yields a long genuine
integer AP inside the reference interval, preserving the density increment. -/
namespace Erdos3IntervalProgressionRectification
open Finset Erdos3CyclicIntervalMask Erdos3NaturalProgressionCuts
  Erdos3TwoIntervalMeanSelection Erdos3CorrelationSifting Erdos3Reduction
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

noncomputable def progressionTrace (S : Finset ℕ) (b d m : ℕ) : Finset ℕ :=
  (range m).filter (fun j ↦ b+j*d ∈ S)

lemma castSet_mem_iff (p N k : ℕ) [NeZero p] (hNp : N ≤ p) (hk : k < p)
    (S : Finset ℕ) (hS : S ⊆ range N) : (k : ZMod p) ∈ castSet p S ↔ k ∈ S := by
  constructor
  · intro hx
    obtain ⟨n,hn,he⟩ := mem_image.mp hx
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt ((mem_range.mp (hS hn)).trans_le hNp),ZMod.val_natCast_of_lt hk] at hv
    exact hv ▸ hn
  · intro hkS
    exact mem_image.mpr ⟨k,hkS,rfl⟩

lemma progression_val (p d j : ℕ) [NeZero p] (a : ZMod p) :
    (a+j • (d : ZMod p)).val = (a.val+j*d)%p := by
  have he : a+j • (d : ZMod p) = ((a.val+j*d : ℕ) : ZMod p) := by
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul]
  rw [he,ZMod.val_natCast]

lemma progressionTrace_mean (S : Finset ℕ) (b d m : ℕ) :
    (𝔼 j : Fin m, if b+j.val*d ∈ S then (1 : ℝ) else 0) = intervalDensity (progressionTrace S b d m) m := by
  rw [Fintype.expect_eq_sum_div_card,Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun j ↦ if b+j*d ∈ S then (1 : ℝ) else 0) m]
  unfold intervalDensity progressionTrace
  congr 1
  simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

lemma trace_density_of_relative_mean (p N : ℕ) [NeZero p] (hNp : N ≤ p)
    (S : Finset ℕ) (hS : S ⊆ range N) (a : ZMod p) (d s b m : ℕ) (hm : 0 < m)
    (hcoords : ∀ j < m, (a+(s+j) • (d : ZMod p)).val = b+j*d ∧ b+j*d < N)
    {η : ℝ} (hmean : η ≤ 𝔼 j : Fin m, relativeBalance p N S (a+(s+j.val) • (d : ZMod p))) :
    intervalDensity S N+η ≤ intervalDensity (progressionTrace S b d m) m := by
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have he (j : Fin m) : relativeBalance p N S (a+(s+j.val) • (d : ZMod p)) =
      (if b+j.val*d ∈ S then (1 : ℝ) else 0)-intervalDensity S N := by
    have hj := hcoords j j.isLt
    have hi : a+(s+j.val) • (d : ZMod p) ∈ intervalMask p N :=
      (mem_intervalMask p N hNp _).mpr (by rw [hj.1]; exact hj.2)
    have hc : a+(s+j.val) • (d : ZMod p) = ((b+j.val*d : ℕ) : ZMod p) := by
      rw [← hj.1,ZMod.natCast_zmod_val]
    have hmemb : a+(s+j.val) • (d : ZMod p) ∈ castSet p S ↔ b+j.val*d ∈ S := by
      rw [hc]
      exact castSet_mem_iff p N _ hNp (hj.2.trans_le hNp) S hS
    unfold relativeBalance indicator
    rw [if_pos hi,mul_one]
    by_cases hh : b+j.val*d ∈ S
    · rw [if_pos hh,if_pos (hmemb.mpr hh)]
    · rw [if_neg hh,if_neg (fun h ↦ hh (hmemb.mp h))]
  simp_rw [he] at hmean
  rw [expect_sub_distrib,Fintype.expect_const,progressionTrace_mean] at hmean
  linarith

/-- At least half the positive mass lies in one of the two interval pieces.
That piece has length at least gamma*L/2 and retains gain gamma/2 over the
original interval density. -/
theorem interval_progression_rectification (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hNp : N ≤ p) (S : Finset ℕ) (hS : S ⊆ range N)
    (a : ZMod p) (d L : ℕ) (hd : 0 < d) (hL : 0 < L) (hspan : (L-1)*d < p)
    {γ : ℝ} (hγ : 0 < γ)
    (hmean : γ ≤ 𝔼 j : Fin L, relativeBalance p N S (a+j.val • (d : ZMod p))) :
    ∃ b m : ℕ, 0 < m ∧ γ*(L : ℝ)/2 ≤ (m : ℝ) ∧
      (∀ j < m, b+j*d < N) ∧
      intervalDensity S N+γ/2 ≤ intervalDensity (progressionTrace S b d m) m := by
  let b₀ := affineCut a.val d N L
  let c₀ := affineCut a.val d p L
  let e₀ := affineCut a.val d (p+N) L
  let f : ℕ → ℝ := fun j ↦ relativeBalance p N S (a+j • (d : ZMod p))
  have hbc : b₀ ≤ c₀ := affineCut_mono a.val L hd hNp
  have hce : c₀ ≤ e₀ := affineCut_mono a.val L hd (by omega : p ≤ p+N)
  have heL : e₀ ≤ L := affineCut_le _ _ _ _
  have hf (j : ℕ) (_ : j < L) : f j ≤ 1 :=
    (le_abs_self _).trans (relativeBalance_bound p N hN S hS _)
  have hzero (j : ℕ) (hj : j < L) (hno : ¬ (j < b₀ ∨ c₀ ≤ j ∧ j < e₀)) : f j = 0 := by
    apply relativeBalance_outside p N S hS
    intro hi
    have hv := (mem_intervalMask p N hNp _).mp hi
    rw [progression_val] at hv
    exact hno ((affine_interval_two_pieces a.val d p N L (ZMod.val_lt a) hd hspan hNp hj).mp hv)
  obtain ⟨s,m,hpiece,hm,hsize,hinc⟩ := positive_two_interval_piece f b₀ c₀ e₀ L
    hbc hce heL hL hf hzero hγ hmean
  rcases hpiece with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hcoords : ∀ j < b₀, (a+(0+j) • (d : ZMod p)).val = a.val+j*d ∧ a.val+j*d < N := by
      intro j hj
      rw [zero_add,progression_val]
      exact affine_first_piece a.val d p N L hd hNp hj
    refine ⟨a.val,b₀,hm,hsize,(fun j hj ↦ (hcoords j hj).2),?_⟩
    exact trace_density_of_relative_mean p N hNp S hS a d 0 a.val b₀ hm hcoords hinc
  · let b := a.val+c₀*d-p
    have hcoords : ∀ j < e₀-c₀, (a+(c₀+j) • (d : ZMod p)).val = b+j*d ∧ b+j*d < N := by
      intro j hj
      rw [progression_val]
      exact affine_second_piece a.val d p N L hd hNp hj
    refine ⟨b,e₀-c₀,hm,hsize,(fun j hj ↦ (hcoords j hj).2),?_⟩
    exact trace_density_of_relative_mean p N hNp S hS a d c₀ b (e₀-c₀) hm hcoords hinc

lemma progressionTrace_subset (S : Finset ℕ) (b d m : ℕ) : progressionTrace S b d m ⊆ range m := filter_subset _ _

lemma progressionTrace_free (S : Finset ℕ) {k : ℕ} (hk : 2 ≤ k)
    (hS : (S : Set ℕ).IsAPOfLengthFree k) (b d m : ℕ) (hd : 0 < d) :
    (progressionTrace S b d m : Set ℕ).IsAPOfLengthFree k := by
  apply (free_iff_not_hasNatAP hk).mpr
  rintro ⟨a,e,he,hmem⟩
  apply (free_iff_not_hasNatAP hk).mp hS
  refine ⟨b+a*d,e*d,Nat.mul_pos he hd,?_⟩
  intro i hi
  have hh : a+i*e ∈ progressionTrace S b d m := hmem i hi
  simp only [progressionTrace,mem_filter] at hh
  have hm := hh.2
  convert hm using 1 <;> ring

#print axioms interval_progression_rectification
#print axioms progressionTrace_free
end Erdos3IntervalProgressionRectification
