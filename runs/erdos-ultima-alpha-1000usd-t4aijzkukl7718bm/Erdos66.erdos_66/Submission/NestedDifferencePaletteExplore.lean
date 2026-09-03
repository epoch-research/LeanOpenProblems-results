import Submission.LogarithmicMixedFamilyExplore
import Submission.MixedDisjointAssemblyExplore

/-! Disjoint differences of nested mixed-flat families give cyclic palettes
that control every later nonnegative kernel entrywise. -/
namespace Erdos66NestedDifferencePalette
open Erdos66OriginRepair Erdos66LogarithmicMixedFamily Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 2400000

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma pairCount_diff_left {A B : Finset G} (hAB : A ⊆ B) (C : Finset G) (z : G) :
    pairCount (B\A) C z+pairCount A C z=pairCount B C z := by
  rw [←pairCount_union_left _ _ _ _ Finset.sdiff_disjoint,
    Finset.sdiff_union_of_subset hAB]

lemma pairCount_diff_right {A B : Finset G} (hAB : A ⊆ B) (C : Finset G) (z : G) :
    pairCount C (B\A) z+pairCount C A z=pairCount C B z := by
  simpa only [pairCount_comm] using pairCount_diff_left hAB C z

noncomputable def layer (C : ℕ → Finset G) (i : ℕ) : Finset G := C (i+1)\C i

lemma layers_disjoint (C : ℕ → Finset G) (hC : Monotone C) :
    Pairwise (fun i j ↦ Disjoint (layer C i) (layer C j)) := by
  intro i j hij
  wlog hlt : i<j generalizing i j
  · exact (this (i := j) (j := i) hij.symm (by omega)).symm
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hz0 := Finset.mem_sdiff.mp hz
  have hz1 := Finset.mem_sdiff.mp hz'
  exact hz1.2 (hC (show i+1 ≤ j by omega) hz0.1)

lemma layer_count_identity (C : ℕ → Finset G) (hC : Monotone C)
    (i j : ℕ) (z : G) :
    pairCount (layer C i) (layer C j) z+
      pairCount (C i) (C (j+1)) z+pairCount (C (i+1)) (C j) z =
      pairCount (C (i+1)) (C (j+1)) z+pairCount (C i) (C j) z := by
  have h₁ := pairCount_diff_left (hC (Nat.le_succ i)) (layer C j) z
  have h₂ := pairCount_diff_right (hC (Nat.le_succ j)) (C i) z
  have h₃ := pairCount_diff_right (hC (Nat.le_succ j)) (C (i+1)) z
  dsimp only [layer] at h₁ h₂ h₃ ⊢
  simp only [Nat.succ_eq_add_one] at h₁ h₂ h₃
  omega

lemma layer_count_error (C : ℕ → Finset G) (hC : Monotone C)
    (i j : ℕ) (z : G) (μ E : ℝ)
    (h00 : |(pairCount (C i) (C j) z:ℝ)-μ*i*j| ≤ E)
    (h10 : |(pairCount (C (i+1)) (C j) z:ℝ)-μ*(i+1)*j| ≤ E)
    (h01 : |(pairCount (C i) (C (j+1)) z:ℝ)-μ*i*(j+1)| ≤ E)
    (h11 : |(pairCount (C (i+1)) (C (j+1)) z:ℝ)-μ*(i+1)*(j+1)| ≤ E) :
    |(pairCount (layer C i) (layer C j) z:ℝ)-μ| ≤ 4*E := by
  have hid : (pairCount (layer C i) (layer C j) z:ℝ)+
      pairCount (C i) (C (j+1)) z+pairCount (C (i+1)) (C j) z =
      pairCount (C (i+1)) (C (j+1)) z+pairCount (C i) (C j) z := by
    exact_mod_cast layer_count_identity C hC i j z
  rw [abs_le] at h00 h10 h01 h11 ⊢
  constructor <;> nlinarith only [hid,h00.1,h00.2,h10.1,h10.2,h01.1,h01.2,h11.1,h11.2]

/-- The color count and accuracy are fixed before the arbitrarily large
cyclic modulus. Every pair of distinct or equal colors is controlled. -/
theorem exists_logarithmic_disjoint_cyclic_palette (c τ δ : ℝ)
    (hc : 0<c) (hτ : 0<τ) (hδ : 0<δ) (q N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ Odd M ∧ ∃ hM : NeZero M,
      ∃ μ : ℝ, 0<μ ∧ |μ/Real.log M-c|<τ ∧
        ∃ P : Fin q → Finset (ZMod M),
          Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
          ∀ i j : Fin q, ∀ z : ZMod M,
            |(cyclicCount M (P i) (P j) z:ℝ)-μ| ≤ δ*μ := by
  let η := min 1 (δ/(4*(q:ℝ)^2+1))
  have hη : 0<η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := min_le_left _ _
  have hbudget : 4*η*(q:ℝ)^2 ≤ δ := by
    have hb := (le_div_iff₀ (by positivity : 0<4*(q:ℝ)^2+1)).mp
      (min_le_right 1 (δ/(4*(q:ℝ)^2+1)))
    change η*(4*(q:ℝ)^2+1) ≤ δ at hb
    nlinarith only [hb,hη]
  obtain ⟨M,hMN,hModd,hM,μ,hμ,htune,C,hC0,hCmono,hC⟩ :=
    exists_logarithmic_mixed_family c τ η hc hτ hη hη1 q N₀
  letI := hM
  have hfixed (a b : ℕ) (ha : a ≤ q) (hb : b ≤ q) (z : ZMod M) :
      |(pairCount (C a) (C b) z:ℝ)-μ*a*b| ≤ η*μ*(q:ℝ)^2 := by
    have he := hC a ha b hb z
    change |(pairCount (C a) (C b) z:ℝ)-μ*a*b| ≤ η*(μ*a*b) at he
    have hab : (a:ℝ)*(b:ℝ) ≤ (q:ℝ)^2 := by
      have hh := mul_le_mul (show (a:ℝ) ≤ q by exact_mod_cast ha)
        (show (b:ℝ) ≤ q by exact_mod_cast hb) (Nat.cast_nonneg b) (Nat.cast_nonneg q)
      nlinarith only [hh]
    have hscale := mul_le_mul_of_nonneg_left hab (show 0 ≤ η*μ by positivity)
    exact he.trans (by nlinarith only [hscale])
  refine ⟨M,hMN,hModd,hM,μ,hμ,htune,(fun i ↦ layer C i.val),?_,?_⟩
  · intro i j hij
    exact layers_disjoint C hCmono (fun hv ↦ hij (Fin.ext hv))
  · intro i j z
    have hi := i.isLt
    have hj := j.isLt
    have he := layer_count_error C hCmono i.val j.val z μ (η*μ*(q:ℝ)^2)
      (hfixed _ _ (by omega) (by omega) z)
      (by simpa only [Nat.cast_add,Nat.cast_one] using hfixed (i.val+1) j.val (by omega) (by omega) z)
      (by simpa only [Nat.cast_add,Nat.cast_one] using hfixed i.val (j.val+1) (by omega) (by omega) z)
      (by simpa only [Nat.cast_add,Nat.cast_one] using hfixed (i.val+1) (j.val+1) (by omega) (by omega) z)
    change |(pairCount (layer C i.val) (layer C j.val) z:ℝ)-μ| ≤ δ*μ
    exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_right hbudget hμ.le])

end Erdos66NestedDifferencePalette
