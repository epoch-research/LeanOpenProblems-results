import Submission.PrefixBalancedPaletteExplore

/-! Independent phase translations of mixed-prefix-controlled palette members.
The wraparound of endpoint intervals costs at most three prefix errors. -/
namespace Erdos66TranslatedPrefixPalette
open Erdos66OuterMixedPrefix Erdos66OuterCarryProfile Erdos66SaturatingCyclicFamily
  Erdos66PrefixBalancedPalette
open scoped Classical
set_option maxHeartbeats 2200000

variable (M : ℕ) [NeZero M]

noncomputable def shift (C : Finset (ZMod M)) (t : ZMod M) : Finset (ZMod M) :=
  C.image (fun x ↦ t+x)

@[simp] lemma mem_shift (C : Finset (ZMod M)) (t x : ZMod M) :
    x ∈ shift M C t ↔ x-t ∈ C := by
  simp only [shift, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x-t, hx, by abel⟩

@[simp] lemma shift_card (C : Finset (ZMod M)) (t : ZMod M) :
    (shift M C t).card = C.card :=
  Finset.card_image_of_injective _ (add_right_injective t)

@[simp] lemma shift_zero (C : Finset (ZMod M)) : shift M C 0 = C := by
  ext x
  simp

@[simp] lemma shift_shift (C : Finset (ZMod M)) (s t : ZMod M) :
    shift M (shift M C s) t = shift M C (t+s) := by
  ext x
  simp only [mem_shift]
  congr 1
  abel

@[simp] lemma shift_mean (C D : Finset (ZMod M)) (s t : ZMod M) :
    actualMean M (shift M C s) (shift M D t) = actualMean M C D := by
  simp only [actualMean, shift_card]

lemma shift_cyclicCount (C D : Finset (ZMod M)) (s t z : ZMod M) :
    cyclicCount M (shift M C s) (shift M D t) z = cyclicCount M C D (z-s-t) := by
  unfold cyclicCount
  rw [show shift M C s = C.image (fun x ↦ s+x) from rfl, Finset.filter_image, Finset.card_image_of_injective _ (add_right_injective s)]
  congr 1
  apply Finset.filter_congr
  intro x hx
  simp only [mem_shift]
  congr 1
  abel

lemma shift_prefix_formula (C D : Finset (ZMod M)) (s t z : ZMod M) (u : ℕ) :
    prefixCount M (shift M C s) (shift M D t) z u =
      (C.filter (fun x ↦ (s+x).val < u ∧ (z-s-t)-x ∈ D)).card := by
  unfold prefixCount
  rw [show shift M C s = C.image (fun x ↦ s+x) from rfl, Finset.filter_image, Finset.card_image_of_injective _ (add_right_injective s)]
  congr 1
  apply Finset.filter_congr
  intro x hx
  simp only [mem_shift]
  congr 2
  abel

lemma val_shift_lt_before (s x : ZMod M) (u : ℕ) (hu : u ≤ s.val) :
    (s+x).val < u ↔ M-s.val ≤ x.val ∧ x.val < M-s.val+u := by
  have hs := ZMod.val_lt s
  have hx := ZMod.val_lt x
  by_cases hh : s.val+x.val < M
  · rw [ZMod.val_add_of_lt hh]
    omega
  · rw [ZMod.val_add_of_le (by omega : M ≤ s.val+x.val)]
    omega

lemma val_shift_lt_after (s x : ZMod M) (u : ℕ) (hu : s.val < u) (huM : u ≤ M) :
    (s+x).val < u ↔ x.val < u-s.val ∨ M-s.val ≤ x.val := by
  have hs := ZMod.val_lt s
  have hx := ZMod.val_lt x
  by_cases hh : s.val+x.val < M
  · rw [ZMod.val_add_of_lt hh]
    omega
  · rw [ZMod.val_add_of_le (by omega : M ≤ s.val+x.val)]
    omega

lemma prefix_full (C D : Finset (ZMod M)) (z : ZMod M) :
    prefixCount M C D z M = cyclicCount M C D z := by
  unfold prefixCount cyclicCount
  congr 1
  apply Finset.filter_congr
  intro x hx
  simp only [ZMod.val_lt, true_and]

lemma shift_prefix_before (C D : Finset (ZMod M)) (s t z : ZMod M)
    (u : ℕ) (hu : u ≤ s.val) :
    prefixCount M (shift M C s) (shift M D t) z u =
      intervalCount M C D (z-s-t) (M-s.val) (M-s.val+u) := by
  rw [shift_prefix_formula, intervalCount]
  congr 1
  apply Finset.filter_congr
  intro x hx
  rw [val_shift_lt_before M s x u hu]
  tauto

lemma shift_prefix_after (C D : Finset (ZMod M)) (s t z : ZMod M)
    (u : ℕ) (hu : s.val < u) (huM : u ≤ M) :
    prefixCount M (shift M C s) (shift M D t) z u +
      prefixCount M C D (z-s-t) (M-s.val) =
      cyclicCount M C D (z-s-t) + prefixCount M C D (z-s-t) (u-s.val) := by
  let S := C.filter (fun x ↦ x.val < u-s.val ∧ (z-s-t)-x ∈ D)
  let T := C.filter (fun x ↦ M-s.val ≤ x.val ∧ x.val < M ∧ (z-s-t)-x ∈ D)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (Finset.mem_filter.mp hx).2.1
    have hy' := (Finset.mem_filter.mp hy).2.1
    omega
  have he : C.filter (fun x ↦ (s+x).val < u ∧ (z-s-t)-x ∈ D) = S ∪ T := by
    ext x
    simp only [S, T, Finset.mem_filter, Finset.mem_union,
      val_shift_lt_after M s x u hu huM, ZMod.val_lt, true_and, and_true]
    tauto
  rw [shift_prefix_formula, he, Finset.card_union_of_disjoint hd]
  change prefixCount M C D (z-s-t) (u-s.val) +
      intervalCount M C D (z-s-t) (M-s.val) M +
      prefixCount M C D (z-s-t) (M-s.val) = _
  have hh := intervalCount_add_prefix M C D (z-s-t) (M-s.val) M (Nat.sub_le _ _)
  rw [prefix_full] at hh
  omega

/-- A phase change on each factor costs at most three endpoint-prefix errors.
There is no density increase and no dependence on the two phases. -/
theorem shifted_prefix_error (C D : Finset (ZMod M)) (s t z : ZMod M)
    (u : ℕ) (hu : u ≤ M) (μ E : ℝ) (hE : 0 ≤ E)
    (hprefix : ∀ z v, v ≤ M →
      |(prefixCount M C D z v : ℝ) - (v : ℝ)/M*μ| ≤ E) :
    |(prefixCount M (shift M C s) (shift M D t) z u : ℝ) -
      (u : ℝ)/M*μ| ≤ 3*E := by
  have hs := (ZMod.val_lt s).le
  by_cases hus : u ≤ s.val
  · rw [shift_prefix_before M C D s t z u hus]
    have hv : M-s.val+u ≤ M := by omega
    have hh := interval_error_of_prefix_error M C D (z-s-t) (M-s.val) (M-s.val+u)
      (by omega) μ E (hprefix _ _ (Nat.sub_le _ _)) (hprefix _ _ hv)
    have he : (((M-s.val+u : ℕ) : ℝ) - (M-s.val : ℕ)) = u := by push_cast; ring
    rw [he] at hh
    linarith
  · have hus' : s.val < u := by omega
    have hc : (prefixCount M (shift M C s) (shift M D t) z u : ℝ) +
        prefixCount M C D (z-s-t) (M-s.val) =
        cyclicCount M C D (z-s-t) + prefixCount M C D (z-s-t) (u-s.val) := by
      exact_mod_cast shift_prefix_after M C D s t z u hus' hu
    have h₀ := hprefix (z-s-t) M le_rfl
    rw [prefix_full, div_self (by exact_mod_cast NeZero.ne M : (M : ℝ) ≠ 0), one_mul] at h₀
    have h₁ := hprefix (z-s-t) (M-s.val) (Nat.sub_le _ _)
    have h₂ := hprefix (z-s-t) (u-s.val) ((Nat.sub_le _ _).trans hu)
    have he : (u : ℝ)/M*μ = μ - (M-s.val : ℕ)/M*μ + (u-s.val : ℕ)/M*μ := by
      rw [Nat.cast_sub hs, Nat.cast_sub hus'.le]
      have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      field_simp [hMr]
      <;> ring
    rw [he, abs_le]
    rw [abs_le] at h₀ h₁ h₂
    constructor <;> linarith

end Erdos66TranslatedPrefixPalette
