import Submission.Explore

/-! A base-four digit core creates exponentially large representation peaks.
This excludes the threshold-walk candidate examined during development; it
is not a disproof of the existential conjecture. -/
namespace Erdos66DigitCore
open Filter AdditiveCombinatorics Erdos66Explore
open scoped Topology Classical

noncomputable def core : ℕ → Finset ℕ
  | 0 => {0}
  | k+1 => (core k).image (fun a ↦ 4*a) ∪ (core k).image (fun a ↦ 4*a+2)

def center : ℕ → ℕ
  | 0 => 0
  | k+1 => 4*center k+2

lemma card_core (k : ℕ) : (core k).card = 2^k := by
  induction k with
  | zero => simp [core]
  | succ k ih =>
    have hd : Disjoint ((core k).image (fun a ↦ 4*a))
        ((core k).image (fun a ↦ 4*a+2)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hy
      omega
    rw [core, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (by intro a b h; dsimp at h; omega),
      Finset.card_image_of_injective _ (by intro a b h; dsimp at h; omega), ih, pow_succ]
    omega

lemma core_reflection (k : ℕ) : ∀ a ∈ core k, a ≤ center k ∧ center k-a ∈ core k := by
  induction k with
  | zero => simp [core,center]
  | succ k ih =>
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hle,hm⟩ := ih b hb
      constructor
      · simp only [center]; omega
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨center k-b,hm,?_⟩
        simp only [center]
        omega
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hle,hm⟩ := ih b hb
      constructor
      · simp only [center]; omega
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨center k-b,hm,?_⟩
        simp only [center]
        omega

lemma core_peak {A : Set ℕ} (k : ℕ) (hA : ∀ a ∈ core k, a ∈ A) :
    2^k ≤ sumRep A (center k) := by
  let f : ℕ → ℕ × ℕ := fun a ↦ (a,center k-a)
  have hf : Function.Injective f := fun a b h ↦ congrArg Prod.fst h
  have hs : (core k).image f ⊆ (Finset.antidiagonal (center k)).filter
      (fun p : ℕ × ℕ ↦ p.1 ∈ A ∧ p.2 ∈ A) := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hle,hm⟩ := core_reflection k a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (by dsimp [f]; omega),
      hA a ha,hA _ hm⟩
  rw [← card_core k, ← Finset.card_image_of_injective (core k) hf]
  exact (Finset.card_le_card hs).trans_eq (sumRep_def A (center k)).symm

lemma center_bounds (k : ℕ) : k ≤ center k ∧ center k < 4^k := by
  induction k with
  | zero => simp [center]
  | succ k ih =>
    simp only [center,pow_succ]
    constructor <;> omega

lemma square_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k^2 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ (2 : ℕ) k]
    nlinarith

/-- No set containing every base-four 0/2 digit block can have a finite
logarithmically normalized representation limit. -/
theorem core_excludes_finite_limit {A : Set ℕ}
    (hA : ∀ k a, a ∈ core k → a ∈ A) (c : ℝ) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro h
  obtain ⟨M,hM⟩ := eventually_atTop.mp (h.eventually_lt_const (lt_add_one c))
  obtain ⟨K,hK⟩ := exists_nat_gt ((c+1)*Real.log 4)
  let k := max (max M K) 4
  have hk4 : 4 ≤ k := le_max_right _ _
  have hkM : M ≤ k := (le_max_left M K).trans (le_max_left _ _)
  have hkK : K ≤ k := (le_max_right M K).trans (le_max_left _ _)
  have hcenter := center_bounds k
  have hlog : 0 < Real.log (center k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < center k by omega))
  have hu : (sumRep A (center k) : ℝ) < (c+1)*Real.log (center k) :=
    (div_lt_iff₀ hlog).mp (hM _ (hkM.trans hcenter.1))
  have hl : ((k : ℝ)^2) ≤ (sumRep A (center k) : ℝ) := by
    exact_mod_cast (square_le_two_pow hk4).trans (core_peak k (hA k))
  have hc : 0 ≤ c+1 := by linarith [limit_nonneg h]
  have hh : Real.log (center k : ℝ) ≤ (k : ℝ)*Real.log 4 := by
    calc
      _ ≤ Real.log ((4 : ℝ)^k) := Real.log_le_log
        (by exact_mod_cast (show 0 < center k by omega))
        (by exact_mod_cast hcenter.2.le)
      _ = _ := Real.log_pow _ _
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkk : (c+1)*Real.log 4 < (k : ℝ) :=
    hK.trans_le (by exact_mod_cast hkK)
  have hupper := mul_le_mul_of_nonneg_left hh hc
  nlinarith

end Erdos66DigitCore
