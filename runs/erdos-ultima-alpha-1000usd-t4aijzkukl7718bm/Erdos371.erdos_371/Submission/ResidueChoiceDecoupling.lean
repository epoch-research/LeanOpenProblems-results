import Submission.ResidueInformationConcentration

/-! Decoupling of a residue-selected position from the uniform position average.
The selected position is the unique one that shifts the residue to zero. -/

namespace Erdos371.FiniteInformation
open Finset

variable {α : Type*} [Fintype α]

lemma mean_sub (p : Law α) (F G : α → ℝ) :
    mean p (fun a => F a - G a) = mean p F - mean p G := by
  simp only [mean, mul_sub, sum_sub_distrib]

lemma mean_div (p : Law α) (F : α → ℝ) (c : ℝ) :
    mean p (fun a => F a / c) = mean p F / c := by
  simp only [mean, ← mul_div_assoc, ← sum_div]

lemma abs_mean_le_one (p : Law α) (F : α → ℝ) (hF : ∀ a, |F a| ≤ 1) :
    |mean p F| ≤ 1 := by
  calc
    _ ≤ ∑ a, |p a * F a| := abs_sum_le_sum_abs _ _
    _ = ∑ a, p a * |F a| := by simp only [abs_mul, abs_of_nonneg (p.nonneg _)]
    _ ≤ ∑ a, p a * 1 := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hF a) (p.nonneg a)
    _ = 1 := by simpa only [mul_one] using p.total

lemma mean_uniform_neg {G : Type*} [AddGroup G] [Fintype G] (F : G → ℝ) :
    mean (uniformLaw G) (fun y => F (-y)) = mean (uniformLaw G) F := by
  have h := mean_mapLaw (uniformLaw G) (Equiv.neg G) F
  rw [mapLaw_uniform_equiv] at h
  exact h.symm

/-- Centering and rescaling a unit-bounded position array yields a unit-bounded
observable with zero mean in the uniformly selected residue. -/
lemma centered_neg_choice (m : ℕ) [NeZero m] (F : ZMod m → ℝ)
    (hF : ∀ j, |F j| ≤ 1) :
    (∀ y, |(F (-y)-mean (uniformLaw (ZMod m)) F)/2| ≤ 1) ∧
    mean (uniformLaw (ZMod m))
      (fun y => (F (-y)-mean (uniformLaw (ZMod m)) F)/2) = 0 := by
  constructor
  · intro y
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have ht := abs_sub (F (-y)) (mean (uniformLaw (ZMod m)) F)
    linarith [hF (-y), abs_mean_le_one (uniformLaw (ZMod m)) F hF]
  · rw [mean_div, mean_sub, mean_uniform_neg, mean_const, sub_self, zero_div]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable (q : ι → ℕ) [∀ i, NeZero (q i)]

/-- The error of residue selection against the position average, using the
information of the full residue and the actual number of selected coordinates. -/
theorem residue_choice_sq_le_information
    (hcop : Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (M : ℕ) [NeZero M] (hd : (∏ i, q i) ∣ M)
    (P : Law (α × ZMod M)) (hP : secondMarginal P = uniformLaw (ZMod M))
    (F : α → ∀ i, ZMod (q i) → ℝ) (hF : ∀ a i j, |F a i j| ≤ 1) :
    (mean P (fun ay =>
      (∑ i, (F ay.1 i (-cyclicResidue M (q i) ay.2) -
        mean (uniformLaw (ZMod (q i))) (F ay.1 i))) / Fintype.card ι)) ^ 2 ≤
          8 * mutualInformation P / Fintype.card ι := by
  let G : α → ∀ i, ZMod (q i) → ℝ := fun a i y =>
    (F a i (-y)-mean (uniformLaw (ZMod (q i))) (F a i))/2
  have hh := residue_average_sq_le_information q hcop M hd P hP G
    (fun a i => (centered_neg_choice (q i) (F a i) (hF a i)).1)
    (fun a i => (centered_neg_choice (q i) (F a i) (hF a i)).2)
  have he : mean P (fun ay =>
      (∑ i, G ay.1 i (cyclicResidue M (q i) ay.2)) / Fintype.card ι) =
    mean P (fun ay =>
      (∑ i, (F ay.1 i (-cyclicResidue M (q i) ay.2) -
        mean (uniformLaw (ZMod (q i))) (F ay.1 i))) / Fintype.card ι) / 2 := by
    rw [← mean_div]
    congr 1
    funext ay
    dsimp [G]
    rw [← sum_div]
    ring
  rw [he] at hh
  convert (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 4)) using 1 <;> ring

#print axioms residue_choice_sq_le_information
end Erdos371.FiniteInformation
