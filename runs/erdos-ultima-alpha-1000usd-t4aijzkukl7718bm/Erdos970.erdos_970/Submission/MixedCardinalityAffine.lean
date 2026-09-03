import Submission.CardinalityBlockBootstrap
import Submission.MixedPatternRescaling

/-! Affine mixed-population lower bounds from an already established
Jacobsthal bound. The source bound remains an explicit premise. -/
namespace Erdos970.MixedPattern
open Finset OptimalCoverCore CardinalityBootstrap

lemma real_floor_div_lower (n g : ℕ) (hg : 0 < g) :
    (n : ℝ)/(g : ℝ)-1 ≤ (n/g : ℕ) := by
  have he := Nat.mod_add_div n g
  have hm := Nat.mod_lt n hg
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have heR : ((n % g : ℕ) : ℝ)+(g : ℝ)*(n/g : ℕ) = n := by exact_mod_cast he
  have hmR : ((n % g : ℕ) : ℝ) < g := by exact_mod_cast hm
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hgR).mpr
  nlinarith

/-- Floor-many valid blocks give a real affine lower bound at every length. -/
theorem survivor_affine_lower {j g : ℕ} (h : IsJacobsthalBound j g) (hg : 0 < g)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (r : ℕ → ℕ) (n : ℕ) :
    ((j+1-B.card : ℕ) : ℝ)/(g : ℝ)*(n : ℝ)-((j+1-B.card : ℕ) : ℝ) ≤
      (survivors n B r).card := by
  have hh := count_lower_floor_blocks (m := n) h B hB r
  have hhR : ((n/g : ℕ) : ℝ)*((j+1-B.card : ℕ) : ℝ) ≤
      (survivors n B r).card := by exact_mod_cast hh
  have hf := mul_le_mul_of_nonneg_right (real_floor_div_lower n g hg)
    (Nat.cast_nonneg (j+1-B.card))
  have he : ((n : ℝ)/(g : ℝ)-1)*((j+1-B.card : ℕ) : ℝ) =
      ((j+1-B.card : ℕ) : ℝ)/(g : ℝ)*(n : ℝ)-((j+1-B.card : ℕ) : ℝ) := by ring
  rw [he] at hf
  exact hf.trans hhR

/-- One CRT progression plus its unit length error transfers the affine block
bound to simultaneous required and forbidden prime classes. -/
theorem mixedCount_affine_lower {j g : ℕ} (h : IsJacobsthalBound j g) (hg : 0 < g)
    (m : ℕ) (A B : Finset ℕ) (r : ℕ → ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hB : ∀ p ∈ B, p.Prime) (hd : Disjoint A B) :
    ((j+1-B.card : ℕ) : ℝ)/(g : ℝ)*
      ((m : ℝ)/(∏ p ∈ A, (p : ℝ))-1)-((j+1-B.card : ℕ) : ℝ) ≤
        (mixedCount m A B r : ℝ) := by
  obtain ⟨c,s,hcl,_,he⟩ := mixedCount_rescale m A B r hA hB hd
  have hD : 0 < ∏ p ∈ A, p := prod_pos (fun p hp => (hA p hp).pos)
  have hcR : ((m/(∏ p ∈ A, p) : ℕ) : ℝ) ≤ c := by exact_mod_cast hcl
  have hc : (m : ℝ)/(∏ p ∈ A, (p : ℝ))-1 ≤ c := by
    rw [← Nat.cast_prod]
    exact (real_floor_div_lower m (∏ p ∈ A, p) hD).trans hcR
  have hn : 0 ≤ ((j+1-B.card : ℕ) : ℝ)/(g : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hc hn
  have hs := survivor_affine_lower h hg B hB s c
  rw [he]
  linarith

#print axioms survivor_affine_lower
#print axioms mixedCount_affine_lower
end Erdos970.MixedPattern
