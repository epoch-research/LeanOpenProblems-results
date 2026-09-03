import Submission.CubicChecksumExample

/-!
Concatenating a genuinely square-Sidon seed need not preserve Sidonness.
This is a limitation of one amplification rule, not a disproof of Erdős 773.
-/
namespace Erdos773.SeedConcatenation
open Finset
set_option maxHeartbeats 2000000

/-- Base-B words, with their least significant letter chosen from A. -/
def words (A : Finset ℕ) (B : ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | k+1 => (A ×ˢ words A B k).image (fun p => p.1 + B*p.2)

lemma cons_mem {A : Finset ℕ} {B k a n : ℕ} (ha : a ∈ A) (hn : n ∈ words A B k) :
    a+B*n ∈ words A B (k+1) :=
  mem_image.mpr ⟨(a,n), mem_product.mpr ⟨ha,hn⟩,rfl⟩

lemma words_card (A : Finset ℕ) (B : ℕ) (hB : 0 < B) (hA : ∀ a ∈ A, a < B) (k : ℕ) :
    (words A B k).card = A.card ^ k := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    rw [words, Finset.card_image_of_injOn, card_product, ih, pow_succ']
    rintro ⟨a,n⟩ han ⟨b,m⟩ hbm he
    obtain ⟨ha,_hn⟩ := mem_product.mp han
    obtain ⟨hb,_hm⟩ := mem_product.mp hbm
    dsimp only at ha hb he
    have hre := congrArg (fun t : ℕ => t % B) he
    have hab : a = b := by
      simpa only [Nat.add_mod, Nat.mul_mod_right, add_zero,
        Nat.mod_eq_of_lt (hA a ha), Nat.mod_eq_of_lt (hA b hb)] using hre
    subst b
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left hB (Nat.add_left_cancel he))

lemma words_lt (A : Finset ℕ) (B : ℕ) (hA : ∀ a ∈ A, a < B) (k : ℕ) :
    ∀ n ∈ words A B k, n < B ^ k := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    intro n hn
    obtain ⟨⟨a,m⟩,ham,rfl⟩ := mem_image.mp hn
    obtain ⟨ha,hm⟩ := mem_product.mp ham
    have haB := hA a ha
    have hmB := ih m hm
    dsimp only
    rw [pow_succ']
    nlinarith

/-- The multiplier that repeats a two-letter block k times. -/
def multiplier (B k : ℕ) : ℕ := ∑ j ∈ range k, (B^2)^j

lemma multiplier_succ (B k : ℕ) : multiplier B (k+1) = 1+B^2*multiplier B k := by
  simp only [multiplier, sum_range_succ', pow_succ', ← mul_sum, pow_zero]
  omega

lemma multiplier_pos (B k : ℕ) (hk : 0 < k) : 0 < multiplier B k := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [multiplier_succ]
  omega

lemma repeat_mem (A : Finset ℕ) (B a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) (k : ℕ) :
    (a+B*b)*multiplier B k ∈ words A B (2*k) := by
  induction k with
  | zero => simp [multiplier, words]
  | succ k ih =>
    have hh := cons_mem ha (cons_mem hb ih)
    have he : (a+B*b)*multiplier B (k+1) = a+B*(b+B*((a+B*b)*multiplier B k)) := by
      rw [multiplier_succ]
      ring
    rw [he]
    convert hh using 1

private lemma seed_digits :
    10 ∈ CubicChecksumExample.roots ∧ 4 ∈ CubicChecksumExample.roots ∧
    51 ∈ CubicChecksumExample.roots ∧ 6 ∈ CubicChecksumExample.roots ∧
    21 ∈ CubicChecksumExample.roots ∧ 44 ∈ CubicChecksumExample.roots := by
  decide +kernel

/-- The seed is Sidon, but its two-block concatenation is not. The four roots
are 334=10+81*4, 537=51+81*6, 345=21+81*4, and 530=44+81*6. -/
theorem every_positive_even_length_fails (k : ℕ) (hk : 0 < k) :
    ¬ IsSidon (((words CubicChecksumExample.roots 81 (2*k)).image
      (fun n => n^2)) : Set ℕ) := by
  obtain ⟨h10,h4,h51,h6,h21,h44⟩ := seed_digits
  let g := multiplier 81 k
  have hg : 0 < g := multiplier_pos 81 k hk
  have hm₁ : 334*g ∈ words CubicChecksumExample.roots 81 (2*k) := by
    simpa using repeat_mem CubicChecksumExample.roots 81 10 4 h10 h4 k
  have hm₂ : 537*g ∈ words CubicChecksumExample.roots 81 (2*k) := by
    simpa using repeat_mem CubicChecksumExample.roots 81 51 6 h51 h6 k
  have hm₃ : 345*g ∈ words CubicChecksumExample.roots 81 (2*k) := by
    simpa using repeat_mem CubicChecksumExample.roots 81 21 4 h21 h4 k
  have hm₄ : 530*g ∈ words CubicChecksumExample.roots 81 (2*k) := by
    simpa using repeat_mem CubicChecksumExample.roots 81 44 6 h44 h6 k
  intro hS
  have hh := hS ((334*g)^2) (mem_image.mpr ⟨_,hm₁,rfl⟩)
    ((345*g)^2) (mem_image.mpr ⟨_,hm₃,rfl⟩)
    ((537*g)^2) (mem_image.mpr ⟨_,hm₂,rfl⟩)
    ((530*g)^2) (mem_image.mpr ⟨_,hm₄,rfl⟩) (by ring)
  have h₁ : (334*g)^2 < (345*g)^2 := by
    apply Nat.pow_lt_pow_left _ (by decide : 2 ≠ 0)
    omega
  have h₂ : (334*g)^2 < (530*g)^2 := by
    apply Nat.pow_lt_pow_left _ (by decide : 2 ≠ 0)
    omega
  rcases hh with h | h
  · exact h₁.ne h.1
  · exact h₂.ne h.1

/-- This attempted code has the desired formal size exponent, but it is not
Sidon for any positive even word length. -/
theorem seed_code_card (k : ℕ) :
    (words CubicChecksumExample.roots 81 k).card = 27^k := by
  rw [words_card _ _ (by decide) ?_ k, CubicChecksumExample.roots_card]
  intro a ha
  obtain ⟨r,_,rfl⟩ := mem_image.mp ha
  have hh := CubicChecksumExample.root_mem_interval r
  exact (mem_Icc.mp hh).2.trans_lt (by decide)

theorem seed_code_height (k : ℕ) :
    ∀ n ∈ words CubicChecksumExample.roots 81 k, n < 81^k := by
  apply words_lt
  intro a ha
  obtain ⟨r,_,rfl⟩ := mem_image.mp ha
  have hh := CubicChecksumExample.root_mem_interval r
  exact (mem_Icc.mp hh).2.trans_lt (by decide)

#print axioms words_card
#print axioms words_lt
#print axioms repeat_mem
#print axioms every_positive_even_length_fails
#print axioms seed_code_card
#print axioms seed_code_height
end Erdos773.SeedConcatenation
