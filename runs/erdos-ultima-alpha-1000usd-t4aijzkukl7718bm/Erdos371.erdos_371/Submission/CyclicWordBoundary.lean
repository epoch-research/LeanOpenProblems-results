import Submission.ComponentwiseCyclicSkewEnergy
import Submission.StationaryOddPrimeEnergy

/-! Fixed-window cyclic energies and their natural-prefix boundary errors. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory DilationSpectrum
open scoped Topology
set_option autoImplicit false

variable {A : Type*}

def cyclicWordOrbit (N : ℕ) [NeZero N] (L : ZMod N → A) (x : ZMod N) : ℕ → A :=
  fun k => L (x+(k : ZMod N))

noncomputable def cyclicWordMean (N : ℕ) [NeZero N] (L : ZMod N → A)
    (F : (ℕ → A) → ℝ) : ℝ := mean (uniformLaw (ZMod N)) (fun x => F (cyclicWordOrbit N L x))

lemma cyclicWordMean_prefix_error (N K : ℕ) [NeZero N] (L : ℕ → A)
    (F : (ℕ → A) → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    (hlocal : ∀ x y : ℕ → A, (∀ k, k ≤ K → x k=y k) → F x=F y) :
    |cyclicWordMean N (fun x => L x.val) F-prefixMean N (fun n => F (wordOrbit L n))| ≤
      2*B*K/N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold cyclicWordMean
  rw [mean_uniform_zmod_prefix]
  by_cases hKN : K ≤ N
  · apply prefixMean_tail_bound N K hKN _ _ B (fun n _ => hF _) (fun n _ => hF _)
    intro n hn
    apply hlocal
    intro k hk
    dsimp only [cyclicWordOrbit,wordOrbit]
    rw [← Nat.cast_add,ZMod.val_natCast,Nat.mod_eq_of_lt (by omega)]
  · have hh := abs_sub
      (prefixMean N (fun n => F (cyclicWordOrbit N (fun x => L x.val) (n : ZMod N))))
      (prefixMean N (fun n => F (wordOrbit L n)))
    have hb₁ := abs_prefixMean_le N hN
      (fun n => F (cyclicWordOrbit N (fun x => L x.val) (n : ZMod N))) B (fun n _ => hF _)
    have hb₂ := abs_prefixMean_le N hN (fun n => F (wordOrbit L n)) B (fun n _ => hF _)
    have hNK : (N : ℝ) ≤ K := by exact_mod_cast (show N ≤ K by omega)
    have hbound : 2*B ≤ 2*B*K/N := by
      apply (le_div_iff₀ hNr).mpr
      nlinarith [mul_le_mul_of_nonneg_left hNK (show 0 ≤ 2*B by positivity)]
    exact (hh.trans (add_le_add hb₁ hb₂)).trans (by linarith)

variable [Fintype A] [DecidableEq A]

noncomputable def labelIndicator (b a : A) : ℝ := if a=b then 1 else 0

lemma labelIndicator_unit (b a : A) : |labelIndicator b a| ≤ 1 := by
  unfold labelIndicator
  split_ifs <;> norm_num

lemma wordOddAverage_abs_le (R : ℕ) (P : Finset ℕ) (f : A → ℝ)
    (hf : ∀ a, |f a| ≤ 1) (x : ℕ → A) : |wordOddAverage R P f x| ≤ 2 := by
  by_cases hP : P.Nonempty
  · apply abs_finset_average_le P hP
    intro p _
    exact (abs_sub _ _).trans (by linarith [hf (x (R+p)),hf (x (R-p))])
  · simp [wordOddAverage,not_nonempty_iff_eq_empty.mp hP]

lemma wordOddAverage_square_le (R : ℕ) (P : Finset ℕ) (f : A → ℝ)
    (hf : ∀ a, |f a| ≤ 1) (x : ℕ → A) : |(wordOddAverage R P f x)^2| ≤ 4 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have hh := (sq_le_sq₀ (abs_nonneg (wordOddAverage R P f x)) (by norm_num : (0 : ℝ) ≤ 2)).mpr
    (wordOddAverage_abs_le R P f hf x)
  simpa only [sq_abs,show (2 : ℝ)^2=4 by norm_num] using hh

lemma wordOddAverage_local (R : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R)
    (f : A → ℝ) (x y : ℕ → A) (hxy : ∀ k, k ≤ 2*R → x k=y k) :
    wordOddAverage R P f x=wordOddAverage R P f y := by
  unfold wordOddAverage
  congr 1
  apply sum_congr rfl
  intro p hp
  rw [hxy (R+p) (by have := hP p hp; omega),hxy (R-p) (by omega)]

lemma cyclicOddIndicatorEnergy_eq_wordMean (N R : ℕ) [NeZero N]
    (L : ZMod N → A) (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) (b : A) :
    cyclicOddIndicatorEnergy N L P b =
      cyclicWordMean N L (fun x => (wordOddAverage R P (labelIndicator b) x)^2) := by
  have hp (x : ZMod N) : cyclicOddIndicatorAverage N L P b (x+(R : ZMod N)) =
      wordOddAverage R P (labelIndicator b) (cyclicWordOrbit N L x) := by
    unfold cyclicOddIndicatorAverage wordOddAverage labelIndicator cyclicWordOrbit
    congr 1
    apply sum_congr rfl
    intro p hp
    simp only [Nat.cast_add,Nat.cast_sub (hP p hp),add_assoc,add_sub_assoc]
  have hm := mean_uniform_addRight (fun x => (cyclicOddIndicatorAverage N L P b x)^2) (R : ZMod N)
  simpa only [hp,cyclicOddIndicatorEnergy,cyclicWordMean] using hm.symm

lemma cyclicOddIndicatorEnergy_prefix_error (N R : ℕ) [NeZero N]
    (L : ℕ → A) (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) (b : A) :
    |cyclicOddIndicatorEnergy N (fun x => L x.val) P b-
      prefixMean N (fun n => (wordOddAverage R P (labelIndicator b) (wordOrbit L n))^2)| ≤
        16*R/N := by
  rw [cyclicOddIndicatorEnergy_eq_wordMean N R _ P hP b]
  have h := cyclicWordMean_prefix_error N (2*R) L
    (fun x => (wordOddAverage R P (labelIndicator b) x)^2) 4 (by norm_num)
    (wordOddAverage_square_le R P _ (labelIndicator_unit b))
    (fun x y hxy => congrArg (fun z : ℝ => z^2) (wordOddAverage_local R P hP _ x y hxy))
  convert h using 1
  push_cast
  ring

#print axioms cyclicWordMean_prefix_error
#print axioms cyclicOddIndicatorEnergy_prefix_error
end Erdos371.FiniteInformation
