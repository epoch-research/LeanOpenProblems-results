import Submission.AsymmetricMixedEnergyExplore
import Submission.WeightedTranslateSelectionExplore

/-! Quadratically spaced parameter lengths with a uniform mixed error.
The spacing constant is independent of the largest selected level. -/
namespace Erdos66QuadraticLevelSelection
open Erdos66AsymmetricMixedEnergy Erdos66WeightedTranslateSelection
  Erdos66CharacterTranslateSelection Erdos66TranslatedCharacterEnergy
  Erdos66TranslatedMixedFiber Erdos66CrossGraph
open scoped Classical
set_option maxHeartbeats 2200000

 def level (D j : ℕ) : ℕ := D*(j+1)^2

lemma level_mono (D : ℕ) : Monotone (level D) := by
  intro i j hij
  exact Nat.mul_le_mul_left D (Nat.pow_le_pow_left (by omega) 2)

lemma level_pos (D j : ℕ) (hD : 0<D) : 0<level D j := by
  unfold level
  positivity

lemma level_ge (D j : ℕ) : D ≤ level D j := by
  unfold level
  have hh : 1 ≤ (j+1)^2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  nlinarith

lemma interval_l1_of_energy (p : ℕ) [Fact p.Prime] (a : ZMod p) (h k : ℕ)
    (hh : 1 ≤ h) (hhk : h ≤ k) (hk : k ≤ p) (e w : ℝ) (he : 0 ≤ e)
    (hE : (translatedEnergy (baseInterval p h) a:ℝ) ≤ w*(h:ℝ)^2)
    (hscale : 12*w ≤ e^4*(h:ℝ)) :
    (∑ z : ZMod p, |(crossCharFiber (intervalTranslate p a h) (intervalTranslate p a k) z:ℝ)|) ≤
      e*(h:ℝ)*(k:ℝ) := by
  have hL := interval_mixed_l1_fourth p a h k hh hhk hk
  have hE' := mul_le_mul_of_nonneg_left hE (show (0:ℝ) ≤ 12*(h:ℝ)*(k:ℝ)^4 by positivity)
  have hscale' := mul_le_mul_of_nonneg_right hscale (show (0:ℝ) ≤ (h:ℝ)^3*(k:ℝ)^4 by positivity)
  have hpow : (∑ z : ZMod p, |(crossCharFiber (intervalTranslate p a h) (intervalTranslate p a k) z:ℝ)|)^4 ≤
      (e*(h:ℝ)*(k:ℝ))^4 := by
    nlinarith only [hL,hE',hscale']
  have hs : (∑ z : ZMod p, |(crossCharFiber (intervalTranslate p a h) (intervalTranslate p a k) z:ℝ)|)^2 ≤
      (e*(h:ℝ)*(k:ℝ))^2 := by
    apply le_of_sq_le_sq _ (by positivity)
    convert hpow using 1 <;> ring
  exact le_of_sq_le_sq hs (by positivity)

 theorem exists_quadratic_level_parameters (e : ℝ) (he : 0<e) (D J p : ℕ)
    [Fact p.Prime] (hD : 0<D) (hscale : 96 ≤ (D:ℝ)*e^4)
    (hp : 8*level D J+3<p) :
    ∃ a : ZMod p,
      (∀ u∈intervalTranslate p a (2*level D J), u≠0) ∧
      (∀ u∈intervalTranslate p a (2*level D J), ∀ v∈intervalTranslate p a (2*level D J), u+v≠0) ∧
      ∀ i≤J, ∀ j≤J,
        (∑ z : ZMod p, |(crossCharFiber (intervalTranslate p a (2*level D i))
          (intervalTranslate p a (2*level D j)) z:ℝ)|) ≤
          e*(4*(level D i:ℝ)*(level D j:ℝ)) := by
  obtain ⟨a,hzero,hopp,hE⟩ := exists_weighted_admissible_intervals p (by omega)
    (2*level D J) (J+1) (by omega) (fun j ↦ 2*level D j)
    (fun j hj ↦ Nat.mul_le_mul_left 2 (level_mono D (by omega)))
  have hbound (i j : ℕ) (hi : i≤J) (hj : j≤J) (hij : i≤j) :
      (∑ z : ZMod p, |(crossCharFiber (intervalTranslate p a (2*level D i))
        (intervalTranslate p a (2*level D j)) z:ℝ)|) ≤
        e*(4*(level D i:ℝ)*(level D j:ℝ)) := by
    have hsc : 12*(16*((i:ℝ)+1)^2) ≤ e^4*(2*level D i:ℕ) := by
      have hm := mul_le_mul_of_nonneg_right hscale (sq_nonneg ((i:ℝ)+1))
      simp only [level,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      nlinarith only [hm]
    have hlen := level_mono D hj
    have hh := interval_l1_of_energy p a (2*level D i) (2*level D j)
      (by have := level_pos D i hD; omega)
      (Nat.mul_le_mul_left 2 (level_mono D hij)) (by omega)
      e (16*((i:ℝ)+1)^2) he.le (hE i (by omega)) hsc
    convert hh using 1 <;> push_cast <;> ring
  refine ⟨a,hzero,hopp,?_⟩
  intro i hi j hj
  rcases le_total i j with hij | hji
  · exact hbound i j hi hj hij
  · have hh := hbound j i hj hi hji
    have he (U V : Finset (ZMod p)) (z : ZMod p) : crossCharFiber U V z=crossCharFiber V U z := by
      unfold crossCharFiber
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      simp only [add_comm,mul_comm]
    simp_rw [he (intervalTranslate p a (2*level D i)) (intervalTranslate p a (2*level D j))]
    convert hh using 1 <;> ring

end Erdos66QuadraticLevelSelection
