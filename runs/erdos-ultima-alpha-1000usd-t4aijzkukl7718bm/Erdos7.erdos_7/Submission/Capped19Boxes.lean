import Submission.Capped19Schedule

/-! Geometric box avoidance through prime 19, with arbitrary finite exponents. -/
namespace Erdos7Capped19Schedule
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7Capped19Rows Erdos7Capped19Real
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable (A : Fin 7 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
variable (E : Fin 7 → ℕ)

lemma not_full_cover (X : Pattern E → ∀ i,Finset (A i)) (ρ : ∀ i,A i → ℝ)
    (hρ : ∀ i y,0 ≤ ρ i y) (hρmass : ∀ i,(∑ y,ρ i y) = 1)
    (hd : ∀ i k,exponent E k i ≠ 0 →
      (∑ y,if y ∈ X k i then ρ i y else 0) ≤ 1/(primes i:ℝ)^(exponent E k i)) :
    ¬ (∀ x,∃ k : Pattern E,(∃ i,exponent E k i ≠ 0) ∧
      indicator A 7 (exponent E k) (X k) x = 1) := by
  apply (schedule A E X ρ hρ hρmass hd).not_full_cover
  · change potential 7 = fun _ => 0
    simpa only [potential,show ¬(7:ℕ) = 0 by omega,if_false,forms] using evalR_terminal
  · change potential 0 1 < 1
    simpa only [potential,if_true] using (show (rootValue:ℝ) < 1 by exact_mod_cast rootValue_lt_one)

/-- Missing exponent patterns are padded by empty boxes, not by extra classes. -/
theorem distinct_box_not_cover {κ : Type} [Fintype κ]
    (e : κ → Fin 7 → ℕ) (he : Function.Injective e) (heE : ∀ k i,e k i ≤ E i)
    (he0 : ∀ k,∃ i,e k i ≠ 0) (X : κ → ∀ i,Finset (A i))
    (ρ : ∀ i,A i → ℝ) (hρ : ∀ i y,0 ≤ ρ i y) (hρmass : ∀ i,(∑ y,ρ i y) = 1)
    (hd : ∀ k i,e k i ≠ 0 →
      (∑ y,if y ∈ X k i then ρ i y else 0) ≤ 1/(primes i:ℝ)^(e k i)) :
    ¬ (∀ x : ∀ i,A i,∃ k,∀ i,e k i ≠ 0 → x i ∈ X k i) := by
  classical
  let X' (k : Pattern E) (i : Fin 7) : Finset (A i) :=
    if h : ∃ l,e l = exponent E k then X h.choose i else ∅
  have hd' (i : Fin 7) (k : Pattern E) (hi : exponent E k i ≠ 0) :
      (∑ y,if y ∈ X' k i then ρ i y else 0) ≤ 1/(primes i:ℝ)^exponent E k i := by
    dsimp only [X']
    split_ifs with h
    · have hh := hd h.choose i (by rw [congrFun h.choose_spec i]; exact hi)
      simpa only [congrFun h.choose_spec i] using hh
    · simp only [Finset.notMem_empty,if_false,Finset.sum_const_zero]
      positivity
  intro hcover
  apply not_full_cover A E X' ρ hρ hρmass hd'
  intro x
  obtain ⟨k,hk⟩ := hcover x
  let l : Pattern E := fun i => ⟨e k i,by have := heE k i; omega⟩
  have hl : exponent E l = e k := rfl
  have hex : ∃ j,e j = exponent E l := ⟨k,rfl⟩
  have hchoice : hex.choose = k := he (hex.choose_spec.trans hl)
  have hX : X' l = X k := by funext i; simp only [X',dif_pos hex,hchoice]
  refine ⟨l,by simpa only [hl] using he0 k,?_⟩
  rw [hX]
  dsimp only [indicator]
  rw [project_full,hl,Erdos7Distortion.boxIndicator,if_pos]
  · norm_num
  · intro i hi
    exact hk i ((Erdos7CompressionSieve.mem_expSupport _ _).mp hi)

#print axioms distinct_box_not_cover
end Erdos7Capped19Schedule
