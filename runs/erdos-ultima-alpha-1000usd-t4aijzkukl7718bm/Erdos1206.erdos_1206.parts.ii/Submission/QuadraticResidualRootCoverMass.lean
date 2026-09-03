import Submission.RoughSquarefreeWholeRootMass
import Submission.QuadraticFamilyResidualMass

/-! Whole-root and bounded-cofactor cover obstructions remain after deleting
finitely many rational quadratic families. These are not arbitrary proper-
divisor cover obstructions and do not settle the positive-density conjecture. -/
namespace Erdos1206.QuadraticResidualRootCoverMass
open FermatCubicConics QuadraticFamilyAvoidance QuadraticFamilyResidualMass
open RoughSquarefreeWholeRootMass
open PrimitiveCollisionMass (Collision)
open scoped Classical

abbrev Source {ι : Type*} (a b c d : ι → Vec) (Q : ℕ) :=
  {e : Collision // Outside a b c d e ∧
    (Squarefree e.val.1 ∧ Nat.Coprime e.val.1 Q) ∧
    (Squarefree e.val.2.1 ∧ Nat.Coprime e.val.2.1 Q) ∧
    (Squarefree e.val.2.2.1 ∧ Nat.Coprime e.val.2.2.1 Q) ∧
    (Squarefree e.val.2.2.2 ∧ Nat.Coprime e.val.2.2.2 Q)}

theorem no_summable_outside_root_cover {ι : Type*} [Finite ι]
    (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3)
    (Q : ℕ) (hQ : 0 < Q) (B : Set ℕ)
    (hB : ∀ e : Source a b c d Q, ∃ i : Fin 4, coordinate e.val i∈B) :
    ¬ Summable (fun n : ℕ => if n∈B then (1:ℝ)/n else 0) := by
  obtain ⟨H,hH,hbound⟩ := finite_uniform_gap_bound a b c d hc
  apply no_summable_residual_root_cover Q H hQ B
  intro e
  let f : Source a b c d Q := ⟨e.val,
    residual_outside a b c d H (fun i x hx => (hbound i x hx).1) ⟨e.val,e.property.1⟩,
    e.property.2⟩
  exact hB f

/-- DISTINCT maximum-root values still have divergent reciprocal mass. -/
theorem outside_maxima_not_summable {ι : Type*} [Finite ι]
    (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3)
    (Q : ℕ) (hQ : 0 < Q) :
    ¬ Summable (fun n : ℕ =>
      if n∈Set.range (fun e : Source a b c d Q => e.val.val.2.2.2) then (1:ℝ)/n else 0) := by
  apply no_summable_outside_root_cover a b c d hc Q hQ
  intro e
  exact ⟨3,e,rfl⟩

/-- Proper divisors with uniformly bounded cofactors cannot provide a
summable cover either. No bound is claimed for unbounded cofactors. -/
theorem no_summable_outside_bounded_cofactor_cover {ι : Type*} [Finite ι]
    (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3)
    (Q : ℕ) (hQ : 0 < Q) (B : Set ℕ) (G : ℕ)
    (hB : ∀ e : Source a b c d Q, ∃ i : Fin 4, ∃ g∈Finset.Icc 1 G,
      ∃ b∈B, coordinate e.val i=g*b) :
    ¬ Summable (fun n : ℕ => if n∈B then (1:ℝ)/n else 0) := by
  intro hs
  apply no_summable_outside_root_cover a b c d hc Q hQ
    (FiniteDilationMass.multiples B G) ?_ (FiniteDilationMass.multiples_summable hs G)
  intro e
  obtain ⟨i,g,hg,b,hb,he⟩ := hB e
  exact ⟨i,g,hg,b,hb,he.symm⟩

/-- Nonnegative fractional weights on the whole roots have divergent
reciprocal cost as well. Weights on arbitrary divisors are not covered. -/
theorem no_summable_outside_fractional_root_cover {ι : Type*} [Finite ι]
    (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3)
    (Q : ℕ) (hQ : 0 < Q) (w : ℕ → ℝ) (hw : ∀ n, 0≤w n)
    (hcover : ∀ e : Source a b c d Q, (1:ℝ)≤∑i : Fin 4, w (coordinate e.val i)) :
    ¬ Summable (fun n : ℕ => w n/n) := by
  intro hs
  let B : Set ℕ := {n | 1/4≤w n}
  have hB : ∀ e : Source a b c d Q, ∃ i : Fin 4, coordinate e.val i∈B := by
    intro e
    by_contra h
    push_neg at h
    have h0 : w (coordinate e.val 0)<1/4 := lt_of_not_ge (h 0)
    have h1 : w (coordinate e.val 1)<1/4 := lt_of_not_ge (h 1)
    have h2 : w (coordinate e.val 2)<1/4 := lt_of_not_ge (h 2)
    have h3 : w (coordinate e.val 3)<1/4 := lt_of_not_ge (h 3)
    have hh := hcover e
    rw [Fin.sum_univ_four] at hh
    linarith
  apply no_summable_outside_root_cover a b c d hc Q hQ B hB
  apply (hs.mul_left 4).of_nonneg_of_le (fun n => by split_ifs <;> positivity)
  intro n
  by_cases hn : n∈B
  · simp only [if_pos hn]
    have hh : (1:ℝ)≤4*w n := by change 1/4≤w n at hn; linarith
    have hh' := div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)
    simpa only [mul_div_assoc] using hh'
  · simp only [if_neg hn]
    exact mul_nonneg (by norm_num) (div_nonneg (hw n) (Nat.cast_nonneg n))

#print axioms no_summable_outside_root_cover
#print axioms outside_maxima_not_summable
#print axioms no_summable_outside_bounded_cofactor_cover
#print axioms no_summable_outside_fractional_root_cover
end Erdos1206.QuadraticResidualRootCoverMass
