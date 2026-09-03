import Submission.AffineQuadraticImageMass
import Submission.SquarefreeConicFamily

/-! Every whole-root cover of the squarefree primitive collision source has
divergent reciprocal cost, even when vertices are reused and the chosen
position varies. Proper-divisor covers are NOT ruled out. -/
namespace Erdos1206.SquarefreeWholeRootCoverMass
open Finset Filter SquarefreeConicFamily FiniteImageEnergy QuadraticImageMass
open scoped Classical Topology

private noncomputable def J : ℕ := AffineQuadraticImageMass.shift M 0 1
private noncomputable def bound (i : Fin 4) : ℕ :=
  (100*(BinaryQuadraticEnergy.coeffBound (c i) (b i) (a i)+1)+9)*(2^J)^2

lemma root_eval (i : Fin 4) :
    AffineQuadraticImageMass.eval (c i) (b i) (a i) M 0 1=roots i := by
  funext x
  dsimp [AffineQuadraticImageMass.eval,roots,F,QuadraticSquarefreeSieve.quad]
  ring

lemma trailing_pos (i : Fin 4) : 0<c i := by fin_cases i <;> norm_num [c]

lemma root_energy (i : Fin 4) (k : ℕ) :
    (equalPairs (grid k) (roots i)).card≤bound i*(k+(J+2))*(2^k)^2 := by
  have hd : 4*((c i):ℤ)*(a i)-((b i):ℤ)^2 ≠ 0 := by
    fin_cases i <;> norm_num [a,b,c]
  have hh := AffineQuadraticImageMass.equal_pairs_card_bound
    (c i) (b i) (a i) M 0 1 k modulus_pos hd
  rwa [root_eval i] at hh

/-- Even an arbitrary choice of one coordinate for each parameter pair has
nonsummable reciprocal mass on its DISTINCT selected values. -/
theorem selected_roots_not_summable (sel : ℕ × ℕ → Fin 4) :
    ¬ Summable (fun n : ℕ =>
      if n∈(fun x => roots (sel x) x) '' {x | Good x} then (1:ℝ)/n else 0) := by
  let H := 1000000*(M+1)
  let K := H^2
  let C := 4*∑i : Fin 4, bound i
  have hK : 0<K := by dsimp [K,H]; positivity
  have hC : 0<C := by
    dsimp [C]
    apply Nat.mul_pos (by decide)
    apply Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    change 0 < (100*(BinaryQuadraticEnergy.coeffBound (c i) (b i) (a i)+1)+9)*(2^J)^2
    exact Nat.mul_pos (by omega) (pow_pos (pow_pos (by decide) _) _)
  apply QuadraticImageMass.distinct_values_not_summable Good (fun x => roots (sel x) x)
    K C (J+2) hK hC (fun x _ => roots_pos (sel x) x)
  · intro x
    have hh := AffineQuadraticImageMass.eval_lower (c (sel x)) (b (sel x)) (a (sel x))
      M 0 1 (trailing_pos _) (coefficient_bounds _).1 modulus_pos x
    rwa [root_eval] at hh
  · intro k x hx
    have hh := roots_height (2^k) (by positivity) (sel x) hx
    change roots (sel x) x ≤ (1000000*(M+1))^2*(2^k)^2
    rw [← mul_pow]
    exact hh
  · intro k
    have hh := selector_energy (grid k) roots sel
    calc
      (equalPairs (grid k) (fun x => roots (sel x) x)).card ≤
          4*∑i : Fin 4, (equalPairs (grid k) (roots i)).card := by simpa using hh
      _ ≤ 4*∑i : Fin 4, bound i*(k+(J+2))*(2^k)^2 := by
        apply Nat.mul_le_mul_left
        exact sum_le_sum (fun i _ => root_energy i k)
      _ = C*(k+(J+2))*(2^k)^2 := by dsimp [C]; simp only [← sum_mul]; ring
  · have hh := (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(2:ℕ))).eventually
      good_eventually_large
    simpa only [good,grid,Nat.cast_pow,Nat.cast_ofNat] using hh

/-- Reusing whole roots does not make the cost summable. This strengthens the
maximum-root obstruction but says nothing about reusing proper divisors. -/
theorem no_summable_whole_root_cover (B : Set ℕ)
    (hB : ∀ e : Collision, ∃ i : Fin 4, e.val i∈B) :
    ¬ Summable (fun n : ℕ => if n∈B then (1:ℝ)/n else 0) := by
  have hex : ∀ x : ℕ × ℕ, ∃ i : Fin 4, Good x → roots i x∈B := by
    intro x
    by_cases hx : Good x
    · obtain ⟨i,hi⟩ := hB (collision ⟨x,hx⟩)
      exact ⟨i,fun _ => hi⟩
    · exact ⟨0,fun h => (hx h).elim⟩
  choose sel hsel using hex
  intro hs
  apply selected_roots_not_summable sel
  apply hs.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
  intro n
  by_cases hn : n∈(fun x => roots (sel x) x) '' {x | Good x}
  · obtain ⟨x,hx,rfl⟩ := hn
    have hh := hsel x hx
    simp [hh,Set.mem_image_of_mem (fun x => roots (sel x) x) hx]
  · simp only [if_neg hn]
    split_ifs <;> positivity

/-- Fractional whole-root covers have the same obstruction. The weights here
are on the roots themselves, NOT sums of weights over their divisors. -/
theorem no_summable_fractional_root_cover (w : ℕ → ℝ) (hw : ∀ n, 0≤w n)
    (hcover : ∀ e : Collision, (1:ℝ)≤∑i : Fin 4, w (e.val i)) :
    ¬ Summable (fun n : ℕ => w n/n) := by
  intro hs
  let B : Set ℕ := {n | 1/4≤w n}
  have hB : ∀ e : Collision, ∃ i : Fin 4, e.val i∈B := by
    intro e
    by_contra h
    push_neg at h
    have h0 : w (e.val 0)<1/4 := lt_of_not_ge (h 0)
    have h1 : w (e.val 1)<1/4 := lt_of_not_ge (h 1)
    have h2 : w (e.val 2)<1/4 := lt_of_not_ge (h 2)
    have h3 : w (e.val 3)<1/4 := lt_of_not_ge (h 3)
    have hh := hcover e
    rw [Fin.sum_univ_four] at hh
    linarith
  apply no_summable_whole_root_cover B hB
  apply (hs.mul_left 4).of_nonneg_of_le (fun n => by split_ifs <;> positivity)
  intro n
  by_cases hn : n∈B
  · simp only [if_pos hn]
    have hh : (1:ℝ)≤4*w n := by change 1/4≤w n at hn; linarith
    have hh' := div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)
    simpa only [mul_div_assoc] using hh'
  · simp only [if_neg hn]
    exact mul_nonneg (by norm_num) (div_nonneg (hw n) (Nat.cast_nonneg n))

#print axioms selected_roots_not_summable
#print axioms no_summable_whole_root_cover
#print axioms no_summable_fractional_root_cover
end Erdos1206.SquarefreeWholeRootCoverMass
