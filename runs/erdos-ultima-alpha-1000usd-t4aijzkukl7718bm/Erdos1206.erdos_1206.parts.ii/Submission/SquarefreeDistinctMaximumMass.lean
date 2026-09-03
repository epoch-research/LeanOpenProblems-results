import Submission.AffineQuadraticImageMass
import Submission.SquarefreeConicFamily

/-! The maximum roots themselves, not merely the collision tuples, have
divergent reciprocal mass on a squarefree primitive cubic-collision source.
This rules out one maximum-root sieve, not arbitrary reusable divisor covers. -/
namespace Erdos1206.SquarefreeDistinctMaximumMass
open SquarefreeConicFamily
open scoped Classical

def maxima : Set ℕ := {n | ∃ e : Collision, e.val 3=n}

lemma family_distinct_maxima_not_summable :
    ¬ Summable (fun n : ℕ => if n∈(roots 3) '' {x | Good x} then (1:ℝ)/n else 0) := by
  have hf : AffineQuadraticImageMass.eval 797983 43324 589 M 0 1=roots 3 := by
    funext x
    dsimp [AffineQuadraticImageMass.eval,roots,F,QuadraticSquarefreeSieve.quad,a,b,c]
    ring
  have hh := AffineQuadraticImageMass.distinct_values_not_summable
    797983 43324 589 M 0 1 (by norm_num) (by norm_num) modulus_pos
    (by norm_num) Good
    (fun x _ => by rw [hf]; exact roots_pos 3 x)
    (by simpa only [good] using good_eventually_large)
  rwa [hf] at hh

/-- Every integer in this set is a distinct maximum root of a primitive,
squarefree, coprime-to-6 strict cubic collision. Their reciprocal series diverges. -/
theorem maxima_reciprocals_not_summable :
    ¬ Summable (fun n : ℕ => if n∈maxima then (1:ℝ)/n else 0) := by
  intro hs
  apply family_distinct_maxima_not_summable
  apply hs.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
  intro n
  by_cases hn : n∈(roots 3) '' {x | Good x}
  · obtain ⟨x,hx,rfl⟩ := hn
    have hm : roots 3 x∈maxima := ⟨collision ⟨x,hx⟩,rfl⟩
    simp [hm,Set.mem_image_of_mem (roots 3) hx]
  · simp only [if_neg hn]
    split_ifs <;> positivity

/-- No reciprocal-summable forbidden-divisor set can contain every primitive
maximum root, even on this restricted source. It may still cover collisions
by other roots or by proper divisors; those possibilities are not excluded. -/
theorem no_summable_maximum_cover (B : Set ℕ)
    (hB : ∀ e : Collision, e.val 3∈B) :
    ¬ Summable (fun n : ℕ => if n∈B then (1:ℝ)/n else 0) := by
  intro hs
  apply maxima_reciprocals_not_summable
  apply hs.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
  intro n
  by_cases hn : n∈maxima
  · obtain ⟨e,rfl⟩ := hn
    have hm : e.val 3∈maxima := ⟨e,rfl⟩
    simp [hm,hB e]
  · simp only [if_neg hn]
    split_ifs <;> positivity

#print axioms maxima_reciprocals_not_summable
#print axioms no_summable_maximum_cover
end Erdos1206.SquarefreeDistinctMaximumMass
