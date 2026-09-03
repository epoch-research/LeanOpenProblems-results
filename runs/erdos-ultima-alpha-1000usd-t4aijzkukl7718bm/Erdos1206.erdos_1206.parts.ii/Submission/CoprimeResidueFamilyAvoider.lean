import Submission.CoprimeResidueCollisions
import Submission.SummableDivisorCover

/-!
The explicit coprime, congruence-flexible, narrow family from the preceding
file is still too sparse to force a collision in every positive-density set:
all of its integer dilates can be excluded by a summable divisor sieve.
This does not exclude every cubic collision.
-/

namespace Erdos1206.CoprimeResidueCollisions
open scoped Classical
set_option maxHeartbeats 1000000

lemma A_quadratic_product_bound (k r : ℕ) :
    ((k+1)*(r+1))^2 ≤ A k (r+1) := by
  dsimp [A]
  ring_nf
  omega

lemma family_reciprocals_summable :
    Summable (fun x : ℕ × ℕ => (1 : ℝ)/A x.1 (x.2+1)) := by
  have hs : Summable (fun n : ℕ => (((n+1 : ℕ) : ℝ)^2)⁻¹) := by
    exact (summable_nat_add_iff 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  have hprod := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hprod
  intro x
  have hbound : (((x.1+1 : ℕ) : ℝ)*((x.2+1 : ℕ) : ℝ))^2 ≤ A x.1 (x.2+1) := by
    exact_mod_cast A_quadratic_product_bound x.1 x.2
  calc
    (1 : ℝ)/A x.1 (x.2+1) ≤
        1/((((x.1+1 : ℕ) : ℝ)*((x.2+1 : ℕ) : ℝ))^2) :=
      one_div_le_one_div_of_le (by positivity) hbound
    _ = _ := by simp [mul_pow, one_div, mul_comm]

/-- The first roots of the entire two-parameter family, not merely the
subfamily selected to satisfy the congruence and coprimality constraints. -/
def familyDivisors : Set ℕ := Set.range (fun x : ℕ × ℕ => A x.1 (x.2+1))

lemma familyDivisors_summable :
    Summable (fun n : ℕ => if n ∈ familyDivisors then (1 : ℝ)/n else 0) := by
  classical
  have hw (n : familyDivisors) : ∃ x : ℕ × ℕ, A x.1 (x.2+1)=n := n.2
  choose w hw using hw
  have hinj : Function.Injective w := by
    intro a b hab
    apply Subtype.ext
    rw [← hw a, ← hw b, hab]
  have hs := family_reciprocals_summable.comp_injective hinj
  have hs' : Summable (fun n : familyDivisors => (1 : ℝ)/(n : ℕ)) := by
    apply hs.congr
    intro n
    dsimp only [Function.comp_apply]
    rw [hw n]
  have hi := (summable_subtype_iff_indicator
    (f := fun n : ℕ => (1 : ℝ)/n) (s := familyDivisors)).mp hs'
  simpa only [Set.indicator_apply] using hi

lemma one_not_familyDivisors : 1 ∉ familyDivisors := by
  rintro ⟨⟨k,r⟩,he⟩
  change A k (r+1)=1 at he
  have hh := (ordered (k := k) (by omega : 0 < r+1)).1
  rw [he] at hh
  omega

/-- A positive-density source can avoid every dilate of every member of
this family, despite its arbitrary congruence and relative-width properties. -/
theorem positive_density_avoids_entire_family :
    ∃ S : Set ℕ, S.Infinite ∧ 0 < S.lowerDensity ∧
      ∀ k q t : ℕ, 0 < q → t*A k q ∉ S := by
  let S := divisorAvoider familyDivisors
  have hden : 0 < S.lowerDensity :=
    divisorAvoider_positive_density_of_summable one_not_familyDivisors familyDivisors_summable
  refine ⟨S, ?_, hden, ?_⟩
  · by_contra hfin
    have hz : S.lowerDensity=0 :=
      (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
    rw [hz] at hden
    exact (lt_irrefl 0) hden
  · intro k q t hq hn
    have hmem : A k q ∈ familyDivisors := by
      refine ⟨(k,q-1), ?_⟩
      dsimp
      rw [Nat.sub_add_cancel hq]
    exact hn.2 (A k q) hmem (dvd_mul_left _ _)

#print axioms family_reciprocals_summable
#print axioms positive_density_avoids_entire_family

end Erdos1206.CoprimeResidueCollisions
