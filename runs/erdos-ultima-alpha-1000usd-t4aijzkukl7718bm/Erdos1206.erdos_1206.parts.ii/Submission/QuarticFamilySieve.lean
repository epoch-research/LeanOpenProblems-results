import Submission.SparseHarmonic
import Submission.SummableDivisorCover

/-!
The explicit quartic family used to test the permutation charts is itself
avoidable at positive lower density. Its large cancellation factors alone
are therefore not a density obstruction.
-/
namespace Erdos1206
open scoped Classical

def quarticFamilyDivisors : Set ℕ :=
  Set.range (fun n : ℕ => 9*(n+1)^3+1)

lemma quarticFamilyDivisors_count (j : ℕ) :
    (quarticFamilyDivisors ∩ Set.Iio (16^j)).ncard ≤ 8^j := by
  let F := (Finset.range (8^j)).image (fun n : ℕ => 9*(n+1)^3+1)
  have hsub : quarticFamilyDivisors ∩ Set.Iio (16^j) ⊆ (F : Set ℕ) := by
    rintro x ⟨⟨n,rfl⟩,hx⟩
    have hn : n < 8^j := by
      by_contra hn
      have hle : 8^j ≤ n := by omega
      have hp := Nat.pow_le_pow_left hle 2
      have hbase : 16^j ≤ (8^j)^2 := by
        calc
          16^j ≤ 64^j := Nat.pow_le_pow_left (by decide) j
          _ = (8^j)^2 := by rw [← pow_mul, Nat.mul_comm j 2, pow_mul]; norm_num
      have hn2 : n^2 ≤ 9*(n+1)^3+1 := by nlinarith [Nat.zero_le (n^3)]
      have hx' : 9*(n+1)^3+1 < 16^j := hx
      omega
    change 9*(n+1)^3+1 ∈ (Finset.range (8^j)).image (fun m : ℕ => 9*(m+1)^3+1)
    exact Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hn,rfl⟩
  have hh := Set.ncard_le_ncard hsub F.finite_toSet
  rw [Set.ncard_coe_finset] at hh
  exact hh.trans ((Finset.card_image_le).trans (by simp))

lemma quarticFamilyDivisors_summable :
    Summable (fun n : ℕ => if n ∈ quarticFamilyDivisors then (1 : ℝ)/n else 0) := by
  apply summable_reciprocals_of_pow_prefix_bound (C := 1)
  intro j
  simpa using quarticFamilyDivisors_count j

/-- All integer dilations of this entire quartic family can be avoided
simultaneously by a set of strictly positive lower density. -/
theorem positive_density_avoids_quartic_family :
    ∃ A : Set ℕ, 0 < A.lowerDensity ∧
      ∀ t q : ℕ, 1 ≤ t → q*(9*t^3+1) ∉ A := by
  have h1 : 1 ∉ quarticFamilyDivisors := by
    rintro ⟨n,hn⟩
    have hp : 0 < (n+1)^3 := by positivity
    nlinarith
  refine ⟨divisorAvoider quarticFamilyDivisors,
    divisorAvoider_positive_density_of_summable h1 quarticFamilyDivisors_summable,?_⟩
  intro t q ht hmem
  have hm : 9*t^3+1 ∈ quarticFamilyDivisors := by
    refine ⟨t-1,?_⟩
    have he : t-1+1=t := by omega
    simp only [he]
  exact hmem.2 _ hm (dvd_mul_left _ q)

#print axioms quarticFamilyDivisors_summable
#print axioms positive_density_avoids_quartic_family
end Erdos1206
