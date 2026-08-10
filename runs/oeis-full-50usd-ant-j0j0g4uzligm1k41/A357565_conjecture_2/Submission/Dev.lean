import FormalConjectures.Util.ProblemImports

open Finset

/-- Abstract character-sum vanishing: if `f : G → R` is multiplicative on a finite group `G`
and `f a - 1` is a unit for some `a`, then `∑ x, f x = 0`. -/
lemma sum_eq_zero_of_mulHom {G : Type*} [Group G] [Fintype G] {R : Type*} [CommRing R]
    (f : G → R) (hf : ∀ x y, f (x * y) = f x * f y) (a : G) (ha : IsUnit (f a - 1)) :
    ∑ x, f x = 0 := by
  have reindex : ∑ x : G, f (a * x) = ∑ x : G, f x :=
    Fintype.sum_bijective (a * ·) (Group.mulLeft_bijective a) _ _ (fun x => rfl)
  have key : f a * ∑ x : G, f x = ∑ x : G, f x := by
    rw [Finset.mul_sum]
    rw [← reindex]
    exact Finset.sum_congr rfl (fun x _ => (hf a x).symm)
  have h0 : (f a - 1) * ∑ x : G, f x = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  exact (ha.mul_right_eq_zero).mp h0
