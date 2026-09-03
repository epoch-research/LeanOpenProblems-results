import FormalConjecturesUtil

/-!
An elementary sharp root bound considered as a possible construction ingredient.
No graph construction or proof of Erdős714 is asserted.
-/
noncomputable section
open Classical Finset Polynomial
namespace Erdos714PowerQuadraticRoots
variable {F : Type*} [Field F]

/-- Both roots must have the same k-th power: otherwise their k-th powers
are the two roots of a quadratic, whose product would make b a k-th power. -/
lemma same_power (k : ℕ) (a b x y : F) (hb : ¬ ∃ z : F, z^k=b)
    (hx : (x^k)^2+a*x^k+b=0) (hy : (y^k)^2+a*y^k+b=0) :
    x^k=y^k := by
  by_contra hxy
  have hprod : (x^k-y^k)*(x^k+y^k+a)=0 := by linear_combination hx-hy
  have hs := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hxy)
  apply hb
  refine ⟨x*y, ?_⟩
  rw [mul_pow]
  linear_combination x^k*hs-hx

/-- A degree-2k polynomial can have at most k roots under the explicit
non-power condition on its constant coefficient. -/
theorem finite_root_bound (k : ℕ) (hk : 0 < k) (a b : F)
    (hb : ¬ ∃ z : F, z^k=b) (S : Finset F)
    (hS : ∀ x ∈ S, (x^k)^2+a*x^k+b=0) : S.card ≤ k := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x,hx⟩
  · simp
  · have hsub : S ⊆ (nthRoots k (x^k)).toFinset := by
      intro y hy
      rw [Multiset.mem_toFinset, mem_nthRoots hk]
      exact same_power k a b y x hb (hS y hy) (hS x hx)
    exact (card_le_card hsub).trans
      ((Multiset.toFinset_card_le _).trans (card_nthRoots k (x^k)))

lemma nonpower_ne_zero (k : ℕ) (hk : 0 < k) (b : F)
    (hb : ¬ ∃ z : F, z^k=b) : b ≠ 0 := by
  intro h
  apply hb
  exact ⟨0, by simp [h,hk.ne']⟩

lemma sharp_equation (k : ℕ) (b x : F) (hb : ¬ ∃ z : F, z^k=b) :
    (x^k)^2-(1+b)*x^k+b=0 ↔ x^k=1 := by
  have he : (x^k)^2-(1+b)*x^k+b=(x^k-1)*(x^k-b) := by ring
  rw [he, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  exact or_iff_left (fun h => hb ⟨x,h⟩)

variable [Fintype F]

def solutions (k : ℕ) (a b : F) : Finset F :=
  univ.filter (fun x => (x^k)^2+a*x^k+b=0)

/-- With all k-th roots of unity present, the full solution set has size
zero or exactly k. This is an all-root count, not a selected-root bound. -/
theorem solution_card_zero_or_k (k : ℕ) (hk : 0 < k) (a b ζ : F)
    (hb : ¬ ∃ z : F, z^k=b) (hζ : IsPrimitiveRoot ζ k) :
    (solutions k a b).card=0 ∨ (solutions k a b).card=k := by
  rcases (solutions k a b).eq_empty_or_nonempty with h | ⟨x,hx⟩
  · exact Or.inl (by rw [h]; rfl)
  · right
    have hx' := (mem_filter.mp hx).2
    have hx0 : x ≠ 0 := by
      intro hx0
      subst x
      have hb0 := nonpower_ne_zero k hk b hb
      simp only [zero_pow hk.ne', zero_pow (by decide : 2 ≠ 0), mul_zero,
        zero_add] at hx'
      exact hb0 hx'
    have he : solutions k a b = (nthRoots k (x^k)).toFinset := by
      ext y
      simp only [solutions, mem_filter, mem_univ, true_and,
        Multiset.mem_toFinset, mem_nthRoots hk]
      constructor
      · exact fun hy => same_power k a b y x hb hy hx'
      · intro hy
        rwa [hy]
    rw [he, Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup (pow_ne_zero k hx0)),
      hζ.card_nthRoots, if_pos ⟨x,rfl⟩]

/-- The upper bound is attained, so this arithmetic ingredient is compatible
with the necessary maximal-common-neighbor count. -/
theorem sharp_card (k : ℕ) (hk : 0 < k) (b ζ : F)
    (hb : ¬ ∃ z : F, z^k=b) (hζ : IsPrimitiveRoot ζ k) :
    (solutions k (-(1+b)) b).card=k := by
  have hone : (1 : F) ∈ solutions k (-(1+b)) b := by
    simp [solutions]
  rcases solution_card_zero_or_k k hk (-(1+b)) b ζ hb hζ with h | h
  · have hp := card_pos.mpr ⟨1,hone⟩
    omega
  · exact h

/-- A nontrivial k-th root of unity guarantees that the power map is not
surjective on a finite field. No choice of a non-power is assumed here. -/
theorem exists_nonpower (k : ℕ) (hk : 1 < k) (ζ : F)
    (hζ : IsPrimitiveRoot ζ k) : ∃ b : F, ¬ ∃ z : F, z^k=b := by
  by_contra! h
  have hi : Function.Injective (fun z : F => z^k) :=
    Finite.injective_iff_surjective.mpr h
  apply hζ.ne_one hk
  apply hi
  simpa only [one_pow] using hζ.pow_eq_one

#print axioms same_power
#print axioms finite_root_bound
#print axioms solution_card_zero_or_k
#print axioms sharp_card
#print axioms exists_nonpower
end Erdos714PowerQuadraticRoots
