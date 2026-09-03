import FormalConjecturesUtil
import Submission.DeterminantQuadraticIncidence
import Submission.ThetaOverlapAccounting

/-! The determinant-one quadratic family has rigid rows and C6-free
punctured column links, but this does not assert full theta exclusion. -/
open Finset
open scoped Classical
namespace Erdos713DeterminantQuadraticLinks
open Erdos713DeterminantQuadraticGeometry Erdos713DeterminantQuadraticIncidence
open Erdos713GlobalLight Erdos713ThetaCross Erdos713ThetaOverlap
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

lemma column_eq_of_parameter {p : Rows K} {x y : Cols K}
    (hx : incidence p x) (hy : incidence p y) (he : x.1 = y.1) : x = y := by
  apply Prod.ext he
  exact hx.symm.trans ((congrArg (eval (coeff p)) he).trans hy)

lemma parameter_ne {p : Rows K} {x y : Cols K}
    (hx : incidence p x) (hy : incidence p y) (hne : x ≠ y) : x.1 ≠ y.1 :=
  fun he => hne (column_eq_of_parameter hx hy he)

/-- Three distinct common columns identify a row. -/
theorem rigid_three {a b : Rows K} {x y z : Cols K}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hax : incidence a x) (hay : incidence a y) (haz : incidence a z)
    (hbx : incidence b x) (hby : incidence b y) (hbz : incidence b z) : a = b := by
  apply coeff_injective
  exact quad_eq_of_three (parameter_ne hay hax hxy.symm)
    (parameter_ne haz hax hxz.symm) (parameter_ne hay haz hyz)
    (hax.trans hbx.symm) (hay.trans hby.symm) (haz.trans hbz.symm)

/-- Explicit C4 exclusion in every punctured column link. -/
theorem column_four (u : Cols K) (a b : {a : Rows K // incidence a u})
    (x y : {x : Cols K // x ≠ u})
    (hax : incidence a.val x.val) (hay : incidence a.val y.val)
    (hbx : incidence b.val x.val) (hby : incidence b.val y.val) : a = b ∨ x = y := by
  by_cases hxy : x = y
  · exact Or.inr hxy
  left
  apply Subtype.ext
  exact rigid_three x.property.symm y.property.symm
    (fun he => hxy (Subtype.ext he)) a.property hax hay b.property hbx hby

/-- Explicit injective C6 exclusion in every punctured column link. -/
theorem column_hexagon (u : Cols K) (a : Fin 3 → Rows K) (b : Fin 3 → Cols K)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hroot : ∀ i, incidence (a i) u) (hout : ∀ i, b i ≠ u)
    (hdiag : ∀ i, incidence (a i) (b i))
    (hnext : ∀ i, incidence (a (i+1)) (b i)) : False := by
  have h20 : incidence (a 0) (b 2) := by simpa using hnext 2
  have h10 : incidence (a 1) (b 0) := by simpa using hnext 0
  have h21 : incidence (a 2) (b 1) := by simpa using hnext 1
  have he : coeff (a 0) = coeff (a 1) := by
    apply common_point_triangle (coeff_admissible _) (coeff_admissible _) (coeff_admissible (a 2))
      (parameter_ne (hdiag 0) (hroot 0) (hout 0))
      (parameter_ne h20 (hroot 0) (hout 2))
      (parameter_ne (hdiag 1) (hroot 1) (hout 1))
      (parameter_ne (hdiag 0) h20 (fun he => (by decide : (0 : Fin 3) ≠ 2) (hb he)))
      (parameter_ne h10 (hdiag 1) (fun he => (by decide : (0 : Fin 3) ≠ 1) (hb he)))
    · exact (hroot 0).trans (hroot 1).symm
    · exact (hroot 0).trans (hroot 2).symm
    · exact (hdiag 0).trans h10.symm
    · exact h20.trans (hdiag 2).symm
    · exact (hdiag 1).trans h21.symm
  exact (by decide : (0 : Fin 3) ≠ 1) (ha (coeff_injective he))

lemma light_count_upper [Fintype K] (hq : 4 ≤ Nat.card K) :
    lightCount (incidence (K := K)) ≤ 2*(Nat.card K)^5 := by
  let S : Finset (Cols K × Cols K) := univ.filter (fun p => p.1.1 = p.2.1)
  let T : Finset (Cols K × Cols K) := univ.filter (fun p => p.1.2.1 = p.2.2.1)
  have hsub : lightSet (incidence (K := K)) ⊆ S ∪ T := by
    intro p hp
    by_cases hs : p.1.1 = p.2.1
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hs⟩)
    · by_cases ht : p.1.2.1 = p.2.2.1
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ht⟩)
      · have hl := codegree_lower p.1 p.2 hs ht
        have hh := (mem_filter.mp hp).2
        omega
  have hS : S.card ≤ (Nat.card K)^5 := by
    let f : S → K × Vec K × Vec K := fun p => (p.val.1.1,p.val.1.2,p.val.2.2)
    have hi : Function.Injective f := by
      intro p q h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg (fun z : K × Vec K × Vec K => z.2.1) h
      have h3 := congrArg (fun z : K × Vec K × Vec K => z.2.2) h
      have hp := (mem_filter.mp p.property).2
      have hq := (mem_filter.mp q.property).2
      apply Subtype.ext
      exact Prod.ext (Prod.ext h1 h2) (Prod.ext (hp.symm.trans (h1.trans hq)) h3)
    have hh := Nat.card_le_card_of_injective f hi
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,
      Fintype.card_prod,Vec,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hh
  have hT : T.card ≤ (Nat.card K)^5 := by
    let f : T → (K × K) × (K × K × K) := fun p =>
      ((p.val.1.1,p.val.2.1),(p.val.1.2.1,p.val.1.2.2,p.val.2.2.2))
    have hi : Function.Injective f := by
      intro p q h
      have h1 := congrArg (fun z : (K × K) × (K × K × K) => z.1.1) h
      have h2 := congrArg (fun z : (K × K) × (K × K × K) => z.1.2) h
      have h3 := congrArg (fun z : (K × K) × (K × K × K) => z.2.1) h
      have h4 := congrArg (fun z : (K × K) × (K × K × K) => z.2.2.1) h
      have h5 := congrArg (fun z : (K × K) × (K × K × K) => z.2.2.2) h
      have hp := (mem_filter.mp p.property).2
      have hq := (mem_filter.mp q.property).2
      apply Subtype.ext
      exact Prod.ext (Prod.ext h1 (Prod.ext h3 h4))
        (Prod.ext h2 (Prod.ext (hp.symm.trans (h3.trans hq)) h5))
    have hh := Nat.card_le_card_of_injective f hi
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_prod,
      pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hh
  rw [← lightSet_card]
  have hh := (card_le_card hsub).trans (card_union_le S T)
  omega

#print axioms rigid_three
#print axioms column_four
#print axioms column_hexagon
#print axioms light_count_upper
end Erdos713DeterminantQuadraticLinks
