import FormalConjecturesUtil
import Submission.C8CommutingDifferences

/-! C8 exclusion forces a small difference set when equal projection fibers
commute. This is an auxiliary construction diagnostic. -/
open SimpleGraph Finset
namespace Erdos713C8FiberDifferences
open Erdos713C8CommutingDifferences
variable {G K : Type*} [Group G] [Field K] [CharP K 2]
set_option maxHeartbeats 2000000

lemma commutator_copy (φ : G → K) (hφ1 : φ 1 = 0)
    (hφmul : ∀ x y, φ (x*y) = φ x+φ y)
    (g : K → G) (hφg : ∀ a, φ (g a) = a)
    (t u : K) (ht : t ≠ 0) (hu : u ≠ 0) (hut : u ≠ t)
    (hc : Commute (g 0*(g t)⁻¹) (g u*(g (u+t))⁻¹))
    (hne : g 0*(g t)⁻¹ ≠ g u*(g (u+t))⁻¹)
    (hp : (g 0*(g t)⁻¹)*(g u*(g (u+t))⁻¹) ≠ 1) :
    cycleGraph 8 ⊑ graph g := by
  let X := g 0*(g t)⁻¹
  let Y := g u*(g (u+t))⁻¹
  have hX : φ X = t := by
    simp only [X,hφmul,coord_inv φ hφ1 hφmul,hφg,zero_add,CharTwo.neg_eq]
  have hY : φ Y = t := by
    simp only [Y,hφmul,coord_inv φ hφ1 hφmul,hφg,CharTwo.neg_eq]
    linear_combination u*(CharTwo.two_eq_zero (R := K))
  have hXY : φ (X*Y) = 0 := by
    rw [hφmul,hX,hY]
    exact CharTwo.add_self_eq_zero t
  have htu : t+u ≠ 0 := by
    rw [add_comm,← CharTwo.sub_eq_add]
    exact sub_ne_zero.mpr hut
  let p : Fin 4 → G := ![1,X,X*Y,Y]
  let l : Fin 4 → G := ![g 0,X*g u,Y*g 0,g u]
  have hpi : Function.Injective p := by
    intro i j he
    have hf := congrArg φ he
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [p] at he hf
      simp only [hφ1,hX,hY,hXY] at hf
      first | exact (ht hf).elim | exact (ht hf.symm).elim |
        exact (hne he).elim | exact (hne he.symm).elim |
        exact (hp he).elim | exact (hp he.symm).elim)
  have hli : Function.Injective l := by
    intro i j he
    have hf := congrArg φ he
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [l] at hf
      simp only [hφmul,hX,hY,hφg,add_zero] at hf
      first | exact (ht hf).elim | exact (ht hf.symm).elim |
        exact (hu hf).elim | exact (hu hf.symm).elim |
        exact (hut hf).elim | exact (hut hf.symm).elim |
        exact (htu hf).elim | exact (htu hf.symm).elim |
        (exfalso; apply ht; linear_combination hf) |
        (exfalso; apply ht; linear_combination -hf) |
        (exfalso; apply hu; linear_combination hf) |
        (exfalso; apply hu; linear_combination -hf))
  have hXt : X*g t = g 0 := by simp [X]
  have hYut : Y*g (u+t) = g u := by simp [Y]
  apply contains_of_octagon g p l hpi hli
  · intro i
    fin_cases i
    · exact ⟨0,(one_mul _).symm⟩
    · exact ⟨u,rfl⟩
    · refine ⟨t,?_⟩
      change Y*g 0 = (X*Y)*g t
      rw [hc.eq,mul_assoc Y X (g t),hXt]
    · exact ⟨u+t,hYut.symm⟩
  · intro i
    fin_cases i
    · exact ⟨t,hXt.symm⟩
    · refine ⟨u+t,?_⟩
      change X*g u = (X*Y)*g (u+t)
      rw [mul_assoc X Y (g (u+t)),hYut]
    · exact ⟨0,rfl⟩
    · exact ⟨u,(one_mul _).symm⟩

lemma difference_dichotomy (φ : G → K) (hφ1 : φ 1 = 0)
    (hφmul : ∀ x y, φ (x*y) = φ x+φ y)
    (g : K → G) (hφg : ∀ a, φ (g a) = a)
    (hc : ∀ x y, φ x = φ y → Commute x y) (hf : (cycleGraph 8).Free (graph g))
    (a b : K) :
    g a*(g b)⁻¹ = g 0*(g (a+b))⁻¹ ∨
      g a*(g b)⁻¹ = (g 0*(g (a+b))⁻¹)⁻¹ := by
  by_cases ha : a = 0
  · subst a
    exact Or.inl (by simp)
  by_cases hb : b = 0
  · subst b
    exact Or.inr (by simp)
  by_cases hab : a = b
  · subst b
    exact Or.inl (by simp [CharTwo.add_self_eq_zero])
  have ht : a+b ≠ 0 := by rw [← CharTwo.sub_eq_add]; exact sub_ne_zero.mpr hab
  have hat : a ≠ a+b := by intro h; apply hb; linear_combination -h
  have hbt : a+(a+b) = b := by
    linear_combination a*(CharTwo.two_eq_zero (R := K))
  by_contra! hn
  let X := g 0*(g (a+b))⁻¹
  let Y := g a*(g b)⁻¹
  have hX : φ X = a+b := by
    simp only [X,hφmul,coord_inv φ hφ1 hφmul,hφg,zero_add,CharTwo.neg_eq]
  have hY : φ Y = a+b := by
    simp only [Y,hφmul,coord_inv φ hφ1 hφmul,hφg,CharTwo.neg_eq]
  have hcomm : Commute X Y := hc X Y (hX.trans hY.symm)
  have hne : X ≠ Y := Ne.symm hn.1
  have hprod : X*Y ≠ 1 := by
    intro h
    apply hn.2
    change Y = X⁻¹
    calc
      Y = X⁻¹*(X*Y) := by group
      _ = X⁻¹ := by rw [h,mul_one]
  apply hf
  apply commutator_copy φ hφ1 hφmul g hφg (a+b) a ht ha hat
  · simpa only [hbt] using hcomm
  · simpa only [hbt] using hne
  · simpa only [hbt] using hprod

open scoped Classical in
noncomputable def differences [Fintype K] (g : K → G) : Finset G :=
  (univ : Finset (K × K)).image (fun p => g p.1*(g p.2)⁻¹)

lemma differences_card [Fintype K] (φ : G → K) (hφ1 : φ 1 = 0)
    (hφmul : ∀ x y, φ (x*y) = φ x+φ y)
    (g : K → G) (hφg : ∀ a, φ (g a) = a)
    (hc : ∀ x y, φ x = φ y → Commute x y) (hf : (cycleGraph 8).Free (graph g)) :
    (differences g).card ≤ 2*Fintype.card K := by
  classical
  let D : K → Finset G := fun t => {g 0*(g t)⁻¹,(g 0*(g t)⁻¹)⁻¹}
  have hsub : differences g ⊆ univ.biUnion D := by
    intro x hx
    obtain ⟨⟨a,b⟩,_,rfl⟩ := mem_image.mp hx
    apply mem_biUnion.mpr
    refine ⟨a+b,mem_univ _,?_⟩
    simpa only [D,mem_insert,mem_singleton] using
      difference_dichotomy φ hφ1 hφmul g hφg hc hf a b
  calc
    _ ≤ (univ.biUnion D).card := card_le_card hsub
    _ ≤ ∑ t : K, (D t).card := card_biUnion_le
    _ ≤ ∑ _t : K, 2 := sum_le_sum (fun _ _ => card_le_two)
    _ = _ := by simp [Nat.mul_comm]

#print axioms commutator_copy
#print axioms difference_dichotomy
#print axioms differences_card
end Erdos713C8FiberDifferences
