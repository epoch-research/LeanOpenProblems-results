import FormalConjecturesUtil
import Submission.C8FiberDifferences
import Submission.KST

/-! A dense local graph excludes large C8-free Cayley sections with commuting
projection fibers. Auxiliary construction obstruction only. -/
open SimpleGraph Finset
namespace Erdos713C8SmallDifferenceCayley
open Erdos713C8CommutingDifferences Erdos713C8FiberDifferences
variable {G K : Type*} [Group G] [Fintype K]
set_option maxHeartbeats 2000000

open scoped Classical in
def localGraph (g : K → G) : SimpleGraph ((differences g) ⊕ K) where
  Adj v w := match v,w with
    | .inl x,.inr a => Inc g x.val (g a)
    | .inr a,.inl x => Inc g x.val (g a)
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact id

lemma local_contained (g : K → G) (hg : Function.Injective g) : localGraph g ⊑ graph g := by
  classical
  let f : (differences g) ⊕ K → G ⊕ G := Sum.map Subtype.val g
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro x y h
    cases x <;> cases y <;> exact h
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
      | inr y => simp [f] at h
    | inr x =>
      cases y with
      | inl y => simp [f] at h
      | inr y => exact congrArg Sum.inr (hg (Sum.inr.inj h))

open scoped Classical in
lemma right_degree (g : K → G) (hg : Function.Injective g) (a : K) :
    (localGraph g).degree (Sum.inr a) = Fintype.card K := by
  classical
  let f : K → (localGraph g).neighborSet (Sum.inr a) := fun b =>
    ⟨Sum.inl ⟨g a*(g b)⁻¹,mem_image.mpr ⟨(a,b),mem_univ _,rfl⟩⟩,
      ⟨b,by simp⟩⟩
  have hfi : Function.Injective f := by
    intro b c h
    have he : g a*(g b)⁻¹ = g a*(g c)⁻¹ :=
      congrArg Subtype.val (Sum.inl.inj (congrArg Subtype.val h))
    exact hg (inv_injective (mul_left_cancel he))
  have hfs : Function.Surjective f := by
    rintro ⟨v,hv⟩
    cases v with
    | inl x =>
      obtain ⟨b,hb⟩ := hv
      refine ⟨b,Subtype.ext ?_⟩
      apply congrArg Sum.inl
      apply Subtype.ext
      change g a*(g b)⁻¹ = x.val
      rw [hb]
      group
    | inr b => exact False.elim hv
  rw [← card_neighborSet_eq_degree]
  exact (Fintype.card_congr (Equiv.ofBijective f ⟨hfi,hfs⟩)).symm

lemma cycle_in_K44 : cycleGraph 8 ⊑ Erdos713KST.Kst 4 4 := by
  let f : Fin 8 → Fin 4 ⊕ Fin 4 :=
    ![Sum.inl 0,Sum.inr 0,Sum.inl 1,Sum.inr 1,Sum.inl 2,Sum.inr 2,Sum.inl 3,Sum.inr 3]
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try (exfalso; revert hij; decide)
    all_goals simp [f,Erdos713KST.Kst,completeBipartiteGraph]
  · intro i j hij
    change f i = f j at hij
    fin_cases i <;> fin_cases j <;> simp_all [f]

/-- The deliberately coarse constant comes from a fourth degree-moment
Kővári--Sós--Turán bound on a graph of at most three times the section order. -/
theorem card_bound_of_small_difference (g : K → G) (hg : Function.Injective g)
    (hf : (cycleGraph 8).Free (graph g))
    (hD : (differences g).card ≤ 2*Fintype.card K) : Fintype.card K ≤ 253125 := by
  classical
  let J := localGraph g
  have hfree : (Erdos713KST.Kst 4 4).Free J := by
    intro h
    exact hf (cycle_in_K44.trans (h.trans (local_contained g hg)))
  have hu := Erdos713KST.sum_degree_pow_le J (s := 4) (t := 4) (by decide) hfree
  have hcard : Fintype.card ((differences g) ⊕ K) ≤ 3*Fintype.card K := by
    simp only [Fintype.card_sum,Fintype.card_coe]
    omega
  have hlo : Fintype.card K*(Fintype.card K)^4 ≤ ∑ v, J.degree v^4 := by
    rw [Fintype.sum_sum_type]
    have he : (∑ a : K, J.degree (Sum.inr a)^4) = Fintype.card K*(Fintype.card K)^4 := by
      simp only [J,right_degree g hg,sum_const,card_univ,smul_eq_mul]
    omega
  have hp := Nat.pow_le_pow_left hcard 4
  have hb : Fintype.card K*(Fintype.card K)^4 ≤ 253125*(Fintype.card K)^4 := by
    calc
      _ ≤ (4+1)^4*(4+1)*Fintype.card ((differences g) ⊕ K)^4 := hlo.trans hu
      _ ≤ (4+1)^4*(4+1)*(3*Fintype.card K)^4 := Nat.mul_le_mul_left _ hp
      _ = _ := by ring
  by_cases hk : Fintype.card K = 0
  · omega
  exact (mul_le_mul_iff_left₀ (pow_pos (Nat.pos_of_ne_zero hk) 4)).mp hb

/-- The same moment argument with an arbitrary difference-set multiplier. -/
theorem card_bound_of_difference_ratio (g : K → G) (hg : Function.Injective g)
    (hf : (cycleGraph 8).Free (graph g)) (C : ℕ)
    (hD : (differences g).card ≤ C*Fintype.card K) :
    Fintype.card K ≤ 3125*(C+1)^4 := by
  classical
  let J := localGraph g
  have hfree : (Erdos713KST.Kst 4 4).Free J := by
    intro h
    exact hf (cycle_in_K44.trans (h.trans (local_contained g hg)))
  have hu := Erdos713KST.sum_degree_pow_le J (s := 4) (t := 4) (by decide) hfree
  have hcard : Fintype.card ((differences g) ⊕ K) ≤ (C+1)*Fintype.card K := by
    simp only [Fintype.card_sum,Fintype.card_coe]
    calc
      _ ≤ C*Fintype.card K+Fintype.card K := Nat.add_le_add_right hD _
      _ = _ := by ring
  have hlo : Fintype.card K*(Fintype.card K)^4 ≤ ∑ v, J.degree v^4 := by
    rw [Fintype.sum_sum_type]
    have he : (∑ a : K, J.degree (Sum.inr a)^4) = Fintype.card K*(Fintype.card K)^4 := by
      simp only [J,right_degree g hg,sum_const,card_univ,smul_eq_mul]
    omega
  have hp := Nat.pow_le_pow_left hcard 4
  have hb : Fintype.card K*(Fintype.card K)^4 ≤
      (3125*(C+1)^4)*(Fintype.card K)^4 := by
    calc
      _ ≤ (4+1)^4*(4+1)*Fintype.card ((differences g) ⊕ K)^4 := hlo.trans hu
      _ ≤ (4+1)^4*(4+1)*((C+1)*Fintype.card K)^4 := Nat.mul_le_mul_left _ hp
      _ = _ := by ring
  by_cases hk : Fintype.card K = 0
  · omega
  exact (mul_le_mul_iff_left₀ (pow_pos (Nat.pos_of_ne_zero hk) 4)).mp hb

variable [Field K] [CharP K 2]

/-- No additional coordinate is needed: over large fields, the commuting-
fiber property itself forces an injective C8 in every section Cayley graph. -/
theorem contains_commuting_section (φ : G → K) (hφ1 : φ 1 = 0)
    (hφmul : ∀ x y, φ (x*y) = φ x+φ y)
    (g : K → G) (hφg : ∀ a, φ (g a) = a)
    (hc : ∀ x y, φ x = φ y → Commute x y)
    (hq : 253125 < Fintype.card K) : cycleGraph 8 ⊑ graph g := by
  by_contra hf
  have hg : Function.Injective g := by
    intro a b h
    simpa only [hφg] using congrArg φ h
  have hD := differences_card φ hφ1 hφmul g hφg hc hf
  have hb := card_bound_of_small_difference g hg hf hD
  omega

#print axioms right_degree
#print axioms card_bound_of_small_difference
#print axioms card_bound_of_difference_ratio
#print axioms contains_commuting_section
end Erdos713C8SmallDifferenceCayley
