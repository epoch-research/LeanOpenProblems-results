import FormalConjecturesUtil
import Submission.UpToSharpDegree

/-! An obstruction to compressing the last coordinate in the five-coordinate C8 construction. -/

open SimpleGraph
namespace Erdos713C8Voltage
set_option maxHeartbeats 1000000

abbrev Vertex (F A : Type*) := (F × (Fin 3 → F)) × A

def Rel {F A : Type*} [Field F] [AddCommGroup A] (f : F →+ A)
    (p l : Vertex F A) : Prop :=
  p.1.2 0 + l.1.2 0 = l.1.1 * p.1.1 ∧
  p.1.2 1 + l.1.2 1 = l.1.2 0 * p.1.1 ∧
  p.1.2 2 + l.1.2 2 = l.1.1 * p.1.2 0 ∧
  p.2 + l.2 = f (l.1.1 * p.1.2 1)

abbrev graph {F A : Type*} [Field F] [AddCommGroup A] (f : F →+ A) :=
  Erdos713C6.bipGraph (Rel f)

def lift {F A : Type*} [Field F] [AddCommGroup A] (f : F →+ A)
    (p : Erdos713C8.Coordinates F) : Vertex F A :=
  ((p.1, ![p.2 0,p.2 1,p.2 2]), f (p.2 3))

lemma rel_of_defect {F A : Type*} [Field F] [AddCommGroup A] (f : F →+ A)
    (p l : Erdos713C8.Coordinates F)
    (h0 : p.2 0 + l.2 0 = l.1 * p.1)
    (h1 : p.2 1 + l.2 1 = l.2 0 * p.1)
    (h2 : p.2 2 + l.2 2 = l.1 * p.2 0)
    (h3 : f (p.2 3 + l.2 3 - l.1 * p.2 1) = 0) : Rel f (lift f p) (lift f l) := by
  refine ⟨h0,h1,h2,?_⟩
  change f (p.2 3) + f (l.2 3) = f (l.1 * p.2 1)
  rw [map_sub,map_add] at h3
  exact sub_eq_zero.mp h3

def points {F : Type*} [Field F] (u v z : F) : Fin 4 → Erdos713C8.Coordinates F :=
  let s := (u-v)*z
  let t := (u+v)*z
  ![(0,![0,0,0,0]), (s,![0,0,0,0]),
    (s+t,![u*t,u*s*t,u^2*t,u^2*s*t]), (t,![v*t,0,v^2*t,-u*v*s*t])]

def lines {F : Type*} [Field F] (u v z : F) : Fin 4 → Erdos713C8.Coordinates F :=
  let s := (u-v)*z
  let t := (u+v)*z
  ![(0,![0,0,0,0]), (u,![u*s,u*s^2,0,0]),
    (u+v,![u*t,u*t^2,u*v*t,u*v*s*t]), (v,![0,0,0,u*v*s*t])]

lemma contains_of_octagon {P L : Type*} (R : P → L → Prop)
    (p : Fin 4 → P) (l : Fin 4 → L) (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, R (p i) (l i)) (hB : ∀ i, R (p (i+1)) (l i)) :
    cycleGraph 8 ⊑ Erdos713C6.bipGraph R := by
  let c : Fin 8 → P ⊕ L :=
    ![Sum.inl (p 0), Sum.inr (l 0), Sum.inl (p 1), Sum.inr (l 1),
      Sum.inl (p 2), Sum.inr (l 2), Sum.inl (p 3), Sum.inr (l 3)]
  have hA0 := hA 0; have hA1 := hA 1; have hA2 := hA 2; have hA3 := hA 3
  have hB0 := hB 0; have hB1 := hB 1; have hB2 := hB 2; have hB3 := hB 3
  refine ⟨⟨⟨c,?_⟩,?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) |
        simpa [c, Erdos713C6.bipGraph] using hA0 |
        simpa [c, Erdos713C6.bipGraph] using hA1 |
        simpa [c, Erdos713C6.bipGraph] using hA2 |
        simpa [c, Erdos713C6.bipGraph] using hA3 |
        simpa [c, Erdos713C6.bipGraph] using hB0 |
        simpa [c, Erdos713C6.bipGraph] using hB1 |
        simpa [c, Erdos713C6.bipGraph] using hB2 |
        simpa [c, Erdos713C6.bipGraph] using hB3
  · intro i j hij
    change c i = c j at hij
    fin_cases i <;> fin_cases j <;> simp_all [c, hp.eq_iff, hl.eq_iff]

set_option maxHeartbeats 1000000 in
lemma contains_of_voltage {F A : Type*} [Field F] [AddCommGroup A]
    (f : F →+ A) (u v z : F) (hu : u ≠ 0) (hv : v ≠ 0) (hz : z ≠ 0)
    (hsub : u-v ≠ 0) (hadd : u+v ≠ 0)
    (hVolt : f (u*v*(u^2-v^2)*z^2) = 0) : cycleGraph 8 ⊑ graph f := by
  let p : Fin 4 → Vertex F A := fun i => lift f (points u v z i)
  let l : Fin 4 → Vertex F A := fun i => lift f (lines u v z i)
  have hs : (u-v)*z ≠ 0 := mul_ne_zero hsub hz
  have ht : (u+v)*z ≠ 0 := mul_ne_zero hadd hz
  have hut : u*((u+v)*z) ≠ 0 := mul_ne_zero hu ht
  have hvt : v*((u+v)*z) ≠ 0 := mul_ne_zero hv ht
  have huv : u ≠ v := sub_ne_zero.mp hsub
  apply contains_of_octagon (Rel f) p l
  · intro i j hij
    have hx := congrArg (fun w : Vertex F A => w.1.1) hij
    have hy := congrArg (fun w : Vertex F A => w.1.2 0) hij
    fin_cases i <;> fin_cases j <;>
      simp_all [p, points, lift]
  · intro i j hij
    have hx := congrArg (fun w : Vertex F A => w.1.1) hij
    fin_cases i <;> fin_cases j <;> simp_all [l, lines, lift]
  · intro i
    apply rel_of_defect
    all_goals fin_cases i <;> dsimp [points, lines]
    all_goals first | (ring; done) | (convert f.map_zero using 1 <;> congr 1 <;> ring; done)
  · intro i
    apply rel_of_defect
    all_goals fin_cases i <;> dsimp [points, lines]
    all_goals first | (ring; done) | (convert f.map_zero using 1 <;> congr 1 <;> ring; done) |
      (convert hVolt using 1 <;> congr 1 <;> ring; done)

lemma quotient_contains_of_voltage {F : Type*} [Field F] (U : AddSubgroup F)
    (u v z : F) (hu : u ≠ 0) (hv : v ≠ 0) (hz : z ≠ 0)
    (hsub : u-v ≠ 0) (hadd : u+v ≠ 0)
    (hVolt : u*v*(u^2-v^2)*z^2 ∈ U) :
    cycleGraph 8 ⊑ graph (QuotientAddGroup.mk' U) :=
  contains_of_voltage _ u v z hu hv hz hsub hadd ((QuotientAddGroup.eq_zero_iff _).mpr hVolt)

lemma noninjective_contains_of_sq_surjective {F A : Type*} [Field F] [AddCommGroup A]
    (f : F →+ A) (hf : ¬ Function.Injective f)
    (hSq : Function.Surjective (fun z : F => z^2))
    (u v : F) (hu : u ≠ 0) (hv : v ≠ 0) (hsub : u-v ≠ 0) (hadd : u+v ≠ 0) :
    cycleGraph 8 ⊑ graph f := by
  classical
  have hKernel : ∃ w : F, w ≠ 0 ∧ f w = 0 := by
    by_contra hn
    apply hf
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    apply hn
    refine ⟨x-y,hne,?_⟩
    rw [map_sub,hxy,sub_self]
  obtain ⟨w,hw,hfw⟩ := hKernel
  let P : F := u*v*(u^2-v^2)
  have hP : P ≠ 0 := by
    dsimp only [P]
    rw [show u^2-v^2 = (u-v)*(u+v) by ring]
    exact mul_ne_zero (mul_ne_zero hu hv) (mul_ne_zero hsub hadd)
  obtain ⟨z,hz⟩ := hSq (w/P)
  change z^2 = w/P at hz
  have hz0 : z ≠ 0 := by
    intro hh
    rw [hh,zero_pow (by decide : 2 ≠ 0)] at hz
    exact div_ne_zero hw hP hz.symm
  have heq : P*z^2 = w := by
    rw [hz]
    field_simp [hP]
  apply contains_of_voltage f u v z hu hv hz0 hsub hadd
  change f (P*z^2) = 0
  rw [heq,hfw]

lemma noninjective_contains_char_two {F A : Type*} [Field F] [Fintype F] [CharP F 2]
    [AddCommGroup A] (f : F →+ A) (hf : ¬ Function.Injective f)
    (hCard : 2 < Fintype.card F) : cycleGraph 8 ⊑ graph f := by
  classical
  have hSq : Function.Surjective (fun z : F => z^2) :=
    Finite.surjective_of_injective (frobenius_inj F 2)
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1} : Finset F)) (t := Finset.univ)
    (by simpa only [Finset.card_pair (zero_ne_one : (0 : F) ≠ 1), Finset.card_univ] using hCard)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  apply noninjective_contains_of_sq_surjective f hf hSq u 1 hu.1 one_ne_zero
    (sub_ne_zero.mpr hu.2)
  rw [← CharTwo.sub_eq_add]
  exact sub_ne_zero.mpr hu.2

#print axioms contains_of_voltage
#print axioms quotient_contains_of_voltage
#print axioms noninjective_contains_char_two
end Erdos713C8Voltage
