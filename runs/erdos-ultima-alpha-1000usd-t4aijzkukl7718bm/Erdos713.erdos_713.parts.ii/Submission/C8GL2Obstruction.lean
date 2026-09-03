import FormalConjecturesUtil
import Submission.C8GL2Curve

/-! The nonzero characteristic-two GL2 matrix curve is not C8-free over
sufficiently large finite fields with injective cubing. This auxiliary
construction obstruction does not settle Erdős 713. -/
open SimpleGraph
open scoped MatrixGroups
namespace Erdos713C8GL2Obstruction
open Erdos713C8GL2Curve
variable {K : Type*} [Field K] [CharP K 2]
set_option maxHeartbeats 2000000

lemma delta_ne_zero (hcube : Function.Injective (fun x : K => x^3))
    {a : K} (ha : a ≠ 1) : delta a ≠ 0 := by
  intro h
  apply ha
  apply hcube
  simpa only [one_pow] using (CharTwo.add_eq_zero.mp h).symm

abbrev NonzeroParam (K : Type*) [Field K] := {a : K // a ≠ 0 ∧ a ≠ 1}

def generator (hcube : Function.Injective (fun x : K => x^3))
    (a : NonzeroParam K) : GL (Fin 2) K :=
  curve ⟨a.val,delta_ne_zero hcube a.property.2⟩

def partner (a b : K) : K := (a+b^2)/(1+a*b)

lemma partner_relations {a b : K} (hden : 1+a*b ≠ 0) :
    a+partner a b = b*partner b a ∧ b+partner b a = a*partner a b := by
  have hden' : 1+b*a ≠ 0 := by simpa only [mul_comm] using hden
  constructor <;> dsimp [partner] <;>
    field_simp [hden,hden'] <;> ring_nf <;> reduce_mod_char!

lemma partner_nonzero {a b : K} (hden : 1+a*b ≠ 0) (hnum : a ≠ b^2) :
    partner a b ≠ 0 := div_ne_zero (fun h => hnum (CharTwo.add_eq_zero.mp h)) hden

lemma partner_ne_one {a b : K} (hden : 1+a*b ≠ 0)
    (hb : b ≠ 1) (hs : a+b ≠ 1) : partner a b ≠ 1 := by
  intro h
  have he : a+b^2 = 1+a*b := (div_eq_one_iff_eq hden).mp h
  have hprod : (b+1)*(a+b+1)=0 := by
    linear_combination (norm := ring_nf) he
    reduce_mod_char!
  exact (mul_ne_zero (fun h => hb (CharTwo.add_eq_zero.mp h))
    (fun h => hs (CharTwo.add_eq_zero.mp h))) hprod

lemma partner_ne_second {a b : K} (hden : 1+a*b ≠ 0)
    (hb : b ≠ 1) (hm : a*b+a+b ≠ 0) : partner a b ≠ b := by
  intro h
  have he : a+b^2 = b*(1+a*b) := (div_eq_iff hden).mp h
  have hprod : (b+1)*(a*b+a+b)=0 := by
    linear_combination (norm := ring_nf) he
    reduce_mod_char!
  exact (mul_ne_zero (fun h => hb (CharTwo.add_eq_zero.mp h)) hm) hprod

/-- The rational two-parameter obstruction remains entirely inside the
nonzero, invertible part of the curve. -/
theorem contains_at (hcube : Function.Injective (fun x : K => x^3))
    (a b : K) (ha : a ≠ 0) (ha1 : a ≠ 1) (hb : b ≠ 0) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hden : 1+a*b ≠ 0) (hs : a+b ≠ 1)
    (hm : a*b+a+b ≠ 0) (hca : a ≠ b^2) (hdb : b ≠ a^2) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator hcube) := by
  have hden' : 1+b*a ≠ 0 := by simpa only [mul_comm] using hden
  have hm' : b*a+b+a ≠ 0 := by convert hm using 1; ring
  let A : NonzeroParam K := ⟨a,ha,ha1⟩
  let B : NonzeroParam K := ⟨b,hb,hb1⟩
  let C : NonzeroParam K := ⟨partner a b,partner_nonzero hden hca,
    partner_ne_one hden hb1 hs⟩
  let D : NonzeroParam K := ⟨partner b a,partner_nonzero hden' hdb,
    partner_ne_one hden' ha1 (by simpa only [add_comm] using hs)⟩
  let f : NonzeroParam K → Param K := fun x => ⟨x.val,delta_ne_zero hcube x.property.2⟩
  have hAB : f A ≠ f B := fun h => hab (congrArg Subtype.val h)
  have hCB : f C ≠ f B := fun h => partner_ne_second hden hb1 hm (congrArg Subtype.val h)
  have hDA : f D ≠ f A := fun h => partner_ne_second hden' ha1 hm' (congrArg Subtype.val h)
  have hrels := partner_relations hden
  apply Erdos713C8InvolutiveBlock.contains (generator hcube) A B C D
    (difference_not_involution (f A) (f B) ha hb hAB) ?_
    (swapped_involution (f A) (f B) (f C) (f D) hrels.1 hrels.2)
    (fun h => hCB (curve_injective h)) (fun h => hDA (curve_injective h))
  intro h
  change (curve (f A)*(curve (f B))⁻¹)*(curve (f C)*(curve (f D))⁻¹)=1 at h
  have he : curve (f A)*(curve (f B))⁻¹ = curve (f D)*(curve (f C))⁻¹ := by
    calc
      _ = ((curve (f A)*(curve (f B))⁻¹)*(curve (f C)*(curve (f D))⁻¹))*
          curve (f D)*(curve (f C))⁻¹ := by simp [mul_assoc]
      _ = _ := by rw [h,one_mul]
  exact hDA (difference_sidon hcube (f A) (f B) (f D) (f C) hAB he).1.symm

/-- For every fixed nonzero a different from one there are at most eight
excluded choices of b in the explicit obstruction. -/
lemma exists_parameters [Fintype K] (hq : 8 < Fintype.card K)
    (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ b : K, b ≠ 0 ∧ b ≠ 1 ∧ a ≠ b ∧ 1+a*b ≠ 0 ∧ a+b ≠ 1 ∧
      a*b+a+b ≠ 0 ∧ a ≠ b^2 ∧ b ≠ a^2 := by
  classical
  let L : List K := [0,1,a,a^2,a⁻¹,a+1,a/(a+1)]
  let S : Finset K := Finset.univ.filter (fun b => b^2=a)
  have hL : L.toFinset.card ≤ 7 := List.toFinset_card_le L
  have hS : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro b hb c hc
    apply frobenius_inj K 2
    exact (Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hc).2.symm
  have hcard : (L.toFinset ∪ S).card < (Finset.univ : Finset K).card := by
    have hh := Finset.card_union_le L.toFinset S
    simp only [Finset.card_univ]
    omega
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hbL : b ∉ L.toFinset := fun h => hb (Finset.mem_union_left _ h)
  have hbS : b^2 ≠ a := fun h => hb (Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,h⟩))
  simp only [L,List.mem_toFinset,List.mem_cons,List.mem_nil_iff,not_or,not_false_eq_true,and_true] at hbL
  rcases hbL with ⟨hb0,hb1,hba,hbsq,hbinv,hbplus,hbfrac⟩
  have hden : 1+a*b ≠ 0 := by
    intro h
    apply hbinv
    apply (mul_eq_one_iff_eq_inv₀ ha).mp
    simpa only [mul_comm] using (CharTwo.add_eq_zero.mp h).symm
  have hs : a+b ≠ 1 := by
    intro h
    apply hbplus
    calc b = a+(a+b) := by rw [← add_assoc,CharTwo.add_self_eq_zero,zero_add]
         _ = a+1 := by rw [h]
  have hm : a*b+a+b ≠ 0 := by
    intro h
    apply hbfrac
    apply (eq_div_iff (show a+1 ≠ 0 from fun hz => ha1 (CharTwo.add_eq_zero.mp hz))).mpr
    linear_combination (norm := ring_nf) h
    reduce_mod_char!
  exact ⟨b,hb0,hb1,Ne.symm hba,hden,hs,hm,hbS.symm,hbsq⟩

/-- In particular removing zero and one does not give a C8-free construction.
The cubing hypothesis holds in finite fields of characteristic two and odd
extension degree. -/
theorem contains_nonzero [Fintype K]
    (hcube : Function.Injective (fun x : K => x^3)) (hq : 8 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator hcube) := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({0,1} : Finset K).card < (Finset.univ : Finset K).card from
      Finset.card_le_two.trans_lt (by simpa using (show 2 < Fintype.card K by omega)))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
  obtain ⟨b,hb,hb1,hab,hden,hs,hm,hca,hdb⟩ := exists_parameters hq a ha.1 ha.2
  exact contains_at hcube a b ha.1 ha.2 hb hb1 hab hden hs hm hca hdb


lemma cube_injective_of_card_mod [Fintype K] (hq : Fintype.card K % 3 = 2) :
    Function.Injective (fun x : K => x^3) := by
  intro x y h
  dsimp only at h
  apply frobenius_inj K 2
  change x^2 = y^2
  have hmult : 3*((Fintype.card K+1)/3) = Fintype.card K+1 := by omega
  calc
    x^2 = x^(Fintype.card K+1) := by rw [pow_succ _ (Fintype.card K),FiniteField.pow_card,pow_two]
    _ = (x^3)^((Fintype.card K+1)/3) := by rw [← pow_mul,hmult]
    _ = (y^3)^((Fintype.card K+1)/3) := by rw [h]
    _ = y^(Fintype.card K+1) := by rw [← pow_mul,hmult]
    _ = y^2 := by rw [pow_succ _ (Fintype.card K),FiniteField.pow_card,pow_two]

omit [Field K] [CharP K 2] in
lemma card_mod_of_odd_degree [Fintype K] {k : ℕ} (hk : Odd k)
    (hq : Fintype.card K = 2^k) : Fintype.card K % 3 = 2 := by
  obtain ⟨t,ht⟩ := hk
  have he : k = 2*t+1 := by omega
  rw [hq,he,pow_add,pow_mul]
  norm_num only [Nat.reducePow]
  rw [Nat.mul_mod,Nat.pow_mod]
  norm_num

/-- The obstruction applies, in particular, at every odd extension degree
larger than three over F2. -/
theorem contains_odd_degree [Fintype K] {k : ℕ} (hk : Odd k)
    (hcard : Fintype.card K = 2^k) (hq : 8 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph
      (generator (cube_injective_of_card_mod (card_mod_of_odd_degree hk hcard))) :=
  contains_nonzero _ hq

end Erdos713C8GL2Obstruction
