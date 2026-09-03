import FormalConjecturesUtil
import Submission.SL2TranslationWords
import Submission.InvolutiveProductCounting

/-! Elementary polynomial-fiber bounds exclude full Möbius voltage sections
in groups of order at most q+1, once q>27. This is an auxiliary obstruction. -/
open SimpleGraph Polynomial Finset
open scoped MatrixGroups
namespace Erdos713SL2MobiusVoltageBounds
open Erdos713C8SL2SectionObstruction Erdos713SL2TranslationWords
variable {K L W : Type*} [Field K] [CharP K 2] [Fintype K]
    [Field L] [Algebra K L] [CommGroup W]
set_option maxHeartbeats 2000000

omit [CharP K 2] [Fintype K] in
lemma card_le_of_roots (s : Finset K) (P : L[X]) (hp : P ≠ 0)
    (hs : ∀ a ∈ s, P.eval (algebraMap K L a) = 0) : s.card ≤ P.natDegree := by
  classical
  rw [← Finset.card_image_of_injective s (algebraMap K L).injective]
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  exact (Polynomial.mem_roots hp).mpr (hs a ha)

omit [Fintype K] in
lemma pair_ratio_cube (f : K → W) (a : K)
    (h : ratio f a = ratio f (a+1)) : f a^3 = f (a+1)^3 := by
  simp only [ratio,shift_involutive a] at h
  calc
    f a^3 = (f a^2*(f (a+1))⁻¹)*(f a*f (a+1)) := by
      calc
        _ = f a^3*((f (a+1))⁻¹*f (a+1)) := by simp
        _ = _ := by simp only [pow_succ,pow_zero,one_mul]; ac_rfl
    _ = (f (a+1)^2*(f a)⁻¹)*(f a*f (a+1)) := by rw [h]
    _ = _ := by simp [mul_assoc,pow_succ]

variable (f : K → W) (F : W →* Lˣ) (w t : L)
variable (hf : ∀ a, (F (f a) : L) =
  (algebraMap K L a+w)/(algebraMap K L a+w+t))
variable (hn : ∀ a : K, algebraMap K L a+w ≠ 0)
variable (hd : ∀ a : K, algebraMap K L a+w+t ≠ 0)

include hf hn hd

omit hn hd [Fintype K] [CharP K 2] in
lemma ratio_value (a : K) : (F (ratio f a) : L) =
    ((algebraMap K L a+w)/(algebraMap K L a+w+t))^2 /
      ((algebraMap K L a+w+1)/(algebraMap K L a+w+1+t)) := by
  simp only [ratio,map_mul,map_pow,map_inv,Units.val_mul,Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val,hf,map_add,map_one,div_eq_mul_inv]
  congr 2; congr 1 <;> ring

omit [CharP K 2] in
open scoped Classical in
lemma fiber_card (ht : t ≠ 0) (y : W) :
    (Finset.univ.filter (fun a => ratio f a = y)).card ≤ 3 := by
  let v : L := F y
  let P : L[X] := (X+C w)^2*(X+C w+1+C t)-C v*(X+C w+C t)^2*(X+C w+1)
  have hv : v ≠ 0 := (F y).ne_zero
  have hp : P ≠ 0 := by
    intro he
    have hval := congrArg (fun p : L[X] => p.eval (-w)) he
    have hbad : v*t^2 = 0 := by
      simpa [P] using hval
    exact (mul_ne_zero hv (pow_ne_zero _ ht)) hbad
  have hdeg : P.natDegree ≤ 3 := by dsimp [P]; compute_degree
  apply (card_le_of_roots _ P hp ?_).trans hdeg
  intro a ha
  have hay := (Finset.mem_filter.mp ha).2
  have he := ratio_value f F w t hf a
  rw [hay] at he
  have hna : algebraMap K L a+w+1 ≠ 0 := by
    simpa only [map_add,map_one,add_right_comm] using hn (a+1)
  have hda : algebraMap K L a+w+1+t ≠ 0 := by
    simpa only [map_add,map_one,add_right_comm] using hd (a+1)
  have hda0 := hd a
  have he' : ((algebraMap K L a+w)/(algebraMap K L a+w+t))^2 /
      ((algebraMap K L a+w+1)/(algebraMap K L a+w+1+t)) = v := he.symm
  field_simp [hda0,hna,hda] at he'
  simp only [P,eval_sub,eval_mul,eval_pow,eval_add,eval_X,eval_C,eval_one]
  linear_combination he'

omit hn in
open scoped Classical in
lemma paired_card (ht : t ≠ 0) :
    (Finset.univ.filter (fun a => ratio f a = ratio f (a+1))).card ≤ 6 := by
  let P : L[X] := (X+C w)^3*(X+C w+1+C t)^3-(X+C w+1)^3*(X+C w+C t)^3
  have hp : P ≠ 0 := by
    intro he
    have hval := congrArg (fun p : L[X] => p.eval (-w)) he
    have hbad : t^3 = 0 := by simpa [P] using hval
    exact pow_ne_zero _ ht hbad
  have hdeg : P.natDegree ≤ 6 := by dsimp [P]; compute_degree
  apply (card_le_of_roots _ P hp ?_).trans hdeg
  intro a ha
  have he := congrArg (fun z : W => (F z : L)) (pair_ratio_cube f a (mem_filter.mp ha).2)
  simp only [map_pow,Units.val_pow_eq_pow_val,hf,map_add,map_one] at he
  have hda : algebraMap K L a+w+1+t ≠ 0 := by
    simpa only [map_add,map_one,add_right_comm] using hd (a+1)
  have hda0 := hd a
  have he' : ((algebraMap K L a+w)/(algebraMap K L a+w+t))^3 =
      ((algebraMap K L a+w+1)/(algebraMap K L a+w+1+t))^3 := by
    convert he using 1; congr 2 <;> ring
  field_simp [hda0,hda] at he'
  simp only [P,eval_sub,eval_mul,eval_pow,eval_add,eval_X,eval_C,eval_one]
  linear_combination he'

/-- A full Möbius section in an ambient voltage group of order at most
q+1 cannot be C8-free for q>27. No trace condition or enumerated field
instance is used. The field extension L need not be finite. -/
theorem contains [Fintype W] (ht : t ≠ 0)
    (hW : Fintype.card W ≤ Fintype.card K+1) (hK : 27 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator f) := by
  classical
  by_contra hfree
  have hbound := Erdos713InvolutiveProductCounting.card_bound
    (fun a : K => a+1) shift_involutive (ratio f) 6
    (fiber_card f F w t hf hn hd ht) (paired_card f F w t hf hd ht) ?_
  · omega
  · intro c r d hcr hcr' hcd hcd' hv
    exact hfree (contains_at f r c d hcr hcr' hcd hcd' hv)

#print axioms fiber_card
#print axioms paired_card
#print axioms contains
end Erdos713SL2MobiusVoltageBounds
