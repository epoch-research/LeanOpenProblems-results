import Submission.BinaryInverseTrace

/-! Binary trace and the Artin--Schreier image, for the Witt-circle investigation.
These auxiliary results do not settle Erdős714. -/
noncomputable section
open Finset Polynomial Classical
open scoped CharTwo
set_option maxHeartbeats 2000000
namespace Erdos714BinaryInverseTrace
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

omit [CharP F 2] in
/-- Agreement with the actual absolute field trace. -/
lemma traceSum_eq_trace (k : ℕ) (hcard : Fintype.card F=2^k)
    [Algebra (ZMod 2) F] (x : F) :
    traceSum k x = algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) F x) := by
  have hr : Module.finrank (ZMod 2) F = k := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hcard,ZMod.card] at h
    exact (Nat.pow_right_injective (by decide : 1 < 2)) h.symm
  rw [FiniteField.algebraMap_trace_eq_sum_pow,hr]
  simp [traceSum, Nat.card_eq_fintype_card]

lemma exists_traceSum_one (k : ℕ) (hcard : Fintype.card F=2^k) :
    ∃ x : F, traceSum k x=1 := by
  letI := ZMod.algebra F 2
  obtain ⟨x,hx⟩ := Algebra.trace_surjective (ZMod 2) F 1
  refine ⟨x,?_⟩
  rw [traceSum_eq_trace k hcard,hx,map_one]

/-- The additive Artin--Schreier map. -/
def artinSchreier : F →+ F where
  toFun x := x^2+x
  map_zero' := by simp
  map_add' x y := by rw [add_pow_char]; ring

omit [Fintype F] in
lemma artinSchreier_eq_zero (x : F) : artinSchreier x=0 ↔ x=0 ∨ x=1 := by
  have he : x^2+x=x*(x-1) := by simp; ring
  simp only [artinSchreier, AddMonoidHom.coe_mk, ZeroHom.coe_mk, he,
    mul_eq_zero, sub_eq_zero]

private lemma artinSchreier_kernel_card : Nat.card (artinSchreier : F →+ F).ker=2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have he : (univ.filter (fun x : F => x ∈ (artinSchreier : F →+ F).ker))={0,1} := by
    ext x
    simp [artinSchreier_eq_zero]
  rw [he]
  simp

def traceHom (k : ℕ) : F →+ F where
  toFun := traceSum k
  map_zero' := by simp [traceSum]
  map_add' := traceSum_add k

private lemma trace_range_card (k : ℕ) (hcard : Fintype.card F=2^k) :
    Nat.card (traceHom (F := F) k).range=2 := by
  obtain ⟨x,hx⟩ := exists_traceSum_one k hcard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have he : (univ.filter (fun y : F => y ∈ (traceHom (F := F) k).range))={0,1} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, AddMonoidHom.mem_range,
      mem_insert, mem_singleton]
    constructor
    · rintro ⟨z,rfl⟩
      exact traceSum_zero_or_one k hcard z
    · rintro (rfl | rfl)
      · exact ⟨0,by simp [traceHom,traceSum]⟩
      · exact ⟨x,hx⟩
  rw [he]
  simp

lemma artinSchreier_trace (k : ℕ) (hcard : Fintype.card F=2^k) (x : F) :
    traceSum k (x^2+x)=0 := by
  rw [traceSum_add,traceSum_square k hcard]
  simp

/-- The binary Artin--Schreier image is exactly the trace-zero hyperplane. -/
theorem trace_zero_iff_artinSchreier (k : ℕ) (hcard : Fintype.card F=2^k) (a : F) :
    traceSum k a=0 ↔ ∃ x : F, x^2+x=a := by
  have hle : (artinSchreier : F →+ F).range ≤ (traceHom (F := F) k).ker := by
    rintro y ⟨x,rfl⟩
    exact artinSchreier_trace k hcard x
  have h₁ := (artinSchreier : F →+ F).ker.card_mul_index
  have h₂ := (traceHom (F := F) k).ker.card_mul_index
  rw [AddSubgroup.index_ker,artinSchreier_kernel_card] at h₁
  rw [AddSubgroup.index_ker,trace_range_card k hcard] at h₂
  have he := AddSubgroup.eq_of_le_of_card_ge hle (by omega)
  change a ∈ (traceHom (F := F) k).ker ↔ a ∈ (artinSchreier : F →+ F).range
  rw [he]

/-- An irreducible quadratic for each trace-one parameter. -/
lemma trace_one_irreducible (k : ℕ) (hcard : Fintype.card F=2^k)
    (c : F) (hc : traceSum k c=1) : Irreducible (X^2+X+C c) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (X^2+X+C c).natDegree=2 := by compute_degree!
    rw [hd]; decide
  · intro x hx
    have hh : x^2+x=c := by
      have hh : x^2+x+c=0 := by simpa using hx
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
    have ht := artinSchreier_trace k hcard x
    rw [hh,hc] at ht
    exact one_ne_zero ht

/-- Frobenius iteration of an Artin--Schreier root. -/
lemma root_frobenius_iteration {E : Type*} [Field E] [CharP E 2]
    (y c : E) (hy : y^2+y=c) (k : ℕ) :
    y^(2^k)=y+∑ i ∈ range k, c^(2^i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',pow_mul,show y^2=y+c by
      have he := congrArg (fun z => z+y) hy
      simpa [add_assoc, add_comm] using he,add_pow_char_pow,ih,sum_range_succ]
    ring

#print axioms traceSum_eq_trace
#print axioms exists_traceSum_one
#print axioms trace_zero_iff_artinSchreier
#print axioms trace_one_irreducible
#print axioms root_frobenius_iteration
end Erdos714BinaryInverseTrace
