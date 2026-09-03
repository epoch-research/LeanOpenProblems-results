import FormalConjecturesUtil

/-!
# An odd repeated-modulus cover within a logarithmic multiplicity envelope

This covers every integer but is NOT a StrictCoveringSystem: its moduli repeat.
It rules out using this multiplicity envelope alone as a no-3 obstruction.
-/
namespace Erdos7LogarithmicMultiplicityCover
open scoped BigOperators
set_option maxHeartbeats 5000000
set_option maxRecDepth 4000
def modulus : Fin 29 → ℕ := ![5,5,7,7,7,11,11,11,11,35,35,35,35,35,35,55,55,55,55,55,55,55,77,77,77,77,77,77,77]
def residue : Fin 29 → ℤ := ![0,1,0,1,2,0,1,2,3,18,33,13,4,19,34,37,27,17,7,52,42,32,59,38,17,73,52,31,10]
def privatePoint : Fin 29 → ℤ := ![235,81,378,323,268,242,67,277,102,158,103,48,4,334,279,312,137,347,172,382,207,32,213,38,248,73,283,108,318]
def labels : Fin 6 → ℕ := ![5,7,11,35,55,77]
def counts : Fin 6 → ℕ := ![2,3,4,6,7,7]
def logCap (d : ℕ) : ℕ := Nat.clog 3 (d*d)-1

lemma arithmetic_data :
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ ¬ 3 ∣ modulus i ∧ modulus i ∣ 385) ∧
    (∀ r : Fin 385, ∃ i, (modulus i : ℤ) ∣ (r.val : ℤ)-residue i) ∧
    (∀ i j, (modulus j : ℤ) ∣ privatePoint i-residue j ↔ j=i) ∧
    (∀ i, ∃ j, modulus i=labels j) ∧
    (∀ j, (Finset.univ.filter (fun i => modulus i=labels j)).card=counts j) := by
  decide +kernel

lemma cap_data : ∀ j, counts j ≤ logCap (labels j) := by
  decide +kernel

theorem multiplicity_bound (d : ℕ) :
    (Finset.univ.filter (fun i => modulus i=d)).card ≤ logCap d := by
  classical
  by_cases h : ∃ j, d=labels j
  · obtain ⟨j,rfl⟩ := h
    rw [arithmetic_data.2.2.2.2 j]
    exact cap_data j
  · have he : Finset.univ.filter (fun i => modulus i=d) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨j,hj⟩ := arithmetic_data.2.2.2.1 i
      exact h ⟨j,(Finset.mem_filter.mp hi).2.symm.trans hj⟩
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

theorem not_injective : ¬ Function.Injective modulus := by
  intro h
  have hh := h (show modulus 0=modulus 1 by rfl)
  have : (0 : Fin 29) ≠ 1 := by decide
  exact this hh

theorem covers (x : ℤ) : ∃ i, (modulus i : ℤ) ∣ x-residue i := by
  have hnonneg : 0 ≤ x % 385 := Int.emod_nonneg _ (by norm_num)
  have hlt : x % 385 < 385 := Int.emod_lt_of_pos _ (by norm_num)
  let r : Fin 385 := ⟨(x % 385).toNat, by omega⟩
  have hr : (r.val : ℤ) = x % 385 := Int.toNat_of_nonneg hnonneg
  obtain ⟨i, hi⟩ := arithmetic_data.2.1 r
  refine ⟨i, ?_⟩
  have hm : (modulus i : ℤ) ∣ 385 := by
    exact_mod_cast (arithmetic_data.1 i).2.2.2
  have hx : (385 : ℤ) ∣ x-x%385 := ⟨x/385, by omega⟩
  have hd := (hm.trans hx).add hi
  rw [hr] at hd
  convert hd using 1 <;> ring

#print axioms covers

#print axioms arithmetic_data
#print axioms multiplicity_bound
#print axioms not_injective
end Erdos7LogarithmicMultiplicityCover
