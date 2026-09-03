import FormalConjecturesUtil

/-!
# Low-energy repeated-modulus covering control

This is an actual cover of the integers, but not a strict covering system.
It satisfies the logarithmic multiplicity bound and has small exponential
multiplicity energy. Neither restriction alone rules out a repeated cover.
-/
namespace Erdos7LowEnergyMultiplicityCover
open scoped BigOperators
set_option maxHeartbeats 5000000
set_option maxRecDepth 4000
def baseModulus : Fin 21 → ℕ := ![5,5,5,7,11,11,11,35,35,35,35,35,35,55,55,55,55,55,55,55,55]
def baseResidue : Fin 21 → ℤ := ![0,1,2,0,0,1,2,8,23,3,18,33,13,14,4,49,39,29,19,9,54]
def modulus : Fin 29 → ℕ := ![5,5,25,25,25,25,25,7,11,11,11,35,35,35,35,35,35,275,275,275,275,275,55,55,55,55,55,55,55]
def residue : Fin 29 → ℤ := ![0,1,2,7,12,17,22,0,0,1,2,8,23,3,18,33,13,14,69,124,179,234,4,49,39,29,19,9,54]
def child : Fin 21 → Fin 5 → Fin 29 := ![![0,0,0,0,0],![1,1,1,1,1],![2,3,4,5,6],![7,7,7,7,7],![8,8,8,8,8],![9,9,9,9,9],![10,10,10,10,10],![11,11,11,11,11],![12,12,12,12,12],![13,13,13,13,13],![14,14,14,14,14],![15,15,15,15,15],![16,16,16,16,16],![17,18,19,20,21],![22,22,22,22,22],![23,23,23,23,23],![24,24,24,24,24],![25,25,25,25,25],![26,26,26,26,26],![27,27,27,27,27],![28,28,28,28,28]]
def privatePoint : Fin 29 → ℤ := ![5,6,27,32,37,17,47,28,44,34,24,8,58,3,18,103,48,289,69,124,179,234,4,104,39,29,19,9,54]
def labels : Fin 7 → ℕ := ![5,7,11,25,35,55,275]
def counts : Fin 7 → ℕ := ![2,1,3,5,6,7,5]
def logCap (d : ℕ) : ℕ := Nat.clog 3 (d*d)-1

def energy : ℚ := ∑ j, ((2 : ℚ)^counts j-1)/(labels j : ℚ)^2

lemma base_data :
    (∀ i, baseModulus i ∣ 385) ∧
    (∀ r : Fin 385, ∃ i, (baseModulus i : ℤ) ∣ (r.val : ℤ)-baseResidue i) := by
  decide +kernel

lemma refinement_data : ∀ i t,
    (modulus (child i t) : ℤ) ∣ 5*(baseModulus i : ℤ) ∧
    (modulus (child i t) : ℤ) ∣
      baseResidue i+(baseModulus i : ℤ)*(t.val : ℤ)-residue (child i t) := by
  decide +kernel

lemma arithmetic_data :
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ ¬ 3 ∣ modulus i ∧ modulus i ∣ 9625) ∧
    (∀ i j, (modulus j : ℤ) ∣ privatePoint i-residue j ↔ j=i) ∧
    (∀ i, ∃ j, modulus i=labels j) ∧
    (∀ j, (Finset.univ.filter (fun i => modulus i=labels j)).card=counts j) ∧
    Function.Injective labels ∧
    (∀ j, counts j ≤ logCap (labels j)) := by
  decide +kernel

/-- Reduction modulo a common period extends the finite covering certificate. -/
lemma base_covers (x : ℤ) : ∃ i, (baseModulus i : ℤ) ∣ x-baseResidue i := by
  have hn : 0 ≤ x % 385 := Int.emod_nonneg _ (by norm_num)
  have hl : x % 385 < 385 := Int.emod_lt_of_pos _ (by norm_num)
  let r : Fin 385 := ⟨(x % 385).toNat, by omega⟩
  have hr : (r.val : ℤ) = x % 385 := Int.toNat_of_nonneg hn
  obtain ⟨i, hi⟩ := base_data.2 r
  refine ⟨i, ?_⟩
  have hm : (baseModulus i : ℤ) ∣ 385 := by exact_mod_cast base_data.1 i
  have hx : (385 : ℤ) ∣ x-x%385 := ⟨x/385, by omega⟩
  have hd := (hm.trans hx).add hi
  rw [hr] at hd
  convert hd using 1 <;> ring

/-- The five children cover their parent class; unchanged parents are repeated
only in the certificate map, not added to the actual family. -/
theorem covers (x : ℤ) : ∃ j, (modulus j : ℤ) ∣ x-residue j := by
  obtain ⟨i,k,hk⟩ := base_covers x
  have hn : 0 ≤ k % 5 := Int.emod_nonneg _ (by norm_num)
  have hl : k % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  let t : Fin 5 := ⟨(k % 5).toNat, by omega⟩
  have ht : (t.val : ℤ) = k % 5 := Int.toNat_of_nonneg hn
  have he : k = 5*(k/5)+k%5 := by omega
  have hd : 5*(baseModulus i : ℤ) ∣
      x-(baseResidue i+(baseModulus i : ℤ)*(t.val : ℤ)) := by
    refine ⟨k/5, ?_⟩
    rw [ht]
    calc
      x-(baseResidue i+(baseModulus i : ℤ)*(k%5)) =
          (x-baseResidue i)-(baseModulus i : ℤ)*(k%5) := by ring
      _ = (baseModulus i : ℤ)*k-(baseModulus i : ℤ)*(k%5) := by rw [hk]
      _ = (5*(baseModulus i : ℤ))*(k/5) := by
        conv_lhs => arg 1; arg 2; rw [he]
        ring
  have hh := ((refinement_data i t).1.trans hd).add (refinement_data i t).2
  refine ⟨child i t, ?_⟩
  convert hh using 1 <;> ring

theorem multiplicity_bound (d : ℕ) :
    (Finset.univ.filter (fun i => modulus i=d)).card ≤ logCap d := by
  classical
  by_cases h : ∃ j, d=labels j
  · obtain ⟨j,rfl⟩ := h
    rw [arithmetic_data.2.2.2.1 j]
    exact arithmetic_data.2.2.2.2.2 j
  · have he : Finset.univ.filter (fun i => modulus i=d) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨j,hj⟩ := arithmetic_data.2.2.1 i
      exact h ⟨j,(Finset.mem_filter.mp hi).2.symm.trans hj⟩
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

theorem energy_value : energy = 1266143/3705625 := by
  decide +kernel

theorem energy_lt : energy < 7/20 := by
  rw [energy_value]
  norm_num

theorem not_injective : ¬ Function.Injective modulus := by
  intro h
  have hh := h (show modulus 0=modulus 1 by rfl)
  have : (0 : Fin 29) ≠ 1 := by decide
  exact this hh

#print axioms covers
#print axioms arithmetic_data
#print axioms multiplicity_bound
#print axioms energy_value
#print axioms energy_lt
#print axioms not_injective
end Erdos7LowEnergyMultiplicityCover
