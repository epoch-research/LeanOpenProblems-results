import Submission.LowEnergyMultiplicityCover
import Submission.FiniteHingeComparison

/-!
A repeated-modulus covering system whose reciprocal-square-weighted multiplicity
law is below a finite geometric law for every increasing convex test. This is
an obstruction to a proposed moment-only criterion, NOT a strict odd cover.
-/
namespace Erdos7ConvexMultiplicityCover
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4000
def modulus : Fin 48 → ℕ := ![5,5,125,125,125,125,125,25,25,25,25,7,11,11,11,175,175,175,175,175,35,35,35,35,35,275,275,275,275,275,385,385,385,385,385,385,385,55,55,55,55,55,55,77,875,1375,1925,9625]
def residue : Fin 48 → ℤ := ![0,1,2,27,52,77,102,7,12,17,22,0,0,1,2,8,43,78,113,148,23,3,18,33,13,14,69,124,179,234,4,59,114,169,224,279,334,49,39,29,19,9,54,0,0,0,0,0]
def splitSize : Fin 29 → ℕ := ![1,1,5,1,1,1,1,1,1,1,1,5,1,1,1,1,1,1,1,1,1,1,7,1,1,1,1,1,1]
def child : Fin 29 → Fin 7 → Fin 48 := ![![0,0,0,0,0,0,0],![1,1,1,1,1,1,1],![2,3,4,5,6,2,2],![7,7,7,7,7,7,7],![8,8,8,8,8,8,8],![9,9,9,9,9,9,9],![10,10,10,10,10,10,10],![11,11,11,11,11,11,11],![12,12,12,12,12,12,12],![13,13,13,13,13,13,13],![14,14,14,14,14,14,14],![15,16,17,18,19,15,15],![20,20,20,20,20,20,20],![21,21,21,21,21,21,21],![22,22,22,22,22,22,22],![23,23,23,23,23,23,23],![24,24,24,24,24,24,24],![25,25,25,25,25,25,25],![26,26,26,26,26,26,26],![27,27,27,27,27,27,27],![28,28,28,28,28,28,28],![29,29,29,29,29,29,29],![30,31,32,33,34,35,36],![37,37,37,37,37,37,37],![38,38,38,38,38,38,38],![39,39,39,39,39,39,39],![40,40,40,40,40,40,40],![41,41,41,41,41,41,41],![42,42,42,42,42,42,42]]
def labels : Fin 15 → ℕ := ![5,7,11,25,35,55,77,125,175,275,385,875,1375,1925,9625]
def counts : Fin 15 → ℕ := ![2,1,3,4,5,6,1,5,5,5,7,1,1,1,1]
def lawNumerator : Fin 7 → ℕ := ![2673,3078,1026,342,114,38,19]

def weight (i : Fin 15) : ℚ := 1/(labels i : ℚ)^2
def mass : ℚ := 265719/3705625
def law (j : Fin 7) : ℚ := (lawNumerator j : ℚ)/7290
def refWeight (j : Fin 7) : ℚ := mass*law j

theorem arithmetic_data :
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ ¬ 3 ∣ modulus i ∧ modulus i ∣ 9625) ∧
    Function.Injective labels ∧
    (∀ i, ∃ j, modulus i=labels j) ∧
    (∀ j, (Finset.univ.filter (fun i => modulus i=labels j)).card=counts j) ∧
    (∀ j, 1 ≤ counts j ∧ counts j ≤ 7) ∧
    Finset.univ.image labels = (Nat.divisors 9625).erase 1 := by
  decide +kernel

theorem refinement_data :
    (∀ i, 0 < splitSize i ∧ splitSize i ≤ 7) ∧
    (∀ i t, t.val < splitSize i →
      (modulus (child i t) : ℤ) ∣
        (splitSize i : ℤ)*(Erdos7LowEnergyMultiplicityCover.modulus i : ℤ) ∧
      (modulus (child i t) : ℤ) ∣
        Erdos7LowEnergyMultiplicityCover.residue i +
          (Erdos7LowEnergyMultiplicityCover.modulus i : ℤ)*(t.val : ℤ)-
            residue (child i t)) := by
  decide +kernel

/-- Each selected parent congruence is replaced by all its children. -/
theorem covers (x : ℤ) : ∃ j, (modulus j : ℤ) ∣ x-residue j := by
  obtain ⟨i,k,hk⟩ := Erdos7LowEnergyMultiplicityCover.covers x
  let p : ℤ := splitSize i
  have hp : 0 < p := by dsimp [p]; exact_mod_cast (refinement_data.1 i).1
  have hn : 0 ≤ k % p := Int.emod_nonneg k hp.ne'
  have hl : k % p < p := Int.emod_lt_of_pos k hp
  have hp7 : p ≤ 7 := by dsimp [p]; exact_mod_cast (refinement_data.1 i).2
  let t : Fin 7 := ⟨(k%p).toNat,by omega⟩
  have ht : (t.val : ℤ)=k%p := Int.toNat_of_nonneg hn
  have htp : t.val < splitSize i := by
    have : (t.val : ℤ) < (splitSize i : ℤ) := by rw [ht]; exact hl
    exact_mod_cast this
  have he : k=p*(k/p)+k%p := by
    have hh := Int.emod_add_mul_ediv k p
    nlinarith
  have hd : p*(Erdos7LowEnergyMultiplicityCover.modulus i : ℤ) ∣
      x-(Erdos7LowEnergyMultiplicityCover.residue i +
        (Erdos7LowEnergyMultiplicityCover.modulus i : ℤ)*(t.val : ℤ)) := by
    refine ⟨k/p,?_⟩
    rw [ht]
    calc
      _ = (x-Erdos7LowEnergyMultiplicityCover.residue i) -
          (Erdos7LowEnergyMultiplicityCover.modulus i : ℤ)*(k%p) := by ring
      _ = (Erdos7LowEnergyMultiplicityCover.modulus i : ℤ)*k -
          (Erdos7LowEnergyMultiplicityCover.modulus i : ℤ)*(k%p) := by rw [hk]
      _ = _ := by conv_lhs => arg 1; arg 2; rw [he]
                  ring
  have hh := ((refinement_data.2 i t htp).1.trans hd).add
    (refinement_data.2 i t htp).2
  refine ⟨child i t,?_⟩
  convert hh using 1 <;> ring

/-- Every nontrivial divisor of the common period occurs as a modulus. -/
theorem divisor_complete (d : ℕ) (hd : d ∣ 9625) (h1 : 1 < d) :
    ∃ i, modulus i=d := by
  have hd' : d ∈ (Nat.divisors 9625).erase 1 :=
    Finset.mem_erase.mpr ⟨by omega,Nat.mem_divisors.mpr ⟨hd,by decide⟩⟩
  rw [← arithmetic_data.2.2.2.2.2] at hd'
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hd'
  have hc := (arithmetic_data.2.2.2.2.1 j).1
  have hh : 0 < (Finset.univ.filter (fun i => modulus i=labels j)).card := by
    rw [arithmetic_data.2.2.2.1 j]; omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hh
  exact ⟨i,(Finset.mem_filter.mp hi).2.trans hj⟩

theorem not_injective : ¬ Function.Injective modulus := by
  intro h
  have he := h (show modulus 0=modulus 1 by rfl)
  exact (by decide : (0 : Fin 48) ≠ 1) he

/-- Exact rational mass, mean, and all hinge comparisons through the support. -/
theorem comparison_data :
    (∀ i, 0 ≤ weight i) ∧ (∀ j, 0 ≤ refWeight j) ∧
    (∑ i, weight i)=mass ∧ (∑ j, law j)=1 ∧
    (∑ i, weight i)=(∑ j, refWeight j) ∧
    (∀ k : Fin 8,
      (∑ i, weight i*((counts i-k.val : ℕ) : ℚ)) ≤
        ∑ j, refWeight j*((j.val+1-k.val : ℕ) : ℚ)) := by
  decide +kernel

/-- A stronger-than-limit finite law: its tails are (19/10)/3^k, not 2/3^k. -/
theorem law_tail : ∀ k : Fin 7,
    (∑ j, if k.val < j.val+1 then law j else 0) =
      if k.val=0 then 1 else (19 : ℚ)/(10*3^k.val) := by
  decide +kernel

/-- One and the same repeated covering family passes EVERY increasing-convex
multiplicity comparison against the specified finite law. The test may be signed. -/
theorem convex_comparison (φ : ℝ → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ i, (weight i : ℝ)*φ (counts i)) ≤
      ∑ j, (refWeight j : ℝ)*φ (j.val+1) := by
  have hμ (i : Fin 15) : (0 : ℝ) ≤ weight i := by
    exact_mod_cast comparison_data.1 i
  have hν (j : Fin 7) : (0 : ℝ) ≤ refWeight j := by
    exact_mod_cast comparison_data.2.1 j
  have hmass : (∑ i, (weight i : ℝ)) = ∑ j, (refWeight j : ℝ) := by
    exact_mod_cast comparison_data.2.2.2.2.1
  have hh (k : Fin 8) :
      (∑ i, (weight i : ℝ)*((counts i-k.val : ℕ) : ℝ)) ≤
        ∑ j, (refWeight j : ℝ)*((j.val+1-k.val : ℕ) : ℝ) := by
    exact_mod_cast comparison_data.2.2.2.2.2 k
  have hmean : (∑ i, (weight i : ℝ)*(counts i : ℝ)) ≤
      ∑ j, (refWeight j : ℝ)*((j.val+1 : ℕ) : ℝ) := by
    simpa using hh 0
  have h := Erdos7FiniteHingeComparison.convex_monotone_comparison
    (fun i => (weight i : ℝ)) (fun j => (refWeight j : ℝ)) counts
    (fun j : Fin 7 => j.val+1) 7 hμ hν
    (fun i => (arithmetic_data.2.2.2.2.1 i).2) (fun j => by change j.val+1 ≤ 7; omega)
    hmass hmean (fun t ht => hh ⟨t+1,by omega⟩) φ hφ hmφ 0
  simpa only [zero_add,Nat.cast_add,Nat.cast_one] using h

noncomputable def exponentialEnergy (b : ℝ) : ℝ :=
  ∑ i, (weight i : ℝ)*(b^counts i-1)
noncomputable def exponentialLaw (b : ℝ) : ℝ :=
  ∑ j, (law j : ℝ)*(b^(j.val+1)-1)

lemma exponential_comparison (b : ℝ) (hb : 1 ≤ b) :
    exponentialEnergy b ≤ (mass : ℝ)*exponentialLaw b := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => b^x-1) := by
    simpa only [sub_eq_add_neg] using
      (convexOn_rpow_left (by linarith : 0 < b)).add_const (-1)
  have hmono : Monotone (fun x : ℝ => b^x-1) := by
    intro x y hxy
    exact sub_le_sub_right (Real.rpow_le_rpow_of_exponent_le hb hxy) 1
  have hh := convex_comparison (fun x : ℝ => b^x-1) hconv hmono
  have hh' : exponentialEnergy b ≤
      ∑ j, (refWeight j : ℝ)*(b^(j.val+1)-1) := by
    simpa only [exponentialEnergy,← Real.rpow_natCast,Nat.cast_add,Nat.cast_one] using hh
  convert hh' using 1
  simp only [refWeight,Rat.cast_mul,mul_assoc,exponentialLaw,Finset.mul_sum]

lemma exponential_law_identity (b : ℝ) :
    (3-b)*exponentialLaw b + (19/10)*(b-1)*b^7/3^6 =
      (b-1)*(3+(9/10)*b) := by
  norm_num [exponentialLaw,law,lawNumerator,Fin.sum_univ_succ]
  ring

/-- No choice of exponential base between1 and3 repairs the proposed
reciprocal-square moment criterion, even using only this finite divisor set. -/
theorem exponential_all_bases (b : ℝ) (hb : 1 < b) (hb3 : b < 3) :
    exponentialEnergy b <
      (mass : ℝ)*((b-1)*(3+b)/(3-b)) := by
  have hb0 : 0 < b := by linarith
  have he := exponential_law_identity b
  have hsub : 0 < b-1 := by linarith
  have hrem : 0 ≤ (19/10 : ℝ)*(b-1)*b^7/3^6 := by positivity
  have hp : 0 < (b-1)*b := mul_pos (by linarith) hb0
  have hbound : exponentialLaw b < (b-1)*(3+b)/(3-b) := by
    apply (lt_div_iff₀ (by linarith : 0 < 3-b)).mpr
    nlinarith
  have hmass : (0 : ℝ) < mass := by norm_num [mass]
  exact (exponential_comparison b hb.le).trans_lt
    (mul_lt_mul_of_pos_left hbound hmass)

#print axioms covers
#print axioms divisor_complete
#print axioms not_injective
#print axioms convex_comparison
#print axioms law_tail
#print axioms exponential_all_bases
end Erdos7ConvexMultiplicityCover
