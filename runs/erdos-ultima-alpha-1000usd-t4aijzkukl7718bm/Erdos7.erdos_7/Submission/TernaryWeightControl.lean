import Submission.TernaryWeightedLoad

/-!
# The weighted branch inequalities are not sufficient for coverage

An explicit distinct odd divisor-closed PARTIAL family, with a private point
for every class, has load greater than one half on every ternary fiber.
Integer2 is uncovered. No odd covering witness is claimed.
-/
namespace Erdos7TernaryWeightControl
open scoped BigOperators
open Erdos7WeightedExceptionArithmetic
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
def modulus : Fin 27 → ℕ := ![3,5,15,7,21,11,33,13,39,17,51,19,57,23,69,29,87,31,93,37,111,41,123,43,129,47,141]
def residue : Fin 27 → ℤ := ![0,0,1,0,8,0,23,0,1,0,35,0,1,0,47,0,1,0,32,0,1,0,83,0,1,0,95]
def privatePoint : Fin 27 → ℤ := ![3,184466934776547425,40992652172566096,58560931675094422,131762096268962447,18633023714802772,111798142288816622,141897642135805712,173430451499318092,192906598459134562,198934929660982517,177994410749300147,37756390158942457,129215968804827907,13367169186706337,265038699391591127,81278534480087947,161987093262559567,29752731415572167,257588962976259917,77553666272422342,289948027562052862,247455644212441667,271695485329798532,238329373096314502,207143721084775477,52331045326680122]

lemma arithmetic_data :
    Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 307444891294245705) ∧
    (∀ i j, (modulus j : ℤ) ∣ privatePoint i-residue j ↔ j=i) ∧
    (∀ i, ¬ (modulus i : ℤ) ∣ 2-residue i) ∧
    (∀ i, (modulus i).factorization 3 ≤ 1) ∧
    (∀ i, 3 ∣ modulus i → (modulus i).factorization 3=1) := by
  simp only [← Nat.primeFactorsList_count_eq]
  decide +kernel

lemma divisor_data : ∀ i, ∀ d : ↥(modulus i).divisors,
    1 < d.val → ∃ j, modulus j=d.val := by
  decide +kernel

theorem divisor_closed (i : Fin 27) (d : ℕ) (hd : d ∣ modulus i) (h1 : 1<d) :
    ∃ j, modulus j=d := by
  have hp : 0 < modulus i := lt_trans (by omega : 0<1) (arithmetic_data.2.1 i).1
  exact divisor_data i ⟨d,Nat.mem_divisors.mpr ⟨hd,hp.ne'⟩⟩ h1

def coarseLoad (r : ℤ) : ℚ :=
  ∑ i, if 3 ∣ modulus i ∧ (3 : ℤ) ∣ r-residue i then weight (ordCompl[3] (modulus i)) else 0

lemma load_data : ∀ r : Fin 3, (1/2 : ℚ) < coarseLoad (r.val : ℤ) := by
  simp only [coarseLoad,← Nat.primeFactorsList_count_eq]
  decide +kernel

lemma coarseLoad_periodic (r : ℤ) : coarseLoad r = coarseLoad (r%3) := by
  apply Finset.sum_congr rfl
  intro i _
  have he : (3 : ℤ) ∣ r-residue i ↔ (3 : ℤ) ∣ r%3-residue i := by omega
  simp only [he]

theorem every_branch_high (r : ℤ) : (1/2 : ℚ) < coarseLoad r := by
  rw [coarseLoad_periodic]
  have hr : r%3=0 ∨ r%3=1 ∨ r%3=2 := by omega
  rcases hr with h | h | h
  · simpa only [h] using load_data 0
  · simpa only [h] using load_data 1
  · simpa only [h] using load_data 2

theorem actual_fiber_load (r : ℤ) :
    (1/2 : ℚ) < ∑ j : {j // 3 ∣ modulus j ∧
      ((3^((modulus j).factorization 3) : ℕ) : ℤ) ∣ r-residue j},
      weight (ordCompl[3] (modulus j)) := by
  have he : (∑ j : {j // 3 ∣ modulus j ∧
      ((3^((modulus j).factorization 3) : ℕ) : ℤ) ∣ r-residue j},
      weight (ordCompl[3] (modulus j))) = coarseLoad r := by
    rw [← Finset.sum_subtype
      (p := fun j => 3 ∣ modulus j ∧ ((3^((modulus j).factorization 3) : ℕ) : ℤ) ∣ r-residue j)
      (Finset.univ.filter (fun j => 3 ∣ modulus j ∧
        ((3^((modulus j).factorization 3) : ℕ) : ℤ) ∣ r-residue j))
      (by simp) (fun j => weight (ordCompl[3] (modulus j))), Finset.sum_filter]
    unfold coarseLoad
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 3 ∣ modulus i
    · simp only [hi,arithmetic_data.2.2.2.2.2 i hi,pow_one,Nat.cast_ofNat,true_and]
    · simp only [hi,false_and,ite_false]
  rw [he]
  exact every_branch_high r

theorem not_cover : ¬ ∀ x : ℤ, ∃ i, (modulus i : ℤ) ∣ x-residue i := by
  intro h
  obtain ⟨i,hi⟩ := h 2
  exact arithmetic_data.2.2.2.1 i hi

#print axioms actual_fiber_load
#print axioms arithmetic_data
#print axioms divisor_closed
#print axioms not_cover
end Erdos7TernaryWeightControl
