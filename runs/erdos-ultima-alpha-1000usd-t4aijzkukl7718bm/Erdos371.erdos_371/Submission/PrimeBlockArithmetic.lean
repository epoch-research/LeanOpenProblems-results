import Submission.PrimeBlockWitness
import Submission.RichPowerPrimeBands

/-! Identification of prime-colour atoms with divisibility, and an explicit
upper bound for the proportion of unoccupied prime blocks. -/
namespace Erdos371.FiniteSieve
open Finset

lemma dvd_succ_iff_mod_pred (p n : ℕ) (hp : 1<p) :
    p ∣ n+1 ↔ n%p=p-1 := by
  have hr : n%p<p := Nat.mod_lt n (by omega)
  have he : (n+1)%p=(n%p+1)%p := by rw [Nat.add_mod,Nat.mod_eq_of_lt hp]
  rw [Nat.dvd_iff_mod_eq_zero,he]
  by_cases h : n%p+1=p
  · rw [h,Nat.mod_self]
    exact ⟨fun _ => by omega,fun _ => rfl⟩
  · have hlt : n%p+1<p := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

lemma primeAtom_false_mem (P : Finset ℕ) (n p : ℕ) :
    (p,false) ∈ activePrimeAtoms P n ↔ p∈P ∧ p∣n := by
  simp only [activePrimeAtoms,mem_filter,primeAtoms,mem_product,mem_univ,and_true,
    primeAtomResidue,Bool.false_eq_true,if_false,Nat.dvd_iff_mod_eq_zero]

lemma primeAtom_true_mem (P : Finset ℕ) (n p : ℕ) (hp : 1<p) :
    (p,true) ∈ activePrimeAtoms P n ↔ p∈P ∧ p∣n+1 := by
  simp only [activePrimeAtoms,mem_filter,primeAtoms,mem_product,mem_univ,and_true,
    primeAtomResidue,if_true,dvd_succ_iff_mod_pred p n hp]

lemma activeBlockPrimes_arithmetic (P : Finset ℕ) (hP : ∀ p∈P, p.Prime) (n : ℕ) :
    activeBlockPrimes P (activePrimeAtoms P n) = P.filter (fun p => p∣n*(n+1)) := by
  apply filter_congr
  intro p hp
  rw [primeAtom_false_mem,primeAtom_true_mem P n p (hP p hp).one_lt]
  simp only [hp,true_and,(hP p hp).dvd_mul]

lemma prime_atomColour_arithmetic (P : Finset ℕ) (p n : ℕ) (hpP : p∈P)
    (hp : p.Prime) (hpn : p∣n*(n+1)) :
    atomColour p (activePrimeAtoms P n) = if p∣n+1 then 1 else -1 := by
  have hdiv := hp.dvd_mul.mp hpn
  have hnot : ¬(p∣n ∧ p∣n+1) := by
    rintro ⟨hd,hs⟩
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hd).mpr hs)
  simp only [atomColour,primeAtom_true_mem P n p hp.one_lt,primeAtom_false_mem,hpP,true_and]
  split_ifs <;> simp_all

noncomputable def emptyPrimeBlockCount (P : Finset ℕ) (N : ℕ) : ℕ :=
  ((range N).filter (fun n => activeBlockPrimes P (activePrimeAtoms P n)=∅)).card

lemma primeDivisorCount_zero_of_block_empty (P : Finset ℕ) (hP : ∀ p∈P, p.Prime)
    (n : ℕ) (h : activeBlockPrimes P (activePrimeAtoms P n)=∅) :
    primeDivisorCountIn P (n+1)=0 := by
  have he : P.filter (fun p => p∣n+1)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpP,hpd⟩ := mem_filter.mp hp
    have hm : p ∈ activeBlockPrimes P (activePrimeAtoms P n) := by
      rw [activeBlockPrimes_arithmetic P hP n]
      exact mem_filter.mpr ⟨hpP,dvd_mul_of_dvd_right hpd n⟩
    rw [h] at hm
    exact notMem_empty p hm
  simp only [primeDivisorCountIn,he,card_empty]

/-- A large reciprocal-prime mass makes the empty-block proportion small.
Only one-integer divisor-count variance is used for this coverage estimate. -/
theorem emptyPrimeBlockCount_bound (P : Finset ℕ) (hP : ∀ p∈P, p.Prime)
    (N : ℕ) (hN : 0<N) (hA : 0<primeReciprocalMass P) :
    (emptyPrimeBlockCount P N : ℝ)/N ≤
      4/primeReciprocalMass P+8*P.card/((N : ℝ)*primeReciprocalMass P) := by
  have hs : (range N).filter (fun n => activeBlockPrimes P (activePrimeAtoms P n)=∅) ⊆
      (range N).filter (fun n => (primeDivisorCountIn P (n+1) : ℝ) ≤ primeReciprocalMass P/2) := by
    intro n hn
    obtain ⟨hn,hz⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hn,?_⟩
    rw [primeDivisorCount_zero_of_block_empty P hP n hz,Nat.cast_zero]
    positivity
  exact (div_le_div_of_nonneg_right (show (emptyPrimeBlockCount P N : ℝ)≤
      ((range N).filter (fun n => (primeDivisorCountIn P (n+1) : ℝ)≤primeReciprocalMass P/2)).card by
        exact_mod_cast card_le_card hs) (Nat.cast_nonneg N)).trans
    (primeDivisorCountIn_low_count_bound P hP N hN hA)

#print axioms emptyPrimeBlockCount_bound
end Erdos371.FiniteSieve
