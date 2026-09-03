import Submission.PrimeBlockArithmetic
import Submission.PrimeBandDensity

/-! Consecutive prime blocks obtained by iterated powering. The total band
has a reciprocal-mass bound independent of its eventual power exponent. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

noncomputable def primesThrough (t : ℕ) : Finset ℕ := (t+1).primesBelow

def blockCutoff (t J i : ℕ) : ℕ := t^(2^(J*i))

noncomputable def iteratedPrimeBlock (t J i : ℕ) : Finset ℕ :=
  largePrimeSet (blockCutoff t J i) (blockCutoff t J (i+1))

lemma mem_primesThrough (p t : ℕ) : p∈primesThrough t ↔ p.Prime ∧ p≤t := by
  simp only [primesThrough,Nat.mem_primesBelow]
  constructor
  · rintro ⟨hl,hp⟩; exact ⟨hp,by omega⟩
  · rintro ⟨hp,hl⟩; exact ⟨by omega,hp⟩

lemma mem_largePrimeSet_iff (p a b : ℕ) : p∈largePrimeSet a b ↔ p.Prime ∧ a<p ∧ p≤b := by
  simp only [largePrimeSet,mem_filter,Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hu,hp⟩,hl⟩; exact ⟨hp,hl,by omega⟩
  · rintro ⟨hp,hl,hu⟩; exact ⟨⟨by omega,hp⟩,hl⟩

lemma blockCutoff_zero (t J : ℕ) : blockCutoff t J 0=t := by simp [blockCutoff]

lemma blockCutoff_step (t J i : ℕ) : blockCutoff t J (i+1)=(blockCutoff t J i)^(2^J) := by
  simp only [blockCutoff,Nat.mul_add,Nat.mul_one,pow_add,pow_mul]

lemma blockCutoff_mono (t J : ℕ) (ht : 0<t) : Monotone (blockCutoff t J) := by
  intro i j hij
  apply Nat.pow_le_pow_right ht
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left J hij)

lemma blockCutoff_base_le (t J i : ℕ) (ht : 0<t) : t≤blockCutoff t J i := by
  simpa only [blockCutoff_zero] using blockCutoff_mono t J ht (Nat.zero_le i)

lemma iteratedPrimeBlock_mass_lower (t J i : ℕ) (ht : 1<t)
    (hlog : 2*(1+primePowerErrorConstant+Real.log 4) ≤ Real.log t) :
    (J : ℝ)/4≤primeReciprocalMass (iteratedPrimeBlock t J i) := by
  have hti := blockCutoff_base_le t J i (by omega)
  have hi : 1<blockCutoff t J i := lt_of_lt_of_le ht hti
  have hlogi : 2*(1+primePowerErrorConstant+Real.log 4) ≤ Real.log (blockCutoff t J i) :=
    hlog.trans (Real.log_le_log (by exact_mod_cast (show 0<t by omega)) (by exact_mod_cast hti))
  simpa only [iteratedPrimeBlock,blockCutoff_step] using
    iterated_square_prime_band_mass (blockCutoff t J i) J hi hlogi

lemma iteratedPrimeBlock_subset (t J i K : ℕ) (ht : 0<t) (hi : i<K) :
    iteratedPrimeBlock t J i ⊆ largePrimeSet t (blockCutoff t J K) := by
  intro p hp
  obtain ⟨hpp,hpl,hpu⟩ := (mem_largePrimeSet_iff p _ _).mp hp
  exact (mem_largePrimeSet_iff p _ _).mpr ⟨hpp,
    (blockCutoff_base_le t J i ht).trans_lt hpl,
    hpu.trans (blockCutoff_mono t J ht (by omega))⟩

lemma iteratedPrimeBlock_disjoint (t J i j : ℕ) (ht : 0<t) (hij : i<j) :
    Disjoint (iteratedPrimeBlock t J i) (iteratedPrimeBlock t J j) := by
  apply disjoint_left.mpr
  intro p hp hq
  have hu := ((mem_largePrimeSet_iff p _ _).mp hp).2.2
  have hl := ((mem_largePrimeSet_iff p _ _).mp hq).2.1
  have hm := blockCutoff_mono t J ht (show i+1≤j by omega)
  omega

lemma primesThrough_blockCutoff_mono (t J : ℕ) (ht : 0<t) :
    Monotone (fun i => primesThrough (blockCutoff t J i)) := by
  intro i j hij p hp
  obtain ⟨hpp,hpl⟩ := (mem_primesThrough p _).mp hp
  exact (mem_primesThrough p _).mpr ⟨hpp,hpl.trans (blockCutoff_mono t J ht hij)⟩

lemma primesThrough_blockCutoff_difference (t J i j K : ℕ) (ht : 0<t) (hj : j≤K) :
    primesThrough (blockCutoff t J j)\primesThrough (blockCutoff t J i) ⊆
      largePrimeSet t (blockCutoff t J K) := by
  intro p hp
  obtain ⟨hpj,hpi⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hpp,hpj⟩ := (mem_primesThrough p _).mp hpj
  have hpgt : blockCutoff t J i<p := by
    by_contra hn
    exact hpi ((mem_primesThrough p _).mpr ⟨hpp,by omega⟩)
  exact (mem_largePrimeSet_iff p _ _).mpr ⟨hpp,
    (blockCutoff_base_le t J i ht).trans_lt hpgt,hpj.trans (blockCutoff_mono t J ht hj)⟩

lemma iteratedPrimeBlocks_total_mass (t J K : ℕ) (ht : 1<t)
    (hlog : 2≤Real.log t/Real.log 2) :
    2*primeReciprocalMass (largePrimeSet t (blockCutoff t J K)) ≤ 16*(2^(J*K) : ℕ) := by
  let Q : ℕ := 2^(J*K)
  have hQ : (1 : ℝ)≤Q := by exact_mod_cast (Nat.pow_pos (by norm_num : 0<(2 : ℕ)) : 1≤Q)
  have h := prime_real_band_reciprocal_bound (largePrimeSet t (blockCutoff t J K)) t 1 Q
    (by norm_num) hQ ht (by simpa only [one_mul] using hlog) (by
      intro p hp
      obtain ⟨hpp,hl,hu⟩ := (mem_largePrimeSet_iff p _ _).mp hp
      refine ⟨hpp,?_,?_⟩
      · simpa only [Real.rpow_one] using (show (t : ℝ)≤p by exact_mod_cast hl.le)
      · simpa only [Real.rpow_natCast,← Nat.cast_pow] using (show (p : ℝ)≤blockCutoff t J K by exact_mod_cast hu))
  have hdiv : 16/(Real.log t/Real.log 2)≤(8 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0<Real.log t/Real.log 2)).mpr
    linarith
  simp only [one_mul,primeReciprocalMass] at h ⊢
  dsimp only [Q] at h
  linarith

lemma iteratedPrimeBlock_empty_bound (t J K i N : ℕ) (ht : 1<t) (hJ : 0<J)
    (hN : 0<N) (hi : i<K)
    (hlog : 2*(1+primePowerErrorConstant+Real.log 4)≤Real.log t) :
    (emptyPrimeBlockCount (iteratedPrimeBlock t J i) N : ℝ)/N ≤
      16/(J : ℝ)+32*(blockCutoff t J K+1 : ℝ)/((N : ℝ)*J) := by
  have hm := iteratedPrimeBlock_mass_lower t J i ht hlog
  have hJr : (0 : ℝ)<J := by exact_mod_cast hJ
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hmass : 0<primeReciprocalMass (iteratedPrimeBlock t J i) := lt_of_lt_of_le (by positivity) hm
  have hprimes (p : ℕ) (hp : p∈iteratedPrimeBlock t J i) := ((mem_largePrimeSet_iff p _ _).mp hp).1
  have hcard : (iteratedPrimeBlock t J i).card≤blockCutoff t J K+1 := by
    apply (card_le_card _).trans_eq (card_range _)
    intro p hp
    have h := ((mem_largePrimeSet_iff p _ _).mp
      (iteratedPrimeBlock_subset t J i K (by omega) hi hp)).2.2
    exact mem_range.mpr (by omega)
  have hcardr : ((iteratedPrimeBlock t J i).card : ℝ)≤blockCutoff t J K+1 := by exact_mod_cast hcard
  calc
    _ ≤ 4/primeReciprocalMass (iteratedPrimeBlock t J i)+
        8*(iteratedPrimeBlock t J i).card/((N : ℝ)*primeReciprocalMass (iteratedPrimeBlock t J i)) :=
      emptyPrimeBlockCount_bound _ hprimes N hN hmass
    _ ≤ 4/((J : ℝ)/4)+8*(blockCutoff t J K+1 : ℝ)/((N : ℝ)*((J : ℝ)/4)) := by
      gcongr
    _ = _ := by field_simp; ring

#print axioms iteratedPrimeBlock_mass_lower
end Erdos371.FiniteSieve
