import Submission.PrimeLoserCollisionEnergy
import Submission.ThreePrimePatternSieve

/-! Exact signed-cofactor coordinates for collisions of prime-loser incidences.
Distinct comparisons have a nonzero three-form determinant. -/
namespace Erdos371
open Finset FiniteSieve

def loserIncidenceCofactor (n : ℕ) : ℕ :=
  if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then primeCofactor n else primeCofactor (n+1)

def winnerIncidenceCofactor (n : ℕ) : ℕ :=
  if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then primeCofactor (n+1) else primeCofactor n

def incidenceShift (n : ℕ) : ℤ :=
  if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then 1 else -1

lemma incidenceShift_cases (n : ℕ) : incidenceShift n=1 ∨ incidenceShift n= -1 := by
  unfold incidenceShift
  split_ifs <;> simp

lemma incidenceShift_natAbs (n : ℕ) : (incidenceShift n).natAbs=1 := by
  rcases incidenceShift_cases n with h | h <;> simp [h]

lemma loserIncidence_equations (n : ℕ) :
    (loserIncidenceCofactor n : ℤ)*primeLoser n+incidenceShift n=
        (winnerIncidenceCofactor n : ℤ)*primeWinner n ∧
      2*(n : ℤ)+1=2*loserIncidenceCofactor n*primeLoser n+incidenceShift n := by
  have h₁ : (Nat.maxPrimeFac n : ℤ)*primeCofactor n=n := by
    exact_mod_cast maxPrimeFac_mul_primeCofactor n
  have h₂ : (Nat.maxPrimeFac (n+1) : ℤ)*primeCofactor (n+1)=(n : ℤ)+1 := by
    exact_mod_cast maxPrimeFac_mul_primeCofactor (n+1)
  unfold loserIncidenceCofactor winnerIncidenceCofactor incidenceShift primeLoser primeWinner
  split_ifs with h
  · rw [min_eq_left h.le,max_eq_right h.le]
    constructor <;> nlinarith
  · rw [min_eq_right (not_lt.mp h),max_eq_left (not_lt.mp h)]
    constructor <;> nlinarith

lemma loserIncidence_cofactor_bounds (B N n : ℕ) (hB : 1 ≤ B)
    (hn : n ∈ bothAboveSet B N) :
    loserIncidenceCofactor n ∈ Icc 1 (N/(B+1)) ∧
      winnerIncidenceCofactor n ∈ Icc 1 (N/(B+1)) := by
  have hh := bothAbove_cofactor_data B N 0 n hB (Nat.zero_le _) hn
  unfold loserIncidenceCofactor winnerIncidenceCofactor
  split_ifs
  · exact ⟨hh.2.1,hh.2.2.1⟩
  · exact ⟨hh.2.2.1,hh.2.1⟩

lemma loserIncidence_product_le_endpoint (N n : ℕ) (hn : n<N) :
    loserIncidenceCofactor n*primeLoser n ≤ N := by
  have hh := (loserIncidence_equations n).2
  have hn' : (n : ℤ)<N := by exact_mod_cast hn
  have hp : (loserIncidenceCofactor n : ℤ)*primeLoser n ≤ N := by
    rcases incidenceShift_cases n with he | he <;> rw [he] at hh <;> nlinarith
  exact_mod_cast hp

lemma signed_slopes_eq_of_det_zero (k l : ℕ) (e d : ℤ)
    (hk : 0<k) (hl : 0<l) (he : e=1 ∨ e= -1) (hd : d=1 ∨ d= -1)
    (hdet : (l : ℤ)*e-k*d=0) : k=l ∧ e=d := by
  rcases he with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num at hdet ⊢ <;> omega

/-- A zero determinant would identify both the sign and the cofactor, and
hence reconstruct the very same comparison. -/
lemma primeLoserCollisions_det_ne_zero (B N n m : ℕ) (hB : 1 ≤ B)
    (hnm : (n,m) ∈ primeLoserCollisions B N) :
    (loserIncidenceCofactor m : ℤ)*incidenceShift n-
      loserIncidenceCofactor n*incidenceShift m ≠ 0 := by
  obtain ⟨hnm,he⟩ := mem_filter.mp hnm
  obtain ⟨hn,hm,hne⟩ := mem_offDiag.mp hnm
  have hnco := (mem_Icc.mp (loserIncidence_cofactor_bounds B N n hB hn).1).1
  have hmco := (mem_Icc.mp (loserIncidence_cofactor_bounds B N m hB hm).1).1
  intro hdet
  obtain ⟨hkl,hed⟩ := signed_slopes_eq_of_det_zero _ _ _ _ hnco hmco
    (incidenceShift_cases n) (incidenceShift_cases m) hdet
  have h₁ := (loserIncidence_equations n).2
  have h₂ := (loserIncidence_equations m).2
  rw [hkl,hed,he] at h₁
  apply hne
  have hh : (n : ℤ)=m := by nlinarith [h₁,h₂]
  exact_mod_cast hh

lemma primeLoser_prime_of_one_lt (n : ℕ) (hn : 1<primeLoser n) : (primeLoser n).Prime := by
  rcases primeLabel_pair_cases n with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [← ha] at hn ⊢
    exact Nat.prime_maxPrimeFac_of_one_lt n ((Nat.one_lt_maxPrimeFac_iff n).mp hn)
  · rw [← hb] at hn ⊢
    exact Nat.prime_maxPrimeFac_of_one_lt (n+1) ((Nat.one_lt_maxPrimeFac_iff (n+1)).mp hn)

def primeLoserCollisionFiber (B N k l a b : ℕ) (e d : ℤ) : Finset (ℕ × ℕ) :=
  (primeLoserCollisions B N).filter fun nm =>
    loserIncidenceCofactor nm.1=k ∧ loserIncidenceCofactor nm.2=l ∧
      winnerIncidenceCofactor nm.1=a ∧ winnerIncidenceCofactor nm.2=b ∧
        incidenceShift nm.1=e ∧ incidenceShift nm.2=d

lemma primeLoserCollisionFiber_prime_injective (B N k l a b : ℕ) (e d : ℤ) :
    Set.InjOn (fun nm : ℕ × ℕ => primeLoser nm.1) (primeLoserCollisionFiber B N k l a b e d) := by
  intro nm hnm uv huv hprime
  dsimp only at hprime
  change nm ∈ primeLoserCollisionFiber B N k l a b e d at hnm
  change uv ∈ primeLoserCollisionFiber B N k l a b e d at huv
  obtain ⟨hnm,hkn,hlm,han,hbm,hen,hdm⟩ := mem_filter.mp hnm
  obtain ⟨huv,hku,hlv,hau,hbv,heu,hdv⟩ := mem_filter.mp huv
  have he₁ := (mem_filter.mp hnm).2
  have he₂ := (mem_filter.mp huv).2
  have hn := (loserIncidence_equations nm.1).2
  have hm := (loserIncidence_equations nm.2).2
  have hu := (loserIncidence_equations uv.1).2
  have hv := (loserIncidence_equations uv.2).2
  rw [hkn,hen,hprime] at hn
  rw [hku,heu] at hu
  rw [hlm,hdm,← he₁,hprime,he₂] at hm
  rw [hlv,hdv] at hv
  apply Prod.ext <;> omega

/-- The map to the common loser prime embeds each fixed-cofactor fiber into
one of the previously sieved three-prime patterns. -/
lemma primeLoserCollisionFiber_card_le_pattern (B N k l a b z : ℕ) (e d : ℤ)
    (hB : 1 ≤ B) (hz : z ≤ B) (hk : 0<k) :
    (primeLoserCollisionFiber B N k l a b e d).card ≤
      (threePrimePatternSet (N/(max k l)+1) k l a b z e d).card := by
  apply card_le_card_of_injOn (f := fun nm : ℕ × ℕ => primeLoser nm.1) _
    (primeLoserCollisionFiber_prime_injective B N k l a b e d)
  intro nm hnm
  dsimp only
  change nm ∈ primeLoserCollisionFiber B N k l a b e d at hnm
  obtain ⟨hnm,hkn,hlm,han,hbm,hen,hdm⟩ := mem_filter.mp hnm
  obtain ⟨hnm,he⟩ := mem_filter.mp hnm
  obtain ⟨hn,hm,_⟩ := mem_offDiag.mp hnm
  obtain ⟨hnN,hnB,hnB'⟩ := mem_filter.mp hn
  obtain ⟨hmN,hmB,hmB'⟩ := mem_filter.mp hm
  have hp : B < primeLoser nm.1 := lt_min hnB hnB'
  have hpm : B < primeLoser nm.2 := lt_min hmB hmB'
  have hq : B < primeWinner nm.1 := hp.trans (primeLoser_lt_primeWinner _)
  have hr : B < primeWinner nm.2 := hpm.trans (primeLoser_lt_primeWinner _)
  have hpp := primeLoser_prime_of_one_lt nm.1 (by omega)
  have hqp : (primeWinner nm.1).Prime := by
    rcases primeWinner_prime_or_one nm.1 with hh | hh
    · exact hh
    · omega
  have hrp : (primeWinner nm.2).Prime := by
    rcases primeWinner_prime_or_one nm.2 with hh | hh
    · exact hh
    · omega
  have hpk := loserIncidence_product_le_endpoint N nm.1 (mem_range.mp hnN)
  have hpl := loserIncidence_product_le_endpoint N nm.2 (mem_range.mp hmN)
  rw [hkn] at hpk
  rw [hlm,← he] at hpl
  have hmax : primeLoser nm.1 ≤ N/(max k l) := by
    apply (Nat.le_div_iff_mul_le (lt_max_of_lt_left hk)).mpr
    rcases le_total k l with hh | hh
    · rw [max_eq_right hh]
      nlinarith
    · rw [max_eq_left hh]
      nlinarith
  have heq := (loserIncidence_equations nm.1).1
  have her := (loserIncidence_equations nm.2).1
  rw [hkn,han,hen] at heq
  rw [hlm,hbm,hdm,← he] at her
  exact (mem_threePrimePatternSet _ _ _ _ _ _ _ _ _).mpr
    ⟨by omega,hpp,by omega,primeWinner nm.1,primeWinner nm.2,hqp,hrp,by omega,by omega,heq,her⟩

#print axioms primeLoserCollisions_det_ne_zero
#print axioms primeLoserCollisionFiber_card_le_pattern
end Erdos371
