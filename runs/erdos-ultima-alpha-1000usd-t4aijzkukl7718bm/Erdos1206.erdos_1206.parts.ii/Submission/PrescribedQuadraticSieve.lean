import Submission.AffineQuadraticSquarefreeSieve

/-! A squarefree sieve that retains prescribed local parameter residues.
This is an auxiliary parameter-counting result, not a Sidon-density theorem. -/
namespace Erdos1206.PrescribedQuadraticSieve
open Finset Filter QuadraticSquarefreeSieve AffineQuadraticSquarefreeSieve
open scoped Classical Topology

/-- A single positive-offset progression realizes the given residues at
all primes up to K. -/
theorem exists_progression (T U : ℕ → ℕ) (K : ℕ) :
    ∃ v w : ℕ, 0 < v ∧ 0 < w ∧ ∀ p, p.Prime → p ≤ K → ∀ t u : ℕ,
      Nat.ModEq (p^2) (sieveModulus K*t+v) (T p) ∧
      Nat.ModEq (p^2) (sieveModulus K*u+w) (U p) := by
  let P := (range (K+1)).filter Nat.Prime
  have hP {p : ℕ} (hp : p ∈ P) : p.Prime ∧ p ≤ K := by
    simpa only [P,mem_filter,mem_range,Nat.lt_succ_iff,and_comm] using hp
  have hn : ∀ p ∈ P, p^2 ≠ 0 := fun p hp => pow_ne_zero _ (hP hp).1.ne_zero
  have hc : (P : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p => p^2)) := by
    intro p hp q hq hpq
    exact Nat.coprime_pow_primes 2 2 (hP hp).1 (hP hq).1 hpq
  let v := Nat.chineseRemainderOfFinset T (fun p => p^2) P hn hc
  let w := Nat.chineseRemainderOfFinset U (fun p => p^2) P hn hc
  refine ⟨v+sieveModulus K,w+sieveModulus K,
    by have := sieveModulus_pos K; omega,by have := sieveModulus_pos K; omega,?_⟩
  intro p hp hpK t u
  have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩
  have hM : p^2 ∣ sieveModulus K :=
    pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpK) 2
  have hM0 : Nat.ModEq (p^2) (sieveModulus K) 0 := Nat.modEq_zero_iff_dvd.mpr hM
  have ht : Nat.ModEq (p^2) (sieveModulus K*t+(v+sieveModulus K)) (T p) := by
    simpa only [zero_mul,zero_add,add_zero] using
      (hM0.mul (Nat.ModEq.refl t)).add ((v.property p hpP).add hM0)
  have hu : Nat.ModEq (p^2) (sieveModulus K*u+(w+sieveModulus K)) (U p) := by
    simpa only [zero_mul,zero_add,add_zero] using
      (hM0.mul (Nat.ModEq.refl u)).add ((w.property p hpP).add hM0)
  exact ⟨ht,hu⟩


/-- Finite local tests, with the CRT residue choices exposed in the output. -/
theorem prescribed_progression_sieve {r : ℕ} (hr : 0 < r)
    (a b c : Fin r → ℕ) (K S : ℕ) (hK : 12*r ≤ K)
    (ha : ∀ i, 0 < a i ∧ a i ≤ K)
    (hd : ∀ i, discriminant (a i) (b i) (c i) ≠ 0 ∧
      (discriminant (a i) (b i) (c i)).natAbs ≤ K)
    (hS : ∀ i, a i+b i+c i ≤ S)
    (T U : ℕ → ℕ)
    (hlocal : ∀ p, p.Prime → p ≤ K → ∀ i,
      ¬ p^2 ∣ quad (a i) (b i) (c i) (T p) (U p)) :
    ∃ v w : ℕ, 0 < v ∧ 0 < w ∧
      (∀ p, p.Prime → p ≤ K → ∀ t u : ℕ,
        Nat.ModEq (p^2) (sieveModulus K*t+v) (T p) ∧
        Nat.ModEq (p^2) (sieveModulus K*u+w) (U p)) ∧
      ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤
        (AffineQuadraticSquarefreeSieve.goodPairs a b c (sieveModulus K) v w N).card := by
  obtain ⟨v,w,hv,hw,hres⟩ := exists_progression T U K
  refine ⟨v,w,hv,hw,hres,AffineQuadraticSquarefreeSieve.goodPairs_eventually_large
    hr a b c (sieveModulus K) v w K (S*(sieveModulus K+v+w+1)) hK ?_ ?_ ?_⟩
  · intro i p hp hpK t u hh
    obtain ⟨ht,hu⟩ := hres p hp hpK t u
    exact hlocal p hp hpK i ((quad_modEq (a i) (b i) (c i) ht hu).dvd_iff dvd_rfl |>.mp hh)
  · intro i p hp hpK
    exact large_prime_regular (a i) (b i) (c i) K (ha i).1 (ha i).2
      (hd i).1 (hd i).2 hp hpK
  · intro N hN i x hx
    exact AffineQuadraticSquarefreeSieve.quad_size_bound
      (a i) (b i) (c i) (sieveModulus K) v w N S (ha i).1 hw (hS i) hN hx

#print axioms exists_progression
#print axioms prescribed_progression_sieve
end Erdos1206.PrescribedQuadraticSieve
