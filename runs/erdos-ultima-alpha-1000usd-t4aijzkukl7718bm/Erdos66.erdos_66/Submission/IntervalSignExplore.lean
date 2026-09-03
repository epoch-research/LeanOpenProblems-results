import Submission.PrimeSignExplore
import Submission.IntervalSquareclassExplore

/-! Realizing a finite sign pattern on an interval by quadratic characters at
arbitrarily large primes. These finite results do not settle Erdős 66. -/
namespace Erdos66IntervalSign
open Erdos66PrimeSign Erdos66IntervalSquareclass

lemma legendre_factorization (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    legendreSym p (n : ℤ) =
      ∏ q ∈ n.primeFactors, (legendreSym p (q : ℤ)) ^ n.factorization q := by
  have hprod : (∏ q ∈ n.primeFactors, q ^ n.factorization q) = n :=
    Nat.factorization_prod_pow_eq_self hn
  calc
    legendreSym p (n : ℤ) = (legendreSym.hom p)
        (∏ q ∈ n.primeFactors, (q : ℤ) ^ n.factorization q) := by
      change (legendreSym.hom p) (n : ℤ) = _
      congr 1
      exact_mod_cast hprod.symm
    _ = _ := by simp only [map_prod, map_pow, legendreSym.hom_apply]

lemma legendre_two_of_one_mod_eight (p : ℕ) [Fact p.Prime] (hp : p % 8 = 1) :
    legendreSym p 2 = 1 := by
  rw [legendreSym.at_two (by omega : p ≠ 2), ZMod.χ₈_nat_eq_if_mod_eight]
  have hp2 : p % 2 = 1 := by omega
  simp [hp, hp2]

/-- A private prime factor allows every finite collection of signs to be
prescribed independently. -/
lemma private_primes_signs {ι : Type*} [Fintype ι] (n Q : ι → ℕ)
    (hn : ∀ i, n i ≠ 0) (hQinj : Function.Injective Q)
    (hQprime : ∀ i, (Q i).Prime) (hQodd : ∀ i, Q i ≠ 2)
    (hval : ∀ i, (n i).factorization (Q i) = 1)
    (hprivate : ∀ i j, j ≠ i → ¬Q i ∣ n j)
    (ε : ι → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (N : ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime, N < p ∧ p % 8 = 1 ∧
      ∀ i, @legendreSym p ⟨hp⟩ (n i : ℤ) = ε i := by
  classical
  let σ (q : ℕ) : ℤ := if h : ∃ i, Q i = q then ε (Classical.choose h) else 1
  have hσ (q : ℕ) : σ q = 1 ∨ σ q = -1 := by
    dsimp only [σ]
    split_ifs with h
    · exact hε _
    · exact Or.inl rfl
  have hσQ (i : ι) : σ (Q i) = ε i := by
    dsimp only [σ]
    rw [dif_pos (show ∃ j, Q j = Q i from ⟨i, rfl⟩)]
    congr 1
    apply hQinj
    exact Classical.choose_spec (show ∃ j, Q j = Q i from ⟨i, rfl⟩)
  have hσother (i : ι) (q : ℕ) (hq : q ∣ n i) (hqi : q ≠ Q i) : σ q = 1 := by
    dsimp only [σ]
    apply dif_neg
    rintro ⟨j, hj⟩
    have hij : i ≠ j := by intro h; subst j; exact hqi hj.symm
    exact hprivate j i hij (hj ▸ hq)
  let S := (Finset.univ.biUnion (fun i ↦ (n i).primeFactors)).erase 2
  have hSp (q : ℕ) (hq : q ∈ S) : q.Prime := by
    obtain ⟨_, hq⟩ := Finset.mem_erase.mp hq
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hq
    exact Nat.prime_of_mem_primeFactors hi
  have hSo (q : ℕ) (hq : q ∈ S) : q ≠ 2 := (Finset.mem_erase.mp hq).1
  have hQi (i : ι) : Q i ∈ (n i).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hQprime i, ?_, hn i⟩
    have hh : 1 ≤ (n i).factorization (Q i) := by rw [hval i]
    simpa only [pow_one] using ((hQprime i).pow_dvd_iff_le_factorization (hn i)).mpr hh
  have hQS (i : ι) : Q i ∈ S :=
    Finset.mem_erase.mpr ⟨hQodd i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hQi i⟩⟩
  obtain ⟨p, hp, hpN, hp8, hsymbols⟩ :=
    exists_prime_legendre_signs S hSp hSo σ (fun q _ ↦ hσ q) N
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hpN, hp8, ?_⟩
  intro i
  have hmain : legendreSym p (Q i : ℤ) = ε i := (hsymbols _ (hQS i)).trans (hσQ i)
  have hother (q : ℕ) (hq : q ∈ (n i).primeFactors) (hne : q ≠ Q i) :
      legendreSym p (q : ℤ) = 1 := by
    by_cases hq2 : q = 2
    · subst q
      exact legendre_two_of_one_mod_eight p hp8
    · have hqS : q ∈ S := Finset.mem_erase.mpr ⟨hq2,
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hq⟩⟩
      exact (hsymbols q hqS).trans (hσother i q (Nat.dvd_of_mem_primeFactors hq) hne)
  rw [legendre_factorization p (n i) (hn i),
    Finset.prod_eq_single (Q i) (fun q hq hne ↦ by rw [hother q hq hne, one_pow])
      (fun h ↦ False.elim (h (hQi i))), hval i, pow_one, hmain]

/-- There are intervals on which any sign pattern can be realized by quadratic
characters for arbitrarily large primes. The interval is chosen before the signs. -/
theorem exists_interval_all_signs (h : ℕ) :
    ∃ a : ℕ, 0 < a ∧ ∀ ε : Fin h → ℤ,
      (∀ i, ε i = 1 ∨ ε i = -1) → ∀ N : ℕ,
      ∃ p : ℕ, ∃ hp : p.Prime, N < p ∧ p % 8 = 1 ∧
        ∀ i, @legendreSym p ⟨hp⟩ ((a + i.val : ℕ) : ℤ) = ε i := by
  obtain ⟨a, ha, Q, hQinj, hQ⟩ := exists_interval_private_primes h
  refine ⟨a, ha, ?_⟩
  intro ε hε N
  exact private_primes_signs (fun i : Fin h ↦ a + i.val) Q
    (fun i ↦ by dsimp only; omega) hQinj (fun i ↦ (hQ i).1)
    (fun i ↦ by have hh := (hQ i).2.1; omega)
    (fun i ↦ (hQ i).2.2.1) (fun i j hji ↦ (hQ i).2.2.2 j hji) ε hε N

end Erdos66IntervalSign
