import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A236566: Number of ordered ways to write $2n = p + q$ with $p, q$ and $\operatorname{prime}(p + 2) + 2$ all prime.
Here $\operatorname{prime}(k)$ denotes the $k$-th prime number $p_k$.
Transcribing this to Mathlib's 0-indexed $p'_{k} = \operatorname{Nat.nth\ Nat.Prime}\ k$, we use $\operatorname{Nat.nth\ Nat.Prime}\ (p+1)$ for $\operatorname{prime}(p + 2)$.
-/
noncomputable def A236566 (n : ℕ) : ℕ :=
  Finset.card <| (Finset.range (2 * n)).filter fun p =>
    Nat.Prime p ∧
    Nat.Prime (2 * n - p) ∧
    Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)

/-- Twin Prime Conjecture: There are infinitely many primes $p$ such that $p + 2$ is prime. -/
def twin_prime_conjecture : Prop := Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}

/-- Lemoine's Conjecture (or Levy's conjecture): Every odd number $k > 5$ can be written as $p + 2q$, where $p$ and $q$ are prime numbers. -/
def lemoine_conjecture : Prop :=
  ∀ k : ℕ, Odd k → 5 < k → ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q

/--
Conjecture A236566 part (ii):
If $n > 30$, then $2n + 1$ can be written as $2p + q$ with $p, q$ and $\operatorname{prime}(p + 2) + 2$ all prime.
Note: We interpret $\operatorname{prime}(p + 2)$ as $\operatorname{Nat.nth\ Nat.Prime}\ (p + 1)$, following the setup of A236566's Lean definition above,
where $p$ is one of the primes involved in the sum $2n+1 = 2p+q$.
-/
def a236566_conjecture_part_ii : Prop :=
  ∀ n : ℕ, 30 < n → ∃ (p q : ℕ),
    Nat.Prime p ∧
    Nat.Prime q ∧
    Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2) ∧
    2 * n + 1 = 2 * p + q

/--
A236566: Conjecture: Part (ii) implies both Lemoine's conjecture (cf. A046927) and the twin prime conjecture.
-/
theorem oeis_236566_conjecture_2 :
  a236566_conjecture_part_ii → lemoine_conjecture ∧ twin_prime_conjecture := by
  intro hii
  unfold a236566_conjecture_part_ii at hii
  constructor
  · -- Lemoine's conjecture
    unfold lemoine_conjecture
    intro k hodd hk5
    obtain ⟨n, rfl⟩ := hodd
    by_cases hbig : 30 < n
    · obtain ⟨p, q, hp, hq, _, heq⟩ := hii n hbig
      exact ⟨q, p, hq, hp, by omega⟩
    · push_neg at hbig
      have hlow : 3 ≤ n := by omega
      interval_cases n
      · exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨5, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨7, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨3, 5, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨11, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨13, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨5, 7, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨17, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨19, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨19, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨23, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨23, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨17, 7, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨29, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨29, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨31, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨29, 5, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨37, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨37, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨41, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨43, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨43, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨47, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨47, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨41, 7, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨53, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨53, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨47, 7, by norm_num, by norm_num, by norm_num⟩
  · -- twin prime conjecture
    show Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}
    by_contra hcon
    rw [Set.not_infinite] at hcon
    -- T : the set of admissible p
    set T : Set ℕ := {p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)} with hTdef
    -- 2 ∉ T
    have h2notT : (2 : ℕ) ∉ T := by
      rintro ⟨-, h⟩
      norm_num [Nat.nth_prime_three_eq_seven] at h
    -- the injection p ↦ prime(p+1) into the twin primes
    have hf_inj : Function.Injective (fun p : ℕ => Nat.nth Nat.Prime (p + 1)) := by
      intro a b hab
      simp only at hab
      have h2 := Nat.nth_injective Nat.infinite_setOf_prime hab
      omega
    -- T is finite, because it injects into the (assumed finite) set of twin primes
    have hTfin : T.Finite := by
      have himg : (fun p : ℕ => Nat.nth Nat.Prime (p + 1)) '' T ⊆
          {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} := by
        rintro x ⟨p, hp, rfl⟩
        exact ⟨Nat.prime_nth_prime _, hp.2⟩
      exact Set.Finite.of_finite_image (hcon.subset himg) hf_inj.injOn
    -- a witness in T from part (ii)
    obtain ⟨p0, q0, hp0, hq0, hcond0, -⟩ := hii 31 (by norm_num)
    have hp0T : p0 ∈ T := ⟨hp0, hcond0⟩
    set P : ℕ := ∏ t ∈ hTfin.toFinset, t with hPdef
    -- P > 0
    have hPpos : 0 < P := by
      rw [hPdef]
      exact Finset.prod_pos (fun t ht => (hTfin.mem_toFinset.mp ht).1.pos)
    -- P is odd (every element of T is an odd prime)
    have hPodd : Odd P := by
      rw [hPdef]
      refine Finset.prod_induction (fun t => t) Odd (fun a b ha hb => ha.mul hb) odd_one ?_
      intro t ht
      have htT : t ∈ T := hTfin.mem_toFinset.mp ht
      exact htT.1.odd_of_ne_two (by rintro rfl; exact h2notT htT)
    -- P ≥ 3
    have hp0F : p0 ∈ hTfin.toFinset := hTfin.mem_toFinset.mpr hp0T
    have hp0dvd : p0 ∣ P := by rw [hPdef]; exact Finset.dvd_prod_of_mem _ hp0F
    have hp0ne2 : p0 ≠ 2 := by rintro rfl; exact h2notT hp0T
    have hp0ge3 : 3 ≤ p0 := by have := hp0.two_le; omega
    have hPge3 : 3 ≤ P := le_trans hp0ge3 (Nat.le_of_dvd hPpos hp0dvd)
    -- m = 21 * P is odd and large; write it as 2 * n + 1
    have hmodd : Odd (21 * P) := (Nat.odd_iff.mpr (by norm_num)).mul hPodd
    obtain ⟨n, hn⟩ := hmodd
    have hngt : 30 < n := by omega
    -- apply part (ii) to n
    obtain ⟨p, q, hp, hq, hcond, heq⟩ := hii n hngt
    have hpT : p ∈ T := ⟨hp, hcond⟩
    have hpF : p ∈ hTfin.toFinset := hTfin.mem_toFinset.mpr hpT
    have hpdvdP : p ∣ P := by rw [hPdef]; exact Finset.dvd_prod_of_mem _ hpF
    have hpne2 : p ≠ 2 := by rintro rfl; exact h2notT hpT
    have hpge3 : 3 ≤ p := by have := hp.two_le; omega
    have hple : p ≤ P := Nat.le_of_dvd hPpos hpdvdP
    have hm : 21 * P = 2 * p + q := by omega
    have hpdvdm : p ∣ 21 * P := hpdvdP.trans (dvd_mul_left P 21)
    -- p divides q = m - 2p, and 1 < p < q, so q cannot be prime — contradiction
    have hpq : p ∣ q := by
      have h2p : p ∣ 2 * p := dvd_mul_left p 2
      have hqe : q = 21 * P - 2 * p := by omega
      rw [hqe]
      exact Nat.dvd_sub hpdvdm h2p
    have hq_gt : p < q := by omega
    rcases hq.eq_one_or_self_of_dvd p hpq with h1 | hself
    · omega
    · omega
