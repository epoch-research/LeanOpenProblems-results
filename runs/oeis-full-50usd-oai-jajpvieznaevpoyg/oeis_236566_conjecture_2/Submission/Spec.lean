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

/-- The finite verification of Lemoine's conjecture for the odd numbers up to `61`. -/
private lemma lemoine_small {k : ℕ} (hk : Odd k) (h5 : 5 < k) (h61 : ¬ 61 < k) :
    ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q := by
  rcases hk with ⟨m, rfl⟩
  have hmlo : 3 ≤ m := by omega
  have hmhi : m ≤ 30 := by omega
  interval_cases m
  · exact ⟨3, 2, by norm_num⟩
  · exact ⟨5, 2, by norm_num⟩
  · exact ⟨7, 2, by norm_num⟩
  · exact ⟨7, 3, by norm_num⟩
  · exact ⟨11, 2, by norm_num⟩
  · exact ⟨13, 2, by norm_num⟩
  · exact ⟨13, 3, by norm_num⟩
  · exact ⟨17, 2, by norm_num⟩
  · exact ⟨19, 2, by norm_num⟩
  · exact ⟨19, 3, by norm_num⟩
  · exact ⟨23, 2, by norm_num⟩
  · exact ⟨23, 3, by norm_num⟩
  · exact ⟨17, 7, by norm_num⟩
  · exact ⟨29, 2, by norm_num⟩
  · exact ⟨31, 2, by norm_num⟩
  · exact ⟨31, 3, by norm_num⟩
  · exact ⟨29, 5, by norm_num⟩
  · exact ⟨37, 2, by norm_num⟩
  · exact ⟨37, 3, by norm_num⟩
  · exact ⟨41, 2, by norm_num⟩
  · exact ⟨43, 2, by norm_num⟩
  · exact ⟨43, 3, by norm_num⟩
  · exact ⟨47, 2, by norm_num⟩
  · exact ⟨47, 3, by norm_num⟩
  · exact ⟨41, 7, by norm_num⟩
  · exact ⟨53, 2, by norm_num⟩
  · exact ⟨53, 3, by norm_num⟩
  · exact ⟨47, 7, by norm_num⟩

private lemma lemoine_of_a236566 (hA : a236566_conjecture_part_ii) : lemoine_conjecture := by
  intro k hk h5
  by_cases h61 : 61 < k
  · let n := k / 2
    have hk_eq : 2 * n + 1 = k := by
      dsimp [n]
      rcases hk with ⟨m, rfl⟩
      omega
    have hn : 30 < n := by
      omega
    rcases hA n hn with ⟨p, q, hp, hq, _hspecial, hsum⟩
    refine ⟨q, p, hq, hp, ?_⟩
    omega
  · exact lemoine_small hk h5 h61

private lemma a236566_special_infinite (hA : a236566_conjecture_part_ii) :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)} := by
  classical
  by_contra hfin_not
  have hfin : Set.Finite {p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)} :=
    Set.not_infinite.mp hfin_not
  let t : Finset ℕ := hfin.toFinset
  let ell : ℕ → ℕ := fun p => Nat.nth Nat.Prime (p + 2)
  let ι := Option {p : ℕ // p ∈ t}
  let modulus : ι → ℕ := fun i =>
    match i with
    | none => 2
    | some p => ell p.1
  let residue : ι → ℕ := fun i =>
    match i with
    | none => 1
    | some p => 2 * p.1
  have hell_prime : ∀ p, Nat.Prime (ell p) := by
    intro p
    exact Nat.prime_nth_prime (p + 2)
  have hell_gt_two : ∀ p, 2 < ell p := by
    intro p
    have hle : p + 2 + 2 ≤ ell p := Nat.add_two_le_nth_prime (p + 2)
    omega
  have hmod_ne0 : ∀ i : ι, modulus i ≠ 0 := by
    intro i
    cases i with
    | none => norm_num [modulus]
    | some p =>
        have hp := (hell_prime p.1).pos
        dsimp [modulus]
        omega
  have hpair : (Set.univ : Set ι).Pairwise (Function.onFun Nat.Coprime modulus) := by
    intro a _ b _ hne
    cases a with
    | none =>
        cases b with
        | none => contradiction
        | some q =>
            dsimp [Function.onFun, modulus]
            exact (Nat.coprime_primes Nat.prime_two (hell_prime q.1)).2 (by
              have hgt := hell_gt_two q.1
              omega)
    | some p =>
        cases b with
        | none =>
            dsimp [Function.onFun, modulus]
            exact (Nat.coprime_primes (hell_prime p.1) Nat.prime_two).2 (by
              have hgt := hell_gt_two p.1
              omega)
        | some q =>
            dsimp [Function.onFun, modulus]
            exact (Nat.coprime_primes (hell_prime p.1) (hell_prime q.1)).2 (by
              intro heq
              have hmono := Nat.nth_strictMono Nat.infinite_setOf_prime
              have hidx : p.1 + 2 = q.1 + 2 := hmono.injective heq
              have hpq : p = q := by
                apply Subtype.ext
                omega
              exact hne (by simp [hpq]))
  let crt := Nat.chineseRemainderOfFinset residue modulus (Finset.univ : Finset ι)
    (by intro i _hi; exact hmod_ne0 i) (by simpa using hpair)
  let r : ℕ := crt.1
  let P : ℕ := ∏ i : ι, modulus i
  let B : ℕ := ∑ p ∈ t, (2 * p + ell p)
  let K : ℕ := B + 100
  let M : ℕ := r + K * P
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos (by
      intro i hi
      have := hmod_ne0 i
      omega)
  have hM_mod : ∀ i : ι, M ≡ residue i [MOD modulus i] := by
    intro i
    have hcrt : r ≡ residue i [MOD modulus i] := crt.2 i (Finset.mem_univ i)
    have hdvdP : modulus i ∣ P := by
      dsimp [P]
      exact Finset.dvd_prod_of_mem (f := modulus) (Finset.mem_univ i)
    have hzero : K * P ≡ 0 [MOD modulus i] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact dvd_mul_of_dvd_right hdvdP K
    have hadd : M ≡ r [MOD modulus i] := by
      dsimp [M]
      simpa using (Nat.ModEq.add (Nat.ModEq.refl r) hzero)
    exact hadd.trans hcrt
  have hM_odd_mod : M % 2 = 1 := by
    have h := hM_mod (none : ι)
    simpa [Nat.ModEq, modulus, residue] using h
  have hM_eq : 2 * (M / 2) + 1 = M := by
    have htwo := Nat.two_mul_odd_div_two hM_odd_mod
    omega
  have hM_gt61 : 61 < M := by
    have hKpos : 0 < K := by dsimp [K]; omega
    have hKP : K ≤ K * P := by
      exact Nat.le_mul_of_pos_right K hPpos
    dsimp [M]
    omega
  let n : ℕ := M / 2
  have hn : 30 < n := by
    dsimp [n]
    omega
  rcases hA n hn with ⟨p, q, hp, hq, hspecial, hsum⟩
  have htarget : 2 * n + 1 = M := by
    dsimp [n]
    exact hM_eq
  have hsumM : M = 2 * p + q := by
    omega
  have hp_mem_set : p ∈ ({p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)} : Set ℕ) :=
    ⟨hp, hspecial⟩
  have hp_mem_t : p ∈ t := by
    dsimp [t]
    exact (hfin.mem_toFinset).2 hp_mem_set
  let ip : ι := some ⟨p, hp_mem_t⟩
  have hmodp : M ≡ 2 * p [MOD ell p] := by
    have h := hM_mod ip
    simpa [ip, modulus, residue] using h
  have hle_two_p : 2 * p ≤ M := by omega
  have hdvd_q : ell p ∣ q := by
    have hdvd : ell p ∣ M - 2 * p := (Nat.modEq_iff_dvd' hle_two_p).mp hmodp.symm
    have hqeq : q = M - 2 * p := by omega
    rwa [← hqeq] at hdvd
  have hell_lt_q : ell p < q := by
    have hterm_le_B : 2 * p + ell p ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (s := t) (f := fun x => 2 * x + ell x)
        (by intro x hx; exact Nat.zero_le _) hp_mem_t
    have hB_lt_M : B < M := by
      have hKP : K ≤ K * P := Nat.le_mul_of_pos_right K hPpos
      have hB_lt_K : B < K := by dsimp [K]; omega
      have hK_le_M : K ≤ M := by dsimp [M]; omega
      omega
    omega
  exact Nat.not_prime_of_dvd_of_lt hdvd_q (by
    have hgt := hell_gt_two p
    omega) hell_lt_q hq

private lemma twin_prime_of_a236566 (hA : a236566_conjecture_part_ii) : twin_prime_conjecture := by
  classical
  have hS := a236566_special_infinite hA
  let S : Set ℕ := {p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)}
  let f : ℕ → ℕ := fun p => Nat.nth Nat.Prime (p + 1)
  have hinj : Set.InjOn f S := by
    intro a ha b hb hEq
    have hmono := Nat.nth_strictMono Nat.infinite_setOf_prime
    have hidx : a + 1 = b + 1 := hmono.injective hEq
    omega
  have himg : Set.Infinite (f '' S) := (Set.infinite_image_iff hinj).2 (by simpa [S] using hS)
  exact Set.Infinite.mono (s := f '' S)
    (t := {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}) (by
      intro r hr
      rcases hr with ⟨p, hpS, rfl⟩
      exact ⟨Nat.prime_nth_prime (p + 1), hpS.2⟩) himg

/--
A236566: Conjecture: Part (ii) implies both Lemoine's conjecture (cf. A046927) and the twin prime conjecture.
-/
theorem oeis_236566_conjecture_2 :
  a236566_conjecture_part_ii → lemoine_conjecture ∧ twin_prime_conjecture := by
  intro hA
  exact ⟨lemoine_of_a236566 hA, twin_prime_of_a236566 hA⟩
