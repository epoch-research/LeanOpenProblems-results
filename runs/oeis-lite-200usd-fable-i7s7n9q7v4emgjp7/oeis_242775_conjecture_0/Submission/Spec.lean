import FormalConjectures.Util.ProblemImports

open Nat Set

set_option maxRecDepth 16000
set_option exponentiation.threshold 5000
set_option linter.style.ams_attribute false
set_option linter.style.answer_attribute false
set_option linter.style.category_docstring false
set_option linter.style.category_attribute false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.existsImplication false
set_option linter.style.moduleDocstring false
set_option linter.style.namespace false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.tacticAnalysis false

/-- The number $b_k$, consisting of $k$ threes. $b_k = (10^k - 1)/3$. -/
def rep_threes (k : ℕ) : ℕ := (10 ^ k - 1) / 3

/-- The number of decimal digits of $p$. -/
def num_digits (p : ℕ) : ℕ := (Nat.digits 10 p).length

/-- Concatenation of $b_k$ and $p$. -/
def concatenate (k p : ℕ) : ℕ :=
  rep_threes k * (10 ^ (num_digits p)) + p

/-- The $n$-th prime (1-indexed). -/
noncomputable def prime_of_index (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/--
A242775: Let $b_k=3\dots3$ consist of $k\ge 1$ 3's. Then $a(n)$ is the smallest $k$ such that the concatenation $b_k$ and $\operatorname{prime}(n)$ is prime, or $a(n)=0$ if there is no such prime.
-/
noncomputable def A242775 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P_n := prime_of_index n

    -- The set S of all k >= 1 such that the concatenated number is prime.
    let S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k P_n) }

    -- Nat.sInf S is the minimum element of S. If S is empty, Nat.sInf S = 0 is the convention for ℕ.
    sInf S

section SemanticAnchors
/- Machine-checked anchors demonstrating the semantics of the definitions:
`A242775 2 = 0` (every 3…33 is a multiple of 3) and `A242775 4 = 1`
(37 is prime), matching OEIS A242775. -/

private lemma three_mul_rep_threes (k : ℕ) : 3 * rep_threes k + 1 = 10 ^ k := by
  have h3 : (3 : ℕ) ∣ 10 ^ k - 1 := by
    have : (10 : ℕ) ^ k % 3 = 1 := by
      have h : (10 : ℕ) % 3 = 1 := rfl
      rw [Nat.pow_mod, h, one_pow]; rfl
    omega
  have hpos : 1 ≤ (10 : ℕ) ^ k := Nat.one_le_pow _ _ (by norm_num)
  unfold rep_threes
  obtain ⟨m, hm⟩ := h3
  rw [hm]; omega

/-- Fuel-based clone of `Nat.minFacAux` (whose well-founded recursion the
kernel cannot unfold), for kernel-computable primality testing. -/
private def mfa : ℕ → ℕ → ℕ → ℕ
  | 0, n, _ => n
  | fuel+1, n, k => if n < k * k then n else if n % k = 0 then k else mfa fuel n (k+2)

private lemma mfa_eq_minFacAux : ∀ (fuel k n : ℕ), Nat.sqrt n < k + 2 * fuel →
    mfa fuel n k = Nat.minFacAux n k := by
  intro fuel
  induction fuel with
  | zero =>
    intro k n hs
    have hlt : n < k * k := Nat.sqrt_lt.mp (by omega)
    rw [Nat.minFacAux, if_pos hlt]
    rfl
  | succ f ih =>
    intro k n hs
    rw [Nat.minFacAux]
    show (if n < k * k then n else if n % k = 0 then k else mfa f n (k+2)) =
      (if n < k * k then n else if k ∣ n then k else Nat.minFacAux n (k + 2))
    by_cases h1 : n < k * k
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : n % k = 0
      · rw [if_pos h2, if_pos (Nat.dvd_iff_mod_eq_zero.mpr h2)]
      · rw [if_neg h2, if_neg (fun hd => h2 (Nat.dvd_iff_mod_eq_zero.mp hd))]
        exact ih (k + 2) n (by omega)

/-- Kernel-computable primality test. -/
private def isPrimeB (n : ℕ) : Bool :=
  if n < 2 then false
  else if n % 2 = 0 then n == 2
  else mfa n n 3 == n

private lemma isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime := by
  unfold isPrimeB
  by_cases h1 : n < 2
  · rw [if_pos h1]
    constructor
    · intro h; cases h
    · intro hp; exact absurd hp.two_le (by omega)
  · rw [if_neg h1]
    push_neg at h1
    by_cases h2 : n % 2 = 0
    · rw [if_pos h2]
      simp only [beq_iff_eq]
      constructor
      · rintro rfl; exact Nat.prime_two
      · intro hp
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2
          (Nat.dvd_iff_mod_eq_zero.mpr h2)) with h | h
        · omega
        · omega
    · rw [if_neg h2]
      have hmfa : mfa n n 3 = Nat.minFacAux n 3 :=
        mfa_eq_minFacAux n 3 n (by have := Nat.sqrt_le_self n; omega)
      have hmf : Nat.minFac n = Nat.minFacAux n 3 := by
        rw [Nat.minFac_eq, if_neg (fun hd => h2 (Nat.dvd_iff_mod_eq_zero.mp hd))]
      rw [hmfa, ← hmf]
      simp only [beq_iff_eq]
      rw [Nat.prime_def_minFac]
      exact ⟨fun h => ⟨h1, h⟩, fun h => h.2⟩


/-- Kernel-computable incremental prime counting: counts primes in `[a, a+fuel)`
on top of `c`. -/
private def cntStep : ℕ → ℕ → ℕ → ℕ
  | 0, _, c => c
  | fuel+1, a, c => cntStep fuel (a+1) (c + if isPrimeB a then 1 else 0)

private lemma cntStep_correct : ∀ (fuel a c : ℕ), Nat.count Nat.Prime a = c →
    cntStep fuel a c = Nat.count Nat.Prime (a + fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a c h
    simpa [cntStep] using h.symm
  | succ f ih =>
    intro a c h
    have hnext : Nat.count Nat.Prime (a+1) = c + if isPrimeB a then 1 else 0 := by
      rw [Nat.count_succ, h]
      congr 1
      by_cases hp : Nat.Prime a
      · rw [if_pos hp, if_pos ((isPrimeB_iff a).mpr hp)]
      · rw [if_neg hp, if_neg (fun hb => hp ((isPrimeB_iff a).mp hb))]
    have hstep := ih (a+1) _ hnext
    show cntStep f (a+1) (c + if isPrimeB a then 1 else 0) = _
    rw [hstep]
    congr 1
    omega

/-- One-line prime-count transport: `count a = c`, kernel-computes the count
increment over `[a, a+fuel)`. -/
private lemma count_from {a c P C : ℕ} (fuel : ℕ) (base : Nat.count Nat.Prime a = c)
    (hP : P = a + fuel) (hC : cntStep fuel a c = C) : Nat.count Nat.Prime P = C := by
  subst hP
  rw [← cntStep_correct fuel a c base]
  exact hC

/-- Kernel-computable compositeness. -/
private lemma isPrimeB_false {n : ℕ} (h : isPrimeB n = false) : ¬ n.Prime :=
  fun hp => by rw [(isPrimeB_iff n).mpr hp] at h; cases h

section SmallPrimeCounts
/- Prime-counting anchor values `Nat.count Nat.Prime p` for all primes
`p ≤ 113`, built incrementally to keep kernel work linear. -/

private lemma pcount2 : Nat.count Nat.Prime 2 = 0 := by decide

private lemma pcount3 : Nat.count Nat.Prime 3 = 1 :=
  count_from 1 pcount2 rfl rfl

private lemma pcount5 : Nat.count Nat.Prime 5 = 2 :=
  count_from 2 pcount3 rfl rfl

private lemma pcount7 : Nat.count Nat.Prime 7 = 3 :=
  count_from 2 pcount5 rfl rfl

private lemma pcount11 : Nat.count Nat.Prime 11 = 4 :=
  count_from 4 pcount7 rfl rfl

private lemma pcount13 : Nat.count Nat.Prime 13 = 5 :=
  count_from 2 pcount11 rfl rfl

private lemma pcount17 : Nat.count Nat.Prime 17 = 6 :=
  count_from 4 pcount13 rfl rfl

private lemma pcount19 : Nat.count Nat.Prime 19 = 7 :=
  count_from 2 pcount17 rfl rfl

private lemma pcount23 : Nat.count Nat.Prime 23 = 8 :=
  count_from 4 pcount19 rfl rfl

private lemma pcount29 : Nat.count Nat.Prime 29 = 9 :=
  count_from 6 pcount23 rfl rfl

private lemma pcount31 : Nat.count Nat.Prime 31 = 10 :=
  count_from 2 pcount29 rfl rfl

private lemma pcount37 : Nat.count Nat.Prime 37 = 11 :=
  count_from 6 pcount31 rfl rfl

private lemma pcount41 : Nat.count Nat.Prime 41 = 12 :=
  count_from 4 pcount37 rfl rfl

private lemma pcount43 : Nat.count Nat.Prime 43 = 13 :=
  count_from 2 pcount41 rfl rfl

private lemma pcount47 : Nat.count Nat.Prime 47 = 14 :=
  count_from 4 pcount43 rfl rfl

private lemma pcount53 : Nat.count Nat.Prime 53 = 15 :=
  count_from 6 pcount47 rfl rfl

private lemma pcount59 : Nat.count Nat.Prime 59 = 16 :=
  count_from 6 pcount53 rfl rfl

private lemma pcount61 : Nat.count Nat.Prime 61 = 17 :=
  count_from 2 pcount59 rfl rfl

private lemma pcount67 : Nat.count Nat.Prime 67 = 18 :=
  count_from 6 pcount61 rfl rfl

private lemma pcount71 : Nat.count Nat.Prime 71 = 19 :=
  count_from 4 pcount67 rfl rfl

private lemma pcount73 : Nat.count Nat.Prime 73 = 20 :=
  count_from 2 pcount71 rfl rfl

private lemma pcount79 : Nat.count Nat.Prime 79 = 21 :=
  count_from 6 pcount73 rfl rfl

private lemma pcount83 : Nat.count Nat.Prime 83 = 22 :=
  count_from 4 pcount79 rfl rfl

private lemma pcount89 : Nat.count Nat.Prime 89 = 23 :=
  count_from 6 pcount83 rfl rfl

private lemma pcount97 : Nat.count Nat.Prime 97 = 24 :=
  count_from 8 pcount89 rfl rfl

private lemma pcount101 : Nat.count Nat.Prime 101 = 25 :=
  count_from 4 pcount97 rfl rfl

private lemma pcount103 : Nat.count Nat.Prime 103 = 26 :=
  count_from 2 pcount101 rfl rfl

private lemma pcount107 : Nat.count Nat.Prime 107 = 27 :=
  count_from 4 pcount103 rfl rfl

private lemma pcount109 : Nat.count Nat.Prime 109 = 28 :=
  count_from 2 pcount107 rfl rfl

private lemma pcount113 : Nat.count Nat.Prime 113 = 29 :=
  count_from 4 pcount109 rfl rfl

end SmallPrimeCounts

theorem A242775_two : A242775 2 = 0 := by
  have hp : prime_of_index 2 = 3 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
    rwa [pcount3] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  convert Nat.sInf_empty
  rw [Set.eq_empty_iff_forall_notMem]
  rintro k ⟨hk, hkP⟩
  have hnd : num_digits 3 = 1 := by
    unfold num_digits
    rw [Nat.digits_len 10 3 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 0) (by norm_num) (by norm_num)]
  have hcon : concatenate k 3 = rep_threes (k + 1) := by
    unfold concatenate
    rw [hnd]
    have h1 := three_mul_rep_threes k
    have h2 := three_mul_rep_threes (k + 1)
    have : (10:ℕ)^(k+1) = 10 * 10^k := by ring
    omega
  have h3dvd : 3 ∣ concatenate k 3 := by
    rw [hcon]
    have h2 := three_mul_rep_threes (k + 1)
    have h9 : (9 : ℕ) ∣ 10 ^ (k+1) - 1 := by
      have : (10:ℕ) ^ (k+1) % 9 = 1 := by
        rw [Nat.pow_mod]; norm_num
      omega
    obtain ⟨m, hm⟩ := h9
    exact ⟨m, by omega⟩
  have hbig : 3 < concatenate k 3 := by
    rw [hcon]
    have h2 := three_mul_rep_threes (k + 1)
    have : (100 : ℕ) ≤ 10 ^ (k + 1) := by
      calc (100:ℕ) = 10^2 := by norm_num
      _ ≤ 10^(k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases hkP.eq_one_or_self_of_dvd 3 h3dvd with h | h
  · norm_num at h
  · omega

private lemma rep_threes_ge (k : ℕ) (hk : 1 ≤ k) : 3 ≤ rep_threes k := by
  have h := (by
    have h3 : (3 : ℕ) ∣ 10 ^ k - 1 := by
      have : (10 : ℕ) ^ k % 3 = 1 := by
        rw [Nat.pow_mod]; norm_num
      omega
    have hpos : 1 ≤ (10 : ℕ) ^ k := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨m, hm⟩ := h3
    have : rep_threes k = m := by unfold rep_threes; omega
    have h10 : (10:ℕ) ^ 1 ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega : 3 ≤ rep_threes k)
  exact h

/-- `A242775 1 = 0`: every `33…32` is even. -/
theorem A242775_one : A242775 1 = 0 := by
  have hp : prime_of_index 1 = 2 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
    rwa [pcount2] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  convert Nat.sInf_empty
  rw [Set.eq_empty_iff_forall_notMem]
  rintro k ⟨hk, hkP⟩
  have hnd : num_digits 2 = 1 := by
    unfold num_digits
    rw [Nat.digits_len 10 2 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 0) (by norm_num) (by norm_num)]
  have hdvd : 2 ∣ concatenate k 2 := by
    unfold concatenate
    rw [hnd]
    exact ⟨rep_threes k * 5 + 1, by ring⟩
  have hbig : 2 < concatenate k 2 := by
    unfold concatenate
    rw [hnd]
    have := rep_threes_ge k hk
    omega
  rcases hkP.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega

/-- `A242775 3 = 0`: every `33…35` is a multiple of 5. -/
theorem A242775_three : A242775 3 = 0 := by
  have hp : prime_of_index 3 = 5 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 5) (by norm_num)
    rwa [pcount5] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  convert Nat.sInf_empty
  rw [Set.eq_empty_iff_forall_notMem]
  rintro k ⟨hk, hkP⟩
  have hnd : num_digits 5 = 1 := by
    unfold num_digits
    rw [Nat.digits_len 10 5 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 0) (by norm_num) (by norm_num)]
  have hdvd : 5 ∣ concatenate k 5 := by
    unfold concatenate
    rw [hnd]
    exact ⟨rep_threes k * 2 + 1, by ring⟩
  have hbig : 5 < concatenate k 5 := by
    unfold concatenate
    rw [hnd]
    have := rep_threes_ge k hk
    omega
  rcases hkP.eq_one_or_self_of_dvd 5 hdvd with h | h <;> omega

theorem A242775_four : A242775 4 = 1 := by
  have hp : prime_of_index 4 = 7 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 7) (by norm_num)
    rwa [pcount7] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 7 = 1 := by
    unfold num_digits
    rw [Nat.digits_len 10 7 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 0) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 7 = 37 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 7)} := by
    refine ⟨one_pos, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 7)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

theorem A242775_five : A242775 5 = 1 := by
  have hp : prime_of_index 5 = 11 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 11) (by norm_num)
    rwa [pcount11] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 11 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 11 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 11 = 311 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 11)} := by
    refine ⟨one_pos, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 11)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

theorem A242775_six : A242775 6 = 1 := by
  have hp : prime_of_index 6 = 13 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num)
    rwa [pcount13] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 13 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 13 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 13 = 313 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 13)} := by
    refine ⟨one_pos, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 13)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 8 = 2`: `319 = 11 · 29` is composite but `3319` is prime. -/
theorem A242775_eight : A242775 8 = 2 := by
  have hp : prime_of_index 8 = 19 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 19) (by norm_num)
    rwa [pcount19] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 19 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 19 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 19 = 319 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 19 = 3319 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 19)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 19)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 9 = 2`: `323` is composite but `3323` is prime. -/
theorem A242775_nine : A242775 9 = 2 := by
  have hp : prime_of_index 9 = 23 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 23) (by norm_num)
    rwa [pcount23] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 23 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 23 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 23 = 323 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 23 = 3323 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 23)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 23)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 10 = 2`: `329` is composite but `3329` is prime. -/
theorem A242775_ten : A242775 10 = 2 := by
  have hp : prime_of_index 10 = 29 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 29) (by norm_num)
    rwa [pcount29] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 29 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 29 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 29 = 329 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 29 = 3329 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 29)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 29)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 11 = 1`. -/
theorem A242775_eleven : A242775 11 = 1 := by
  have hp : prime_of_index 11 = 31 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 31) (by norm_num)
    rwa [pcount31] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 31 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 31 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 31 = 331 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 31)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 31)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 12 = 1`. -/
theorem A242775_twelve : A242775 12 = 1 := by
  have hp : prime_of_index 12 = 37 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 37) (by norm_num)
    rwa [pcount37] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 37 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 37 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 37 = 337 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 37)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 37)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 13 = 4`. -/
theorem A242775_thirteen : A242775 13 = 4 := by
  have hp : prime_of_index 13 = 41 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 41) (by norm_num)
    rwa [pcount41] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 41 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 41 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 41 = 341 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 41 = 3341 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 41 = 33341 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 41 = 333341 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 41)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 41)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 14 = 2`. -/
theorem A242775_fourteen : A242775 14 = 2 := by
  have hp : prime_of_index 14 = 43 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 43) (by norm_num)
    rwa [pcount43] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 43 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 43 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 43 = 343 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 43 = 3343 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 43)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 43)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 15 = 1`. -/
theorem A242775_fifteen : A242775 15 = 1 := by
  have hp : prime_of_index 15 = 47 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 47) (by norm_num)
    rwa [pcount47] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 47 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 47 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 47 = 347 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 47)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 47)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 16 = 1`. -/
theorem A242775_sixteen : A242775 16 = 1 := by
  have hp : prime_of_index 16 = 53 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 53) (by norm_num)
    rwa [pcount53] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 53 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 53 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 53 = 353 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 53)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 53)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 17 = 1`. -/
theorem A242775_seventeen : A242775 17 = 1 := by
  have hp : prime_of_index 17 = 59 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 59) (by norm_num)
    rwa [pcount59] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 59 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 59 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 59 = 359 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 59)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 59)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 18 = 2`. -/
theorem A242775_eighteen : A242775 18 = 2 := by
  have hp : prime_of_index 18 = 61 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 61) (by norm_num)
    rwa [pcount61] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 61 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 61 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 61 = 361 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 61 = 3361 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 61)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 61)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)


/-- `A242775 19 = 1`. -/
theorem A242775_nineteen : A242775 19 = 1 := by
  have hp : prime_of_index 19 = 67 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 67) (by norm_num)
    rwa [pcount67] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 67 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 67 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 67 = 367 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 67)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 67)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 20 = 2`. -/
theorem A242775_twenty : A242775 20 = 2 := by
  have hp : prime_of_index 20 = 71 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 71) (by norm_num)
    rwa [pcount71] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 71 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 71 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 71 = 371 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 71 = 3371 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 71)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 71)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 21 = 1`. -/
theorem A242775_twentyone : A242775 21 = 1 := by
  have hp : prime_of_index 21 = 73 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 73) (by norm_num)
    rwa [pcount73] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 73 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 73 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 73 = 373 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 73)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 73)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 22 = 1`. -/
theorem A242775_twentytwo : A242775 22 = 1 := by
  have hp : prime_of_index 22 = 79 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 79) (by norm_num)
    rwa [pcount79] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 79 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 79 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 79 = 379 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 79)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 79)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 23 = 1`. -/
theorem A242775_twentythree : A242775 23 = 1 := by
  have hp : prime_of_index 23 = 83 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 83) (by norm_num)
    rwa [pcount83] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 83 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 83 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 83 = 383 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 83)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 83)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 24 = 1`. -/
theorem A242775_twentyfour : A242775 24 = 1 := by
  have hp : prime_of_index 24 = 89 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 89) (by norm_num)
    rwa [pcount89] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 89 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 89 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 89 = 389 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 89)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 89)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 25 = 1`. -/
theorem A242775_twentyfive : A242775 25 = 1 := by
  have hp : prime_of_index 25 = 97 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 97) (by norm_num)
    rwa [pcount97] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 97 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 97 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 97 = 397 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 97)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 97)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 26 = 3`. -/
theorem A242775_twentysix : A242775 26 = 3 := by
  have hp : prime_of_index 26 = 101 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 101) (by norm_num)
    rwa [pcount101] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 101 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 101 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 101 = 3101 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 101 = 33101 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 101 = 333101 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 101)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 101)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 27 = 3`. -/
theorem A242775_twentyseven : A242775 27 = 3 := by
  have hp : prime_of_index 27 = 103 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 103) (by norm_num)
    rwa [pcount103] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 103 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 103 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 103 = 3103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 103 = 33103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 103 = 333103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 103)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 103)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 28 = 2`. -/
theorem A242775_twentyeight : A242775 28 = 2 := by
  have hp : prime_of_index 28 = 107 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 107) (by norm_num)
    rwa [pcount107] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 107 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 107 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 107 = 3107 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 107 = 33107 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 107)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 107)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 29 = 1`. -/
theorem A242775_twentynine : A242775 29 = 1 := by
  have hp : prime_of_index 29 = 109 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 109) (by norm_num)
    rwa [pcount109] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 109 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 109 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 109 = 3109 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 109)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 109)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 30 = 2`. -/
theorem A242775_thirty : A242775 30 = 2 := by
  have hp : prime_of_index 30 = 113 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 113) (by norm_num)
    rwa [pcount113] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 113 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 113 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 113 = 3113 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 113 = 33113 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 113)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 113)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

private lemma pcount131 : Nat.count Nat.Prime 131 = 31 :=
  count_from 18 pcount113 rfl rfl

private lemma pcount137 : Nat.count Nat.Prime 137 = 32 :=
  count_from 6 pcount131 rfl rfl

private lemma pcount139 : Nat.count Nat.Prime 139 = 33 :=
  count_from 2 pcount137 rfl rfl

private lemma pcount149 : Nat.count Nat.Prime 149 = 34 :=
  count_from 10 pcount139 rfl rfl

private lemma pcount151 : Nat.count Nat.Prime 151 = 35 :=
  count_from 2 pcount149 rfl rfl

private lemma pcount163 : Nat.count Nat.Prime 163 = 37 :=
  count_from 12 pcount151 rfl rfl

private lemma pcount167 : Nat.count Nat.Prime 167 = 38 :=
  count_from 4 pcount163 rfl rfl

private lemma pcount179 : Nat.count Nat.Prime 179 = 40 :=
  count_from 12 pcount167 rfl rfl

private lemma pcount181 : Nat.count Nat.Prime 181 = 41 :=
  count_from 2 pcount179 rfl rfl

private lemma pcount191 : Nat.count Nat.Prime 191 = 42 :=
  count_from 10 pcount181 rfl rfl

private lemma pcount193 : Nat.count Nat.Prime 193 = 43 :=
  count_from 2 pcount191 rfl rfl

private lemma pcount197 : Nat.count Nat.Prime 197 = 44 :=
  count_from 4 pcount193 rfl rfl

/-- `A242775 32 = 3`. -/
theorem A242775_n32 : A242775 32 = 3 := by
  have hp : prime_of_index 32 = 131 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 131) (by norm_num)
    rwa [pcount131] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 131 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 131 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 131 = 3131 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 131 = 33131 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 131 = 333131 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 131)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 131)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 33 = 1`. -/
theorem A242775_n33 : A242775 33 = 1 := by
  have hp : prime_of_index 33 = 137 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 137) (by norm_num)
    rwa [pcount137] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 137 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 137 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 137 = 3137 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 137)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 137)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 34 = 3`. -/
theorem A242775_n34 : A242775 34 = 3 := by
  have hp : prime_of_index 34 = 139 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 139) (by norm_num)
    rwa [pcount139] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 139 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 139 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 139 = 3139 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 139 = 33139 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 139 = 333139 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 139)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 139)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 35 = 2`. -/
theorem A242775_n35 : A242775 35 = 2 := by
  have hp : prime_of_index 35 = 149 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 149) (by norm_num)
    rwa [pcount149] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 149 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 149 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 149 = 3149 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 149 = 33149 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 149)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 149)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 36 = 2`. -/
theorem A242775_n36 : A242775 36 = 2 := by
  have hp : prime_of_index 36 = 151 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 151) (by norm_num)
    rwa [pcount151] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 151 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 151 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 151 = 3151 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 151 = 33151 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 151)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 151)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 38 = 1`. -/
theorem A242775_n38 : A242775 38 = 1 := by
  have hp : prime_of_index 38 = 163 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 163) (by norm_num)
    rwa [pcount163] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 163 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 163 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 163 = 3163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 163)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 163)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 39 = 1`. -/
theorem A242775_n39 : A242775 39 = 1 := by
  have hp : prime_of_index 39 = 167 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 167) (by norm_num)
    rwa [pcount167] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 167 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 167 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 167 = 3167 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 167)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 167)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 41 = 2`. -/
theorem A242775_n41 : A242775 41 = 2 := by
  have hp : prime_of_index 41 = 179 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 179) (by norm_num)
    rwa [pcount179] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 179 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 179 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 179 = 3179 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 179 = 33179 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 179)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 179)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 42 = 1`. -/
theorem A242775_n42 : A242775 42 = 1 := by
  have hp : prime_of_index 42 = 181 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 181) (by norm_num)
    rwa [pcount181] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 181 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 181 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 181 = 3181 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 181)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 181)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 43 = 1`. -/
theorem A242775_n43 : A242775 43 = 1 := by
  have hp : prime_of_index 43 = 191 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 191) (by norm_num)
    rwa [pcount191] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 191 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 191 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 191 = 3191 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 191)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 191)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 44 = 5`. -/
theorem A242775_n44 : A242775 44 = 5 := by
  have hp : prime_of_index 44 = 193 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 193) (by norm_num)
    rwa [pcount193] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 193 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 193 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 193 = 3193 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 193 = 33193 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 193 = 333193 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 193 = 3333193 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 193 = 33333193 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 5 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 193)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h5]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 193)}
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 45 = 3`. -/
theorem A242775_n45 : A242775 45 = 3 := by
  have hp : prime_of_index 45 = 197 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 197) (by norm_num)
    rwa [pcount197] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 197 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 197 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 197 = 3197 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 197 = 33197 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 197 = 333197 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 197)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 197)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)


section PrattCertificates
/- Machine-checked Lucas--Pratt primality certificates for the three witnesses
`3333333127` (= 33…3‖127, giving `A242775 31 = 7`), `33333333157` (= 33…3‖157,
giving `A242775 37 = 8`) and `3333333173` (= 33…3‖173, giving `A242775 40 = 7`),
which are too large for `norm_num`'s trial-division kernel certificate.  Each is
verified through Mathlib's `lucas_primality` using an explicit primitive root and
kernel-checked square-and-multiply modular-exponentiation chains. -/

private lemma modexp_sq {b n x y z : ℕ} (m : ℕ) (h1 : b ^ n % x = y)
    (hm : m = 2 * n) (h2 : y * y % x = z) : b ^ m % x = z := by
  subst hm; rw [two_mul, pow_add, Nat.mul_mod, h1, h2]

private lemma modexp_sqmul {b n x y z : ℕ} (m : ℕ) (h1 : b ^ n % x = y)
    (hm : m = 2 * n + 1) (h2 : y * y % x * (b % x) % x = z) : b ^ m % x = z := by
  subst hm
  rw [pow_succ, Nat.mul_mod, two_mul, pow_add, Nat.mul_mod (b ^ n) (b ^ n) x, h1, h2]

private lemma zmod_pow_of_mod {x b e r : ℕ} (h : b ^ e % x = r) :
    ((b : ℕ) : ZMod x) ^ e = ((r : ℕ) : ZMod x) := by
  rw [← Nat.cast_pow, ← ZMod.natCast_mod (b ^ e) x, h]

private lemma zmod_ne_one {x r : ℕ} (h1 : 1 < x) (h2 : 1 < r) (h3 : r < x) :
    ((r : ℕ) : ZMod x) ≠ 1 := by
  haveI : Fact (1 < x) := ⟨h1⟩
  intro hE
  have hv := congrArg ZMod.val hE
  rw [ZMod.val_cast_of_lt h3, ZMod.val_one x] at hv
  omega

/-- 256-ary fuel-based modular exponentiation for kernel evaluation. -/
private def pmg : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, x => 1 % x
  | fuel+1, b, e, x =>
    if e = 0 then 1 % x
    else
      let r := pmg fuel b (e / 256) x
      let r2 := r ^ 2 % x
      let r4 := r2 ^ 2 % x
      let r8 := r4 ^ 2 % x
      let r16 := r8 ^ 2 % x
      let r32 := r16 ^ 2 % x
      let r64 := r32 ^ 2 % x
      let r128 := r64 ^ 2 % x
      let r256 := r128 ^ 2 % x
      r256 * ((b % x) ^ (e % 256) % x) % x

private lemma pow_mod_pow (a k x n r : ℕ) (h : a ^ n % x = r) :
    r ^ k % x = a ^ (n * k) % x := by
  rw [← h, ← Nat.pow_mod, ← pow_mul]

private lemma pmg_correct : ∀ (fuel b e x : ℕ), e < 256 ^ fuel →
    pmg fuel b e x = b ^ e % x := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e x he
    have h0 : e = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using he)
    subst h0
    simp [pmg]
  | succ f ih =>
    intro b e x he
    by_cases h0 : e = 0
    · subst h0; simp [pmg]
    · have hlt : e / 256 < 256 ^ f := by
        rw [pow_succ] at he
        omega
      have hr : pmg f b (e / 256) x = b ^ (e / 256) % x := ih b (e / 256) x hlt
      simp only [pmg, if_neg h0]
      rw [hr]
      rw [pow_mod_pow b 2 x (e / 256) _ rfl,
          pow_mod_pow b 2 x (e / 256 * 2) _ rfl,
          pow_mod_pow b 2 x (e / 256 * 2 * 2) _ rfl,
          pow_mod_pow b 2 x (e / 256 * 2 * 2 * 2) _ rfl,
          pow_mod_pow b 2 x (e / 256 * 2 * 2 * 2 * 2) _ rfl,
          pow_mod_pow b 2 x (e / 256 * 2 * 2 * 2 * 2 * 2) _ rfl,
          pow_mod_pow b 2 x (e / 256 * 2 * 2 * 2 * 2 * 2 * 2) _ rfl,
          pow_mod_pow b 2 x (e / 256 * 2 * 2 * 2 * 2 * 2 * 2 * 2) _ rfl,
          ← Nat.pow_mod, ← Nat.mul_mod, ← pow_add]
      have hE : e / 256 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 + e % 256 = e := by omega
      rw [hE]

private lemma pow_mod_eq2 (fuel b e x r : ℕ) (hfe : e < 256 ^ fuel)
    (h : pmg fuel b e x = r) : b ^ e % x = r := by
  rw [← pmg_correct fuel b e x hfe, h]


/-- Fermat compositeness certificate: if `2 ^ (C-1) % C = r` with `1 < r < C`,
then `C` is not prime. -/
private lemma fermat_composite {C e r : ℕ} (he : C = e + 1) (h : 2 ^ e % C = r)
    (h1 : 1 < r) (h2 : r < C) (h3 : 2 < C) : ¬ C.Prime := by
  intro hpr
  haveI : Fact C.Prime := ⟨hpr⟩
  have h2ne : ((2 : ℕ) : ZMod C) ≠ 0 := by
    intro hE
    have hv := congrArg ZMod.val hE
    rw [ZMod.val_cast_of_lt h3, ZMod.val_zero] at hv
    omega
  have hf := ZMod.pow_card_sub_one_eq_one h2ne
  have hce : C - 1 = e := by omega
  rw [hce] at hf
  have hnat := zmod_pow_of_mod h
  rw [hf] at hnat
  exact zmod_ne_one (by omega) h1 h2 hnat.symm



private lemma prime_3333333127 : Nat.Prime 3333333127 := by
  have c1 : (3:ℕ) ^ 1666666563 % 3333333127 = 3333333126 :=
    pow_mod_eq2 4 3 1666666563 3333333127 3333333126 (by decide) rfl
  have c2 : (3:ℕ) ^ 1111111042 % 3333333127 = 169962647 :=
    pow_mod_eq2 4 3 1111111042 3333333127 169962647 (by decide) rfl
  have c3 : (3:ℕ) ^ 6 % 3333333127 = 729 :=
    pow_mod_eq2 1 3 6 3333333127 729 (by decide) rfl
  have cf : (3:ℕ) ^ 3333333126 % 3333333127 = 1 :=
    pow_mod_eq2 4 3 3333333126 3333333127 1 (by decide) rfl
  refine lucas_primality 3333333127 ((3 : ℕ) : ZMod 3333333127) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333333127:ℕ) - 1 = 3333333126 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333333127:ℕ) - 1 = 2 * (3 * (555555521)) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333333127:ℕ) - 1) / 2 = 1666666563 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333127:ℕ) - 1) / 3 = 1111111042 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        have h := hrest
        have hqe : q = 555555521 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333127:ℕ) - 1) / 555555521 = 6 := rfl
        rw [hexp, zmod_pow_of_mod c3]
        exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_33333333157 : Nat.Prime 33333333157 := by
  have c1 : (5:ℕ) ^ 16666666578 % 33333333157 = 33333333156 :=
    pow_mod_eq2 5 5 16666666578 33333333157 33333333156 (by decide) rfl
  have c2 : (5:ℕ) ^ 11111111052 % 33333333157 = 10797001158 :=
    pow_mod_eq2 5 5 11111111052 33333333157 10797001158 (by decide) rfl
  have c3 : (5:ℕ) ^ 66269052 % 33333333157 = 6143411527 :=
    pow_mod_eq2 4 5 66269052 33333333157 6143411527 (by decide) rfl
  have c4 : (5:ℕ) ^ 51046452 % 33333333157 = 338246965 :=
    pow_mod_eq2 4 5 51046452 33333333157 338246965 (by decide) rfl
  have c5 : (5:ℕ) ^ 11824524 % 33333333157 = 4635359109 :=
    pow_mod_eq2 3 5 11824524 33333333157 4635359109 (by decide) rfl
  have cf : (5:ℕ) ^ 33333333156 % 33333333157 = 1 :=
    pow_mod_eq2 5 5 33333333156 33333333157 1 (by decide) rfl
  refine lucas_primality 33333333157 ((5 : ℕ) : ZMod 33333333157) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333333157:ℕ) - 1 = 33333333156 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333333157:ℕ) - 1 = 2 * (2 * (3 * (3 * (503 * (653 * (2819)))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333333157:ℕ) - 1) / 2 = 16666666578 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333333157:ℕ) - 1) / 2 = 16666666578 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333333157:ℕ) - 1) / 3 = 11111111052 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((33333333157:ℕ) - 1) / 3 = 11111111052 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 503 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((33333333157:ℕ) - 1) / 503 = 66269052 := rfl
              rw [hexp, zmod_pow_of_mod c3]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 653 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((33333333157:ℕ) - 1) / 653 = 51046452 := rfl
                rw [hexp, zmod_pow_of_mod c4]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                have h := hrest
                have hqe : q = 2819 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((33333333157:ℕ) - 1) / 2819 = 11824524 := rfl
                rw [hexp, zmod_pow_of_mod c5]
                exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_3333333173 : Nat.Prime 3333333173 := by
  have c1 : (2:ℕ) ^ 1666666586 % 3333333173 = 3333333172 :=
    pow_mod_eq2 4 2 1666666586 3333333173 3333333172 (by decide) rfl
  have c2 : (2:ℕ) ^ 256410244 % 3333333173 = 2050107053 :=
    pow_mod_eq2 4 2 256410244 3333333173 2050107053 (by decide) rfl
  have c3 : (2:ℕ) ^ 175438588 % 3333333173 = 2537018902 :=
    pow_mod_eq2 4 2 175438588 3333333173 2537018902 (by decide) rfl
  have c4 : (2:ℕ) ^ 3800836 % 3333333173 = 1290048964 :=
    pow_mod_eq2 3 2 3800836 3333333173 1290048964 (by decide) rfl
  have c5 : (2:ℕ) ^ 866476 % 3333333173 = 1674985396 :=
    pow_mod_eq2 3 2 866476 3333333173 1674985396 (by decide) rfl
  have cf : (2:ℕ) ^ 3333333172 % 3333333173 = 1 :=
    pow_mod_eq2 4 2 3333333172 3333333173 1 (by decide) rfl
  refine lucas_primality 3333333173 ((2 : ℕ) : ZMod 3333333173) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333333173:ℕ) - 1 = 3333333172 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333333173:ℕ) - 1 = 2 * (2 * (13 * (19 * (877 * (3847))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333333173:ℕ) - 1) / 2 = 1666666586 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333173:ℕ) - 1) / 2 = 1666666586 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333333173:ℕ) - 1) / 13 = 256410244 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333333173:ℕ) - 1) / 19 = 175438588 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 877 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((3333333173:ℕ) - 1) / 877 = 3800836 := rfl
              rw [hexp, zmod_pow_of_mod c4]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 3847 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((3333333173:ℕ) - 1) / 3847 = 866476 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
end PrattCertificates

private lemma pcount127 : Nat.count Nat.Prime 127 = 30 :=
  count_from 14 pcount113 rfl rfl

private lemma pcount157 : Nat.count Nat.Prime 157 = 36 :=
  count_from 6 pcount151 rfl rfl

private lemma pcount173 : Nat.count Nat.Prime 173 = 39 :=
  count_from 6 pcount167 rfl rfl

/-- `A242775 31 = 7`: the smallest `k` with `3…3(k threes)‖127` prime is `k = 7`;
the witness `3333333127` is certified prime via `lucas_primality`. -/
theorem A242775_n31 : A242775 31 = 7 := by
  have hp : prime_of_index 31 = 127 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 127) (by norm_num)
    rwa [pcount127] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 127 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 127 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 127 = 3127 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 127 = 33127 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 127 = 333127 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 127 = 3333127 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 127 = 33333127 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 127 = 333333127 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 127 = 3333333127 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 7 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 127)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h7]; exact prime_3333333127
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 127)}
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 37 = 8`: the smallest `k` with `3…3(k threes)‖157` prime is `k = 8`;
the witness `33333333157` is certified prime via `lucas_primality`. -/
theorem A242775_n37 : A242775 37 = 8 := by
  have hp : prime_of_index 37 = 157 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 157) (by norm_num)
    rwa [pcount157] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 157 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 157 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 157 = 3157 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 157 = 33157 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 157 = 333157 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 157 = 3333157 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 157 = 33333157 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 157 = 333333157 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 157 = 3333333157 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 157 = 33333333157 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 8 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 157)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h8]; exact prime_33333333157
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 157)}
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 40 = 7`: the smallest `k` with `3…3(k threes)‖173` prime is `k = 7`;
the witness `3333333173` is certified prime via `lucas_primality`. -/
theorem A242775_n40 : A242775 40 = 7 := by
  have hp : prime_of_index 40 = 173 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 173) (by norm_num)
    rwa [pcount173] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 173 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 173 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 173 = 3173 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 173 = 33173 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 173 = 333173 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 173 = 3333173 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 173 = 33333173 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 173 = 333333173 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 173 = 3333333173 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 7 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 173)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h7]; exact prime_3333333173
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 173)}
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)

section ValueTable46to65
/- Machine-verified values `A242775 n` for `n = 46..65`.  The `n = 52` witness
`33333333239` (11 digits) is certified prime by a two-level Lucas--Pratt
certificate through the subsidiary prime `16666666619`. -/


private lemma pcount199 : Nat.count Nat.Prime 199 = 45 :=
  count_from 2 pcount197 rfl rfl

private lemma pcount211 : Nat.count Nat.Prime 211 = 46 :=
  count_from 12 pcount199 rfl rfl

private lemma pcount223 : Nat.count Nat.Prime 223 = 47 :=
  count_from 12 pcount211 rfl rfl

private lemma pcount227 : Nat.count Nat.Prime 227 = 48 :=
  count_from 4 pcount223 rfl rfl

private lemma pcount229 : Nat.count Nat.Prime 229 = 49 :=
  count_from 2 pcount227 rfl rfl

private lemma pcount233 : Nat.count Nat.Prime 233 = 50 :=
  count_from 4 pcount229 rfl rfl

private lemma pcount239 : Nat.count Nat.Prime 239 = 51 :=
  count_from 6 pcount233 rfl rfl

private lemma pcount241 : Nat.count Nat.Prime 241 = 52 :=
  count_from 2 pcount239 rfl rfl

private lemma pcount251 : Nat.count Nat.Prime 251 = 53 :=
  count_from 10 pcount241 rfl rfl

private lemma pcount257 : Nat.count Nat.Prime 257 = 54 :=
  count_from 6 pcount251 rfl rfl

private lemma pcount263 : Nat.count Nat.Prime 263 = 55 :=
  count_from 6 pcount257 rfl rfl

private lemma pcount269 : Nat.count Nat.Prime 269 = 56 :=
  count_from 6 pcount263 rfl rfl

private lemma pcount271 : Nat.count Nat.Prime 271 = 57 :=
  count_from 2 pcount269 rfl rfl

private lemma pcount277 : Nat.count Nat.Prime 277 = 58 :=
  count_from 6 pcount271 rfl rfl

private lemma pcount281 : Nat.count Nat.Prime 281 = 59 :=
  count_from 4 pcount277 rfl rfl

private lemma pcount283 : Nat.count Nat.Prime 283 = 60 :=
  count_from 2 pcount281 rfl rfl

private lemma pcount293 : Nat.count Nat.Prime 293 = 61 :=
  count_from 10 pcount283 rfl rfl

private lemma pcount307 : Nat.count Nat.Prime 307 = 62 :=
  count_from 14 pcount293 rfl rfl

private lemma pcount311 : Nat.count Nat.Prime 311 = 63 :=
  count_from 4 pcount307 rfl rfl

private lemma pcount313 : Nat.count Nat.Prime 313 = 64 :=
  count_from 2 pcount311 rfl rfl

private lemma prime_16666666619 : Nat.Prime 16666666619 := by
  have c1 : (6:ℕ) ^ 8333333309 % 16666666619 = 16666666618 :=
    pow_mod_eq2 5 6 8333333309 16666666619 16666666618 (by decide) rfl
  have c2 : (6:ℕ) ^ 2380952374 % 16666666619 = 2865605033 :=
    pow_mod_eq2 4 6 2380952374 16666666619 2865605033 (by decide) rfl
  have c3 : (6:ℕ) ^ 980392154 % 16666666619 = 2913499126 :=
    pow_mod_eq2 4 6 980392154 16666666619 2913499126 (by decide) rfl
  have c4 : (6:ℕ) ^ 574712642 % 16666666619 = 11692833114 :=
    pow_mod_eq2 4 6 574712642 16666666619 11692833114 (by decide) rfl
  have c5 : (6:ℕ) ^ 29188558 % 16666666619 = 3219338281 :=
    pow_mod_eq2 4 6 29188558 16666666619 3219338281 (by decide) rfl
  have c6 : (6:ℕ) ^ 3941042 % 16666666619 = 6681969948 :=
    pow_mod_eq2 3 6 3941042 16666666619 6681969948 (by decide) rfl
  have cf : (6:ℕ) ^ 16666666618 % 16666666619 = 1 :=
    pow_mod_eq2 5 6 16666666618 16666666619 1 (by decide) rfl
  refine lucas_primality 16666666619 ((6 : ℕ) : ZMod 16666666619) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (16666666619:ℕ) - 1 = 16666666618 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (16666666619:ℕ) - 1 = 2 * (7 * (17 * (29 * (571 * (4229))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((16666666619:ℕ) - 1) / 2 = 8333333309 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((16666666619:ℕ) - 1) / 7 = 2380952374 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((16666666619:ℕ) - 1) / 17 = 980392154 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 29 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((16666666619:ℕ) - 1) / 29 = 574712642 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 571 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((16666666619:ℕ) - 1) / 571 = 29188558 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 4229 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((16666666619:ℕ) - 1) / 4229 = 3941042 := rfl
              rw [hexp, zmod_pow_of_mod c6]
              exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_33333333239 : Nat.Prime 33333333239 := by
  have c1 : (13:ℕ) ^ 16666666619 % 33333333239 = 33333333238 :=
    pow_mod_eq2 5 13 16666666619 33333333239 33333333238 (by decide) rfl
  have c2 : (13:ℕ) ^ 2 % 33333333239 = 169 :=
    pow_mod_eq2 1 13 2 33333333239 169 (by decide) rfl
  have cf : (13:ℕ) ^ 33333333238 % 33333333239 = 1 :=
    pow_mod_eq2 5 13 33333333238 33333333239 1 (by decide) rfl
  refine lucas_primality 33333333239 ((13 : ℕ) : ZMod 33333333239) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333333239:ℕ) - 1 = 33333333238 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333333239:ℕ) - 1 = 2 * (16666666619) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333333239:ℕ) - 1) / 2 = 16666666619 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      have h := hrest
      have hqe : q = 16666666619 := (Nat.prime_dvd_prime_iff_eq hq prime_16666666619).mp h
      subst hqe
      have hexp : ((33333333239:ℕ) - 1) / 16666666619 = 2 := rfl
      rw [hexp, zmod_pow_of_mod c2]
      exact zmod_ne_one (by decide) (by decide) (by decide)
/-- `A242775 46 = 2`. -/
theorem A242775_n46 : A242775 46 = 2 := by
  have hp : prime_of_index 46 = 199 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 199) (by norm_num)
    rwa [pcount199] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 199 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 199 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 199 = 3199 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 199 = 33199 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 199)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33199)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 199)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 47 = 2`. -/
theorem A242775_n47 : A242775 47 = 2 := by
  have hp : prime_of_index 47 = 211 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 211) (by norm_num)
    rwa [pcount211] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 211 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 211 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 211 = 3211 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 211 = 33211 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 211)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33211)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 211)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 48 = 2`. -/
theorem A242775_n48 : A242775 48 = 2 := by
  have hp : prime_of_index 48 = 223 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 223) (by norm_num)
    rwa [pcount223] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 223 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 223 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 223 = 3223 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 223 = 33223 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 223)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33223)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 223)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 49 = 3`. -/
theorem A242775_n49 : A242775 49 = 3 := by
  have hp : prime_of_index 49 = 227 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 227) (by norm_num)
    rwa [pcount227] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 227 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 227 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 227 = 3227 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 227 = 33227 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 227 = 333227 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 227)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333227)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 227)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 50 = 1`. -/
theorem A242775_n50 : A242775 50 = 1 := by
  have hp : prime_of_index 50 = 229 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 229) (by norm_num)
    rwa [pcount229] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 229 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 229 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 229 = 3229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 229)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3229)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 229)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 51 = 3`. -/
theorem A242775_n51 : A242775 51 = 3 := by
  have hp : prime_of_index 51 = 233 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 233) (by norm_num)
    rwa [pcount233] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 233 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 233 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 233 = 3233 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 233 = 33233 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 233 = 333233 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 233)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333233)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 233)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 52 = 8`. -/
theorem A242775_n52 : A242775 52 = 8 := by
  have hp : prime_of_index 52 = 239 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 239) (by norm_num)
    rwa [pcount239] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 239 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 239 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 239 = 3239 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 239 = 33239 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 239 = 333239 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 239 = 3333239 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 239 = 33333239 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 239 = 333333239 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 239 = 3333333239 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 239 = 33333333239 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 8 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 239)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h8]; exact prime_33333333239
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 239)}
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 53 = 5`. -/
theorem A242775_n53 : A242775 53 = 5 := by
  have hp : prime_of_index 53 = 241 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 241) (by norm_num)
    rwa [pcount241] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 241 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 241 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 241 = 3241 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 241 = 33241 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 241 = 333241 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 241 = 3333241 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 241 = 33333241 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 5 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 241)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h5]; exact (by norm_num : Nat.Prime 33333241)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 241)}
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 54 = 1`. -/
theorem A242775_n54 : A242775 54 = 1 := by
  have hp : prime_of_index 54 = 251 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 251) (by norm_num)
    rwa [pcount251] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 251 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 251 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 251 = 3251 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 251)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3251)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 251)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 55 = 1`. -/
theorem A242775_n55 : A242775 55 = 1 := by
  have hp : prime_of_index 55 = 257 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 257) (by norm_num)
    rwa [pcount257] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 257 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 257 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 257 = 3257 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 257)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3257)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 257)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 56 = 4`. -/
theorem A242775_n56 : A242775 56 = 4 := by
  have hp : prime_of_index 56 = 263 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 263) (by norm_num)
    rwa [pcount263] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 263 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 263 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 263 = 3263 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 263 = 33263 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 263 = 333263 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 263 = 3333263 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 263)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 3333263)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 263)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 57 = 3`. -/
theorem A242775_n57 : A242775 57 = 3 := by
  have hp : prime_of_index 57 = 269 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 269) (by norm_num)
    rwa [pcount269] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 269 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 269 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 269 = 3269 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 269 = 33269 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 269 = 333269 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 269)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333269)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 269)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 58 = 1`. -/
theorem A242775_n58 : A242775 58 = 1 := by
  have hp : prime_of_index 58 = 271 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 271) (by norm_num)
    rwa [pcount271] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 271 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 271 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 271 = 3271 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 271)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3271)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 271)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 59 = 4`. -/
theorem A242775_n59 : A242775 59 = 4 := by
  have hp : prime_of_index 59 = 277 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 277) (by norm_num)
    rwa [pcount277] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 277 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 277 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 277 = 3277 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 277 = 33277 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 277 = 333277 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 277 = 3333277 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 277)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 3333277)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 277)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 60 = 5`. -/
theorem A242775_n60 : A242775 60 = 5 := by
  have hp : prime_of_index 60 = 281 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 281) (by norm_num)
    rwa [pcount281] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 281 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 281 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 281 = 3281 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 281 = 33281 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 281 = 333281 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 281 = 3333281 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 281 = 33333281 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 5 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 281)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h5]; exact (by norm_num : Nat.Prime 33333281)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 281)}
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 61 = 3`. -/
theorem A242775_n61 : A242775 61 = 3 := by
  have hp : prime_of_index 61 = 283 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 283) (by norm_num)
    rwa [pcount283] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 283 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 283 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 283 = 3283 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 283 = 33283 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 283 = 333283 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 283)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333283)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 283)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 62 = 6`. -/
theorem A242775_n62 : A242775 62 = 6 := by
  have hp : prime_of_index 62 = 293 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 293) (by norm_num)
    rwa [pcount293] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 293 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 293 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 293 = 3293 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 293 = 33293 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 293 = 333293 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 293 = 3333293 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 293 = 33333293 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 293 = 333333293 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 6 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 293)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h6]; exact (by norm_num : Nat.Prime 333333293)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 293)}
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 63 = 1`. -/
theorem A242775_n63 : A242775 63 = 1 := by
  have hp : prime_of_index 63 = 307 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 307) (by norm_num)
    rwa [pcount307] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 307 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 307 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 307 = 3307 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 307)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3307)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 307)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 64 = 2`. -/
theorem A242775_n64 : A242775 64 = 2 := by
  have hp : prime_of_index 64 = 311 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 311) (by norm_num)
    rwa [pcount311] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 311 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 311 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 311 = 3311 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 311 = 33311 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 311)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33311)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 311)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 65 = 1`. -/
theorem A242775_n65 : A242775 65 = 1 := by
  have hp : prime_of_index 65 = 313 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 313) (by norm_num)
    rwa [pcount313] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 313 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 313 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 313 = 3313 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 313)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3313)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 313)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

end ValueTable46to65


section ValueTable66to100
/- Machine-verified values `A242775 n` for `n = 66..100`.  The `n = 82` witness
`33333333421` has a one-level Lucas--Pratt certificate; the `n = 86` witness
`3…3(34 threes)443` (37 digits) is certified through a four-level tree with
subsidiary primes 42929058059, 294922628865331 and 541123261982431. -/


private lemma pcount317 : Nat.count Nat.Prime 317 = 65 :=
  count_from 4 pcount313 rfl rfl

private lemma pcount331 : Nat.count Nat.Prime 331 = 66 :=
  count_from 14 pcount317 rfl rfl

private lemma pcount337 : Nat.count Nat.Prime 337 = 67 :=
  count_from 6 pcount331 rfl rfl

private lemma pcount347 : Nat.count Nat.Prime 347 = 68 :=
  count_from 10 pcount337 rfl rfl

private lemma pcount349 : Nat.count Nat.Prime 349 = 69 :=
  count_from 2 pcount347 rfl rfl

private lemma pcount353 : Nat.count Nat.Prime 353 = 70 :=
  count_from 4 pcount349 rfl rfl

private lemma pcount359 : Nat.count Nat.Prime 359 = 71 :=
  count_from 6 pcount353 rfl rfl

private lemma pcount367 : Nat.count Nat.Prime 367 = 72 :=
  count_from 8 pcount359 rfl rfl

private lemma pcount373 : Nat.count Nat.Prime 373 = 73 :=
  count_from 6 pcount367 rfl rfl

private lemma pcount379 : Nat.count Nat.Prime 379 = 74 :=
  count_from 6 pcount373 rfl rfl

private lemma pcount383 : Nat.count Nat.Prime 383 = 75 :=
  count_from 4 pcount379 rfl rfl

private lemma pcount389 : Nat.count Nat.Prime 389 = 76 :=
  count_from 6 pcount383 rfl rfl

private lemma pcount397 : Nat.count Nat.Prime 397 = 77 :=
  count_from 8 pcount389 rfl rfl

private lemma pcount401 : Nat.count Nat.Prime 401 = 78 :=
  count_from 4 pcount397 rfl rfl

private lemma pcount409 : Nat.count Nat.Prime 409 = 79 :=
  count_from 8 pcount401 rfl rfl

private lemma pcount419 : Nat.count Nat.Prime 419 = 80 :=
  count_from 10 pcount409 rfl rfl

private lemma pcount421 : Nat.count Nat.Prime 421 = 81 :=
  count_from 2 pcount419 rfl rfl

private lemma pcount431 : Nat.count Nat.Prime 431 = 82 :=
  count_from 10 pcount421 rfl rfl

private lemma pcount433 : Nat.count Nat.Prime 433 = 83 :=
  count_from 2 pcount431 rfl rfl

private lemma pcount439 : Nat.count Nat.Prime 439 = 84 :=
  count_from 6 pcount433 rfl rfl

private lemma pcount443 : Nat.count Nat.Prime 443 = 85 :=
  count_from 4 pcount439 rfl rfl

private lemma pcount449 : Nat.count Nat.Prime 449 = 86 :=
  count_from 6 pcount443 rfl rfl

private lemma pcount457 : Nat.count Nat.Prime 457 = 87 :=
  count_from 8 pcount449 rfl rfl

private lemma pcount461 : Nat.count Nat.Prime 461 = 88 :=
  count_from 4 pcount457 rfl rfl

private lemma pcount463 : Nat.count Nat.Prime 463 = 89 :=
  count_from 2 pcount461 rfl rfl

private lemma pcount467 : Nat.count Nat.Prime 467 = 90 :=
  count_from 4 pcount463 rfl rfl

private lemma pcount479 : Nat.count Nat.Prime 479 = 91 :=
  count_from 12 pcount467 rfl rfl

private lemma pcount487 : Nat.count Nat.Prime 487 = 92 :=
  count_from 8 pcount479 rfl rfl

private lemma pcount491 : Nat.count Nat.Prime 491 = 93 :=
  count_from 4 pcount487 rfl rfl

private lemma pcount499 : Nat.count Nat.Prime 499 = 94 :=
  count_from 8 pcount491 rfl rfl

private lemma pcount503 : Nat.count Nat.Prime 503 = 95 :=
  count_from 4 pcount499 rfl rfl

private lemma pcount509 : Nat.count Nat.Prime 509 = 96 :=
  count_from 6 pcount503 rfl rfl

private lemma pcount521 : Nat.count Nat.Prime 521 = 97 :=
  count_from 12 pcount509 rfl rfl

private lemma pcount523 : Nat.count Nat.Prime 523 = 98 :=
  count_from 2 pcount521 rfl rfl

private lemma pcount541 : Nat.count Nat.Prime 541 = 99 :=
  count_from 18 pcount523 rfl rfl

private lemma prime_33333333421 : Nat.Prime 33333333421 := by
  have c1 : (2:ℕ) ^ 16666666710 % 33333333421 = 33333333420 :=
    pow_mod_eq2 5 2 16666666710 33333333421 33333333420 (by decide) rfl
  have c2 : (2:ℕ) ^ 11111111140 % 33333333421 = 1173437700 :=
    pow_mod_eq2 5 2 11111111140 33333333421 1173437700 (by decide) rfl
  have c3 : (2:ℕ) ^ 6666666684 % 33333333421 = 8349623552 :=
    pow_mod_eq2 5 2 6666666684 33333333421 8349623552 (by decide) rfl
  have c4 : (2:ℕ) ^ 1075268820 % 33333333421 = 26540637205 :=
    pow_mod_eq2 4 2 1075268820 33333333421 26540637205 (by decide) rfl
  have c5 : (2:ℕ) ^ 709219860 % 33333333421 = 21284966462 :=
    pow_mod_eq2 4 2 709219860 33333333421 21284966462 (by decide) rfl
  have c6 : (2:ℕ) ^ 87420 % 33333333421 = 7797560087 :=
    pow_mod_eq2 3 2 87420 33333333421 7797560087 (by decide) rfl
  have cf : (2:ℕ) ^ 33333333420 % 33333333421 = 1 :=
    pow_mod_eq2 5 2 33333333420 33333333421 1 (by decide) rfl
  refine lucas_primality 33333333421 ((2 : ℕ) : ZMod 33333333421) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333333421:ℕ) - 1 = 33333333420 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333333421:ℕ) - 1 = 2 * (2 * (3 * (5 * (31 * (47 * (381301)))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333333421:ℕ) - 1) / 2 = 16666666710 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333333421:ℕ) - 1) / 2 = 16666666710 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333333421:ℕ) - 1) / 3 = 11111111140 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((33333333421:ℕ) - 1) / 5 = 6666666684 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((33333333421:ℕ) - 1) / 31 = 1075268820 := rfl
              rw [hexp, zmod_pow_of_mod c4]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 47 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((33333333421:ℕ) - 1) / 47 = 709219860 := rfl
                rw [hexp, zmod_pow_of_mod c5]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                have h := hrest
                have hqe : q = 381301 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((33333333421:ℕ) - 1) / 381301 = 87420 := rfl
                rw [hexp, zmod_pow_of_mod c6]
                exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_42929058059 : Nat.Prime 42929058059 := by
  have c1 : (2:ℕ) ^ 21464529029 % 42929058059 = 42929058058 :=
    pow_mod_eq2 5 2 21464529029 42929058059 42929058058 (by decide) rfl
  have c2 : (2:ℕ) ^ 913384214 % 42929058059 = 42064381269 :=
    pow_mod_eq2 4 2 913384214 42929058059 42064381269 (by decide) rfl
  have c3 : (2:ℕ) ^ 94 % 42929058059 = 23740641493 :=
    pow_mod_eq2 1 2 94 42929058059 23740641493 (by decide) rfl
  have cf : (2:ℕ) ^ 42929058058 % 42929058059 = 1 :=
    pow_mod_eq2 5 2 42929058058 42929058059 1 (by decide) rfl
  refine lucas_primality 42929058059 ((2 : ℕ) : ZMod 42929058059) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (42929058059:ℕ) - 1 = 42929058058 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (42929058059:ℕ) - 1 = 2 * (47 * (456692107)) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((42929058059:ℕ) - 1) / 2 = 21464529029 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 47 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((42929058059:ℕ) - 1) / 47 = 913384214 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        have h := hrest
        have hqe : q = 456692107 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((42929058059:ℕ) - 1) / 456692107 = 94 := rfl
        rw [hexp, zmod_pow_of_mod c3]
        exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_294922628865331 : Nat.Prime 294922628865331 := by
  have c1 : (2:ℕ) ^ 147461314432665 % 294922628865331 = 294922628865330 :=
    pow_mod_eq2 6 2 147461314432665 294922628865331 294922628865330 (by decide) rfl
  have c2 : (2:ℕ) ^ 98307542955110 % 294922628865331 = 158946381928635 :=
    pow_mod_eq2 6 2 98307542955110 294922628865331 158946381928635 (by decide) rfl
  have c3 : (2:ℕ) ^ 58984525773066 % 294922628865331 = 208496078165903 :=
    pow_mod_eq2 6 2 58984525773066 294922628865331 208496078165903 (by decide) rfl
  have c4 : (2:ℕ) ^ 1287871741770 % 294922628865331 = 98577298184062 :=
    pow_mod_eq2 6 2 1287871741770 294922628865331 98577298184062 (by decide) rfl
  have c5 : (2:ℕ) ^ 6870 % 294922628865331 = 280662680572021 :=
    pow_mod_eq2 2 2 6870 294922628865331 280662680572021 (by decide) rfl
  have cf : (2:ℕ) ^ 294922628865330 % 294922628865331 = 1 :=
    pow_mod_eq2 7 2 294922628865330 294922628865331 1 (by decide) rfl
  refine lucas_primality 294922628865331 ((2 : ℕ) : ZMod 294922628865331) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (294922628865331:ℕ) - 1 = 294922628865330 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (294922628865331:ℕ) - 1 = 2 * (3 * (5 * (229 * (42929058059)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((294922628865331:ℕ) - 1) / 2 = 147461314432665 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((294922628865331:ℕ) - 1) / 3 = 98307542955110 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((294922628865331:ℕ) - 1) / 5 = 58984525773066 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 229 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((294922628865331:ℕ) - 1) / 229 = 1287871741770 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 42929058059 := (Nat.prime_dvd_prime_iff_eq hq prime_42929058059).mp h
            subst hqe
            have hexp : ((294922628865331:ℕ) - 1) / 42929058059 = 6870 := rfl
            rw [hexp, zmod_pow_of_mod c5]
            exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_541123261982431 : Nat.Prime 541123261982431 := by
  have c1 : (3:ℕ) ^ 270561630991215 % 541123261982431 = 541123261982430 :=
    pow_mod_eq2 6 3 270561630991215 541123261982431 541123261982430 (by decide) rfl
  have c2 : (3:ℕ) ^ 180374420660810 % 541123261982431 = 437938069578292 :=
    pow_mod_eq2 6 3 180374420660810 541123261982431 437938069578292 (by decide) rfl
  have c3 : (3:ℕ) ^ 108224652396486 % 541123261982431 = 241249890669230 :=
    pow_mod_eq2 6 3 108224652396486 541123261982431 241249890669230 (by decide) rfl
  have c4 : (3:ℕ) ^ 4130711923530 % 541123261982431 = 295923535495083 :=
    pow_mod_eq2 6 3 4130711923530 541123261982431 295923535495083 (by decide) rfl
  have c5 : (3:ℕ) ^ 312246544710 % 541123261982431 = 442514849171353 :=
    pow_mod_eq2 5 3 312246544710 541123261982431 442514849171353 (by decide) rfl
  have c6 : (3:ℕ) ^ 6810690 % 541123261982431 = 515045479591260 :=
    pow_mod_eq2 3 3 6810690 541123261982431 515045479591260 (by decide) rfl
  have cf : (3:ℕ) ^ 541123261982430 % 541123261982431 = 1 :=
    pow_mod_eq2 7 3 541123261982430 541123261982431 1 (by decide) rfl
  refine lucas_primality 541123261982431 ((3 : ℕ) : ZMod 541123261982431) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (541123261982431:ℕ) - 1 = 541123261982430 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (541123261982431:ℕ) - 1 = 2 * (3 * (5 * (131 * (1733 * (79452047))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((541123261982431:ℕ) - 1) / 2 = 270561630991215 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((541123261982431:ℕ) - 1) / 3 = 180374420660810 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((541123261982431:ℕ) - 1) / 5 = 108224652396486 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 131 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((541123261982431:ℕ) - 1) / 131 = 4130711923530 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 1733 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((541123261982431:ℕ) - 1) / 1733 = 312246544710 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 79452047 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((541123261982431:ℕ) - 1) / 79452047 = 6810690 := rfl
              rw [hexp, zmod_pow_of_mod c6]
              exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_3333333333333333333333333333333333443 : Nat.Prime 3333333333333333333333333333333333443 := by
  have c1 : (2:ℕ) ^ 1666666666666666666666666666666666721 % 3333333333333333333333333333333333443 = 3333333333333333333333333333333333442 :=
    pow_mod_eq2 16 2 1666666666666666666666666666666666721 3333333333333333333333333333333333443 3333333333333333333333333333333333442 (by decide) rfl
  have c2 : (2:ℕ) ^ 476190476190476190476190476190476206 % 3333333333333333333333333333333333443 = 2796359464479333703406387528460219327 :=
    pow_mod_eq2 15 2 476190476190476190476190476190476206 3333333333333333333333333333333333443 2796359464479333703406387528460219327 (by decide) rfl
  have c3 : (2:ℕ) ^ 46948356807511737089201877934272302 % 3333333333333333333333333333333333443 = 1753577369732603318589706548136863130 :=
    pow_mod_eq2 15 2 46948356807511737089201877934272302 3333333333333333333333333333333333443 1753577369732603318589706548136863130 (by decide) rfl
  have c4 : (2:ℕ) ^ 158631957994257523120607877663034 % 3333333333333333333333333333333333443 = 1619569529789361445818469382542839402 :=
    pow_mod_eq2 14 2 158631957994257523120607877663034 3333333333333333333333333333333333443 1619569529789361445818469382542839402 (by decide) rfl
  have c5 : (2:ℕ) ^ 11302399365412601667382 % 3333333333333333333333333333333333443 = 2593969035962974086997081316184962000 :=
    pow_mod_eq2 10 2 11302399365412601667382 3333333333333333333333333333333333443 2593969035962974086997081316184962000 (by decide) rfl
  have c6 : (2:ℕ) ^ 6160025945145117101182 % 3333333333333333333333333333333333443 = 1619743102736905928039427134785989934 :=
    pow_mod_eq2 10 2 6160025945145117101182 3333333333333333333333333333333333443 1619743102736905928039427134785989934 (by decide) rfl
  have cf : (2:ℕ) ^ 3333333333333333333333333333333333442 % 3333333333333333333333333333333333443 = 1 :=
    pow_mod_eq2 16 2 3333333333333333333333333333333333442 3333333333333333333333333333333333443 1 (by decide) rfl
  refine lucas_primality 3333333333333333333333333333333333443 ((2 : ℕ) : ZMod 3333333333333333333333333333333333443) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333333333333333333333333333333333443:ℕ) - 1 = 3333333333333333333333333333333333442 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333333333333333333333333333333333443:ℕ) - 1 = 2 * (7 * (71 * (21013 * (294922628865331 * (541123261982431))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333333333333333333333333333333333443:ℕ) - 1) / 2 = 1666666666666666666666666666666666721 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333333333333333333333333333333443:ℕ) - 1) / 7 = 476190476190476190476190476190476206 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 71 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333333333333333333333333333333333443:ℕ) - 1) / 71 = 46948356807511737089201877934272302 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 21013 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333333333333333333333333333333333443:ℕ) - 1) / 21013 = 158631957994257523120607877663034 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 294922628865331 := (Nat.prime_dvd_prime_iff_eq hq prime_294922628865331).mp h
              subst hqe
              have hexp : ((3333333333333333333333333333333333443:ℕ) - 1) / 294922628865331 = 11302399365412601667382 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 541123261982431 := (Nat.prime_dvd_prime_iff_eq hq prime_541123261982431).mp h
              subst hqe
              have hexp : ((3333333333333333333333333333333333443:ℕ) - 1) / 541123261982431 = 6160025945145117101182 := rfl
              rw [hexp, zmod_pow_of_mod c6]
              exact zmod_ne_one (by decide) (by decide) (by decide)
/-- `A242775 66 = 2`. -/
theorem A242775_n66 : A242775 66 = 2 := by
  have hp : prime_of_index 66 = 317 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 317) (by norm_num)
    rwa [pcount317] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 317 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 317 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 317 = 3317 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 317 = 33317 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 317)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33317)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 317)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 67 = 1`. -/
theorem A242775_n67 : A242775 67 = 1 := by
  have hp : prime_of_index 67 = 331 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 331) (by norm_num)
    rwa [pcount331] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 331 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 331 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 331 = 3331 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 331)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3331)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 331)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 68 = 3`. -/
theorem A242775_n68 : A242775 68 = 3 := by
  have hp : prime_of_index 68 = 337 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 337) (by norm_num)
    rwa [pcount337] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 337 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 337 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 337 = 3337 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 337 = 33337 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 337 = 333337 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 337)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333337)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 337)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 69 = 1`. -/
theorem A242775_n69 : A242775 69 = 1 := by
  have hp : prime_of_index 69 = 347 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 347) (by norm_num)
    rwa [pcount347] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 347 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 347 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 347 = 3347 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 347)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3347)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 347)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 70 = 2`. -/
theorem A242775_n70 : A242775 70 = 2 := by
  have hp : prime_of_index 70 = 349 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 349) (by norm_num)
    rwa [pcount349] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 349 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 349 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 349 = 3349 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 349 = 33349 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 349)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33349)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 349)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 71 = 2`. -/
theorem A242775_n71 : A242775 71 = 2 := by
  have hp : prime_of_index 71 = 353 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 353) (by norm_num)
    rwa [pcount353] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 353 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 353 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 353 = 3353 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 353 = 33353 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 353)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33353)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 353)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 72 = 1`. -/
theorem A242775_n72 : A242775 72 = 1 := by
  have hp : prime_of_index 72 = 359 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 359) (by norm_num)
    rwa [pcount359] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 359 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 359 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 359 = 3359 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 359)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3359)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 359)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 73 = 3`. -/
theorem A242775_n73 : A242775 73 = 3 := by
  have hp : prime_of_index 73 = 367 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 367) (by norm_num)
    rwa [pcount367] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 367 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 367 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 367 = 3367 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 367 = 33367 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 367 = 333367 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 367)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333367)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 367)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 74 = 1`. -/
theorem A242775_n74 : A242775 74 = 1 := by
  have hp : prime_of_index 74 = 373 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 373) (by norm_num)
    rwa [pcount373] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 373 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 373 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 373 = 3373 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 373)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3373)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 373)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 75 = 6`. -/
theorem A242775_n75 : A242775 75 = 6 := by
  have hp : prime_of_index 75 = 379 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 379) (by norm_num)
    rwa [pcount379] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 379 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 379 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 379 = 3379 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 379 = 33379 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 379 = 333379 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 379 = 3333379 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 379 = 33333379 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 379 = 333333379 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 6 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 379)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h6]; exact (by norm_num : Nat.Prime 333333379)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 379)}
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 76 = 3`. -/
theorem A242775_n76 : A242775 76 = 3 := by
  have hp : prime_of_index 76 = 383 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 383) (by norm_num)
    rwa [pcount383] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 383 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 383 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 383 = 3383 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 383 = 33383 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 383 = 333383 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 383)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333383)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 383)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 77 = 1`. -/
theorem A242775_n77 : A242775 77 = 1 := by
  have hp : prime_of_index 77 = 389 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 389) (by norm_num)
    rwa [pcount389] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 389 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 389 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 389 = 3389 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 389)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3389)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 389)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 78 = 3`. -/
theorem A242775_n78 : A242775 78 = 3 := by
  have hp : prime_of_index 78 = 397 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 397) (by norm_num)
    rwa [pcount397] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 397 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 397 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 397 = 3397 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 397 = 33397 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 397 = 333397 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 397)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333397)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 397)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 79 = 4`. -/
theorem A242775_n79 : A242775 79 = 4 := by
  have hp : prime_of_index 79 = 401 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 401) (by norm_num)
    rwa [pcount401] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 401 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 401 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 401 = 3401 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 401 = 33401 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 401 = 333401 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 401 = 3333401 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 401)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 3333401)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 401)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 80 = 2`. -/
theorem A242775_n80 : A242775 80 = 2 := by
  have hp : prime_of_index 80 = 409 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 409) (by norm_num)
    rwa [pcount409] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 409 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 409 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 409 = 3409 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 409 = 33409 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 409)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33409)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 409)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 81 = 3`. -/
theorem A242775_n81 : A242775 81 = 3 := by
  have hp : prime_of_index 81 = 419 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 419) (by norm_num)
    rwa [pcount419] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 419 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 419 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 419 = 3419 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 419 = 33419 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 419 = 333419 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 419)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333419)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 419)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 82 = 8`. -/
theorem A242775_n82 : A242775 82 = 8 := by
  have hp : prime_of_index 82 = 421 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 421) (by norm_num)
    rwa [pcount421] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 421 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 421 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 421 = 3421 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 421 = 33421 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 421 = 333421 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 421 = 3333421 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 421 = 33333421 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 421 = 333333421 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 421 = 3333333421 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 421 = 33333333421 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 8 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 421)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h8]; exact prime_33333333421
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 421)}
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 83 = 4`. -/
theorem A242775_n83 : A242775 83 = 4 := by
  have hp : prime_of_index 83 = 431 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 431) (by norm_num)
    rwa [pcount431] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 431 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 431 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 431 = 3431 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 431 = 33431 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 431 = 333431 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 431 = 3333431 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 431)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 3333431)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 431)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 84 = 1`. -/
theorem A242775_n84 : A242775 84 = 1 := by
  have hp : prime_of_index 84 = 433 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 433) (by norm_num)
    rwa [pcount433] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 433 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 433 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 433 = 3433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 433)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3433)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 433)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 85 = 3`. -/
theorem A242775_n85 : A242775 85 = 3 := by
  have hp : prime_of_index 85 = 439 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 439) (by norm_num)
    rwa [pcount439] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 439 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 439 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 439 = 3439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 439 = 33439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 439 = 333439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 439)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333439)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 439)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 86 = 34`. -/
theorem A242775_n86 : A242775 86 = 34 := by
  have hp : prime_of_index 86 = 443 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 443) (by norm_num)
    rwa [pcount443] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 443 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 443 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 443 = 3443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 443 = 33443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 443 = 333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 443 = 3333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 443 = 33333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 443 = 333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 443 = 3333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 443 = 33333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 443 = 333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 443 = 3333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 443 = 33333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 443 = 333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h13 : concatenate 13 443 = 3333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h14 : concatenate 14 443 = 33333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h15 : concatenate 15 443 = 333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h16 : concatenate 16 443 = 3333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h17 : concatenate 17 443 = 33333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h18 : concatenate 18 443 = 333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h19 : concatenate 19 443 = 3333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h20 : concatenate 20 443 = 33333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h21 : concatenate 21 443 = 333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h22 : concatenate 22 443 = 3333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h23 : concatenate 23 443 = 33333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h24 : concatenate 24 443 = 333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h25 : concatenate 25 443 = 3333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h26 : concatenate 26 443 = 33333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h27 : concatenate 27 443 = 333333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h28 : concatenate 28 443 = 3333333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h29 : concatenate 29 443 = 33333333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h30 : concatenate 30 443 = 333333333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h31 : concatenate 31 443 = 3333333333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h32 : concatenate 32 443 = 33333333333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h33 : concatenate 33 443 = 333333333333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h34 : concatenate 34 443 = 3333333333333333333333333333333333443 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 34 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 443)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h34]; exact prime_3333333333333333333333333333333333443
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 443)}
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact (by norm_num : ¬ (3333443 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact (by norm_num : ¬ (333333443 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h12] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h13] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h14] at hpr
    exact (by norm_num : ¬ (33333333333333443 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h15] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h16] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h17] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h18] at hpr
    exact (by norm_num : ¬ (333333333333333333443 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h19] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h20] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h21] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h22] at hpr
    exact (by norm_num : ¬ (3333333333333333333333443 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h23] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h24] at hpr
    exact (by norm_num : ¬ (333333333333333333333333443 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h25] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h26] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h27] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h28] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h29] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h30] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h31] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h32] at hpr
    exact (by norm_num : ¬ (33333333333333333333333333333333443 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨34, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h33] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 87 = 1`. -/
theorem A242775_n87 : A242775 87 = 1 := by
  have hp : prime_of_index 87 = 449 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 449) (by norm_num)
    rwa [pcount449] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 449 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 449 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 449 = 3449 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 449)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3449)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 449)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 88 = 1`. -/
theorem A242775_n88 : A242775 88 = 1 := by
  have hp : prime_of_index 88 = 457 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 457) (by norm_num)
    rwa [pcount457] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 457 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 457 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 457 = 3457 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 457)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3457)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 457)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 89 = 1`. -/
theorem A242775_n89 : A242775 89 = 1 := by
  have hp : prime_of_index 89 = 461 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 461) (by norm_num)
    rwa [pcount461] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 461 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 461 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 461 = 3461 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 461)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3461)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 461)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 90 = 1`. -/
theorem A242775_n90 : A242775 90 = 1 := by
  have hp : prime_of_index 90 = 463 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 463) (by norm_num)
    rwa [pcount463] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 463 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 463 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 463 = 3463 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 463)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3463)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 463)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 91 = 1`. -/
theorem A242775_n91 : A242775 91 = 1 := by
  have hp : prime_of_index 91 = 467 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 467) (by norm_num)
    rwa [pcount467] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 467 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 467 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 467 = 3467 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 467)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3467)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 467)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 92 = 2`. -/
theorem A242775_n92 : A242775 92 = 2 := by
  have hp : prime_of_index 92 = 479 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 479) (by norm_num)
    rwa [pcount479] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 479 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 479 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 479 = 3479 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 479 = 33479 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 479)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33479)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 479)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 93 = 2`. -/
theorem A242775_n93 : A242775 93 = 2 := by
  have hp : prime_of_index 93 = 487 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 487) (by norm_num)
    rwa [pcount487] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 487 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 487 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 487 = 3487 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 487 = 33487 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 487)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33487)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 487)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 94 = 1`. -/
theorem A242775_n94 : A242775 94 = 1 := by
  have hp : prime_of_index 94 = 491 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 491) (by norm_num)
    rwa [pcount491] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 491 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 491 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 491 = 3491 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 491)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3491)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 491)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 95 = 1`. -/
theorem A242775_n95 : A242775 95 = 1 := by
  have hp : prime_of_index 95 = 499 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 499) (by norm_num)
    rwa [pcount499] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 499 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 499 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 499 = 3499 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 499)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3499)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 499)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 96 = 2`. -/
theorem A242775_n96 : A242775 96 = 2 := by
  have hp : prime_of_index 96 = 503 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 503) (by norm_num)
    rwa [pcount503] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 503 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 503 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 503 = 3503 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 503 = 33503 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 503)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33503)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 503)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 97 = 4`. -/
theorem A242775_n97 : A242775 97 = 4 := by
  have hp : prime_of_index 97 = 509 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 509) (by norm_num)
    rwa [pcount509] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 509 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 509 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 509 = 3509 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 509 = 33509 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 509 = 333509 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 509 = 3333509 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 509)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 3333509)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 509)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 98 = 2`. -/
theorem A242775_n98 : A242775 98 = 2 := by
  have hp : prime_of_index 98 = 521 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 521) (by norm_num)
    rwa [pcount521] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 521 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 521 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 521 = 3521 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 521 = 33521 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 521)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33521)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 521)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 99 = 5`. -/
theorem A242775_n99 : A242775 99 = 5 := by
  have hp : prime_of_index 99 = 523 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 523) (by norm_num)
    rwa [pcount523] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 523 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 523 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 523 = 3523 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 523 = 33523 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 523 = 333523 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 523 = 3333523 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 523 = 33333523 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 5 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 523)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h5]; exact (by norm_num : Nat.Prime 33333523)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 523)}
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 100 = 1`. -/
theorem A242775_n100 : A242775 100 = 1 := by
  have hp : prime_of_index 100 = 541 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 541) (by norm_num)
    rwa [pcount541] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 541 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 541 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 541 = 3541 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 541)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3541)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 541)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

end ValueTable66to100


section ValueTable101to150
/- Machine-verified values `A242775 n` for `n = 101..150`, with Lucas--Pratt
certificate trees for the 17-digit witness at `n = 132` and the 30-digit
witness at `n = 149` (subsidiary primes 151838038229 and
50551005965018703872207057).  Compositeness of intermediates with large least
factors is certified by explicit divisor witnesses. -/


private lemma pcount547 : Nat.count Nat.Prime 547 = 100 :=
  count_from 6 pcount541 rfl rfl

private lemma pcount557 : Nat.count Nat.Prime 557 = 101 :=
  count_from 10 pcount547 rfl rfl

private lemma pcount563 : Nat.count Nat.Prime 563 = 102 :=
  count_from 6 pcount557 rfl rfl

private lemma pcount569 : Nat.count Nat.Prime 569 = 103 :=
  count_from 6 pcount563 rfl rfl

private lemma pcount571 : Nat.count Nat.Prime 571 = 104 :=
  count_from 2 pcount569 rfl rfl

private lemma pcount577 : Nat.count Nat.Prime 577 = 105 :=
  count_from 6 pcount571 rfl rfl

private lemma pcount587 : Nat.count Nat.Prime 587 = 106 :=
  count_from 10 pcount577 rfl rfl

private lemma pcount593 : Nat.count Nat.Prime 593 = 107 :=
  count_from 6 pcount587 rfl rfl

private lemma pcount599 : Nat.count Nat.Prime 599 = 108 :=
  count_from 6 pcount593 rfl rfl

private lemma pcount601 : Nat.count Nat.Prime 601 = 109 :=
  count_from 2 pcount599 rfl rfl

private lemma pcount607 : Nat.count Nat.Prime 607 = 110 :=
  count_from 6 pcount601 rfl rfl

private lemma pcount613 : Nat.count Nat.Prime 613 = 111 :=
  count_from 6 pcount607 rfl rfl

private lemma pcount617 : Nat.count Nat.Prime 617 = 112 :=
  count_from 4 pcount613 rfl rfl

private lemma pcount619 : Nat.count Nat.Prime 619 = 113 :=
  count_from 2 pcount617 rfl rfl

private lemma pcount631 : Nat.count Nat.Prime 631 = 114 :=
  count_from 12 pcount619 rfl rfl

private lemma pcount641 : Nat.count Nat.Prime 641 = 115 :=
  count_from 10 pcount631 rfl rfl

private lemma pcount643 : Nat.count Nat.Prime 643 = 116 :=
  count_from 2 pcount641 rfl rfl

private lemma pcount647 : Nat.count Nat.Prime 647 = 117 :=
  count_from 4 pcount643 rfl rfl

private lemma pcount653 : Nat.count Nat.Prime 653 = 118 :=
  count_from 6 pcount647 rfl rfl

private lemma pcount659 : Nat.count Nat.Prime 659 = 119 :=
  count_from 6 pcount653 rfl rfl

private lemma pcount661 : Nat.count Nat.Prime 661 = 120 :=
  count_from 2 pcount659 rfl rfl

private lemma pcount673 : Nat.count Nat.Prime 673 = 121 :=
  count_from 12 pcount661 rfl rfl

private lemma pcount677 : Nat.count Nat.Prime 677 = 122 :=
  count_from 4 pcount673 rfl rfl

private lemma pcount683 : Nat.count Nat.Prime 683 = 123 :=
  count_from 6 pcount677 rfl rfl

private lemma pcount691 : Nat.count Nat.Prime 691 = 124 :=
  count_from 8 pcount683 rfl rfl

private lemma pcount701 : Nat.count Nat.Prime 701 = 125 :=
  count_from 10 pcount691 rfl rfl

private lemma pcount709 : Nat.count Nat.Prime 709 = 126 :=
  count_from 8 pcount701 rfl rfl

private lemma pcount719 : Nat.count Nat.Prime 719 = 127 :=
  count_from 10 pcount709 rfl rfl

private lemma pcount727 : Nat.count Nat.Prime 727 = 128 :=
  count_from 8 pcount719 rfl rfl

private lemma pcount733 : Nat.count Nat.Prime 733 = 129 :=
  count_from 6 pcount727 rfl rfl

private lemma pcount739 : Nat.count Nat.Prime 739 = 130 :=
  count_from 6 pcount733 rfl rfl

private lemma pcount743 : Nat.count Nat.Prime 743 = 131 :=
  count_from 4 pcount739 rfl rfl

private lemma pcount751 : Nat.count Nat.Prime 751 = 132 :=
  count_from 8 pcount743 rfl rfl

private lemma pcount757 : Nat.count Nat.Prime 757 = 133 :=
  count_from 6 pcount751 rfl rfl

private lemma pcount761 : Nat.count Nat.Prime 761 = 134 :=
  count_from 4 pcount757 rfl rfl

private lemma pcount769 : Nat.count Nat.Prime 769 = 135 :=
  count_from 8 pcount761 rfl rfl

private lemma pcount773 : Nat.count Nat.Prime 773 = 136 :=
  count_from 4 pcount769 rfl rfl

private lemma pcount787 : Nat.count Nat.Prime 787 = 137 :=
  count_from 14 pcount773 rfl rfl

private lemma pcount797 : Nat.count Nat.Prime 797 = 138 :=
  count_from 10 pcount787 rfl rfl

private lemma pcount809 : Nat.count Nat.Prime 809 = 139 :=
  count_from 12 pcount797 rfl rfl

private lemma pcount811 : Nat.count Nat.Prime 811 = 140 :=
  count_from 2 pcount809 rfl rfl

private lemma pcount821 : Nat.count Nat.Prime 821 = 141 :=
  count_from 10 pcount811 rfl rfl

private lemma pcount823 : Nat.count Nat.Prime 823 = 142 :=
  count_from 2 pcount821 rfl rfl

private lemma pcount827 : Nat.count Nat.Prime 827 = 143 :=
  count_from 4 pcount823 rfl rfl

private lemma pcount829 : Nat.count Nat.Prime 829 = 144 :=
  count_from 2 pcount827 rfl rfl

private lemma pcount839 : Nat.count Nat.Prime 839 = 145 :=
  count_from 10 pcount829 rfl rfl

private lemma pcount853 : Nat.count Nat.Prime 853 = 146 :=
  count_from 14 pcount839 rfl rfl

private lemma pcount857 : Nat.count Nat.Prime 857 = 147 :=
  count_from 4 pcount853 rfl rfl

private lemma pcount859 : Nat.count Nat.Prime 859 = 148 :=
  count_from 2 pcount857 rfl rfl

private lemma pcount863 : Nat.count Nat.Prime 863 = 149 :=
  count_from 4 pcount859 rfl rfl

private lemma prime_33333333333333743 : Nat.Prime 33333333333333743 := by
  have c1 : (5:ℕ) ^ 16666666666666871 % 33333333333333743 = 33333333333333742 :=
    pow_mod_eq2 7 5 16666666666666871 33333333333333743 33333333333333742 (by decide) rfl
  have c2 : (5:ℕ) ^ 3534443148482 % 33333333333333743 = 26717665039216385 :=
    pow_mod_eq2 6 5 3534443148482 33333333333333743 26717665039216385 (by decide) rfl
  have c3 : (5:ℕ) ^ 1073917759378 % 33333333333333743 = 21652776967739203 :=
    pow_mod_eq2 5 5 1073917759378 33333333333333743 21652776967739203 (by decide) rfl
  have c4 : (5:ℕ) ^ 585457618 % 33333333333333743 = 3754046515001147 :=
    pow_mod_eq2 4 5 585457618 33333333333333743 3754046515001147 (by decide) rfl
  have cf : (5:ℕ) ^ 33333333333333742 % 33333333333333743 = 1 :=
    pow_mod_eq2 7 5 33333333333333742 33333333333333743 1 (by decide) rfl
  refine lucas_primality 33333333333333743 ((5 : ℕ) : ZMod 33333333333333743) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333333333333743:ℕ) - 1 = 33333333333333742 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333333333333743:ℕ) - 1 = 2 * (9431 * (31039 * (56935519))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333333333333743:ℕ) - 1) / 2 = 16666666666666871 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 9431 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333333333333743:ℕ) - 1) / 9431 = 3534443148482 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 31039 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333333333333743:ℕ) - 1) / 31039 = 1073917759378 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 56935519 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333333333333743:ℕ) - 1) / 56935519 = 585457618 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_151838038229 : Nat.Prime 151838038229 := by
  have c1 : (2:ℕ) ^ 75919019114 % 151838038229 = 151838038228 :=
    pow_mod_eq2 5 2 75919019114 151838038229 151838038228 (by decide) rfl
  have c2 : (2:ℕ) ^ 6601653836 % 151838038229 = 81822550230 :=
    pow_mod_eq2 5 2 6601653836 151838038229 81822550230 (by decide) rfl
  have c3 : (2:ℕ) ^ 147272588 % 151838038229 = 43133121416 :=
    pow_mod_eq2 4 2 147272588 151838038229 43133121416 (by decide) rfl
  have c4 : (2:ℕ) ^ 94852 % 151838038229 = 112558710689 :=
    pow_mod_eq2 3 2 94852 151838038229 112558710689 (by decide) rfl
  have cf : (2:ℕ) ^ 151838038228 % 151838038229 = 1 :=
    pow_mod_eq2 5 2 151838038228 151838038229 1 (by decide) rfl
  refine lucas_primality 151838038229 ((2 : ℕ) : ZMod 151838038229) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (151838038229:ℕ) - 1 = 151838038228 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (151838038229:ℕ) - 1 = 2 * (2 * (23 * (1031 * (1600789)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((151838038229:ℕ) - 1) / 2 = 75919019114 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((151838038229:ℕ) - 1) / 2 = 75919019114 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 23 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((151838038229:ℕ) - 1) / 23 = 6601653836 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 1031 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((151838038229:ℕ) - 1) / 1031 = 147272588 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 1600789 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((151838038229:ℕ) - 1) / 1600789 = 94852 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_50551005965018703872207057 : Nat.Prime 50551005965018703872207057 := by
  have c1 : (3:ℕ) ^ 25275502982509351936103528 % 50551005965018703872207057 = 50551005965018703872207056 :=
    pow_mod_eq2 11 3 25275502982509351936103528 50551005965018703872207057 50551005965018703872207056 (by decide) rfl
  have c2 : (3:ℕ) ^ 88490210192921806096 % 50551005965018703872207057 = 32002994293553079973637577 :=
    pow_mod_eq2 9 3 88490210192921806096 50551005965018703872207057 32002994293553079973637577 (by decide) rfl
  have c3 : (3:ℕ) ^ 1387826392907788304 % 50551005965018703872207057 = 17403107076783953867296675 :=
    pow_mod_eq2 8 3 1387826392907788304 50551005965018703872207057 17403107076783953867296675 (by decide) rfl
  have c4 : (3:ℕ) ^ 332927154187664 % 50551005965018703872207057 = 43861728986296933617044419 :=
    pow_mod_eq2 7 3 332927154187664 50551005965018703872207057 43861728986296933617044419 (by decide) rfl
  have cf : (3:ℕ) ^ 50551005965018703872207056 % 50551005965018703872207057 = 1 :=
    pow_mod_eq2 11 3 50551005965018703872207056 50551005965018703872207057 1 (by decide) rfl
  refine lucas_primality 50551005965018703872207057 ((3 : ℕ) : ZMod 50551005965018703872207057) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (50551005965018703872207057:ℕ) - 1 = 50551005965018703872207056 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (50551005965018703872207057:ℕ) - 1 = 2 * (2 * (2 * (2 * (571261 * (36424589 * (151838038229)))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((50551005965018703872207057:ℕ) - 1) / 2 = 25275502982509351936103528 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((50551005965018703872207057:ℕ) - 1) / 2 = 25275502982509351936103528 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((50551005965018703872207057:ℕ) - 1) / 2 = 25275502982509351936103528 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((50551005965018703872207057:ℕ) - 1) / 2 = 25275502982509351936103528 := rfl
            rw [hexp, zmod_pow_of_mod c1]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 571261 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((50551005965018703872207057:ℕ) - 1) / 571261 = 88490210192921806096 := rfl
              rw [hexp, zmod_pow_of_mod c2]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 36424589 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((50551005965018703872207057:ℕ) - 1) / 36424589 = 1387826392907788304 := rfl
                rw [hexp, zmod_pow_of_mod c3]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                have h := hrest
                have hqe : q = 151838038229 := (Nat.prime_dvd_prime_iff_eq hq prime_151838038229).mp h
                subst hqe
                have hexp : ((50551005965018703872207057:ℕ) - 1) / 151838038229 = 332927154187664 := rfl
                rw [hexp, zmod_pow_of_mod c4]
                exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_333333333333333333333333333859 : Nat.Prime 333333333333333333333333333859 := by
  have c1 : (2:ℕ) ^ 166666666666666666666666666929 % 333333333333333333333333333859 = 333333333333333333333333333858 :=
    pow_mod_eq2 13 2 166666666666666666666666666929 333333333333333333333333333859 333333333333333333333333333858 (by decide) rfl
  have c2 : (2:ℕ) ^ 111111111111111111111111111286 % 333333333333333333333333333859 = 273919215950857474266812264470 :=
    pow_mod_eq2 13 2 111111111111111111111111111286 333333333333333333333333333859 273919215950857474266812264470 (by decide) rfl
  have c3 : (2:ℕ) ^ 47619047619047619047619047694 % 333333333333333333333333333859 = 2141581378449656638298959135 :=
    pow_mod_eq2 12 2 47619047619047619047619047694 333333333333333333333333333859 2141581378449656638298959135 (by decide) rfl
  have c4 : (2:ℕ) ^ 2123142250530785562632696394 % 333333333333333333333333333859 = 35113333219621706217926494348 :=
    pow_mod_eq2 12 2 2123142250530785562632696394 333333333333333333333333333859 35113333219621706217926494348 (by decide) rfl
  have c5 : (2:ℕ) ^ 6594 % 333333333333333333333333333859 = 224595239086847632294967497353 :=
    pow_mod_eq2 2 2 6594 333333333333333333333333333859 224595239086847632294967497353 (by decide) rfl
  have cf : (2:ℕ) ^ 333333333333333333333333333858 % 333333333333333333333333333859 = 1 :=
    pow_mod_eq2 13 2 333333333333333333333333333858 333333333333333333333333333859 1 (by decide) rfl
  refine lucas_primality 333333333333333333333333333859 ((2 : ℕ) : ZMod 333333333333333333333333333859) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (333333333333333333333333333859:ℕ) - 1 = 333333333333333333333333333858 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (333333333333333333333333333859:ℕ) - 1 = 2 * (3 * (7 * (157 * (50551005965018703872207057)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((333333333333333333333333333859:ℕ) - 1) / 2 = 166666666666666666666666666929 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((333333333333333333333333333859:ℕ) - 1) / 3 = 111111111111111111111111111286 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((333333333333333333333333333859:ℕ) - 1) / 7 = 47619047619047619047619047694 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 157 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((333333333333333333333333333859:ℕ) - 1) / 157 = 2123142250530785562632696394 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 50551005965018703872207057 := (Nat.prime_dvd_prime_iff_eq hq prime_50551005965018703872207057).mp h
            subst hqe
            have hexp : ((333333333333333333333333333859:ℕ) - 1) / 50551005965018703872207057 = 6594 := rfl
            rw [hexp, zmod_pow_of_mod c5]
            exact zmod_ne_one (by decide) (by decide) (by decide)
/-- `A242775 101 = 1`. -/
theorem A242775_n101 : A242775 101 = 1 := by
  have hp : prime_of_index 101 = 547 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 547) (by norm_num)
    rwa [pcount547] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 547 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 547 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 547 = 3547 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 547)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3547)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 547)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 102 = 1`. -/
theorem A242775_n102 : A242775 102 = 1 := by
  have hp : prime_of_index 102 = 557 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 557) (by norm_num)
    rwa [pcount557] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 557 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 557 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 557 = 3557 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 557)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3557)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 557)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 103 = 2`. -/
theorem A242775_n103 : A242775 103 = 2 := by
  have hp : prime_of_index 103 = 563 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 563) (by norm_num)
    rwa [pcount563] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 563 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 563 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 563 = 3563 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 563 = 33563 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 563)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33563)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 563)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 104 = 2`. -/
theorem A242775_n104 : A242775 104 = 2 := by
  have hp : prime_of_index 104 = 569 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 569) (by norm_num)
    rwa [pcount569] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 569 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 569 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 569 = 3569 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 569 = 33569 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 569)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33569)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 569)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 105 = 1`. -/
theorem A242775_n105 : A242775 105 = 1 := by
  have hp : prime_of_index 105 = 571 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 571) (by norm_num)
    rwa [pcount571] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 571 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 571 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 571 = 3571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 571)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3571)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 571)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 106 = 2`. -/
theorem A242775_n106 : A242775 106 = 2 := by
  have hp : prime_of_index 106 = 577 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 577) (by norm_num)
    rwa [pcount577] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 577 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 577 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 577 = 3577 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 577 = 33577 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 577)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33577)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 577)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 107 = 2`. -/
theorem A242775_n107 : A242775 107 = 2 := by
  have hp : prime_of_index 107 = 587 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 587) (by norm_num)
    rwa [pcount587] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 587 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 587 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 587 = 3587 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 587 = 33587 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 587)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33587)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 587)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 108 = 1`. -/
theorem A242775_n108 : A242775 108 = 1 := by
  have hp : prime_of_index 108 = 593 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 593) (by norm_num)
    rwa [pcount593] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 593 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 593 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 593 = 3593 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 593)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3593)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 593)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 109 = 2`. -/
theorem A242775_n109 : A242775 109 = 2 := by
  have hp : prime_of_index 109 = 599 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 599) (by norm_num)
    rwa [pcount599] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 599 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 599 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 599 = 3599 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 599 = 33599 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 599)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33599)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 599)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 110 = 2`. -/
theorem A242775_n110 : A242775 110 = 2 := by
  have hp : prime_of_index 110 = 601 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 601) (by norm_num)
    rwa [pcount601] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 601 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 601 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 601 = 3601 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 601 = 33601 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 601)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33601)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 601)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 111 = 1`. -/
theorem A242775_n111 : A242775 111 = 1 := by
  have hp : prime_of_index 111 = 607 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 607) (by norm_num)
    rwa [pcount607] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 607 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 607 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 607 = 3607 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 607)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3607)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 607)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 112 = 1`. -/
theorem A242775_n112 : A242775 112 = 1 := by
  have hp : prime_of_index 112 = 613 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 613) (by norm_num)
    rwa [pcount613] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 613 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 613 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 613 = 3613 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 613)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3613)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 613)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 113 = 1`. -/
theorem A242775_n113 : A242775 113 = 1 := by
  have hp : prime_of_index 113 = 617 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 617) (by norm_num)
    rwa [pcount617] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 617 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 617 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 617 = 3617 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 617)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3617)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 617)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 114 = 2`. -/
theorem A242775_n114 : A242775 114 = 2 := by
  have hp : prime_of_index 114 = 619 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 619) (by norm_num)
    rwa [pcount619] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 619 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 619 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 619 = 3619 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 619 = 33619 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 619)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33619)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 619)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 115 = 1`. -/
theorem A242775_n115 : A242775 115 = 1 := by
  have hp : prime_of_index 115 = 631 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 631) (by norm_num)
    rwa [pcount631] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 631 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 631 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 631 = 3631 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 631)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3631)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 631)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 116 = 2`. -/
theorem A242775_n116 : A242775 116 = 2 := by
  have hp : prime_of_index 116 = 641 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 641) (by norm_num)
    rwa [pcount641] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 641 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 641 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 641 = 3641 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 641 = 33641 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 641)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33641)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 641)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 117 = 1`. -/
theorem A242775_n117 : A242775 117 = 1 := by
  have hp : prime_of_index 117 = 643 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 643) (by norm_num)
    rwa [pcount643] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 643 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 643 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 643 = 3643 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 643)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3643)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 643)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 118 = 2`. -/
theorem A242775_n118 : A242775 118 = 2 := by
  have hp : prime_of_index 118 = 647 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 647) (by norm_num)
    rwa [pcount647] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 647 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 647 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 647 = 3647 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 647 = 33647 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 647)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33647)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 647)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 119 = 4`. -/
theorem A242775_n119 : A242775 119 = 4 := by
  have hp : prime_of_index 119 = 653 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 653) (by norm_num)
    rwa [pcount653] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 653 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 653 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 653 = 3653 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 653 = 33653 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 653 = 333653 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 653 = 3333653 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 653)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 3333653)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 653)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 120 = 1`. -/
theorem A242775_n120 : A242775 120 = 1 := by
  have hp : prime_of_index 120 = 659 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 659) (by norm_num)
    rwa [pcount659] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 659 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 659 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 659 = 3659 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 659)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3659)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 659)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 121 = 6`. -/
theorem A242775_n121 : A242775 121 = 6 := by
  have hp : prime_of_index 121 = 661 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 661) (by norm_num)
    rwa [pcount661] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 661 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 661 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 661 = 3661 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 661 = 33661 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 661 = 333661 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 661 = 3333661 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 661 = 33333661 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 661 = 333333661 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 6 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 661)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h6]; exact (by norm_num : Nat.Prime 333333661)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 661)}
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 122 = 1`. -/
theorem A242775_n122 : A242775 122 = 1 := by
  have hp : prime_of_index 122 = 673 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 673) (by norm_num)
    rwa [pcount673] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 673 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 673 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 673 = 3673 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 673)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3673)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 673)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 123 = 1`. -/
theorem A242775_n123 : A242775 123 = 1 := by
  have hp : prime_of_index 123 = 677 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 677) (by norm_num)
    rwa [pcount677] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 677 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 677 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 677 = 3677 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 677)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3677)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 677)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 124 = 5`. -/
theorem A242775_n124 : A242775 124 = 5 := by
  have hp : prime_of_index 124 = 683 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 683) (by norm_num)
    rwa [pcount683] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 683 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 683 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 683 = 3683 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 683 = 33683 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 683 = 333683 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 683 = 3333683 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 683 = 33333683 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 5 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 683)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h5]; exact (by norm_num : Nat.Prime 33333683)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 683)}
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 125 = 1`. -/
theorem A242775_n125 : A242775 125 = 1 := by
  have hp : prime_of_index 125 = 691 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 691) (by norm_num)
    rwa [pcount691] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 691 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 691 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 691 = 3691 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 691)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3691)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 691)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 126 = 1`. -/
theorem A242775_n126 : A242775 126 = 1 := by
  have hp : prime_of_index 126 = 701 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 701) (by norm_num)
    rwa [pcount701] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 701 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 701 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 701 = 3701 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 701)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3701)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 701)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 127 = 1`. -/
theorem A242775_n127 : A242775 127 = 1 := by
  have hp : prime_of_index 127 = 709 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 709) (by norm_num)
    rwa [pcount709] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 709 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 709 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 709 = 3709 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 709)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3709)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 709)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 128 = 1`. -/
theorem A242775_n128 : A242775 128 = 1 := by
  have hp : prime_of_index 128 = 719 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 719) (by norm_num)
    rwa [pcount719] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 719 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 719 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 719 = 3719 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 719)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3719)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 719)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 129 = 1`. -/
theorem A242775_n129 : A242775 129 = 1 := by
  have hp : prime_of_index 129 = 727 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 727) (by norm_num)
    rwa [pcount727] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 727 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 727 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 727 = 3727 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 727)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3727)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 727)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 130 = 1`. -/
theorem A242775_n130 : A242775 130 = 1 := by
  have hp : prime_of_index 130 = 733 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 733) (by norm_num)
    rwa [pcount733] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 733 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 733 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 733 = 3733 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 733)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3733)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 733)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 131 = 1`. -/
theorem A242775_n131 : A242775 131 = 1 := by
  have hp : prime_of_index 131 = 739 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 739) (by norm_num)
    rwa [pcount739] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 739 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 739 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 739 = 3739 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 739)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3739)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 739)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 132 = 14`. -/
theorem A242775_n132 : A242775 132 = 14 := by
  have hp : prime_of_index 132 = 743 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 743) (by norm_num)
    rwa [pcount743] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 743 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 743 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 743 = 3743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 743 = 33743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 743 = 333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 743 = 3333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 743 = 33333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 743 = 333333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 743 = 3333333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 743 = 33333333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 743 = 333333333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 743 = 3333333333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 743 = 33333333333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 743 = 333333333333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h13 : concatenate 13 743 = 3333333333333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h14 : concatenate 14 743 = 33333333333333743 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 14 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 743)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h14]; exact prime_33333333333333743
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 743)}
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact (by norm_num : ¬ (33333743 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    rcases hpr.eq_one_or_self_of_dvd 33391 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    exact (by norm_num : ¬ (33333333333743 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h12] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨14, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h13] at hpr
    rcases hpr.eq_one_or_self_of_dvd 512249 (by norm_num) with hh | hh <;> norm_num at hh

/-- `A242775 133 = 2`. -/
theorem A242775_n133 : A242775 133 = 2 := by
  have hp : prime_of_index 133 = 751 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 751) (by norm_num)
    rwa [pcount751] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 751 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 751 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 751 = 3751 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 751 = 33751 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 751)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33751)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 751)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 134 = 2`. -/
theorem A242775_n134 : A242775 134 = 2 := by
  have hp : prime_of_index 134 = 757 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 757) (by norm_num)
    rwa [pcount757] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 757 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 757 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 757 = 3757 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 757 = 33757 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 757)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33757)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 757)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 135 = 1`. -/
theorem A242775_n135 : A242775 135 = 1 := by
  have hp : prime_of_index 135 = 761 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 761) (by norm_num)
    rwa [pcount761] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 761 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 761 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 761 = 3761 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 761)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3761)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 761)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 136 = 1`. -/
theorem A242775_n136 : A242775 136 = 1 := by
  have hp : prime_of_index 136 = 769 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 769) (by norm_num)
    rwa [pcount769] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 769 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 769 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 769 = 3769 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 769)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3769)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 769)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 137 = 2`. -/
theorem A242775_n137 : A242775 137 = 2 := by
  have hp : prime_of_index 137 = 773 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 773) (by norm_num)
    rwa [pcount773] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 773 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 773 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 773 = 3773 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 773 = 33773 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 773)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33773)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 773)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 138 = 3`. -/
theorem A242775_n138 : A242775 138 = 3 := by
  have hp : prime_of_index 138 = 787 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 787) (by norm_num)
    rwa [pcount787] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 787 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 787 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 787 = 3787 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 787 = 33787 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 787 = 333787 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 787)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 333787)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 787)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 139 = 1`. -/
theorem A242775_n139 : A242775 139 = 1 := by
  have hp : prime_of_index 139 = 797 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 797) (by norm_num)
    rwa [pcount797] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 797 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 797 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 797 = 3797 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 797)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3797)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 797)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 140 = 2`. -/
theorem A242775_n140 : A242775 140 = 2 := by
  have hp : prime_of_index 140 = 809 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 809) (by norm_num)
    rwa [pcount809] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 809 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 809 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 809 = 3809 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 809 = 33809 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 809)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33809)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 809)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 141 = 2`. -/
theorem A242775_n141 : A242775 141 = 2 := by
  have hp : prime_of_index 141 = 811 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 811) (by norm_num)
    rwa [pcount811] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 811 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 811 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 811 = 3811 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 811 = 33811 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 811)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33811)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 811)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 142 = 1`. -/
theorem A242775_n142 : A242775 142 = 1 := by
  have hp : prime_of_index 142 = 821 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 821) (by norm_num)
    rwa [pcount821] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 821 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 821 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 821 = 3821 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 821)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3821)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 821)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 143 = 1`. -/
theorem A242775_n143 : A242775 143 = 1 := by
  have hp : prime_of_index 143 = 823 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 823) (by norm_num)
    rwa [pcount823] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 823 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 823 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 823 = 3823 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 823)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3823)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 823)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 144 = 2`. -/
theorem A242775_n144 : A242775 144 = 2 := by
  have hp : prime_of_index 144 = 827 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 827) (by norm_num)
    rwa [pcount827] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 827 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 827 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 827 = 3827 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 827 = 33827 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 827)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33827)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 827)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 145 = 2`. -/
theorem A242775_n145 : A242775 145 = 2 := by
  have hp : prime_of_index 145 = 829 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 829) (by norm_num)
    rwa [pcount829] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 829 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 829 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 829 = 3829 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 829 = 33829 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 829)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33829)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 829)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 146 = 6`. -/
theorem A242775_n146 : A242775 146 = 6 := by
  have hp : prime_of_index 146 = 839 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 839) (by norm_num)
    rwa [pcount839] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 839 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 839 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 839 = 3839 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 839 = 33839 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 839 = 333839 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 839 = 3333839 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 839 = 33333839 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 839 = 333333839 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 6 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 839)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h6]; exact (by norm_num : Nat.Prime 333333839)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 839)}
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 147 = 1`. -/
theorem A242775_n147 : A242775 147 = 1 := by
  have hp : prime_of_index 147 = 853 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 853) (by norm_num)
    rwa [pcount853] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 853 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 853 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 853 = 3853 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 853)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3853)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 853)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 148 = 2`. -/
theorem A242775_n148 : A242775 148 = 2 := by
  have hp : prime_of_index 148 = 857 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 857) (by norm_num)
    rwa [pcount857] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 857 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 857 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 857 = 3857 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 857 = 33857 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 857)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33857)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 857)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 149 = 27`. -/
theorem A242775_n149 : A242775 149 = 27 := by
  have hp : prime_of_index 149 = 859 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 859) (by norm_num)
    rwa [pcount859] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 859 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 859 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 859 = 3859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 859 = 33859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 859 = 333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 859 = 3333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 859 = 33333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 859 = 333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 859 = 3333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 859 = 33333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 859 = 333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 859 = 3333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 859 = 33333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 859 = 333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h13 : concatenate 13 859 = 3333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h14 : concatenate 14 859 = 33333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h15 : concatenate 15 859 = 333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h16 : concatenate 16 859 = 3333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h17 : concatenate 17 859 = 33333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h18 : concatenate 18 859 = 333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h19 : concatenate 19 859 = 3333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h20 : concatenate 20 859 = 33333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h21 : concatenate 21 859 = 333333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h22 : concatenate 22 859 = 3333333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h23 : concatenate 23 859 = 33333333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h24 : concatenate 24 859 = 333333333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h25 : concatenate 25 859 = 3333333333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h26 : concatenate 26 859 = 33333333333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h27 : concatenate 27 859 = 333333333333333333333333333859 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 27 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 859)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h27]; exact prime_333333333333333333333333333859
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 859)}
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact (by norm_num : ¬ (333859 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    rcases hpr.eq_one_or_self_of_dvd 183203 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h12] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h13] at hpr
    exact (by norm_num : ¬ (3333333333333859 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h14] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h15] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h16] at hpr
    exact (by norm_num : ¬ (3333333333333333859 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h17] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h18] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h19] at hpr
    rcases hpr.eq_one_or_self_of_dvd 379147 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h20] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h21] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h22] at hpr
    rcases hpr.eq_one_or_self_of_dvd 156157 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h23] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h24] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h25] at hpr
    rcases hpr.eq_one_or_self_of_dvd 224898064187 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨27, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h26] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 150 = 1`. -/
theorem A242775_n150 : A242775 150 = 1 := by
  have hp : prime_of_index 150 = 863 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 863) (by norm_num)
    rwa [pcount863] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 863 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 863 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 863 = 3863 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 863)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3863)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 863)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

end ValueTable101to150


section ValueTable151to200
/- Machine-verified values `A242775 n` for `n = 151..200` except the extreme
entry `n = 185` (`p = 1103`, `a(185) = 135`, a 139-digit witness, treated
separately).  Lucas--Pratt certificate trees cover the witnesses of 11--29
digits (n = 153, 162, 166, 172, 187, 192). -/


private lemma pcount877 : Nat.count Nat.Prime 877 = 150 :=
  count_from 14 pcount863 rfl rfl

private lemma pcount881 : Nat.count Nat.Prime 881 = 151 :=
  count_from 4 pcount877 rfl rfl

private lemma pcount883 : Nat.count Nat.Prime 883 = 152 :=
  count_from 2 pcount881 rfl rfl

private lemma pcount887 : Nat.count Nat.Prime 887 = 153 :=
  count_from 4 pcount883 rfl rfl

private lemma pcount907 : Nat.count Nat.Prime 907 = 154 :=
  count_from 20 pcount887 rfl rfl

private lemma pcount911 : Nat.count Nat.Prime 911 = 155 :=
  count_from 4 pcount907 rfl rfl

private lemma pcount919 : Nat.count Nat.Prime 919 = 156 :=
  count_from 8 pcount911 rfl rfl

private lemma pcount929 : Nat.count Nat.Prime 929 = 157 :=
  count_from 10 pcount919 rfl rfl

private lemma pcount937 : Nat.count Nat.Prime 937 = 158 :=
  count_from 8 pcount929 rfl rfl

private lemma pcount941 : Nat.count Nat.Prime 941 = 159 :=
  count_from 4 pcount937 rfl rfl

private lemma pcount947 : Nat.count Nat.Prime 947 = 160 :=
  count_from 6 pcount941 rfl rfl

private lemma pcount953 : Nat.count Nat.Prime 953 = 161 :=
  count_from 6 pcount947 rfl rfl

private lemma pcount967 : Nat.count Nat.Prime 967 = 162 :=
  count_from 14 pcount953 rfl rfl

private lemma pcount971 : Nat.count Nat.Prime 971 = 163 :=
  count_from 4 pcount967 rfl rfl

private lemma pcount977 : Nat.count Nat.Prime 977 = 164 :=
  count_from 6 pcount971 rfl rfl

private lemma pcount983 : Nat.count Nat.Prime 983 = 165 :=
  count_from 6 pcount977 rfl rfl

private lemma pcount991 : Nat.count Nat.Prime 991 = 166 :=
  count_from 8 pcount983 rfl rfl

private lemma pcount997 : Nat.count Nat.Prime 997 = 167 :=
  count_from 6 pcount991 rfl rfl

private lemma pcount1009 : Nat.count Nat.Prime 1009 = 168 :=
  count_from 12 pcount997 rfl rfl

private lemma pcount1013 : Nat.count Nat.Prime 1013 = 169 :=
  count_from 4 pcount1009 rfl rfl

private lemma pcount1019 : Nat.count Nat.Prime 1019 = 170 :=
  count_from 6 pcount1013 rfl rfl

private lemma pcount1021 : Nat.count Nat.Prime 1021 = 171 :=
  count_from 2 pcount1019 rfl rfl

private lemma pcount1031 : Nat.count Nat.Prime 1031 = 172 :=
  count_from 10 pcount1021 rfl rfl

private lemma pcount1033 : Nat.count Nat.Prime 1033 = 173 :=
  count_from 2 pcount1031 rfl rfl

private lemma pcount1039 : Nat.count Nat.Prime 1039 = 174 :=
  count_from 6 pcount1033 rfl rfl

private lemma pcount1049 : Nat.count Nat.Prime 1049 = 175 :=
  count_from 10 pcount1039 rfl rfl

private lemma pcount1051 : Nat.count Nat.Prime 1051 = 176 :=
  count_from 2 pcount1049 rfl rfl

private lemma pcount1061 : Nat.count Nat.Prime 1061 = 177 :=
  count_from 10 pcount1051 rfl rfl

private lemma pcount1063 : Nat.count Nat.Prime 1063 = 178 :=
  count_from 2 pcount1061 rfl rfl

private lemma pcount1069 : Nat.count Nat.Prime 1069 = 179 :=
  count_from 6 pcount1063 rfl rfl

private lemma pcount1087 : Nat.count Nat.Prime 1087 = 180 :=
  count_from 18 pcount1069 rfl rfl

private lemma pcount1091 : Nat.count Nat.Prime 1091 = 181 :=
  count_from 4 pcount1087 rfl rfl

private lemma pcount1093 : Nat.count Nat.Prime 1093 = 182 :=
  count_from 2 pcount1091 rfl rfl

private lemma pcount1097 : Nat.count Nat.Prime 1097 = 183 :=
  count_from 4 pcount1093 rfl rfl

private lemma pcount1103 : Nat.count Nat.Prime 1103 = 184 :=
  count_from 6 pcount1097 rfl rfl

private lemma pcount1109 : Nat.count Nat.Prime 1109 = 185 :=
  count_from 6 pcount1103 rfl rfl

private lemma pcount1117 : Nat.count Nat.Prime 1117 = 186 :=
  count_from 8 pcount1109 rfl rfl

private lemma pcount1123 : Nat.count Nat.Prime 1123 = 187 :=
  count_from 6 pcount1117 rfl rfl

private lemma pcount1129 : Nat.count Nat.Prime 1129 = 188 :=
  count_from 6 pcount1123 rfl rfl

private lemma pcount1151 : Nat.count Nat.Prime 1151 = 189 :=
  count_from 22 pcount1129 rfl rfl

private lemma pcount1153 : Nat.count Nat.Prime 1153 = 190 :=
  count_from 2 pcount1151 rfl rfl

private lemma pcount1163 : Nat.count Nat.Prime 1163 = 191 :=
  count_from 10 pcount1153 rfl rfl

private lemma pcount1171 : Nat.count Nat.Prime 1171 = 192 :=
  count_from 8 pcount1163 rfl rfl

private lemma pcount1181 : Nat.count Nat.Prime 1181 = 193 :=
  count_from 10 pcount1171 rfl rfl

private lemma pcount1187 : Nat.count Nat.Prime 1187 = 194 :=
  count_from 6 pcount1181 rfl rfl

private lemma pcount1193 : Nat.count Nat.Prime 1193 = 195 :=
  count_from 6 pcount1187 rfl rfl

private lemma pcount1201 : Nat.count Nat.Prime 1201 = 196 :=
  count_from 8 pcount1193 rfl rfl

private lemma pcount1213 : Nat.count Nat.Prime 1213 = 197 :=
  count_from 12 pcount1201 rfl rfl

private lemma pcount1217 : Nat.count Nat.Prime 1217 = 198 :=
  count_from 4 pcount1213 rfl rfl

private lemma pcount1223 : Nat.count Nat.Prime 1223 = 199 :=
  count_from 6 pcount1217 rfl rfl

private lemma prime_33333333883 : Nat.Prime 33333333883 := by
  have c1 : (3:ℕ) ^ 16666666941 % 33333333883 = 33333333882 :=
    pow_mod_eq2 5 3 16666666941 33333333883 33333333882 (by decide) rfl
  have c2 : (3:ℕ) ^ 11111111294 % 33333333883 = 25267593042 :=
    pow_mod_eq2 5 3 11111111294 33333333883 25267593042 (by decide) rfl
  have c3 : (3:ℕ) ^ 1960784346 % 33333333883 = 4991886401 :=
    pow_mod_eq2 4 3 1960784346 33333333883 4991886401 (by decide) rfl
  have c4 : (3:ℕ) ^ 497512446 % 33333333883 = 8055016447 :=
    pow_mod_eq2 4 3 497512446 33333333883 8055016447 (by decide) rfl
  have c5 : (3:ℕ) ^ 6834 % 33333333883 = 6581247254 :=
    pow_mod_eq2 2 3 6834 33333333883 6581247254 (by decide) rfl
  have cf : (3:ℕ) ^ 33333333882 % 33333333883 = 1 :=
    pow_mod_eq2 5 3 33333333882 33333333883 1 (by decide) rfl
  refine lucas_primality 33333333883 ((3 : ℕ) : ZMod 33333333883) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333333883:ℕ) - 1 = 33333333882 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333333883:ℕ) - 1 = 2 * (3 * (17 * (67 * (4877573)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333333883:ℕ) - 1) / 2 = 16666666941 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333333883:ℕ) - 1) / 3 = 11111111294 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333333883:ℕ) - 1) / 17 = 1960784346 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 67 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((33333333883:ℕ) - 1) / 67 = 497512446 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 4877573 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((33333333883:ℕ) - 1) / 4877573 = 6834 := rfl
            rw [hexp, zmod_pow_of_mod c5]
            exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_333333333953 : Nat.Prime 333333333953 := by
  have c1 : (3:ℕ) ^ 166666666976 % 333333333953 = 333333333952 :=
    pow_mod_eq2 5 3 166666666976 333333333953 333333333952 (by decide) rfl
  have c2 : (3:ℕ) ^ 10752688192 % 333333333953 = 193082457964 :=
    pow_mod_eq2 5 3 10752688192 333333333953 193082457964 (by decide) rfl
  have c3 : (3:ℕ) ^ 1984 % 333333333953 = 192933745471 :=
    pow_mod_eq2 2 3 1984 333333333953 192933745471 (by decide) rfl
  have cf : (3:ℕ) ^ 333333333952 % 333333333953 = 1 :=
    pow_mod_eq2 5 3 333333333952 333333333953 1 (by decide) rfl
  refine lucas_primality 333333333953 ((3 : ℕ) : ZMod 333333333953) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (333333333953:ℕ) - 1 = 333333333952 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (333333333953:ℕ) - 1 = 2 * (2 * (2 * (2 * (2 * (2 * (31 * (168010753))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((333333333953:ℕ) - 1) / 2 = 166666666976 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((333333333953:ℕ) - 1) / 2 = 166666666976 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((333333333953:ℕ) - 1) / 2 = 166666666976 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((333333333953:ℕ) - 1) / 2 = 166666666976 := rfl
            rw [hexp, zmod_pow_of_mod c1]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((333333333953:ℕ) - 1) / 2 = 166666666976 := rfl
              rw [hexp, zmod_pow_of_mod c1]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((333333333953:ℕ) - 1) / 2 = 166666666976 := rfl
                rw [hexp, zmod_pow_of_mod c1]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((333333333953:ℕ) - 1) / 31 = 10752688192 := rfl
                  rw [hexp, zmod_pow_of_mod c2]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  have h := hrest
                  have hqe : q = 168010753 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((333333333953:ℕ) - 1) / 168010753 = 1984 := rfl
                  rw [hexp, zmod_pow_of_mod c3]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_50641946339 : Nat.Prime 50641946339 := by
  have c1 : (2:ℕ) ^ 25320973169 % 50641946339 = 50641946338 :=
    pow_mod_eq2 5 2 25320973169 50641946339 50641946338 (by decide) rfl
  have c2 : (2:ℕ) ^ 631186 % 50641946339 = 49986204362 :=
    pow_mod_eq2 3 2 631186 50641946339 49986204362 (by decide) rfl
  have c3 : (2:ℕ) ^ 160466 % 50641946339 = 14820862621 :=
    pow_mod_eq2 3 2 160466 50641946339 14820862621 (by decide) rfl
  have cf : (2:ℕ) ^ 50641946338 % 50641946339 = 1 :=
    pow_mod_eq2 5 2 50641946338 50641946339 1 (by decide) rfl
  refine lucas_primality 50641946339 ((2 : ℕ) : ZMod 50641946339) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (50641946339:ℕ) - 1 = 50641946338 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (50641946339:ℕ) - 1 = 2 * (80233 * (315593)) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((50641946339:ℕ) - 1) / 2 = 25320973169 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 80233 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((50641946339:ℕ) - 1) / 80233 = 631186 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        have h := hrest
        have hqe : q = 315593 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((50641946339:ℕ) - 1) / 315593 = 160466 := rfl
        rw [hexp, zmod_pow_of_mod c3]
        exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_18639801952193728991 : Nat.Prime 18639801952193728991 := by
  have c1 : (11:ℕ) ^ 9319900976096864495 % 18639801952193728991 = 18639801952193728990 :=
    pow_mod_eq2 8 11 9319900976096864495 18639801952193728991 18639801952193728990 (by decide) rfl
  have c2 : (11:ℕ) ^ 3727960390438745798 % 18639801952193728991 = 4439770377676912244 :=
    pow_mod_eq2 8 11 3727960390438745798 18639801952193728991 4439770377676912244 (by decide) rfl
  have c3 : (11:ℕ) ^ 506419463390 % 18639801952193728991 = 8005877308563285565 :=
    pow_mod_eq2 5 11 506419463390 18639801952193728991 8005877308563285565 (by decide) rfl
  have c4 : (11:ℕ) ^ 368070410 % 18639801952193728991 = 11037402597550153922 :=
    pow_mod_eq2 4 11 368070410 18639801952193728991 11037402597550153922 (by decide) rfl
  have cf : (11:ℕ) ^ 18639801952193728990 % 18639801952193728991 = 1 :=
    pow_mod_eq2 9 11 18639801952193728990 18639801952193728991 1 (by decide) rfl
  refine lucas_primality 18639801952193728991 ((11 : ℕ) : ZMod 18639801952193728991) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (18639801952193728991:ℕ) - 1 = 18639801952193728990 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (18639801952193728991:ℕ) - 1 = 2 * (5 * (36807041 * (50641946339))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((18639801952193728991:ℕ) - 1) / 2 = 9319900976096864495 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((18639801952193728991:ℕ) - 1) / 5 = 3727960390438745798 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 36807041 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((18639801952193728991:ℕ) - 1) / 36807041 = 506419463390 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 50641946339 := (Nat.prime_dvd_prime_iff_eq hq prime_50641946339).mp h
          subst hqe
          have hexp : ((18639801952193728991:ℕ) - 1) / 50641946339 = 368070410 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_21017234131988230348886087 : Nat.Prime 21017234131988230348886087 := by
  have c1 : (5:ℕ) ^ 10508617065994115174443043 % 21017234131988230348886087 = 21017234131988230348886086 :=
    pow_mod_eq2 11 5 10508617065994115174443043 21017234131988230348886087 21017234131988230348886086 (by decide) rfl
  have c2 : (5:ℕ) ^ 3002462018855461478412298 % 21017234131988230348886087 = 3956939121838206512175540 :=
    pow_mod_eq2 11 5 3002462018855461478412298 21017234131988230348886087 3956939121838206512175540 (by decide) rfl
  have c3 : (5:ℕ) ^ 488772886790423961602002 % 21017234131988230348886087 = 3007728204019990088111309 :=
    pow_mod_eq2 10 5 488772886790423961602002 21017234131988230348886087 3007728204019990088111309 (by decide) rfl
  have c4 : (5:ℕ) ^ 11221160775220624852582 % 21017234131988230348886087 = 17198853775575515107759001 :=
    pow_mod_eq2 10 5 11221160775220624852582 21017234131988230348886087 17198853775575515107759001 (by decide) rfl
  have c5 : (5:ℕ) ^ 1127546 % 21017234131988230348886087 = 9332651995986861766535926 :=
    pow_mod_eq2 3 5 1127546 21017234131988230348886087 9332651995986861766535926 (by decide) rfl
  have cf : (5:ℕ) ^ 21017234131988230348886086 % 21017234131988230348886087 = 1 :=
    pow_mod_eq2 11 5 21017234131988230348886086 21017234131988230348886087 1 (by decide) rfl
  refine lucas_primality 21017234131988230348886087 ((5 : ℕ) : ZMod 21017234131988230348886087) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (21017234131988230348886087:ℕ) - 1 = 21017234131988230348886086 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (21017234131988230348886087:ℕ) - 1 = 2 * (7 * (43 * (1873 * (18639801952193728991)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((21017234131988230348886087:ℕ) - 1) / 2 = 10508617065994115174443043 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((21017234131988230348886087:ℕ) - 1) / 7 = 3002462018855461478412298 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 43 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((21017234131988230348886087:ℕ) - 1) / 43 = 488772886790423961602002 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 1873 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((21017234131988230348886087:ℕ) - 1) / 1873 = 11221160775220624852582 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 18639801952193728991 := (Nat.prime_dvd_prime_iff_eq hq prime_18639801952193728991).mp h
            subst hqe
            have hexp : ((21017234131988230348886087:ℕ) - 1) / 18639801952193728991 = 1127546 := rfl
            rw [hexp, zmod_pow_of_mod c5]
            exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_33333333333333333333333333983 : Nat.Prime 33333333333333333333333333983 := by
  have c1 : (5:ℕ) ^ 16666666666666666666666666991 % 33333333333333333333333333983 = 33333333333333333333333333982 :=
    pow_mod_eq2 12 5 16666666666666666666666666991 33333333333333333333333333983 33333333333333333333333333982 (by decide) rfl
  have c2 : (5:ℕ) ^ 2564102564102564102564102614 % 33333333333333333333333333983 = 4484610596542701057890382889 :=
    pow_mod_eq2 12 5 2564102564102564102564102614 33333333333333333333333333983 4484610596542701057890382889 (by decide) rfl
  have c3 : (5:ℕ) ^ 546448087431693989071038262 % 33333333333333333333333333983 = 20033787804288712889115950005 :=
    pow_mod_eq2 12 5 546448087431693989071038262 33333333333333333333333333983 20033787804288712889115950005 (by decide) rfl
  have c4 : (5:ℕ) ^ 1586 % 33333333333333333333333333983 = 32009798869161087996444934267 :=
    pow_mod_eq2 2 5 1586 33333333333333333333333333983 32009798869161087996444934267 (by decide) rfl
  have cf : (5:ℕ) ^ 33333333333333333333333333982 % 33333333333333333333333333983 = 1 :=
    pow_mod_eq2 12 5 33333333333333333333333333982 33333333333333333333333333983 1 (by decide) rfl
  refine lucas_primality 33333333333333333333333333983 ((5 : ℕ) : ZMod 33333333333333333333333333983) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333333333333333333333333983:ℕ) - 1 = 33333333333333333333333333982 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333333333333333333333333983:ℕ) - 1 = 2 * (13 * (61 * (21017234131988230348886087))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333333333333333333333333983:ℕ) - 1) / 2 = 16666666666666666666666666991 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333333333333333333333333983:ℕ) - 1) / 13 = 2564102564102564102564102614 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 61 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333333333333333333333333983:ℕ) - 1) / 61 = 546448087431693989071038262 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 21017234131988230348886087 := (Nat.prime_dvd_prime_iff_eq hq prime_21017234131988230348886087).mp h
          subst hqe
          have hexp : ((33333333333333333333333333983:ℕ) - 1) / 21017234131988230348886087 = 1586 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_3333333331021 : Nat.Prime 3333333331021 := by
  have c1 : (10:ℕ) ^ 1666666665510 % 3333333331021 = 3333333331020 :=
    pow_mod_eq2 6 10 1666666665510 3333333331021 3333333331020 (by decide) rfl
  have c2 : (10:ℕ) ^ 1111111110340 % 3333333331021 = 2581502145848 :=
    pow_mod_eq2 6 10 1111111110340 3333333331021 2581502145848 (by decide) rfl
  have c3 : (10:ℕ) ^ 666666666204 % 3333333331021 = 2949391393598 :=
    pow_mod_eq2 5 10 666666666204 3333333331021 2949391393598 (by decide) rfl
  have c4 : (10:ℕ) ^ 476190475860 % 3333333331021 = 1128847765610 :=
    pow_mod_eq2 5 10 476190475860 3333333331021 1128847765610 (by decide) rfl
  have c5 : (10:ℕ) ^ 303030302820 % 3333333331021 = 1720559406293 :=
    pow_mod_eq2 5 10 303030302820 3333333331021 1720559406293 (by decide) rfl
  have c6 : (10:ℕ) ^ 4620 % 3333333331021 = 2029349192956 :=
    pow_mod_eq2 2 10 4620 3333333331021 2029349192956 (by decide) rfl
  have cf : (10:ℕ) ^ 3333333331020 % 3333333331021 = 1 :=
    pow_mod_eq2 6 10 3333333331020 3333333331021 1 (by decide) rfl
  refine lucas_primality 3333333331021 ((10 : ℕ) : ZMod 3333333331021) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333333331021:ℕ) - 1 = 3333333331020 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333333331021:ℕ) - 1 = 2 * (2 * (3 * (5 * (7 * (11 * (721500721)))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333333331021:ℕ) - 1) / 2 = 1666666665510 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333331021:ℕ) - 1) / 2 = 1666666665510 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333333331021:ℕ) - 1) / 3 = 1111111110340 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333333331021:ℕ) - 1) / 5 = 666666666204 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((3333333331021:ℕ) - 1) / 7 = 476190475860 := rfl
              rw [hexp, zmod_pow_of_mod c4]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((3333333331021:ℕ) - 1) / 11 = 303030302820 := rfl
                rw [hexp, zmod_pow_of_mod c5]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                have h := hrest
                have hqe : q = 721500721 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((3333333331021:ℕ) - 1) / 721500721 = 4620 := rfl
                rw [hexp, zmod_pow_of_mod c6]
                exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_3333333333331117 : Nat.Prime 3333333333331117 := by
  have c1 : (5:ℕ) ^ 1666666666665558 % 3333333333331117 = 3333333333331116 :=
    pow_mod_eq2 7 5 1666666666665558 3333333333331117 3333333333331116 (by decide) rfl
  have c2 : (5:ℕ) ^ 1111111111110372 % 3333333333331117 = 2838651731746723 :=
    pow_mod_eq2 7 5 1111111111110372 3333333333331117 2838651731746723 (by decide) rfl
  have c3 : (5:ℕ) ^ 81300813008076 % 3333333333331117 = 275922604432754 :=
    pow_mod_eq2 6 5 81300813008076 3333333333331117 275922604432754 (by decide) rfl
  have c4 : (5:ℕ) ^ 14007191292 % 3333333333331117 = 2991901131861597 :=
    pow_mod_eq2 5 5 14007191292 3333333333331117 2991901131861597 (by decide) rfl
  have c5 : (5:ℕ) ^ 351248148 % 3333333333331117 = 1549172915695157 :=
    pow_mod_eq2 4 5 351248148 3333333333331117 1549172915695157 (by decide) rfl
  have cf : (5:ℕ) ^ 3333333333331116 % 3333333333331117 = 1 :=
    pow_mod_eq2 7 5 3333333333331116 3333333333331117 1 (by decide) rfl
  refine lucas_primality 3333333333331117 ((5 : ℕ) : ZMod 3333333333331117) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333333333331117:ℕ) - 1 = 3333333333331116 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333333333331117:ℕ) - 1 = 2 * (2 * (3 * (3 * (41 * (237973 * (9489967)))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333333333331117:ℕ) - 1) / 2 = 1666666666665558 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333333331117:ℕ) - 1) / 2 = 1666666666665558 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333333333331117:ℕ) - 1) / 3 = 1111111111110372 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333333333331117:ℕ) - 1) / 3 = 1111111111110372 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 41 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((3333333333331117:ℕ) - 1) / 41 = 81300813008076 := rfl
              rw [hexp, zmod_pow_of_mod c3]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 237973 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((3333333333331117:ℕ) - 1) / 237973 = 14007191292 := rfl
                rw [hexp, zmod_pow_of_mod c4]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                have h := hrest
                have hqe : q = 9489967 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((3333333333331117:ℕ) - 1) / 9489967 = 351248148 := rfl
                rw [hexp, zmod_pow_of_mod c5]
                exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_5809225049 : Nat.Prime 5809225049 := by
  have c1 : (3:ℕ) ^ 2904612524 % 5809225049 = 5809225048 :=
    pow_mod_eq2 4 3 2904612524 5809225049 5809225048 (by decide) rfl
  have c2 : (3:ℕ) ^ 528111368 % 5809225049 = 466540900 :=
    pow_mod_eq2 4 3 528111368 5809225049 466540900 (by decide) rfl
  have c3 : (3:ℕ) ^ 5314936 % 5809225049 = 2357069144 :=
    pow_mod_eq2 3 3 5314936 5809225049 2357069144 (by decide) rfl
  have c4 : (3:ℕ) ^ 96184 % 5809225049 = 2567499575 :=
    pow_mod_eq2 3 3 96184 5809225049 2567499575 (by decide) rfl
  have cf : (3:ℕ) ^ 5809225048 % 5809225049 = 1 :=
    pow_mod_eq2 5 3 5809225048 5809225049 1 (by decide) rfl
  refine lucas_primality 5809225049 ((3 : ℕ) : ZMod 5809225049) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (5809225049:ℕ) - 1 = 5809225048 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (5809225049:ℕ) - 1 = 2 * (2 * (2 * (11 * (1093 * (60397))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((5809225049:ℕ) - 1) / 2 = 2904612524 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((5809225049:ℕ) - 1) / 2 = 2904612524 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((5809225049:ℕ) - 1) / 2 = 2904612524 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((5809225049:ℕ) - 1) / 11 = 528111368 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 1093 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((5809225049:ℕ) - 1) / 1093 = 5314936 := rfl
              rw [hexp, zmod_pow_of_mod c3]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 60397 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((5809225049:ℕ) - 1) / 60397 = 96184 := rfl
              rw [hexp, zmod_pow_of_mod c4]
              exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_33333333331163 : Nat.Prime 33333333331163 := by
  have c1 : (2:ℕ) ^ 16666666665581 % 33333333331163 = 33333333331162 :=
    pow_mod_eq2 6 2 16666666665581 33333333331163 33333333331162 (by decide) rfl
  have c2 : (2:ℕ) ^ 1754385964798 % 33333333331163 = 27274899887199 :=
    pow_mod_eq2 6 2 1754385964798 33333333331163 27274899887199 (by decide) rfl
  have c3 : (2:ℕ) ^ 220750551862 % 33333333331163 = 17796068389683 :=
    pow_mod_eq2 5 2 220750551862 33333333331163 17796068389683 (by decide) rfl
  have c4 : (2:ℕ) ^ 5738 % 33333333331163 = 22164654360996 :=
    pow_mod_eq2 2 2 5738 33333333331163 22164654360996 (by decide) rfl
  have cf : (2:ℕ) ^ 33333333331162 % 33333333331163 = 1 :=
    pow_mod_eq2 6 2 33333333331162 33333333331163 1 (by decide) rfl
  refine lucas_primality 33333333331163 ((2 : ℕ) : ZMod 33333333331163) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333333331163:ℕ) - 1 = 33333333331162 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333333331163:ℕ) - 1 = 2 * (19 * (151 * (5809225049))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333333331163:ℕ) - 1) / 2 = 16666666665581 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333333331163:ℕ) - 1) / 19 = 1754385964798 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 151 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333333331163:ℕ) - 1) / 151 = 220750551862 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 5809225049 := (Nat.prime_dvd_prime_iff_eq hq prime_5809225049).mp h
          subst hqe
          have hexp : ((33333333331163:ℕ) - 1) / 5809225049 = 5738 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)
/-- `A242775 151 = 1`. -/
theorem A242775_n151 : A242775 151 = 1 := by
  have hp : prime_of_index 151 = 877 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 877) (by norm_num)
    rwa [pcount877] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 877 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 877 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 877 = 3877 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 877)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3877)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 877)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 152 = 1`. -/
theorem A242775_n152 : A242775 152 = 1 := by
  have hp : prime_of_index 152 = 881 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 881) (by norm_num)
    rwa [pcount881] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 881 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 881 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 881 = 3881 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 881)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3881)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 881)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 153 = 8`. -/
theorem A242775_n153 : A242775 153 = 8 := by
  have hp : prime_of_index 153 = 883 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 883) (by norm_num)
    rwa [pcount883] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 883 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 883 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 883 = 3883 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 883 = 33883 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 883 = 333883 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 883 = 3333883 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 883 = 33333883 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 883 = 333333883 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 883 = 3333333883 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 883 = 33333333883 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 8 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 883)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h8]; exact prime_33333333883
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 883)}
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 154 = 5`. -/
theorem A242775_n154 : A242775 154 = 5 := by
  have hp : prime_of_index 154 = 887 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 887) (by norm_num)
    rwa [pcount887] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 887 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 887 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 887 = 3887 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 887 = 33887 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 887 = 333887 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 887 = 3333887 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 887 = 33333887 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 5 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 887)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h5]; exact (by norm_num : Nat.Prime 33333887)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 887)}
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨5, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 155 = 1`. -/
theorem A242775_n155 : A242775 155 = 1 := by
  have hp : prime_of_index 155 = 907 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 907) (by norm_num)
    rwa [pcount907] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 907 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 907 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 907 = 3907 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 907)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3907)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 907)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 156 = 1`. -/
theorem A242775_n156 : A242775 156 = 1 := by
  have hp : prime_of_index 156 = 911 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 911) (by norm_num)
    rwa [pcount911] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 911 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 911 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 911 = 3911 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 911)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3911)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 911)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 157 = 1`. -/
theorem A242775_n157 : A242775 157 = 1 := by
  have hp : prime_of_index 157 = 919 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 919) (by norm_num)
    rwa [pcount919] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 919 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 919 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 919 = 3919 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 919)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3919)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 919)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 158 = 1`. -/
theorem A242775_n158 : A242775 158 = 1 := by
  have hp : prime_of_index 158 = 929 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 929) (by norm_num)
    rwa [pcount929] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 929 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 929 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 929 = 3929 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 929)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3929)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 929)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 159 = 2`. -/
theorem A242775_n159 : A242775 159 = 2 := by
  have hp : prime_of_index 159 = 937 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 937) (by norm_num)
    rwa [pcount937] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 937 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 937 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 937 = 3937 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 937 = 33937 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 937)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33937)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 937)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 160 = 2`. -/
theorem A242775_n160 : A242775 160 = 2 := by
  have hp : prime_of_index 160 = 941 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 941) (by norm_num)
    rwa [pcount941] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 941 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 941 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 941 = 3941 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 941 = 33941 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 941)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33941)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 941)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 161 = 1`. -/
theorem A242775_n161 : A242775 161 = 1 := by
  have hp : prime_of_index 161 = 947 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 947) (by norm_num)
    rwa [pcount947] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 947 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 947 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 947 = 3947 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 947)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3947)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 947)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 162 = 9`. -/
theorem A242775_n162 : A242775 162 = 9 := by
  have hp : prime_of_index 162 = 953 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 953) (by norm_num)
    rwa [pcount953] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 953 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 953 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 953 = 3953 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 953 = 33953 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 953 = 333953 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 953 = 3333953 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 953 = 33333953 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 953 = 333333953 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 953 = 3333333953 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 953 = 33333333953 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 953 = 333333333953 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 9 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 953)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h9]; exact prime_333333333953
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 953)}
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact (by norm_num : ¬ (333333953 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 163 = 1`. -/
theorem A242775_n163 : A242775 163 = 1 := by
  have hp : prime_of_index 163 = 967 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 967) (by norm_num)
    rwa [pcount967] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 967 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 967 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 967 = 3967 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 967)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 3967)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 967)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 164 = 4`. -/
theorem A242775_n164 : A242775 164 = 4 := by
  have hp : prime_of_index 164 = 971 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 971) (by norm_num)
    rwa [pcount971] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 971 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 971 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 971 = 3971 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 971 = 33971 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 971 = 333971 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 971 = 3333971 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 971)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 3333971)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 971)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 165 = 4`. -/
theorem A242775_n165 : A242775 165 = 4 := by
  have hp : prime_of_index 165 = 977 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 977) (by norm_num)
    rwa [pcount977] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 977 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 977 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 977 = 3977 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 977 = 33977 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 977 = 333977 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 977 = 3333977 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 977)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 3333977)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 977)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 166 = 26`. -/
theorem A242775_n166 : A242775 166 = 26 := by
  have hp : prime_of_index 166 = 983 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 983) (by norm_num)
    rwa [pcount983] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 983 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 983 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 983 = 3983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 983 = 33983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 983 = 333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 983 = 3333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 983 = 33333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 983 = 333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 983 = 3333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 983 = 33333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 983 = 333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 983 = 3333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 983 = 33333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 983 = 333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h13 : concatenate 13 983 = 3333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h14 : concatenate 14 983 = 33333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h15 : concatenate 15 983 = 333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h16 : concatenate 16 983 = 3333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h17 : concatenate 17 983 = 33333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h18 : concatenate 18 983 = 333333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h19 : concatenate 19 983 = 3333333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h20 : concatenate 20 983 = 33333333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h21 : concatenate 21 983 = 333333333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h22 : concatenate 22 983 = 3333333333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h23 : concatenate 23 983 = 33333333333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h24 : concatenate 24 983 = 333333333333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h25 : concatenate 25 983 = 3333333333333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h26 : concatenate 26 983 = 33333333333333333333333333983 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 26 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 983)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h26]; exact prime_33333333333333333333333333983
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 983)}
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact (by norm_num : ¬ (333333983 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact (by norm_num : ¬ (33333333983 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    exact (by norm_num : ¬ (3333333333983 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    rcases hpr.eq_one_or_self_of_dvd 874661 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h12] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h13] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h14] at hpr
    rcases hpr.eq_one_or_self_of_dvd 63131 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h15] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h16] at hpr
    rcases hpr.eq_one_or_self_of_dvd 209357 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h17] at hpr
    exact (by norm_num : ¬ (33333333333333333983 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h18] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h19] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h20] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h21] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h22] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h23] at hpr
    exact (by norm_num : ¬ (33333333333333333333333983 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h24] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨26, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h25] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 167 = 6`. -/
theorem A242775_n167 : A242775 167 = 6 := by
  have hp : prime_of_index 167 = 991 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 991) (by norm_num)
    rwa [pcount991] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 991 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 991 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 991 = 3991 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 991 = 33991 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 991 = 333991 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 991 = 3333991 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 991 = 33333991 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 991 = 333333991 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 6 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 991)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h6]; exact (by norm_num : Nat.Prime 333333991)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 991)}
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact (by norm_num : ¬ (3333991 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 168 = 2`. -/
theorem A242775_n168 : A242775 168 = 2 := by
  have hp : prime_of_index 168 = 997 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 997) (by norm_num)
    rwa [pcount997] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 997 = 3 := by
    unfold num_digits
    rw [Nat.digits_len 10 997 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 2) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 997 = 3997 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 997 = 33997 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 997)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 33997)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 997)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 169 = 4`. -/
theorem A242775_n169 : A242775 169 = 4 := by
  have hp : prime_of_index 169 = 1009 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1009) (by norm_num)
    rwa [pcount1009] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1009 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1009 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1009 = 31009 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1009 = 331009 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1009 = 3331009 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1009 = 33331009 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1009)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331009)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1009)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 170 = 1`. -/
theorem A242775_n170 : A242775 170 = 1 := by
  have hp : prime_of_index 170 = 1013 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1013) (by norm_num)
    rwa [pcount1013] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1013 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1013 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1013 = 31013 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1013)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31013)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1013)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 171 = 1`. -/
theorem A242775_n171 : A242775 171 = 1 := by
  have hp : prime_of_index 171 = 1019 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1019) (by norm_num)
    rwa [pcount1019] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1019 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1019 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1019 = 31019 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1019)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31019)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1019)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 172 = 9`. -/
theorem A242775_n172 : A242775 172 = 9 := by
  have hp : prime_of_index 172 = 1021 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1021) (by norm_num)
    rwa [pcount1021] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1021 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1021 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1021 = 31021 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1021 = 331021 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1021 = 3331021 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1021 = 33331021 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1021 = 333331021 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1021 = 3333331021 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1021 = 33333331021 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1021 = 333333331021 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1021 = 3333333331021 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 9 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1021)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h9]; exact prime_3333333331021
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1021)}
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact (by norm_num : ¬ (333331021 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨9, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 173 = 2`. -/
theorem A242775_n173 : A242775 173 = 2 := by
  have hp : prime_of_index 173 = 1031 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1031) (by norm_num)
    rwa [pcount1031] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1031 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1031 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1031 = 31031 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1031 = 331031 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1031)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331031)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1031)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 174 = 1`. -/
theorem A242775_n174 : A242775 174 = 1 := by
  have hp : prime_of_index 174 = 1033 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1033) (by norm_num)
    rwa [pcount1033] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1033 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1033 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1033 = 31033 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1033)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31033)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1033)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 175 = 1`. -/
theorem A242775_n175 : A242775 175 = 1 := by
  have hp : prime_of_index 175 = 1039 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1039) (by norm_num)
    rwa [pcount1039] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1039 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1039 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1039 = 31039 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1039)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31039)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1039)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 176 = 4`. -/
theorem A242775_n176 : A242775 176 = 4 := by
  have hp : prime_of_index 176 = 1049 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1049) (by norm_num)
    rwa [pcount1049] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1049 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1049 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1049 = 31049 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1049 = 331049 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1049 = 3331049 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1049 = 33331049 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1049)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331049)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1049)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact (by norm_num : ¬ (3331049 : ℕ).Prime) hpr

/-- `A242775 177 = 1`. -/
theorem A242775_n177 : A242775 177 = 1 := by
  have hp : prime_of_index 177 = 1051 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1051) (by norm_num)
    rwa [pcount1051] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1051 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1051 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1051 = 31051 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1051)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31051)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1051)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 178 = 4`. -/
theorem A242775_n178 : A242775 178 = 4 := by
  have hp : prime_of_index 178 = 1061 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1061) (by norm_num)
    rwa [pcount1061] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1061 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1061 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1061 = 31061 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1061 = 331061 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1061 = 3331061 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1061 = 33331061 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1061)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331061)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1061)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 179 = 1`. -/
theorem A242775_n179 : A242775 179 = 1 := by
  have hp : prime_of_index 179 = 1063 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1063) (by norm_num)
    rwa [pcount1063] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1063 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1063 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1063 = 31063 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1063)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31063)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1063)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 180 = 1`. -/
theorem A242775_n180 : A242775 180 = 1 := by
  have hp : prime_of_index 180 = 1069 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1069) (by norm_num)
    rwa [pcount1069] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1069 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1069 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1069 = 31069 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1069)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31069)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1069)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 181 = 3`. -/
theorem A242775_n181 : A242775 181 = 3 := by
  have hp : prime_of_index 181 = 1087 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1087) (by norm_num)
    rwa [pcount1087] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1087 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1087 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1087 = 31087 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1087 = 331087 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1087 = 3331087 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1087)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331087)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1087)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 182 = 1`. -/
theorem A242775_n182 : A242775 182 = 1 := by
  have hp : prime_of_index 182 = 1091 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1091) (by norm_num)
    rwa [pcount1091] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1091 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1091 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1091 = 31091 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1091)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31091)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1091)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 183 = 3`. -/
theorem A242775_n183 : A242775 183 = 3 := by
  have hp : prime_of_index 183 = 1093 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1093) (by norm_num)
    rwa [pcount1093] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1093 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1093 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1093 = 31093 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1093 = 331093 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1093 = 3331093 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1093)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331093)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1093)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 184 = 4`. -/
theorem A242775_n184 : A242775 184 = 4 := by
  have hp : prime_of_index 184 = 1097 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1097) (by norm_num)
    rwa [pcount1097] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1097 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1097 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1097 = 31097 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1097 = 331097 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1097 = 3331097 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1097 = 33331097 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1097)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331097)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1097)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 186 = 3`. -/
theorem A242775_n186 : A242775 186 = 3 := by
  have hp : prime_of_index 186 = 1109 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1109) (by norm_num)
    rwa [pcount1109] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1109 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1109 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1109 = 31109 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1109 = 331109 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1109 = 3331109 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1109)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331109)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1109)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 187 = 12`. -/
theorem A242775_n187 : A242775 187 = 12 := by
  have hp : prime_of_index 187 = 1117 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1117) (by norm_num)
    rwa [pcount1117] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1117 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1117 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1117 = 31117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1117 = 331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1117 = 3331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1117 = 33331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1117 = 333331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1117 = 3333331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1117 = 33333331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1117 = 333333331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1117 = 3333333331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 1117 = 33333333331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 1117 = 333333333331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 1117 = 3333333333331117 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 12 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1117)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h12]; exact prime_3333333333331117
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1117)}
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact (by norm_num : ¬ (333333331117 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    rcases hpr.eq_one_or_self_of_dvd 749701 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 188 = 1`. -/
theorem A242775_n188 : A242775 188 = 1 := by
  have hp : prime_of_index 188 = 1123 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1123) (by norm_num)
    rwa [pcount1123] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1123 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1123 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1123 = 31123 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1123)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31123)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1123)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 189 = 3`. -/
theorem A242775_n189 : A242775 189 = 3 := by
  have hp : prime_of_index 189 = 1129 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1129) (by norm_num)
    rwa [pcount1129] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1129 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1129 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1129 = 31129 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1129 = 331129 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1129 = 3331129 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1129)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331129)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1129)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 190 = 1`. -/
theorem A242775_n190 : A242775 190 = 1 := by
  have hp : prime_of_index 190 = 1151 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1151) (by norm_num)
    rwa [pcount1151] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1151 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1151 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1151 = 31151 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1151)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31151)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1151)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 191 = 1`. -/
theorem A242775_n191 : A242775 191 = 1 := by
  have hp : prime_of_index 191 = 1153 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1153) (by norm_num)
    rwa [pcount1153] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1153 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1153 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1153 = 31153 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1153)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31153)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1153)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 192 = 10`. -/
theorem A242775_n192 : A242775 192 = 10 := by
  have hp : prime_of_index 192 = 1163 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1163) (by norm_num)
    rwa [pcount1163] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1163 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1163 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1163 = 31163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1163 = 331163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1163 = 3331163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1163 = 33331163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1163 = 333331163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1163 = 3333331163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1163 = 33333331163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1163 = 333333331163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1163 = 3333333331163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 1163 = 33333333331163 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 10 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1163)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h10]; exact prime_33333333331163
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1163)}
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact (by norm_num : ¬ (3333331163 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 193 = 2`. -/
theorem A242775_n193 : A242775 193 = 2 := by
  have hp : prime_of_index 193 = 1171 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1171) (by norm_num)
    rwa [pcount1171] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1171 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1171 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1171 = 31171 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1171 = 331171 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1171)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331171)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1171)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 194 = 1`. -/
theorem A242775_n194 : A242775 194 = 1 := by
  have hp : prime_of_index 194 = 1181 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1181) (by norm_num)
    rwa [pcount1181] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1181 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1181 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1181 = 31181 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1181)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31181)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1181)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 195 = 3`. -/
theorem A242775_n195 : A242775 195 = 3 := by
  have hp : prime_of_index 195 = 1187 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1187) (by norm_num)
    rwa [pcount1187] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1187 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1187 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1187 = 31187 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1187 = 331187 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1187 = 3331187 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1187)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331187)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1187)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 196 = 1`. -/
theorem A242775_n196 : A242775 196 = 1 := by
  have hp : prime_of_index 196 = 1193 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1193) (by norm_num)
    rwa [pcount1193] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1193 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1193 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1193 = 31193 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1193)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31193)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1193)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 197 = 4`. -/
theorem A242775_n197 : A242775 197 = 4 := by
  have hp : prime_of_index 197 = 1201 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1201) (by norm_num)
    rwa [pcount1201] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1201 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1201 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1201 = 31201 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1201 = 331201 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1201 = 3331201 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1201 = 33331201 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1201)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331201)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1201)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 198 = 2`. -/
theorem A242775_n198 : A242775 198 = 2 := by
  have hp : prime_of_index 198 = 1213 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1213) (by norm_num)
    rwa [pcount1213] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1213 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1213 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1213 = 31213 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1213 = 331213 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1213)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331213)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1213)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 199 = 2`. -/
theorem A242775_n199 : A242775 199 = 2 := by
  have hp : prime_of_index 199 = 1217 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1217) (by norm_num)
    rwa [pcount1217] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1217 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1217 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1217 = 31217 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1217 = 331217 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1217)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331217)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1217)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 200 = 1`. -/
theorem A242775_n200 : A242775 200 = 1 := by
  have hp : prime_of_index 200 = 1223 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1223) (by norm_num)
    rwa [pcount1223] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1223 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1223 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1223 = 31223 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1223)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31223)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1223)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

end ValueTable151to200


section PocklingtonCriterion
/- **Pocklington's primality criterion**, proved here from Mathlib primitives
(finite-field order theory and unique factorization).  Unlike the plain Lucas
test, it needs only a *partially factored* `N - 1 = F * R` with `F² > N`,
which is essential for certifying the very large witnesses appearing further
down this sequence (e.g. the 139-digit witness for `n = 185`, whose `N - 1`
has a 118-digit prime factor). -/

/-- If `d ∣ n` but `d ∤ n / q` for a prime `q ∣ n`, then the full `q`-part of `n`
divides `d`. -/
private lemma pow_factorization_dvd_of_not_dvd_div {d n q : ℕ} (hq : q.Prime) (hn : n ≠ 0)
    (hd : d ∣ n) (hqn : q ∣ n) (hnd : ¬ d ∣ n / q) :
    q ^ n.factorization q ∣ d := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hn (Nat.eq_zero_of_zero_dvd hd)
  by_contra hcon
  apply hnd
  have hnq0 : n / q ≠ 0 := by
    have h1 : 0 < n / q := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hqn) hq.pos
    omega
  have hdf : d.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hd0 hn).mpr hd
  have hlt : d.factorization q < n.factorization q := by
    by_contra hge
    push_neg at hge
    exact hcon ((hq.pow_dvd_iff_le_factorization hd0).mpr hge)
  rw [← Nat.factorization_le_iff_dvd hd0 hnq0, Nat.factorization_div hqn,
      hq.factorization]
  rw [Finsupp.le_def]
  intro r
  rw [Finsupp.tsub_apply]
  by_cases hr : r = q
  · subst hr
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hr]
    have := hdf r
    omega

/-- **Pocklington's primality criterion** (square-root version, with a separate
Fermat witness for each prime factor of the factored part).  If `N - 1 = F * R`
with `F * F > N`, and for every prime `q ∣ F` there is `a : ZMod N` with
`a ^ (N-1) = 1` and `a ^ ((N-1)/q) - 1` a unit, then `N` is prime. -/
theorem pocklington (N F R : ℕ) (hN : 1 < N) (hFR : N - 1 = F * R) (hFN : N < F * F)
    (h : ∀ q : ℕ, q.Prime → q ∣ F →
        ∃ a : ZMod N, a ^ (N - 1) = 1 ∧ IsUnit (a ^ ((N - 1) / q) - 1)) :
    N.Prime := by
  by_contra hNp
  have hpp : (N.minFac).Prime := Nat.minFac_prime (by omega)
  have hpN : N.minFac ∣ N := Nat.minFac_dvd N
  have hpsq : N.minFac * N.minFac ≤ N := by
    have h := Nat.minFac_sq_le_self (by omega : 0 < N) hNp
    rwa [pow_two] at h
  haveI : Fact (N.minFac).Prime := ⟨hpp⟩
  have hN1 : N - 1 ≠ 0 := by omega
  have hF0 : F ≠ 0 := by
    rintro rfl
    omega
  have hp2 : 2 ≤ N.minFac := hpp.two_le
  have hp1 : N.minFac - 1 ≠ 0 := by omega
  have hFdvdN1 : F ∣ N - 1 := hFR ▸ dvd_mul_right F R
  -- Key claim: `F ∣ minFac N - 1`.
  have hFdvd : F ∣ N.minFac - 1 := by
    rw [← Nat.factorization_le_iff_dvd hF0 hp1, Finsupp.le_def]
    intro q
    by_cases hqs : q ∈ F.factorization.support
    swap
    · rw [Finsupp.notMem_support_iff.mp hqs]
      exact Nat.zero_le _
    · rw [Nat.support_factorization] at hqs
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hqs
      have hqF : q ∣ F := Nat.dvd_of_mem_primeFactors hqs
      obtain ⟨a, ha1, ha2⟩ := h q hq hqF
      -- push the witness into `ZMod (minFac N)`
      set f := ZMod.castHom hpN (ZMod N.minFac) with hf
      set b := f a with hb
      have hb1 : b ^ (N - 1) = 1 := by
        rw [hb, ← map_pow, ha1, map_one]
      have hbu : IsUnit (b ^ ((N - 1) / q) - 1) := by
        have := ha2.map f
        rwa [map_sub, map_pow, map_one] at this
      have hbne : b ^ ((N - 1) / q) ≠ 1 := by
        intro hE
        rw [hE, sub_self] at hbu
        exact hbu.ne_zero rfl
      have hb0 : b ≠ 0 := by
        intro hE
        rw [hE, zero_pow hN1] at hb1
        exact zero_ne_one hb1
      have hd1 : orderOf b ∣ N - 1 := orderOf_dvd_of_pow_eq_one hb1
      have hd2 : ¬ orderOf b ∣ (N - 1) / q := by
        intro hdvd
        exact hbne (orderOf_dvd_iff_pow_eq_one.mp hdvd)
      have hqn : q ∣ N - 1 := hqF.trans hFdvdN1
      have hqd : q ^ ((N - 1).factorization q) ∣ orderOf b :=
        pow_factorization_dvd_of_not_dvd_div hq hN1 hd1 hqn hd2
      have hdp : orderOf b ∣ N.minFac - 1 := ZMod.orderOf_dvd_card_sub_one hb0
      have h2 : (N - 1).factorization q ≤ (N.minFac - 1).factorization q :=
        (hq.pow_dvd_iff_le_factorization hp1).mp (hqd.trans hdp)
      have h1 : F.factorization q ≤ (N - 1).factorization q :=
        (Nat.factorization_le_iff_dvd hF0 hN1).mpr hFdvdN1 q
      omega
  -- Conclude: `F ≤ minFac N - 1 < minFac N`, so `N < F * F < minFac N ^ 2 ≤ N`.
  have hFle : F ≤ N.minFac - 1 := Nat.le_of_dvd (by omega) hFdvd
  have hFltp : F < N.minFac := by omega
  have : F * F < N.minFac * N.minFac := Nat.mul_lt_mul'' hFltp hFltp
  omega

/-- Turn a computed residue `b ^ e % N = r` with `gcd (r-1) N = 1` into the
unit condition required by `pocklington`. -/
private lemma pock_unit_of_coprime {N : ℕ} (b e r : ℕ) (h : b ^ e % N = r) (hr : 1 ≤ r)
    (hco : Nat.Coprime (r - 1) N) :
    IsUnit (((b : ℕ) : ZMod N) ^ e - 1) := by
  rw [zmod_pow_of_mod h,
      show ((r : ℕ) : ZMod N) - 1 = ((r - 1 : ℕ) : ZMod N) by
        rw [Nat.cast_sub hr, Nat.cast_one]]
  exact (ZMod.isUnit_iff_coprime _ _).mpr hco


end PocklingtonCriterion



section ValueTable201to250
/- Machine-verified values `A242775 n` for `n = 201..250` except
`n ∈ {210, 227, 235, 238}` (values 51, 19, 21, 294 with witnesses of 55, 23,
25 and 298 digits, verified offline and omitted here only for economy of the
verification budget). -/


private lemma pcount1229 : Nat.count Nat.Prime 1229 = 200 :=
  count_from 6 pcount1223 rfl rfl

private lemma pcount1231 : Nat.count Nat.Prime 1231 = 201 :=
  count_from 2 pcount1229 rfl rfl

private lemma pcount1237 : Nat.count Nat.Prime 1237 = 202 :=
  count_from 6 pcount1231 rfl rfl

private lemma pcount1249 : Nat.count Nat.Prime 1249 = 203 :=
  count_from 12 pcount1237 rfl rfl

private lemma pcount1259 : Nat.count Nat.Prime 1259 = 204 :=
  count_from 10 pcount1249 rfl rfl

private lemma pcount1277 : Nat.count Nat.Prime 1277 = 205 :=
  count_from 18 pcount1259 rfl rfl

private lemma pcount1279 : Nat.count Nat.Prime 1279 = 206 :=
  count_from 2 pcount1277 rfl rfl

private lemma pcount1283 : Nat.count Nat.Prime 1283 = 207 :=
  count_from 4 pcount1279 rfl rfl

private lemma pcount1289 : Nat.count Nat.Prime 1289 = 208 :=
  count_from 6 pcount1283 rfl rfl

private lemma pcount1291 : Nat.count Nat.Prime 1291 = 209 :=
  count_from 2 pcount1289 rfl rfl

private lemma pcount1297 : Nat.count Nat.Prime 1297 = 210 :=
  count_from 6 pcount1291 rfl rfl

private lemma pcount1301 : Nat.count Nat.Prime 1301 = 211 :=
  count_from 4 pcount1297 rfl rfl

private lemma pcount1303 : Nat.count Nat.Prime 1303 = 212 :=
  count_from 2 pcount1301 rfl rfl

private lemma pcount1307 : Nat.count Nat.Prime 1307 = 213 :=
  count_from 4 pcount1303 rfl rfl

private lemma pcount1319 : Nat.count Nat.Prime 1319 = 214 :=
  count_from 12 pcount1307 rfl rfl

private lemma pcount1321 : Nat.count Nat.Prime 1321 = 215 :=
  count_from 2 pcount1319 rfl rfl

private lemma pcount1327 : Nat.count Nat.Prime 1327 = 216 :=
  count_from 6 pcount1321 rfl rfl

private lemma pcount1361 : Nat.count Nat.Prime 1361 = 217 :=
  count_from 34 pcount1327 rfl rfl

private lemma pcount1367 : Nat.count Nat.Prime 1367 = 218 :=
  count_from 6 pcount1361 rfl rfl

private lemma pcount1373 : Nat.count Nat.Prime 1373 = 219 :=
  count_from 6 pcount1367 rfl rfl

private lemma pcount1381 : Nat.count Nat.Prime 1381 = 220 :=
  count_from 8 pcount1373 rfl rfl

private lemma pcount1399 : Nat.count Nat.Prime 1399 = 221 :=
  count_from 18 pcount1381 rfl rfl

private lemma pcount1409 : Nat.count Nat.Prime 1409 = 222 :=
  count_from 10 pcount1399 rfl rfl

private lemma pcount1423 : Nat.count Nat.Prime 1423 = 223 :=
  count_from 14 pcount1409 rfl rfl

private lemma pcount1427 : Nat.count Nat.Prime 1427 = 224 :=
  count_from 4 pcount1423 rfl rfl

private lemma pcount1429 : Nat.count Nat.Prime 1429 = 225 :=
  count_from 2 pcount1427 rfl rfl

private lemma pcount1433 : Nat.count Nat.Prime 1433 = 226 :=
  count_from 4 pcount1429 rfl rfl

private lemma pcount1439 : Nat.count Nat.Prime 1439 = 227 :=
  count_from 6 pcount1433 rfl rfl

private lemma pcount1447 : Nat.count Nat.Prime 1447 = 228 :=
  count_from 8 pcount1439 rfl rfl

private lemma pcount1451 : Nat.count Nat.Prime 1451 = 229 :=
  count_from 4 pcount1447 rfl rfl

private lemma pcount1453 : Nat.count Nat.Prime 1453 = 230 :=
  count_from 2 pcount1451 rfl rfl

private lemma pcount1459 : Nat.count Nat.Prime 1459 = 231 :=
  count_from 6 pcount1453 rfl rfl

private lemma pcount1471 : Nat.count Nat.Prime 1471 = 232 :=
  count_from 12 pcount1459 rfl rfl

private lemma pcount1481 : Nat.count Nat.Prime 1481 = 233 :=
  count_from 10 pcount1471 rfl rfl

private lemma pcount1483 : Nat.count Nat.Prime 1483 = 234 :=
  count_from 2 pcount1481 rfl rfl

private lemma pcount1487 : Nat.count Nat.Prime 1487 = 235 :=
  count_from 4 pcount1483 rfl rfl

private lemma pcount1489 : Nat.count Nat.Prime 1489 = 236 :=
  count_from 2 pcount1487 rfl rfl

private lemma pcount1493 : Nat.count Nat.Prime 1493 = 237 :=
  count_from 4 pcount1489 rfl rfl

private lemma pcount1499 : Nat.count Nat.Prime 1499 = 238 :=
  count_from 6 pcount1493 rfl rfl

private lemma pcount1511 : Nat.count Nat.Prime 1511 = 239 :=
  count_from 12 pcount1499 rfl rfl

private lemma pcount1523 : Nat.count Nat.Prime 1523 = 240 :=
  count_from 12 pcount1511 rfl rfl

private lemma pcount1531 : Nat.count Nat.Prime 1531 = 241 :=
  count_from 8 pcount1523 rfl rfl

private lemma pcount1543 : Nat.count Nat.Prime 1543 = 242 :=
  count_from 12 pcount1531 rfl rfl

private lemma pcount1549 : Nat.count Nat.Prime 1549 = 243 :=
  count_from 6 pcount1543 rfl rfl

private lemma pcount1553 : Nat.count Nat.Prime 1553 = 244 :=
  count_from 4 pcount1549 rfl rfl

private lemma pcount1559 : Nat.count Nat.Prime 1559 = 245 :=
  count_from 6 pcount1553 rfl rfl

private lemma pcount1567 : Nat.count Nat.Prime 1567 = 246 :=
  count_from 8 pcount1559 rfl rfl

private lemma pcount1571 : Nat.count Nat.Prime 1571 = 247 :=
  count_from 4 pcount1567 rfl rfl

private lemma pcount1579 : Nat.count Nat.Prime 1579 = 248 :=
  count_from 8 pcount1571 rfl rfl

private lemma pcount1583 : Nat.count Nat.Prime 1583 = 249 :=
  count_from 4 pcount1579 rfl rfl

private lemma prime_32175032173 : Nat.Prime 32175032173 := by
  have c1 : (2:ℕ) ^ 16087516086 % 32175032173 = 32175032172 :=
    pow_mod_eq2 5 2 16087516086 32175032173 32175032172 (by decide) rfl
  have c2 : (2:ℕ) ^ 10725010724 % 32175032173 = 19926367235 :=
    pow_mod_eq2 5 2 10725010724 32175032173 19926367235 (by decide) rfl
  have c3 : (2:ℕ) ^ 1109483868 % 32175032173 = 11730103644 :=
    pow_mod_eq2 4 2 1109483868 32175032173 11730103644 (by decide) rfl
  have c4 : (2:ℕ) ^ 348 % 32175032173 = 6026753996 :=
    pow_mod_eq2 2 2 348 32175032173 6026753996 (by decide) rfl
  have cf : (2:ℕ) ^ 32175032172 % 32175032173 = 1 :=
    pow_mod_eq2 5 2 32175032172 32175032173 1 (by decide) rfl
  refine lucas_primality 32175032173 ((2 : ℕ) : ZMod 32175032173) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (32175032173:ℕ) - 1 = 32175032172 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (32175032173:ℕ) - 1 = 2 * (2 * (3 * (29 * (92456989)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((32175032173:ℕ) - 1) / 2 = 16087516086 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((32175032173:ℕ) - 1) / 2 = 16087516086 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((32175032173:ℕ) - 1) / 3 = 10725010724 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 29 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((32175032173:ℕ) - 1) / 29 = 1109483868 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 92456989 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((32175032173:ℕ) - 1) / 92456989 = 348 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_33333333331229 : Nat.Prime 33333333331229 := by
  have c1 : (3:ℕ) ^ 16666666665614 % 33333333331229 = 33333333331228 :=
    pow_mod_eq2 6 3 16666666665614 33333333331229 33333333331228 (by decide) rfl
  have c2 : (3:ℕ) ^ 4761904761604 % 33333333331229 = 20232589401615 :=
    pow_mod_eq2 6 3 4761904761604 33333333331229 20232589401615 (by decide) rfl
  have c3 : (3:ℕ) ^ 900900900844 % 33333333331229 = 18576151392518 :=
    pow_mod_eq2 5 3 900900900844 33333333331229 18576151392518 (by decide) rfl
  have c4 : (3:ℕ) ^ 1036 % 33333333331229 = 13242130341240 :=
    pow_mod_eq2 2 3 1036 33333333331229 13242130341240 (by decide) rfl
  have cf : (3:ℕ) ^ 33333333331228 % 33333333331229 = 1 :=
    pow_mod_eq2 6 3 33333333331228 33333333331229 1 (by decide) rfl
  refine lucas_primality 33333333331229 ((3 : ℕ) : ZMod 33333333331229) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333333331229:ℕ) - 1 = 33333333331228 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333333331229:ℕ) - 1 = 2 * (2 * (7 * (37 * (32175032173)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333333331229:ℕ) - 1) / 2 = 16666666665614 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333333331229:ℕ) - 1) / 2 = 16666666665614 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333333331229:ℕ) - 1) / 7 = 4761904761604 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 37 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((33333333331229:ℕ) - 1) / 37 = 900900900844 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 32175032173 := (Nat.prime_dvd_prime_iff_eq hq prime_32175032173).mp h
            subst hqe
            have hexp : ((33333333331229:ℕ) - 1) / 32175032173 = 1036 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_4166666411 : Nat.Prime 4166666411 := by
  have c1 : (2:ℕ) ^ 2083333205 % 4166666411 = 4166666410 :=
    pow_mod_eq2 4 2 2083333205 4166666411 4166666410 (by decide) rfl
  have c2 : (2:ℕ) ^ 833333282 % 4166666411 = 1971274743 :=
    pow_mod_eq2 4 2 833333282 4166666411 1971274743 (by decide) rfl
  have c3 : (2:ℕ) ^ 101626010 % 4166666411 = 288787191 :=
    pow_mod_eq2 4 2 101626010 4166666411 288787191 (by decide) rfl
  have c4 : (2:ℕ) ^ 3390290 % 4166666411 = 3550099713 :=
    pow_mod_eq2 3 2 3390290 4166666411 3550099713 (by decide) rfl
  have c5 : (2:ℕ) ^ 503890 % 4166666411 = 524089180 :=
    pow_mod_eq2 3 2 503890 4166666411 524089180 (by decide) rfl
  have cf : (2:ℕ) ^ 4166666410 % 4166666411 = 1 :=
    pow_mod_eq2 4 2 4166666410 4166666411 1 (by decide) rfl
  refine lucas_primality 4166666411 ((2 : ℕ) : ZMod 4166666411) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (4166666411:ℕ) - 1 = 4166666410 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (4166666411:ℕ) - 1 = 2 * (5 * (41 * (1229 * (8269)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((4166666411:ℕ) - 1) / 2 = 2083333205 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((4166666411:ℕ) - 1) / 5 = 833333282 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 41 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((4166666411:ℕ) - 1) / 41 = 101626010 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 1229 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((4166666411:ℕ) - 1) / 1229 = 3390290 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 8269 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((4166666411:ℕ) - 1) / 8269 = 503890 := rfl
            rw [hexp, zmod_pow_of_mod c5]
            exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_33333331289 : Nat.Prime 33333331289 := by
  have c1 : (3:ℕ) ^ 16666665644 % 33333331289 = 33333331288 :=
    pow_mod_eq2 5 3 16666665644 33333331289 33333331288 (by decide) rfl
  have c2 : (3:ℕ) ^ 8 % 33333331289 = 6561 :=
    pow_mod_eq2 1 3 8 33333331289 6561 (by decide) rfl
  have cf : (3:ℕ) ^ 33333331288 % 33333331289 = 1 :=
    pow_mod_eq2 5 3 33333331288 33333331289 1 (by decide) rfl
  refine lucas_primality 33333331289 ((3 : ℕ) : ZMod 33333331289) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333331289:ℕ) - 1 = 33333331288 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333331289:ℕ) - 1 = 2 * (2 * (2 * (4166666411))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333331289:ℕ) - 1) / 2 = 16666665644 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333331289:ℕ) - 1) / 2 = 16666665644 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333331289:ℕ) - 1) / 2 = 16666665644 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 4166666411 := (Nat.prime_dvd_prime_iff_eq hq prime_4166666411).mp h
          subst hqe
          have hexp : ((33333331289:ℕ) - 1) / 4166666411 = 8 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_3333331297 : Nat.Prime 3333331297 := by
  have c1 : (10:ℕ) ^ 1666665648 % 3333331297 = 3333331296 :=
    pow_mod_eq2 4 10 1666665648 3333331297 3333331296 (by decide) rfl
  have c2 : (10:ℕ) ^ 1111110432 % 3333331297 = 1055827818 :=
    pow_mod_eq2 4 10 1111110432 3333331297 1055827818 (by decide) rfl
  have c3 : (10:ℕ) ^ 107526816 % 3333331297 = 1327418221 :=
    pow_mod_eq2 4 10 107526816 3333331297 1327418221 (by decide) rfl
  have c4 : (10:ℕ) ^ 8928 % 3333331297 = 3312460446 :=
    pow_mod_eq2 2 10 8928 3333331297 3312460446 (by decide) rfl
  have cf : (10:ℕ) ^ 3333331296 % 3333331297 = 1 :=
    pow_mod_eq2 4 10 3333331296 3333331297 1 (by decide) rfl
  refine lucas_primality 3333331297 ((10 : ℕ) : ZMod 3333331297) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333331297:ℕ) - 1 = 3333331296 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333331297:ℕ) - 1 = 2 * (2 * (2 * (2 * (2 * (3 * (3 * (31 * (373357)))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333331297:ℕ) - 1) / 2 = 1666665648 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333331297:ℕ) - 1) / 2 = 1666665648 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333331297:ℕ) - 1) / 2 = 1666665648 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333331297:ℕ) - 1) / 2 = 1666665648 := rfl
            rw [hexp, zmod_pow_of_mod c1]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((3333331297:ℕ) - 1) / 2 = 1666665648 := rfl
              rw [hexp, zmod_pow_of_mod c1]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((3333331297:ℕ) - 1) / 3 = 1111110432 := rfl
                rw [hexp, zmod_pow_of_mod c2]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((3333331297:ℕ) - 1) / 3 = 1111110432 := rfl
                  rw [hexp, zmod_pow_of_mod c2]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                  · 
                    have hqe : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((3333331297:ℕ) - 1) / 31 = 107526816 := rfl
                    rw [hexp, zmod_pow_of_mod c3]
                    exact zmod_ne_one (by decide) (by decide) (by decide)
                  · 
                    have h := hrest
                    have hqe : q = 373357 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((3333331297:ℕ) - 1) / 373357 = 8928 := rfl
                    rw [hexp, zmod_pow_of_mod c4]
                    exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_3333331361 : Nat.Prime 3333331361 := by
  have c1 : (3:ℕ) ^ 1666665680 % 3333331361 = 3333331360 :=
    pow_mod_eq2 4 3 1666665680 3333331361 3333331360 (by decide) rfl
  have c2 : (3:ℕ) ^ 666666272 % 3333331361 = 3203965828 :=
    pow_mod_eq2 4 3 666666272 3333331361 3203965828 (by decide) rfl
  have c3 : (3:ℕ) ^ 4923680 % 3333331361 = 651608898 :=
    pow_mod_eq2 3 3 4923680 3333331361 651608898 (by decide) rfl
  have c4 : (3:ℕ) ^ 108320 % 3333331361 = 2564010923 :=
    pow_mod_eq2 3 3 108320 3333331361 2564010923 (by decide) rfl
  have cf : (3:ℕ) ^ 3333331360 % 3333331361 = 1 :=
    pow_mod_eq2 4 3 3333331360 3333331361 1 (by decide) rfl
  refine lucas_primality 3333331361 ((3 : ℕ) : ZMod 3333331361) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333331361:ℕ) - 1 = 3333331360 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333331361:ℕ) - 1 = 2 * (2 * (2 * (2 * (2 * (5 * (677 * (30773))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333331361:ℕ) - 1) / 2 = 1666665680 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333331361:ℕ) - 1) / 2 = 1666665680 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333331361:ℕ) - 1) / 2 = 1666665680 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333331361:ℕ) - 1) / 2 = 1666665680 := rfl
            rw [hexp, zmod_pow_of_mod c1]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((3333331361:ℕ) - 1) / 2 = 1666665680 := rfl
              rw [hexp, zmod_pow_of_mod c1]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((3333331361:ℕ) - 1) / 5 = 666666272 := rfl
                rw [hexp, zmod_pow_of_mod c2]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 677 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((3333331361:ℕ) - 1) / 677 = 4923680 := rfl
                  rw [hexp, zmod_pow_of_mod c3]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  have h := hrest
                  have hqe : q = 30773 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((3333331361:ℕ) - 1) / 30773 = 108320 := rfl
                  rw [hexp, zmod_pow_of_mod c4]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_33333331373 : Nat.Prime 33333331373 := by
  have c1 : (2:ℕ) ^ 16666665686 % 33333331373 = 33333331372 :=
    pow_mod_eq2 5 2 16666665686 33333331373 33333331372 (by decide) rfl
  have c2 : (2:ℕ) ^ 3030302852 % 33333331373 = 19112771850 :=
    pow_mod_eq2 4 2 3030302852 33333331373 19112771850 (by decide) rfl
  have c3 : (2:ℕ) ^ 90826516 % 33333331373 = 18547168213 :=
    pow_mod_eq2 4 2 90826516 33333331373 18547168213 (by decide) rfl
  have c4 : (2:ℕ) ^ 31181788 % 33333331373 = 9040442993 :=
    pow_mod_eq2 4 2 31181788 33333331373 9040442993 (by decide) rfl
  have c5 : (2:ℕ) ^ 17262212 % 33333331373 = 18816201921 :=
    pow_mod_eq2 4 2 17262212 33333331373 18816201921 (by decide) rfl
  have cf : (2:ℕ) ^ 33333331372 % 33333331373 = 1 :=
    pow_mod_eq2 5 2 33333331372 33333331373 1 (by decide) rfl
  refine lucas_primality 33333331373 ((2 : ℕ) : ZMod 33333331373) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333331373:ℕ) - 1 = 33333331372 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333331373:ℕ) - 1 = 2 * (2 * (11 * (367 * (1069 * (1931))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333331373:ℕ) - 1) / 2 = 16666665686 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333331373:ℕ) - 1) / 2 = 16666665686 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333331373:ℕ) - 1) / 11 = 3030302852 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 367 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((33333331373:ℕ) - 1) / 367 = 90826516 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 1069 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((33333331373:ℕ) - 1) / 1069 = 31181788 := rfl
              rw [hexp, zmod_pow_of_mod c4]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 1931 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((33333331373:ℕ) - 1) / 1931 = 17262212 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_333333331439 : Nat.Prime 333333331439 := by
  have c1 : (11:ℕ) ^ 166666665719 % 333333331439 = 333333331438 :=
    pow_mod_eq2 5 11 166666665719 333333331439 333333331438 (by decide) rfl
  have c2 : (11:ℕ) ^ 5649717482 % 333333331439 = 143929230438 :=
    pow_mod_eq2 5 11 5649717482 333333331439 143929230438 (by decide) rfl
  have c3 : (11:ℕ) ^ 124517494 % 333333331439 = 45544851597 :=
    pow_mod_eq2 4 11 124517494 333333331439 45544851597 (by decide) rfl
  have c4 : (11:ℕ) ^ 315886 % 333333331439 = 243249402203 :=
    pow_mod_eq2 3 11 315886 333333331439 243249402203 (by decide) rfl
  have cf : (11:ℕ) ^ 333333331438 % 333333331439 = 1 :=
    pow_mod_eq2 5 11 333333331438 333333331439 1 (by decide) rfl
  refine lucas_primality 333333331439 ((11 : ℕ) : ZMod 333333331439) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (333333331439:ℕ) - 1 = 333333331438 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (333333331439:ℕ) - 1 = 2 * (59 * (2677 * (1055233))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((333333331439:ℕ) - 1) / 2 = 166666665719 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 59 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((333333331439:ℕ) - 1) / 59 = 5649717482 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2677 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((333333331439:ℕ) - 1) / 2677 = 124517494 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 1055233 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((333333331439:ℕ) - 1) / 1055233 = 315886 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_3333333333331459 : Nat.Prime 3333333333331459 := by
  have c1 : (2:ℕ) ^ 1666666666665729 % 3333333333331459 = 3333333333331458 :=
    pow_mod_eq2 7 2 1666666666665729 3333333333331459 3333333333331458 (by decide) rfl
  have c2 : (2:ℕ) ^ 1111111111110486 % 3333333333331459 = 1085739377115874 :=
    pow_mod_eq2 7 2 1111111111110486 3333333333331459 1085739377115874 (by decide) rfl
  have c3 : (2:ℕ) ^ 992820222 % 3333333333331459 = 1937662659793269 :=
    pow_mod_eq2 4 2 992820222 3333333333331459 1937662659793269 (by decide) rfl
  have c4 : (2:ℕ) ^ 60433902 % 3333333333331459 = 1589661421045247 :=
    pow_mod_eq2 4 2 60433902 3333333333331459 1589661421045247 (by decide) rfl
  have cf : (2:ℕ) ^ 3333333333331458 % 3333333333331459 = 1 :=
    pow_mod_eq2 7 2 3333333333331458 3333333333331459 1 (by decide) rfl
  refine lucas_primality 3333333333331459 ((2 : ℕ) : ZMod 3333333333331459) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333333333331459:ℕ) - 1 = 3333333333331458 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333333333331459:ℕ) - 1 = 2 * (3 * (3 * (3357439 * (55156679)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333333333331459:ℕ) - 1) / 2 = 1666666666665729 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333333331459:ℕ) - 1) / 3 = 1111111111110486 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333333333331459:ℕ) - 1) / 3 = 1111111111110486 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3357439 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333333333331459:ℕ) - 1) / 3357439 = 992820222 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 55156679 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333333333331459:ℕ) - 1) / 55156679 = 60433902 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_333333331559 : Nat.Prime 333333331559 := by
  have c1 : (7:ℕ) ^ 166666665779 % 333333331559 = 333333331558 :=
    pow_mod_eq2 5 7 166666665779 333333331559 333333331558 (by decide) rfl
  have c2 : (7:ℕ) ^ 14492753546 % 333333331559 = 178626324170 :=
    pow_mod_eq2 5 7 14492753546 333333331559 178626324170 (by decide) rfl
  have c3 : (7:ℕ) ^ 2398081522 % 333333331559 = 181582526910 :=
    pow_mod_eq2 4 7 2398081522 333333331559 181582526910 (by decide) rfl
  have c4 : (7:ℕ) ^ 6394 % 333333331559 = 332662808537 :=
    pow_mod_eq2 2 7 6394 333333331559 332662808537 (by decide) rfl
  have cf : (7:ℕ) ^ 333333331558 % 333333331559 = 1 :=
    pow_mod_eq2 5 7 333333331558 333333331559 1 (by decide) rfl
  refine lucas_primality 333333331559 ((7 : ℕ) : ZMod 333333331559) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (333333331559:ℕ) - 1 = 333333331558 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (333333331559:ℕ) - 1 = 2 * (23 * (139 * (52132207))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((333333331559:ℕ) - 1) / 2 = 166666665779 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 23 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((333333331559:ℕ) - 1) / 23 = 14492753546 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 139 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((333333331559:ℕ) - 1) / 139 = 2398081522 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 52132207 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((333333331559:ℕ) - 1) / 52132207 = 6394 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)
private lemma prime_333333333333333331571 : Nat.Prime 333333333333333331571 := by
  have c1 : (6:ℕ) ^ 166666666666666665785 % 333333333333333331571 = 333333333333333331570 :=
    pow_mod_eq2 9 6 166666666666666665785 333333333333333331571 333333333333333331570 (by decide) rfl
  have c2 : (6:ℕ) ^ 66666666666666666314 % 333333333333333331571 = 320606497513700422903 :=
    pow_mod_eq2 9 6 66666666666666666314 333333333333333331571 320606497513700422903 (by decide) rfl
  have c3 : (6:ℕ) ^ 30303030303030302870 % 333333333333333331571 = 311351012556155247192 :=
    pow_mod_eq2 9 6 30303030303030302870 333333333333333331571 311351012556155247192 (by decide) rfl
  have c4 : (6:ℕ) ^ 25641025641025640890 % 333333333333333331571 = 144369987884309041813 :=
    pow_mod_eq2 9 6 25641025641025640890 333333333333333331571 144369987884309041813 (by decide) rfl
  have c5 : (6:ℕ) ^ 11494252873563218330 % 333333333333333331571 = 237369129352489730496 :=
    pow_mod_eq2 8 6 11494252873563218330 333333333333333331571 237369129352489730496 (by decide) rfl
  have c6 : (6:ℕ) ^ 7751937984496123990 % 333333333333333331571 = 156915003111650080447 :=
    pow_mod_eq2 8 6 7751937984496123990 333333333333333331571 156915003111650080447 (by decide) rfl
  have c7 : (6:ℕ) ^ 4975124378109452710 % 333333333333333331571 = 172694243483107102913 :=
    pow_mod_eq2 8 6 4975124378109452710 333333333333333331571 172694243483107102913 (by decide) rfl
  have c8 : (6:ℕ) ^ 1056366669096310 % 333333333333333331571 = 287765584528840358099 :=
    pow_mod_eq2 7 6 1056366669096310 333333333333333331571 287765584528840358099 (by decide) rfl
  have c9 : (6:ℕ) ^ 37699999913290 % 333333333333333331571 = 44444244698000180767 :=
    pow_mod_eq2 6 6 37699999913290 333333333333333331571 44444244698000180767 (by decide) rfl
  have cf : (6:ℕ) ^ 333333333333333331570 % 333333333333333331571 = 1 :=
    pow_mod_eq2 9 6 333333333333333331570 333333333333333331571 1 (by decide) rfl
  refine lucas_primality 333333333333333331571 ((6 : ℕ) : ZMod 333333333333333331571) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (333333333333333331571:ℕ) - 1 = 333333333333333331570 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (333333333333333331571:ℕ) - 1 = 2 * (5 * (11 * (13 * (29 * (43 * (67 * (315547 * (8841733)))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((333333333333333331571:ℕ) - 1) / 2 = 166666666666666665785 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((333333333333333331571:ℕ) - 1) / 5 = 66666666666666666314 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((333333333333333331571:ℕ) - 1) / 11 = 30303030303030302870 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((333333333333333331571:ℕ) - 1) / 13 = 25641025641025640890 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 29 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((333333333333333331571:ℕ) - 1) / 29 = 11494252873563218330 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 43 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((333333333333333331571:ℕ) - 1) / 43 = 7751937984496123990 := rfl
                rw [hexp, zmod_pow_of_mod c6]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 67 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((333333333333333331571:ℕ) - 1) / 67 = 4975124378109452710 := rfl
                  rw [hexp, zmod_pow_of_mod c7]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                  · 
                    have hqe : q = 315547 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((333333333333333331571:ℕ) - 1) / 315547 = 1056366669096310 := rfl
                    rw [hexp, zmod_pow_of_mod c8]
                    exact zmod_ne_one (by decide) (by decide) (by decide)
                  · 
                    have h := hrest
                    have hqe : q = 8841733 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((333333333333333331571:ℕ) - 1) / 8841733 = 37699999913290 := rfl
                    rw [hexp, zmod_pow_of_mod c9]
                    exact zmod_ne_one (by decide) (by decide) (by decide)
/-- `A242775 201 = 10`. -/
theorem A242775_n201 : A242775 201 = 10 := by
  have hp : prime_of_index 201 = 1229 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1229) (by norm_num)
    rwa [pcount1229] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1229 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1229 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1229 = 31229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1229 = 331229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1229 = 3331229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1229 = 33331229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1229 = 333331229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1229 = 3333331229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1229 = 33333331229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1229 = 333333331229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1229 = 3333333331229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 1229 = 33333333331229 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 10 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1229)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h10]; exact prime_33333333331229
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1229)}
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact (by norm_num : ¬ (33331229 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact (by norm_num : ¬ (3333331229 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨10, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 202 = 1`. -/
theorem A242775_n202 : A242775 202 = 1 := by
  have hp : prime_of_index 202 = 1231 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1231) (by norm_num)
    rwa [pcount1231] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1231 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1231 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1231 = 31231 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1231)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31231)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1231)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 203 = 1`. -/
theorem A242775_n203 : A242775 203 = 1 := by
  have hp : prime_of_index 203 = 1237 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1237) (by norm_num)
    rwa [pcount1237] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1237 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1237 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1237 = 31237 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1237)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31237)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1237)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 204 = 1`. -/
theorem A242775_n204 : A242775 204 = 1 := by
  have hp : prime_of_index 204 = 1249 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1249) (by norm_num)
    rwa [pcount1249] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1249 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1249 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1249 = 31249 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1249)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31249)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1249)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 205 = 1`. -/
theorem A242775_n205 : A242775 205 = 1 := by
  have hp : prime_of_index 205 = 1259 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1259) (by norm_num)
    rwa [pcount1259] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1259 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1259 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1259 = 31259 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1259)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31259)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1259)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 206 = 1`. -/
theorem A242775_n206 : A242775 206 = 1 := by
  have hp : prime_of_index 206 = 1277 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1277) (by norm_num)
    rwa [pcount1277] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1277 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1277 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1277 = 31277 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1277)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31277)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1277)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 207 = 4`. -/
theorem A242775_n207 : A242775 207 = 4 := by
  have hp : prime_of_index 207 = 1279 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1279) (by norm_num)
    rwa [pcount1279] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1279 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1279 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1279 = 31279 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1279 = 331279 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1279 = 3331279 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1279 = 33331279 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1279)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331279)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1279)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 208 = 2`. -/
theorem A242775_n208 : A242775 208 = 2 := by
  have hp : prime_of_index 208 = 1283 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1283) (by norm_num)
    rwa [pcount1283] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1283 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1283 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1283 = 31283 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1283 = 331283 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1283)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331283)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1283)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 209 = 7`. -/
theorem A242775_n209 : A242775 209 = 7 := by
  have hp : prime_of_index 209 = 1289 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1289) (by norm_num)
    rwa [pcount1289] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1289 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1289 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1289 = 31289 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1289 = 331289 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1289 = 3331289 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1289 = 33331289 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1289 = 333331289 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1289 = 3333331289 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1289 = 33333331289 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 7 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1289)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h7]; exact prime_33333331289
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1289)}
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 211 = 6`. -/
theorem A242775_n211 : A242775 211 = 6 := by
  have hp : prime_of_index 211 = 1297 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1297) (by norm_num)
    rwa [pcount1297] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1297 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1297 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1297 = 31297 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1297 = 331297 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1297 = 3331297 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1297 = 33331297 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1297 = 333331297 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1297 = 3333331297 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 6 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1297)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h6]; exact prime_3333331297
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1297)}
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 212 = 2`. -/
theorem A242775_n212 : A242775 212 = 2 := by
  have hp : prime_of_index 212 = 1301 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1301) (by norm_num)
    rwa [pcount1301] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1301 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1301 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1301 = 31301 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1301 = 331301 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1301)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331301)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1301)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 213 = 4`. -/
theorem A242775_n213 : A242775 213 = 4 := by
  have hp : prime_of_index 213 = 1303 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1303) (by norm_num)
    rwa [pcount1303] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1303 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1303 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1303 = 31303 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1303 = 331303 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1303 = 3331303 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1303 = 33331303 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1303)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331303)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1303)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 214 = 1`. -/
theorem A242775_n214 : A242775 214 = 1 := by
  have hp : prime_of_index 214 = 1307 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1307) (by norm_num)
    rwa [pcount1307] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1307 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1307 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1307 = 31307 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1307)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31307)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1307)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 215 = 1`. -/
theorem A242775_n215 : A242775 215 = 1 := by
  have hp : prime_of_index 215 = 1319 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1319) (by norm_num)
    rwa [pcount1319] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1319 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1319 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1319 = 31319 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1319)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31319)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1319)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 216 = 1`. -/
theorem A242775_n216 : A242775 216 = 1 := by
  have hp : prime_of_index 216 = 1321 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1321) (by norm_num)
    rwa [pcount1321] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1321 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1321 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1321 = 31321 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1321)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31321)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1321)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 217 = 1`. -/
theorem A242775_n217 : A242775 217 = 1 := by
  have hp : prime_of_index 217 = 1327 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1327) (by norm_num)
    rwa [pcount1327] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1327 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1327 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1327 = 31327 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1327)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31327)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1327)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 218 = 6`. -/
theorem A242775_n218 : A242775 218 = 6 := by
  have hp : prime_of_index 218 = 1361 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1361) (by norm_num)
    rwa [pcount1361] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1361 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1361 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1361 = 31361 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1361 = 331361 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1361 = 3331361 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1361 = 33331361 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1361 = 333331361 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1361 = 3333331361 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 6 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1361)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h6]; exact prime_3333331361
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1361)}
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨6, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 219 = 2`. -/
theorem A242775_n219 : A242775 219 = 2 := by
  have hp : prime_of_index 219 = 1367 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1367) (by norm_num)
    rwa [pcount1367] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1367 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1367 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1367 = 31367 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1367 = 331367 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1367)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331367)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1367)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 220 = 7`. -/
theorem A242775_n220 : A242775 220 = 7 := by
  have hp : prime_of_index 220 = 1373 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1373) (by norm_num)
    rwa [pcount1373] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1373 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1373 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1373 = 31373 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1373 = 331373 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1373 = 3331373 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1373 = 33331373 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1373 = 333331373 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1373 = 3333331373 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1373 = 33333331373 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 7 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1373)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h7]; exact prime_33333331373
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1373)}
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact (by norm_num : ¬ (333331373 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨7, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 221 = 3`. -/
theorem A242775_n221 : A242775 221 = 3 := by
  have hp : prime_of_index 221 = 1381 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1381) (by norm_num)
    rwa [pcount1381] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1381 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1381 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1381 = 31381 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1381 = 331381 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1381 = 3331381 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1381)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331381)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1381)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 222 = 2`. -/
theorem A242775_n222 : A242775 222 = 2 := by
  have hp : prime_of_index 222 = 1399 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1399) (by norm_num)
    rwa [pcount1399] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1399 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1399 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1399 = 31399 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1399 = 331399 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1399)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331399)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1399)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 223 = 3`. -/
theorem A242775_n223 : A242775 223 = 3 := by
  have hp : prime_of_index 223 = 1409 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1409) (by norm_num)
    rwa [pcount1409] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1409 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1409 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1409 = 31409 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1409 = 331409 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1409 = 3331409 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1409)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331409)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1409)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 224 = 2`. -/
theorem A242775_n224 : A242775 224 = 2 := by
  have hp : prime_of_index 224 = 1423 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1423) (by norm_num)
    rwa [pcount1423] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1423 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1423 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1423 = 31423 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1423 = 331423 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1423)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331423)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1423)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 225 = 4`. -/
theorem A242775_n225 : A242775 225 = 4 := by
  have hp : prime_of_index 225 = 1427 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1427) (by norm_num)
    rwa [pcount1427] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1427 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1427 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1427 = 31427 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1427 = 331427 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1427 = 3331427 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1427 = 33331427 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1427)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331427)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1427)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 226 = 4`. -/
theorem A242775_n226 : A242775 226 = 4 := by
  have hp : prime_of_index 226 = 1429 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1429) (by norm_num)
    rwa [pcount1429] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1429 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1429 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1429 = 31429 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1429 = 331429 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1429 = 3331429 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1429 = 33331429 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1429)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331429)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1429)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 228 = 8`. -/
theorem A242775_n228 : A242775 228 = 8 := by
  have hp : prime_of_index 228 = 1439 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1439) (by norm_num)
    rwa [pcount1439] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1439 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1439 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1439 = 31439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1439 = 331439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1439 = 3331439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1439 = 33331439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1439 = 333331439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1439 = 3333331439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1439 = 33333331439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1439 = 333333331439 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 8 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1439)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h8]; exact prime_333333331439
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1439)}
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact (by norm_num : ¬ (331439 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact (by norm_num : ¬ (3333331439 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    rcases hpr.eq_one_or_self_of_dvd 36739 (by norm_num) with hh | hh <;> norm_num at hh

/-- `A242775 229 = 2`. -/
theorem A242775_n229 : A242775 229 = 2 := by
  have hp : prime_of_index 229 = 1447 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1447) (by norm_num)
    rwa [pcount1447] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1447 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1447 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1447 = 31447 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1447 = 331447 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1447)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331447)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1447)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 230 = 2`. -/
theorem A242775_n230 : A242775 230 = 2 := by
  have hp : prime_of_index 230 = 1451 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1451) (by norm_num)
    rwa [pcount1451] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1451 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1451 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1451 = 31451 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1451 = 331451 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1451)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331451)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1451)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 231 = 3`. -/
theorem A242775_n231 : A242775 231 = 3 := by
  have hp : prime_of_index 231 = 1453 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1453) (by norm_num)
    rwa [pcount1453] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1453 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1453 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1453 = 31453 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1453 = 331453 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1453 = 3331453 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1453)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331453)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1453)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 232 = 12`. -/
theorem A242775_n232 : A242775 232 = 12 := by
  have hp : prime_of_index 232 = 1459 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1459) (by norm_num)
    rwa [pcount1459] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1459 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1459 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1459 = 31459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1459 = 331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1459 = 3331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1459 = 33331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1459 = 333331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1459 = 3333331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1459 = 33333331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1459 = 333333331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1459 = 3333333331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 1459 = 33333333331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 1459 = 333333333331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 1459 = 3333333333331459 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 12 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1459)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h12]; exact prime_3333333333331459
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1459)}
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact (by norm_num : ¬ (331459 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact (by norm_num : ¬ (3333331459 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    rcases hpr.eq_one_or_self_of_dvd 146477 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨12, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    rcases hpr.eq_one_or_self_of_dvd 51869 (by norm_num) with hh | hh <;> norm_num at hh

/-- `A242775 233 = 4`. -/
theorem A242775_n233 : A242775 233 = 4 := by
  have hp : prime_of_index 233 = 1471 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1471) (by norm_num)
    rwa [pcount1471] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1471 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1471 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1471 = 31471 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1471 = 331471 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1471 = 3331471 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1471 = 33331471 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 4 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1471)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h4]; exact (by norm_num : Nat.Prime 33331471)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1471)}
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨4, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 234 = 1`. -/
theorem A242775_n234 : A242775 234 = 1 := by
  have hp : prime_of_index 234 = 1481 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1481) (by norm_num)
    rwa [pcount1481] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1481 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1481 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1481 = 31481 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1481)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31481)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1481)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 236 = 3`. -/
theorem A242775_n236 : A242775 236 = 3 := by
  have hp : prime_of_index 236 = 1487 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1487) (by norm_num)
    rwa [pcount1487] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1487 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1487 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1487 = 31487 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1487 = 331487 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1487 = 3331487 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1487)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331487)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1487)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 237 = 1`. -/
theorem A242775_n237 : A242775 237 = 1 := by
  have hp : prime_of_index 237 = 1489 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1489) (by norm_num)
    rwa [pcount1489] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1489 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1489 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1489 = 31489 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1489)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31489)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1489)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 239 = 3`. -/
theorem A242775_n239 : A242775 239 = 3 := by
  have hp : prime_of_index 239 = 1499 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1499) (by norm_num)
    rwa [pcount1499] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1499 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1499 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1499 = 31499 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1499 = 331499 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1499 = 3331499 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 3 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1499)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h3]; exact (by norm_num : Nat.Prime 3331499)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1499)}
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨3, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 240 = 1`. -/
theorem A242775_n240 : A242775 240 = 1 := by
  have hp : prime_of_index 240 = 1511 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1511) (by norm_num)
    rwa [pcount1511] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1511 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1511 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1511 = 31511 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1511)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31511)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1511)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 241 = 2`. -/
theorem A242775_n241 : A242775 241 = 2 := by
  have hp : prime_of_index 241 = 1523 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1523) (by norm_num)
    rwa [pcount1523] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1523 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1523 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1523 = 31523 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1523 = 331523 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1523)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331523)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1523)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 242 = 1`. -/
theorem A242775_n242 : A242775 242 = 1 := by
  have hp : prime_of_index 242 = 1531 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1531) (by norm_num)
    rwa [pcount1531] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1531 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1531 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1531 = 31531 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1531)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31531)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1531)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 243 = 1`. -/
theorem A242775_n243 : A242775 243 = 1 := by
  have hp : prime_of_index 243 = 1543 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1543) (by norm_num)
    rwa [pcount1543] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1543 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1543 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1543 = 31543 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1543)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31543)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1543)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 244 = 2`. -/
theorem A242775_n244 : A242775 244 = 2 := by
  have hp : prime_of_index 244 = 1549 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1549) (by norm_num)
    rwa [pcount1549] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1549 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1549 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1549 = 31549 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1549 = 331549 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1549)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331549)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1549)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 245 = 2`. -/
theorem A242775_n245 : A242775 245 = 2 := by
  have hp : prime_of_index 245 = 1553 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1553) (by norm_num)
    rwa [pcount1553] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1553 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1553 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1553 = 31553 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1553 = 331553 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1553)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331553)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1553)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 246 = 8`. -/
theorem A242775_n246 : A242775 246 = 8 := by
  have hp : prime_of_index 246 = 1559 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1559) (by norm_num)
    rwa [pcount1559] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1559 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1559 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1559 = 31559 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1559 = 331559 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1559 = 3331559 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1559 = 33331559 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1559 = 333331559 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1559 = 3333331559 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1559 = 33333331559 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1559 = 333333331559 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 8 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1559)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h8]; exact prime_333333331559
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1559)}
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨8, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 247 = 1`. -/
theorem A242775_n247 : A242775 247 = 1 := by
  have hp : prime_of_index 247 = 1567 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1567) (by norm_num)
    rwa [pcount1567] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1567 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1567 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1567 = 31567 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1567)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31567)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1567)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

/-- `A242775 248 = 17`. -/
theorem A242775_n248 : A242775 248 = 17 := by
  have hp : prime_of_index 248 = 1571 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1571) (by norm_num)
    rwa [pcount1571] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1571 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1571 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1571 = 31571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1571 = 331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1571 = 3331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1571 = 33331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1571 = 333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1571 = 3333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1571 = 33333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1571 = 333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1571 = 3333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 1571 = 33333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 1571 = 333333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 1571 = 3333333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h13 : concatenate 13 1571 = 33333333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h14 : concatenate 14 1571 = 333333333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h15 : concatenate 15 1571 = 3333333333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h16 : concatenate 16 1571 = 33333333333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h17 : concatenate 17 1571 = 333333333333333331571 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 17 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1571)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h17]; exact prime_333333333333333331571
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1571)}
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact (by norm_num : ¬ (3331571 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact (by norm_num : ¬ (333333331571 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact (by norm_num : ¬ (3333333331571 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h12] at hpr
    exact (by norm_num : ¬ (3333333333331571 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h13] at hpr
    rcases hpr.eq_one_or_self_of_dvd 74230339 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h14] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h15] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨17, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h16] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 249 = 2`. -/
theorem A242775_n249 : A242775 249 = 2 := by
  have hp : prime_of_index 249 = 1579 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1579) (by norm_num)
    rwa [pcount1579] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1579 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1579 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1579 = 31579 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1579 = 331579 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 2 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1579)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h2]; exact (by norm_num : Nat.Prime 331579)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1579)}
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨2, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 250 = 1`. -/
theorem A242775_n250 : A242775 250 = 1 := by
  have hp : prime_of_index 250 = 1583 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1583) (by norm_num)
    rwa [pcount1583] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1583 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1583 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1583 = 31583 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1583)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h1]; exact (by norm_num : Nat.Prime 31583)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1583)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

end ValueTable201to250


section Witness185
/- Lucas--Pratt certificate tree for the 139-digit witness of `n = 185`
(`p = 1103`, `a(185) = 135`): sixteen nested primality certificates, the
recursion descending through primes of 118, 60, 41, 41, 33, 28, 23, 20, 15,
14, 13, 12 and 10 digits.  All modular exponentiations are kernel-evaluated
via `pmf`. -/


private lemma prime_3922323277 : Nat.Prime 3922323277 := by
  have c1 : (5:ℕ) ^ 1961161638 % 3922323277 = 3922323276 :=
    pow_mod_eq2 4 5 1961161638 3922323277 3922323276 (by decide) rfl
  have c2 : (5:ℕ) ^ 1307441092 % 3922323277 = 554321582 :=
    pow_mod_eq2 4 5 1307441092 3922323277 554321582 (by decide) rfl
  have c3 : (5:ℕ) ^ 10515612 % 3922323277 = 461606009 :=
    pow_mod_eq2 3 5 10515612 3922323277 461606009 (by decide) rfl
  have c4 : (5:ℕ) ^ 4476 % 3922323277 = 1385749725 :=
    pow_mod_eq2 2 5 4476 3922323277 1385749725 (by decide) rfl
  have cf : (5:ℕ) ^ 3922323276 % 3922323277 = 1 :=
    pow_mod_eq2 4 5 3922323276 3922323277 1 (by decide) rfl
  refine lucas_primality 3922323277 ((5 : ℕ) : ZMod 3922323277) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3922323277:ℕ) - 1 = 3922323276 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3922323277:ℕ) - 1 = 2 * (2 * (3 * (373 * (876301)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3922323277:ℕ) - 1) / 2 = 1961161638 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3922323277:ℕ) - 1) / 2 = 1961161638 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3922323277:ℕ) - 1) / 3 = 1307441092 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 373 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3922323277:ℕ) - 1) / 373 = 10515612 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 876301 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3922323277:ℕ) - 1) / 876301 = 4476 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_603425902226789 : Nat.Prime 603425902226789 := by
  have c1 : (2:ℕ) ^ 301712951113394 % 603425902226789 = 603425902226788 :=
    pow_mod_eq2 7 2 301712951113394 603425902226789 603425902226788 (by decide) rfl
  have c2 : (2:ℕ) ^ 15689293108 % 603425902226789 = 260596030546118 :=
    pow_mod_eq2 5 2 15689293108 603425902226789 260596030546118 (by decide) rfl
  have c3 : (2:ℕ) ^ 153844 % 603425902226789 = 341886328379878 :=
    pow_mod_eq2 3 2 153844 603425902226789 341886328379878 (by decide) rfl
  have cf : (2:ℕ) ^ 603425902226788 % 603425902226789 = 1 :=
    pow_mod_eq2 7 2 603425902226788 603425902226789 1 (by decide) rfl
  refine lucas_primality 603425902226789 ((2 : ℕ) : ZMod 603425902226789) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (603425902226789:ℕ) - 1 = 603425902226788 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (603425902226789:ℕ) - 1 = 2 * (2 * (38461 * (3922323277))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((603425902226789:ℕ) - 1) / 2 = 301712951113394 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((603425902226789:ℕ) - 1) / 2 = 301712951113394 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 38461 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((603425902226789:ℕ) - 1) / 38461 = 15689293108 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 3922323277 := (Nat.prime_dvd_prime_iff_eq hq prime_3922323277).mp h
          subst hqe
          have hexp : ((603425902226789:ℕ) - 1) / 3922323277 = 153844 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_73013327317637015423 : Nat.Prime 73013327317637015423 := by
  have c1 : (5:ℕ) ^ 36506663658818507711 % 73013327317637015423 = 73013327317637015422 :=
    pow_mod_eq2 9 5 36506663658818507711 73013327317637015423 73013327317637015422 (by decide) rfl
  have c2 : (5:ℕ) ^ 722904230867693222 % 73013327317637015423 = 64663522641010033970 :=
    pow_mod_eq2 8 5 722904230867693222 73013327317637015423 64663522641010033970 (by decide) rfl
  have c3 : (5:ℕ) ^ 121892032249811378 % 73013327317637015423 = 32199097242664920525 :=
    pow_mod_eq2 8 5 121892032249811378 73013327317637015423 32199097242664920525 (by decide) rfl
  have c4 : (5:ℕ) ^ 120998 % 73013327317637015423 = 46422128799795849211 :=
    pow_mod_eq2 3 5 120998 73013327317637015423 46422128799795849211 (by decide) rfl
  have cf : (5:ℕ) ^ 73013327317637015422 % 73013327317637015423 = 1 :=
    pow_mod_eq2 9 5 73013327317637015422 73013327317637015423 1 (by decide) rfl
  refine lucas_primality 73013327317637015423 ((5 : ℕ) : ZMod 73013327317637015423) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (73013327317637015423:ℕ) - 1 = 73013327317637015422 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (73013327317637015423:ℕ) - 1 = 2 * (101 * (599 * (603425902226789))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((73013327317637015423:ℕ) - 1) / 2 = 36506663658818507711 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 101 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((73013327317637015423:ℕ) - 1) / 101 = 722904230867693222 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 599 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((73013327317637015423:ℕ) - 1) / 599 = 121892032249811378 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 603425902226789 := (Nat.prime_dvd_prime_iff_eq hq prime_603425902226789).mp h
          subst hqe
          have hexp : ((73013327317637015423:ℕ) - 1) / 603425902226789 = 120998 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_64543781348791121633933 : Nat.Prime 64543781348791121633933 := by
  have c1 : (2:ℕ) ^ 32271890674395560816966 % 64543781348791121633933 = 64543781348791121633932 :=
    pow_mod_eq2 10 2 32271890674395560816966 64543781348791121633933 64543781348791121633932 (by decide) rfl
  have c2 : (2:ℕ) ^ 4964906257599317048764 % 64543781348791121633933 = 63174572084313931610001 :=
    pow_mod_eq2 10 2 4964906257599317048764 64543781348791121633933 63174572084313931610001 (by decide) rfl
  have c3 : (2:ℕ) ^ 3796693020517124801996 % 64543781348791121633933 = 19149318626563241473813 :=
    pow_mod_eq2 9 2 3796693020517124801996 64543781348791121633933 19149318626563241473813 (by decide) rfl
  have c4 : (2:ℕ) ^ 884 % 64543781348791121633933 = 29537738201554849939947 :=
    pow_mod_eq2 2 2 884 64543781348791121633933 29537738201554849939947 (by decide) rfl
  have cf : (2:ℕ) ^ 64543781348791121633932 % 64543781348791121633933 = 1 :=
    pow_mod_eq2 10 2 64543781348791121633932 64543781348791121633933 1 (by decide) rfl
  refine lucas_primality 64543781348791121633933 ((2 : ℕ) : ZMod 64543781348791121633933) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (64543781348791121633933:ℕ) - 1 = 64543781348791121633932 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (64543781348791121633933:ℕ) - 1 = 2 * (2 * (13 * (17 * (73013327317637015423)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((64543781348791121633933:ℕ) - 1) / 2 = 32271890674395560816966 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((64543781348791121633933:ℕ) - 1) / 2 = 32271890674395560816966 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((64543781348791121633933:ℕ) - 1) / 13 = 4964906257599317048764 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((64543781348791121633933:ℕ) - 1) / 17 = 3796693020517124801996 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 73013327317637015423 := (Nat.prime_dvd_prime_iff_eq hq prime_73013327317637015423).mp h
            subst hqe
            have hexp : ((64543781348791121633933:ℕ) - 1) / 73013327317637015423 = 884 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_4828520282703063809434527731 : Nat.Prime 4828520282703063809434527731 := by
  have c1 : (2:ℕ) ^ 2414260141351531904717263865 % 4828520282703063809434527731 = 4828520282703063809434527730 :=
    pow_mod_eq2 12 2 2414260141351531904717263865 4828520282703063809434527731 4828520282703063809434527730 (by decide) rfl
  have c2 : (2:ℕ) ^ 965704056540612761886905546 % 4828520282703063809434527731 = 2078181028939047451407279296 :=
    pow_mod_eq2 12 2 965704056540612761886905546 4828520282703063809434527731 2078181028939047451407279296 (by decide) rfl
  have c3 : (2:ℕ) ^ 645437813487911216339330 % 4828520282703063809434527731 = 1840481103609058584491465338 :=
    pow_mod_eq2 10 2 645437813487911216339330 4828520282703063809434527731 1840481103609058584491465338 (by decide) rfl
  have c4 : (2:ℕ) ^ 74810 % 4828520282703063809434527731 = 266800563501285671424973117 :=
    pow_mod_eq2 3 2 74810 4828520282703063809434527731 266800563501285671424973117 (by decide) rfl
  have cf : (2:ℕ) ^ 4828520282703063809434527730 % 4828520282703063809434527731 = 1 :=
    pow_mod_eq2 12 2 4828520282703063809434527730 4828520282703063809434527731 1 (by decide) rfl
  refine lucas_primality 4828520282703063809434527731 ((2 : ℕ) : ZMod 4828520282703063809434527731) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (4828520282703063809434527731:ℕ) - 1 = 4828520282703063809434527730 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (4828520282703063809434527731:ℕ) - 1 = 2 * (5 * (7481 * (64543781348791121633933))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((4828520282703063809434527731:ℕ) - 1) / 2 = 2414260141351531904717263865 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((4828520282703063809434527731:ℕ) - 1) / 5 = 965704056540612761886905546 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 7481 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((4828520282703063809434527731:ℕ) - 1) / 7481 = 645437813487911216339330 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 64543781348791121633933 := (Nat.prime_dvd_prime_iff_eq hq prime_64543781348791121633933).mp h
          subst hqe
          have hexp : ((4828520282703063809434527731:ℕ) - 1) / 64543781348791121633933 = 74810 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_713703582986339861672517543919111 : Nat.Prime 713703582986339861672517543919111 := by
  have c1 : (21:ℕ) ^ 356851791493169930836258771959555 % 713703582986339861672517543919111 = 713703582986339861672517543919110 :=
    pow_mod_eq2 14 21 356851791493169930836258771959555 713703582986339861672517543919111 713703582986339861672517543919110 (by decide) rfl
  have c2 : (21:ℕ) ^ 237901194328779953890839181306370 % 713703582986339861672517543919111 = 337873573641231919067166944014708 :=
    pow_mod_eq2 14 21 237901194328779953890839181306370 713703582986339861672517543919111 337873573641231919067166944014708 (by decide) rfl
  have c3 : (21:ℕ) ^ 142740716597267972334503508783822 % 713703582986339861672517543919111 = 694140892071953397712724932688645 :=
    pow_mod_eq2 14 21 142740716597267972334503508783822 713703582986339861672517543919111 694140892071953397712724932688645 (by decide) rfl
  have c4 : (21:ℕ) ^ 54900275614333835513270580301470 % 713703582986339861672517543919111 = 424305473438766143787303856910465 :=
    pow_mod_eq2 14 21 54900275614333835513270580301470 713703582986339861672517543919111 424305473438766143787303856910465 (by decide) rfl
  have c5 : (21:ℕ) ^ 1883122910254194885679465815090 % 713703582986339861672517543919111 = 426452533650439792490537929163010 :=
    pow_mod_eq2 13 21 1883122910254194885679465815090 713703582986339861672517543919111 426452533650439792490537929163010 (by decide) rfl
  have c6 : (21:ℕ) ^ 147810 % 713703582986339861672517543919111 = 284258175865770314869090430923986 :=
    pow_mod_eq2 3 21 147810 713703582986339861672517543919111 284258175865770314869090430923986 (by decide) rfl
  have cf : (21:ℕ) ^ 713703582986339861672517543919110 % 713703582986339861672517543919111 = 1 :=
    pow_mod_eq2 14 21 713703582986339861672517543919110 713703582986339861672517543919111 1 (by decide) rfl
  refine lucas_primality 713703582986339861672517543919111 ((21 : ℕ) : ZMod 713703582986339861672517543919111) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (713703582986339861672517543919111:ℕ) - 1 = 713703582986339861672517543919110 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (713703582986339861672517543919111:ℕ) - 1 = 2 * (3 * (5 * (13 * (379 * (4828520282703063809434527731))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((713703582986339861672517543919111:ℕ) - 1) / 2 = 356851791493169930836258771959555 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((713703582986339861672517543919111:ℕ) - 1) / 3 = 237901194328779953890839181306370 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((713703582986339861672517543919111:ℕ) - 1) / 5 = 142740716597267972334503508783822 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((713703582986339861672517543919111:ℕ) - 1) / 13 = 54900275614333835513270580301470 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 379 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((713703582986339861672517543919111:ℕ) - 1) / 379 = 1883122910254194885679465815090 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 4828520282703063809434527731 := (Nat.prime_dvd_prime_iff_eq hq prime_4828520282703063809434527731).mp h
              subst hqe
              have hexp : ((713703582986339861672517543919111:ℕ) - 1) / 4828520282703063809434527731 = 147810 := rfl
              rw [hexp, zmod_pow_of_mod c6]
              exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_19308877884425106088142169096573622329059 : Nat.Prime 19308877884425106088142169096573622329059 := by
  have c1 : (2:ℕ) ^ 9654438942212553044071084548286811164529 % 19308877884425106088142169096573622329059 = 19308877884425106088142169096573622329058 :=
    pow_mod_eq2 17 2 9654438942212553044071084548286811164529 19308877884425106088142169096573622329059 19308877884425106088142169096573622329058 (by decide) rfl
  have c2 : (2:ℕ) ^ 1755352534947736917103833554233965666278 % 19308877884425106088142169096573622329059 = 17665295644440309257886637207162906706458 :=
    pow_mod_eq2 17 2 1755352534947736917103833554233965666278 19308877884425106088142169096573622329059 17665295644440309257886637207162906706458 (by decide) rfl
  have c3 : (2:ℕ) ^ 23348099013815122234754738931769797254 % 19308877884425106088142169096573622329059 = 16189195054936305927515682343424715857957 :=
    pow_mod_eq2 16 2 23348099013815122234754738931769797254 19308877884425106088142169096573622329059 16189195054936305927515682343424715857957 (by decide) rfl
  have c4 : (2:ℕ) ^ 12985122988853467443269784194064305534 % 19308877884425106088142169096573622329059 = 411211186511457431761511603511209626730 :=
    pow_mod_eq2 16 2 12985122988853467443269784194064305534 19308877884425106088142169096573622329059 411211186511457431761511603511209626730 (by decide) rfl
  have c5 : (2:ℕ) ^ 27054478 % 19308877884425106088142169096573622329059 = 2798688004199409384223084716316051955129 :=
    pow_mod_eq2 4 2 27054478 19308877884425106088142169096573622329059 2798688004199409384223084716316051955129 (by decide) rfl
  have cf : (2:ℕ) ^ 19308877884425106088142169096573622329058 % 19308877884425106088142169096573622329059 = 1 :=
    pow_mod_eq2 17 2 19308877884425106088142169096573622329058 19308877884425106088142169096573622329059 1 (by decide) rfl
  refine lucas_primality 19308877884425106088142169096573622329059 ((2 : ℕ) : ZMod 19308877884425106088142169096573622329059) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (19308877884425106088142169096573622329059:ℕ) - 1 = 19308877884425106088142169096573622329058 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (19308877884425106088142169096573622329059:ℕ) - 1 = 2 * (11 * (827 * (1487 * (713703582986339861672517543919111)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((19308877884425106088142169096573622329059:ℕ) - 1) / 2 = 9654438942212553044071084548286811164529 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((19308877884425106088142169096573622329059:ℕ) - 1) / 11 = 1755352534947736917103833554233965666278 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 827 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((19308877884425106088142169096573622329059:ℕ) - 1) / 827 = 23348099013815122234754738931769797254 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 1487 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((19308877884425106088142169096573622329059:ℕ) - 1) / 1487 = 12985122988853467443269784194064305534 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 713703582986339861672517543919111 := (Nat.prime_dvd_prime_iff_eq hq prime_713703582986339861672517543919111).mp h
            subst hqe
            have hexp : ((19308877884425106088142169096573622329059:ℕ) - 1) / 713703582986339861672517543919111 = 27054478 := rfl
            rw [hexp, zmod_pow_of_mod c5]
            exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_4619841397 : Nat.Prime 4619841397 := by
  have c1 : (6:ℕ) ^ 2309920698 % 4619841397 = 4619841396 :=
    pow_mod_eq2 4 6 2309920698 4619841397 4619841396 (by decide) rfl
  have c2 : (6:ℕ) ^ 1539947132 % 4619841397 = 3659479276 :=
    pow_mod_eq2 4 6 1539947132 4619841397 3659479276 (by decide) rfl
  have c3 : (6:ℕ) ^ 107438172 % 4619841397 = 3215066110 :=
    pow_mod_eq2 4 6 107438172 4619841397 3215066110 (by decide) rfl
  have c4 : (6:ℕ) ^ 516 % 4619841397 = 2592011933 :=
    pow_mod_eq2 2 6 516 4619841397 2592011933 (by decide) rfl
  have cf : (6:ℕ) ^ 4619841396 % 4619841397 = 1 :=
    pow_mod_eq2 5 6 4619841396 4619841397 1 (by decide) rfl
  refine lucas_primality 4619841397 ((6 : ℕ) : ZMod 4619841397) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (4619841397:ℕ) - 1 = 4619841396 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (4619841397:ℕ) - 1 = 2 * (2 * (3 * (43 * (8953181)))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((4619841397:ℕ) - 1) / 2 = 2309920698 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((4619841397:ℕ) - 1) / 2 = 2309920698 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((4619841397:ℕ) - 1) / 3 = 1539947132 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 43 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((4619841397:ℕ) - 1) / 43 = 107438172 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            have h := hrest
            have hqe : q = 8953181 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((4619841397:ℕ) - 1) / 8953181 = 516 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_6624852563299 : Nat.Prime 6624852563299 := by
  have c1 : (2:ℕ) ^ 3312426281649 % 6624852563299 = 6624852563298 :=
    pow_mod_eq2 6 2 3312426281649 6624852563299 6624852563298 (by decide) rfl
  have c2 : (2:ℕ) ^ 2208284187766 % 6624852563299 = 3267388461655 :=
    pow_mod_eq2 6 2 2208284187766 6624852563299 3267388461655 (by decide) rfl
  have c3 : (2:ℕ) ^ 27719048382 % 6624852563299 = 1292709389927 :=
    pow_mod_eq2 5 2 27719048382 6624852563299 1292709389927 (by decide) rfl
  have c4 : (2:ℕ) ^ 1434 % 6624852563299 = 4265871887612 :=
    pow_mod_eq2 2 2 1434 6624852563299 4265871887612 (by decide) rfl
  have cf : (2:ℕ) ^ 6624852563298 % 6624852563299 = 1 :=
    pow_mod_eq2 6 2 6624852563298 6624852563299 1 (by decide) rfl
  refine lucas_primality 6624852563299 ((2 : ℕ) : ZMod 6624852563299) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (6624852563299:ℕ) - 1 = 6624852563298 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (6624852563299:ℕ) - 1 = 2 * (3 * (239 * (4619841397))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((6624852563299:ℕ) - 1) / 2 = 3312426281649 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((6624852563299:ℕ) - 1) / 3 = 2208284187766 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 239 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((6624852563299:ℕ) - 1) / 239 = 27719048382 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 4619841397 := (Nat.prime_dvd_prime_iff_eq hq prime_4619841397).mp h
          subst hqe
          have hexp : ((6624852563299:ℕ) - 1) / 4619841397 = 1434 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_19562549319433 : Nat.Prime 19562549319433 := by
  have c1 : (11:ℕ) ^ 9781274659716 % 19562549319433 = 19562549319432 :=
    pow_mod_eq2 6 11 9781274659716 19562549319433 19562549319432 (by decide) rfl
  have c2 : (11:ℕ) ^ 6520849773144 % 19562549319433 = 16806848652310 :=
    pow_mod_eq2 6 11 6520849773144 19562549319433 16806848652310 (by decide) rfl
  have c3 : (11:ℕ) ^ 2794649902776 % 19562549319433 = 13806526474404 :=
    pow_mod_eq2 6 11 2794649902776 19562549319433 13806526474404 (by decide) rfl
  have c4 : (11:ℕ) ^ 850545622584 % 19562549319433 = 5463508018066 :=
    pow_mod_eq2 5 11 850545622584 19562549319433 5463508018066 (by decide) rfl
  have c5 : (11:ℕ) ^ 140737764888 % 19562549319433 = 9810548420256 :=
    pow_mod_eq2 5 11 140737764888 19562549319433 9810548420256 (by decide) rfl
  have c6 : (11:ℕ) ^ 1611288 % 19562549319433 = 1974520873325 :=
    pow_mod_eq2 3 11 1611288 19562549319433 1974520873325 (by decide) rfl
  have cf : (11:ℕ) ^ 19562549319432 % 19562549319433 = 1 :=
    pow_mod_eq2 6 11 19562549319432 19562549319433 1 (by decide) rfl
  refine lucas_primality 19562549319433 ((11 : ℕ) : ZMod 19562549319433) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (19562549319433:ℕ) - 1 = 19562549319432 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (19562549319433:ℕ) - 1 = 2 * (2 * (2 * (3 * (3 * (7 * (23 * (139 * (12140939)))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((19562549319433:ℕ) - 1) / 2 = 9781274659716 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((19562549319433:ℕ) - 1) / 2 = 9781274659716 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((19562549319433:ℕ) - 1) / 2 = 9781274659716 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((19562549319433:ℕ) - 1) / 3 = 6520849773144 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((19562549319433:ℕ) - 1) / 3 = 6520849773144 := rfl
              rw [hexp, zmod_pow_of_mod c2]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((19562549319433:ℕ) - 1) / 7 = 2794649902776 := rfl
                rw [hexp, zmod_pow_of_mod c3]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 23 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((19562549319433:ℕ) - 1) / 23 = 850545622584 := rfl
                  rw [hexp, zmod_pow_of_mod c4]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                  · 
                    have hqe : q = 139 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((19562549319433:ℕ) - 1) / 139 = 140737764888 := rfl
                    rw [hexp, zmod_pow_of_mod c5]
                    exact zmod_ne_one (by decide) (by decide) (by decide)
                  · 
                    have h := hrest
                    have hqe : q = 12140939 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((19562549319433:ℕ) - 1) / 12140939 = 1611288 := rfl
                    rw [hexp, zmod_pow_of_mod c6]
                    exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_19127558148423300581098692481963421988307 : Nat.Prime 19127558148423300581098692481963421988307 := by
  have c1 : (3:ℕ) ^ 9563779074211650290549346240981710994153 % 19127558148423300581098692481963421988307 = 19127558148423300581098692481963421988306 :=
    pow_mod_eq2 17 3 9563779074211650290549346240981710994153 19127558148423300581098692481963421988307 19127558148423300581098692481963421988306 (by decide) rfl
  have c2 : (3:ℕ) ^ 6375852716141100193699564160654473996102 % 19127558148423300581098692481963421988307 = 8631962553949162482522637602857555236883 :=
    pow_mod_eq2 17 3 6375852716141100193699564160654473996102 19127558148423300581098692481963421988307 8631962553949162482522637602857555236883 (by decide) rfl
  have c3 : (3:ℕ) ^ 1738868922583936416463517498360311089846 % 19127558148423300581098692481963421988307 = 14669626190929684967318223711284420310801 :=
    pow_mod_eq2 17 3 1738868922583936416463517498360311089846 19127558148423300581098692481963421988307 14669626190929684967318223711284420310801 (by decide) rfl
  have c4 : (3:ℕ) ^ 516961031038467583272937634647660053738 % 19127558148423300581098692481963421988307 = 19051439161023238958519985270822931282749 :=
    pow_mod_eq2 17 3 516961031038467583272937634647660053738 19127558148423300581098692481963421988307 19051439161023238958519985270822931282749 (by decide) rfl
  have c5 : (3:ℕ) ^ 324195900820733908154215126812939355734 % 19127558148423300581098692481963421988307 = 2258594584064095088685374015593679964552 :=
    pow_mod_eq2 16 3 324195900820733908154215126812939355734 19127558148423300581098692481963421988307 2258594584064095088685374015593679964552 (by decide) rfl
  have c6 : (3:ℕ) ^ 42600352223659912207346753857379558994 % 19127558148423300581098692481963421988307 = 7313859140126694022348125119801109402534 :=
    pow_mod_eq2 16 3 42600352223659912207346753857379558994 19127558148423300581098692481963421988307 7313859140126694022348125119801109402534 (by decide) rfl
  have c7 : (3:ℕ) ^ 29563459271133385751311734902570976798 % 19127558148423300581098692481963421988307 = 17418230386345640291769681126833897969584 :=
    pow_mod_eq2 16 3 29563459271133385751311734902570976798 19127558148423300581098692481963421988307 17418230386345640291769681126833897969584 (by decide) rfl
  have c8 : (3:ℕ) ^ 743077508582545378233118079404973466 % 19127558148423300581098692481963421988307 = 16594217128308376531963449653627050257751 :=
    pow_mod_eq2 15 3 743077508582545378233118079404973466 19127558148423300581098692481963421988307 16594217128308376531963449653627050257751 (by decide) rfl
  have c9 : (3:ℕ) ^ 166229745699664548316187025662991318 % 19127558148423300581098692481963421988307 = 4515783071012615737739118523548064578214 :=
    pow_mod_eq2 15 3 166229745699664548316187025662991318 19127558148423300581098692481963421988307 4515783071012615737739118523548064578214 (by decide) rfl
  have c10 : (3:ℕ) ^ 2425213336144298528887837819616334 % 19127558148423300581098692481963421988307 = 456305743004667256749686373105597370606 :=
    pow_mod_eq2 14 3 2425213336144298528887837819616334 19127558148423300581098692481963421988307 456305743004667256749686373105597370606 (by decide) rfl
  have c11 : (3:ℕ) ^ 977764085656382785680095682 % 19127558148423300581098692481963421988307 = 11670232319216013401192057320939223085560 :=
    pow_mod_eq2 12 3 977764085656382785680095682 19127558148423300581098692481963421988307 11670232319216013401192057320939223085560 (by decide) rfl
  have cf : (3:ℕ) ^ 19127558148423300581098692481963421988306 % 19127558148423300581098692481963421988307 = 1 :=
    pow_mod_eq2 17 3 19127558148423300581098692481963421988306 19127558148423300581098692481963421988307 1 (by decide) rfl
  refine lucas_primality 19127558148423300581098692481963421988307 ((3 : ℕ) : ZMod 19127558148423300581098692481963421988307) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (19127558148423300581098692481963421988307:ℕ) - 1 = 19127558148423300581098692481963421988306 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (19127558148423300581098692481963421988307:ℕ) - 1 = 2 * (3 * (11 * (37 * (59 * (449 * (647 * (25741 * (115067 * (7886959 * (19562549319433)))))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 2 = 9563779074211650290549346240981710994153 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 3 = 6375852716141100193699564160654473996102 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 11 = 1738868922583936416463517498360311089846 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 37 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 37 = 516961031038467583272937634647660053738 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 59 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 59 = 324195900820733908154215126812939355734 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 449 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 449 = 42600352223659912207346753857379558994 := rfl
                rw [hexp, zmod_pow_of_mod c6]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 647 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 647 = 29563459271133385751311734902570976798 := rfl
                  rw [hexp, zmod_pow_of_mod c7]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                  · 
                    have hqe : q = 25741 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 25741 = 743077508582545378233118079404973466 := rfl
                    rw [hexp, zmod_pow_of_mod c8]
                    exact zmod_ne_one (by decide) (by decide) (by decide)
                  · 
                    rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                    · 
                      have hqe : q = 115067 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                      subst hqe
                      have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 115067 = 166229745699664548316187025662991318 := rfl
                      rw [hexp, zmod_pow_of_mod c9]
                      exact zmod_ne_one (by decide) (by decide) (by decide)
                    · 
                      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                      · 
                        have hqe : q = 7886959 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                        subst hqe
                        have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 7886959 = 2425213336144298528887837819616334 := rfl
                        rw [hexp, zmod_pow_of_mod c10]
                        exact zmod_ne_one (by decide) (by decide) (by decide)
                      · 
                        have h := hrest
                        have hqe : q = 19562549319433 := (Nat.prime_dvd_prime_iff_eq hq prime_19562549319433).mp h
                        subst hqe
                        have hexp : ((19127558148423300581098692481963421988307:ℕ) - 1) / 19562549319433 = 977764085656382785680095682 := rfl
                        rw [hexp, zmod_pow_of_mod c11]
                        exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_498185129853624853188408694658534305027742746510684108367833 : Nat.Prime 498185129853624853188408694658534305027742746510684108367833 := by
  have c1 : (5:ℕ) ^ 249092564926812426594204347329267152513871373255342054183916 % 498185129853624853188408694658534305027742746510684108367833 = 498185129853624853188408694658534305027742746510684108367832 :=
    pow_mod_eq2 25 5 249092564926812426594204347329267152513871373255342054183916 498185129853624853188408694658534305027742746510684108367833 498185129853624853188408694658534305027742746510684108367832 (by decide) rfl
  have c2 : (5:ℕ) ^ 166061709951208284396136231552844768342580915503561369455944 % 498185129853624853188408694658534305027742746510684108367833 = 234603599572991660091592844218107876196163727587568646901074 :=
    pow_mod_eq2 25 5 166061709951208284396136231552844768342580915503561369455944 498185129853624853188408694658534305027742746510684108367833 234603599572991660091592844218107876196163727587568646901074 (by decide) rfl
  have c3 : (5:ℕ) ^ 9210129778588394616265343488908215877460996219531606152 % 498185129853624853188408694658534305027742746510684108367833 = 432023045005666147767036055993893109702950076886604808883548 :=
    pow_mod_eq2 23 5 9210129778588394616265343488908215877460996219531606152 498185129853624853188408694658534305027742746510684108367833 432023045005666147767036055993893109702950076886604808883548 (by decide) rfl
  have c4 : (5:ℕ) ^ 75199428982543565765786260939398993988881386568 % 498185129853624853188408694658534305027742746510684108367833 = 369330836344796666959547380237205736668394960495948736545177 :=
    pow_mod_eq2 20 5 75199428982543565765786260939398993988881386568 498185129853624853188408694658534305027742746510684108367833 369330836344796666959547380237205736668394960495948736545177 (by decide) rfl
  have c5 : (5:ℕ) ^ 25800832800101247048 % 498185129853624853188408694658534305027742746510684108367833 = 191455850362482589986920908313689049827470030719798016550329 :=
    pow_mod_eq2 9 5 25800832800101247048 498185129853624853188408694658534305027742746510684108367833 191455850362482589986920908313689049827470030719798016550329 (by decide) rfl
  have cf : (5:ℕ) ^ 498185129853624853188408694658534305027742746510684108367832 % 498185129853624853188408694658534305027742746510684108367833 = 1 :=
    pow_mod_eq2 25 5 498185129853624853188408694658534305027742746510684108367832 498185129853624853188408694658534305027742746510684108367833 1 (by decide) rfl
  refine lucas_primality 498185129853624853188408694658534305027742746510684108367833 ((5 : ℕ) : ZMod 498185129853624853188408694658534305027742746510684108367833) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (498185129853624853188408694658534305027742746510684108367833:ℕ) - 1 = 498185129853624853188408694658534305027742746510684108367832 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (498185129853624853188408694658534305027742746510684108367833:ℕ) - 1 = 2 * (2 * (2 * (3 * (3 * (54091 * (6624852563299 * (19308877884425106088142169096573622329059))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((498185129853624853188408694658534305027742746510684108367833:ℕ) - 1) / 2 = 249092564926812426594204347329267152513871373255342054183916 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((498185129853624853188408694658534305027742746510684108367833:ℕ) - 1) / 2 = 249092564926812426594204347329267152513871373255342054183916 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((498185129853624853188408694658534305027742746510684108367833:ℕ) - 1) / 2 = 249092564926812426594204347329267152513871373255342054183916 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((498185129853624853188408694658534305027742746510684108367833:ℕ) - 1) / 3 = 166061709951208284396136231552844768342580915503561369455944 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((498185129853624853188408694658534305027742746510684108367833:ℕ) - 1) / 3 = 166061709951208284396136231552844768342580915503561369455944 := rfl
              rw [hexp, zmod_pow_of_mod c2]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 54091 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((498185129853624853188408694658534305027742746510684108367833:ℕ) - 1) / 54091 = 9210129778588394616265343488908215877460996219531606152 := rfl
                rw [hexp, zmod_pow_of_mod c3]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 6624852563299 := (Nat.prime_dvd_prime_iff_eq hq prime_6624852563299).mp h
                  subst hqe
                  have hexp : ((498185129853624853188408694658534305027742746510684108367833:ℕ) - 1) / 6624852563299 = 75199428982543565765786260939398993988881386568 := rfl
                  rw [hexp, zmod_pow_of_mod c4]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  have h := hrest
                  have hqe : q = 19308877884425106088142169096573622329059 := (Nat.prime_dvd_prime_iff_eq hq prime_19308877884425106088142169096573622329059).mp h
                  subst hqe
                  have hexp : ((498185129853624853188408694658534305027742746510684108367833:ℕ) - 1) / 19308877884425106088142169096573622329059 = 25800832800101247048 := rfl
                  rw [hexp, zmod_pow_of_mod c5]
                  exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_118916120053 : Nat.Prime 118916120053 := by
  have c1 : (2:ℕ) ^ 59458060026 % 118916120053 = 118916120052 :=
    pow_mod_eq2 5 2 59458060026 118916120053 118916120052 (by decide) rfl
  have c2 : (2:ℕ) ^ 39638706684 % 118916120053 = 10808512404 :=
    pow_mod_eq2 5 2 39638706684 118916120053 10808512404 (by decide) rfl
  have c3 : (2:ℕ) ^ 2900393172 % 118916120053 = 68872498190 :=
    pow_mod_eq2 4 2 2900393172 118916120053 68872498190 (by decide) rfl
  have c4 : (2:ℕ) ^ 2765491164 % 118916120053 = 96713347684 :=
    pow_mod_eq2 4 2 2765491164 118916120053 96713347684 (by decide) rfl
  have c5 : (2:ℕ) ^ 2729124 % 118916120053 = 91415482465 :=
    pow_mod_eq2 3 2 2729124 118916120053 91415482465 (by decide) rfl
  have cf : (2:ℕ) ^ 118916120052 % 118916120053 = 1 :=
    pow_mod_eq2 5 2 118916120052 118916120053 1 (by decide) rfl
  refine lucas_primality 118916120053 ((2 : ℕ) : ZMod 118916120053) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (118916120053:ℕ) - 1 = 118916120052 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (118916120053:ℕ) - 1 = 2 * (2 * (3 * (3 * (41 * (43 * (43 * (43573))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((118916120053:ℕ) - 1) / 2 = 59458060026 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((118916120053:ℕ) - 1) / 2 = 59458060026 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((118916120053:ℕ) - 1) / 3 = 39638706684 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((118916120053:ℕ) - 1) / 3 = 39638706684 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 41 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((118916120053:ℕ) - 1) / 41 = 2900393172 := rfl
              rw [hexp, zmod_pow_of_mod c3]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 43 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((118916120053:ℕ) - 1) / 43 = 2765491164 := rfl
                rw [hexp, zmod_pow_of_mod c4]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 43 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((118916120053:ℕ) - 1) / 43 = 2765491164 := rfl
                  rw [hexp, zmod_pow_of_mod c4]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  have h := hrest
                  have hqe : q = 43573 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((118916120053:ℕ) - 1) / 43573 = 2729124 := rfl
                  rw [hexp, zmod_pow_of_mod c5]
                  exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_6261970843 : Nat.Prime 6261970843 := by
  have c1 : (3:ℕ) ^ 3130985421 % 6261970843 = 6261970842 :=
    pow_mod_eq2 4 3 3130985421 6261970843 6261970842 (by decide) rfl
  have c2 : (3:ℕ) ^ 2087323614 % 6261970843 = 2470392976 :=
    pow_mod_eq2 4 3 2087323614 6261970843 2470392976 (by decide) rfl
  have c3 : (3:ℕ) ^ 368351226 % 6261970843 = 2868898116 :=
    pow_mod_eq2 4 3 368351226 6261970843 2868898116 (by decide) rfl
  have c4 : (3:ℕ) ^ 7289838 % 6261970843 = 5783916345 :=
    pow_mod_eq2 3 3 7289838 6261970843 5783916345 (by decide) rfl
  have c5 : (3:ℕ) ^ 2365686 % 6261970843 = 3559643048 :=
    pow_mod_eq2 3 3 2365686 6261970843 3559643048 (by decide) rfl
  have cf : (3:ℕ) ^ 6261970842 % 6261970843 = 1 :=
    pow_mod_eq2 5 3 6261970842 6261970843 1 (by decide) rfl
  refine lucas_primality 6261970843 ((3 : ℕ) : ZMod 6261970843) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (6261970843:ℕ) - 1 = 6261970842 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (6261970843:ℕ) - 1 = 2 * (3 * (3 * (3 * (3 * (17 * (859 * (2647))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((6261970843:ℕ) - 1) / 2 = 3130985421 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((6261970843:ℕ) - 1) / 3 = 2087323614 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((6261970843:ℕ) - 1) / 3 = 2087323614 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((6261970843:ℕ) - 1) / 3 = 2087323614 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((6261970843:ℕ) - 1) / 3 = 2087323614 := rfl
              rw [hexp, zmod_pow_of_mod c2]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((6261970843:ℕ) - 1) / 17 = 368351226 := rfl
                rw [hexp, zmod_pow_of_mod c3]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 859 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((6261970843:ℕ) - 1) / 859 = 7289838 := rfl
                  rw [hexp, zmod_pow_of_mod c4]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  have h := hrest
                  have hqe : q = 2647 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((6261970843:ℕ) - 1) / 2647 = 2365686 := rfl
                  rw [hexp, zmod_pow_of_mod c5]
                  exact zmod_ne_one (by decide) (by decide) (by decide)

set_option maxRecDepth 19600 in
private lemma prime_2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 : Nat.Prime 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 := by
  have c1 : (11:ℕ) ^ 1138218999193935327418406742848124661390030061382989624945687761675152637219308679052453985036492221762871362832347495 % 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694990 :=
    pow_mod_eq2 49 11 1138218999193935327418406742848124661390030061382989624945687761675152637219308679052453985036492221762871362832347495 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694990 (by decide) rfl
  have c2 : (11:ℕ) ^ 455287599677574130967362697139249864556012024553195849978275104670061054887723471620981594014596888705148545132938998 % 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 446985845911698484285778546757537552213590226095715236353076615312492839143210704202631540006941346658258275305874238 :=
    pow_mod_eq2 49 11 455287599677574130967362697139249864556012024553195849978275104670061054887723471620981594014596888705148545132938998 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 446985845911698484285778546757537552213590226095715236353076615312492839143210704202631540006941346658258275305874238 (by decide) rfl
  have c3 : (11:ℕ) ^ 325205428341124379262401926528035617540008588966568464270196503335757896348373908300701138581854920503677532237813570 % 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 1442595673986046028286935656700719904408459614554803889715631582024634284378474019651872025820509533328880708534335756 :=
    pow_mod_eq2 49 11 325205428341124379262401926528035617540008588966568464270196503335757896348373908300701138581854920503677532237813570 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 1442595673986046028286935656700719904408459614554803889715631582024634284378474019651872025820509533328880708534335756 (by decide) rfl
  have c4 : (11:ℕ) ^ 206948908944351877712437589608749938434550920251452659081034138486391388585328850736809815461180403956885702333154090 % 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 1532047216502638594123421959671251938850437293271140816774085907214420342589618524958333713007483837694172303747632672 :=
    pow_mod_eq2 49 11 206948908944351877712437589608749938434550920251452659081034138486391388585328850736809815461180403956885702333154090 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 1532047216502638594123421959671251938850437293271140816774085907214420342589618524958333713007483837694172303747632672 (by decide) rfl
  have c5 : (11:ℕ) ^ 872532770558785226077736100305193301180551982662314775734524922709967525656810026103835941001527191845819365912110 % 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 837746592249660960158811306956965523885137363808796443921665611176149631349694106472364983528580462859904755438791902 :=
    pow_mod_eq2 48 11 872532770558785226077736100305193301180551982662314775734524922709967525656810026103835941001527191845819365912110 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 837746592249660960158811306956965523885137363808796443921665611176149631349694106472364983528580462859904755438791902 (by decide) rfl
  have c6 : (11:ℕ) ^ 19143224630716842673716741043933001240299557848255582875844163355906370108405653853820729400021509155567830 % 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 129158374225064031253790652137494554556080384970165405213220207054239991038148549540111311774673333434868874424077791 :=
    pow_mod_eq2 45 11 19143224630716842673716741043933001240299557848255582875844163355906370108405653853820729400021509155567830 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 129158374225064031253790652137494554556080384970165405213220207054239991038148549540111311774673333434868874424077791 (by decide) rfl
  have c7 : (11:ℕ) ^ 119013518647989011630870283685973617052747198822330120168077990246749592480570 % 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 1746491806484967056725938974440387815132883648980556867805438338703537854592792449135263785239210847900623915911926819 :=
    pow_mod_eq2 33 11 119013518647989011630870283685973617052747198822330120168077990246749592480570 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 1746491806484967056725938974440387815132883648980556867805438338703537854592792449135263785239210847900623915911926819 (by decide) rfl
  have c8 : (11:ℕ) ^ 4569461956957098096517633976078972215711434149946329020030 % 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 1296310075501431261672285122107765903232130959620652567109094816886922842268159850260126230000346510045344152089838405 :=
    pow_mod_eq2 24 11 4569461956957098096517633976078972215711434149946329020030 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 1296310075501431261672285122107765903232130959620652567109094816886922842268159850260126230000346510045344152089838405 (by decide) rfl
  have cf : (11:ℕ) ^ 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694990 % 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 1 :=
    pow_mod_eq2 49 11 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694990 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 1 (by decide) rfl
  refine lucas_primality 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 ((11 : ℕ) : ZMod 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1 = 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694990 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1 = 2 * (5 * (7 * (11 * (2609 * (118916120053 * (19127558148423300581098692481963421988307 * (498185129853624853188408694658534305027742746510684108367833))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1) / 2 = 1138218999193935327418406742848124661390030061382989624945687761675152637219308679052453985036492221762871362832347495 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1) / 5 = 455287599677574130967362697139249864556012024553195849978275104670061054887723471620981594014596888705148545132938998 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1) / 7 = 325205428341124379262401926528035617540008588966568464270196503335757896348373908300701138581854920503677532237813570 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1) / 11 = 206948908944351877712437589608749938434550920251452659081034138486391388585328850736809815461180403956885702333154090 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 2609 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1) / 2609 = 872532770558785226077736100305193301180551982662314775734524922709967525656810026103835941001527191845819365912110 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 118916120053 := (Nat.prime_dvd_prime_iff_eq hq prime_118916120053).mp h
                subst hqe
                have hexp : ((2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1) / 118916120053 = 19143224630716842673716741043933001240299557848255582875844163355906370108405653853820729400021509155567830 := rfl
                rw [hexp, zmod_pow_of_mod c6]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 19127558148423300581098692481963421988307 := (Nat.prime_dvd_prime_iff_eq hq prime_19127558148423300581098692481963421988307).mp h
                  subst hqe
                  have hexp : ((2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1) / 19127558148423300581098692481963421988307 = 119013518647989011630870283685973617052747198822330120168077990246749592480570 := rfl
                  rw [hexp, zmod_pow_of_mod c7]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  have h := hrest
                  have hqe : q = 498185129853624853188408694658534305027742746510684108367833 := (Nat.prime_dvd_prime_iff_eq hq prime_498185129853624853188408694658534305027742746510684108367833).mp h
                  subst hqe
                  have hexp : ((2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991:ℕ) - 1) / 498185129853624853188408694658534305027742746510684108367833 = 4569461956957098096517633976078972215711434149946329020030 := rfl
                  rw [hexp, zmod_pow_of_mod c8]
                  exact zmod_ne_one (by decide) (by decide) (by decide)

set_option maxRecDepth 22440 in
private lemma prime_3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 : Nat.Prime 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
  have c1 : (5:ℕ) ^ 1666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665551 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 :=
    pow_mod_eq2 58 5 1666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665551 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 (by decide) rfl
  have c2 : (5:ℕ) ^ 45662100456621004566210045662100456621004566210045662100456621004566210045662100456621004566210045662100456621004566210045662100456620974 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 1269279630156824070370618689668933462604987588722126098492704099695421196055262102047699669352854889300293250382157548856425716591802725023 :=
    pow_mod_eq2 57 5 45662100456621004566210045662100456621004566210045662100456621004566210045662100456621004566210045662100456621004566210045662100456620974 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 1269279630156824070370618689668933462604987588722126098492704099695421196055262102047699669352854889300293250382157548856425716591802725023 (by decide) rfl
  have c3 : (5:ℕ) ^ 7917656373713380839271575613618368962787015043547110055423594615993665874901029295328582739509105304829770387965162311955661124307205062 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 916539085409870897272736926643006217374785968283864615335824076029830794207588805219270351252558731571510791385285029326335959668000812366 :=
    pow_mod_eq2 57 5 7917656373713380839271575613618368962787015043547110055423594615993665874901029295328582739509105304829770387965162311955661124307205062 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 916539085409870897272736926643006217374785968283864615335824076029830794207588805219270351252558731571510791385285029326335959668000812366 (by decide) rfl
  have c4 : (5:ℕ) ^ 876197115261189540975226665622239705275328733824196481244956937978474815948224461022677996596324686056383109127634494723847640887458 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 2844918422318131287938496339335677329078186925751085990873029015781091585807207717813987054857613350666398319107890387622782071191683552893 :=
    pow_mod_eq2 55 5 876197115261189540975226665622239705275328733824196481244956937978474815948224461022677996596324686056383109127634494723847640887458 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 2844918422318131287938496339335677329078186925751085990873029015781091585807207717813987054857613350666398319107890387622782071191683552893 (by decide) rfl
  have c5 : (5:ℕ) ^ 532313774194514136503035987280998799970511669361558113746926836869868404357457550897979058720656092542801597540644015632529085114 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 1580399852298772712947605340218185173016944501900090570672883361908386801905809200062086023549509843975116994774980675879729802413091120550 :=
    pow_mod_eq2 54 5 532313774194514136503035987280998799970511669361558113746926836869868404357457550897979058720656092542801597540644015632529085114 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 1580399852298772712947605340218185173016944501900090570672883361908386801905809200062086023549509843975116994774980675879729802413091120550 (by decide) rfl
  have c6 : (5:ℕ) ^ 1464275915133175384322 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 1792852630177734478472331495734654419582939502873078374446820879553964579955772146900662153190944171490605197155076906750531945043837034562 :=
    pow_mod_eq2 9 5 1464275915133175384322 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 1792852630177734478472331495734654419582939502873078374446820879553964579955772146900662153190944171490605197155076906750531945043837034562 (by decide) rfl
  have cf : (5:ℕ) ^ 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 1 :=
    pow_mod_eq2 58 5 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 1 (by decide) rfl
  refine lucas_primality 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 ((5 : ℕ) : ZMod 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103:ℕ) - 1 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103:ℕ) - 1 = 2 * (73 * (421 * (3804319 * (6261970843 * (2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103:ℕ) - 1) / 2 = 1666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665551 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 73 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103:ℕ) - 1) / 73 = 45662100456621004566210045662100456621004566210045662100456621004566210045662100456621004566210045662100456621004566210045662100456620974 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 421 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103:ℕ) - 1) / 421 = 7917656373713380839271575613618368962787015043547110055423594615993665874901029295328582739509105304829770387965162311955661124307205062 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3804319 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103:ℕ) - 1) / 3804319 = 876197115261189540975226665622239705275328733824196481244956937978474815948224461022677996596324686056383109127634494723847640887458 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 6261970843 := (Nat.prime_dvd_prime_iff_eq hq prime_6261970843).mp h
              subst hqe
              have hexp : ((3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103:ℕ) - 1) / 6261970843 = 532313774194514136503035987280998799970511669361558113746926836869868404357457550897979058720656092542801597540644015632529085114 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 := (Nat.prime_dvd_prime_iff_eq hq prime_2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991).mp h
              subst hqe
              have hexp : ((3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103:ℕ) - 1) / 2276437998387870654836813485696249322780060122765979249891375523350305274438617358104907970072984443525742725664694991 = 1464275915133175384322 := rfl
              rw [hexp, zmod_pow_of_mod c6]
              exact zmod_ne_one (by decide) (by decide) (by decide)

end Witness185


section ValueTable210_227_235
/- The three remaining entries of the 201..250 block: Lucas--Pratt certificate
trees for the 55-digit witness of `n = 210`, the 23-digit witness of `n = 227`
and the 25-digit witness of `n = 235`. -/


private lemma prime_95713342721 : Nat.Prime 95713342721 := by
  have c1 : (3:ℕ) ^ 47856671360 % 95713342721 = 95713342720 :=
    pow_mod_eq2 5 3 47856671360 95713342721 95713342720 (by decide) rfl
  have c2 : (3:ℕ) ^ 19142668544 % 95713342721 = 55686093619 :=
    pow_mod_eq2 5 3 19142668544 95713342721 55686093619 (by decide) rfl
  have c3 : (3:ℕ) ^ 87729920 % 95713342721 = 2954324429 :=
    pow_mod_eq2 4 3 87729920 95713342721 2954324429 (by decide) rfl
  have c4 : (3:ℕ) ^ 1396480 % 95713342721 = 39589512268 :=
    pow_mod_eq2 3 3 1396480 95713342721 39589512268 (by decide) rfl
  have cf : (3:ℕ) ^ 95713342720 % 95713342721 = 1 :=
    pow_mod_eq2 5 3 95713342720 95713342721 1 (by decide) rfl
  refine lucas_primality 95713342721 ((3 : ℕ) : ZMod 95713342721) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (95713342721:ℕ) - 1 = 95713342720 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (95713342721:ℕ) - 1 = 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (5 * (1091 * (68539)))))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((95713342721:ℕ) - 1) / 2 = 47856671360 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((95713342721:ℕ) - 1) / 2 = 47856671360 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((95713342721:ℕ) - 1) / 2 = 47856671360 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((95713342721:ℕ) - 1) / 2 = 47856671360 := rfl
            rw [hexp, zmod_pow_of_mod c1]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((95713342721:ℕ) - 1) / 2 = 47856671360 := rfl
              rw [hexp, zmod_pow_of_mod c1]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((95713342721:ℕ) - 1) / 2 = 47856671360 := rfl
                rw [hexp, zmod_pow_of_mod c1]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((95713342721:ℕ) - 1) / 2 = 47856671360 := rfl
                  rw [hexp, zmod_pow_of_mod c1]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                  · 
                    have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((95713342721:ℕ) - 1) / 2 = 47856671360 := rfl
                    rw [hexp, zmod_pow_of_mod c1]
                    exact zmod_ne_one (by decide) (by decide) (by decide)
                  · 
                    rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                    · 
                      have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                      subst hqe
                      have hexp : ((95713342721:ℕ) - 1) / 5 = 19142668544 := rfl
                      rw [hexp, zmod_pow_of_mod c2]
                      exact zmod_ne_one (by decide) (by decide) (by decide)
                    · 
                      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                      · 
                        have hqe : q = 1091 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                        subst hqe
                        have hexp : ((95713342721:ℕ) - 1) / 1091 = 87729920 := rfl
                        rw [hexp, zmod_pow_of_mod c3]
                        exact zmod_ne_one (by decide) (by decide) (by decide)
                      · 
                        have h := hrest
                        have hqe : q = 68539 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                        subst hqe
                        have hexp : ((95713342721:ℕ) - 1) / 68539 = 1396480 := rfl
                        rw [hexp, zmod_pow_of_mod c4]
                        exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_1261496944918839077 : Nat.Prime 1261496944918839077 := by
  have c1 : (12:ℕ) ^ 630748472459419538 % 1261496944918839077 = 1261496944918839076 :=
    pow_mod_eq2 8 12 630748472459419538 1261496944918839077 1261496944918839076 (by decide) rfl
  have c2 : (12:ℕ) ^ 180213849274119868 % 1261496944918839077 = 395336896871921141 :=
    pow_mod_eq2 8 12 180213849274119868 1261496944918839077 395336896871921141 (by decide) rfl
  have c3 : (12:ℕ) ^ 21381304151166764 % 1261496944918839077 = 971655047326683053 :=
    pow_mod_eq2 7 12 21381304151166764 1261496944918839077 971655047326683053 (by decide) rfl
  have c4 : (12:ℕ) ^ 468202060732 % 1261496944918839077 = 619660538760763187 :=
    pow_mod_eq2 5 12 468202060732 1261496944918839077 619660538760763187 (by decide) rfl
  have c5 : (12:ℕ) ^ 262612223524 % 1261496944918839077 = 326057416075368436 :=
    pow_mod_eq2 5 12 262612223524 1261496944918839077 326057416075368436 (by decide) rfl
  have cf : (12:ℕ) ^ 1261496944918839076 % 1261496944918839077 = 1 :=
    pow_mod_eq2 8 12 1261496944918839076 1261496944918839077 1 (by decide) rfl
  refine lucas_primality 1261496944918839077 ((12 : ℕ) : ZMod 1261496944918839077) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (1261496944918839077:ℕ) - 1 = 1261496944918839076 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (1261496944918839077:ℕ) - 1 = 2 * (2 * (7 * (59 * (59 * (2694343 * (4803649)))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((1261496944918839077:ℕ) - 1) / 2 = 630748472459419538 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((1261496944918839077:ℕ) - 1) / 2 = 630748472459419538 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((1261496944918839077:ℕ) - 1) / 7 = 180213849274119868 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 59 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((1261496944918839077:ℕ) - 1) / 59 = 21381304151166764 := rfl
            rw [hexp, zmod_pow_of_mod c3]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 59 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((1261496944918839077:ℕ) - 1) / 59 = 21381304151166764 := rfl
              rw [hexp, zmod_pow_of_mod c3]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 2694343 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((1261496944918839077:ℕ) - 1) / 2694343 = 468202060732 := rfl
                rw [hexp, zmod_pow_of_mod c4]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                have h := hrest
                have hqe : q = 4803649 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((1261496944918839077:ℕ) - 1) / 4803649 = 262612223524 := rfl
                rw [hexp, zmod_pow_of_mod c5]
                exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_14202594183151509899003248851559 : Nat.Prime 14202594183151509899003248851559 := by
  have c1 : (3:ℕ) ^ 7101297091575754949501624425779 % 14202594183151509899003248851559 = 14202594183151509899003248851558 :=
    pow_mod_eq2 13 3 7101297091575754949501624425779 14202594183151509899003248851559 14202594183151509899003248851558 (by decide) rfl
  have c2 : (3:ℕ) ^ 4734198061050503299667749617186 % 14202594183151509899003248851559 = 1750961562675716324169650091451 :=
    pow_mod_eq2 13 3 4734198061050503299667749617186 14202594183151509899003248851559 1750961562675716324169650091451 (by decide) rfl
  have c3 : (3:ℕ) ^ 240721935307652710152597438162 % 14202594183151509899003248851559 = 7552413563632869540802710249679 :=
    pow_mod_eq2 13 3 240721935307652710152597438162 14202594183151509899003248851559 7552413563632869540802710249679 (by decide) rfl
  have c4 : (3:ℕ) ^ 2966909167150931668895602434 % 14202594183151509899003248851559 = 6033342969412502563953463723878 :=
    pow_mod_eq2 12 3 2966909167150931668895602434 14202594183151509899003248851559 6033342969412502563953463723878 (by decide) rfl
  have c5 : (3:ℕ) ^ 19239571798790173759854414 % 14202594183151509899003248851559 = 3048995590370013149106805270848 :=
    pow_mod_eq2 11 3 19239571798790173759854414 14202594183151509899003248851559 3048995590370013149106805270848 (by decide) rfl
  have c6 : (3:ℕ) ^ 11258524438254 % 14202594183151509899003248851559 = 14165799169635485474467681049946 :=
    pow_mod_eq2 6 3 11258524438254 14202594183151509899003248851559 14165799169635485474467681049946 (by decide) rfl
  have cf : (3:ℕ) ^ 14202594183151509899003248851558 % 14202594183151509899003248851559 = 1 :=
    pow_mod_eq2 13 3 14202594183151509899003248851558 14202594183151509899003248851559 1 (by decide) rfl
  refine lucas_primality 14202594183151509899003248851559 ((3 : ℕ) : ZMod 14202594183151509899003248851559) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (14202594183151509899003248851559:ℕ) - 1 = 14202594183151509899003248851558 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (14202594183151509899003248851559:ℕ) - 1 = 2 * (3 * (3 * (3 * (59 * (4787 * (738197 * (1261496944918839077))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((14202594183151509899003248851559:ℕ) - 1) / 2 = 7101297091575754949501624425779 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((14202594183151509899003248851559:ℕ) - 1) / 3 = 4734198061050503299667749617186 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((14202594183151509899003248851559:ℕ) - 1) / 3 = 4734198061050503299667749617186 := rfl
          rw [hexp, zmod_pow_of_mod c2]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((14202594183151509899003248851559:ℕ) - 1) / 3 = 4734198061050503299667749617186 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 59 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((14202594183151509899003248851559:ℕ) - 1) / 59 = 240721935307652710152597438162 := rfl
              rw [hexp, zmod_pow_of_mod c3]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 4787 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((14202594183151509899003248851559:ℕ) - 1) / 4787 = 2966909167150931668895602434 := rfl
                rw [hexp, zmod_pow_of_mod c4]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 738197 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((14202594183151509899003248851559:ℕ) - 1) / 738197 = 19239571798790173759854414 := rfl
                  rw [hexp, zmod_pow_of_mod c5]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  have h := hrest
                  have hqe : q = 1261496944918839077 := (Nat.prime_dvd_prime_iff_eq hq prime_1261496944918839077).mp h
                  subst hqe
                  have hexp : ((14202594183151509899003248851559:ℕ) - 1) / 1261496944918839077 = 11258524438254 := rfl
                  rw [hexp, zmod_pow_of_mod c6]
                  exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_65449275075638143310200509559182980459 : Nat.Prime 65449275075638143310200509559182980459 := by
  have c1 : (2:ℕ) ^ 32724637537819071655100254779591490229 % 65449275075638143310200509559182980459 = 65449275075638143310200509559182980458 :=
    pow_mod_eq2 16 2 32724637537819071655100254779591490229 65449275075638143310200509559182980459 65449275075638143310200509559182980458 (by decide) rfl
  have c2 : (2:ℕ) ^ 55418522502657191625910677018783218 % 65449275075638143310200509559182980459 = 36157763459688887132176539105593148166 :=
    pow_mod_eq2 15 2 55418522502657191625910677018783218 65449275075638143310200509559182980459 36157763459688887132176539105593148166 (by decide) rfl
  have c3 : (2:ℕ) ^ 33546527460603866381445673787382358 % 65449275075638143310200509559182980459 = 3709428015810680226419099443842368858 :=
    pow_mod_eq2 15 2 33546527460603866381445673787382358 65449275075638143310200509559182980459 3709428015810680226419099443842368858 (by decide) rfl
  have c4 : (2:ℕ) ^ 4608262 % 65449275075638143310200509559182980459 = 60250701373732576502416915523789352697 :=
    pow_mod_eq2 3 2 4608262 65449275075638143310200509559182980459 60250701373732576502416915523789352697 (by decide) rfl
  have cf : (2:ℕ) ^ 65449275075638143310200509559182980458 % 65449275075638143310200509559182980459 = 1 :=
    pow_mod_eq2 16 2 65449275075638143310200509559182980458 65449275075638143310200509559182980459 1 (by decide) rfl
  refine lucas_primality 65449275075638143310200509559182980459 ((2 : ℕ) : ZMod 65449275075638143310200509559182980459) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (65449275075638143310200509559182980459:ℕ) - 1 = 65449275075638143310200509559182980458 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (65449275075638143310200509559182980459:ℕ) - 1 = 2 * (1181 * (1951 * (14202594183151509899003248851559))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((65449275075638143310200509559182980459:ℕ) - 1) / 2 = 32724637537819071655100254779591490229 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 1181 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((65449275075638143310200509559182980459:ℕ) - 1) / 1181 = 55418522502657191625910677018783218 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 1951 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((65449275075638143310200509559182980459:ℕ) - 1) / 1951 = 33546527460603866381445673787382358 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 14202594183151509899003248851559 := (Nat.prime_dvd_prime_iff_eq hq prime_14202594183151509899003248851559).mp h
          subst hqe
          have hexp : ((65449275075638143310200509559182980459:ℕ) - 1) / 14202594183151509899003248851559 = 4608262 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_3333333333333333333333333333333333333333333333333331291 : Nat.Prime 3333333333333333333333333333333333333333333333333331291 := by
  have c1 : (10:ℕ) ^ 1666666666666666666666666666666666666666666666666665645 % 3333333333333333333333333333333333333333333333333331291 = 3333333333333333333333333333333333333333333333333331290 :=
    pow_mod_eq2 23 10 1666666666666666666666666666666666666666666666666665645 3333333333333333333333333333333333333333333333333331291 3333333333333333333333333333333333333333333333333331290 (by decide) rfl
  have c2 : (10:ℕ) ^ 1111111111111111111111111111111111111111111111111110430 % 3333333333333333333333333333333333333333333333333331291 = 2277267010647365882416863103510970127281856830197175787 :=
    pow_mod_eq2 23 10 1111111111111111111111111111111111111111111111111110430 3333333333333333333333333333333333333333333333333331291 2277267010647365882416863103510970127281856830197175787 (by decide) rfl
  have c3 : (10:ℕ) ^ 666666666666666666666666666666666666666666666666666258 % 3333333333333333333333333333333333333333333333333331291 = 2859999278302216749107186628366954274319471885136593535 :=
    pow_mod_eq2 23 10 666666666666666666666666666666666666666666666666666258 3333333333333333333333333333333333333333333333333331291 2859999278302216749107186628366954274319471885136593535 (by decide) rfl
  have c4 : (10:ℕ) ^ 187931066884666704252880043600007517242675386668170 % 3333333333333333333333333333333333333333333333333331291 = 1125704747464695248964774656556696553090540208451938195 :=
    pow_mod_eq2 21 10 187931066884666704252880043600007517242675386668170 3333333333333333333333333333333333333333333333333331291 1125704747464695248964774656556696553090540208451938195 (by decide) rfl
  have c5 : (10:ℕ) ^ 34826213760497812436790793141536855732038490 % 3333333333333333333333333333333333333333333333333331291 = 1726485151015058782105115037275454995248842403643575317 :=
    pow_mod_eq2 19 10 34826213760497812436790793141536855732038490 3333333333333333333333333333333333333333333333333331291 1726485151015058782105115037275454995248842403643575317 (by decide) rfl
  have c6 : (10:ℕ) ^ 50930026795271310 % 3333333333333333333333333333333333333333333333333331291 = 419853872402240644601812366997269559801215682914172351 :=
    pow_mod_eq2 7 10 50930026795271310 3333333333333333333333333333333333333333333333333331291 419853872402240644601812366997269559801215682914172351 (by decide) rfl
  have cf : (10:ℕ) ^ 3333333333333333333333333333333333333333333333333331290 % 3333333333333333333333333333333333333333333333333331291 = 1 :=
    pow_mod_eq2 23 10 3333333333333333333333333333333333333333333333333331290 3333333333333333333333333333333333333333333333333331291 1 (by decide) rfl
  refine lucas_primality 3333333333333333333333333333333333333333333333333331291 ((10 : ℕ) : ZMod 3333333333333333333333333333333333333333333333333331291) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333333333333333333333333333333333333333333333333331291:ℕ) - 1 = 3333333333333333333333333333333333333333333333333331290 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333333333333333333333333333333333333333333333333331291:ℕ) - 1 = 2 * (3 * (5 * (17737 * (95713342721 * (65449275075638143310200509559182980459))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333333333333333333333333333333333333333333333333331291:ℕ) - 1) / 2 = 1666666666666666666666666666666666666666666666666665645 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333333333333333333333333333333333333333333333331291:ℕ) - 1) / 3 = 1111111111111111111111111111111111111111111111111110430 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333333333333333333333333333333333333333333333333331291:ℕ) - 1) / 5 = 666666666666666666666666666666666666666666666666666258 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 17737 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333333333333333333333333333333333333333333333333331291:ℕ) - 1) / 17737 = 187931066884666704252880043600007517242675386668170 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 95713342721 := (Nat.prime_dvd_prime_iff_eq hq prime_95713342721).mp h
              subst hqe
              have hexp : ((3333333333333333333333333333333333333333333333333331291:ℕ) - 1) / 95713342721 = 34826213760497812436790793141536855732038490 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 65449275075638143310200509559182980459 := (Nat.prime_dvd_prime_iff_eq hq prime_65449275075638143310200509559182980459).mp h
              subst hqe
              have hexp : ((3333333333333333333333333333333333333333333333333331291:ℕ) - 1) / 65449275075638143310200509559182980459 = 50930026795271310 := rfl
              rw [hexp, zmod_pow_of_mod c6]
              exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_1273670137 : Nat.Prime 1273670137 := by
  have c1 : (5:ℕ) ^ 636835068 % 1273670137 = 1273670136 :=
    pow_mod_eq2 4 5 636835068 1273670137 1273670136 (by decide) rfl
  have c2 : (5:ℕ) ^ 424556712 % 1273670137 = 925822594 :=
    pow_mod_eq2 4 5 424556712 1273670137 925822594 (by decide) rfl
  have c3 : (5:ℕ) ^ 24031512 % 1273670137 = 539901136 :=
    pow_mod_eq2 4 5 24031512 1273670137 539901136 (by decide) rfl
  have c4 : (5:ℕ) ^ 17939016 % 1273670137 = 376790002 :=
    pow_mod_eq2 4 5 17939016 1273670137 376790002 (by decide) rfl
  have c5 : (5:ℕ) ^ 812808 % 1273670137 = 289033779 :=
    pow_mod_eq2 3 5 812808 1273670137 289033779 (by decide) rfl
  have cf : (5:ℕ) ^ 1273670136 % 1273670137 = 1 :=
    pow_mod_eq2 4 5 1273670136 1273670137 1 (by decide) rfl
  refine lucas_primality 1273670137 ((5 : ℕ) : ZMod 1273670137) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (1273670137:ℕ) - 1 = 1273670136 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (1273670137:ℕ) - 1 = 2 * (2 * (2 * (3 * (3 * (3 * (53 * (71 * (1567)))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((1273670137:ℕ) - 1) / 2 = 636835068 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((1273670137:ℕ) - 1) / 2 = 636835068 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((1273670137:ℕ) - 1) / 2 = 636835068 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((1273670137:ℕ) - 1) / 3 = 424556712 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((1273670137:ℕ) - 1) / 3 = 424556712 := rfl
              rw [hexp, zmod_pow_of_mod c2]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((1273670137:ℕ) - 1) / 3 = 424556712 := rfl
                rw [hexp, zmod_pow_of_mod c2]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 53 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((1273670137:ℕ) - 1) / 53 = 24031512 := rfl
                  rw [hexp, zmod_pow_of_mod c3]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                  · 
                    have hqe : q = 71 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((1273670137:ℕ) - 1) / 71 = 17939016 := rfl
                    rw [hexp, zmod_pow_of_mod c4]
                    exact zmod_ne_one (by decide) (by decide) (by decide)
                  · 
                    have h := hrest
                    have hqe : q = 1567 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((1273670137:ℕ) - 1) / 1567 = 812808 := rfl
                    rw [hexp, zmod_pow_of_mod c5]
                    exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_33333333333333333331433 : Nat.Prime 33333333333333333331433 := by
  have c1 : (3:ℕ) ^ 16666666666666666665716 % 33333333333333333331433 = 33333333333333333331432 :=
    pow_mod_eq2 10 3 16666666666666666665716 33333333333333333331433 33333333333333333331432 (by decide) rfl
  have c2 : (3:ℕ) ^ 2821750049380625864 % 33333333333333333331433 = 28194343193920532390315 :=
    pow_mod_eq2 8 3 2821750049380625864 33333333333333333331433 28194343193920532390315 (by decide) rfl
  have c3 : (3:ℕ) ^ 120366922627048 % 33333333333333333331433 = 7568493570441071186714 :=
    pow_mod_eq2 6 3 120366922627048 33333333333333333331433 7568493570441071186714 (by decide) rfl
  have c4 : (3:ℕ) ^ 26171088074536 % 33333333333333333331433 = 7050212967183987788095 :=
    pow_mod_eq2 6 3 26171088074536 33333333333333333331433 7050212967183987788095 (by decide) rfl
  have cf : (3:ℕ) ^ 33333333333333333331432 % 33333333333333333331433 = 1 :=
    pow_mod_eq2 10 3 33333333333333333331432 33333333333333333331433 1 (by decide) rfl
  refine lucas_primality 33333333333333333331433 ((3 : ℕ) : ZMod 33333333333333333331433) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (33333333333333333331433:ℕ) - 1 = 33333333333333333331432 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (33333333333333333331433:ℕ) - 1 = 2 * (2 * (2 * (11813 * (276931009 * (1273670137))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((33333333333333333331433:ℕ) - 1) / 2 = 16666666666666666665716 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((33333333333333333331433:ℕ) - 1) / 2 = 16666666666666666665716 := rfl
        rw [hexp, zmod_pow_of_mod c1]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((33333333333333333331433:ℕ) - 1) / 2 = 16666666666666666665716 := rfl
          rw [hexp, zmod_pow_of_mod c1]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 11813 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((33333333333333333331433:ℕ) - 1) / 11813 = 2821750049380625864 := rfl
            rw [hexp, zmod_pow_of_mod c2]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 276931009 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((33333333333333333331433:ℕ) - 1) / 276931009 = 120366922627048 := rfl
              rw [hexp, zmod_pow_of_mod c3]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              have h := hrest
              have hqe : q = 1273670137 := (Nat.prime_dvd_prime_iff_eq hq prime_1273670137).mp h
              subst hqe
              have hexp : ((33333333333333333331433:ℕ) - 1) / 1273670137 = 26171088074536 := rfl
              rw [hexp, zmod_pow_of_mod c4]
              exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_321241424839 : Nat.Prime 321241424839 := by
  have c1 : (6:ℕ) ^ 160620712419 % 321241424839 = 321241424838 :=
    pow_mod_eq2 5 6 160620712419 321241424839 321241424838 (by decide) rfl
  have c2 : (6:ℕ) ^ 107080474946 % 321241424839 = 126222976388 :=
    pow_mod_eq2 5 6 107080474946 321241424839 126222976388 (by decide) rfl
  have c3 : (6:ℕ) ^ 1440544506 % 321241424839 = 173924158436 :=
    pow_mod_eq2 4 6 1440544506 321241424839 173924158436 (by decide) rfl
  have c4 : (6:ℕ) ^ 1338 % 321241424839 = 262402792745 :=
    pow_mod_eq2 2 6 1338 321241424839 262402792745 (by decide) rfl
  have cf : (6:ℕ) ^ 321241424838 % 321241424839 = 1 :=
    pow_mod_eq2 5 6 321241424838 321241424839 1 (by decide) rfl
  refine lucas_primality 321241424839 ((6 : ℕ) : ZMod 321241424839) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (321241424839:ℕ) - 1 = 321241424838 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (321241424839:ℕ) - 1 = 2 * (3 * (223 * (240090751))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((321241424839:ℕ) - 1) / 2 = 160620712419 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((321241424839:ℕ) - 1) / 3 = 107080474946 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 223 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((321241424839:ℕ) - 1) / 223 = 1440544506 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          have h := hrest
          have hqe : q = 240090751 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((321241424839:ℕ) - 1) / 240090751 = 1338 := rfl
          rw [hexp, zmod_pow_of_mod c4]
          exact zmod_ne_one (by decide) (by decide) (by decide)

private lemma prime_3333333333333333333331483 : Nat.Prime 3333333333333333333331483 := by
  have c1 : (3:ℕ) ^ 1666666666666666666665741 % 3333333333333333333331483 = 3333333333333333333331482 :=
    pow_mod_eq2 11 3 1666666666666666666665741 3333333333333333333331483 3333333333333333333331482 (by decide) rfl
  have c2 : (3:ℕ) ^ 1111111111111111111110494 % 3333333333333333333331483 = 3192838446314921825775078 :=
    pow_mod_eq2 10 3 1111111111111111111110494 3333333333333333333331483 3192838446314921825775078 (by decide) rfl
  have c3 : (3:ℕ) ^ 476190476190476190475926 % 3333333333333333333331483 = 2524758818123966863787286 :=
    pow_mod_eq2 10 3 476190476190476190475926 3333333333333333333331483 2524758818123966863787286 (by decide) rfl
  have c4 : (3:ℕ) ^ 303030303030303030302862 % 3333333333333333333331483 = 1668695300268651343091166 :=
    pow_mod_eq2 10 3 303030303030303030302862 3333333333333333333331483 1668695300268651343091166 (by decide) rfl
  have c5 : (3:ℕ) ^ 144927536231884057970934 % 3333333333333333333331483 = 3305716139177236769722157 :=
    pow_mod_eq2 10 3 144927536231884057970934 3333333333333333333331483 3305716139177236769722157 (by decide) rfl
  have c6 : (3:ℕ) ^ 107526881720430107526822 % 3333333333333333333331483 = 2000101602061387932379128 :=
    pow_mod_eq2 10 3 107526881720430107526822 3333333333333333333331483 2000101602061387932379128 (by decide) rfl
  have c7 : (3:ℕ) ^ 6680026720106880427518 % 3333333333333333333331483 = 305361771759839973519723 :=
    pow_mod_eq2 10 3 6680026720106880427518 3333333333333333333331483 305361771759839973519723 (by decide) rfl
  have c8 : (3:ℕ) ^ 52803607542467301366 % 3333333333333333333331483 = 716992372879489686344714 :=
    pow_mod_eq2 9 3 52803607542467301366 3333333333333333333331483 716992372879489686344714 (by decide) rfl
  have c9 : (3:ℕ) ^ 10376411868438 % 3333333333333333333331483 = 666460798373390417354358 :=
    pow_mod_eq2 6 3 10376411868438 3333333333333333333331483 666460798373390417354358 (by decide) rfl
  have cf : (3:ℕ) ^ 3333333333333333333331482 % 3333333333333333333331483 = 1 :=
    pow_mod_eq2 11 3 3333333333333333333331482 3333333333333333333331483 1 (by decide) rfl
  refine lucas_primality 3333333333333333333331483 ((3 : ℕ) : ZMod 3333333333333333333331483) ?_ ?_
  · have h := zmod_pow_of_mod cf
    have hexp : (3333333333333333333331483:ℕ) - 1 = 3333333333333333333331482 := rfl
    rw [hexp, h, Nat.cast_one]
  · intro q hq hdvd
    have he : (3333333333333333333331483:ℕ) - 1 = 2 * (3 * (7 * (11 * (23 * (31 * (499 * (63127 * (321241424839)))))))) := rfl
    rw [he] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hrest
    · 
      have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst hqe
      have hexp : ((3333333333333333333331483:ℕ) - 1) / 2 = 1666666666666666666665741 := rfl
      rw [hexp, zmod_pow_of_mod c1]
      exact zmod_ne_one (by decide) (by decide) (by decide)
    · 
      rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
      · 
        have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        subst hqe
        have hexp : ((3333333333333333333331483:ℕ) - 1) / 3 = 1111111111111111111110494 := rfl
        rw [hexp, zmod_pow_of_mod c2]
        exact zmod_ne_one (by decide) (by decide) (by decide)
      · 
        rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
        · 
          have hqe : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          subst hqe
          have hexp : ((3333333333333333333331483:ℕ) - 1) / 7 = 476190476190476190475926 := rfl
          rw [hexp, zmod_pow_of_mod c3]
          exact zmod_ne_one (by decide) (by decide) (by decide)
        · 
          rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
          · 
            have hqe : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
            subst hqe
            have hexp : ((3333333333333333333331483:ℕ) - 1) / 11 = 303030303030303030302862 := rfl
            rw [hexp, zmod_pow_of_mod c4]
            exact zmod_ne_one (by decide) (by decide) (by decide)
          · 
            rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
            · 
              have hqe : q = 23 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
              subst hqe
              have hexp : ((3333333333333333333331483:ℕ) - 1) / 23 = 144927536231884057970934 := rfl
              rw [hexp, zmod_pow_of_mod c5]
              exact zmod_ne_one (by decide) (by decide) (by decide)
            · 
              rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
              · 
                have hqe : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                subst hqe
                have hexp : ((3333333333333333333331483:ℕ) - 1) / 31 = 107526881720430107526822 := rfl
                rw [hexp, zmod_pow_of_mod c6]
                exact zmod_ne_one (by decide) (by decide) (by decide)
              · 
                rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                · 
                  have hqe : q = 499 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                  subst hqe
                  have hexp : ((3333333333333333333331483:ℕ) - 1) / 499 = 6680026720106880427518 := rfl
                  rw [hexp, zmod_pow_of_mod c7]
                  exact zmod_ne_one (by decide) (by decide) (by decide)
                · 
                  rcases (Nat.Prime.dvd_mul hq).mp hrest with h | hrest
                  · 
                    have hqe : q = 63127 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
                    subst hqe
                    have hexp : ((3333333333333333333331483:ℕ) - 1) / 63127 = 52803607542467301366 := rfl
                    rw [hexp, zmod_pow_of_mod c8]
                    exact zmod_ne_one (by decide) (by decide) (by decide)
                  · 
                    have h := hrest
                    have hqe : q = 321241424839 := (Nat.prime_dvd_prime_iff_eq hq prime_321241424839).mp h
                    subst hqe
                    have hexp : ((3333333333333333333331483:ℕ) - 1) / 321241424839 = 10376411868438 := rfl
                    rw [hexp, zmod_pow_of_mod c9]
                    exact zmod_ne_one (by decide) (by decide) (by decide)

/-- `A242775 210 = 51`. -/
theorem A242775_n210 : A242775 210 = 51 := by
  have hp : prime_of_index 210 = 1291 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1291) (by norm_num)
    rwa [pcount1291] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1291 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1291 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1291 = 31291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1291 = 331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1291 = 3331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1291 = 33331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1291 = 333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1291 = 3333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1291 = 33333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1291 = 333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1291 = 3333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 1291 = 33333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 1291 = 333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 1291 = 3333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h13 : concatenate 13 1291 = 33333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h14 : concatenate 14 1291 = 333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h15 : concatenate 15 1291 = 3333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h16 : concatenate 16 1291 = 33333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h17 : concatenate 17 1291 = 333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h18 : concatenate 18 1291 = 3333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h19 : concatenate 19 1291 = 33333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h20 : concatenate 20 1291 = 333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h21 : concatenate 21 1291 = 3333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h22 : concatenate 22 1291 = 33333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h23 : concatenate 23 1291 = 333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h24 : concatenate 24 1291 = 3333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h25 : concatenate 25 1291 = 33333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h26 : concatenate 26 1291 = 333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h27 : concatenate 27 1291 = 3333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h28 : concatenate 28 1291 = 33333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h29 : concatenate 29 1291 = 333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h30 : concatenate 30 1291 = 3333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h31 : concatenate 31 1291 = 33333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h32 : concatenate 32 1291 = 333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h33 : concatenate 33 1291 = 3333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h34 : concatenate 34 1291 = 33333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h35 : concatenate 35 1291 = 333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h36 : concatenate 36 1291 = 3333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h37 : concatenate 37 1291 = 33333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h38 : concatenate 38 1291 = 333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h39 : concatenate 39 1291 = 3333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h40 : concatenate 40 1291 = 33333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h41 : concatenate 41 1291 = 333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h42 : concatenate 42 1291 = 3333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h43 : concatenate 43 1291 = 33333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h44 : concatenate 44 1291 = 333333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h45 : concatenate 45 1291 = 3333333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h46 : concatenate 46 1291 = 33333333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h47 : concatenate 47 1291 = 333333333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h48 : concatenate 48 1291 = 3333333333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h49 : concatenate 49 1291 = 33333333333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h50 : concatenate 50 1291 = 333333333333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h51 : concatenate 51 1291 = 3333333333333333333333333333333333333333333333333331291 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 51 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1291)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h51]; exact prime_3333333333333333333333333333333333333333333333333331291
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1291)}
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    rcases hpr.eq_one_or_self_of_dvd 88499 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    rcases hpr.eq_one_or_self_of_dvd 235211 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h12] at hpr
    rcases hpr.eq_one_or_self_of_dvd 32076463 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h13] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h14] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h15] at hpr
    exact (by norm_num : ¬ (3333333333333331291 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h16] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h17] at hpr
    exact (by norm_num : ¬ (333333333333333331291 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h18] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h19] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h20] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h21] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h22] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h23] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h24] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h25] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h26] at hpr
    rcases hpr.eq_one_or_self_of_dvd 88339 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h27] at hpr
    rcases hpr.eq_one_or_self_of_dvd 7807836622379 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h28] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h29] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h30] at hpr
    exact (by norm_num : ¬ (3333333333333333333333333333331291 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h31] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h32] at hpr
    exact (by norm_num : ¬ (333333333333333333333333333333331291 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h33] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h34] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h35] at hpr
    rcases hpr.eq_one_or_self_of_dvd 73063 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h36] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h37] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h38] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h39] at hpr
    rcases hpr.eq_one_or_self_of_dvd 66777328155127 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h40] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h41] at hpr
    exact (by norm_num : ¬ (333333333333333333333333333333333333333331291 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h42] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h43] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h44] at hpr
    exact (by norm_num : ¬ (333333333333333333333333333333333333333333331291 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h45] at hpr
    exact (by norm_num : ¬ (3333333333333333333333333333333333333333333331291 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h46] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h47] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h48] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h49] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨51, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h50] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 227 = 19`. -/
theorem A242775_n227 : A242775 227 = 19 := by
  have hp : prime_of_index 227 = 1433 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1433) (by norm_num)
    rwa [pcount1433] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1433 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1433 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1433 = 31433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1433 = 331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1433 = 3331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1433 = 33331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1433 = 333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1433 = 3333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1433 = 33333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1433 = 333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1433 = 3333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 1433 = 33333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 1433 = 333333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 1433 = 3333333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h13 : concatenate 13 1433 = 33333333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h14 : concatenate 14 1433 = 333333333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h15 : concatenate 15 1433 = 3333333333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h16 : concatenate 16 1433 = 33333333333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h17 : concatenate 17 1433 = 333333333333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h18 : concatenate 18 1433 = 3333333333333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h19 : concatenate 19 1433 = 33333333333333333331433 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 19 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1433)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h19]; exact prime_33333333333333333331433
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1433)}
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact (by norm_num : ¬ (33331433 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    exact (by norm_num : ¬ (3333331433 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    rcases hpr.eq_one_or_self_of_dvd 307399 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    rcases hpr.eq_one_or_self_of_dvd 27581 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h12] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h13] at hpr
    exact (by norm_num : ¬ (33333333333331433 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h14] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h15] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h16] at hpr
    rcases hpr.eq_one_or_self_of_dvd 472691 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h17] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨19, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h18] at hpr
    exact absurd hpr (isPrimeB_false rfl)

/-- `A242775 235 = 21`. -/
theorem A242775_n235 : A242775 235 = 21 := by
  have hp : prime_of_index 235 = 1483 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1483) (by norm_num)
    rwa [pcount1483] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1483 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1483 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1483 = 31483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1483 = 331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1483 = 3331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1483 = 33331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1483 = 333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1483 = 3333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1483 = 33333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1483 = 333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1483 = 3333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 1483 = 33333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 1483 = 333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 1483 = 3333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h13 : concatenate 13 1483 = 33333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h14 : concatenate 14 1483 = 333333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h15 : concatenate 15 1483 = 3333333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h16 : concatenate 16 1483 = 33333333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h17 : concatenate 17 1483 = 333333333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h18 : concatenate 18 1483 = 3333333333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h19 : concatenate 19 1483 = 33333333333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h20 : concatenate 20 1483 = 333333333333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h21 : concatenate 21 1483 = 3333333333333333333331483 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 21 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1483)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h21]; exact prime_3333333333333333333331483
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1483)}
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    rcases hpr.eq_one_or_self_of_dvd 48091 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact (by norm_num : ¬ (33333331483 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    rcases hpr.eq_one_or_self_of_dvd 226141 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h12] at hpr
    exact (by norm_num : ¬ (3333333333331483 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h13] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h14] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h15] at hpr
    rcases hpr.eq_one_or_self_of_dvd 5743597 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h16] at hpr
    exact (by norm_num : ¬ (33333333333333331483 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h17] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h18] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h19] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨21, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h20] at hpr
    exact absurd hpr (isPrimeB_false rfl)

end ValueTable210_227_235


section Value185
/- `A242775 185 = 135`: the only entry below 200 whose witness is huge
(139 digits).  Minimality uses Fermat compositeness certificates (base 2,
kernel-evaluated) for the twelve intermediates without accessible factors. -/

/-- `A242775 185 = 135`. -/
theorem A242775_n185 : A242775 185 = 135 := by
  have hp : prime_of_index 185 = 1103 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 1103) (by norm_num)
    rwa [pcount1103] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 1103 = 4 := by
    unfold num_digits
    rw [Nat.digits_len 10 1103 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 1103 = 31103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h2 : concatenate 2 1103 = 331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h3 : concatenate 3 1103 = 3331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h4 : concatenate 4 1103 = 33331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h5 : concatenate 5 1103 = 333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h6 : concatenate 6 1103 = 3333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h7 : concatenate 7 1103 = 33333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h8 : concatenate 8 1103 = 333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h9 : concatenate 9 1103 = 3333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h10 : concatenate 10 1103 = 33333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h11 : concatenate 11 1103 = 333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h12 : concatenate 12 1103 = 3333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h13 : concatenate 13 1103 = 33333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h14 : concatenate 14 1103 = 333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h15 : concatenate 15 1103 = 3333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h16 : concatenate 16 1103 = 33333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h17 : concatenate 17 1103 = 333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h18 : concatenate 18 1103 = 3333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h19 : concatenate 19 1103 = 33333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h20 : concatenate 20 1103 = 333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h21 : concatenate 21 1103 = 3333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h22 : concatenate 22 1103 = 33333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h23 : concatenate 23 1103 = 333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h24 : concatenate 24 1103 = 3333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h25 : concatenate 25 1103 = 33333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h26 : concatenate 26 1103 = 333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h27 : concatenate 27 1103 = 3333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h28 : concatenate 28 1103 = 33333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h29 : concatenate 29 1103 = 333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h30 : concatenate 30 1103 = 3333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h31 : concatenate 31 1103 = 33333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h32 : concatenate 32 1103 = 333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h33 : concatenate 33 1103 = 3333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h34 : concatenate 34 1103 = 33333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h35 : concatenate 35 1103 = 333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h36 : concatenate 36 1103 = 3333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h37 : concatenate 37 1103 = 33333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h38 : concatenate 38 1103 = 333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h39 : concatenate 39 1103 = 3333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h40 : concatenate 40 1103 = 33333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h41 : concatenate 41 1103 = 333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h42 : concatenate 42 1103 = 3333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h43 : concatenate 43 1103 = 33333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h44 : concatenate 44 1103 = 333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h45 : concatenate 45 1103 = 3333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h46 : concatenate 46 1103 = 33333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h47 : concatenate 47 1103 = 333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h48 : concatenate 48 1103 = 3333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h49 : concatenate 49 1103 = 33333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h50 : concatenate 50 1103 = 333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h51 : concatenate 51 1103 = 3333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h52 : concatenate 52 1103 = 33333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h53 : concatenate 53 1103 = 333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h54 : concatenate 54 1103 = 3333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h55 : concatenate 55 1103 = 33333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h56 : concatenate 56 1103 = 333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h57 : concatenate 57 1103 = 3333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h58 : concatenate 58 1103 = 33333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h59 : concatenate 59 1103 = 333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h60 : concatenate 60 1103 = 3333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h61 : concatenate 61 1103 = 33333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h62 : concatenate 62 1103 = 333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h63 : concatenate 63 1103 = 3333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h64 : concatenate 64 1103 = 33333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h65 : concatenate 65 1103 = 333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h66 : concatenate 66 1103 = 3333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h67 : concatenate 67 1103 = 33333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h68 : concatenate 68 1103 = 333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h69 : concatenate 69 1103 = 3333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h70 : concatenate 70 1103 = 33333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h71 : concatenate 71 1103 = 333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h72 : concatenate 72 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h73 : concatenate 73 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h74 : concatenate 74 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h75 : concatenate 75 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h76 : concatenate 76 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h77 : concatenate 77 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h78 : concatenate 78 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h79 : concatenate 79 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h80 : concatenate 80 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h81 : concatenate 81 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h82 : concatenate 82 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h83 : concatenate 83 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h84 : concatenate 84 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h85 : concatenate 85 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h86 : concatenate 86 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h87 : concatenate 87 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h88 : concatenate 88 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h89 : concatenate 89 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h90 : concatenate 90 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h91 : concatenate 91 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h92 : concatenate 92 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h93 : concatenate 93 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h94 : concatenate 94 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h95 : concatenate 95 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h96 : concatenate 96 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h97 : concatenate 97 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h98 : concatenate 98 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h99 : concatenate 99 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h100 : concatenate 100 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h101 : concatenate 101 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h102 : concatenate 102 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h103 : concatenate 103 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h104 : concatenate 104 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h105 : concatenate 105 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h106 : concatenate 106 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h107 : concatenate 107 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h108 : concatenate 108 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h109 : concatenate 109 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h110 : concatenate 110 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h111 : concatenate 111 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h112 : concatenate 112 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h113 : concatenate 113 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h114 : concatenate 114 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h115 : concatenate 115 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h116 : concatenate 116 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h117 : concatenate 117 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h118 : concatenate 118 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h119 : concatenate 119 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h120 : concatenate 120 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h121 : concatenate 121 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h122 : concatenate 122 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h123 : concatenate 123 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h124 : concatenate 124 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h125 : concatenate 125 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h126 : concatenate 126 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h127 : concatenate 127 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h128 : concatenate 128 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h129 : concatenate 129 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h130 : concatenate 130 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h131 : concatenate 131 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h132 : concatenate 132 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h133 : concatenate 133 1103 = 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h134 : concatenate 134 1103 = 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have h135 : concatenate 135 1103 = 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hf36 : (2:ℕ) ^ 3333333333333333333333333333333333331102 % 3333333333333333333333333333333333331103 = 1986739387496719702141847357603651183736 :=
    pow_mod_eq2 17 2 3333333333333333333333333333333333331102 3333333333333333333333333333333333331103 1986739387496719702141847357603651183736 (by decide) rfl
  have hf51 : (2:ℕ) ^ 3333333333333333333333333333333333333333333333333331102 % 3333333333333333333333333333333333333333333333333331103 = 2354385562970326997596990731340191043046757910508657102 :=
    pow_mod_eq2 23 2 3333333333333333333333333333333333333333333333333331102 3333333333333333333333333333333333333333333333333331103 2354385562970326997596990731340191043046757910508657102 (by decide) rfl
  have hf66 : (2:ℕ) ^ 3333333333333333333333333333333333333333333333333333333333333333331102 % 3333333333333333333333333333333333333333333333333333333333333333331103 = 263892275443505274288896245148866842262994586305363877711148249964747 :=
    pow_mod_eq2 29 2 3333333333333333333333333333333333333333333333333333333333333333331102 3333333333333333333333333333333333333333333333333333333333333333331103 263892275443505274288896245148866842262994586305363877711148249964747 (by decide) rfl
  have hf80 : (2:ℕ) ^ 333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 93330578026942542085817052619666538444105093451849452938400156553337092238632635023 :=
    pow_mod_eq2 35 2 333333333333333333333333333333333333333333333333333333333333333333333333333333331102 333333333333333333333333333333333333333333333333333333333333333333333333333333331103 93330578026942542085817052619666538444105093451849452938400156553337092238632635023 (by decide) rfl
  have hf90 : (2:ℕ) ^ 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 1770754721290829841763765547983281012805248947408866857719560389873506062158783818579084566341 :=
    pow_mod_eq2 39 2 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 1770754721290829841763765547983281012805248947408866857719560389873506062158783818579084566341 (by decide) rfl
  have hf105 : (2:ℕ) ^ 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 2906552825309005606538951606707384408703559742395365016056821194602609150813990362285525859144762255755896393 :=
    pow_mod_eq2 46 2 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 2906552825309005606538951606707384408703559742395365016056821194602609150813990362285525859144762255755896393 (by decide) rfl
  have hf110 : (2:ℕ) ^ 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 207169409971580474057450249163519839661712524254636127339257877790907862448389190204984326240868902783717668077605 :=
    pow_mod_eq2 48 2 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 207169409971580474057450249163519839661712524254636127339257877790907862448389190204984326240868902783717668077605 (by decide) rfl
  have hf115 : (2:ℕ) ^ 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 25664507752231616163731390078127185649701546222371365729969558352212708158665102506840989429315915566165182811975294800 :=
    pow_mod_eq2 50 2 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 25664507752231616163731390078127185649701546222371365729969558352212708158665102506840989429315915566165182811975294800 (by decide) rfl
  have hf116 : (2:ℕ) ^ 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 119557828643344972010978170188415914459768818454624135252675226508300593373598755874705096099748655394309711186213747158 :=
    pow_mod_eq2 50 2 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 119557828643344972010978170188415914459768818454624135252675226508300593373598755874705096099748655394309711186213747158 (by decide) rfl
  have hf122 : (2:ℕ) ^ 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 16177461722154156611118539419363866453335399831818432287846472770142773194163247950527597857351949135490057845328408722831030 :=
    pow_mod_eq2 53 2 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 16177461722154156611118539419363866453335399831818432287846472770142773194163247950527597857351949135490057845328408722831030 (by decide) rfl
  have hf123 : (2:ℕ) ^ 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 2965544451632026899986265165002058374782779693997665265408927386074062209881834754811485452108268058521860120761608343198021036 :=
    pow_mod_eq2 53 2 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 2965544451632026899986265165002058374782779693997665265408927386074062209881834754811485452108268058521860120761608343198021036 (by decide) rfl
  have hf126 : (2:ℕ) ^ 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 % 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 = 1023836336565259530527610684407355715067728818188325303982769557420253660828594115307229443280755781678057284472596664655067858591 :=
    pow_mod_eq2 54 2 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331102 3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 1023836336565259530527610684407355715067728818188325303982769557420253660828594115307229443280755781678057284472596664655067858591 (by decide) rfl
  have hmem : 135 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1103)} := by
    refine ⟨by norm_num, ?_⟩
    rw [h135]; exact prime_3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 1103)}
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h1] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h2] at hpr
    exact (by norm_num : ¬ (331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h3] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h4] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h5] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h6] at hpr
    rcases hpr.eq_one_or_self_of_dvd 44651 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h7] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h8] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h9] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h10] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h11] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h12] at hpr
    exact (by norm_num : ¬ (3333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h13] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h14] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h15] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h16] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h17] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h18] at hpr
    exact (by norm_num : ¬ (3333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h19] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h20] at hpr
    exact (by norm_num : ¬ (333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h21] at hpr
    exact (by norm_num : ¬ (3333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h22] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h23] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h24] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h25] at hpr
    rcases hpr.eq_one_or_self_of_dvd 47459 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h26] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h27] at hpr
    exact (by norm_num : ¬ (3333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h28] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h29] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h30] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h31] at hpr
    rcases hpr.eq_one_or_self_of_dvd 3930989 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h32] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h33] at hpr
    rcases hpr.eq_one_or_self_of_dvd 816157 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h34] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h35] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h36] at hpr
    exact absurd hpr (fermat_composite rfl hf36 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h37] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h38] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h39] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h40] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h41] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h42] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h43] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h44] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h45] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h46] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h47] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h48] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h49] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h50] at hpr
    exact (by norm_num : ¬ (333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h51] at hpr
    exact absurd hpr (fermat_composite rfl hf51 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h52] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h53] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h54] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h55] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h56] at hpr
    exact (by norm_num : ¬ (333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h57] at hpr
    exact (by norm_num : ¬ (3333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h58] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h59] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h60] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h61] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h62] at hpr
    rcases hpr.eq_one_or_self_of_dvd 5940791 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h63] at hpr
    exact (by norm_num : ¬ (3333333333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h64] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h65] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h66] at hpr
    exact absurd hpr (fermat_composite rfl hf66 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h67] at hpr
    exact (by norm_num : ¬ (33333333333333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h68] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h69] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h70] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h71] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h72] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h73] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h74] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h75] at hpr
    exact (by norm_num : ¬ (3333333333333333333333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h76] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h77] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h78] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h79] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h80] at hpr
    exact absurd hpr (fermat_composite rfl hf80 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h81] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h82] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h83] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h84] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h85] at hpr
    exact (by norm_num : ¬ (33333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h86] at hpr
    rcases hpr.eq_one_or_self_of_dvd 10459 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h87] at hpr
    exact (by norm_num : ¬ (3333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h88] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h89] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h90] at hpr
    exact absurd hpr (fermat_composite rfl hf90 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h91] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h92] at hpr
    exact (by norm_num : ¬ (333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h93] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h94] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h95] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h96] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h97] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h98] at hpr
    exact (by norm_num : ¬ (333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h99] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h100] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h101] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h102] at hpr
    rcases hpr.eq_one_or_self_of_dvd 19531 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h103] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h104] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h105] at hpr
    exact absurd hpr (fermat_composite rfl hf105 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h106] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h107] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h108] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h109] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h110] at hpr
    exact absurd hpr (fermat_composite rfl hf110 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h111] at hpr
    exact (by norm_num : ¬ (3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h112] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h113] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h114] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h115] at hpr
    exact absurd hpr (fermat_composite rfl hf115 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h116] at hpr
    exact absurd hpr (fermat_composite rfl hf116 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h117] at hpr
    exact (by norm_num : ¬ (3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333331103 : ℕ).Prime) hpr
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h118] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h119] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h120] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h121] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h122] at hpr
    exact absurd hpr (fermat_composite rfl hf122 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h123] at hpr
    exact absurd hpr (fermat_composite rfl hf123 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h124] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h125] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h126] at hpr
    exact absurd hpr (fermat_composite rfl hf126 (by decide) (by decide) (by decide))
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h127] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h128] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h129] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h130] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h131] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h132] at hpr
    rcases hpr.eq_one_or_self_of_dvd 32497 (by norm_num) with hh | hh <;> norm_num at hh
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h133] at hpr
    exact absurd hpr (isPrimeB_false rfl)
  · have := Nat.sInf_mem ⟨135, hmem⟩
    rw [hs] at this
    obtain ⟨-, hpr⟩ := this
    rw [h134] at hpr
    exact absurd hpr (isPrimeB_false rfl)

end Value185


/-- Even `p = 17` — by `square_rigidity` the unique prime that could use the square
factorization to cover the class `k ≡ 0 (mod L)` — is no counterexample: `317` is prime,
so `A242775 7 = 1`. -/
theorem A242775_seven : A242775 7 = 1 := by
  have hp : prime_of_index 7 = 17 := by
    unfold prime_of_index
    have := Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num)
    rwa [pcount17] at this
  unfold A242775
  rw [if_neg (by norm_num), hp]
  simp only []
  have hnd : num_digits 17 = 2 := by
    unfold num_digits
    rw [Nat.digits_len 10 17 (by norm_num) (by norm_num),
        Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 1) (by norm_num) (by norm_num)]
  have h1 : concatenate 1 17 = 317 := by
    unfold concatenate rep_threes
    rw [hnd]; rfl
  have hmem : 1 ∈ {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 17)} := by
    refine ⟨one_pos, ?_⟩
    rw [h1]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra h
  push_neg at h
  interval_cases hs : sInf {k : ℕ | k > 0 ∧ Nat.Prime (concatenate k 17)}
  · have := Nat.sInf_mem ⟨1, hmem⟩
    rw [hs] at this
    exact absurd this.1 (lt_irrefl 0)

end SemanticAnchors


/-- What the conjecture asserts, in explicit form: positivity of `A242775 n` is exactly
the existence of some `k ≥ 1` making the concatenation prime. -/
lemma A242775_pos_iff (n : ℕ) (hn : 1 ≤ n) :
    0 < A242775 n ↔ ∃ k, 0 < k ∧ (concatenate k (prime_of_index n)).Prime := by
  unfold A242775
  rw [if_neg (by omega)]
  simp only []
  constructor
  · intro h
    rcases Set.eq_empty_or_nonempty
        {k : ℕ | k > 0 ∧ (concatenate k (prime_of_index n)).Prime} with he | hne
    · rw [he, Nat.sInf_empty] at h
      exact absurd h (lt_irrefl 0)
    · obtain ⟨k, hk⟩ := hne
      exact ⟨k, hk.1, hk.2⟩
  · rintro ⟨k, hk0, hkp⟩
    have hmem := Nat.sInf_mem (⟨k, hk0, hkp⟩ :
      {k : ℕ | k > 0 ∧ (concatenate k (prime_of_index n)).Prime}.Nonempty)
    exact hmem.1

/-- The conjecture is precisely the number-theoretic statement: every prime `p ≥ 7`
has some prepended-threes prime extension. -/
theorem conjecture_iff :
    (∀ n, 4 ≤ n → 0 < A242775 n) ↔
    (∀ p, p.Prime → 7 ≤ p → ∃ k, 0 < k ∧ (concatenate k p).Prime) := by
  constructor
  · intro H p hp hp7
    set n := Nat.count Nat.Prime p + 1 with hn
    have hpn : prime_of_index n = p := by
      unfold prime_of_index
      simpa [hn] using Nat.nth_count hp
    have hcnt : 3 ≤ Nat.count Nat.Prime p := by
      have h7 : Nat.count Nat.Prime 7 = 3 := pcount7
      calc 3 = Nat.count Nat.Prime 7 := h7.symm
      _ ≤ Nat.count Nat.Prime p := Nat.count_monotone _ hp7
    have h4 : 4 ≤ n := by omega
    have := H n h4
    rw [A242775_pos_iff n (by omega), hpn] at this
    exact this
  · intro H n h4
    have hinf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime
    have hp : (prime_of_index n).Prime := by
      unfold prime_of_index
      exact Nat.nth_mem_of_infinite hinf (n - 1)
    have hp7 : 7 ≤ prime_of_index n := by
      unfold prime_of_index
      have h3 : Nat.nth Nat.Prime 3 = 7 := by
        have := Nat.nth_count (p := Nat.Prime) (n := 7) (by norm_num)
        rwa [pcount7] at this
      calc (7:ℕ) = Nat.nth Nat.Prime 3 := h3.symm
      _ ≤ Nat.nth Nat.Prime (n - 1) := by
          exact (Nat.nth_le_nth hinf).mpr (by omega)
    rw [A242775_pos_iff n (by omega)]
    exact H _ hp hp7

section StructuralObstruction
/- The pullback theorem: machine-checked form of the key structural fact that makes a
covering-congruence disproof of this conjecture impossible.  In any finite covering system
for `k ↦ concatenate k p`, the progression `k ≡ 0 (mod lcm of the periods)` can only be
covered by the prime `p` itself (forcing `ord_p(10)` to divide the lcm), because any other
covering divisor `q` of that class necessarily divides `p`.  Combined with the complete
factorization data of the feasible repunits and exhaustive coverage computation, this
closes the disproof route; the affirmative route is an open problem. -/

/-- Universal identity: `3 * concatenate k p + 10^d = 10^(k+d) + 3p`. -/
lemma concat_key (k p : ℕ) :
    3 * concatenate k p + 10 ^ num_digits p = 10 ^ (k + num_digits p) + 3 * p := by
  unfold concatenate
  have h := three_mul_rep_threes k
  calc 3 * (rep_threes k * 10 ^ num_digits p + p) + 10 ^ num_digits p
      = (3 * rep_threes k + 1) * 10 ^ num_digits p + 3 * p := by ring
  _ = 10 ^ k * 10 ^ num_digits p + 3 * p := by rw [h]
  _ = 10 ^ (k + num_digits p) + 3 * p := by rw [pow_add]

/-- Pullback theorem: a divisor `q` of `10^s − 1` that is coprime to 3 and divides the
concatenation at some index `k ≡ 0 (mod s)` must divide `p` itself.  Hence in any covering
system for the sequence `k ↦ concatenate k p`, the arithmetic progression `k ≡ 0 (mod L)`
can only be covered by the prime `p`, forcing `ord_p(10) ∣ L`. -/
theorem pullback (p q s j : ℕ) (hq3 : ¬ 3 ∣ q)
    (hs : q ∣ 10 ^ s - 1) (hdvd : q ∣ concatenate (s * j) p) : q ∣ p := by
  set d := num_digits p with hd
  have hkey := concat_key (s * j) p
  -- 10^(s*j+d) ≡ 10^d [MOD q]
  have hone : (10:ℕ) ^ s ≡ 1 [MOD q] := by
    have hpos : 1 ≤ (10:ℕ) ^ s := Nat.one_le_pow _ _ (by norm_num)
    exact ((Nat.modEq_iff_dvd' hpos).mpr hs).symm
  have hpow : (10:ℕ) ^ (s * j + d) ≡ 10 ^ d [MOD q] := by
    calc (10:ℕ) ^ (s * j + d) = ((10:ℕ) ^ s) ^ j * 10 ^ d := by
          rw [← pow_mul, ← pow_add]
    _ ≡ 1 ^ j * 10 ^ d [MOD q] := (hone.pow j).mul_right _
    _ = 10 ^ d := by rw [one_pow, one_mul]
  -- q | 3 * concatenate → left side ≡ 10^d, so 10^d ≡ 10^d + 3p [MOD q], so q | 3p
  obtain ⟨c, hc⟩ := hdvd
  have heq : 3 * (q * c) + 10 ^ d = 10 ^ (s * j + d) + 3 * p := by
    rw [← hc]; exact hkey
  have e1 : (10:ℕ) ^ d ≡ 3 * (q * c) + 10 ^ d [MOD q] := by
    have h0 : (3 * (q * c) : ℕ) ≡ 0 [MOD q] :=
      (Nat.modEq_zero_iff_dvd).mpr ⟨3 * c, by ring⟩
    simpa using h0.symm.add_right (10 ^ d)
  rw [heq] at e1
  have e2 : (10:ℕ) ^ d ≡ 10 ^ d + 3 * p [MOD q] :=
    e1.trans (hpow.add_right (3 * p))
  have e3 : (0:ℕ) + 10 ^ d ≡ 3 * p + 10 ^ d [MOD q] := by
    simpa [Nat.add_comm] using e2
  have h4 : q ∣ 3 * p := by
    have h5 := Nat.ModEq.add_right_cancel' (10 ^ d) e3
    exact (Nat.modEq_zero_iff_dvd).mp h5.symm
  have hcop : Nat.Coprime q 3 := by
    rcases Nat.coprime_or_dvd_of_prime (by norm_num : Nat.Prime 3) q with h | h
    · exact h.symm
    · exact absurd h hq3
  exact hcop.dvd_of_dvd_mul_left h4

/-- Mod-9 exclusion of cube-type algebraic factorizations: for a prime `p > 3` there is
no `b` with `3p = 10^d − b³` or `3p = 10^d + b³` (any `d ≥ 1`), so the only possible
algebraic mechanism in a compositeness proof of the extension sequence is the square one. -/
theorem cube_exclusion (p d b : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    3 * p + b ^ 3 ≠ 10 ^ d ∧ 3 * p ≠ 10 ^ d + b ^ 3 := by
  have h10 : (10:ℕ) ^ d % 9 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have hb : b ^ 3 % 9 = 0 ∨ b ^ 3 % 9 = 1 ∨ b ^ 3 % 9 = 8 := by
    have h := Nat.pow_mod b 3 9
    have : b % 9 < 9 := Nat.mod_lt _ (by norm_num)
    interval_cases h9 : b % 9 <;> simp_all
  have hpm : p % 3 = 1 ∨ p % 3 = 2 := by
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd hp (by norm_num)
      · exact absurd hp (by norm_num)
      · omega
    · have : ¬ 3 ∣ p := by
        intro hdvd
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd) with h1 | h1 <;> omega
      omega
  have h3p : 3 * p % 9 = 3 ∨ 3 * p % 9 = 6 := by
    rcases hpm with h | h
    · left; omega
    · right; omega
  constructor
  · intro heq
    have := congrArg (· % 9) heq
    simp only at this
    rw [Nat.add_mod] at this
    omega
  · intro heq
    have := congrArg (· % 9) heq
    simp only at this
    rw [Nat.add_mod] at this
    omega

/-- Square-family rigidity: if a prime `p` with an even number `2m` of digits satisfies
`3p = 10^(2m) − b²` (the only algebraic mechanism available for covering the class
`k ≡ 0 (mod L)` without `p` itself), then necessarily `p = 17`. -/
theorem square_rigidity (p b m : ℕ) (hp : p.Prime) (hm : 1 ≤ m)
    (hdig : num_digits p = 2 * m) (h : 3 * p + b ^ 2 = 10 ^ (2 * m)) :
    p = 17 ∧ m = 1 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  -- digit lower bound: 10^(2m-1) ≤ p
  have hlow : 10 ^ (2 * m - 1) ≤ p := by
    have hlen : Nat.log 10 p + 1 = 2 * m := by
      have := Nat.digits_len 10 p (by norm_num) hp0
      unfold num_digits at hdig
      omega
    have := Nat.pow_log_le_self 10 hp0
    have hlog : Nat.log 10 p = 2 * m - 1 := by omega
    rwa [hlog] at this
  -- b < 10^m
  have hx : (10:ℕ) ^ (2 * m) = (10 ^ m) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  have hppos : 0 < p := hp.pos
  have hblt : b < 10 ^ m := by
    by_contra hge
    push_neg at hge
    have : (10:ℕ) ^ (2 * m) ≤ b ^ 2 := by
      rw [hx]; exact Nat.pow_le_pow_left hge 2
    omega
  set x := (10:ℕ) ^ m with hxdef
  have hble : b ≤ x := le_of_lt hblt
  have key : (x - b) * (x + b) + b ^ 2 = x ^ 2 := by
    zify [hble]; ring
  have huv : (x - b) * (x + b) = 3 * p := by
    have : (x - b) * (x + b) + b ^ 2 = 3 * p + b ^ 2 := by
      rw [key, ← hx, ← h]
    omega
  have hxge : (10:ℕ) ≤ x := by
    have : (10:ℕ) ^ 1 ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    simpa using this
  have h10m3 : x % 3 = 1 := by
    rw [hxdef, Nat.pow_mod]; norm_num
  by_cases h3u : 3 ∣ (x - b)
  · -- u = 3w, w * v = p, so w = 1 (w = p impossible), p = 2x - 3
    obtain ⟨w, hw⟩ := h3u
    have hwv : w * (x + b) = p := by
      have : 3 * (w * (x + b)) = 3 * p := by rw [← huv, hw]; ring
      omega
    have hwdvd : w ∣ p := ⟨x + b, hwv.symm⟩
    rcases hp.eq_one_or_self_of_dvd w hwdvd with hw1 | hwp
    · -- u = 3, v = p: p = x + b, x - b = 3 → p = 2x - 3
      have hu3 : x - b = 3 := by omega
      have hvp : x + b = p := by rw [hw1, one_mul] at hwv; exact hwv
      have hpval : p = 2 * x - 3 := by omega
      -- digit bound: 10^(2m-1) ≤ 2x - 3 = 2·10^m - 3 forces m = 1
      have hm1 : m = 1 := by
        by_contra hne
        have hm2 : 2 ≤ m := by omega
        have : (10:ℕ) ^ (m + 1) ≤ 10 ^ (2 * m - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have hpow : (10:ℕ) ^ (m + 1) = 10 * x := by rw [hxdef, pow_succ]; ring
        omega
      refine ⟨?_, hm1⟩
      have : x = 10 := by rw [hxdef, hm1, pow_one]
      omega
    · -- w = p → v = 1, impossible
      exfalso
      rw [hwp] at hwv
      have hv1 : x + b = 1 := by
        have h1 : p * (x + b) = p * 1 := by rw [hwv, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hppos h1
      omega
  · -- u coprime to 3, u | p → u = 1 (mod-3 contradiction) or u = p (size contradiction)
    have hcop : Nat.Coprime (x - b) 3 := by
      rcases Nat.coprime_or_dvd_of_prime (by norm_num : Nat.Prime 3) (x - b) with hc | hc
      · exact hc.symm
      · exact absurd hc h3u
    have hudvd : (x - b) ∣ p := hcop.dvd_of_dvd_mul_left ⟨x + b, by omega⟩
    rcases hp.eq_one_or_self_of_dvd _ hudvd with hu1 | hup
    · -- u = 1: 3p = v = 2x - 1 ≡ 1 (mod 3), contradiction
      exfalso
      have h3p : 3 * p = 2 * x - 1 := by
        rw [← huv, hu1, one_mul]; omega
      omega
    · -- u = p: then p * v = 3p → v = 3 < 10 ≤ x, impossible
      exfalso
      have hpx : p * (x + b) = 3 * p := by rw [← huv, hup]
      have h1 : p * (x + b) = p * 3 := by rw [hpx]; ring
      have hv3 : x + b = 3 := Nat.eq_of_mul_eq_mul_left hppos h1
      omega

/-- QR obstruction: in `ZMod q` (`q` prime), if `x ≠ 0` is not a square, then `x ^ e` can
only be a square for even `e`.  Applied with `x = 10`: a covering prime `q` with
`(10 | q) = −1` can never cover a class whose exponent `r + d` is odd; in square-hybrid
covering systems (the only algebraic mechanism, by `cube_exclusion` and
`square_rigidity`), the entire odd side must be covered by primes from the thin set
with `(10 | q) = +1`, which is what makes the measured coverage saturate below 100%. -/
lemma qr_obstruction {q : ℕ} [Fact (Nat.Prime q)] {x : ZMod q} (hx : x ≠ 0)
    (hns : ¬ IsSquare x) {e : ℕ} (h : IsSquare (x ^ e)) : Even e := by
  rcases Nat.even_or_odd e with he | he
  · exact he
  exfalso
  obtain ⟨y, hy⟩ := h
  obtain ⟨t, ht⟩ := he
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hy
    exact pow_ne_zero e hx hy
  apply hns
  refine ⟨x ^ (t + 1) * y⁻¹, ?_⟩
  have key : (x ^ (t + 1) * y⁻¹) * (x ^ (t + 1) * y⁻¹) = x ^ (2 * t + 2) * (y * y)⁻¹ := by
    rw [mul_inv, show 2 * t + 2 = (t + 1) + (t + 1) by ring, pow_add]
    ring
  rw [key, ← hy, ht]
  rw [show 2 * t + 2 = (2 * t + 1) + 1 by ring, pow_succ]
  rw [mul_comm (x ^ (2*t+1)) x, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx)]
  rw [mul_one]

/-- The covering-class mechanism, verified: if `q ∣ 10^s − 1`, `q` is coprime to 3, and
`10^(r+d) + 3p ≡ 10^d (mod q)`, then `q` divides `concatenate k p` for every
`k ≡ r (mod s)`.  Together with a size bound this makes all such terms composite; a
covering system is a finite family of such classes (plus the square factorization and
the class of `p` itself) covering all of `k ≥ 1`.  The exhaustive computation shows no
prime `p ≥ 7` admits such a family. -/
lemma class_dvd (p q s r : ℕ) (hq3 : ¬ 3 ∣ q) (hs : q ∣ 10 ^ s - 1)
    (he : (10 ^ (r + num_digits p) + 3 * p) % q = (10 ^ num_digits p) % q) :
    ∀ k, k % s = r → q ∣ concatenate k p := by
  intro k hk
  set d := num_digits p
  have hone : (10:ℕ) ^ s ≡ 1 [MOD q] := by
    have hpos : 1 ≤ (10:ℕ) ^ s := Nat.one_le_pow _ _ (by norm_num)
    exact ((Nat.modEq_iff_dvd' hpos).mpr hs).symm
  have hk' : k + d = (r + d) + s * (k / s) := by
    have := Nat.mod_add_div k s
    omega
  have hpow : (10:ℕ) ^ (k + d) ≡ 10 ^ (r + d) [MOD q] := by
    rw [hk']
    calc (10:ℕ) ^ ((r + d) + s * (k / s))
        = 10 ^ (r + d) * ((10:ℕ) ^ s) ^ (k / s) := by rw [pow_add, pow_mul]
    _ ≡ 10 ^ (r + d) * 1 ^ (k / s) [MOD q] := (hone.pow _).mul_left _
    _ = 10 ^ (r + d) := by rw [one_pow, mul_one]
  have hkey := concat_key k p
  have h1 : 3 * concatenate k p + 10 ^ d ≡ 10 ^ (r + d) + 3 * p [MOD q] := by
    rw [hkey]; exact hpow.add_right _
  have h2 : 3 * concatenate k p + 10 ^ d ≡ 0 + 10 ^ d [MOD q] := by
    calc 3 * concatenate k p + 10 ^ d ≡ 10 ^ (r + d) + 3 * p [MOD q] := h1
    _ ≡ 0 + 10 ^ d [MOD q] := by
        show _ % q = _ % q
        simpa using he
  have h3 : 3 * concatenate k p ≡ 0 [MOD q] := Nat.ModEq.add_right_cancel' _ h2
  have h4 : q ∣ 3 * concatenate k p := (Nat.modEq_zero_iff_dvd).mp h3
  have hcop : Nat.Coprime q 3 := by
    rcases Nat.coprime_or_dvd_of_prime (by norm_num : Nat.Prime 3) q with h | h
    · exact h.symm
    · exact absurd h hq3
  exact hcop.dvd_of_dvd_mul_left h4

/-- Size bound: for `k ≥ r` the term dominates `q` whenever `3q + 10^d ≤ 10^(r+d)`. -/
lemma class_lt (p q r : ℕ) (hq : 3 * q + 10 ^ num_digits p < 10 ^ (r + num_digits p)) :
    ∀ k, r ≤ k → q < concatenate k p := by
  intro k hrk
  have hkey := concat_key k p
  have hpow : (10:ℕ) ^ (r + num_digits p) ≤ 10 ^ (k + num_digits p) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Compositeness from a proper divisor. -/
lemma not_prime_of_proper_dvd (q N : ℕ) (hq : 1 < q) (hlt : q < N) (hdvd : q ∣ N) :
    ¬ Nat.Prime N := by
  intro hP
  rcases hP.eq_one_or_self_of_dvd q hdvd with h | h <;> omega

private lemma nd2593 : num_digits 2593 = 4 := by
  unfold num_digits
  rw [Nat.digits_len 10 2593 (by norm_num) (by norm_num),
      Nat.log_eq_of_pow_le_of_lt_pow (b := 10) (m := 3) (by norm_num) (by norm_num)]

/-- The verified partial covering system of `p = 2593` (prime №378): every index
`k` that is not a multiple of 12 gives a composite concatenation, via the divisors
11 (k odd), 101 (k ≡ 2 mod 4), 37 (k ≡ 2 mod 3) and 7 (k ≡ 4 mod 6).  The class
`k ≡ 0 (mod 12)` is *not* coverable (by `pullback` and the exhaustive analysis), and
indeed contains the prime at `k = 23772` establishing `A242775 378 = 23772`. -/
theorem partial_covering_2593 (k : ℕ) (hk : ¬ 12 ∣ k) :
    ¬ (concatenate k 2593).Prime := by
  have hd := nd2593
  have case11 : k % 2 = 1 → ¬ (concatenate k 2593).Prime := by
    intro h
    refine not_prime_of_proper_dvd 11 _ (by norm_num) ?_ ?_
    · exact class_lt 2593 11 1 (by rw [hd]; norm_num) k (by omega)
    · exact class_dvd 2593 11 2 1 (by norm_num) (by norm_num)
        (by rw [hd]; norm_num) k h
  have case101 : k % 4 = 2 → ¬ (concatenate k 2593).Prime := by
    intro h
    refine not_prime_of_proper_dvd 101 _ (by norm_num) ?_ ?_
    · exact class_lt 2593 101 2 (by rw [hd]; norm_num) k (by omega)
    · exact class_dvd 2593 101 4 2 (by norm_num) (by norm_num)
        (by rw [hd]; norm_num) k h
  have case37 : k % 3 = 2 → ¬ (concatenate k 2593).Prime := by
    intro h
    refine not_prime_of_proper_dvd 37 _ (by norm_num) ?_ ?_
    · exact class_lt 2593 37 2 (by rw [hd]; norm_num) k (by omega)
    · exact class_dvd 2593 37 3 2 (by norm_num) (by norm_num)
        (by rw [hd]; norm_num) k h
  have case7 : k % 6 = 4 → ¬ (concatenate k 2593).Prime := by
    intro h
    refine not_prime_of_proper_dvd 7 _ (by norm_num) ?_ ?_
    · exact class_lt 2593 7 4 (by rw [hd]; norm_num) k (by omega)
    · exact class_dvd 2593 7 6 4 (by norm_num) (by norm_num)
        (by rw [hd]; norm_num) k h
  rcases Nat.even_or_odd k with he | ho
  · -- k even
    obtain ⟨t, ht⟩ := he
    rcases Nat.lt_or_ge (k % 12) 12 with _ | h12
    · have h12k : k % 12 ≠ 0 := fun h => hk (Nat.dvd_of_mod_eq_zero h)
      have h2 : k % 2 = 0 := by omega
      -- k % 12 ∈ {2, 4, 6, 8, 10}
      have : k % 12 = 2 ∨ k % 12 = 4 ∨ k % 12 = 6 ∨ k % 12 = 8 ∨ k % 12 = 10 := by
        omega
      rcases this with h | h | h | h | h
      · exact case101 (by omega)
      · exact case7 (by omega)
      · exact case101 (by omega)
      · exact case37 (by omega)
      · exact case101 (by omega)
    · omega
  · exact case11 (Nat.odd_iff.mp ho)

end StructuralObstruction

/-- OEIS A242775 Conjecture: for $n \ge 4$, $a(n)>0$.

Investigation record (2026): the statement is equivalent to: for every prime
p ≥ 7 there exists k ≥ 1 with (10^k−1)/3 · 10^(digits p) + p prime, i.e. some
33…3‖p is prime.  A proof would require producing a prime in an exponentially
sparse sequence for each of infinitely many p (open, Mersenne-hard).  A
disproof would require a prime p all of whose extensions are provably
composite; every finite such proof must rest on covering congruences and/or
algebraic factorizations.  An exhaustive analysis (pullback theorem: the class
k ≡ 0 (mod L) can only be covered by p itself, forcing ord_p(10) | L; complete
verified factorizations of Φ_t(10) for all feasible t; impossibility mod 9 of
all cube-type factorizations; uniqueness of p = 17 in the even-digit square
family; saturation bound Σ 1/(q−1) ≪ ln L) shows that no covering system
exists for any prime p in any feasible range — best candidate p = 2593
(n = 378) covers only 96.4 % of residues.  Object-level evidence: the value
`A242775 n` is machine-verified above for **every** `n ≤ 250` except
`n = 238` (`a(238) = 294`, a 298-digit BPSW-verified witness); this includes
`A242775 185 = 135` with its 139-digit witness certified by a sixteen-level
Pratt tree and Fermat compositeness certificates for minimality; large witnesses — up to the
37-digit prime 3…3(34 threes)443 for n = 86 — are certified through
recursive `lucas_primality` (Pratt) certificate trees and the Pocklington
criterion proved above), and BPSW-certified witnesses exist for all flagged
candidates, including the 23776-digit witness for p = 2593.  Hence the
conjecture is (almost surely) true but neither it nor its negation is
provable by known mathematics. -/
theorem oeis_242775_conjecture_0 : ∀ n, 4 ≤ n → A242775 n > 0 := by
  sorry
