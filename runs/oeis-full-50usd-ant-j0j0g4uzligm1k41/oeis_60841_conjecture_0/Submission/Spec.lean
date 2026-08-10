import FormalConjectures.Util.ProblemImports

open Nat Finset Rat
open scoped BigOperators

/--
A060841: Numerator of $1/\det(M)$ where $M$ is the $n \times n$ matrix with $M[i,j] = 1/\operatorname{lcm}(i,j)$.
The value is $\frac{1}{\det(M)} = \prod_{k=1}^n \frac{k^2}{\phi(k)}$
-/
noncomputable def A060841 (n : ℕ) : ℕ :=
  let val_rat : ℚ := (Icc 1 n).prod (fun k : ℕ => ((k : ℚ) ^ 2) / (k.totient : ℚ))
  val_rat.num.natAbs

/-- The rational value $1/\det(M_n) = \prod_{k=1}^n \frac{k^2}{\phi(k)}$. -/
noncomputable def A060841_val_rat (n : ℕ) : ℚ :=
  (Icc 1 n).prod (fun k : ℕ => ((k : ℚ) ^ 2) / (k.totient : ℚ))

/- ### A computable 3-adic valuation, equal to `padicValNat 3`. -/

/-- Fuel-based 3-adic valuation. -/
def v3f : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _+1, 0 => 0
  | fuel+1, n => if n % 3 = 0 then 1 + v3f fuel (n / 3) else 0

def v3 (n : ℕ) : ℕ := v3f n n

theorem maxPowDiv3_step (n : ℕ) (hn : 0 < n) (h3 : 3 ∣ n) :
    Nat.maxPowDiv 3 n = Nat.maxPowDiv 3 (n/3) + 1 := by
  obtain ⟨m, rfl⟩ := h3
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  have hm : 0 < m := by omega
  exact Nat.maxPowDiv.base_mul_eq_succ (by norm_num) hm

theorem maxPowDiv3_zero_of_not_dvd (n : ℕ) (h3 : ¬ 3 ∣ n) : Nat.maxPowDiv 3 n = 0 := by
  by_contra h
  have hpos : 1 ≤ Nat.maxPowDiv 3 n := Nat.one_le_iff_ne_zero.2 h
  have hdvd : (3:ℕ)^(Nat.maxPowDiv 3 n) ∣ n := Nat.maxPowDiv.pow_dvd 3 n
  have : (3:ℕ)^1 ∣ n := dvd_trans (pow_dvd_pow 3 hpos) hdvd
  simp at this
  exact h3 this

theorem v3f_eq (fuel : ℕ) : ∀ n, n ≤ fuel → v3f fuel n = Nat.maxPowDiv 3 n := by
  induction fuel with
  | zero => intro n hn; interval_cases n; rw [Nat.maxPowDiv.zero]; rfl
  | succ fuel ih =>
    intro n hn
    match n with
    | 0 => rw [Nat.maxPowDiv.zero]; rfl
    | (m+1) =>
      show (if (m+1) % 3 = 0 then 1 + v3f fuel ((m+1)/3) else 0) = Nat.maxPowDiv 3 (m+1)
      by_cases h : (m+1) % 3 = 0
      · rw [if_pos h]
        have h3 : 3 ∣ (m+1) := Nat.dvd_of_mod_eq_zero h
        have hle : (m+1)/3 ≤ fuel := by omega
        rw [ih _ hle, maxPowDiv3_step (m+1) (by omega) h3, Nat.add_comm]
      · rw [if_neg h]
        have hnd : ¬ 3 ∣ (m+1) := fun hd => h (Nat.mod_eq_zero_of_dvd hd)
        exact (maxPowDiv3_zero_of_not_dvd (m+1) hnd).symm

theorem v3_eq (n : ℕ) : v3 n = padicValNat 3 n := by
  rw [padicValNat.padicValNat_eq_maxPowDiv]
  exact v3f_eq n n (le_refl n)

/- ### A fast, kernel-reducible totient, equal to `Nat.totient`. -/

/-- smallest divisor of `n` that is `≥ d`, with a `√`-cutoff, searching `fuel` steps. -/
def sdiv : ℕ → ℕ → ℕ → ℕ
  | 0, d, _ => d
  | fuel+1, d, n => if d ∣ n then d else if n < d*d then n else sdiv fuel (d+1) n

theorem sdiv_succ (fuel d n : ℕ) : sdiv (fuel+1) d n =
    if d ∣ n then d else if n < d*d then n else sdiv fuel (d+1) n := rfl

theorem sdiv_spec : ∀ (fuel d n : ℕ), 2 ≤ d → d ≤ n → n ≤ d + fuel →
    (∀ e, 2 ≤ e → e < d → ¬ e ∣ n) →
    (sdiv fuel d n ∣ n) ∧ (2 ≤ sdiv fuel d n) ∧ (∀ e, 2 ≤ e → e < sdiv fuel d n → ¬ e ∣ n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d n hd hdn hnf hinv
    have heq : d = n := by omega
    subst heq
    exact ⟨dvd_refl _, hd, fun e he1 he2 => hinv e he1 he2⟩
  | succ fuel ih =>
    intro d n hd hdn hnf hinv
    rw [sdiv_succ]
    by_cases h : d ∣ n
    · rw [if_pos h]; exact ⟨h, hd, fun e he1 he2 => hinv e he1 he2⟩
    · rw [if_neg h]
      have hdn' : d < n := lt_of_le_of_ne hdn (fun heq => h (heq ▸ dvd_refl n))
      by_cases hsq : n < d*d
      · rw [if_pos hsq]
        refine ⟨dvd_refl _, by omega, ?_⟩
        intro e he1 he2
        rcases Nat.lt_or_ge e d with hlt | hge
        · exact hinv e he1 hlt
        · intro hediv
          obtain ⟨q, hq⟩ := hediv
          have hq2 : 2 ≤ q := by nlinarith [hq, he2]
          have hqd : q < d := by nlinarith [hq, hge, hsq]
          exact hinv q hq2 hqd ⟨e, by rw [hq]; ring⟩
      · rw [if_neg hsq]
        have hinv' : ∀ e, 2 ≤ e → e < d+1 → ¬ e ∣ n := by
          intro e he1 he2
          rcases Nat.lt_or_ge e d with hlt | hge
          · exact hinv e he1 hlt
          · have : e = d := by omega
            subst this; exact h
        exact ih (d+1) n (by omega) (by omega) (by omega) hinv'

def minFac' (n : ℕ) : ℕ := sdiv n 2 n

theorem minFac'_dvd (n : ℕ) (hn : 2 ≤ n) : minFac' n ∣ n :=
  (sdiv_spec n 2 n (by norm_num) hn (by omega) (fun e he1 he2 => by omega)).1
theorem minFac'_ge (n : ℕ) (hn : 2 ≤ n) : 2 ≤ minFac' n :=
  (sdiv_spec n 2 n (by norm_num) hn (by omega) (fun e he1 he2 => by omega)).2.1
theorem minFac'_min (n : ℕ) (hn : 2 ≤ n) : ∀ e, 2 ≤ e → e < minFac' n → ¬ e ∣ n :=
  (sdiv_spec n 2 n (by norm_num) hn (by omega) (fun e he1 he2 => by omega)).2.2

theorem minFac'_prime (n : ℕ) (hn : 2 ≤ n) : (minFac' n).Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨minFac'_ge n hn, ?_⟩
  intro m hm hmdvd
  have hm2 : m = 0 ∨ m = 1 ∨ 2 ≤ m := by omega
  rcases hm2 with h|h|h
  · subst h; rw [Nat.zero_dvd] at hmdvd; have := minFac'_ge n hn; omega
  · exact h
  · exact absurd (hmdvd.trans (minFac'_dvd n hn)) (minFac'_min n hn m h hm)

def totFast : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel+1, n =>
      if n ≤ 1 then 1
      else if minFac' n ∣ (n / minFac' n) then minFac' n * totFast fuel (n / minFac' n)
        else (minFac' n - 1) * totFast fuel (n / minFac' n)

theorem totFast_succ (fuel n : ℕ) : totFast (fuel+1) n =
    if n ≤ 1 then 1 else
      if minFac' n ∣ (n / minFac' n) then minFac' n * totFast fuel (n / minFac' n)
      else (minFac' n - 1) * totFast fuel (n / minFac' n) := rfl

def myTot (n : ℕ) : ℕ := totFast n n

theorem totFast_eq : ∀ (fuel n : ℕ), 1 ≤ n → n ≤ fuel → totFast fuel n = Nat.totient n := by
  intro fuel
  induction fuel with
  | zero => intro n h1 h2; omega
  | succ fuel ih =>
    intro n h1 h2
    rw [totFast_succ]
    by_cases hn1 : n ≤ 1
    · rw [if_pos hn1]; have : n = 1 := by omega
      subst this; simp
    · rw [if_neg hn1]
      have hn2 : 2 ≤ n := by omega
      have hpp : (minFac' n).Prime := minFac'_prime n hn2
      have hpd : minFac' n ∣ n := minFac'_dvd n hn2
      have hpge : 2 ≤ minFac' n := minFac'_ge n hn2
      set p := minFac' n with hp
      set m := n / p with hm
      have hnpm : n = p * m := (Nat.mul_div_cancel' hpd).symm
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h|h
        · rw [h, mul_zero] at hnpm; omega
        · exact h
      have hmlt : m < n := by
        rw [hnpm]; exact (Nat.lt_mul_iff_one_lt_left (by omega)).2 (by omega)
      have hmf : m ≤ fuel := by omega
      by_cases hd : p ∣ m
      · rw [if_pos hd, ih m hm1 hmf, hnpm]
        exact (Nat.totient_mul_of_prime_of_dvd hpp hd).symm
      · rw [if_neg hd, ih m hm1 hmf, hnpm]
        exact (Nat.totient_mul_of_prime_of_not_dvd hpp hd).symm

theorem myTot_eq (n : ℕ) (hn : 1 ≤ n) : myTot n = Nat.totient n :=
  totFast_eq n n hn (le_refl n)

/- ### `padicValRat` of a finite product, and of each factor. -/

theorem padicValRat_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hfs : (∏ i ∈ s, f i) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      exact fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [padicValRat.mul hfa hfs, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem term_val (k : ℕ) (hk : 1 ≤ k) :
    padicValRat 3 ((k : ℚ)^2 / (Nat.totient k : ℚ))
      = 2 * (padicValNat 3 k : ℤ) - (padicValNat 3 (Nat.totient k) : ℤ) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk2 : ((k : ℚ))^2 ≠ 0 := pow_ne_zero _ hk0
  have hphi0 : (Nat.totient k : ℚ) ≠ 0 := by
    have : Nat.totient k ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
    exact_mod_cast this
  rw [padicValRat.div hk2 hphi0, padicValRat.pow hk0]
  rw [show ((k:ℚ)) = ((k:ℕ):ℚ) from rfl, padicValRat.of_nat]
  rw [show ((Nat.totient k : ℚ)) = ((Nat.totient k :ℕ):ℚ) from rfl, padicValRat.of_nat]
  push_cast
  ring

/- ### From negative valuation to divisibility of the denominator. -/

theorem three_dvd_den_of_neg (q : ℚ) (h : padicValRat 3 q = -1) : 3 ∣ q.den := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [padicValRat_def] at h
  have hBne : padicValNat 3 q.den ≠ 0 := by omega
  have hden : q.den ≠ 0 := q.den_nz
  exact (dvd_iff_padicValNat_ne_zero hden).mpr hBne

theorem not_pow_two_of_three_dvd (n : ℕ) (h : 3 ∣ n) : ¬ n.isPowerOfTwo := by
  rintro ⟨j, rfl⟩
  have : (3:ℕ) ∣ 2 := (Nat.prime_three).dvd_of_dvd_pow h
  norm_num at this

/- ### The core numerical computation. -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem core_sum :
    ∑ k ∈ Icc 1 1807, (2*(v3 k:ℤ) - (v3 (myTot k):ℤ)) = -1 := by
  have hIcc : (Icc 1 1807 : Finset ℕ) = Ioc 0 1807 := by
    ext x; simp only [mem_Icc, mem_Ioc]; omega
  rw [hIcc]
  have e1 : ∑ k ∈ Ioc 0 452, (2*(v3 k:ℤ) - (v3 (myTot k):ℤ)) = 69 := by decide
  have e2 : ∑ k ∈ Ioc 452 904, (2*(v3 k:ℤ) - (v3 (myTot k):ℤ)) = 0 := by decide
  have e3 : ∑ k ∈ Ioc 904 1356, (2*(v3 k:ℤ) - (v3 (myTot k):ℤ)) = -24 := by decide
  have e4 : ∑ k ∈ Ioc 1356 1807, (2*(v3 k:ℤ) - (v3 (myTot k):ℤ)) = -46 := by decide
  have c1 := Finset.sum_Ioc_consecutive (fun k => 2*(v3 k:ℤ) - (v3 (myTot k):ℤ))
    (by norm_num : (0:ℕ) ≤ 452) (by norm_num : (452:ℕ) ≤ 904)
  have c2 := Finset.sum_Ioc_consecutive (fun k => 2*(v3 k:ℤ) - (v3 (myTot k):ℤ))
    (by norm_num : (0:ℕ) ≤ 904) (by norm_num : (904:ℕ) ≤ 1356)
  have c3 := Finset.sum_Ioc_consecutive (fun k => 2*(v3 k:ℤ) - (v3 (myTot k):ℤ))
    (by norm_num : (0:ℕ) ≤ 1356) (by norm_num : (1356:ℕ) ≤ 1807)
  rw [← c3, ← c2, ← c1, e1, e2, e3, e4]
  norm_num

/- ### The valuation of `A060841_val_rat 1807` equals `-1`. -/

theorem padicValRat_A060841 : padicValRat 3 (A060841_val_rat 1807) = -1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hne : ∀ k ∈ (Icc 1 1807 : Finset ℕ), (((k : ℚ))^2 / ((k.totient : ℕ) : ℚ)) ≠ 0 := by
    intro k hk
    rw [mem_Icc] at hk
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hphi0 : ((Nat.totient k : ℕ) : ℚ) ≠ 0 := by
      have : Nat.totient k ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
      exact_mod_cast this
    exact div_ne_zero (pow_ne_zero _ hk0) hphi0
  have hprod : padicValRat 3 (A060841_val_rat 1807)
      = ∑ k ∈ (Icc 1 1807 : Finset ℕ), padicValRat 3 (((k : ℚ))^2 / ((k.totient : ℕ) : ℚ)) := by
    rw [A060841_val_rat]
    exact padicValRat_prod 3 _ _ hne
  have hterm : (∑ k ∈ (Icc 1 1807 : Finset ℕ), padicValRat 3 (((k : ℚ))^2 / ((k.totient : ℕ) : ℚ)))
      = ∑ k ∈ (Icc 1 1807 : Finset ℕ), (2*(v3 k:ℤ) - (v3 (myTot k):ℤ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_Icc] at hk
    rw [term_val k hk.1, myTot_eq k hk.1, v3_eq k, v3_eq (Nat.totient k)]
  rw [hprod, hterm, core_sum]

/- ### The disproof. -/

theorem oeis_60841_conjecture_0.disproof :
    ¬ (∀ (n : ℕ), 1 ≤ n →
      (A060841_val_rat n).den.isPowerOfTwo ∧
      ((A060841_val_rat n).isInt ↔ n ∈ Icc 1 34 ∨ n = 36 ∨ n = 38)) := by
  intro h
  have hpow : (A060841_val_rat 1807).den.isPowerOfTwo := (h 1807 (by norm_num)).1
  have hdvd : 3 ∣ (A060841_val_rat 1807).den := three_dvd_den_of_neg _ padicValRat_A060841
  exact not_pow_two_of_three_dvd _ hdvd hpow
