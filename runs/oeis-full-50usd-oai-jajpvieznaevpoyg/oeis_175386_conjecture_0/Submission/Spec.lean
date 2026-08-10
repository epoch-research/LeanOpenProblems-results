import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Polynomial


/--
A175386: $a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    -- The upper index is $2n - i - 1$, which is equivalent to $2n - (i+1)$ in $\mathbb{N}$ for $i \le n$.
    -- The lower index $i-1$ is standard subtraction in $\mathbb{N}$.
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)
  ).den

/-- The sum which A175386 $a(n)$ is the denominator of. -/
def S (n : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)

lemma fib_sum_diag (m : ℕ) :
    Nat.fib (m + 1) = ∑ i ∈ Finset.range (m + 1), Nat.choose (m - i) i := by
  rw [Nat.fib_succ_eq_sum_choose]
  rw [Finset.Nat.antidiagonal_eq_map']
  simp

lemma coeff_nat (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    2 * n * Nat.choose (2 * n - (i + 1)) (i - 1) =
      i * (Nat.choose (2 * n - i) i + Nat.choose (2 * n - (i + 1)) (i - 1)) := by
  let c := Nat.choose (2 * n - (i + 1)) (i - 1)
  have hle2 : i ≤ 2*n := by omega
  have hsucc : 2*n - (i+1) + 1 = 2*n - i := by omega
  have hmain := Nat.add_one_mul_choose_eq (2*n - (i+1)) (i-1)
  have hmain' : (2*n - i) * c = Nat.choose (2*n - i) i * i := by
    simpa [c, hsucc, Nat.succ_eq_add_one, hi1] using hmain
  calc
    2 * n * c = (2*n - i + i) * c := by rw [Nat.sub_add_cancel hle2]
    _ = (2*n - i) * c + i * c := by rw [Nat.add_mul]
    _ = Nat.choose (2*n - i) i * i + i * c := by rw [hmain']
    _ = i * (Nat.choose (2*n - i) i + c) := by ring

lemma coeff_rat (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (2 * n : ℚ) * ((Nat.choose (2 * n - (i + 1)) (i - 1) : ℚ) / (i : ℚ)) =
      (Nat.choose (2 * n - i) i : ℚ) + (Nat.choose (2 * n - (i + 1)) (i - 1) : ℚ) := by
  have hiq : (i : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hi1)
  apply mul_right_injective₀ hiq
  field_simp [hiq]
  ring_nf
  have h := congrArg (fun x : ℕ => (x : ℚ)) (coeff_nat n i hi1 hin)
  norm_num [Nat.cast_mul, Nat.cast_add] at h
  ring_nf at h ⊢
  exact h

lemma sum_choose_trunc (n : ℕ) :
    (∑ i ∈ Finset.range (2*n + 1), Nat.choose (2*n - i) i) =
    ∑ i ∈ Finset.Icc 0 n, Nat.choose (2*n - i) i := by
  symm
  apply Finset.sum_subset
  · intro x hx
    simp at hx ⊢
    omega
  · intro x hx hnot
    simp at hx hnot ⊢
    apply Nat.choose_eq_zero_of_lt
    omega

lemma fib_odd_split (n : ℕ) :
    Nat.fib (2*n + 1) = 1 + ∑ i ∈ Finset.Icc 1 n, Nat.choose (2*n - i) i := by
  rw [fib_sum_diag]
  rw [sum_choose_trunc]
  rw [show (∑ i ∈ Finset.Icc 0 n, Nat.choose (2*n - i) i) =
      Nat.choose (2*n - 0) 0 + ∑ i ∈ Finset.Icc 1 n, Nat.choose (2*n - i) i by
    rw [show Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) by
      ext x
      simp
      omega]
    rw [Finset.sum_insert]
    simp]
  simp

lemma fib_odd_split2 (n : ℕ) (hn : 0 < n) :
    Nat.fib (2*n - 1) = ∑ i ∈ Finset.Icc 1 n, Nat.choose (2*n - (i + 1)) (i - 1) := by
  -- reindex k=i-1; use fib_sum_diag with m=2*n-2
  rw [show 2*n - 1 = (2*n - 2) + 1 by omega]
  rw [fib_sum_diag (2*n - 2)]
  -- truncate range (2n-1) to k=0..n-1
  have htr : (∑ k ∈ Finset.range ((2*n - 2) + 1), Nat.choose (2*n - 2 - k) k)
      = ∑ k ∈ Finset.Icc 0 (n-1), Nat.choose (2*n - 2 - k) k := by
    symm
    apply Finset.sum_subset
    · intro x hx; simp at hx ⊢; omega
    · intro x hx hnot; simp at hx hnot ⊢; apply Nat.choose_eq_zero_of_lt; omega
  rw [htr]
  symm
  apply Finset.sum_bij (fun i _ => i-1)
  · intro i hi; simp at hi ⊢; omega
  · intro a ha b hb h; simp at ha hb; omega
  · intro k hk; simp at hk ⊢; refine ⟨k+1, ?_, ?_⟩ <;> simp <;> omega
  · intro i hi
    simp at hi ⊢
    have harg : 2 * n - (i + 1) = 2 * n - 2 - (i - 1) := by omega
    rw [harg]

lemma closed (n : ℕ) (hn : 0 < n) :
    (2*n : ℚ) * S n = (Nat.fib (2*n + 1) : ℚ) + (Nat.fib (2*n - 1) : ℚ) - 1 := by
  simp [S, Finset.mul_sum]
  trans (∑ i ∈ Finset.Icc 1 n, ((Nat.choose (2*n - i) i : ℚ) + (Nat.choose (2*n - (i+1)) (i-1) : ℚ)))
  · apply Finset.sum_congr rfl
    intro i hi
    simp at hi
    exact coeff_rat n i hi.1 hi.2
  · rw [Finset.sum_add_distrib]
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    have h1 := fib_odd_split n
    have h2 := fib_odd_split2 n hn
    have h1q : (Nat.fib (2 * n + 1) : ℚ) = 1 + (∑ i ∈ Finset.Icc 1 n, Nat.choose (2*n - i) i : ℕ) := by
      exact_mod_cast h1
    have h2q : (Nat.fib (2 * n - 1) : ℚ) = (∑ i ∈ Finset.Icc 1 n, Nat.choose (2*n - (i+1)) (i-1) : ℕ) := by
      exact_mod_cast h2
    linarith

lemma fib_period_zmod (M T : ℕ) (hT : 0 < T)
    (h0 : (Nat.fib T : ZMod M) = 0) (h1 : (Nat.fib (T+1) : ZMod M) = 1) :
    ∀ k, (Nat.fib (k+T) : ZMod M) = (Nat.fib k : ZMod M) := by
  intro k
  have h := Nat.fib_add k (T-1)
  have hT' : T - 1 + 1 = T := by omega
  have hTp : T - 1 + 1 + 1 = T + 1 := by omega
  -- h: fib (k + (T-1)+1)= fib k*fib(T-1)+fib(k+1)*fib T
  have hc := congrArg (fun x : ℕ => (x : ZMod M)) h
  norm_num [Nat.cast_add, Nat.cast_mul] at hc
  rw [hT'] at hc
  have hkarg : k + (T - 1) + 1 = k + T := by omega
  rw [hkarg] at hc
  rw [hc, h0, mul_zero, add_zero]
  -- need fib(T-1)=1 mod? From h1 and recurrence h1=fib(T-1)+fibT
  have hrec := Nat.fib_add_one (n := T) (by omega : T ≠ 0)
  have hrecC := congrArg (fun x : ℕ => (x : ZMod M)) hrec
  norm_num [Nat.cast_add] at hrecC
  rw [h1, h0, add_zero] at hrecC
  rw [← hrecC]
  simp


lemma coprime_minFac_sq_sub_one {n p : ℕ} (hn1 : n ≠ 1) (hp : p = Nat.minFac n) (hp5 : 5 < p) :
    Nat.Coprime n (p^2 - 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro q hq hqg
  have hqn : q ∣ n := dvd_trans hqg (Nat.gcd_dvd_left _ _)
  have hqm : q ∣ p^2 - 1 := dvd_trans hqg (Nat.gcd_dvd_right _ _)
  have hqge : p ≤ q := by
    rw [hp]
    exact Nat.minFac_le_of_dvd hq.two_le hqn
  have hpprime : Nat.Prime p := by rw [hp]; exact Nat.minFac_prime hn1
  have hppos2 : 2 ≤ p := hpprime.two_le
  have hfactor : p^2 - 1 = (p+1)*(p-1) := by simpa [add_comm, Nat.sub_self] using (sq_tsub_sq p 1)
  have hqm0 : q ∣ p^2 - 1 := hqm

  rw [hfactor] at hqm
  rw [mul_comm] at hqm
  have hq_or := hq.dvd_mul.mp hqm
  rcases hq_or with hq1 | hq2
  · have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hq1
    omega
  · have hqle : q ≤ p + 1 := Nat.le_of_dvd (by omega) hq2
    have hqne : q ≠ p + 1 := by
      intro heq
      have heven : 2 ∣ q := by
        rw [heq]
        have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
        exact (hpodd.add_odd odd_one).two_dvd
      have hqeq2 : q = 2 := by
        rcases (Nat.dvd_prime hq).mp heven with h | h
        · exact False.elim (Nat.prime_two.ne_one h)
        · exact h.symm
      omega
    have hqnep : q ≠ p := by
      intro hqp
      rw [hqp] at hqm
      have hp2dvd : p ∣ p^2 := by rw [pow_two]; exact dvd_mul_right p p
      have hqm_p : p ∣ p^2 - 1 := by simpa [hqp] using hqm0
      have hsub : p ∣ p^2 - (p^2 - 1) := Nat.dvd_sub hp2dvd hqm_p
      have hp2pos : 0 < p^2 := by positivity
      have hsubeq : p^2 - (p^2 - 1) = 1 := by omega
      have : p ∣ 1 := by rwa [hsubeq] at hsub
      exact hpprime.not_dvd_one this
    omega

lemma bezout_poly (R : Type*) [CommRing R] :
  ((-144 : R[X]) * X^11 + (88 : R[X]) * X^10 - (56 : R[X]) * X^9 + (32 : R[X]) * X^8 - (24 : R[X]) * X^7 + (8 : R[X]) * X^6 - (16 : R[X]) * X^5 - (8 : R[X]) * X^4 - (24 : R[X]) * X^3 - (32 : R[X]) * X^2 - (56 : R[X]) * X - (88 : R[X])) * (X^2 - X - 1) +
  ((144 : R[X]) * X - (232 : R[X])) * (X^12 - 1) = (320 : R[X]) := by
  ring_nf

lemma root_frob_sq {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (K : Type*) [Field K] [CharP K p]
    (a : K) (ha : a^2 - a - 1 = 0) : a^(p^2) = a := by
  let b : K := 1 - a
  have ha' : a^2 = a + 1 := by linear_combination ha
  have haproot : (a^p)^2 - a^p - 1 = 0 := by
    have hpow : (a^2)^p = (a+1)^p := by rw [ha']
    rw [add_pow_char] at hpow
    rw [← pow_mul] at hpow
    rw [show 2 * p = p * 2 by omega, pow_mul] at hpow
    simp at hpow
    linear_combination hpow
  have hfac : (a^p - a) * (a^p - b) = 0 := by
    have haa : a - a^2 = -1 := by linear_combination -ha
    calc (a^p - a) * (a^p - b) = (a^p)^2 - a^p + (a - a^2) := by rw [show b = 1 - a by rfl]; ring
      _ = (a^p)^2 - a^p - 1 := by rw [haa]; ring
      _ = 0 := haproot
  have hor : a^p = a ∨ a^p = b := by
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hor with h | h
  · calc a^(p^2) = (a^p)^p := by rw [show p^2 = p*p by ring, pow_mul]
      _ = a := by rw [h, h]
  · have hbp : b^p = a := by
      calc b^p = (1 + (-a))^p := by simp [b, sub_eq_add_neg]
        _ = 1^p + (-a)^p := by rw [add_pow_char]
        _ = 1 - a^p := by
          rw [show (-a)^p = - a^p by simpa using Odd.neg_pow hpodd a]
          ring
        _ = a := by rw [h]; simp [b]
    calc a^(p^2) = (a^p)^p := by rw [show p^2 = p*p by ring, pow_mul]
      _ = a := by rw [h, hbp]

lemma root_pow_sum {K : Type*} [CommRing K] (a b : K)
    (hs : a + b = 1) (ha : a^2 = a + 1) (hb : b^2 = b + 1) :
    ∀ k : ℕ, 0 < k → a^k + b^k = (Nat.fib (k+1) : K) + ((Nat.fib (k+1) : K) - (Nat.fib k : K))
  | 1, _ => by simpa using hs
  | 2, _ => by
      rw [ha, hb]
      calc a + 1 + (b + 1) = (a + b) + 2 := by ring
        _ = ↑(Nat.fib (2 + 1)) + (↑(Nat.fib (2 + 1)) - ↑(Nat.fib 2)) := by rw [hs]; norm_num
  | k+3, _ => by
      have h1 := root_pow_sum a b hs ha hb (k+2) (by omega)
      have h2 := root_pow_sum a b hs ha hb (k+1) (by omega)
      have reca : a^(k+3) = a^(k+2) + a^(k+1) := by
        calc a^(k+3) = a^(k+1) * a^2 := by ring_nf
          _ = a^(k+1) * (a+1) := by rw [ha]
          _ = a^(k+2) + a^(k+1) := by ring
      have recb : b^(k+3) = b^(k+2) + b^(k+1) := by
        calc b^(k+3) = b^(k+1) * b^2 := by ring_nf
          _ = b^(k+1) * (b+1) := by rw [hb]
          _ = b^(k+2) + b^(k+1) := by ring
      rw [reca, recb]
      rw [show a ^ (k+2) + a ^ (k+1) + (b ^ (k+2) + b ^ (k+1)) =
          (a ^ (k+2) + b ^ (k+2)) + (a ^ (k+1) + b ^ (k+1)) by ring]
      rw [h1, h2]
      simp [Nat.fib_add_two]
      ring

lemma prime_obstruction_aux {p n : ℕ} [Fact p.Prime] (hp5 : 5 < p) (hn : 0 < n)
    (hcop : Nat.Coprime n (p^2 - 1)) :
    ¬ p ∣ (Nat.fib (2*n+1) + Nat.fib (2*n-1) - 1) := by
  intro hdiv
  let f : (ZMod p)[X] := X^2 - X - 1
  let K := f.SplittingField
  haveI : Fintype K := by
    haveI : FiniteDimensional (ZMod p) K := Polynomial.IsSplittingField.finiteDimensional K f
    exact Fintype.ofFinite K
  have hpodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  have hroot_exists : ∃ a : K, a^2 - a - 1 = 0 := by
    have hs : (map (algebraMap (ZMod p) K) f).Splits := Polynomial.SplittingField.splits f
    have hd : (map (algebraMap (ZMod p) K) f).degree ≠ 0 := by
      rw [show map (algebraMap (ZMod p) K) f = (X^2 - X - 1 : K[X]) by simp [f]]
      have hdeg : (X^2 - X - 1 : K[X]).degree = 2 := by compute_degree!
      rw [hdeg]; norm_num
    obtain ⟨a, haeval⟩ := Polynomial.Splits.exists_eval_eq_zero hs hd
    use a
    simpa [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using haeval
  obtain ⟨a, ha⟩ := hroot_exists
  let b : K := 1 - a
  have ha' : a^2 = a + 1 := by linear_combination ha
  have hb : b^2 = b + 1 := by
    have hb0 : b^2 - b - 1 = 0 := by
      calc b^2 - b - 1 = a^2 - a - 1 := by simp [b]; ring
        _ = 0 := ha
    linear_combination hb0
  have hs : a + b = 1 := by simp [b]
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; norm_num at ha
  have hab : a * b = -1 := by rw [show b=1-a by rfl]; linear_combination -ha
  have hsum := root_pow_sum a b hs ha' hb (2*n) (by omega)
  have hLzero : ((Nat.fib (2*n+1) + Nat.fib (2*n-1) - 1 : ℕ) : K) = 0 := by
    have hz : ((Nat.fib (2*n+1) + Nat.fib (2*n-1) - 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hdiv
    change algebraMap (ZMod p) K ((Nat.fib (2*n+1) + Nat.fib (2*n-1) - 1 : ℕ) : ZMod p) = 0
    rw [hz]
    simp
  have hsum1 : a^(2*n) + b^(2*n) = 1 := by
    -- from hsum and hLzero
    have hfm1 : (Nat.fib (2*n+1) : K) - (Nat.fib (2*n) : K) = (Nat.fib (2*n-1) : K) := by
      have hrec := Nat.fib_add_one (n := 2*n) (by omega : 2*n ≠ 0)
      have hc := congrArg (fun x : ℕ => (x : K)) hrec
      norm_num [Nat.cast_add] at hc
      linear_combination hc
    rw [hsum, hfm1]
    have hpos : 1 ≤ Nat.fib (2*n+1) + Nat.fib (2*n-1) := by simp [Nat.succ_le_iff]
    norm_num [Nat.cast_sub hpos, Nat.cast_add] at hLzero
    linear_combination hLzero
  have hbpow : b^(2*n) = (a^(2*n))⁻¹ := by
    have hprod : a^(2*n) * b^(2*n) = 1 := by
      calc a^(2*n) * b^(2*n) = (a*b)^(2*n) := by rw [mul_pow]
        _ = (-1 : K)^(2*n) := by rw [hab]
        _ = 1 := by rw [neg_one_pow_eq_pow_mod_two, show (2*n)%2=0 by omega, pow_zero]
    have ha0pow : a^(2*n) ≠ 0 := pow_ne_zero _ ha0
    exact eq_inv_of_mul_eq_one_right hprod
  let x := a^(2*n)
  have hx0 : x ≠ 0 := pow_ne_zero _ ha0
  have hxsum : x + x⁻¹ = 1 := by simpa [x, hbpow] using hsum1
  have hx6 : x^6 = 1 := by
    have hxquad : x^2 - x + 1 = 0 := by
      have hmul : (x + x⁻¹) * x = (1:K) * x := by rw [hxsum]
      rw [add_mul, inv_mul_cancel₀ hx0, one_mul] at hmul
      linear_combination hmul
    have hx3 : x^3 = -1 := by
      have hx2 : x^2 = x - 1 := by linear_combination hxquad
      calc x^3 = x * x^2 := by ring
        _ = x * (x - 1) := by rw [hx2]
        _ = -1 := by linear_combination hxquad
    calc x^6 = (x^3)^2 := by ring
      _ = 1 := by rw [hx3]; norm_num
  have h12n : a^(12*n) = 1 := by
    change (a^(2*n))^6 = 1 at hx6
    rw [← pow_mul] at hx6
    convert hx6 using 2 <;> ring
  have hp2 : 0 < p^2 := by positivity
  have hfrob := root_frob_sq hpodd K a ha
  have hpord : a^(p^2 - 1) = 1 := by
    apply mul_right_cancel₀ ha0
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p^2), hfrob, one_mul]
  let d := orderOf a
  have hd1 : d ∣ 12*n := orderOf_dvd_of_pow_eq_one h12n
  have hd2 : d ∣ p^2 - 1 := orderOf_dvd_of_pow_eq_one hpord
  have hdn : Nat.Coprime d n := Nat.Coprime.coprime_dvd_left hd2 hcop.symm
  have hd12 : d ∣ 12 := by
    have hd1' : d ∣ n * 12 := by simpa [mul_comm, mul_left_comm, mul_assoc] using hd1
    exact hdn.dvd_of_dvd_mul_left hd1'
  have ha12 : a^12 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd12
  have hbez := congrArg (fun P : K[X] => Polynomial.eval a P) (bezout_poly f.SplittingField)
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, ha, ha12] at hbez
  have h320zero : (320 : K) = 0 := by simpa using hbez.symm
  have hnot : (320 : K) ≠ 0 := by
    change ¬ (((320 : ℕ) : K) = 0)
    rw [CharP.cast_eq_zero_iff K p]
    intro hpdiv
    have hple : p ≤ 320 := Nat.le_of_dvd (by norm_num) hpdiv
    -- p could be <=320, need p not divide by hp5? false p=7 not divide; need prime divisor of 320 are 2,5
    have hp2or5 : p = 2 ∨ p = 5 := by
      have hfac : 320 = 2^6 * 5 := by norm_num
      rw [hfac] at hpdiv
      have hp2pow_or : p ∣ 2^6 ∨ p ∣ 5 := (Fact.out : Nat.Prime p).dvd_mul.mp hpdiv
      rcases hp2pow_or with h2 | h5
      · left
        have hp2dvd : p ∣ 2 := (Fact.out : Nat.Prime p).dvd_of_dvd_pow h2
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hp2dvd with hp1 | hp2
        · exact False.elim ((Fact.out : Nat.Prime p).ne_one hp1)
        · exact hp2
      · right
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h5 with hp1 | hp5eq
        · exact False.elim ((Fact.out : Nat.Prime p).ne_one hp1)
        · exact hp5eq
    omega
  exact hnot h320zero

lemma fib_mod_period_mul (M T : ℕ) (hT : 0 < T)
    (h0 : (Nat.fib T : ZMod M) = 0) (h1 : (Nat.fib (T+1) : ZMod M) = 1) :
    ∀ m k, (Nat.fib (k + m*T) : ZMod M) = (Nat.fib k : ZMod M) := by
  intro m
  induction m with
  | zero => intro k; simp
  | succ m ih =>
      intro k
      rw [show k + (m+1)*T = (k + m*T) + T by rw [Nat.succ_mul]; omega]
      rw [fib_period_zmod M T hT h0 h1, ih]

lemma fib_mod_eq_mod (M T : ℕ) (hT : 0 < T)
    (h0 : (Nat.fib T : ZMod M) = 0) (h1 : (Nat.fib (T+1) : ZMod M) = 1) (k : ℕ) :
    (Nat.fib k : ZMod M) = Nat.fib (k % T) := by
  have h := fib_mod_period_mul M T hT h0 h1 (k / T) (k % T)
  nth_rw 1 [show k = k % T + k / T * T by rw [Nat.mul_comm, Nat.mod_add_div]]
  exact h

lemma L_not_dvd_of_even {n L : ℕ} (hn : 0 < n) (he : 2 ∣ n)
    (hL : L = Nat.fib (2*n+1) + Nat.fib (2*n-1) - 1) : ¬ 4 ∣ L := by
  intro h4
  have hz : (L : ZMod 4) = 0 := by rwa [ZMod.natCast_eq_zero_iff]
  have hcalc : (L : ZMod 4) ≠ 0 := by
    rw [hL]
    have hpos : 1 ≤ Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1) := by simp [Nat.succ_le_iff]
    norm_num [Nat.cast_sub hpos, Nat.cast_add]
    have h1 := fib_mod_eq_mod 4 6 (by norm_num) (by decide) (by decide) (2*n+1)
    have h2 := fib_mod_eq_mod 4 6 (by norm_num) (by decide) (by decide) (2*n-1)
    rw [h1, h2]
    obtain ⟨k, rfl⟩ := he
    have hkpos : 0 < k := by omega
    have r1 : (2 * (2 * k) + 1) % 6 = (4 * (k % 6) + 1) % 6 := by omega
    have r2 : (2 * (2 * k) - 1) % 6 = (4 * (k % 6) + 5) % 6 := by omega
    rw [r1, r2]
    have hklt : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases (k % 6) <;> decide
  exact hcalc hz

lemma L_not_dvd_of_three_odd {n L : ℕ} (hn : 0 < n) (h3 : 3 ∣ n) (hodd : Odd n)
    (hL : L = Nat.fib (2*n+1) + Nat.fib (2*n-1) - 1) : ¬ 3 ∣ L := by
  intro h3L
  have hz : (L : ZMod 3) = 0 := by rwa [ZMod.natCast_eq_zero_iff]
  have hcalc : (L : ZMod 3) ≠ 0 := by
    rw [hL]
    have hpos : 1 ≤ Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1) := by simp [Nat.succ_le_iff]
    norm_num [Nat.cast_sub hpos, Nat.cast_add]
    have h1 := fib_mod_eq_mod 3 8 (by norm_num) (by decide) (by decide) (2*n+1)
    have h2 := fib_mod_eq_mod 3 8 (by norm_num) (by decide) (by decide) (2*n-1)
    rw [h1, h2]
    rcases h3 with ⟨k, rfl⟩
    rcases hodd with ⟨j, hj⟩
    -- 3*k = 2*j+1, so k odd; case k mod 4
    have r1 : (2 * (3 * k) + 1) % 8 = (6 * (k % 8) + 1) % 8 := by omega
    have r2 : (2 * (3 * k) - 1) % 8 = (6 * (k % 8) + 7) % 8 := by omega
    rw [r1, r2]
    have hklt : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases (k % 8) <;> (first | omega | decide)
  exact hcalc hz

lemma L_not_dvd_of_five_coprime6 {n L : ℕ} (hn : 0 < n) (h5 : 5 ∣ n) (hn2 : ¬ 2 ∣ n) (hn3 : ¬ 3 ∣ n)
    (hL : L = Nat.fib (2*n+1) + Nat.fib (2*n-1) - 1) : ¬ 5 ∣ L := by
  intro h5L
  have hz : (L : ZMod 5) = 0 := by rwa [ZMod.natCast_eq_zero_iff]
  have hcalc : (L : ZMod 5) ≠ 0 := by
    rw [hL]
    have hpos : 1 ≤ Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1) := by simp [Nat.succ_le_iff]
    norm_num [Nat.cast_sub hpos, Nat.cast_add]
    have h1 := fib_mod_eq_mod 5 20 (by norm_num) (by decide) (by decide) (2*n+1)
    have h2 := fib_mod_eq_mod 5 20 (by norm_num) (by decide) (by decide) (2*n-1)
    rw [h1, h2]
    rcases h5 with ⟨k, rfl⟩
    have hkodd : k % 2 = 1 := by
      have : ¬ 2 ∣ k := by intro hk; exact hn2 (dvd_mul_of_dvd_right hk 5)
      omega
    have r1 : (2 * (5 * k) + 1) % 20 = (10 * (k % 20) + 1) % 20 := by omega
    have r2 : (2 * (5 * k) - 1) % 20 = (10 * (k % 20) + 19) % 20 := by omega
    rw [r1, r2]
    have hklt20 : k % 20 < 20 := Nat.mod_lt _ (by norm_num)
    interval_cases (k % 20) <;> (first | omega | decide)
  exact hcalc hz

def L_def (n : ℕ) : ℕ := Nat.fib (2*n+1) + Nat.fib (2*n-1) - 1

lemma denom_one_implies_dvd (n : ℕ) (hn : 0 < n) (hden : a n = 1) : 2*n ∣ L_def n := by
  have hdenS : (S n).den = 1 := by simpa [a, S] using hden
  have hclosed := closed n hn
  have h2n0 : (2*n : ℚ) ≠ 0 := by positivity
  have hS : S n = ((L_def n : ℕ) : ℚ) / (2*n : ℚ) := by
    rw [eq_div_iff h2n0]
    rw [mul_comm]
    simpa [L_def] using hclosed
  have hdenDiv : (((L_def n : ℕ) : ℚ) / (2*n : ℕ)).den = 1 := by simpa [Nat.cast_mul] using hS ▸ hdenS
  exact (Rat.den_div_natCast_eq_one_iff (L_def n) (2*n) (by omega)).mp hdenDiv

theorem oeis_175386_conjecture_0 (n : ℕ) (hn : 1 < n) : a n ≠ 1 := by
  intro hden
  have hnpos : 0 < n := by omega
  have hdiv := denom_one_implies_dvd n hnpos hden
  let L := L_def n
  have hLdef : L = Nat.fib (2*n+1) + Nat.fib (2*n-1) - 1 := rfl
  by_cases h2 : 2 ∣ n
  · have h4 : 4 ∣ 2*n := by rcases h2 with ⟨k, rfl⟩; use k; ring
    exact (L_not_dvd_of_even hnpos h2 hLdef) (dvd_trans h4 hdiv)
  · by_cases h3 : 3 ∣ n
    · have hodd : Odd n := by exact Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
      exact (L_not_dvd_of_three_odd hnpos h3 hodd hLdef) (dvd_trans (by exact dvd_mul_of_dvd_right h3 2) hdiv)
    · by_cases h5 : 5 ∣ n
      · exact (L_not_dvd_of_five_coprime6 hnpos h5 h2 h3 hLdef) (dvd_trans (by exact dvd_mul_of_dvd_right h5 2) hdiv)
      · let p := Nat.minFac n
        have hn1 : n ≠ 1 := by omega
        have hpprime : Nat.Prime p := Nat.minFac_prime hn1
        have hpdvdn : p ∣ n := Nat.minFac_dvd n
        have hpgt5 : 5 < p := by
          by_contra hnotgt
          have hple : p ≤ 5 := by omega
          interval_cases p
          · norm_num at hpprime
          · norm_num at hpprime
          · exact h2 hpdvdn
          · exact h3 hpdvdn
          · norm_num at hpprime
          · exact h5 hpdvdn
        have hcop : Nat.Coprime n (p^2 - 1) := coprime_minFac_sq_sub_one hn1 rfl hpgt5
        have hpdiv2n : p ∣ 2*n := by simpa [mul_comm] using dvd_mul_of_dvd_right hpdvdn 2
        have hpdivL : p ∣ L := dvd_trans hpdiv2n hdiv
        haveI : Fact p.Prime := ⟨hpprime⟩
        exact prime_obstruction_aux hpgt5 hnpos hcop hpdivL
