import FormalConjectures.Util.ProblemImports

open Nat Finset

-- Arithmetic helper: f+1 ≤ p^f for p ≥ 2
theorem succ_le_pow_dev (p f : ℕ) (hp : 2 ≤ p) : f + 1 ≤ p ^ f := by
  induction f with
  | zero => simp
  | succ k ih =>
    have : p ^ (k+1) = p * p ^ k := by ring
    rw [this]
    calc k + 1 + 1 ≤ (k+1) + (k+1) := by lia
      _ ≤ p * p^k := by nlinarith [ih]

-- Arithmetic helper: (f+1)^2 ≤ p^f for p ≥ 4
theorem sq_le_pow_dev (p f : ℕ) (hp : 4 ≤ p) : (f + 1)^2 ≤ p ^ f := by
  induction f with
  | zero => simp
  | succ k ih =>
    have h1 : p ^ (k+1) = p * p ^ k := by ring
    rw [h1]
    have heq : (k + 1 + 1)^2 + (3*k^2 + 4*k) = 4 * (k+1)^2 := by ring
    have : (k + 1 + 1)^2 ≤ 4 * (k+1)^2 := by lia
    calc (k+1+1)^2 ≤ 4 * (k+1)^2 := this
      _ ≤ p * p^k := by nlinarith [ih]

/--
Auxiliary sequence A051403, defined as
$$\frac{(n+2) \sum_{k=0}^n k!}{2}$$
-/
def a051403 (n : ℕ) : ℕ :=
  let fact_sum := Finset.sum (range (n + 1)) (fun k => k.factorial)
  ((n + 2) * fact_sum) / 2

-- Evenness of the sum of factorials beyond the first two terms
theorem even_sumfact_dev (k : ℕ) :
    2 ∣ (k + 2) * (∑ j ∈ range (k+1), j !) := by
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨t, ht⟩ := hk
    exact ⟨(t+1) * (∑ j ∈ range (k+1), j !), by rw [ht]; ring⟩
  · obtain ⟨t, ht⟩ := hk
    have hk1 : 1 ≤ k := by lia
    have : 2 ∣ (∑ j ∈ range (k+1), j !) := by
      have hsplit : (∑ j ∈ range (k+1), j !) = 2 + ∑ j ∈ Finset.Ico 2 (k+1), j ! := by
        rw [← Finset.sum_range_add_sum_Ico _ (by lia : 2 ≤ k+1)]
        norm_num [Finset.sum_range_succ, Nat.factorial]
      rw [hsplit]
      apply Nat.dvd_add
      · exact ⟨1, rfl⟩
      · apply Finset.dvd_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        obtain ⟨a, ha⟩ : ∃ a, i = a + 2 := ⟨i - 2, by lia⟩
        rw [ha]
        have he2 : (a+2)! = (a+2) * (a+1) * a ! := by
          rw [Nat.factorial_succ, Nat.factorial_succ]; ring
        rw [he2]
        rcases Nat.even_or_odd a with he | ho
        · obtain ⟨s, hs⟩ := he; exact ⟨(s+1)*(a+1)*a !, by rw [hs]; ring⟩
        · obtain ⟨s, hs⟩ := ho; exact ⟨(a+2)*(s+1)*a !, by rw [hs]; ring⟩
    exact Dvd.dvd.mul_left this (k+2)

theorem two_mul_a051403_dev (k : ℕ) :
    2 * a051403 k = (k + 2) * (∑ j ∈ range (k+1), j !) := by
  unfold a051403
  simp only
  rw [Nat.mul_div_cancel' (even_sumfact_dev k)]

-- The 2D identity, for n ≥ 4
theorem twoD_identity_dev (n : ℕ) (hn : 4 ≤ n) :
    2 * (2 * a051403 (n-3) + n * a051403 (n-4))
      = 2 * (n-1) * (n-3)! + (n^2 - 2) * (∑ j ∈ range (n-3), j !) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 4 := ⟨n - 4, by lia⟩
  have e3 : N + 4 - 3 = N + 1 := by lia
  have e4 : N + 4 - 4 = N := by lia
  have e1 : N + 4 - 1 = N + 3 := by lia
  rw [e3, e4, e1]
  rw [show 2 * (2 * a051403 (N+1) + (N+4) * a051403 N)
        = 2 * (2 * a051403 (N+1)) + (N+4) * (2 * a051403 N) by ring]
  rw [two_mul_a051403_dev (N+1), two_mul_a051403_dev N]
  have hsr : (∑ j ∈ range (N+1+1), j !) = (∑ j ∈ range (N+1), j !) + (N+1)! := by
    rw [Finset.sum_range_succ]
  have hsq : (N+4)^2 - 2 = N^2 + 8*N + 14 := by
    rw [show (N+4)^2 = N^2 + 8*N + 16 by ring]; lia
  rw [hsr, hsq]
  ring

-- Legendre lower bound
theorem legendre_lower_dev (p N : ℕ) (hp : p.Prime) :
    N / p ≤ (N !).factorization p := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  rw [Nat.factorization_factorial hp (b := N+1)
        (Nat.lt_succ_of_le (Nat.log_le_self p N))]
  calc N / p = N / p ^ 1 := by rw [pow_one]
    _ ≤ ∑ i ∈ Finset.Ico 1 (N+1), N / p ^ i := by
        apply Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _)
        rw [Finset.mem_Ico]; exact ⟨le_refl 1, by lia⟩

-- 3 never divides n^2 - 2
theorem three_not_dvd_dev (n : ℕ) (hn : 2 ≤ n) : ¬ (3 ∣ (n^2 - 2)) := by
  have hmod : n^2 % 3 = 0 ∨ n^2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by lia
    rcases this with h | h | h <;> rw [h] <;> decide
  have hge : 2 ≤ n^2 := by nlinarith
  lia

-- For odd prime dividing n^2-2, it does not divide n-2
theorem prime_not_dvd_sub_two_dev (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpm : p ∣ (n^2 - 2)) : ¬ p ∣ (n - 2) := by
  intro hpd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by lia⟩
  have hsplit : (k+2)^2 - 2 = (k+2-2)*(k+2+2) + 2 := by
    have : (k+2)^2 = k^2 + 4*k + 4 := by ring
    rw [this]; simp; ring_nf
  have h2 : p ∣ 2 := by
    have hd : p ∣ (k+2-2)*(k+2+2) := Dvd.dvd.mul_right hpd _
    have := Nat.dvd_sub hpm hd
    rwa [hsplit, Nat.add_sub_cancel_left] at this
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  exact hp2 this

-- For prime dividing n^2-2, it does not divide n-1
theorem prime_not_dvd_sub_one_dev (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime)
    (hpm : p ∣ (n^2 - 2)) : ¬ p ∣ (n - 1) := by
  intro hpd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by lia⟩
  have hsplit : (k+2-1)*(k+2+1) = ((k+2)^2 - 2) + 1 := by
    have : (k+2)^2 = k^2 + 4*k + 4 := by ring
    rw [this]; simp; ring_nf
  have h1 : p ∣ 1 := by
    have hd : p ∣ (k+2-1)*(k+2+1) := Dvd.dvd.mul_right hpd _
    rw [hsplit] at hd
    have := Nat.dvd_sub hd hpm
    rwa [Nat.add_sub_cancel_left] at this
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp h1)

-- Lemma D : (f+1)*p ≥ n  where f = (n-3)/p
theorem lemmaD_dev (n p : ℕ) (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ (n^2 - 2)) : n ≤ ((n-3)/p + 1) * p := by
  set f := (n-3)/p with hf
  set r := (n-3)%p with hr
  have hpos : 0 < p := hp.pos
  have hdm : p * f + r = n - 3 := Nat.div_add_mod (n-3) p
  have hrp : r < p := Nat.mod_lt _ hpos
  have hpn2 : ¬ p ∣ (n - 2) := prime_not_dvd_sub_two_dev n p (by lia) hp hp2 hpm
  have hpn1 : ¬ p ∣ (n - 1) := prime_not_dvd_sub_one_dev n p (by lia) hp hpm
  -- show p ≥ r + 3
  have hge : r + 3 ≤ p := by
    by_contra hc
    push_neg at hc  -- p < r + 3, i.e. p ≤ r + 2
    have hcase : p = r + 1 ∨ p = r + 2 := by lia
    rcases hcase with hcase | hcase
    · -- p = r+1 ⟹ p ∣ n-2
      have hpf : p * f + p = n - 2 := by lia
      exact hpn2 ⟨f + 1, by rw [Nat.mul_succ]; exact hpf.symm⟩
    · -- p = r+2 ⟹ p ∣ n-1
      have hpf : p * f + p = n - 1 := by lia
      exact hpn1 ⟨f + 1, by rw [Nat.mul_succ]; exact hpf.symm⟩
  -- conclude
  have key : ((n-3)/p + 1) * p = p * f + p := by rw [← hf]; ring
  rw [key]
  lia

-- a051403 is positive
theorem a051403_pos_dev (k : ℕ) : 1 ≤ a051403 k := by
  have h2 : 2 ≤ 2 * a051403 k := by
    rw [two_mul_a051403_dev]
    have hS : 1 ≤ ∑ j ∈ range (k+1), j ! := by
      have h0 := Finset.single_le_sum (f := fun j => j !) (fun j _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.succ_pos k))
      simpa using h0
    nlinarith [hS]
  lia

-- 4 never divides n^2 - 2
theorem four_not_dvd_dev (n : ℕ) (hn : 2 ≤ n) : ¬ (4 ∣ (n^2 - 2)) := by
  have hmod : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
    rw [Nat.pow_mod]
    have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by lia
    rcases this with h | h | h | h <;> rw [h] <;> decide
  have hge : 2 ≤ n^2 := by nlinarith
  lia

-- 2 does not divide  a n
theorem two_not_dvd_a_dev (n : ℕ) (hn : 4 ≤ n) :
    ¬ 2 ∣ ((n^2 - 2) / Nat.gcd (n^2 - 2) (2 * a051403 (n-3) + n * a051403 (n-4))) := by
  set m := n^2 - 2 with hm
  set D := 2 * a051403 (n-3) + n * a051403 (n-4) with hD
  set g := Nat.gcd m D with hg
  have hm0 : m ≠ 0 := by
    have hsq : 16 ≤ n^2 := by nlinarith
    rw [hm]; lia
  have hD0 : D ≠ 0 := by
    have h1 : 1 ≤ a051403 (n-3) := a051403_pos_dev _
    rw [hD]; lia
  have hgdvd : g ∣ m := Nat.gcd_dvd_left m D
  -- v_2 m ≤ v_2 D
  have hv2 : m.factorization 2 ≤ D.factorization 2 := by
    rcases Nat.even_or_odd n with hne | hno
    · -- n even ⟹ 2 ∣ D, and v_2 m ≤ 1
      have h2m1 : m.factorization 2 ≤ 1 := by
        by_contra hc
        push_neg at hc
        have h22 : 2^2 ∣ m := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).mpr (by lia)
        have h4 : (4:ℕ) ∣ m := by rw [show (4:ℕ) = 2^2 by norm_num]; exact h22
        exact four_not_dvd_dev n (by lia) h4
      have h2D : 2 ∣ D := by
        obtain ⟨k, rfl⟩ := hne
        rw [hD]; exact Nat.dvd_add ⟨a051403 (k+k-3), by ring⟩ ⟨k * a051403 (k+k-4), by ring⟩
      have : 1 ≤ D.factorization 2 :=
        (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hD0).mp h2D
      lia
    · -- n odd ⟹ m odd ⟹ v_2 m = 0
      have h2nm : ¬ 2 ∣ m := by
        intro h2m
        obtain ⟨k, rfl⟩ := hno
        rw [hm] at h2m
        have : (2*k+1)^2 = 2*(2*k^2+2*k) + 1 := by ring
        rw [this] at h2m
        omega
      rw [Nat.factorization_eq_zero_of_not_dvd h2nm]
      exact Nat.zero_le _
  -- conclude
  intro habs
  have hdiv : ((m / g)).factorization 2 = m.factorization 2 - g.factorization 2 := by
    rw [Nat.factorization_div hgdvd, Finsupp.tsub_apply]
  have hgf : g.factorization 2 = min (m.factorization 2) (D.factorization 2) := by
    rw [hg, Nat.factorization_gcd hm0 hD0]; simp [Finsupp.inf_apply]
  have hg0 : g ≠ 0 := by rw [hg]; exact Nat.gcd_ne_zero_left hm0
  have hmg0 : m / g ≠ 0 := by
    have : 0 < m / g := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hgdvd)
      (Nat.pos_of_ne_zero hg0)
    lia
  have h1le : 1 ≤ (m / g).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hmg0).mp habs
  rw [hdiv, hgf] at h1le
  omega

/--
A363102: Denominator of the continued fraction $1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2)))))$.
The sequence is defined by the formula:
$$a(n) = \frac{n^2 - 2}{\gcd(n^2 - 2, 2 \cdot A051403(n-3) + n \cdot A051403(n-4))}$$
The formula is valid for $n \ge 3$.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := n ^ 2 - 2
  let a051403_nm3 := a051403 (n - 3)
  let a051403_nm4 := a051403 (n - 4)
  let denom_arg := 2 * a051403_nm3 + n * a051403_nm4
  -- The subtraction n^2 - 2 is safe for n >= 3.
  num / Nat.gcd num denom_arg

-- Core footprint lemma
theorem core_dev (n p j : ℕ) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ (n^2 - 2)) (hjpos : 1 ≤ j)
    (hj : p ^ j ∣ (n^2 - 2) / Nat.gcd (n^2 - 2) (2 * a051403 (n-3) + n * a051403 (n-4))) :
    p ^ ((n-3)/p + j) ∣ (n^2 - 2) := by
  set m := n^2 - 2 with hm
  set D := 2 * a051403 (n-3) + n * a051403 (n-4) with hD
  set g := Nat.gcd m D with hg
  set q := m / g with hq
  -- positivity
  have hm0 : m ≠ 0 := by
    have hsq : 16 ≤ n^2 := by nlinarith
    rw [hm]; lia
  have hD0 : D ≠ 0 := by
    have h1 : 1 ≤ a051403 (n-3) := a051403_pos_dev _
    rw [hD]; lia
  have hg0 : g ≠ 0 := by
    rw [hg]; exact Nat.gcd_ne_zero_left hm0
  have hgdvd : g ∣ m := Nat.gcd_dvd_left m D
  have hq0 : q ≠ 0 := by
    rw [hq]
    have : 0 < m / g := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hgdvd)
      (Nat.pos_of_ne_zero hg0)
    lia
  have hfac0 : (n-3)! ≠ 0 := Nat.factorial_ne_zero _
  -- abbreviations for valuations
  set vp := m.factorization p with hvp
  set vD := D.factorization p with hvD
  set vg := g.factorization p with hvg_def
  set vq := q.factorization p with hvq
  set A := ((n-3)!).factorization p with hA
  set L := (n-3)/p with hL
  -- vg = min vp vD
  have hvg : vg = min vp vD := by
    rw [hvg_def, hg, Nat.factorization_gcd hm0 hD0]
    simp [Finsupp.inf_apply, hvp, hvD]
  -- vp = vg + vq
  have hmgq : m = g * q := by rw [hq]; exact (Nat.mul_div_cancel' hgdvd).symm
  have hvpsum : vp = vg + vq := by
    rw [hvp, hmgq, Nat.factorization_mul hg0 hq0]; rfl
  -- vq ≥ j
  have hvqj : j ≤ vq := by
    rw [hvq]
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hq0).mp hj
  -- A ≥ L
  have hAL : L ≤ A := by rw [hA, hL]; exact legendre_lower_dev p (n-3) hp
  -- vD ≥ min A vp
  set kmin := min A vp with hkmin
  have hVDk : kmin ≤ vD := by
    have hk1 : p ^ kmin ∣ (n-3)! := by
      apply (Nat.Prime.pow_dvd_iff_le_factorization hp hfac0).mpr
      rw [hkmin, hA]; exact Nat.min_le_left _ _
    have hk2 : p ^ kmin ∣ m := by
      apply (Nat.Prime.pow_dvd_iff_le_factorization hp hm0).mpr
      rw [hkmin, hvp]; exact Nat.min_le_right _ _
    have h2D : p ^ kmin ∣ 2 * D := by
      rw [hD, twoD_identity_dev n hn, ← hm]
      apply Nat.dvd_add
      · exact Dvd.dvd.mul_left hk1 (2 * (n-1))
      · exact Dvd.dvd.mul_right hk2 _
    have hcop : Nat.Coprime (p ^ kmin) 2 :=
      (Nat.Coprime.pow_left kmin ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
    have hdD : p ^ kmin ∣ D := hcop.dvd_of_dvd_mul_left h2D
    rw [hvD]
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hD0).mp hdD
  -- conclude via arithmetic
  have hfinal : L + j ≤ vp := by omega
  rw [hm]  -- goal back to m
  apply (Nat.Prime.pow_dvd_iff_le_factorization hp hm0).mpr
  rw [← hvp, hL]
  exact hfinal


theorem main_ge4 (n : ℕ) (hn : 4 ≤ n) : a n = 1 ∨ Nat.Prime (a n) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hq1, hqp⟩ := hcon
  set m := n^2 - 2 with hm
  set q := a n with hqq
  have hgdvd : Nat.gcd m (2*a051403 (n-3)+n*a051403 (n-4)) ∣ m := Nat.gcd_dvd_left _ _
  have hqdvdm : q ∣ m := ⟨_, (Nat.div_mul_cancel hgdvd).symm⟩
  have hm0 : 0 < m := by have : 16 ≤ n^2 := by nlinarith
                         rw [hm]; lia
  have hmn2 : 2 ≤ n^2 := by nlinarith
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hqdvdm; exact absurd (Nat.eq_zero_of_zero_dvd hqdvdm) hm0.ne'
    · exact h
  have hq2 : 2 ≤ q := by lia
  -- ¬ 2 ∣ q
  have hnot2q : ¬ 2 ∣ q := by rw [hqq]; exact two_not_dvd_a_dev n hn
  -- minFac
  have hp_prime : (q.minFac).Prime := Nat.minFac_prime hq1
  set p := q.minFac with hpdef
  have hpq : p ∣ q := Nat.minFac_dvd q
  have hpm : p ∣ m := hpq.trans hqdvdm
  have hp2ne : p ≠ 2 := fun h => hnot2q (h ▸ hpq)
  have hp3ne : p ≠ 3 := fun h => three_not_dvd_dev n (by lia) (by rw [← hm]; exact (h ▸ hpm))
  have h2le : 2 ≤ p := hp_prime.two_le
  have hp5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with hlt | hge
    · interval_cases p
      · exact absurd rfl hp2ne
      · exact absurd rfl hp3ne
      · exact absurd hp_prime (by norm_num)
    · exact hge
  -- footprint for p, exponent fp+1
  have hpq1 : p ^ 1 ∣ a n := by rw [pow_one]; exact (hqq ▸ hpq)
  have hfp : p ^ ((n-3)/p + 1) ∣ m :=
    core_dev n p 1 hn hp_prime hp2ne hpm (by norm_num) hpq1
  have hfpn : n ≤ p ^ ((n-3)/p + 1) := by
    have h1 : (n-3)/p + 1 ≤ p ^ ((n-3)/p) := succ_le_pow_dev p ((n-3)/p) (by lia)
    have h2 : n ≤ ((n-3)/p + 1) * p := lemmaD_dev n p (by lia) hp_prime hp2ne hpm
    calc n ≤ ((n-3)/p + 1) * p := h2
      _ ≤ p ^ ((n-3)/p) * p := by nlinarith [h1]
      _ = p ^ ((n-3)/p + 1) := by rw [pow_succ]
  -- q/p ≥ 2
  have hqp_ne : q ≠ p := fun h => hqp (h ▸ hp_prime)
  have hpltq : p < q := lt_of_le_of_ne (Nat.le_of_dvd hq0 hpq) (fun h => hqp_ne h.symm)
  have hqq2 : 2 ≤ q / p := by
    have hqe : q / p * p = q := Nat.div_mul_cancel hpq
    have hlt : 1 * p < q / p * p := by rw [one_mul, hqe]; exact hpltq
    have h1 := Nat.lt_of_mul_lt_mul_right hlt
    lia
  have hp2_prime : ((q/p).minFac).Prime := Nat.minFac_prime (by omega)
  set p2 := (q/p).minFac with hp2def
  have hp2dvd : p2 ∣ q/p := Nat.minFac_dvd _
  have hqpdvdq : q/p ∣ q := ⟨p, (Nat.div_mul_cancel hpq).symm⟩
  have hp2q : p2 ∣ q := hp2dvd.trans hqpdvdq
  have hp2m : p2 ∣ m := hp2q.trans hqdvdm
  have hp2ne2 : p2 ≠ 2 := fun h => hnot2q (h ▸ hp2q)
  have hple : p ≤ p2 := Nat.minFac_le_of_dvd hp2_prime.two_le hp2q
  rcases eq_or_lt_of_le hple with heq | hlt
  · -- p = p2 : square case
    have hpp : p ∣ q/p := heq ▸ hp2dvd
    have hp2q2 : p ^ 2 ∣ q := by
      rw [pow_two, ← Nat.div_mul_cancel hpq]
      exact Nat.mul_dvd_mul hpp dvd_rfl
    have hfp2m : p ^ ((n-3)/p + 2) ∣ m :=
      core_dev n p 2 hn hp_prime hp2ne hpm (by norm_num) hp2q2
    have hbig : n^2 ≤ p ^ ((n-3)/p + 2) := by
      have h1 : ((n-3)/p + 1)^2 ≤ p ^ ((n-3)/p) := sq_le_pow_dev p ((n-3)/p) (by lia)
      have h2 : n ≤ ((n-3)/p + 1) * p := lemmaD_dev n p (by lia) hp_prime hp2ne hpm
      calc n^2 ≤ (((n-3)/p + 1) * p)^2 := by nlinarith [h2]
        _ = ((n-3)/p + 1)^2 * p^2 := by ring
        _ ≤ p ^ ((n-3)/p) * p^2 := by nlinarith [h1]
        _ = p ^ ((n-3)/p + 2) := by rw [pow_add]
    have hle : p ^ ((n-3)/p + 2) ≤ m := Nat.le_of_dvd hm0 hfp2m
    rw [hm] at hle
    omega
  · -- p < p2 : distinct case
    have hp2q1 : p2 ^ 1 ∣ a n := by rw [pow_one]; exact (hqq ▸ hp2q)
    have hfp2 : p2 ^ ((n-3)/p2 + 1) ∣ m :=
      core_dev n p2 1 hn hp2_prime hp2ne2 hp2m (by norm_num) hp2q1
    have hfp2n : n ≤ p2 ^ ((n-3)/p2 + 1) := by
      have h1 : (n-3)/p2 + 1 ≤ p2 ^ ((n-3)/p2) := succ_le_pow_dev p2 ((n-3)/p2) hp2_prime.two_le
      have h2 : n ≤ ((n-3)/p2 + 1) * p2 := lemmaD_dev n p2 (by lia) hp2_prime hp2ne2 hp2m
      calc n ≤ ((n-3)/p2 + 1) * p2 := h2
        _ ≤ p2 ^ ((n-3)/p2) * p2 := by nlinarith [h1]
        _ = p2 ^ ((n-3)/p2 + 1) := by rw [pow_succ]
    have hcop : Nat.Coprime (p ^ ((n-3)/p + 1)) (p2 ^ ((n-3)/p2 + 1)) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp_prime hp2_prime).mpr (Nat.ne_of_lt hlt))
    have hprod : p ^ ((n-3)/p + 1) * p2 ^ ((n-3)/p2 + 1) ∣ m :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hfp hfp2
    have hprodle : p ^ ((n-3)/p + 1) * p2 ^ ((n-3)/p2 + 1) ≤ m := Nat.le_of_dvd hm0 hprod
    have hprodge : n ^ 2 ≤ p ^ ((n-3)/p + 1) * p2 ^ ((n-3)/p2 + 1) := by
      rw [pow_two]; exact Nat.mul_le_mul hfpn hfp2n
    rw [hm] at hprodle
    omega

/-- A363102 Conjecture 1: The sequence contains only 1's and primes. -/
theorem oeis_a363102_conjecture_1 :
  ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ Nat.Prime (a n) := by
  intro n hn
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n
    · right
      norm_num [a, a051403, Finset.sum_range_succ, Nat.factorial]
  · exact main_ge4 n h
