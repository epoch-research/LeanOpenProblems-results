import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The term $C(6k,3k)C(3k,k)$ appearing in the sum. -/
def T_term (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

/--
A189286: $a(n):=\frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}\binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$.
We define the sequence as an integer sequence, handling $n=0$ explicitly and relying on exact division for $n>0$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if h : n = 0 then
    (-1 : ℤ) -- Explicitly defined a(0)
  else
    let numerator_nat : ℕ := Finset.sum (range (n + 1)) fun k => T_term k * T_term (n - k)

    -- Denominator: (2n - 1) * C(3n, n). The result is known to be an integer.
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)

    (numerator_nat : ℤ) / denominator

-- SA: if the two "A-carries" of k vanish then 6*(k%q) < q.
private lemma sa (q k : ℕ) (hq : 2 ≤ q)
    (h1 : ¬ (q ≤ (3*k)%q + (3*k)%q)) (h2 : ¬ (q ≤ k%q + (2*k)%q)) : 6*(k%q) < q := by
  have m3 : (3*k)%q = (3*(k%q))%q := (Nat.mod_modEq k q).symm.mul_left 3
  have m2 : (2*k)%q = (2*(k%q))%q := (Nat.mod_modEq k q).symm.mul_left 2
  set a := k%q with ha_def
  have ha : a < q := Nat.mod_lt _ (by omega)
  rw [m3] at h1
  rw [m2] at h2
  have e3 := Nat.div_add_mod (3*a) q
  have e2 := Nat.div_add_mod (2*a) q
  have b3 : (3*a)%q < q := Nat.mod_lt _ (by omega)
  have b2 : (2*a)%q < q := Nat.mod_lt _ (by omega)
  have d3 : 3*a/q < 3 := by apply Nat.div_lt_of_lt_mul; omega
  have d2 : 2*a/q < 2 := by apply Nat.div_lt_of_lt_mul; omega
  set r3 := (3*a)%q with hr3
  set r2 := (2*a)%q with hr2
  set q3 := 3*a/q with hq3'
  set q2 := 2*a/q with hq2'
  interval_cases q3 <;> interval_cases q2 <;> omega

-- SB1': if the B-carry of s fires, then q ≤ 3*(s%q)
private lemma sb1 (q s : ℕ) (hq : 2 ≤ q) (h : q ≤ s%q + (2*s)%q) : q ≤ 3*(s%q) := by
  have m2 : (2*s)%q = (2*(s%q))%q := (Nat.mod_modEq s q).symm.mul_left 2
  rw [m2] at h
  set r := s%q with hr
  have hrq : r < q := Nat.mod_lt _ (by omega)
  have e2 := Nat.div_add_mod (2*r) q
  have b2 : (2*r)%q < q := Nat.mod_lt _ (by omega)
  have d2 : 2*r/q < 2 := by apply Nat.div_lt_of_lt_mul; omega
  set r2 := (2*r)%q with hr2
  set q2 := 2*r/q with hq2'
  interval_cases q2 <;> omega

-- SB2': if 2s ≡ 1 mod q then q ≤ 3*(s%q)
private lemma sb2 (q s : ℕ) (hq : 2 ≤ q) (h : (2*s)%q = 1) : q ≤ 3*(s%q) := by
  have m2 : (2*s)%q = (2*(s%q))%q := (Nat.mod_modEq s q).symm.mul_left 2
  rw [m2] at h
  set r := s%q with hr
  have hrq : r < q := Nat.mod_lt _ (by omega)
  have e2 := Nat.div_add_mod (2*r) q
  rw [h] at e2
  have d2 : 2*r/q < 2 := by apply Nat.div_lt_of_lt_mul; omega
  set q2 := 2*r/q with hq2'
  interval_cases q2 <;> omega

-- not both: for q ≠ 3, cannot have (2s)%q=1 and B-carry fire simultaneously
private lemma notboth (q s : ℕ) (hq : 2 ≤ q) (hq3 : q ≠ 3)
    (hi : (2*s)%q = 1) (hb : q ≤ s%q + (2*s)%q) : False := by
  have hmod : (2*s)%q = (2*(s%q))%q := (Nat.mod_modEq s q).symm.mul_left 2
  have b1 : s%q < q := Nat.mod_lt _ (by omega)
  have hsq : s%q = q - 1 := by omega
  rw [hsq] at hmod
  have hval : (2*(q-1))%q = q - 2 := by
    have h2 : 2*(q-1) = q + (q-2) := by omega
    rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [hval] at hmod
  omega

-- ind_iff : q ∣ (2n-1) ↔ (2n)%q = 1  (for q≥2, n≥1)
private lemma ind_iff (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    (q ∣ (2*n-1)) ↔ ((2*n)%q = 1) := by
  constructor
  · rintro ⟨m, hm⟩
    have h2 : 2*n = q*m + 1 := by omega
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  · intro h
    have e := Nat.div_add_mod (2*n) q
    rw [h] at e
    exact ⟨2*n/q, by omega⟩

private lemma core (q k j : ℕ) (hq : 2 ≤ q) (hq3 : q ≠ 3) (hn : 1 ≤ k + j) :
    (if q ∣ (2*(k+j)-1) then 1 else 0) + (if q ≤ (k+j)%q + (2*(k+j))%q then 1 else 0)
    ≤ (if q ≤ (3*k)%q + (3*k)%q then 1 else 0) + (if q ≤ k%q + (2*k)%q then 1 else 0)
      + (if q ≤ (3*j)%q + (3*j)%q then 1 else 0) + (if q ≤ j%q + (2*j)%q then 1 else 0) := by
  set n := k + j with hn_def
  -- LHS ≤ 1
  have hle : (if q ∣ (2*n-1) then 1 else 0) + (if q ≤ n%q + (2*n)%q then 1 else 0) ≤ 1 := by
    by_cases hA : q ∣ (2*n-1) <;> by_cases hB : q ≤ n%q + (2*n)%q <;>
      simp only [hA, hB, if_true, if_false] <;> try omega
    -- remaining: hA true, hB true
    exact absurd (notboth q n hq hq3 ((ind_iff q n hq hn).mp hA) hB) (by simp)
  -- if LHS ≥ 1, then q ≤ 3*(k%q)+3*(j%q)
  have hge : (q ∣ (2*n-1)) ∨ (q ≤ n%q + (2*n)%q) →
      1 ≤ (if q ≤ (3*k)%q + (3*k)%q then 1 else 0) + (if q ≤ k%q + (2*k)%q then 1 else 0)
        + (if q ≤ (3*j)%q + (3*j)%q then 1 else 0) + (if q ≤ j%q + (2*j)%q then 1 else 0) := by
    intro hAB
    have h3n : q ≤ 3*(n%q) := by
      rcases hAB with hA | hB
      · exact sb2 q n hq ((ind_iff q n hq hn).mp hA)
      · exact sb1 q n hq hB
    have hmod : n%q ≤ k%q + j%q := by
      have : n%q = (k%q + j%q)%q := by rw [hn_def, Nat.add_mod]
      rw [this]; exact Nat.mod_le _ _
    have hkey : q ≤ 3*(k%q) + 3*(j%q) := by omega
    by_contra hc
    push_neg at hc
    -- all four terms are 0
    have t1 : ¬ (q ≤ (3*k)%q + (3*k)%q) := by
      intro hcon; simp only [hcon, if_true] at hc; omega
    have t2 : ¬ (q ≤ k%q + (2*k)%q) := by
      intro hcon; simp only [hcon, if_true] at hc; omega
    have t3 : ¬ (q ≤ (3*j)%q + (3*j)%q) := by
      intro hcon; simp only [hcon, if_true] at hc; omega
    have t4 : ¬ (q ≤ j%q + (2*j)%q) := by
      intro hcon; simp only [hcon, if_true] at hc; omega
    have sk := sa q k hq t1 t2
    have sj := sa q j hq t3 t4
    omega
  -- combine
  by_cases hAB : (q ∣ (2*n-1)) ∨ (q ≤ n%q + (2*n)%q)
  · have := hge hAB
    omega
  · push_neg at hAB
    obtain ⟨hA, hB⟩ := hAB
    rw [if_neg hA, if_neg (Nat.not_le.mpr hB)]
    omega

-- test bounds
example (p m : ℕ) (hp : p.Prime) : m < p ^ m := Nat.lt_pow_self hp.one_lt

private lemma star_ne3 (p n k : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (hk : k ≤ n) (hn : 1 ≤ n) :
    (2*n-1).factorization p + ((3*n).choose n).factorization p
    ≤ ((6*k).choose (3*k)).factorization p + ((3*k).choose k).factorization p
      + ((6*(n-k)).choose (3*(n-k))).factorization p + ((3*(n-k)).choose (n-k)).factorization p := by
  set b := 6*n+1 with hb
  have hbig : (6*n : ℕ) < p^b := by
    have h1 : (6*n+1 : ℕ) < p^(6*n+1) := Nat.lt_pow_self hp.one_lt
    rw [← hb] at h1
    omega
  -- log bounds
  have hlog : ∀ m : ℕ, m ≤ 6*n → Nat.log p m < b := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.log_zero_right]; omega
    · exact (Nat.log_lt_iff_lt_pow hp.one_lt (by omega)).mpr (lt_of_le_of_lt hm hbig)
  -- express (2n-1) factorization as card
  have H2n : (2*n-1).factorization p = ∑ i ∈ Ico 1 b, (if p^i ∣ (2*n-1) then 1 else 0) := by
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega)
        (lt_of_le_of_lt (by omega : 2*n-1 ≤ 6*n) hbig), Finset.card_filter]
  have HC3n : ((3*n).choose n).factorization p
      = ∑ i ∈ Ico 1 b, (if p^i ≤ n%p^i + (2*n)%p^i then 1 else 0) := by
    rw [Nat.factorization_choose hp (by omega) (hlog (3*n) (by omega)),
        Finset.card_filter]
    apply Finset.sum_congr rfl; intro i _; rw [show 3*n-n = 2*n from by omega]
  have HC6k : ((6*k).choose (3*k)).factorization p
      = ∑ i ∈ Ico 1 b, (if p^i ≤ (3*k)%p^i + (3*k)%p^i then 1 else 0) := by
    rw [Nat.factorization_choose hp (by omega) (hlog (6*k) (by omega)),
        Finset.card_filter]
    apply Finset.sum_congr rfl; intro i _; rw [show 6*k-3*k = 3*k from by omega]
  have HC3k : ((3*k).choose k).factorization p
      = ∑ i ∈ Ico 1 b, (if p^i ≤ k%p^i + (2*k)%p^i then 1 else 0) := by
    rw [Nat.factorization_choose hp (by omega) (hlog (3*k) (by omega)),
        Finset.card_filter]
    apply Finset.sum_congr rfl; intro i _; rw [show 3*k-k = 2*k from by omega]
  have HC6j : ((6*(n-k)).choose (3*(n-k))).factorization p
      = ∑ i ∈ Ico 1 b, (if p^i ≤ (3*(n-k))%p^i + (3*(n-k))%p^i then 1 else 0) := by
    rw [Nat.factorization_choose hp (by omega) (hlog (6*(n-k)) (by omega)),
        Finset.card_filter]
    apply Finset.sum_congr rfl; intro i _; rw [show 6*(n-k)-3*(n-k) = 3*(n-k) from by omega]
  have HC3j : ((3*(n-k)).choose (n-k)).factorization p
      = ∑ i ∈ Ico 1 b, (if p^i ≤ (n-k)%p^i + (2*(n-k))%p^i then 1 else 0) := by
    rw [Nat.factorization_choose hp (by omega) (hlog (3*(n-k)) (by omega)),
        Finset.card_filter]
    apply Finset.sum_congr rfl; intro i _; rw [show 3*(n-k)-(n-k) = 2*(n-k) from by omega]
  rw [H2n, HC3n, HC6k, HC3k, HC6j, HC3j, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [mem_Ico] at hi
  set q := p^i with hqi
  have hq2 : 2 ≤ q := by
    rw [hqi]; calc 2 ≤ p := hp.two_le
      _ = p^1 := (pow_one p).symm
      _ ≤ p^i := Nat.pow_le_pow_right hp.one_lt.le hi.1
  have hq3 : q ≠ 3 := by
    rw [hqi]; intro h
    have hd : p ∣ 3 := h ▸ dvd_pow_self p (by omega : i ≠ 0)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd)
  have hc := core q k (n-k) hq2 hq3 (by omega : 1 ≤ k + (n-k))
  rw [show k+(n-k) = n from by omega] at hc
  exact hc

-- digit sum abbreviation lemmas
private lemma sh (m : ℕ) : (Nat.digits 3 (3*m)).sum = (Nat.digits 3 m).sum := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · rw [Nat.digits_base_mul (by norm_num) h]; simp

private lemma fact3_factorial (m : ℕ) :
    2 * (m !).factorization 3 = m - (Nat.digits 3 m).sum := by
  have := Nat.sub_one_mul_factorization_factorial (n := m) (p := 3) (by norm_num)
  simpa using this

private lemma key3 (a b : ℕ) :
    2 * ((a+b).choose a).factorization 3 + (Nat.digits 3 (a+b)).sum
      = (Nat.digits 3 a).sum + (Nat.digits 3 b).sum := by
  have hmul : (a+b).choose a * a ! * b ! = (a+b)! := by
    have h := Nat.add_choose_mul_factorial_mul_factorial b a
    rw [Nat.add_comm b a] at h
    rw [mul_assoc, mul_comm (b !) (a !), ← mul_assoc] at h
    exact h
  have hcpos : (a+b).choose a ≠ 0 := (Nat.choose_pos (Nat.le_add_right a b)).ne'
  have hf : ((a+b).choose a).factorization 3 + (a !).factorization 3 + (b !).factorization 3
      = ((a+b)!).factorization 3 := by
    have h1 : ((a+b).choose a * a ! * b !).factorization 3 = ((a+b)!).factorization 3 := by
      rw [hmul]
    rw [Nat.factorization_mul (by positivity) (factorial_ne_zero b),
        Nat.factorization_mul hcpos (factorial_ne_zero a)] at h1
    simpa [Finsupp.add_apply] using h1
  have da := fact3_factorial a
  have db := fact3_factorial b
  have dab := fact3_factorial (a+b)
  have ba : (Nat.digits 3 a).sum ≤ a := Nat.digit_sum_le 3 a
  have bb : (Nat.digits 3 b).sum ≤ b := Nat.digit_sum_le 3 b
  have bab : (Nat.digits 3 (a+b)).sum ≤ a+b := Nat.digit_sum_le 3 (a+b)
  omega

private lemma coprime_2m1_m1 (m : ℕ) : Nat.Coprime (2*m+1) (m+1) := by
  have h1 : Nat.gcd (2*m+1) (m+1) ∣ (2*m+1) := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (2*m+1) (m+1) ∣ (m+1) := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (2*m+1) (m+1) ∣ 1 := by
    have h := Nat.dvd_sub (h2.mul_left 2) h1
    rwa [show 2*(m+1)-(2*m+1) = 1 from by omega] at h
  exact Nat.dvd_one.mp h3

private lemma central_dvd (m : ℕ) : (2*m+1) ∣ (2*m+2).choose (m+1) := by
  have symm1 : (2*m+1).choose (m+1) = (2*m+1).choose m := by
    rw [← Nat.choose_symm (by omega : m+1 ≤ 2*m+1)]; congr 1; omega
  -- (m+1)*C(2m+1,m) = (2m+1)*C(2m,m)
  have s2 : (2*m+1) * (2*m).choose m = (2*m+1).choose (m+1) * (m+1) :=
    Nat.succ_mul_choose_eq (2*m) m
  have hdvd1 : (2*m+1) ∣ (2*m+1).choose m := by
    apply (coprime_2m1_m1 m).dvd_of_dvd_mul_right
    rw [← symm1]
    exact ⟨(2*m).choose m, by linarith [s2]⟩
  -- (2m+2)*C(2m+1,m) = C(2m+2,m+1)*(m+1)
  have s1 : (2*m+1+1) * (2*m+1).choose m = (2*m+1+1).choose (m+1) * (m+1) :=
    Nat.succ_mul_choose_eq (2*m+1) m
  apply (coprime_2m1_m1 m).dvd_of_dvd_mul_right
  have : (2*m+2).choose (m+1) * (m+1) = (2*m+2) * (2*m+1).choose m := by
    have : (2*m+1+1) = 2*m+2 := by ring
    rw [this] at s1; linarith [s1]
  rw [this]
  exact hdvd1.mul_left (2*m+2)

private lemma star_eq3 (n k : ℕ) (hk : k ≤ n) (hn : 1 ≤ n) :
    (2*n-1).factorization 3 + ((3*n).choose n).factorization 3
    ≤ ((6*k).choose (3*k)).factorization 3 + ((3*k).choose k).factorization 3
      + ((6*(n-k)).choose (3*(n-k))).factorization 3 + ((3*(n-k)).choose (n-k)).factorization 3 := by
  set j := n - k with hj
  have hkj : k + j = n := by omega
  have k1 := key3 (3*k) (3*k); rw [show 3*k+3*k = 6*k from by ring] at k1
  have k2 := key3 k (2*k); rw [show k+2*k = 3*k from by ring] at k2
  have k3 := key3 (3*j) (3*j); rw [show 3*j+3*j = 6*j from by ring] at k3
  have k4 := key3 j (2*j); rw [show j+2*j = 3*j from by ring] at k4
  have k5 := key3 n (2*n); rw [show n+2*n = 3*n from by ring] at k5
  have k6 := key3 k j; rw [hkj] at k6
  have k7 := key3 n n; rw [show n+n = 2*n from by ring] at k7
  have s1 := sh k
  have s2 := sh (2*k); rw [show 3*(2*k) = 6*k from by ring] at s2
  have s3 := sh j
  have s4 := sh (2*j); rw [show 3*(2*j) = 6*j from by ring] at s4
  have s5 := sh n
  have factle : (2*n-1).factorization 3 ≤ ((2*n).choose n).factorization 3 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
    have hd := central_dvd m
    rw [show 2*(m+1)-1 = 2*m+1 from by omega, show 2*(m+1) = 2*m+2 from by omega]
    exact Nat.factorization_le_factorization_of_dvd_right hd (by positivity)
      (Nat.choose_pos (by omega)).ne'
  omega

private lemma termwise (n k : ℕ) (hk : k ≤ n) (hn : 1 ≤ n) :
    (2*n-1) * ((3*n).choose n) ∣
      ((6*k).choose (3*k)) * ((3*k).choose k)
        * ((6*(n-k)).choose (3*(n-k))) * ((3*(n-k)).choose (n-k)) := by
  set A := (6*k).choose (3*k)
  set B := (3*k).choose k
  set C := (6*(n-k)).choose (3*(n-k))
  set D := (3*(n-k)).choose (n-k)
  have hAp : 0 < A := Nat.choose_pos (by omega)
  have hBp : 0 < B := Nat.choose_pos (by omega)
  have hCp : 0 < C := Nat.choose_pos (by omega)
  have hDp : 0 < D := Nat.choose_pos (by omega)
  have h3n : 0 < (3*n).choose n := Nat.choose_pos (by omega)
  have hden : (2*n-1) * ((3*n).choose n) ≠ 0 := Nat.mul_ne_zero (by omega) h3n.ne'
  have hM : A * B * C * D ≠ 0 := by positivity
  rw [← Nat.factorization_le_iff_dvd hden hM]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (by omega) (Nat.choose_pos (n := 3*n) (by omega)).ne',
        Nat.factorization_mul (by positivity) hDp.ne',
        Nat.factorization_mul (by positivity) hCp.ne',
        Nat.factorization_mul hAp.ne' hBp.ne']
    simp only [Finsupp.add_apply, Finsupp.coe_add, Pi.add_apply]
    by_cases hp3 : p = 3
    · subst hp3
      have := star_eq3 n k hk hn
      simpa [A, B, C, D] using this
    · have := star_ne3 p n k hp hp3 hk hn
      simpa [A, B, C, D] using this
  · rw [Nat.factorization_eq_zero_of_non_prime _ hp]
    simp


/--
Conjecture (Zhi-Wei Sun, Apr 19 2011): a(n) is an integer for every n=0,1,2,....
This conjecture states that $a(n)$ is always the result of an exact division.
Specifically, for all $n>0$, $(2n-1)\binom{3n}{n}$ divides
$\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}\binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}$.
-/
theorem oeis_a189286_conjecture_0 (n : ℕ) :
  if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int :=
by
  by_cases hn0 : n = 0
  · rw [if_pos hn0]; trivial
  · rw [if_neg hn0]
    have hpos : 1 ≤ n := by omega
    have hnat : (2*n-1) * ((3*n).choose n) ∣
        ∑ k ∈ range (n+1), T_term k * T_term (n-k) := by
      apply Finset.dvd_sum
      intro k hk
      rw [mem_range] at hk
      have hkn : k ≤ n := by omega
      have hd := termwise n k hkn hpos
      have heq : T_term k * T_term (n-k)
          = ((6*k).choose (3*k)) * ((3*k).choose k)
            * ((6*(n-k)).choose (3*(n-k))) * ((3*(n-k)).choose (n-k)) := by
        unfold T_term; ring
      rw [heq]; exact hd
    show ((2 * (n:ℤ)) - 1) * ((3 * n).choose n : ℤ) ∣
        ∑ k ∈ range (n+1), (T_term k : ℤ) * (T_term (n - k) : ℤ)
    have hcast : ((2 * (n:ℤ)) - 1) * ((3 * n).choose n : ℤ)
        = (((2*n-1) * ((3*n).choose n) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2*n)]; ring
    rw [hcast]
    have hcast2 : (∑ k ∈ range (n+1), (T_term k : ℤ) * (T_term (n - k) : ℤ))
        = (((∑ k ∈ range (n+1), T_term k * T_term (n-k)) : ℕ) : ℤ) := by
      push_cast; rfl
    rw [hcast2]
    exact_mod_cast hnat
