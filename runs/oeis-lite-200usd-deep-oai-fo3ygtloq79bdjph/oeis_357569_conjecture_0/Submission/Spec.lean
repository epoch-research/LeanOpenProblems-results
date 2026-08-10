import FormalConjectures.Util.ProblemImports
open Nat

def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

open scoped BigOperators
open Finset Nat

lemma choose_add_eq_prod (n k : ℕ) :
    (((n + k).choose k : ℚ)) =
      ∏ i ∈ Finset.range k, (((n + (i + 1) : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)) := by
  classical
  have hchoose_nat : (n + 1).ascFactorial k = k ! * (n + k).choose k := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.ascFactorial_eq_factorial_mul_choose' (n + 1) k)
  have hchoose_q : (((n + k).choose k : ℕ) : ℚ) = ((n + 1).ascFactorial k : ℚ) / (k ! : ℚ) := by
    have hfac : ((k ! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero k)
    rw [eq_div_iff_mul_eq hfac]
    rw [← Nat.cast_mul, Nat.mul_comm, ← hchoose_nat]
  have hasc_prod : (((n + 1).ascFactorial k : ℕ) : ℚ) =
      ∏ i ∈ Finset.range k, (((n + 1 + i : ℕ) : ℚ)) := by
    exact_mod_cast (Nat.ascFactorial_eq_prod_range (n + 1) k)
  have hfac_prod : (((k ! : ℕ) : ℚ)) =
      ∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℚ)) := by
    exact_mod_cast (Nat.factorial_eq_prod_range_add_one k)
  rw [hchoose_q, hasc_prod, hfac_prod]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hn : n + 1 + i = n + (i + 1) := by omega
  simp [hn]

lemma choose_mul_eq_prod (q m : ℕ) :
    ((Nat.choose ((m+1)*q) q : ℚ)) =
      ∏ i ∈ Finset.range q, (((m*q + (i+1) : ℕ) : ℚ) / ((i+1 : ℕ) : ℚ)) := by
  have h := choose_add_eq_prod (m*q) q
  have harg : m * q + q = (m + 1) * q := by ring
  rw [← harg]
  exact h

lemma choose_mul_eq_prod_Icc (q m : ℕ) :
    ((Nat.choose ((m+1)*q) q : ℚ)) =
      ∏ i ∈ Finset.Icc 1 q, (((m*q + i : ℕ) : ℚ) / (i : ℚ)) := by
  rw [choose_mul_eq_prod]
  rw [← Nat.Ico_zero_eq_range]
  rw [Finset.prod_Ico_add' (fun i : ℕ => (((m*q + i : ℕ) : ℚ) / (i : ℚ))) 0 q 1]
  rw [zero_add, Finset.Ico_add_one_right_eq_Icc]

lemma divisible_part_product (p n m q : ℕ) (hp : p ≠ 0) (hq : q = p * n) :
    (∏ i ∈ Finset.Icc 1 n, (((m*n + i : ℕ) : ℚ) / (i : ℚ))) =
      ∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i),
        (((m*q + i : ℕ) : ℚ) / (i : ℚ)) := by
  classical
  let Fq : ℕ → ℚ := fun i => (((m*q + i : ℕ) : ℚ) / (i : ℚ))
  let Fn : ℕ → ℚ := fun i => (((m*n + i : ℕ) : ℚ) / (i : ℚ))
  refine Finset.prod_bij (fun i _ => p * i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_Icc] at hi
    rcases hi with ⟨h1, h2⟩
    constructor
    · constructor
      · exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hp) (Nat.succ_le_iff.mp h1))
      · rw [hq]
        exact Nat.mul_le_mul_left p h2
    · exact ⟨i, rfl⟩
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) hab
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    rcases hb with ⟨⟨hb1, hb2⟩, ⟨a, ha⟩⟩
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · by_contra hzero
        have : a = 0 := Nat.eq_zero_of_not_pos (by simpa [Nat.succ_le_iff] using hzero)
        subst a
        simp at ha
        omega
      · rw [hq] at hb2
        rw [ha] at hb2
        exact Nat.le_of_mul_le_mul_left hb2 (Nat.pos_of_ne_zero hp)
    · exact ha.symm
  · intro i hi
    dsimp [Fn, Fq]
    rw [hq]
    have hpq : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hp
    have hnum : ((m * (p * n) + p * i : ℕ) : ℚ) = (p : ℚ) * ((m * n + i : ℕ) : ℚ) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    have hden : ((p * i : ℕ) : ℚ) = (p : ℚ) * (i : ℚ) := by norm_num [Nat.cast_mul]
    rw [hnum, hden]
    field_simp [hpq]

lemma binomial_ratio_product (p n m q : ℕ) (hp : p ≠ 0) (hn : n ≠ 0) (hq : q = p * n) :
    ((Nat.choose ((m+1)*q) q : ℚ) / (Nat.choose ((m+1)*n) n : ℚ)) =
      ∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i),
        (((m*q + i : ℕ) : ℚ) / (i : ℚ)) := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let F : ℕ → ℚ := fun i => (((m*q + i : ℕ) : ℚ) / (i : ℚ))
  have hbig : ((Nat.choose ((m+1)*q) q : ℚ)) = ∏ i ∈ Finset.Icc 1 q, F i := by
    simpa [F] using choose_mul_eq_prod_Icc q m
  have hsmall_choose : ((Nat.choose ((m+1)*n) n : ℚ)) =
      ∏ i ∈ Finset.Icc 1 n, (((m*n + i : ℕ) : ℚ) / (i : ℚ)) := by
    simpa using choose_mul_eq_prod_Icc n m
  have hdiv : ((Nat.choose ((m+1)*n) n : ℚ)) =
      ∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i), F i := by
    rw [hsmall_choose]
    simpa [F] using divisible_part_product p n m q hp hq
  have hsplit :
      (∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i), F i) *
        (∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), F i) =
          ∏ i ∈ Finset.Icc 1 q, F i := by
    simpa using (Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 q) (fun i => p ∣ i) F)
  have hden_ne : ((Nat.choose ((m+1)*n) n : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (by nlinarith [hnpos, Nat.mul_le_mul_right n (Nat.le_add_left m 1)] : n ≤ (m + 1) * n))
  have hdiv_ne : (∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i), F i) ≠ 0 := by
    simpa [hdiv] using hden_ne
  have hsplit' : ∏ i ∈ Finset.Icc 1 q, F i =
      (∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), F i) *
        (∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i), F i) := by
    rw [mul_comm]
    exact hsplit.symm
  rw [hbig, hdiv]
  exact (div_eq_of_eq_mul hdiv_ne hsplit')



lemma binomial_ratio_product_clear_denoms_nat (p n m q : ℕ)
    (hp : p ≠ 0) (hn : n ≠ 0) (hq : q = p * n) :
    Nat.choose ((m+1)*q) q *
        (∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), i)
      = Nat.choose ((m+1)*n) n *
        (∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), (m*q + i)) := by
  classical
  let S := (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i)
  let A := Nat.choose ((m+1)*q) q
  let B := Nat.choose ((m+1)*n) n
  let C := ∏ i ∈ S, (m*q + i)
  let D := ∏ i ∈ S, i
  have hrat := binomial_ratio_product p n m q hp hn hq
  have hprod :
      (∏ i ∈ S, ((((m*q + i : ℕ) : ℚ) / (i : ℚ))))
        = ((C : ℕ) : ℚ) / ((D : ℕ) : ℚ) := by
    dsimp [C, D]
    rw [Finset.prod_div_distrib]
    simp [S]
  have hrat' : ((A : ℕ) : ℚ) / ((B : ℕ) : ℚ) = ((C : ℕ) : ℚ) / ((D : ℕ) : ℚ) := by
    dsimp [A, B]
    rw [hrat]
    exact hprod
  have hB_ne : ((B : ℕ) : ℚ) ≠ 0 := by
    dsimp [B]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast (Nat.choose_ne_zero (by
      nlinarith [hnpos, Nat.mul_le_mul_right n (Nat.le_add_left m 1)] :
        n ≤ (m + 1) * n))
  have hD_pos : 0 < D := by
    dsimp [D]
    refine Finset.prod_pos ?_
    intro i hi
    have hiIcc : i ∈ Finset.Icc 1 q := (Finset.mem_filter.mp hi).1
    have : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
    exact Nat.succ_le_iff.mp this
  have hD_ne_Q : ((D : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD_pos)
  have hmainQ : ((A : ℕ) : ℚ) * ((D : ℕ) : ℚ) = ((B : ℕ) : ℚ) * ((C : ℕ) : ℚ) := by
    rw [div_eq_div_iff hB_ne hD_ne_Q] at hrat'
    simpa [mul_comm, mul_left_comm, mul_assoc] using hrat'
  have hnat : A * D = B * C := by exact_mod_cast hmainQ
  simpa [A, B, C, D, S, mul_comm, mul_left_comm, mul_assoc] using hnat

lemma zmod_prod_nat_inv_eq_inv_prod {N : ℕ} (s : Finset ℕ)
    (hcop : ∀ i ∈ s, Nat.Coprime i N) :
    (∏ i ∈ s, (i : ZMod N)) * (∏ i ∈ s, (i : ZMod N)⁻¹) = 1 := by
  classical
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (by
    intro i hi
    exact ZMod.coe_mul_inv_eq_one i (hcop i hi))

lemma binomial_product_zmod (N p n m q : ℕ)
    (hp : p ≠ 0) (hn : n ≠ 0) (hq : q = p * n)
    (hcop : ∀ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), Nat.Coprime i N) :
    ((Nat.choose ((m+1)*q) q : ℕ) : ZMod N)
      = ((Nat.choose ((m+1)*n) n : ℕ) : ZMod N) *
          ∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i),
            (((m*q + i : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹) := by
  classical
  let S := (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i)
  let A := Nat.choose ((m+1)*q) q
  let B := Nat.choose ((m+1)*n) n
  let C := ∏ i ∈ S, (m*q + i)
  let D := ∏ i ∈ S, i
  have hnat := binomial_ratio_product_clear_denoms_nat p n m q hp hn hq
  have hnat' : A * D = B * C := by
    simpa [A, B, C, D, S, mul_comm, mul_left_comm, mul_assoc] using hnat
  have hcast : (A : ZMod N) * (D : ZMod N) = (B : ZMod N) * (C : ZMod N) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    exact congrArg (fun x : ℕ => (x : ZMod N)) hnat'
  have hcopS : ∀ i ∈ S, Nat.Coprime i N := by
    intro i hi
    exact hcop i hi
  have hDinv : (D : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) = 1 := by
    dsimp [D]
    rw [Nat.cast_prod]
    exact zmod_prod_nat_inv_eq_inv_prod S hcopS
  have hA : (A : ZMod N) = (B : ZMod N) * (C : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) := by
    calc
      (A : ZMod N) = (A : ZMod N) * 1 := by rw [mul_one]
      _ = (A : ZMod N) * ((D : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹)) := by rw [hDinv]
      _ = ((A : ZMod N) * (D : ZMod N)) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) := by ring
      _ = ((B : ZMod N) * (C : ZMod N)) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) := by rw [hcast]
      _ = (B : ZMod N) * (C : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) := by ring
  have hprod_rhs :
      (C : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹)
        = ∏ i ∈ S, (((m*q + i : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹) := by
    dsimp [C]
    rw [Nat.cast_prod]
    rw [← Finset.prod_mul_distrib]
  dsimp [A, B, S] at hA ⊢
  rw [hA]
  calc
    ↑(((m + 1) * n).choose n) * ↑C * (∏ i ∈ Finset.Icc 1 q with ¬p ∣ i, (↑i)⁻¹ : ZMod N)
        = ↑(((m + 1) * n).choose n) * (↑C * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹)) := by
          simp [S, mul_assoc]
    _ = ↑(((m + 1) * n).choose n) *
          (∏ i ∈ S, (((m*q + i : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹)) := by
          rw [hprod_rhs]
    _ = ↑(((m + 1) * n).choose n) *
          ∏ i ∈ Finset.Icc 1 q with ¬p ∣ i,
            (((m*q + i : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹) := by
          simp [S]

/-- Specialization of `binomial_product_zmod` to one prime-power step, with the
exact modulus appearing in `oeis_357569_conjecture_0`.  This is the product
identity used to compare `choose ((m+1)*p^r) (p^r)` with the previous level after
removing the factors divisible by `p`. -/
lemma binomial_product_prime_power_step_zmod
    (p r m : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    ((Nat.choose ((m + 1) * (p ^ r)) (p ^ r) : ℕ) : ZMod (p ^ (3 * r + 3))) =
      ((Nat.choose ((m + 1) * (p ^ (r - 1))) (p ^ (r - 1)) : ℕ) : ZMod (p ^ (3 * r + 3))) *
        ∏ i ∈ (Finset.Icc 1 (p ^ r)).filter (fun i => ¬ p ∣ i),
          (((m * (p ^ r) + i : ℕ) : ZMod (p ^ (3 * r + 3))) *
            ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hn0 : p ^ (r - 1) ≠ 0 := pow_ne_zero (r - 1) hp0
  have hq : p ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcop : ∀ i ∈ (Finset.Icc 1 (p ^ r)).filter (fun i => ¬ p ∣ i),
      Nat.Coprime i (p ^ (3 * r + 3)) := by
    intro i hi
    have hnot : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot
  simpa using
    (binomial_product_zmod (N := p ^ (3 * r + 3)) (p := p) (n := p ^ (r - 1))
      (m := m) (q := p ^ r) hp0 hn0 hq hcop)

/-- The `m = 1` instance: product formula for the central binomial coefficient
`choose (2*p^r) (p^r)` modulo the target modulus. -/
lemma choose_two_prime_power_step_product_zmod
    (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    ((Nat.choose (2 * (p ^ r)) (p ^ r) : ℕ) : ZMod (p ^ (3 * r + 3))) =
      ((Nat.choose (2 * (p ^ (r - 1))) (p ^ (r - 1)) : ℕ) : ZMod (p ^ (3 * r + 3))) *
        ∏ i ∈ (Finset.Icc 1 (p ^ r)).filter (fun i => ¬ p ∣ i),
          ((((p ^ r) + i : ℕ) : ZMod (p ^ (3 * r + 3))) *
            ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹) := by
  simpa [one_add_one_eq_two, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using (binomial_product_prime_power_step_zmod (p := p) (r := r) (m := 1) hp hr)

/-- The `m = 2` instance: product formula for `choose (3*p^r) (p^r)` modulo
the target modulus. -/
lemma choose_three_prime_power_step_product_zmod
    (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    ((Nat.choose (3 * (p ^ r)) (p ^ r) : ℕ) : ZMod (p ^ (3 * r + 3))) =
      ((Nat.choose (3 * (p ^ (r - 1))) (p ^ (r - 1)) : ℕ) : ZMod (p ^ (3 * r + 3))) *
        ∏ i ∈ (Finset.Icc 1 (p ^ r)).filter (fun i => ¬ p ∣ i),
          (((2 * (p ^ r) + i : ℕ) : ZMod (p ^ (3 * r + 3))) *
            ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹) := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.succ_eq_add_one]
    using (binomial_product_prime_power_step_zmod (p := p) (r := r) (m := 2) hp hr)

open scoped BigOperators
open Nat

def unitReps (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun i => Nat.Coprime i q)

lemma coprime_prime_pow_iff_not_dvd {p i k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    Nat.Coprime i (p ^ k) ↔ ¬ p ∣ i := by
  constructor
  · intro h hdiv
    have hpdvd : p ∣ p^k := dvd_pow_self p (Nat.ne_of_gt hk)
    have hpdvdg : p ∣ Nat.gcd i (p^k) := Nat.dvd_gcd hdiv hpdvd
    rw [h.gcd_eq_one] at hpdvdg
    exact hp.not_dvd_one hpdvdg
  · intro hnot
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot

lemma prime_pow_one_lt {p r : ℕ} (hp : Nat.Prime p) (hr : 1 ≤ r) : 1 < p^r := by
  have hp2 : 2 ≤ p := hp.two_le
  exact one_lt_pow₀ (by omega) (Nat.ne_of_gt (by omega : 0 < r))

lemma unitReps_eq_Icc_filter_not_dvd (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    unitReps (p^r) = (Finset.Icc 1 (p^r)).filter (fun i => ¬ p ∣ i) := by
  classical
  ext i
  simp only [unitReps, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · intro h
    rcases h with ⟨hi_lt, hcop⟩
    have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hcop
    have hi_pos : 1 ≤ i := by
      by_contra hle
      have hi0 : i = 0 := by omega
      subst i
      have hq1 : 1 < p^r := prime_pow_one_lt hp hr
      have : ¬ Nat.Coprime 0 (p^r) := by
        intro hc
        rw [Nat.coprime_zero_left] at hc
        omega
      exact this hcop
    exact ⟨⟨hi_pos, le_of_lt hi_lt⟩, hnot⟩
  · intro h
    rcases h with ⟨⟨hi1, hi_le⟩, hnot⟩
    have hi_ne_q : i ≠ p^r := by
      intro hiq
      apply hnot
      rw [hiq]
      exact dvd_pow_self p (Nat.ne_of_gt (by omega : 0 < r))
    have hi_lt : i < p^r := lt_of_le_of_ne hi_le hi_ne_q
    have hcop : Nat.Coprime i (p^r) := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mpr hnot
    exact ⟨hi_lt, hcop⟩

lemma unitReps_q_sub_mem {q i : ℕ} (hq1 : 1 < q) (hi : i ∈ unitReps q) : q - i ∈ unitReps q := by
  classical
  rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi ⊢
  rcases hi with ⟨hi_lt, hcop⟩
  have hi_pos : 0 < i := by
    by_contra hz
    have hi0 : i = 0 := by omega
    subst i
    simp at hcop
    omega
  have hsub_pos : 0 < q - i := Nat.sub_pos_of_lt hi_lt
  constructor
  · exact Nat.sub_lt (by omega : 0 < q) hi_pos
  · rw [Nat.coprime_comm]
    rw [Nat.coprime_comm] at hcop
    exact Nat.Coprime.symm ((Nat.coprime_self_sub_left (le_of_lt hi_lt)).mpr hcop.symm)

lemma unitReps_q_sub_involutive {q i : ℕ} (hi : i ∈ unitReps q) : q - (q - i) = i := by
  rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
  exact Nat.sub_sub_self (le_of_lt hi.1)

open scoped BigOperators
open Nat

noncomputable def ratioProd (M q m : ℕ) : ZMod M :=
  ∏ i ∈ unitReps q,
    (1 + ((m * q : ℕ) : ZMod M) * ((i : ℕ) : ZMod M)⁻¹)

lemma prime_pow_step_product_as_ratioProd
    (p r m : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    let q := p^r
    let M := p ^ (3 * r + 3)
    ((Nat.choose ((m + 1) * q) q : ℕ) : ZMod M) =
      ((Nat.choose ((m + 1) * (p ^ (r - 1))) (p ^ (r - 1)) : ℕ) : ZMod M) *
        ratioProd M q m := by
  classical
  intro q M
  subst q
  subst M
  have hbase := binomial_product_prime_power_step_zmod (p := p) (r := r) (m := m) hp hr
  rw [hbase]
  congr 1
  have hset := (unitReps_eq_Icc_filter_not_dvd p r hp hr).symm
  rw [hset]
  apply Finset.prod_congr rfl
  intro i hi
  rw [unitReps, Finset.mem_filter] at hi
  have hcop_q : Nat.Coprime i (p^r) := hi.2
  have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hcop_q
  have hcopM : Nat.Coprime i (p ^ (3 * r + 3)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot
  have hiinv : ((i : ℕ) : ZMod (p ^ (3 * r + 3))) * ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one i hcopM
  calc
    (((m * (p ^ r) + i : ℕ) : ZMod (p ^ (3 * r + 3))) * ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹)
        = (((m * (p ^ r) : ℕ) : ZMod (p ^ (3 * r + 3))) + (i : ZMod (p ^ (3 * r + 3)))) * ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹ := by
          rw [Nat.cast_add]
    _ = 1 + ((m * (p ^ r : ℕ) : ℕ) : ZMod (p ^ (3 * r + 3))) * ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹ := by
          rw [add_mul, hiinv]
          ring

lemma pair_factor_identity_zmod
    (M q m i : ℕ) (hi_le : i ≤ q)
    (hcop_i : Nat.Coprime i M) (hcop_qi : Nat.Coprime (q - i) M) :
    let R := ZMod M
    (1 + ((m * q : ℕ) : R) * ((i : ℕ) : R)⁻¹) *
      (1 + ((m * q : ℕ) : R) * (((q - i : ℕ) : R)⁻¹)) =
    1 + ((m * (m + 1) : ℕ) : R) * (q : R)^2 *
      ((((i : ℕ) : R) * ((q - i : ℕ) : R))⁻¹) := by
  intro R
  let x : R := i
  let y : R := q - i
  let z : R := (i : R)⁻¹
  let w : R := ((q - i : ℕ) : R)⁻¹
  have hxz : x * z = 1 := by simpa [x, z] using ZMod.coe_mul_inv_eq_one i hcop_i
  have hqsub : y = ((q - i : ℕ) : R) := by
    dsimp [y]
    rw [Nat.cast_sub hi_le]
  have hyw : y * w = 1 := by
    rw [hqsub]
    change (((q - i : ℕ) : R) * (((q - i : ℕ) : R)⁻¹)) = 1
    exact ZMod.coe_mul_inv_eq_one (q - i) hcop_qi
  have hxy : x + y = (q : R) := by
    rw [hqsub]
    dsimp [x]
    rw [← Nat.cast_add, Nat.add_sub_of_le hi_le]
  have hinvxy : (((i : ℕ) : R) * ((q - i : ℕ) : R))⁻¹ = z * w := by
    apply ZMod.inv_eq_of_mul_eq_one
    dsimp [z, w]
    calc
      (((i : ℕ) : R) * ((q - i : ℕ) : R)) * ((i : R)⁻¹ * (((q - i : ℕ) : R)⁻¹))
          = (((i : ℕ) : R) * ((i : R)⁻¹)) * (((q - i : ℕ) : R) * (((q - i : ℕ) : R)⁻¹)) := by ring
      _ = 1 := by rw [ZMod.coe_mul_inv_eq_one i hcop_i, ZMod.coe_mul_inv_eq_one (q - i) hcop_qi, one_mul]
  have hzw_sum : z + w = (q : R) * (z * w) := by
    calc
      z + w = (y * w) * z + (x * z) * w := by rw [hyw, hxz]; ring
      _ = (x + y) * (z * w) := by ring
      _ = (q : R) * (z * w) := by rw [hxy]
  rw [hinvxy]
  change (1 + ((m * q : ℕ) : R) * z) * (1 + ((m * q : ℕ) : R) * w) =
    1 + ((m * (m + 1) : ℕ) : R) * (q : R)^2 * (z * w)
  have hmq : ((m * q : ℕ) : R) = (m : R) * (q : R) := by norm_num [Nat.cast_mul]
  have hmm1 : ((m * (m + 1) : ℕ) : R) = (m : R) * ((m : R) + 1) := by
    norm_num [Nat.cast_mul, Nat.cast_add]
  rw [hmq, hmm1]
  calc
    (1 + (m : R) * (q : R) * z) * (1 + (m : R) * (q : R) * w)
        = 1 + (m : R) * (q : R) * (z + w) + ((m : R) * (q : R))^2 * (z * w) := by ring
    _ = 1 + (m : R) * ((m : R) + 1) * (q : R)^2 * (z * w) := by
      rw [hzw_sum]
      ring

noncomputable def pairedProd (M q A : ℕ) : ZMod M :=
  ∏ i ∈ unitReps q,
    (1 + ((A : ℕ) : ZMod M) * (q : ZMod M)^2 *
      ((((i : ℕ) : ZMod M) * ((q - i : ℕ) : ZMod M))⁻¹))

lemma ratioProd_sq_eq_pairedProd
    (p r m : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    let q := p^r
    let M := p ^ (3 * r + 3)
    ratioProd M q m ^ 2 = pairedProd M q (m * (m + 1)) := by
  classical
  intro q M
  subst q
  subst M
  let U := unitReps (p^r)
  let f : ℕ → ZMod (p ^ (3 * r + 3)) := fun i =>
    (1 + ((m * (p^r) : ℕ) : ZMod (p ^ (3 * r + 3))) * ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹)
  let g : ℕ → ZMod (p ^ (3 * r + 3)) := fun i =>
    1 + (((m * (m + 1) : ℕ) : ZMod (p ^ (3 * r + 3))) * (p^r : ZMod (p ^ (3 * r + 3)))^2 *
      ((((i : ℕ) : ZMod (p ^ (3 * r + 3))) * ((p^r - i : ℕ) : ZMod (p ^ (3 * r + 3))))⁻¹))
  have hq1 : 1 < p^r := prime_pow_one_lt hp hr
  have hperm : (∏ i ∈ U, f (p^r - i)) = (∏ i ∈ U, f i) := by
    refine Finset.prod_bij' (fun i hi => p^r - i) (fun i hi => p^r - i) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      dsimp [U] at hi ⊢
      exact unitReps_q_sub_mem hq1 hi
    · intro i hi
      dsimp [U] at hi ⊢
      exact unitReps_q_sub_mem hq1 hi
    · intro i hi
      dsimp [U] at hi ⊢
      exact unitReps_q_sub_involutive hi
    · intro i hi
      dsimp [U] at hi ⊢
      exact unitReps_q_sub_involutive hi
    · intro i hi
      rfl
  dsimp [ratioProd, pairedProd]
  simpa [U, f, g] using (show (∏ i ∈ U, f i) ^ 2 = ∏ i ∈ U, g i from by
  calc
    (∏ i ∈ U, f i) ^ 2 = (∏ i ∈ U, f i) * (∏ i ∈ U, f i) := by rw [pow_two]
    _ = (∏ i ∈ U, f i) * (∏ i ∈ U, f (p^r - i)) := by rw [hperm]
    _ = ∏ i ∈ U, (f i * f (p^r - i)) := by rw [← Finset.prod_mul_distrib]
    _ = ∏ i ∈ U, g i := by
        apply Finset.prod_congr rfl
        intro i hi
        have hiU : i ∈ unitReps (p^r) := by simpa [U] using hi
        rw [unitReps, Finset.mem_filter, Finset.mem_range] at hiU
        have hi_le : i ≤ p^r := le_of_lt hiU.1
        have hcopq : Nat.Coprime i (p^r) := hiU.2
        have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hcopq
        have hcopM : Nat.Coprime i (p ^ (3 * r + 3)) := by
          apply Nat.Coprime.pow_right
          rw [Nat.coprime_comm]
          exact hp.coprime_iff_not_dvd.mpr hnot
        have hcopqi_q : Nat.Coprime (p^r - i) (p^r) := by
          have hmemqi := unitReps_q_sub_mem hq1 (by simpa [unitReps, Finset.mem_filter, Finset.mem_range] using ⟨hiU.1, hiU.2⟩)
          rw [unitReps, Finset.mem_filter, Finset.mem_range] at hmemqi
          exact hmemqi.2
        have hnotqi : ¬ p ∣ (p^r - i) := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hcopqi_q
        have hcopqiM : Nat.Coprime (p^r - i) (p ^ (3 * r + 3)) := by
          apply Nat.Coprime.pow_right
          rw [Nat.coprime_comm]
          exact hp.coprime_iff_not_dvd.mpr hnotqi
        dsimp [f, g]
        simpa [mul_assoc] using
          (pair_factor_identity_zmod (M := p ^ (3 * r + 3)) (q := p^r) (m := m) (i := i) hi_le hcopM hcopqiM)
  )

lemma ratioProd_sq_eq_pairedProd_generic
    (M q m : ℕ) (hq1 : 1 < q)
    (hcopM : ∀ i ∈ unitReps q, Nat.Coprime i M)
    (hcopqsubM : ∀ i ∈ unitReps q, Nat.Coprime (q - i) M) :
    ratioProd M q m ^ 2 = pairedProd M q (m * (m + 1)) := by
  classical
  let U := unitReps q
  let f : ℕ → ZMod M := fun i =>
    (1 + ((m * q : ℕ) : ZMod M) * ((i : ℕ) : ZMod M)⁻¹)
  let g : ℕ → ZMod M := fun i =>
    1 + (((m * (m + 1) : ℕ) : ZMod M) * (q : ZMod M)^2 *
      ((((i : ℕ) : ZMod M) * ((q - i : ℕ) : ZMod M))⁻¹))
  have hperm : (∏ i ∈ U, f (q - i)) = (∏ i ∈ U, f i) := by
    refine Finset.prod_bij' (fun i hi => q - i) (fun i hi => q - i) ?_ ?_ ?_ ?_ ?_
    · intro i hi; dsimp [U] at hi ⊢; exact unitReps_q_sub_mem hq1 hi
    · intro i hi; dsimp [U] at hi ⊢; exact unitReps_q_sub_mem hq1 hi
    · intro i hi; dsimp [U] at hi ⊢; exact unitReps_q_sub_involutive hi
    · intro i hi; dsimp [U] at hi ⊢; exact unitReps_q_sub_involutive hi
    · intro i hi; rfl
  dsimp [ratioProd, pairedProd]
  simpa [U, f, g] using (show (∏ i ∈ U, f i) ^ 2 = ∏ i ∈ U, g i from by
  calc
    (∏ i ∈ U, f i) ^ 2 = (∏ i ∈ U, f i) * (∏ i ∈ U, f i) := by rw [pow_two]
    _ = (∏ i ∈ U, f i) * (∏ i ∈ U, f (q - i)) := by rw [hperm]
    _ = ∏ i ∈ U, (f i * f (q - i)) := by rw [← Finset.prod_mul_distrib]
    _ = ∏ i ∈ U, g i := by
      apply Finset.prod_congr rfl
      intro i hi
      have hiU_mem : i ∈ unitReps q := by simpa [U] using hi
      have hiU : i < q ∧ i.Coprime q := by
        rw [unitReps, Finset.mem_filter, Finset.mem_range] at hiU_mem
        exact hiU_mem
      have hi_le : i ≤ q := le_of_lt hiU.1
      dsimp [f, g]
      simpa [mul_assoc] using
        (pair_factor_identity_zmod (M := M) (q := q) (m := m) (i := i) hi_le (hcopM i hiU_mem) (hcopqsubM i hiU_mem))
  )
open scoped BigOperators

lemma zmod_q_mul_eq_zero_of_cast_eq_zero (q : ℕ) [NeZero (q^2)] (z : ZMod (q^2))
    (h : (ZMod.cast z : ZMod q) = 0) : (q : ZMod (q^2)) * z = 0 := by
  rw [← ZMod.natCast_zmod_val z]
  rw [← Nat.cast_mul]
  rw [ZMod.natCast_eq_zero_iff]
  have hdiv : q ∣ q^2 := by exact dvd_pow_self q (by norm_num)
  have hv : q ∣ z.val := by
    rw [← ZMod.natCast_zmod_val z] at h
    rw [ZMod.cast_natCast hdiv] at h
    exact (ZMod.natCast_eq_zero_iff z.val q).mp h
  obtain ⟨k,hk⟩ := hv
  rw [hk]
  rw [pow_two]
  rw [← Nat.mul_assoc]
  exact dvd_mul_right (q*q) k

lemma zmod_cast_inv_of_coprime (q i : ℕ) [NeZero q] [NeZero (q^2)] (hcop : Nat.Coprime i q) :
    (ZMod.cast (((i : ZMod (q^2))⁻¹)) : ZMod q) = ((i : ZMod q)⁻¹) := by
  have hdiv : q ∣ q^2 := by exact dvd_pow_self q (by norm_num)
  have hcop2 : Nat.Coprime i (q^2) := Nat.Coprime.pow_right 2 hcop
  have hmul2 : (i : ZMod (q^2)) * ((i : ZMod (q^2))⁻¹) = 1 := by
    exact ZMod.coe_mul_inv_eq_one (n := q^2) i hcop2
  have hmulq : (i : ZMod q) * (ZMod.cast (((i : ZMod (q^2))⁻¹)) : ZMod q) = 1 := by
    calc
      (i : ZMod q) * (ZMod.cast (((i : ZMod (q^2))⁻¹)) : ZMod q)
          = (ZMod.cast ((i : ZMod (q^2)) * ((i : ZMod (q^2))⁻¹)) : ZMod q) := by
            rw [ZMod.cast_mul hdiv, ZMod.cast_natCast hdiv]
      _ = 1 := by rw [hmul2, ZMod.cast_one hdiv]
  exact (ZMod.inv_eq_of_mul_eq_one q (i : ZMod q) (ZMod.cast (((i : ZMod (q^2))⁻¹)) : ZMod q) hmulq).symm

lemma sum_range_coprime_inv_sq_eq_units (q : ℕ) [NeZero q] :
    (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q), ((i : ZMod q)⁻¹) ^ 2) =
      (∑ u : (ZMod q)ˣ, (((u : ZMod q)⁻¹) ^ 2)) := by
  classical
  let s := (Finset.range q).filter (fun i => Nat.Coprime i q)
  let f := fun i : ℕ => ((i : ZMod q)⁻¹) ^ 2
  let g := fun u : (ZMod q)ˣ => (((u : ZMod q)⁻¹) ^ 2)
  change (∑ i ∈ s, f i) = ∑ u ∈ (Finset.univ : Finset (ZMod q)ˣ), g u
  refine Finset.sum_bij (fun i hi => ZMod.unitOfCoprime i ?_) ?_ ?_ ?_ ?_
  · have hi' : i ∈ s := hi
    simp [s] at hi'
    exact hi'.2
  · intro i hi
    simp
  · intro a ha b hb hab
    have ha' : a < q := by
      have : a ∈ s := ha; simp [s] at this; exact this.1
    have hb' : b < q := by
      have : b ∈ s := hb; simp [s] at this; exact this.1
    apply_fun ((fun u : (ZMod q)ˣ => (u : ZMod q)) : (ZMod q)ˣ → ZMod q) at hab
    have hv := congrArg ZMod.val hab
    simp [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at hv
    exact hv
  · intro u hu
    refine ⟨(u : ZMod q).val, ?_, ?_⟩
    · simp [s, ZMod.val_lt]
      exact ZMod.val_coe_unit_coprime u
    · ext
      simp [ZMod.coe_unitOfCoprime]
  · intro i hi
    change ((i : ZMod q)⁻¹) ^ 2 = ((((ZMod.unitOfCoprime i (by
      have hi' : i ∈ s := hi
      simp [s] at hi'
      exact hi'.2) : (ZMod q)ˣ) : ZMod q)⁻¹) ^ 2)
    rw [ZMod.coe_unitOfCoprime]

lemma zmod_prime_pow_units_sq_sum_eq_zero (p n : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (_hn : 1 ≤ n) :
    (∑ x : (ZMod (p ^ n))ˣ, ((x : ZMod (p ^ n)) ^ 2)) = 0 := by
  let R := ZMod (p ^ n)
  let S : R := ∑ x : Rˣ, ((x : R) ^ 2)
  have hp : p.Prime := Fact.out
  have h2cop : Nat.Coprime 2 (p ^ n) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by
      intro h
      have hp_le_2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
      omega)
  have h3cop : Nat.Coprime 3 (p ^ n) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by
      intro h
      have hp_le_3 : p ≤ 3 := Nat.le_of_dvd (by norm_num) h
      omega)
  have h2is : IsUnit (2 : R) := (ZMod.isUnit_iff_coprime 2 (p ^ n)).mpr h2cop
  have h3is : IsUnit (3 : R) := (ZMod.isUnit_iff_coprime 3 (p ^ n)).mpr h3cop
  let u : Rˣ := h2is.unit
  have hu : (u : R) = 2 := h2is.unit_spec
  have hperm : (∑ x : Rˣ, (((u * x : Rˣ) : R) ^ 2)) = S := by
    simpa [S] using (Equiv.sum_comp (Equiv.mulLeft u) (fun x : Rˣ => ((x : R) ^ 2)))
  have hscale : (∑ x : Rˣ, (((u * x : Rˣ) : R) ^ 2)) = (2 : R) ^ 2 * S := by
    simp [S, hu, mul_pow, Finset.mul_sum]
  have hS : S = (2 : R) ^ 2 * S := hperm.symm.trans hscale
  have h3S : (3 : R) * S = 0 := by
    calc
      (3 : R) * S = ((2 : R) ^ 2 - 1) * S := by ring
      _ = (2 : R) ^ 2 * S - S := by ring
      _ = S - S := by rw [← hS]
      _ = 0 := sub_self S
  let v : Rˣ := h3is.unit
  have hv : (v : R) = 3 := h3is.unit_spec
  have hvS : (v : R) * S = 0 := by simpa [hv] using h3S
  have : S = 0 := by
    calc
      S = ((v⁻¹ : Rˣ) : R) * ((v : R) * S) := by simp
      _ = 0 := by rw [hvS, mul_zero]
  simpa [S, R] using this

lemma zmod_prime_pow_units_inv_sq_sum_eq_zero (p n : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 1 ≤ n) :
    (∑ x : (ZMod (p ^ n))ˣ, (((x : ZMod (p ^ n))⁻¹) ^ 2)) = 0 := by
  classical
  have hsquares := zmod_prime_pow_units_sq_sum_eq_zero p n hp5 hn
  have hperm :
      (∑ x : (ZMod (p ^ n))ˣ, (((x : ZMod (p ^ n))⁻¹) ^ 2)) =
        ∑ x : (ZMod (p ^ n))ˣ, ((x : ZMod (p ^ n)) ^ 2) := by
    refine Fintype.sum_equiv (Equiv.inv ((ZMod (p ^ n))ˣ)) _ _ ?_
    intro x
    rw [Equiv.inv_apply]
    have hinv : ((x : ZMod (p ^ n))⁻¹) = ((x⁻¹ : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) := by
      exact ZMod.inv_eq_of_mul_eq_one (p ^ n) (x : ZMod (p ^ n)) ((x⁻¹ : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) (by exact x.val_inv)
    rw [hinv]
  rw [hperm]
  exact hsquares

lemma q_mul_representative_inv_sq_sum_eq_zero
    (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    let q := p ^ r
    (q : ZMod (q^2)) *
      (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q), ((i : ZMod (q^2))⁻¹) ^ 2) = 0 := by
  intro q
  have hp : p.Prime := Fact.out
  have hq0 : q ≠ 0 := by exact pow_ne_zero r hp.ne_zero
  haveI : NeZero q := ⟨hq0⟩
  haveI : NeZero (q^2) := ⟨pow_ne_zero 2 hq0⟩
  apply zmod_q_mul_eq_zero_of_cast_eq_zero q
  have hdiv : q ∣ q^2 := by exact dvd_pow_self q (by norm_num)
  change (ZMod.castHom hdiv (ZMod q)) (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q), ((i : ZMod (q^2))⁻¹) ^ 2) = 0
  rw [map_sum]
  -- maybe simp casts over filtered sum and inv
  have hcast_terms :
      (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q),
          ((ZMod.castHom hdiv (ZMod q)) (((i : ZMod (q^2))⁻¹ ^ 2)) : ZMod q)) =
      (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q), ((i : ZMod q)⁻¹) ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hicop : Nat.Coprime i q := by simpa using (Finset.mem_filter.mp hi).2
    rw [map_pow]
    rw [ZMod.castHom_apply]
    rw [zmod_cast_inv_of_coprime q i hicop]
  rw [hcast_terms]
  rw [sum_range_coprime_inv_sq_eq_units q]
  simpa [q] using zmod_prime_pow_units_inv_sq_sum_eq_zero p r hp5 hr
lemma inv_add_inv_q_sub (q i : ℕ) (hcop : i.Coprime (q ^ 2)) :
    let R := ZMod (q ^ 2)
    ((i : R)⁻¹ + (((q : R) - (i : R))⁻¹)) =
      - (q : R) * ((i : R)⁻¹) ^ 2 := by
  intro R
  let x : R := i
  let y : R := q
  let z : R := (i : R)⁻¹
  have hz : x * z = 1 := by
    simpa [x, z] using (ZMod.coe_mul_inv_eq_one (n := q ^ 2) i hcop)
  have hy2 : y ^ 2 = 0 := by
    change ((q : R) ^ 2) = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hmul : (y - x) * (-z - y * z ^ 2) = 1 := by
    have hxz2 : x * z ^ 2 = z := by
      calc
        x * z ^ 2 = (x * z) * z := by ring
        _ = z := by rw [hz, one_mul]
    calc
      (y - x) * (-z - y * z ^ 2)
          = -(y * z) - y^2 * z^2 + x*z + y*(x*z^2) := by ring
      _ = -(y * z) - 0 * z^2 + 1 + y*z := by rw [hy2, hz, hxz2]
      _ = 1 := by ring
  have hinv : (y - x)⁻¹ = -z - y * z ^ 2 :=
    ZMod.inv_eq_of_mul_eq_one (q ^ 2) (y - x) (-z - y * z ^ 2) hmul
  calc
    (i : R)⁻¹ + (((q : R) - (i : R))⁻¹)
        = z + (y - x)⁻¹ := by rfl
    _ = z + (-z - y * z ^ 2) := by rw [hinv]
    _ = - y * z ^ 2 := by ring
    _ = - (q : R) * ((i : R)⁻¹) ^ 2 := by rfl


/-- A reusable finite-set pairing formula.  If a finite set of representatives is stable
under `i ↦ q - i` and all representatives are units modulo `q^2`, then pairing every
term with its partner converts twice the reciprocal sum into the corresponding
inverse-square sum.  The remaining Wolstenholme step is to show that the right hand
side vanishes for the particular set of representatives modulo `p^r`. -/
lemma recip_sum_pair_formula_of_q_sub_involution
    (q : ℕ) (s : Finset ℕ)
    (hmem : ∀ i, i ∈ s → q - i ∈ s)
    (hleft : ∀ i, i ∈ s → q - (q - i) = i)
    (hcop : ∀ i, i ∈ s → i.Coprime (q ^ 2)) :
    let R := ZMod (q ^ 2);
    (2 : R) * (∑ i ∈ s, ((i : R)⁻¹)) =
      - (q : R) * (∑ i ∈ s, ((i : R)⁻¹) ^ 2) := by
  classical
  intro R
  have hsum_partner :
      (∑ i ∈ s, ((((q - i : ℕ) : R))⁻¹)) = (∑ i ∈ s, ((i : R)⁻¹)) := by
    refine Finset.sum_bij' (fun i hi => q - i) (fun i hi => q - i) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      exact hmem i hi
    · intro i hi
      exact hmem i hi
    · intro i hi
      exact hleft i hi
    · intro i hi
      exact hleft i hi
    · intro i hi
      simp
  calc
    (2 : R) * (∑ i ∈ s, ((i : R)⁻¹))
        = (∑ i ∈ s, ((i : R)⁻¹)) + (∑ i ∈ s, ((i : R)⁻¹)) := by ring
    _ = (∑ i ∈ s, ((i : R)⁻¹)) + (∑ i ∈ s, ((((q - i : ℕ) : R))⁻¹)) := by
      rw [hsum_partner]
    _ = ∑ i ∈ s, (((i : R)⁻¹) + ((((q - i : ℕ) : R))⁻¹)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ s, (- (q : R) * ((i : R)⁻¹) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hqi : ((q - i : ℕ) : R) = (q : R) - (i : R) := by
        rw [Nat.cast_sub]
        have : q - (q - i) = i := hleft i hi
        omega
      rw [hqi]
      exact inv_add_inv_q_sub q i (hcop i hi)
    _ = - (q : R) * (∑ i ∈ s, ((i : R)⁻¹) ^ 2) := by
      simp [Finset.mul_sum]


/-- A close Wolstenholme-style conclusion from the pairing formula: once the
`q`-multiple of the inverse-square sum is known to vanish and `2` is a unit, the
reciprocal sum itself is zero.  For the requested prime-power representative set,
the missing arithmetic bridge is precisely the proof of the `hsq` hypothesis from
`zmod_prime_pow_units_inv_sq_sum_eq_zero`. -/
lemma recip_sum_eq_zero_of_q_sub_involution_of_sq_sum_zero
    (q : ℕ) (s : Finset ℕ)
    (hmem : ∀ i, i ∈ s → q - i ∈ s)
    (hleft : ∀ i, i ∈ s → q - (q - i) = i)
    (hcop : ∀ i, i ∈ s → i.Coprime (q ^ 2))
    (h2 : IsUnit (2 : ZMod (q ^ 2)))
    (hsq : (q : ZMod (q ^ 2)) * (∑ i ∈ s, ((i : ZMod (q ^ 2))⁻¹) ^ 2) = 0) :
    (∑ i ∈ s, ((i : ZMod (q ^ 2))⁻¹)) = 0 := by
  classical
  let R := ZMod (q ^ 2)
  let S : R := ∑ i ∈ s, ((i : R)⁻¹)
  let T : R := ∑ i ∈ s, ((i : R)⁻¹) ^ 2
  have hpair := recip_sum_pair_formula_of_q_sub_involution q s hmem hleft hcop
  dsimp only at hpair
  have htwoS : (2 : R) * S = 0 := by
    calc
      (2 : R) * S = - (q : R) * T := by simpa [S, T, R] using hpair
      _ = 0 := by simpa [T, R] using congrArg Neg.neg hsq
  let u : Rˣ := h2.unit
  have hu : (u : R) = 2 := h2.unit_spec
  have : S = 0 := by
    calc
      S = ((u⁻¹ : Rˣ) : R) * ((u : R) * S) := by simp
      _ = ((u⁻¹ : Rˣ) : R) * ((2 : R) * S) := by rw [hu]
      _ = 0 := by rw [htwoS, mul_zero]
  simpa [S, R] using this

lemma representative_recip_sum_eq_zero
    (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    let q := p ^ r
    (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q), ((i : ZMod (q^2))⁻¹)) = 0 := by
  intro q
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : 1 < p := by omega
  have hrpos : r ≠ 0 := (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hr))
  have hq0 : q ≠ 0 := pow_ne_zero r hp0
  have hq1 : 1 < q := by
    dsimp [q]
    exact one_lt_pow₀ hp1 hrpos
  haveI : NeZero q := ⟨hq0⟩
  haveI : NeZero (q^2) := ⟨pow_ne_zero 2 hq0⟩
  let s := (Finset.range q).filter (fun i => Nat.Coprime i q)
  have hmem : ∀ i, i ∈ s → q - i ∈ s := by
    intro i hi
    have hi' : i ∈ Finset.range q ∧ Nat.Coprime i q := by simpa [s] using hi
    have hilt : i < q := Finset.mem_range.mp hi'.1
    have hicop : Nat.Coprime i q := hi'.2
    have hi0 : i ≠ 0 := by
      intro h0
      subst h0
      have : q = 1 := by simpa using hicop
      omega
    have hpos : 0 < i := Nat.pos_of_ne_zero hi0
    have hlt : q - i < q := Nat.sub_lt (Nat.zero_lt_of_lt hilt) hpos
    have hle : i ≤ q := le_of_lt hilt
    have hcop : Nat.Coprime (q - i) q := (Nat.coprime_self_sub_left hle).2 hicop
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hcop⟩
  have hleft : ∀ i, i ∈ s → q - (q - i) = i := by
    intro i hi
    have hi' : i ∈ Finset.range q ∧ Nat.Coprime i q := by simpa [s] using hi
    exact Nat.sub_sub_self (le_of_lt (Finset.mem_range.mp hi'.1))
  have hcop2 : ∀ i, i ∈ s → i.Coprime (q ^ 2) := by
    intro i hi
    have hi' : i ∈ Finset.range q ∧ Nat.Coprime i q := by simpa [s] using hi
    exact Nat.Coprime.pow_right 2 hi'.2
  have h2cop : Nat.Coprime 2 (q ^ 2) := by
    apply Nat.Coprime.pow_right
    dsimp [q]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by
      intro h
      have hp_le_2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
      omega)
  have h2unit : IsUnit (2 : ZMod (q^2)) := (ZMod.isUnit_iff_coprime 2 (q^2)).mpr h2cop
  have hsq := q_mul_representative_inv_sq_sum_eq_zero p r hp5 hr
  dsimp only at hsq
  exact recip_sum_eq_zero_of_q_sub_involution_of_sq_sum_zero q s hmem hleft hcop2 h2unit hsq
open scoped BigOperators

lemma zmod_qsq_mul_eq_zero_of_cast_eq_zero (q : ℕ) [NeZero (q^3)] (z : ZMod (q^3))
    (h : (ZMod.cast z : ZMod q) = 0) : (q : ZMod (q^3))^2 * z = 0 := by
  rw [← ZMod.natCast_zmod_val z]
  rw [← Nat.cast_pow, ← Nat.cast_mul]
  rw [ZMod.natCast_eq_zero_iff]
  have hdiv : q ∣ q^3 := by exact dvd_pow_self q (by norm_num)
  have hv : q ∣ z.val := by
    rw [← ZMod.natCast_zmod_val z] at h
    rw [ZMod.cast_natCast hdiv] at h
    exact (ZMod.natCast_eq_zero_iff z.val q).mp h
  obtain ⟨k,hk⟩ := hv
  rw [hk]
  rw [show q ^ 2 * (q * k) = q ^ 3 * k by ring]
  exact dvd_mul_right (q ^ 3) k

lemma q_pow_four_eq_zero_in_zmod_q_cubed (q : ℕ) : ((q : ZMod (q^3)) ^ 4) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow q (by norm_num : 3 ≤ 4)

lemma prod_one_add_qsq_eq_one_add_qsq_sum (q : ℕ) (s : Finset ℕ) (f : ℕ → ZMod (q^3)) :
    (∏ i ∈ s, (1 + (q : ZMod (q^3))^2 * f i)) =
      1 + (q : ZMod (q^3))^2 * (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s has ih
    simp [has, ih, Finset.sum_insert, Finset.prod_insert]
    ring_nf
    rw [q_pow_four_eq_zero_in_zmod_q_cubed]
    ring

lemma prod_one_add_qsq_eq_one_of_cast_sum_zero (q : ℕ) [NeZero (q^3)]
    (s : Finset ℕ) (f : ℕ → ZMod (q^3))
    (hsum : (ZMod.cast (∑ i ∈ s, f i) : ZMod q) = 0) :
    (∏ i ∈ s, (1 + (q : ZMod (q^3))^2 * f i)) = 1 := by
  rw [prod_one_add_qsq_eq_one_add_qsq_sum]
  rw [zmod_qsq_mul_eq_zero_of_cast_eq_zero q (∑ i ∈ s, f i) hsum]
  simp

lemma zmod_cast_inv_of_coprime_cube (q i : ℕ) [NeZero q] [NeZero (q^3)] (hcop : Nat.Coprime i q) :
    ((ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)) (((i : ZMod (q^3))⁻¹)) : ZMod q) = ((i : ZMod q)⁻¹) := by
  have hdiv : q ∣ q^3 := by exact dvd_pow_self q (by norm_num : 3 ≠ 0)
  have hcop3 : Nat.Coprime i (q^3) := Nat.Coprime.pow_right 3 hcop
  have hmul3 : (i : ZMod (q^3)) * ((i : ZMod (q^3))⁻¹) = 1 := by
    exact ZMod.coe_mul_inv_eq_one (n := q^3) i hcop3
  have hmulq : (i : ZMod q) * ((ZMod.castHom hdiv (ZMod q)) (((i : ZMod (q^3))⁻¹)) : ZMod q) = 1 := by
    rw [← ZMod.cast_natCast hdiv i]
    change (ZMod.castHom hdiv (ZMod q)) (i : ZMod (q^3)) *
        (ZMod.castHom hdiv (ZMod q)) (((i : ZMod (q^3))⁻¹)) = 1
    rw [← map_mul]
    rw [hmul3, map_one]
  exact (ZMod.inv_eq_of_mul_eq_one q (i : ZMod q) ((ZMod.castHom hdiv (ZMod q)) (((i : ZMod (q^3))⁻¹)) : ZMod q) hmulq).symm

lemma cast_inv_mul_q_sub_eq_neg_inv_sq (q i : ℕ) [NeZero q] [NeZero (q^3)]
    (hq1 : 1 < q) (hi_lt : i < q) (hcop : Nat.Coprime i q) :
    ((ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)) ((((i : ZMod (q^3)) * ((q - i : ℕ) : ZMod (q^3)))⁻¹) : ZMod (q^3)) : ZMod q) =
      - ((i : ZMod q)⁻¹)^2 := by
  have hdiv : q ∣ q^3 := by exact dvd_pow_self q (by norm_num : 3 ≠ 0)
  have hi0 : i ≠ 0 := by
    intro h0
    subst h0
    have hqeq : q = 1 := by simpa using hcop
    omega
  have hpos : 0 < i := Nat.pos_of_ne_zero hi0
  have hle : i ≤ q := le_of_lt hi_lt
  have hsubcop : Nat.Coprime (q - i) q := (Nat.coprime_self_sub_left hle).2 hcop
  have hprodcop : Nat.Coprime (i * (q - i)) q := hcop.mul_left hsubcop
  have hterm_eq : ((i : ZMod (q^3)) * ((q - i : ℕ) : ZMod (q^3))) = ((i * (q - i) : ℕ) : ZMod (q^3)) := by
    norm_num [Nat.cast_mul]
  rw [hterm_eq]
  rw [zmod_cast_inv_of_coprime_cube q (i * (q - i)) hprodcop]
  have hsub_cast : ((q - i : ℕ) : ZMod q) = - (i : ZMod q) := by
    rw [Nat.cast_sub hle]
    simp
  have hprod_cast : ((i * (q - i) : ℕ) : ZMod q) = - (i : ZMod q)^2 := by
    rw [Nat.cast_mul, hsub_cast]
    ring
  rw [hprod_cast]
  have hiunit : IsUnit (i : ZMod q) := (ZMod.isUnit_iff_coprime i q).mpr hcop
  let u : (ZMod q)ˣ := hiunit.unit
  have hu : (u : ZMod q) = i := hiunit.unit_spec
  rw [← hu]
  have hmul : (-(u : ZMod q)^2) * ( - (((u⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) = 1 := by
    rw [neg_mul_neg]
    calc
      (u : ZMod q)^2 * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)^2)
          = (((u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q))^2) := by ring
      _ = 1 := by simp
  have hinv : (-(u : ZMod q)^2)⁻¹ = - (((u⁻¹ : (ZMod q)ˣ) : ZMod q)^2) :=
    ZMod.inv_eq_of_mul_eq_one q (-(u : ZMod q)^2) (- (((u⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) hmul
  rw [hinv]
  have huinv : ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = ((u : ZMod q)⁻¹) := by
    exact (ZMod.inv_eq_of_mul_eq_one q (u : ZMod q) ((u⁻¹ : (ZMod q)ˣ) : ZMod q) (by exact u.val_inv)).symm
  rw [huinv]

lemma T_cast_sum_eq_neg_inv_sq_sum (q : ℕ) [NeZero q] [NeZero (q^3)] (hq1 : 1 < q) :
    ((ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q))
      (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q),
        ((((i : ZMod (q^3)) * ((q - i : ℕ) : ZMod (q^3)))⁻¹)) : ZMod (q^3)) : ZMod q) =
      - (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q), ((i : ZMod q)⁻¹)^2) := by
  have hdiv : q ∣ q^3 := by exact dvd_pow_self q (by norm_num : 3 ≠ 0)
  change (ZMod.castHom hdiv (ZMod q))
      (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q),
        ((((i : ZMod (q^3)) * ((q - i : ℕ) : ZMod (q^3)))⁻¹)) : ZMod (q^3)) = _
  rw [map_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_lt : i < q := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hcop : Nat.Coprime i q := (Finset.mem_filter.mp hi).2
  exact cast_inv_mul_q_sub_eq_neg_inv_sq q i hq1 hi_lt hcop

lemma T_cast_sum_zero (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    let q := p^r
    ((ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q))
      (∑ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q),
        ((((i : ZMod (q^3)) * ((q - i : ℕ) : ZMod (q^3)))⁻¹)) : ZMod (q^3)) : ZMod q) = 0 := by
  intro q
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := by omega
  have hrpos : r ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hr)
  have hq0 : q ≠ 0 := by exact pow_ne_zero r hp.ne_zero
  have hq1 : 1 < q := by
    dsimp [q]
    exact one_lt_pow₀ hp1 hrpos
  haveI : NeZero q := ⟨hq0⟩
  haveI : NeZero (q^3) := ⟨pow_ne_zero 3 hq0⟩
  rw [T_cast_sum_eq_neg_inv_sq_sum q hq1]
  rw [sum_range_coprime_inv_sq_eq_units]
  simpa [q] using congrArg Neg.neg (zmod_prime_pow_units_inv_sq_sum_eq_zero p r hp5 hr)

lemma paired_unit_product_eq_one_mod_q_cubed
    (p r A : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    let q := p^r
    (∏ i ∈ (Finset.range q).filter (fun i => Nat.Coprime i q),
      (1 + (q : ZMod (q^3))^2 *
        ((A : ZMod (q^3)) * ((((i : ZMod (q^3)) * ((q - i : ℕ) : ZMod (q^3)))⁻¹))))) = 1 := by
  intro q
  have hp : p.Prime := Fact.out
  have hq0 : q ≠ 0 := by exact pow_ne_zero r hp.ne_zero
  haveI : NeZero q := ⟨hq0⟩
  haveI : NeZero (q^3) := ⟨pow_ne_zero 3 hq0⟩
  let s := (Finset.range q).filter (fun i => Nat.Coprime i q)
  let f : ℕ → ZMod (q^3) := fun i =>
      (A : ZMod (q^3)) * ((((i : ZMod (q^3)) * ((q - i : ℕ) : ZMod (q^3)))⁻¹))
  change (∏ i ∈ s, (1 + (q : ZMod (q^3))^2 * f i)) = 1
  apply prod_one_add_qsq_eq_one_of_cast_sum_zero
  have hT := T_cast_sum_zero p r hp5 hr
  dsimp only at hT
  change (ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)) (∑ i ∈ s, f i) = 0
  rw [map_sum]
  simp_rw [f, map_mul]
  rw [← Finset.mul_sum]
  rw [← map_sum]
  change (ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)) (A : ZMod (q^3)) *
      (ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)) (∑ i ∈ s, ((((i : ZMod (q^3)) * ((q - i : ℕ) : ZMod (q^3)))⁻¹))) = 0
  rw [show (ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)) (∑ i ∈ s, ((((i : ZMod (q^3)) * ((q - i : ℕ) : ZMod (q^3)))⁻¹))) = 0 by simpa [q, s] using hT]
  simp

lemma q_pow_two_eq_zero_in_zmod_q_sq (q : ℕ) : ((q : ZMod (q^2))^2) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]

lemma prod_one_add_q_eq_one_add_q_sum (q : ℕ) (s : Finset ℕ) (f : ℕ → ZMod (q^2)) :
    (∏ i ∈ s, (1 + (q : ZMod (q^2)) * f i)) =
      1 + (q : ZMod (q^2)) * (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s has ih
    simp [has, ih, Finset.sum_insert, Finset.prod_insert]
    ring_nf
    rw [q_pow_two_eq_zero_in_zmod_q_sq]
    ring

lemma ratioProd_eq_one_mod_qsq_pge5
    (p r m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    let q := p^r
    ratioProd (q^2) q m = 1 := by
  intro q
  classical
  have hp : p.Prime := Fact.out
  have hsum := representative_recip_sum_eq_zero (p := p) (r := r) hp5 hr
  dsimp only at hsum
  dsimp [ratioProd]
  let f : ℕ → ZMod (q^2) := fun i => (m : ZMod (q^2)) * ((i : ZMod (q^2))⁻¹)
  calc
    (∏ i ∈ unitReps q, (1 + ((m * q : ℕ) : ZMod (q^2)) * ((i : ℕ) : ZMod (q^2))⁻¹))
        = ∏ i ∈ unitReps q, (1 + (q : ZMod (q^2)) * f i) := by
          apply Finset.prod_congr rfl
          intro i hi
          dsimp [f]
          norm_num [Nat.cast_mul]
          ring
    _ = 1 + (q : ZMod (q^2)) * (∑ i ∈ unitReps q, f i) := by
          rw [prod_one_add_q_eq_one_add_q_sum]
    _ = 1 := by
          dsimp [f, unitReps]
          rw [← Finset.mul_sum]
          rw [show (∑ i ∈ Finset.range q with i.Coprime q, (↑i)⁻¹ : ZMod (q^2)) = 0 by simpa [q] using hsum]
          simp
open scoped BigOperators

lemma q_pow_four_eq_zero_in_zmod_p_3r3 (p r : ℕ) (hr : 3 ≤ r) :
    let q := p^r
    ((q : ZMod (p^(3*r+3))) ^ 4) = 0 := by
  intro q
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  dsimp [q]
  rw [← pow_mul]
  apply pow_dvd_pow
  omega

lemma prod_one_add_qsq_eq_one_add_qsq_sum_high (p r : ℕ) (hr : 3 ≤ r)
    (s : Finset ℕ) (f : ℕ → ZMod (p^(3*r+3))) :
    let q := p^r
    (∏ i ∈ s, (1 + (q : ZMod (p^(3*r+3)))^2 * f i)) =
      1 + (q : ZMod (p^(3*r+3)))^2 * (∑ i ∈ s, f i) := by
  intro q
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s has ih
    simp [has, ih, Finset.sum_insert, Finset.prod_insert]
    ring_nf
    rw [q_pow_four_eq_zero_in_zmod_p_3r3 p r hr]
    ring

noncomputable def Tpair (M q : ℕ) : ZMod M :=
  ∑ i ∈ unitReps q,
    ((((i : ℕ) : ZMod M) * ((q - i : ℕ) : ZMod M))⁻¹)

lemma pairedProd_eq_one_add_linear_high
    (p r A : ℕ) (hr : 3 ≤ r) :
    let q := p^r
    let M := p ^ (3 * r + 3)
    pairedProd M q A = 1 + (A : ZMod M) * (q : ZMod M)^2 * Tpair M q := by
  classical
  intro q M
  subst q
  subst M
  let f : ℕ → ZMod (p ^ (3 * r + 3)) := fun i =>
    (A : ZMod (p ^ (3 * r + 3))) *
      ((((i : ℕ) : ZMod (p ^ (3 * r + 3))) * ((p^r - i : ℕ) : ZMod (p ^ (3 * r + 3))))⁻¹)
  have hlin := prod_one_add_qsq_eq_one_add_qsq_sum_high (p := p) (r := r) hr (s := unitReps (p^r)) (f := f)
  dsimp [pairedProd, Tpair]
  change (∏ i ∈ unitReps (p^r), (1 + (A : ZMod (p ^ (3 * r + 3))) * ((p^r : ℕ) : ZMod (p ^ (3 * r + 3)))^2 *
      ((((i : ℕ) : ZMod (p ^ (3 * r + 3))) * ((p^r - i : ℕ) : ZMod (p ^ (3 * r + 3))))⁻¹))) =
    1 + (A : ZMod (p ^ (3 * r + 3))) * ((p^r : ℕ) : ZMod (p ^ (3 * r + 3)))^2 *
      (∑ i ∈ unitReps (p^r), ((((i : ℕ) : ZMod (p ^ (3 * r + 3))) * ((p^r - i : ℕ) : ZMod (p ^ (3 * r + 3))))⁻¹))
  calc
    (∏ i ∈ unitReps (p^r), (1 + (A : ZMod (p ^ (3 * r + 3))) * ((p^r : ℕ) : ZMod (p ^ (3 * r + 3)))^2 *
      ((((i : ℕ) : ZMod (p ^ (3 * r + 3))) * ((p^r - i : ℕ) : ZMod (p ^ (3 * r + 3))))⁻¹)))
        = ∏ i ∈ unitReps (p^r), (1 + ((p^r : ℕ) : ZMod (p^(3*r+3)))^2 * f i) := by
          apply Finset.prod_congr rfl
          intro i hi
          dsimp [f]
          ring
    _ = 1 + ((p^r : ℕ) : ZMod (p^(3*r+3)))^2 * (∑ i ∈ unitReps (p^r), f i) := by
          simpa using hlin
    _ = 1 + (A : ZMod (p ^ (3 * r + 3))) * ((p^r : ℕ) : ZMod (p ^ (3 * r + 3)))^2 *
      (∑ i ∈ unitReps (p^r), ((((i : ℕ) : ZMod (p ^ (3 * r + 3))) * ((p^r - i : ℕ) : ZMod (p ^ (3 * r + 3))))⁻¹)) := by
          dsimp [f]
          rw [← Finset.mul_sum]
          ring

lemma zmod_cast_inv_of_coprime_any (M q i : ℕ) [NeZero M]
    (hdiv : q ∣ M) (hcopM : Nat.Coprime i M) (hcopq : Nat.Coprime i q) :
    ((ZMod.castHom hdiv (ZMod q)) (((i : ZMod M)⁻¹)) : ZMod q) = ((i : ZMod q)⁻¹) := by
  have hmulM : (i : ZMod M) * ((i : ZMod M)⁻¹) = 1 := by
    exact ZMod.coe_mul_inv_eq_one (n := M) i hcopM
  have hmulq : (i : ZMod q) * ((ZMod.castHom hdiv (ZMod q)) (((i : ZMod M)⁻¹)) : ZMod q) = 1 := by
    rw [← ZMod.cast_natCast hdiv i]
    change (ZMod.castHom hdiv (ZMod q)) (i : ZMod M) *
        (ZMod.castHom hdiv (ZMod q)) (((i : ZMod M)⁻¹)) = 1
    rw [← map_mul]
    rw [hmulM, map_one]
  exact (ZMod.inv_eq_of_mul_eq_one q (i : ZMod q) ((ZMod.castHom hdiv (ZMod q)) (((i : ZMod M)⁻¹)) : ZMod q) hmulq).symm

lemma cast_inv_mul_q_sub_eq_neg_inv_sq_any
    (p r i : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r)
    (hi_lt : i < p^r) (hcop : Nat.Coprime i (p^r)) :
    let q := p^r
    let M := p ^ (3 * r + 3)
    ((ZMod.castHom (show q ∣ M by
        dsimp [q, M]
        exact pow_dvd_pow p (by omega : r ≤ 3 * r + 3)) (ZMod q))
      ((((i : ZMod M) * ((q - i : ℕ) : ZMod M))⁻¹) : ZMod M) : ZMod q) =
      - ((i : ZMod q)⁻¹)^2 := by
  intro q M
  subst q
  subst M
  have hdiv : p^r ∣ p ^ (3 * r + 3) := pow_dvd_pow p (by omega : r ≤ 3 * r + 3)
  have hq1 : 1 < p^r := prime_pow_one_lt hp hr
  have hle : i ≤ p^r := le_of_lt hi_lt
  have hsubcop : Nat.Coprime (p^r - i) (p^r) := (Nat.coprime_self_sub_left hle).2 hcop
  have hprodcopq : Nat.Coprime (i * (p^r - i)) (p^r) := hcop.mul_left hsubcop
  have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hcop
  have hnotsub : ¬ p ∣ (p^r - i) := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hsubcop
  have hcopiM : Nat.Coprime i (p ^ (3 * r + 3)) := by
    apply Nat.Coprime.pow_right; rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd.mpr hnot
  have hcopsubM : Nat.Coprime (p^r - i) (p ^ (3 * r + 3)) := by
    apply Nat.Coprime.pow_right; rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd.mpr hnotsub
  have hprodM : Nat.Coprime (i * (p^r - i)) (p ^ (3 * r + 3)) := hcopiM.mul_left hcopsubM
  haveI : NeZero (p ^ (3 * r + 3)) := ⟨pow_ne_zero (3 * r + 3) hp.ne_zero⟩
  have hterm_eq : ((i : ZMod (p ^ (3 * r + 3))) * ((p^r - i : ℕ) : ZMod (p ^ (3 * r + 3)))) = ((i * (p^r - i) : ℕ) : ZMod (p ^ (3 * r + 3))) := by
    norm_num [Nat.cast_mul]
  rw [hterm_eq]
  rw [zmod_cast_inv_of_coprime_any (M := p ^ (3 * r + 3)) (q := p^r) (i := i * (p^r - i)) hdiv hprodM hprodcopq]
  have hsub_cast : ((p^r - i : ℕ) : ZMod (p^r)) = - (i : ZMod (p^r)) := by
    rw [Nat.cast_sub hle]
    simp
  have hprod_cast : ((i * (p^r - i) : ℕ) : ZMod (p^r)) = - (i : ZMod (p^r))^2 := by
    rw [Nat.cast_mul, hsub_cast]
    ring
  rw [hprod_cast]
  have hiunit : IsUnit (i : ZMod (p^r)) := (ZMod.isUnit_iff_coprime i (p^r)).mpr hcop
  let u : (ZMod (p^r))ˣ := hiunit.unit
  have hu : (u : ZMod (p^r)) = i := hiunit.unit_spec
  rw [← hu]
  have hmul : (-(u : ZMod (p^r))^2) * ( - (((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2)) = 1 := by
    rw [neg_mul_neg]
    calc
      (u : ZMod (p^r))^2 * (((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2)
          = (((u : ZMod (p^r)) * ((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)))^2) := by ring
      _ = 1 := by simp
  have hinv : (-(u : ZMod (p^r))^2)⁻¹ = - (((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2) :=
    ZMod.inv_eq_of_mul_eq_one (p^r) (-(u : ZMod (p^r))^2) (- (((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2)) hmul
  rw [hinv]
  have huinv : ((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)) = ((u : ZMod (p^r))⁻¹) := by
    exact (ZMod.inv_eq_of_mul_eq_one (p^r) (u : ZMod (p^r)) ((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)) (by exact u.val_inv)).symm
  rw [huinv]

lemma Tpair_cast_zero_pge5
    (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    let q := p^r
    let M := p ^ (3 * r + 3)
    ((ZMod.castHom (show q ∣ M by
        dsimp [q, M]
        exact pow_dvd_pow p (by omega : r ≤ 3 * r + 3)) (ZMod q)) (Tpair M q) : ZMod q) = 0 := by
  intro q M
  subst q
  subst M
  have hp : p.Prime := Fact.out
  have hdiv : p^r ∣ p ^ (3 * r + 3) := pow_dvd_pow p (by omega : r ≤ 3 * r + 3)
  dsimp [Tpair, unitReps]
  change (ZMod.castHom hdiv (ZMod (p^r)))
      (∑ i ∈ (Finset.range (p^r)).filter (fun i => Nat.Coprime i (p^r)),
        ((((i : ZMod (p ^ (3 * r + 3))) * ((p^r - i : ℕ) : ZMod (p ^ (3 * r + 3))))⁻¹)) : ZMod (p ^ (3 * r + 3))) = 0
  rw [map_sum]
  have hterms : (∑ x ∈ Finset.range (p ^ r) with x.Coprime (p ^ r),
      (ZMod.castHom hdiv (ZMod (p ^ r))) ((↑x * ↑(p ^ r - x))⁻¹ : ZMod (p ^ (3 * r + 3)))) =
      -∑ x ∈ Finset.range (p ^ r) with x.Coprime (p ^ r), ((x : ZMod (p^r))⁻¹)^2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_lt : i < p^r := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hcop : Nat.Coprime i (p^r) := (Finset.mem_filter.mp hi).2
    exact cast_inv_mul_q_sub_eq_neg_inv_sq_any (p := p) (r := r) (i := i) hp hr hi_lt hcop
  rw [hterms]
  rw [sum_range_coprime_inv_sq_eq_units]
  simpa using congrArg Neg.neg (zmod_prime_pow_units_inv_sq_sum_eq_zero p r hp5 hr)

lemma zmod_sq_eq_zero_of_cast_qsq_eq_zero_high (p r : ℕ) (hp0 : p ≠ 0) (hr : 3 ≤ r)
    (z : ZMod (p ^ (3 * r + 3)))
    (h : (ZMod.castHom (show (p^r)^2 ∣ p ^ (3 * r + 3) by
        rw [← pow_mul]
        exact pow_dvd_pow p (by omega : r * 2 ≤ 3 * r + 3)) (ZMod ((p^r)^2))) z = 0) :
    z^2 = 0 := by
  haveI : NeZero (p ^ (3 * r + 3)) := ⟨pow_ne_zero (3 * r + 3) hp0⟩
  rw [← ZMod.natCast_zmod_val z]
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hdiv : (p^r)^2 ∣ p ^ (3 * r + 3) := by
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega : r * 2 ≤ 3 * r + 3)
  have hv : (p^r)^2 ∣ z.val := by
    rw [← ZMod.natCast_zmod_val z] at h
    rw [show (ZMod.castHom hdiv (ZMod ((p^r)^2))) ((z.val : ℕ) : ZMod (p ^ (3 * r + 3))) = ((z.val : ℕ) : ZMod ((p^r)^2)) from ZMod.cast_natCast hdiv z.val] at h
    exact (ZMod.natCast_eq_zero_iff z.val ((p^r)^2)).mp h
  obtain ⟨k, hk⟩ := hv
  rw [hk]
  suffices p ^ (3 * r + 3) ∣ p ^ (4 * r) * k^2 by
    convert this using 1
    ring_nf
  exact dvd_mul_of_dvd_left (pow_dvd_pow p (by omega : 3 * r + 3 ≤ 4 * r)) (k^2)

lemma ratioProd_cast_to_qsq_pge5
    (p r m : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    let q := p^r
    (ZMod.castHom (show q^2 ∣ p ^ (3 * r + 3) by
        dsimp [q]
        rw [← pow_mul]
        exact pow_dvd_pow p (by omega : r * 2 ≤ 3 * r + 3)) (ZMod (q^2)))
      (ratioProd (p ^ (3 * r + 3)) q m) = ratioProd (q^2) q m := by
  intro q
  subst q
  classical
  haveI : NeZero (p ^ (3 * r + 3)) := ⟨pow_ne_zero (3 * r + 3) hp.ne_zero⟩
  have hdiv : (p^r)^2 ∣ p ^ (3 * r + 3) := by
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega : r * 2 ≤ 3 * r + 3)
  dsimp [ratioProd]
  change (ZMod.castHom hdiv (ZMod ((p^r)^2)))
      (∏ i ∈ unitReps (p^r), (1 + ((m * p^r : ℕ) : ZMod (p ^ (3 * r + 3))) * ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹)) =
    ∏ i ∈ unitReps (p^r), (1 + ((m * p^r : ℕ) : ZMod ((p^r)^2)) * ((i : ℕ) : ZMod ((p^r)^2))⁻¹)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_add, map_one, map_mul]
  have hcopq : Nat.Coprime i (p^r) := by
    rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
    exact hi.2
  have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hcopq
  have hcopM : Nat.Coprime i (p ^ (3 * r + 3)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot
  have hcopq2 : Nat.Coprime i ((p^r)^2) := Nat.Coprime.pow_right 2 hcopq
  have hcast_inv := zmod_cast_inv_of_coprime_any (M := p ^ (3 * r + 3)) (q := (p^r)^2) (i := i) hdiv hcopM hcopq2
  rw [hcast_inv]
  rw [show (ZMod.castHom hdiv (ZMod ((p^r)^2))) (((m * p^r : ℕ) : ZMod (p ^ (3 * r + 3)))) = (((m * p^r : ℕ) : ZMod ((p^r)^2)) : ZMod ((p^r)^2)) from ZMod.cast_natCast hdiv _]

lemma ratioProd_sub_one_sq_zero_high_pge5
    (p r m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 3 ≤ r) :
    let q := p^r
    (ratioProd (p ^ (3 * r + 3)) q m - 1)^2 = 0 := by
  intro q
  subst q
  have hp : p.Prime := Fact.out
  apply zmod_sq_eq_zero_of_cast_qsq_eq_zero_high (p := p) (r := r) hp.ne_zero hr
  rw [map_sub, map_one]
  rw [ratioProd_cast_to_qsq_pge5 (p := p) (r := r) (m := m) hp (by omega : 1 ≤ r)]
  rw [ratioProd_eq_one_mod_qsq_pge5 (p := p) (r := r) (m := m) hp5 (by omega : 1 ≤ r)]
  simp

lemma sub_one_eq_inv_two_mul_sq_sub_one_zmod (M : ℕ) (V : ZMod M)
    (h2unit : (2 : ZMod M) * (2 : ZMod M)⁻¹ = 1)
    (hsq : (V - 1)^2 = 0) :
    V - 1 = (2 : ZMod M)⁻¹ * (V^2 - 1) := by
  have hmain : V^2 - 1 = (2 : ZMod M) * (V - 1) := by
    calc
      V^2 - 1 = (2 : ZMod M) * (V - 1) + (V - 1)^2 := by ring
      _ = (2 : ZMod M) * (V - 1) := by rw [hsq, add_zero]
  calc
    V - 1 = 1 * (V - 1) := by rw [one_mul]
    _ = ((2 : ZMod M)⁻¹ * (2 : ZMod M)) * (V - 1) := by rw [mul_comm (2 : ZMod M)⁻¹ (2 : ZMod M), h2unit]
    _ = (2 : ZMod M)⁻¹ * ((2 : ZMod M) * (V - 1)) := by ring
    _ = (2 : ZMod M)⁻¹ * (V^2 - 1) := by rw [hmain]

open scoped BigOperators
open Nat

lemma zmod_isUnit_of_cast_ne_zero_prime' (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0)
    (x : ZMod (p^k)) (hcast : (ZMod.cast x : ZMod p) ≠ 0) : IsUnit x := by
  classical
  have hp : p.Prime := Fact.out
  rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm]
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  apply hcast
  have hdivpk : p ∣ p^k := dvd_pow_self p hk
  have hcastval : ((x.val : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hdiv
  calc
    ZMod.cast x = ZMod.cast ((x.val : ℕ) : ZMod (p^k)) := by rw [ZMod.natCast_zmod_val]
    _ = ((x.val : ℕ) : ZMod p) := by
      exact ZMod.cast_natCast hdivpk x.val
    _ = 0 := hcastval

lemma zmod_eq_of_sq_eq_sq_and_mod_p
    (p a : ℕ) [Fact p.Prime] (ha0 : 0 < a) (hap : a < p) (hp2 : 2 < p)
    (x : ZMod (p^3))
    (hsq : x^2 = (a : ZMod (p^3))^2)
    (hmod : (ZMod.cast x : ZMod p) = (a : ZMod p)) : x = a := by
  classical
  have hdiv : p ∣ p^3 := dvd_pow_self p (by norm_num : 3 ≠ 0)
  have hfac : (x - (a : ZMod (p^3))) * (x + (a : ZMod (p^3))) = 0 := by
    calc
      (x - (a : ZMod (p^3))) * (x + (a : ZMod (p^3))) = x^2 - (a : ZMod (p^3))^2 := by ring
      _ = 0 := by rw [hsq, sub_self]
  have hcast_sum : (ZMod.cast (x + (a : ZMod (p^3))) : ZMod p) = (2 * a : ZMod p) := by
    change (ZMod.castHom hdiv (ZMod p)) (x + (a : ZMod (p^3))) = (2 * a : ZMod p)
    rw [map_add]
    change (ZMod.cast x : ZMod p) + (ZMod.cast (a : ZMod (p^3)) : ZMod p) = (2 * a : ZMod p)
    rw [hmod]
    rw [show (ZMod.cast (a : ZMod (p^3)) : ZMod p) = (a : ZMod p) from ZMod.cast_natCast hdiv a]
    norm_num [two_mul]
  have hsum_ne : (ZMod.cast (x + (a : ZMod (p^3))) : ZMod p) ≠ 0 := by
    rw [hcast_sum]
    intro hzero
    have hp : p.Prime := Fact.out
    have hzero_nat : (((2 * a : ℕ) : ZMod p) = 0) := by
      simpa [Nat.cast_mul] using hzero
    have hmodnat : p ∣ 2 * a := by
      rw [ZMod.natCast_eq_zero_iff] at hzero_nat
      exact hzero_nat
    rcases hp.dvd_mul.mp hmodnat with hp2dvd | hpadvd
    · have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2dvd
      omega
    · have hplea : p ≤ a := Nat.le_of_dvd ha0 hpadvd
      omega
  have hunit : IsUnit (x + (a : ZMod (p^3))) :=
    zmod_isUnit_of_cast_ne_zero_prime' p 3 (by norm_num) _ hsum_ne
  rcases hunit with ⟨u, hu⟩
  have hfacu : (x - (a : ZMod (p^3))) * (u : ZMod (p^3)) = 0 := by
    simpa [hu] using hfac
  have hxsub : x - (a : ZMod (p^3)) = 0 := by
    calc
      x - (a : ZMod (p^3)) = (x - (a : ZMod (p^3))) * 1 := by rw [mul_one]
      _ = (x - (a : ZMod (p^3))) * ((u : ZMod (p^3)) * ↑u⁻¹) := by simp
      _ = ((x - (a : ZMod (p^3))) * (u : ZMod (p^3))) * ↑u⁻¹ := by ring
      _ = 0 := by rw [hfacu, zero_mul]
  exact sub_eq_zero.mp hxsub

lemma zmod_eq_two_of_sq_eq_four_and_mod_p'
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (x : ZMod (p^3))
    (hsq : x^2 = (4 : ZMod (p^3)))
    (hmod : (ZMod.cast x : ZMod p) = 2) : x = 2 := by
  have hsq' : x^2 = (2 : ZMod (p^3))^2 := by
    norm_num
    exact hsq
  exact zmod_eq_of_sq_eq_sq_and_mod_p (p := p) (a := 2) (by omega) (by omega) (by omega) x hsq' hmod

lemma zmod_eq_three_of_sq_eq_nine_and_mod_p
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (x : ZMod (p^3))
    (hsq : x^2 = (9 : ZMod (p^3)))
    (hmod : (ZMod.cast x : ZMod p) = 3) : x = 3 := by
  have hsq' : x^2 = (3 : ZMod (p^3))^2 := by
    norm_num
    exact hsq
  exact zmod_eq_of_sq_eq_sq_and_mod_p (p := p) (a := 3) (by omega) (by omega) (by omega) x hsq' hmod
open Nat

lemma choose_two_prime_pow_mod_p_all (p s : ℕ) [Fact p.Prime] :
    ((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod p) = 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * p^(s+1)) (k := p^(s+1)) (p := p)
      -- theorem h Int.ModEq between ↑choose and RHS. Try convert to ZMod equality by exact_mod_cast?
      have hz : (((2 * p^(s+1)).choose (p^(s+1)) : ℕ) : ZMod p) =
          ((((2 * p^(s+1)) % p).choose ((p^(s+1)) % p) * ((2 * p^(s+1)) / p).choose ((p^(s+1)) / p) : ℕ) : ZMod p) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact h
      rw [hz]
      have hp : p.Prime := Fact.out
      have hp0 : p ≠ 0 := hp.ne_zero
      have hpowmod : p^(s+1) % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self p (by omega))
      have h2powmod : (2 * p^(s+1)) % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) 2)
      have hdiv1 : p^(s+1) / p = p^s := by
        rw [pow_succ']; exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hp0)
      have hdiv2 : (2 * p^(s+1)) / p = 2 * p^s := by
        rw [pow_succ']
        rw [show 2 * (p * p^s) = p * (2 * p^s) by ring]
        exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hp0)
      rw [hpowmod, h2powmod, hdiv1, hdiv2]
      simp [ih]

lemma choose_two_prime_pow_mod_p (p s : ℕ) [Fact p.Prime] (hs : 1 ≤ s) :
    ((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod p) = 2 := choose_two_prime_pow_mod_p_all p s

lemma choose_three_prime_pow_mod_p_all (p s : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod p) = 3 := by
  induction s with
  | zero => simp
  | succ s ih =>
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 3 * p^(s+1)) (k := p^(s+1)) (p := p)
      have hz : (((3 * p^(s+1)).choose (p^(s+1)) : ℕ) : ZMod p) =
          ((((3 * p^(s+1)) % p).choose ((p^(s+1)) % p) * ((3 * p^(s+1)) / p).choose ((p^(s+1)) / p) : ℕ) : ZMod p) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact h
      rw [hz]
      have hp : p.Prime := Fact.out
      have hp0 : p ≠ 0 := hp.ne_zero
      have hpowmod : p^(s+1) % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self p (by omega))
      have h3powmod : (3 * p^(s+1)) % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) 3)
      have hdiv1 : p^(s+1) / p = p^s := by
        rw [pow_succ']; exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hp0)
      have hdiv3 : (3 * p^(s+1)) / p = 3 * p^s := by
        rw [pow_succ']
        rw [show 3 * (p * p^s) = p * (3 * p^s) by ring]
        exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hp0)
      rw [hpowmod, h3powmod, hdiv1, hdiv3]
      simp [ih]

lemma choose_three_prime_pow_mod_p (p s : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    ((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod p) = 3 := choose_three_prime_pow_mod_p_all p s hp5

lemma zmod_prime_units_inv_sq_sum_eq_zero_for_coeff (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ x : (ZMod p)ˣ, (((x : ZMod p)⁻¹) ^ 2)) = 0 := by
  classical
  have hp : p.Prime := Fact.out
  letI : Fintype (⊤ : Subgroup (ZMod p)ˣ) := Subtype.fintype _
  have hcard : 2 < Fintype.card (⊤ : Subgroup (ZMod p)ˣ) := by
    rw [Fintype.card_subtype]
    simp [Nat.totient_prime hp]
    omega
  have htop := FiniteField.sum_subgroup_pow_eq_zero (K := ZMod p)
    (G := (⊤ : Subgroup (ZMod p)ˣ)) (k := 2) (by norm_num) hcard
  have hsquares : (∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ 2)) = 0 := by
    have hsum :
        (∑ x : (⊤ : Subgroup (ZMod p)ˣ), (((x : (ZMod p)ˣ) : ZMod p) ^ 2)) =
          ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ 2) := by
      refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv ?_) _ _ ?_
      · intro x; simp
      · intro x; rfl
    rw [← hsum]
    exact htop
  have hperm :
      (∑ x : (ZMod p)ˣ, (((x : ZMod p)⁻¹) ^ 2)) =
        ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ 2) := by
    refine Fintype.sum_equiv (Equiv.inv ((ZMod p)ˣ)) _ _ ?_
    intro x
    rw [Equiv.inv_apply, Units.val_inv_eq_inv_val]
  rw [hperm]
  exact hsquares

lemma prime_power_step_product_ratioProd_zmod_mod
    (N p r m : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r)
    (hcop : ∀ i ∈ unitReps (p^r), Nat.Coprime i N) :
    ((Nat.choose ((m + 1) * (p ^ r)) (p ^ r) : ℕ) : ZMod N) =
      ((Nat.choose ((m + 1) * (p ^ (r - 1))) (p ^ (r - 1)) : ℕ) : ZMod N) *
        ratioProd N (p^r) m := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have hn0 : p ^ (r - 1) ≠ 0 := pow_ne_zero (r - 1) hp0
  have hq : p ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hbase := binomial_product_zmod (N := N) (p := p) (n := p^(r-1)) (m := m) (q := p^r) hp0 hn0 hq ?_
  · rw [hbase]
    congr 1
    have hset := (unitReps_eq_Icc_filter_not_dvd p r hp hr).symm
    rw [hset]
    apply Finset.prod_congr rfl
    intro i hi
    have hiU : i ∈ unitReps (p^r) := by simpa using hi
    have hcopi := hcop i hiU
    calc
      (((m * (p ^ r) + i : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹)
          = (((m * (p ^ r) : ℕ) : ZMod N) + (i : ZMod N)) * ((i : ℕ) : ZMod N)⁻¹ := by rw [Nat.cast_add]
      _ = 1 + ((m * (p ^ r : ℕ) : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹ := by
          rw [add_mul, ZMod.coe_mul_inv_eq_one i hcopi]
          ring
  · intro i hi
    have hiU : i ∈ unitReps (p^r) := by
      have hset := (unitReps_eq_Icc_filter_not_dvd p r hp hr).symm
      rw [← hset]
      exact hi
    exact hcop i hiU

lemma pairedProd_mod_p3_eq_one_pge5
    (p s A : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    pairedProd (p^3) (p^s) A = 1 := by
  classical
  have hp : p.Prime := Fact.out
  by_cases hs1 : s = 1
  · subst s
    have hp0 : p ≠ 0 := hp.ne_zero
    haveI : NeZero p := ⟨hp0⟩
    haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp0⟩
    let sset := (Finset.range p).filter (fun i => Nat.Coprime i p)
    let f : ℕ → ZMod (p^3) := fun i =>
      (A : ZMod (p^3)) * ((((i : ZMod (p^3)) * ((p - i : ℕ) : ZMod (p^3)))⁻¹))
    dsimp [pairedProd, unitReps]
    simp only [pow_one]
    calc
      (∏ i ∈ sset, (1 + (A : ZMod (p^3)) * (p : ZMod (p^3))^2 * ((((i : ZMod (p^3)) * ((p - i : ℕ) : ZMod (p^3)))⁻¹))))
          = ∏ i ∈ sset, (1 + (p : ZMod (p^3))^2 * f i) := by
            apply Finset.prod_congr rfl
            intro i hi
            dsimp [f]
            ring
      _ = 1 := by
        apply prod_one_add_qsq_eq_one_of_cast_sum_zero
        have hT : (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p))
            (∑ i ∈ sset, ((((i : ZMod (p^3)) * ((p - i : ℕ) : ZMod (p^3)))⁻¹))) = 0 := by
          have hq1 : 1 < p := by omega
          rw [T_cast_sum_eq_neg_inv_sq_sum p hq1]
          rw [sum_range_coprime_inv_sq_eq_units p]
          rw [zmod_prime_units_inv_sq_sum_eq_zero_for_coeff p hp5]
          simp
        change (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (∑ i ∈ sset, f i) = 0
        rw [map_sum]
        simp_rw [f, map_mul]
        rw [← Finset.mul_sum]
        rw [← map_sum]
        change (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (A : ZMod (p^3)) *
          (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p))
            (∑ i ∈ sset, ((((i : ZMod (p^3)) * ((p - i : ℕ) : ZMod (p^3)))⁻¹))) = 0
        rw [hT]
        simp
  · have hs2 : 2 ≤ s := by omega
    dsimp [pairedProd]
    apply Finset.prod_eq_one
    intro i hi
    suffices hz : ((p^s : ℕ) : ZMod (p^3))^2 = 0 by
      rw [hz]
      ring
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega : 3 ≤ s * 2)

lemma ratioProd_sq_eq_one_mod_p3_pge5
    (p s m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    ratioProd (p^3) (p^s) m ^ 2 = 1 := by
  have hp : p.Prime := Fact.out
  have hq1 : 1 < p^s := prime_pow_one_lt hp hs
  rw [ratioProd_sq_eq_pairedProd_generic (M := p^3) (q := p^s) (m := m) hq1]


  · exact pairedProd_mod_p3_eq_one_pge5 p s (m * (m + 1)) hp5 hs
  · intro i hi
    have hi' : i < p^s ∧ Nat.Coprime i (p^s) := by
      rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
      exact hi
    have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < s)).mp hi'.2
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot
  · intro i hi
    have hmem := unitReps_q_sub_mem hq1 hi
    have hmem' : (p^s - i) < p^s ∧ Nat.Coprime (p^s - i) (p^s) := by
      rw [unitReps, Finset.mem_filter, Finset.mem_range] at hmem
      exact hmem
    have hnot : ¬ p ∣ (p^s - i) := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < s)).mp hmem'.2
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot

lemma choose_two_prime_pow_sq_mod_p3_pge5
    (p s : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod (p^3))^2) = 4 := by
  classical
  have hp : p.Prime := Fact.out
  induction s with
  | zero => norm_num
  | succ s ih =>
      have hs1 : 1 ≤ s + 1 := by omega
      have hcop : ∀ i ∈ unitReps (p^(s+1)), Nat.Coprime i (p^3) := by
        intro i hi
        have hi' : i < p^(s+1) ∧ Nat.Coprime i (p^(s+1)) := by
          rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
          exact hi
        have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < s + 1)).mp hi'.2
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm]
        exact hp.coprime_iff_not_dvd.mpr hnot
      have hstep := prime_power_step_product_ratioProd_zmod_mod (N := p^3) (p := p) (r := s+1) (m := 1) hp hs1 hcop
      have hratio := ratioProd_sq_eq_one_mod_p3_pge5 (p := p) (s := s+1) (m := 1) hp5 hs1
      have hchoose : ((Nat.choose (2 * p^(s+1)) (p^(s+1)) : ℕ) : ZMod (p^3)) =
          ((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod (p^3)) * ratioProd (p^3) (p^(s+1)) 1 := by
        simpa [one_add_one_eq_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hstep
      rw [hchoose]
      calc
        (((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod (p^3)) * ratioProd (p^3) (p^(s+1)) 1)^2
            = (((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod (p^3))^2) * (ratioProd (p^3) (p^(s+1)) 1)^2 := by ring
        _ = 4 := by rw [ih, hratio, mul_one]

lemma choose_three_prime_pow_sq_mod_p3_pge5
    (p s : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod (p^3))^2) = 9 := by
  classical
  have hp : p.Prime := Fact.out
  induction s with
  | zero => norm_num
  | succ s ih =>
      have hs1 : 1 ≤ s + 1 := by omega
      have hcop : ∀ i ∈ unitReps (p^(s+1)), Nat.Coprime i (p^3) := by
        intro i hi
        have hi' : i < p^(s+1) ∧ Nat.Coprime i (p^(s+1)) := by
          rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
          exact hi
        have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < s + 1)).mp hi'.2
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm]
        exact hp.coprime_iff_not_dvd.mpr hnot
      have hstep := prime_power_step_product_ratioProd_zmod_mod (N := p^3) (p := p) (r := s+1) (m := 2) hp hs1 hcop
      have hratio := ratioProd_sq_eq_one_mod_p3_pge5 (p := p) (s := s+1) (m := 2) hp5 hs1
      have hchoose : ((Nat.choose (3 * p^(s+1)) (p^(s+1)) : ℕ) : ZMod (p^3)) =
          ((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod (p^3)) * ratioProd (p^3) (p^(s+1)) 2 := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.succ_eq_add_one] using hstep
      rw [hchoose]
      calc
        (((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod (p^3)) * ratioProd (p^3) (p^(s+1)) 2)^2
            = (((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod (p^3))^2) * (ratioProd (p^3) (p^(s+1)) 2)^2 := by ring
        _ = 9 := by rw [ih, hratio, mul_one]


lemma choose_two_prime_pow_mod_p3_pge5
    (p s : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod (p^3)) = 2 := by
  let x : ZMod (p^3) := ((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod (p^3))
  have hsq : x^2 = (4 : ZMod (p^3)) := by
    dsimp [x]
    exact choose_two_prime_pow_sq_mod_p3_pge5 p s hp5
  have hdiv : p ∣ p^3 := dvd_pow_self p (by norm_num : 3 ≠ 0)
  have hmod : (ZMod.cast x : ZMod p) = 2 := by
    dsimp [x]
    change (ZMod.castHom hdiv (ZMod p)) (((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod (p^3))) = 2
    rw [show (ZMod.castHom hdiv (ZMod p)) (((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod (p^3))) = (((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod p)) from ZMod.cast_natCast hdiv _]
    exact choose_two_prime_pow_mod_p_all p s
  exact zmod_eq_two_of_sq_eq_four_and_mod_p' p hp5 x hsq hmod

lemma choose_three_prime_pow_mod_p3_pge5
    (p s : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod (p^3)) = 3 := by
  let x : ZMod (p^3) := ((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod (p^3))
  have hsq : x^2 = (9 : ZMod (p^3)) := by
    dsimp [x]
    exact choose_three_prime_pow_sq_mod_p3_pge5 p s hp5
  have hdiv : p ∣ p^3 := dvd_pow_self p (by norm_num : 3 ≠ 0)
  have hmod : (ZMod.cast x : ZMod p) = 3 := by
    dsimp [x]
    change (ZMod.castHom hdiv (ZMod p)) (((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod (p^3))) = 3
    rw [show (ZMod.castHom hdiv (ZMod p)) (((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod (p^3))) = (((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod p)) from ZMod.cast_natCast hdiv _]
    exact choose_three_prime_pow_mod_p_all p s hp5
  exact zmod_eq_three_of_sq_eq_nine_and_mod_p p hp5 x hsq hmod

lemma main_coeff_mod_p3_pge5
    (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    let n := p ^ (r - 1)
    let A := Nat.choose (3 * n) n
    let B := Nat.choose (2 * n) n
    ((6 : ZMod (p^3)) * (A : ZMod (p^3))^2 - (27 : ZMod (p^3)) * (B : ZMod (p^3))) = 0 := by
  intro n A B
  rw [show (A : ZMod (p^3)) = 3 by simpa [A, n] using choose_three_prime_pow_mod_p3_pge5 p (r-1) hp5]
  rw [show (B : ZMod (p^3)) = 2 by simpa [B, n] using choose_two_prime_pow_mod_p3_pge5 p (r-1) hp5]
  norm_num

lemma coeff_qsq_T_eq_zero_of_casts_high
    (p r : ℕ) (hp0 : p ≠ 0) (hr : 1 ≤ r)
    (C T : ZMod (p ^ (3 * r + 3)))
    (hC : (ZMod.castHom (show p^3 ∣ p ^ (3 * r + 3) by
        exact pow_dvd_pow p (by omega : 3 ≤ 3 * r + 3)) (ZMod (p^3))) C = 0)
    (hT : (ZMod.castHom (show p^r ∣ p ^ (3 * r + 3) by
        exact pow_dvd_pow p (by omega : r ≤ 3 * r + 3)) (ZMod (p^r))) T = 0) :
    C * ((p^r : ℕ) : ZMod (p ^ (3 * r + 3)))^2 * T = 0 := by
  haveI : NeZero (p ^ (3 * r + 3)) := ⟨pow_ne_zero (3 * r + 3) hp0⟩
  rw [← ZMod.natCast_zmod_val C, ← ZMod.natCast_zmod_val T]
  rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  have hdivC : p^3 ∣ p ^ (3 * r + 3) := pow_dvd_pow p (by omega : 3 ≤ 3 * r + 3)
  have hdivT : p^r ∣ p ^ (3 * r + 3) := pow_dvd_pow p (by omega : r ≤ 3 * r + 3)
  have hvC : p^3 ∣ C.val := by
    rw [← ZMod.natCast_zmod_val C] at hC
    rw [show (ZMod.castHom hdivC (ZMod (p^3))) ((C.val : ℕ) : ZMod (p ^ (3 * r + 3))) = ((C.val : ℕ) : ZMod (p^3)) from ZMod.cast_natCast hdivC C.val] at hC
    exact (ZMod.natCast_eq_zero_iff C.val (p^3)).mp hC
  have hvT : p^r ∣ T.val := by
    rw [← ZMod.natCast_zmod_val T] at hT
    rw [show (ZMod.castHom hdivT (ZMod (p^r))) ((T.val : ℕ) : ZMod (p ^ (3 * r + 3))) = ((T.val : ℕ) : ZMod (p^r)) from ZMod.cast_natCast hdivT T.val] at hT
    exact (ZMod.natCast_eq_zero_iff T.val (p^r)).mp hT
  obtain ⟨a, ha⟩ := hvC
  obtain ⟨b, hb⟩ := hvT
  rw [ha, hb]
  suffices p ^ (3 * r + 3) ∣ p ^ (3 + 2*r + r) * (a * b) by
    convert this using 1
    ring_nf
  exact dvd_mul_of_dvd_left (by
    convert pow_dvd_pow p (by omega : 3 * r + 3 ≤ 3 + 2 * r + r) using 2 <;> omega) (a*b)

lemma ratioProd_sq_sub_one_high_pge5
    (p r m : ℕ) (hp : Nat.Prime p) (hr : 3 ≤ r) :
    let q := p^r
    let M := p ^ (3 * r + 3)
    ratioProd M q m ^ 2 - 1 =
      ((m * (m + 1) : ℕ) : ZMod M) * (q : ZMod M)^2 * Tpair M q := by
  intro q M
  subst q
  subst M
  rw [ratioProd_sq_eq_pairedProd (p := p) (r := r) (m := m) hp (by omega : 1 ≤ r)]
  rw [pairedProd_eq_one_add_linear_high (p := p) (r := r) (A := m * (m+1)) hr]
  ring

lemma ratioProd_sub_one_high_pge5
    (p r m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 3 ≤ r)
    (h2cop : Nat.Coprime 2 (p ^ (3 * r + 3))) :
    let q := p^r
    let M := p ^ (3 * r + 3)
    ratioProd M q m - 1 =
      (2 : ZMod M)⁻¹ * (((m * (m + 1) : ℕ) : ZMod M) * (q : ZMod M)^2 * Tpair M q) := by
  intro q M
  subst q
  subst M
  have hp : p.Prime := Fact.out
  have h2unit : (2 : ZMod (p ^ (3 * r + 3))) * (2 : ZMod (p ^ (3 * r + 3)))⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one 2 h2cop
  rw [← ratioProd_sq_sub_one_high_pge5 (p := p) (r := r) (m := m) hp hr]
  exact sub_one_eq_inv_two_mul_sq_sub_one_zmod (p ^ (3 * r + 3)) (ratioProd (p ^ (3 * r + 3)) (p^r) m) h2unit
    (ratioProd_sub_one_sq_zero_high_pge5 (p := p) (r := r) (m := m) hp5 hr)


lemma key_zmod_congruence_pge5_rge3
    (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 3 ≤ r) :
    let q := p^r
    let n := p^(r-1)
    let M := p ^ (3 * r + 3)
    let A := Nat.choose (3*n) n
    let B := Nat.choose (2*n) n
    let Aq := Nat.choose (3*q) q
    let Bq := Nat.choose (2*q) q
    ((Aq : ZMod M)^2 - (A : ZMod M)^2) = (27 : ZMod M) * ((Bq : ZMod M) - (B : ZMod M)) := by
  classical
  intro q n M A B Aq Bq
  subst q; subst n; subst M; subst A; subst B; subst Aq; subst Bq
  have hp : p.Prime := Fact.out
  have h2cop : Nat.Coprime 2 (p ^ (3 * r + 3)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by
      intro h
      have hp_le_2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
      omega)
  let U : ZMod (p ^ (3 * r + 3)) := ratioProd (p ^ (3 * r + 3)) (p^r) 2
  let V : ZMod (p ^ (3 * r + 3)) := ratioProd (p ^ (3 * r + 3)) (p^r) 1
  let T : ZMod (p ^ (3 * r + 3)) := Tpair (p ^ (3 * r + 3)) (p^r)
  let qz : ZMod (p ^ (3 * r + 3)) := (p^r : ℕ)
  let A0 : ZMod (p ^ (3 * r + 3)) := ((Nat.choose (3 * p^(r-1)) (p^(r-1)) : ℕ) : ZMod (p ^ (3 * r + 3)))
  let B0 : ZMod (p ^ (3 * r + 3)) := ((Nat.choose (2 * p^(r-1)) (p^(r-1)) : ℕ) : ZMod (p ^ (3 * r + 3)))
  have hAq : ((Nat.choose (3 * p^r) (p^r) : ℕ) : ZMod (p ^ (3 * r + 3))) = A0 * U := by
    have h := prime_pow_step_product_as_ratioProd (p := p) (r := r) (m := 2) hp (by omega : 1 ≤ r)
    dsimp only at h
    simpa [A0, U, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.succ_eq_add_one] using h
  have hBq : ((Nat.choose (2 * p^r) (p^r) : ℕ) : ZMod (p ^ (3 * r + 3))) = B0 * V := by
    have h := prime_pow_step_product_as_ratioProd (p := p) (r := r) (m := 1) hp (by omega : 1 ≤ r)
    dsimp only at h
    simpa [B0, V, one_add_one_eq_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hU : U^2 - 1 = (6 : ZMod (p ^ (3 * r + 3))) * qz^2 * T := by
    have h := ratioProd_sq_sub_one_high_pge5 (p := p) (r := r) (m := 2) hp hr
    dsimp only at h
    simpa [U, T, qz, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hVhalf := ratioProd_sub_one_high_pge5 (p := p) (r := r) (m := 1) hp5 hr h2cop
  have hV : V - 1 = qz^2 * T := by
    dsimp only at hVhalf
    have h2unit : (2 : ZMod (p ^ (3 * r + 3))) * (2 : ZMod (p ^ (3 * r + 3)))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one 2 h2cop
    have htmp : V - 1 = (2 : ZMod (p ^ (3 * r + 3)))⁻¹ * ((2 : ZMod (p ^ (3 * r + 3))) * qz^2 * T) := by
      simpa [V, T, qz, one_add_one_eq_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hVhalf
    rw [htmp]
    calc
      (2 : ZMod (p ^ (3 * r + 3)))⁻¹ * ((2 : ZMod (p ^ (3 * r + 3))) * qz^2 * T)
          = ((2 : ZMod (p ^ (3 * r + 3)))⁻¹ * (2 : ZMod (p ^ (3 * r + 3)))) * (qz^2 * T) := by ring
      _ = qz^2 * T := by rw [mul_comm (2 : ZMod (p ^ (3 * r + 3)))⁻¹ (2 : ZMod (p ^ (3 * r + 3))), h2unit, one_mul]
  have hCcast : (ZMod.castHom (show p^3 ∣ p ^ (3 * r + 3) by exact pow_dvd_pow p (by omega : 3 ≤ 3 * r + 3)) (ZMod (p^3)))
      ((6 : ZMod (p ^ (3 * r + 3))) * A0^2 - (27 : ZMod (p ^ (3 * r + 3))) * B0) = 0 := by
    let hdiv3 : p^3 ∣ p ^ (3 * r + 3) := pow_dvd_pow p (by omega : 3 ≤ 3 * r + 3)
    change (ZMod.castHom hdiv3 (ZMod (p^3)))
      ((6 : ZMod (p ^ (3 * r + 3))) * A0^2 - (27 : ZMod (p ^ (3 * r + 3))) * B0) = 0
    rw [map_sub, map_mul, map_pow, map_mul]
    rw [show (ZMod.castHom hdiv3 (ZMod (p^3))) (6 : ZMod (p ^ (3 * r + 3))) = (6 : ZMod (p^3)) from ZMod.cast_natCast hdiv3 6]
    rw [show (ZMod.castHom hdiv3 (ZMod (p^3))) (27 : ZMod (p ^ (3 * r + 3))) = (27 : ZMod (p^3)) from ZMod.cast_natCast hdiv3 27]
    rw [show (ZMod.castHom hdiv3 (ZMod (p^3))) A0 = (((Nat.choose (3 * p^(r-1)) (p^(r-1)) : ℕ) : ZMod (p^3))) by dsimp [A0]; exact ZMod.cast_natCast hdiv3 _]
    rw [show (ZMod.castHom hdiv3 (ZMod (p^3))) B0 = (((Nat.choose (2 * p^(r-1)) (p^(r-1)) : ℕ) : ZMod (p^3))) by dsimp [B0]; exact ZMod.cast_natCast hdiv3 _]
    exact main_coeff_mod_p3_pge5 p r hp5
  have hTcast : (ZMod.castHom (show p^r ∣ p ^ (3 * r + 3) by exact pow_dvd_pow p (by omega : r ≤ 3 * r + 3)) (ZMod (p^r))) T = 0 := by
    have h := Tpair_cast_zero_pge5 (p := p) (r := r) hp5 (by omega : 1 ≤ r)
    dsimp only at h
    simpa [T] using h
  have hkill : ((6 : ZMod (p ^ (3 * r + 3))) * A0^2 - (27 : ZMod (p ^ (3 * r + 3))) * B0) * qz^2 * T = 0 := by
    simpa [qz] using coeff_qsq_T_eq_zero_of_casts_high (p := p) (r := r) hp.ne_zero (by omega : 1 ≤ r)
      (((6 : ZMod (p ^ (3 * r + 3))) * A0^2 - (27 : ZMod (p ^ (3 * r + 3))) * B0)) T hCcast hTcast
  rw [hAq, hBq]
  have hgoal : A0^2 * ((6 : ZMod (p ^ (3 * r + 3))) * qz^2 * T) = (27 : ZMod (p ^ (3 * r + 3))) * (B0 * (qz^2 * T)) := by
    have hk := hkill
    ring_nf at hk ⊢
    exact sub_eq_zero.mp hk
  calc
    (A0 * U)^2 - A0^2 = A0^2 * (U^2 - 1) := by ring
    _ = A0^2 * ((6 : ZMod (p ^ (3 * r + 3))) * qz^2 * T) := by rw [hU]
    _ = (27 : ZMod (p ^ (3 * r + 3))) * (B0 * (qz^2 * T)) := hgoal
    _ = (27 : ZMod (p ^ (3 * r + 3))) * (B0 * V - B0) := by rw [show B0 * V - B0 = B0 * (V - 1) by ring, hV]

lemma int_key_congruence_of_zmod_key
    (p r : ℕ)
    (hkey :
      let q := p^r
      let n := p^(r-1)
      let M := p ^ (3 * r + 3)
      let A := Nat.choose (3*n) n
      let B := Nat.choose (2*n) n
      let Aq := Nat.choose (3*q) q
      let Bq := Nat.choose (2*q) q
      ((Aq : ZMod M)^2 - (A : ZMod M)^2) = (27 : ZMod M) * ((Bq : ZMod M) - (B : ZMod M))) :
    (Int.ofNat ((3 * (p ^ r)).choose (p ^ r))) ^ 2 -
        (Int.ofNat ((3 * (p ^ (r - 1))).choose (p ^ (r - 1)))) ^ 2 ≡
      (27 : ℤ) * (Int.ofNat ((2 * (p ^ r)).choose (p ^ r)) -
        Int.ofNat ((2 * (p ^ (r - 1))).choose (p ^ (r - 1))))
      [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  change ((p ^ (3 * r + 3) : ℕ) : ℤ).ModEq
    ((Int.ofNat ((3 * (p ^ r)).choose (p ^ r))) ^ 2 -
        (Int.ofNat ((3 * (p ^ (r - 1))).choose (p ^ (r - 1)))) ^ 2)
      ((27 : ℤ) * (Int.ofNat ((2 * (p ^ r)).choose (p ^ r)) -
        Int.ofNat ((2 * (p ^ (r - 1))).choose (p ^ (r - 1)))))
  rw [← ZMod.intCast_eq_intCast_iff]
  dsimp only at hkey
  norm_num [Int.ofNat_eq_coe]
  simpa [Nat.cast_pow, Nat.cast_mul] using hkey

lemma oeis_357569_step_of_key
    (p r : ℕ)
    (hkey :
      (Int.ofNat ((3 * (p ^ r)).choose (p ^ r))) ^ 2 -
          (Int.ofNat ((3 * (p ^ (r - 1))).choose (p ^ (r - 1)))) ^ 2 ≡
        (27 : ℤ) * (Int.ofNat ((2 * (p ^ r)).choose (p ^ r)) -
          Int.ofNat ((2 * (p ^ (r - 1))).choose (p ^ (r - 1))))
        [ZMOD ((p : ℤ) ^ (3 * r + 3))]) :
    a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  unfold a
  rw [Int.modEq_iff_dvd] at hkey ⊢
  convert hkey using 1
  ring

lemma oeis_357569_conjecture_0_pge5_rge3
    (p r : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hr3 : r ≥ 3) :
    a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  letI : Fact p.Prime := ⟨hp⟩
  apply oeis_357569_step_of_key
  exact int_key_congruence_of_zmod_key p r (key_zmod_congruence_pge5_rge3 p r hp5 hr3)

/-- For the `p = 3` branch, the reported numerics say that the coefficient
`6*A^2 - 27*B` has 3-adic valuation `5`, while the remaining paired sum has
valuation at least `r-1`.  This is the exact zero-product lemma needed in the
same final algebraic assembly used by the `p ≥ 5` proof. -/
lemma coeff_qsq_T_eq_zero_of_casts_p3
    (r : ℕ) (hr : 3 ≤ r)
    (C T : ZMod (3 ^ (3 * r + 3)))
    (hC : (ZMod.castHom (show 3^5 ∣ 3 ^ (3 * r + 3) by
        exact pow_dvd_pow 3 (by omega : 5 ≤ 3 * r + 3)) (ZMod (3^5))) C = 0)
    (hT : (ZMod.castHom (show 3^(r-1) ∣ 3 ^ (3 * r + 3) by
        exact pow_dvd_pow 3 (by omega : r - 1 ≤ 3 * r + 3)) (ZMod (3^(r-1)))) T = 0) :
    C * ((3^r : ℕ) : ZMod (3 ^ (3 * r + 3)))^2 * T = 0 := by
  have h30 : (3 : ℕ) ≠ 0 := by norm_num
  haveI : NeZero (3 ^ (3 * r + 3)) := ⟨pow_ne_zero (3 * r + 3) h30⟩
  rw [← ZMod.natCast_zmod_val C, ← ZMod.natCast_zmod_val T]
  rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  have hdivC : 3^5 ∣ 3 ^ (3 * r + 3) := pow_dvd_pow 3 (by omega : 5 ≤ 3 * r + 3)
  have hdivT : 3^(r-1) ∣ 3 ^ (3 * r + 3) := pow_dvd_pow 3 (by omega : r - 1 ≤ 3 * r + 3)
  have hvC : 3^5 ∣ C.val := by
    rw [← ZMod.natCast_zmod_val C] at hC
    rw [show (ZMod.castHom hdivC (ZMod (3^5))) ((C.val : ℕ) : ZMod (3 ^ (3 * r + 3))) = ((C.val : ℕ) : ZMod (3^5)) from ZMod.cast_natCast hdivC C.val] at hC
    exact (ZMod.natCast_eq_zero_iff C.val (3^5)).mp hC
  have hvT : 3^(r-1) ∣ T.val := by
    rw [← ZMod.natCast_zmod_val T] at hT
    rw [show (ZMod.castHom hdivT (ZMod (3^(r-1)))) ((T.val : ℕ) : ZMod (3 ^ (3 * r + 3))) = ((T.val : ℕ) : ZMod (3^(r-1))) from ZMod.cast_natCast hdivT T.val] at hT
    exact (ZMod.natCast_eq_zero_iff T.val (3^(r-1))).mp hT
  obtain ⟨a, ha⟩ := hvC
  obtain ⟨b, hb⟩ := hvT
  rw [ha, hb]
  suffices 3 ^ (3 * r + 3) ∣ 3 ^ (5 + 2*r + (r-1)) * (a * b) by
    convert this using 1
    ring_nf
  exact dvd_mul_of_dvd_left (by
    convert pow_dvd_pow 3 (by omega : 3 * r + 3 ≤ 5 + 2 * r + (r - 1)) using 2 <;> omega) (a*b)

/-- The square-ratio linearization used in the p=3 branch.  This part is already
available without the `p ≥ 5` unit-square-sum argument; specializing the generic
high-modulus paired-product expansion gives the predicted valuation
`v_3(U^2 - 1) ≥ 3*r+2`. -/
lemma ratioProd_sq_sub_one_high_p3
    (r m : ℕ) (hr : 3 ≤ r) :
    let q := 3^r
    let M := 3 ^ (3 * r + 3)
    ratioProd M q m ^ 2 - 1 =
      ((m * (m + 1) : ℕ) : ZMod M) * (q : ZMod M)^2 * Tpair M q := by
  simpa using ratioProd_sq_sub_one_high_pge5 (p := 3) (r := r) (m := m) (by norm_num : Nat.Prime 3) hr

/-- Conditional p=3 final ZMod assembly.  It isolates the remaining arithmetic
blockers exactly as the reported numerics suggest:
* coefficient `6*A^2-27*B` is zero modulo `3^5`;
* `Tpair` is zero after casting modulo `3^(r-1)`;
* the `m=1` ratio has the linear form `V-1=q^2*T`.
The `m=2` square-ratio linear form is proved above, and the binomial step
products are supplied by the existing product-ratio machinery. -/
lemma key_zmod_congruence_p3_rge3_of_T_and_linear_V
    (r : ℕ) (hr : 3 ≤ r)
    (hCcast :
      let M := 3 ^ (3 * r + 3)
      let A0 : ZMod M := ((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod M)
      let B0 : ZMod M := ((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod M)
      (ZMod.castHom (show 3^5 ∣ M by
        dsimp; exact pow_dvd_pow 3 (by omega : 5 ≤ 3 * r + 3)) (ZMod (3^5)))
        ((6 : ZMod M) * A0^2 - (27 : ZMod M) * B0) = 0)
    (hTcast :
      let M := 3 ^ (3 * r + 3)
      let T : ZMod M := Tpair M (3^r)
      (ZMod.castHom (show 3^(r-1) ∣ M by
        change 3^(r-1) ∣ 3 ^ (3 * r + 3)
        exact pow_dvd_pow 3 (by omega : r - 1 ≤ 3 * r + 3)) (ZMod (3^(r-1)))) T = 0)
    (hVlinear :
      let q := 3^r
      let M := 3 ^ (3 * r + 3)
      let V : ZMod M := ratioProd M q 1
      let T : ZMod M := Tpair M q
      V - 1 = (q : ZMod M)^2 * T) :
    let q := 3^r
    let n := 3^(r-1)
    let M := 3 ^ (3 * r + 3)
    let A := Nat.choose (3*n) n
    let B := Nat.choose (2*n) n
    let Aq := Nat.choose (3*q) q
    let Bq := Nat.choose (2*q) q
    ((Aq : ZMod M)^2 - (A : ZMod M)^2) = (27 : ZMod M) * ((Bq : ZMod M) - (B : ZMod M)) := by
  classical
  intro q n M A B Aq Bq
  subst q; subst n; subst M; subst A; subst B; subst Aq; subst Bq
  have hp3 : Nat.Prime 3 := by norm_num
  let U : ZMod (3 ^ (3 * r + 3)) := ratioProd (3 ^ (3 * r + 3)) (3^r) 2
  let V : ZMod (3 ^ (3 * r + 3)) := ratioProd (3 ^ (3 * r + 3)) (3^r) 1
  let T : ZMod (3 ^ (3 * r + 3)) := Tpair (3 ^ (3 * r + 3)) (3^r)
  let qz : ZMod (3 ^ (3 * r + 3)) := (3^r : ℕ)
  let A0 : ZMod (3 ^ (3 * r + 3)) := ((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3 ^ (3 * r + 3)))
  let B0 : ZMod (3 ^ (3 * r + 3)) := ((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3 ^ (3 * r + 3)))
  have hAq : ((Nat.choose (3 * 3^r) (3^r) : ℕ) : ZMod (3 ^ (3 * r + 3))) = A0 * U := by
    have h := prime_pow_step_product_as_ratioProd (p := 3) (r := r) (m := 2) hp3 (by omega : 1 ≤ r)
    dsimp only at h
    simpa [A0, U, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.succ_eq_add_one] using h
  have hBq : ((Nat.choose (2 * 3^r) (3^r) : ℕ) : ZMod (3 ^ (3 * r + 3))) = B0 * V := by
    have h := prime_pow_step_product_as_ratioProd (p := 3) (r := r) (m := 1) hp3 (by omega : 1 ≤ r)
    dsimp only at h
    simpa [B0, V, one_add_one_eq_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hU : U^2 - 1 = (6 : ZMod (3 ^ (3 * r + 3))) * qz^2 * T := by
    have h := ratioProd_sq_sub_one_high_p3 (r := r) (m := 2) hr
    dsimp only at h
    simpa [U, T, qz, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hV : V - 1 = qz^2 * T := by
    dsimp only at hVlinear
    simpa [V, T, qz] using hVlinear
  have hCcast' : (ZMod.castHom (show 3^5 ∣ 3 ^ (3 * r + 3) by exact pow_dvd_pow 3 (by omega : 5 ≤ 3 * r + 3)) (ZMod (3^5)))
      ((6 : ZMod (3 ^ (3 * r + 3))) * A0^2 - (27 : ZMod (3 ^ (3 * r + 3))) * B0) = 0 := by
    dsimp only at hCcast
    simpa [A0, B0] using hCcast
  have hTcast' : (ZMod.castHom (show 3^(r-1) ∣ 3 ^ (3 * r + 3) by exact pow_dvd_pow 3 (by omega : r - 1 ≤ 3 * r + 3)) (ZMod (3^(r-1)))) T = 0 := by
    dsimp only at hTcast
    simpa [T] using hTcast
  have hkill : ((6 : ZMod (3 ^ (3 * r + 3))) * A0^2 - (27 : ZMod (3 ^ (3 * r + 3))) * B0) * qz^2 * T = 0 := by
    simpa [qz] using coeff_qsq_T_eq_zero_of_casts_p3 (r := r) hr
      (((6 : ZMod (3 ^ (3 * r + 3))) * A0^2 - (27 : ZMod (3 ^ (3 * r + 3))) * B0)) T hCcast' hTcast'
  rw [hAq, hBq]
  have hgoal : A0^2 * ((6 : ZMod (3 ^ (3 * r + 3))) * qz^2 * T) = (27 : ZMod (3 ^ (3 * r + 3))) * (B0 * (qz^2 * T)) := by
    have hk := hkill
    ring_nf at hk ⊢
    exact sub_eq_zero.mp hk
  calc
    (A0 * U)^2 - A0^2 = A0^2 * (U^2 - 1) := by ring
    _ = A0^2 * ((6 : ZMod (3 ^ (3 * r + 3))) * qz^2 * T) := by rw [hU]
    _ = (27 : ZMod (3 ^ (3 * r + 3))) * (B0 * (qz^2 * T)) := hgoal
    _ = (27 : ZMod (3 ^ (3 * r + 3))) * (B0 * V - B0) := by rw [show B0 * V - B0 = B0 * (V - 1) by ring, hV]

/-- Once the three p=3 arithmetic blockers above are supplied, the original OEIS
step follows for all `r ≥ 3`. -/
lemma oeis_357569_p3_rge3_of_T_and_linear_V
    (r : ℕ) (hr : 3 ≤ r)
    (hCcast :
      let M := 3 ^ (3 * r + 3)
      let A0 : ZMod M := ((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod M)
      let B0 : ZMod M := ((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod M)
      (ZMod.castHom (show 3^5 ∣ M by
        dsimp; exact pow_dvd_pow 3 (by omega : 5 ≤ 3 * r + 3)) (ZMod (3^5)))
        ((6 : ZMod M) * A0^2 - (27 : ZMod M) * B0) = 0)
    (hTcast :
      let M := 3 ^ (3 * r + 3)
      let T : ZMod M := Tpair M (3^r)
      (ZMod.castHom (show 3^(r-1) ∣ M by
        change 3^(r-1) ∣ 3 ^ (3 * r + 3)
        exact pow_dvd_pow 3 (by omega : r - 1 ≤ 3 * r + 3)) (ZMod (3^(r-1)))) T = 0)
    (hVlinear :
      let q := 3^r
      let M := 3 ^ (3 * r + 3)
      let V : ZMod M := ratioProd M q 1
      let T : ZMod M := Tpair M q
      V - 1 = (q : ZMod M)^2 * T) :
    a (3 ^ r) ≡ a (3 ^ (r - 1)) [ZMOD ((3 : ℤ) ^ (3 * r + 3))] := by
  apply oeis_357569_step_of_key
  exact int_key_congruence_of_zmod_key 3 r
    (key_zmod_congruence_p3_rge3_of_T_and_linear_V r hr hCcast hTcast hVlinear)


/-- A small coefficient-side reduction for the p=3 branch.  Numerically the two
binomial coefficients at every positive 3-power level are congruent to the base
values `choose 9 3 = 84` and `choose 6 3 = 20` modulo `3^5`.  Once those two
residue facts are available, the troublesome coefficient is automatically zero
modulo `3^5`. -/
lemma main_coeff_mod_3pow5_p3_of_residues
    (r : ℕ)
    (hA : (((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5))) = 84)
    (hB : (((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5))) = 20) :
    ((6 : ZMod (3^5)) *
        (((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5)))^2 -
      (27 : ZMod (3^5)) *
        (((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5)))) = 0 := by
  rw [hA, hB]
  decide

/-- The same coefficient reduction in the exact cast shape required by
`key_zmod_congruence_p3_rge3_of_T_and_linear_V`.  Thus the coefficient blocker
can be attacked independently by proving the two stable residue congruences
`A ≡ 84` and `B ≡ 20` modulo `3^5`. -/
lemma coeff_cast_3pow5_p3_of_residues
    (r : ℕ) (hr : 3 ≤ r)
    (hA : (((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5))) = 84)
    (hB : (((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5))) = 20) :
    let M := 3 ^ (3 * r + 3)
    let A0 : ZMod M := ((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod M)
    let B0 : ZMod M := ((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod M)
    (ZMod.castHom (show 3^5 ∣ M by
      dsimp
      exact pow_dvd_pow 3 (by omega : 5 ≤ 3 * r + 3)) (ZMod (3^5)))
      ((6 : ZMod M) * A0^2 - (27 : ZMod M) * B0) = 0 := by
  intro M A0 B0
  subst M
  subst A0
  subst B0
  let hdiv : 3^5 ∣ 3 ^ (3 * r + 3) := pow_dvd_pow 3 (by omega : 5 ≤ 3 * r + 3)
  change (ZMod.castHom hdiv (ZMod (3^5)))
      ((6 : ZMod (3 ^ (3 * r + 3))) *
        (((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3 ^ (3 * r + 3))))^2 -
      (27 : ZMod (3 ^ (3 * r + 3))) *
        (((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3 ^ (3 * r + 3))))) = 0
  rw [map_sub, map_mul, map_pow, map_mul]
  rw [show (ZMod.castHom hdiv (ZMod (3^5))) (6 : ZMod (3 ^ (3 * r + 3))) = (6 : ZMod (3^5)) from ZMod.cast_natCast hdiv 6]
  rw [show (ZMod.castHom hdiv (ZMod (3^5))) (27 : ZMod (3 ^ (3 * r + 3))) = (27 : ZMod (3^5)) from ZMod.cast_natCast hdiv 27]
  rw [show (ZMod.castHom hdiv (ZMod (3^5))) (((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3 ^ (3 * r + 3)))) = (((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5))) from ZMod.cast_natCast hdiv _]
  rw [show (ZMod.castHom hdiv (ZMod (3^5))) (((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3 ^ (3 * r + 3)))) = (((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5))) from ZMod.cast_natCast hdiv _]
  exact main_coeff_mod_3pow5_p3_of_residues r hA hB

/-- Concrete base residues for the coefficient pattern: `choose 9 3 = 84` and
`choose 6 3 = 20` give the p=3 coefficient cancellation modulo `3^5` at the
first positive 3-power level.  This is the base case needed for an eventual
induction proving the stable residue congruences. -/
lemma main_coeff_mod_3pow5_p3_base :
    ((6 : ZMod (3^5)) *
        (((Nat.choose (3 * 3^1) (3^1) : ℕ) : ZMod (3^5)))^2 -
      (27 : ZMod (3^5)) *
        (((Nat.choose (2 * 3^1) (3^1) : ℕ) : ZMod (3^5)))) = 0 := by
  norm_num
  decide

open Nat
open scoped BigOperators

/--
A focused r=2 handoff lemma.  For `p ≥ 5`, the final ZMod assembly for
`r = 2` is exactly the same as the proved `r ≥ 3` assembly once the two
ratio-products have the same linear forms modulo `p^9`:

* `ratioProd p^9 p^2 2` satisfies `U^2 - 1 = 6 * (p^2)^2 * Tpair`;
* `ratioProd p^9 p^2 1` satisfies `V - 1 = (p^2)^2 * Tpair`.

The existing coefficient congruence modulo `p^3` and the existing `Tpair`
vanishing modulo `p^2` then kill the common `p^4*Tpair` term.
-/
lemma key_zmod_congruence_pge5_r2_of_ratio_linear
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hUlin :
      let q := p^2
      let M := p^9
      let U : ZMod M := ratioProd M q 2
      let T : ZMod M := Tpair M q
      U^2 - 1 = (6 : ZMod M) * (q : ZMod M)^2 * T)
    (hVlin :
      let q := p^2
      let M := p^9
      let V : ZMod M := ratioProd M q 1
      let T : ZMod M := Tpair M q
      V - 1 = (q : ZMod M)^2 * T) :
    let q := p^2
    let n := p^(2-1)
    let M := p ^ (3 * 2 + 3)
    let A := Nat.choose (3*n) n
    let B := Nat.choose (2*n) n
    let Aq := Nat.choose (3*q) q
    let Bq := Nat.choose (2*q) q
    ((Aq : ZMod M)^2 - (A : ZMod M)^2) =
      (27 : ZMod M) * ((Bq : ZMod M) - (B : ZMod M)) := by
  classical
  intro q n M A B Aq Bq
  subst q; subst n; subst M; subst A; subst B; subst Aq; subst Bq
  norm_num only [mul_one, tsub_self, pow_one]
  have hp : p.Prime := Fact.out
  let U : ZMod (p ^ 9) := ratioProd (p ^ 9) (p^2) 2
  let V : ZMod (p ^ 9) := ratioProd (p ^ 9) (p^2) 1
  let T : ZMod (p ^ 9) := Tpair (p ^ 9) (p^2)
  let qz : ZMod (p ^ 9) := (p^2 : ℕ)
  let A0 : ZMod (p ^ 9) := ((Nat.choose (3 * p) p : ℕ) : ZMod (p ^ 9))
  let B0 : ZMod (p ^ 9) := ((Nat.choose (2 * p) p : ℕ) : ZMod (p ^ 9))
  have hAq : ((Nat.choose (3 * p^2) (p^2) : ℕ) : ZMod (p ^ 9)) = A0 * U := by
    have h := prime_pow_step_product_as_ratioProd (p := p) (r := 2) (m := 2) hp (by norm_num : 1 ≤ 2)
    dsimp only at h
    simpa [A0, U, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.succ_eq_add_one] using h
  have hBq : ((Nat.choose (2 * p^2) (p^2) : ℕ) : ZMod (p ^ 9)) = B0 * V := by
    have h := prime_pow_step_product_as_ratioProd (p := p) (r := 2) (m := 1) hp (by norm_num : 1 ≤ 2)
    dsimp only at h
    simpa [B0, V, one_add_one_eq_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hU : U^2 - 1 = (6 : ZMod (p ^ 9)) * qz^2 * T := by
    dsimp only at hUlin
    simpa [U, T, qz] using hUlin
  have hV : V - 1 = qz^2 * T := by
    dsimp only at hVlin
    simpa [V, T, qz] using hVlin
  have hCcast :
      (ZMod.castHom (show p^3 ∣ p ^ 9 by exact pow_dvd_pow p (by norm_num : 3 ≤ 9)) (ZMod (p^3)))
      ((6 : ZMod (p ^ 9)) * A0^2 - (27 : ZMod (p ^ 9)) * B0) = 0 := by
    let hdiv3 : p^3 ∣ p ^ 9 := pow_dvd_pow p (by norm_num : 3 ≤ 9)
    change (ZMod.castHom hdiv3 (ZMod (p^3)))
      ((6 : ZMod (p ^ 9)) * A0^2 - (27 : ZMod (p ^ 9)) * B0) = 0
    rw [map_sub, map_mul, map_pow, map_mul]
    rw [show (ZMod.castHom hdiv3 (ZMod (p^3))) (6 : ZMod (p ^ 9)) = (6 : ZMod (p^3)) from ZMod.cast_natCast hdiv3 6]
    rw [show (ZMod.castHom hdiv3 (ZMod (p^3))) (27 : ZMod (p ^ 9)) = (27 : ZMod (p^3)) from ZMod.cast_natCast hdiv3 27]
    rw [show (ZMod.castHom hdiv3 (ZMod (p^3))) A0 = (((Nat.choose (3 * p) p : ℕ) : ZMod (p^3))) by dsimp [A0]; exact ZMod.cast_natCast hdiv3 _]
    rw [show (ZMod.castHom hdiv3 (ZMod (p^3))) B0 = (((Nat.choose (2 * p) p : ℕ) : ZMod (p^3))) by dsimp [B0]; exact ZMod.cast_natCast hdiv3 _]
    simpa using main_coeff_mod_p3_pge5 p 2 hp5
  have hTcast :
      (ZMod.castHom (show p^2 ∣ p ^ 9 by exact pow_dvd_pow p (by norm_num : 2 ≤ 9)) (ZMod (p^2))) T = 0 := by
    have h := Tpair_cast_zero_pge5 (p := p) (r := 2) hp5 (by norm_num : 1 ≤ 2)
    dsimp only at h
    simpa [T] using h
  have hkill : ((6 : ZMod (p ^ 9)) * A0^2 - (27 : ZMod (p ^ 9)) * B0) * qz^2 * T = 0 := by
    simpa [qz] using coeff_qsq_T_eq_zero_of_casts_high (p := p) (r := 2) hp.ne_zero (by norm_num : 1 ≤ 2)
      (((6 : ZMod (p ^ 9)) * A0^2 - (27 : ZMod (p ^ 9)) * B0)) T hCcast hTcast
  rw [hAq, hBq]
  have hgoal : A0^2 * ((6 : ZMod (p ^ 9)) * qz^2 * T) = (27 : ZMod (p ^ 9)) * (B0 * (qz^2 * T)) := by
    have hk := hkill
    ring_nf at hk ⊢
    exact sub_eq_zero.mp hk
  calc
    (A0 * U)^2 - A0^2 = A0^2 * (U^2 - 1) := by ring
    _ = A0^2 * ((6 : ZMod (p ^ 9)) * qz^2 * T) := by rw [hU]
    _ = (27 : ZMod (p ^ 9)) * (B0 * (qz^2 * T)) := hgoal
    _ = (27 : ZMod (p ^ 9)) * (B0 * V - B0) := by rw [show B0 * V - B0 = B0 * (V - 1) by ring, hV]

/-- Integer OEIS step for `p ≥ 5, r = 2`, conditional only on the two ratio
linearizations isolated in `key_zmod_congruence_pge5_r2_of_ratio_linear`. -/
lemma oeis_357569_conjecture_0_pge5_r2_of_ratio_linear
    (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5)
    (hUlin :
      let q := p^2
      let M := p^9
      let U : ZMod M := ratioProd M q 2
      let T : ZMod M := Tpair M q
      U^2 - 1 = (6 : ZMod M) * (q : ZMod M)^2 * T)
    (hVlin :
      let q := p^2
      let M := p^9
      let V : ZMod M := ratioProd M q 1
      let T : ZMod M := Tpair M q
      V - 1 = (q : ZMod M)^2 * T) :
    a (p ^ 2) ≡ a (p ^ (2 - 1)) [ZMOD ((p : ℤ) ^ (3 * 2 + 3))] := by
  letI : Fact p.Prime := ⟨hp⟩
  apply oeis_357569_step_of_key
  exact int_key_congruence_of_zmod_key p 2
    (key_zmod_congruence_pge5_r2_of_ratio_linear p hp5 hUlin hVlin)

open Nat
open scoped BigOperators

def unitRepsLocal (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun i => Nat.Coprime i q)

lemma coprime_prime_pow_iff_not_dvd_local {p i k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    Nat.Coprime i (p ^ k) ↔ ¬ p ∣ i := by
  constructor
  · intro h hdiv
    have hpdvd : p ∣ p^k := dvd_pow_self p (Nat.ne_of_gt hk)
    have hpdvdg : p ∣ Nat.gcd i (p^k) := Nat.dvd_gcd hdiv hpdvd
    rw [h.gcd_eq_one] at hpdvdg
    exact hp.not_dvd_one hpdvdg
  · intro hnot
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot


lemma prime_dvd_add_mul_self_iff {p a k : ℕ} :
    p ∣ a + k * p ↔ p ∣ a := by
  have hterm : p ∣ k * p := dvd_mul_left p k
  rw [Nat.add_comm]
  exact (Nat.dvd_add_iff_right hterm).symm

lemma coprime_add_mul_prime_iff {p a k : ℕ} (hp : Nat.Prime p) :
    Nat.Coprime (a + k * p) (p^2) ↔ Nat.Coprime a p := by
  rw [coprime_prime_pow_iff_not_dvd_local hp (by norm_num : 0 < 2)]
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  exact not_congr prime_dvd_add_mul_self_iff

lemma coprime_mod_prime_iff {p i : ℕ} (hp : Nat.Prime p) :
    Nat.Coprime (i % p) p ↔ Nat.Coprime i (p^2) := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  rw [coprime_prime_pow_iff_not_dvd_local hp (by norm_num : 0 < 2)]
  constructor
  · intro h hdiv
    exact h ((Nat.dvd_mod_iff (dvd_refl p)).2 hdiv)
  · intro h hmod
    apply h
    rw [← Nat.mod_add_div i p]
    exact dvd_add hmod (dvd_mul_right p (i / p))

lemma sum_units_prime_square_lift (p : ℕ) (hp : Nat.Prime p)
    (F : ℕ → R) [CommSemiring R] :
    (∑ i ∈ unitRepsLocal (p^2), F (i % p)) =
      (p : R) * ∑ a ∈ unitRepsLocal p, F a := by
  classical
  let q : ℕ := p
  let s : Finset ℕ := unitRepsLocal (p^2)
  let t : Finset (ℕ × ℕ) := (unitRepsLocal p).product (Finset.range p)
  have hp_pos : 0 < p := hp.pos
  have hbij : (∑ i ∈ s, F (i % p)) = (∑ x ∈ t, F x.1) := by
    refine Finset.sum_bij'
      (s := s) (t := t) (f := fun i => F (i % p)) (g := fun x : ℕ × ℕ => F x.1)
      (fun i _hi => (i % p, i / p))
      (fun x _hx => x.1 + x.2 * p)
      ?hi ?hj ?left_inv ?right_inv ?hfg
    · intro i hi
      change i ∈ unitRepsLocal (p^2) at hi
      rw [unitRepsLocal, Finset.mem_filter, Finset.mem_range] at hi
      apply Finset.mk_mem_product
      · rw [unitRepsLocal, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.mod_lt i hp_pos, (coprime_mod_prime_iff hp).mpr hi.2⟩
      · rw [Finset.mem_range]
        exact Nat.div_lt_of_lt_mul (by simpa [pow_two] using hi.1)
    · intro x hx
      rcases x with ⟨a,k⟩
      have hx' : (a,k) ∈ (unitRepsLocal p) ×ˢ Finset.range p := by simpa [t] using hx
      rw [Finset.mem_product] at hx'
      rcases hx' with ⟨ha,hk⟩
      rw [unitRepsLocal, Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_range] at hk
      change a + k * p ∈ unitRepsLocal (p^2)
      rw [unitRepsLocal, Finset.mem_filter, Finset.mem_range]
      constructor
      · rw [pow_two]
        nlinarith [ha.1, hk, hp_pos]
      · exact (coprime_add_mul_prime_iff hp).mpr ha.2
    · intro i hi
      simpa [Nat.mul_comm] using (Nat.mod_add_div i p)
    · intro x hx
      rcases x with ⟨a,k⟩
      have hx' : (a,k) ∈ (unitRepsLocal p) ×ˢ Finset.range p := by simpa [t] using hx
      rw [Finset.mem_product] at hx'
      rcases hx' with ⟨ha,hk⟩
      rw [unitRepsLocal, Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_range] at hk
      ext
      · change (a + k * p) % p = a
        exact Nat.add_mul_mod_self_right a k p |>.trans (Nat.mod_eq_of_lt ha.1)
      · change (a + k * p) / p = k
        rw [Nat.add_mul_div_right _ _ hp_pos, Nat.div_eq_of_lt ha.1, zero_add]
    · intro i hi
      rfl
  calc
    (∑ i ∈ unitRepsLocal (p^2), F (i % p)) = (∑ i ∈ s, F (i % p)) := by rfl
    _ = (∑ x ∈ t, F x.1) := hbij
    _ = (p : R) * ∑ a ∈ unitRepsLocal p, F a := by
      simp [t, Finset.sum_product, Finset.mul_sum]
open scoped BigOperators

lemma sum_powersetCard_one_insert_prod {R : Type*} [CommRing R] (s : Finset ℕ) (a : ℕ) (f : ℕ → R)
    (ha : a ∉ s) :
    (∑ t ∈ s.powersetCard 1, ∏ i ∈ insert a t, f i) = f a * ∑ i ∈ s, f i := by
  classical
  rw [Finset.powersetCard_one]
  rw [Finset.sum_map]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxa : x ≠ a := by intro h; subst h; exact ha hx
  rw [Finset.prod_insert]
  · simp
  · simpa [Finset.mem_singleton] using hxa.symm

lemma elemSym2_two_mul {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R) :
    (2 : R) * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) =
      (∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2 := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [Finset.powersetCard]
  · intro a s ha ih
    rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha]
    rw [Finset.powersetCard_succ_insert ha 1]
    rw [Finset.sum_union]
    · rw [mul_add, ih]
      rw [Finset.sum_image]
      · have hpc1 := sum_powersetCard_one_insert_prod (R := R) s a f ha
        rw [hpc1]
        ring
      · intro x hx y hy hxy
        have hax : a ∉ x := by
          intro hmem
          exact ha ((Finset.mem_powersetCard.mp hx).1 hmem)
        have hay : a ∉ y := by
          intro hmem
          exact ha ((Finset.mem_powersetCard.mp hy).1 hmem)
        ext z
        constructor
        · intro hz
          have hzins : z ∈ insert a y := by
            rw [← hxy]
            exact Finset.mem_insert_of_mem hz
          rw [Finset.mem_insert] at hzins
          rcases hzins with hz_eq | hz_y
          · subst hz_eq
            exact False.elim (hax hz)
          · exact hz_y
        · intro hz
          have hzins : z ∈ insert a x := by
            rw [hxy]
            exact Finset.mem_insert_of_mem hz
          rw [Finset.mem_insert] at hzins
          rcases hzins with hz_eq | hz_x
          · subst hz_eq
            exact False.elim (hay hz)
          · exact hz_x
    · rw [Finset.disjoint_left]
      intro u hu him
      rw [Finset.mem_image] at him
      rcases him with ⟨t, ht, rfl⟩
      have hsub : insert a t ⊆ s := (Finset.mem_powersetCard.mp hu).1
      have : a ∈ s := hsub (Finset.mem_insert_self a t)
      exact ha this

lemma elemSym2_eq_zero_of_sum_and_sq_sum_zero
    {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R)
    (h2 : IsUnit (2 : R))
    (hS : (∑ i ∈ s, f i) = 0)
    (hSq : (∑ i ∈ s, (f i)^2) = 0) :
    (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) = 0 := by
  classical
  let E : R := ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i
  have htwoE : (2 : R) * E = 0 := by
    dsimp [E]
    rw [elemSym2_two_mul, hS, hSq]
    ring
  let u : Rˣ := h2.unit
  have hu : (u : R) = 2 := h2.unit_spec
  have : E = 0 := by
    calc E = ((u⁻¹ : Rˣ) : R) * ((u : R) * E) := by simp
      _ = ((u⁻¹ : Rˣ) : R) * ((2 : R) * E) := by rw [hu]
      _ = 0 := by rw [htwoE, mul_zero]
  simpa [E] using this


-- R2 quadratic cancellation full attempt
noncomputable def pairedT2 (p : ℕ) (i : ℕ) : ZMod (p^9) :=
  ((((i : ℕ) : ZMod (p^9)) * ((p^2 - i : ℕ) : ZMod (p^9)))⁻¹)

noncomputable def pairedT2_e2 (p : ℕ) : ZMod (p^9) :=
  ∑ s ∈ (unitReps (p^2)).powersetCard 2, ∏ i ∈ s, pairedT2 p i

lemma pairedT2_cast_to_p
    (p i : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hi : i ∈ unitReps (p^2)) :
    (ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2 p i)
      = - ((i : ZMod p)⁻¹)^2 := by
  classical
  have hp : p.Prime := Fact.out
  have hi' : i < p^2 ∧ Nat.Coprime i (p^2) := by
    simpa [unitReps] using hi
  have hdiv92 : p^2 ∣ p^9 := pow_dvd_pow p (by norm_num : 2 ≤ 9)
  have hdiv21 : p ∣ p^2 := dvd_pow_self p (by norm_num : 2 ≠ 0)
  have hterm2 :
      ((ZMod.castHom hdiv92 (ZMod (p^2))) (pairedT2 p i) : ZMod (p^2)) =
        - ((i : ZMod (p^2))⁻¹)^2 := by
    simpa [pairedT2] using
      (cast_inv_mul_q_sub_eq_neg_inv_sq_any (p := p) (r := 2) (i := i) hp (by norm_num : 1 ≤ 2)
        hi'.1 hi'.2)
  have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by norm_num : 0 < 2)).mp hi'.2
  have hcop_p : Nat.Coprime i p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot
  have hinvcast :
      ((ZMod.castHom hdiv21 (ZMod p)) (((i : ZMod (p^2))⁻¹)) : ZMod p) = ((i : ZMod p)⁻¹) := by
    exact zmod_cast_inv_of_coprime_any (M := p^2) (q := p) (i := i) hdiv21 hi'.2 hcop_p
  have hcasted := congrArg (fun x : ZMod (p^2) => (ZMod.castHom hdiv21 (ZMod p)) x) hterm2
  change (ZMod.castHom hdiv21 (ZMod p)) ((ZMod.castHom hdiv92 (ZMod (p^2))) (pairedT2 p i)) =
      (ZMod.castHom hdiv21 (ZMod p)) (- ((i : ZMod (p^2))⁻¹)^2) at hcasted
  rw [map_neg, map_pow, hinvcast] at hcasted
  have hcomp : (ZMod.castHom hdiv21 (ZMod p)).comp (ZMod.castHom hdiv92 (ZMod (p^2))) =
      ZMod.castHom (dvd_trans hdiv21 hdiv92) (ZMod p) := ZMod.castHom_comp hdiv21 hdiv92
  change ((ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2 p i) : ZMod p) = -((i : ZMod p)⁻¹)^2
  rw [← hcasted]
  change (ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2 p i) =
      ((ZMod.castHom hdiv21 (ZMod p)).comp (ZMod.castHom hdiv92 (ZMod (p^2)))) (pairedT2 p i)
  rw [hcomp]

lemma pairedT2_cast_sum_zero_pge5_r2
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ i ∈ unitReps (p^2),
      (ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2 p i)) = 0 := by
  classical
  have hp : p.Prime := Fact.out
  let F : ℕ → ZMod p := fun a => - ((a : ZMod p)⁻¹)^2
  calc
    (∑ i ∈ unitReps (p^2), (ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2 p i))
        = ∑ i ∈ unitReps (p^2), F i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact pairedT2_cast_to_p p i hp5 hi
    _ = ∑ i ∈ unitReps (p^2), F (i % p) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          dsimp [F]
          have hcast : ((i % p : ℕ) : ZMod p) = (i : ZMod p) := by
            rw [ZMod.natCast_eq_natCast_iff]
            exact (Nat.mod_modEq i p)
          rw [hcast]
    _ = (p : ZMod p) * ∑ a ∈ unitReps p, F a := by
          simpa [unitRepsLocal, unitReps] using
            (sum_units_prime_square_lift (p := p) hp (F := F) (R := ZMod p))
    _ = 0 := by simp

lemma pairedT2_cast_sq_sum_zero_pge5_r2
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ i ∈ unitReps (p^2),
      ((ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2 p i))^2) = 0 := by
  classical
  have hp : p.Prime := Fact.out
  let F : ℕ → ZMod p := fun a => (- ((a : ZMod p)⁻¹)^2)^2
  calc
    (∑ i ∈ unitReps (p^2), ((ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2 p i))^2)
        = ∑ i ∈ unitReps (p^2), F i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          dsimp [F]
          change ((ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2 p i))^2 = ( - ((i : ZMod p)⁻¹)^2)^2
          rw [pairedT2_cast_to_p p i hp5 hi]
    _ = ∑ i ∈ unitReps (p^2), F (i % p) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          dsimp [F]
          have hcast : ((i % p : ℕ) : ZMod p) = (i : ZMod p) := by
            rw [ZMod.natCast_eq_natCast_iff]
            exact (Nat.mod_modEq i p)
          rw [hcast]
    _ = (p : ZMod p) * ∑ a ∈ unitReps p, F a := by
          simpa [unitRepsLocal, unitReps] using
            (sum_units_prime_square_lift (p := p) hp (F := F) (R := ZMod p))
    _ = 0 := by simp

lemma pairedT2_e2_cast_zero_pge5_r2
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2_e2 p) = 0 := by
  classical
  let hdiv : p ∣ p^9 := dvd_pow_self p (by norm_num : 9 ≠ 0)
  dsimp [pairedT2_e2]
  change (ZMod.castHom hdiv (ZMod p))
      (∑ s ∈ (unitReps (p^2)).powersetCard 2, ∏ i ∈ s, pairedT2 p i) = 0
  rw [map_sum]
  simp_rw [map_prod]
  exact elemSym2_eq_zero_of_sum_and_sq_sum_zero
    (s := unitReps (p^2))
    (f := fun i => (ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) (pairedT2 p i))
    (show IsUnit (2 : ZMod p) from by
      have hp : p.Prime := Fact.out
      exact (ZMod.isUnit_iff_coprime 2 p).mpr (by
        rw [Nat.coprime_comm]
        exact hp.coprime_iff_not_dvd.mpr (by
          intro h
          have hp_le_2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
          omega)))
    (pairedT2_cast_sum_zero_pge5_r2 p hp5)
    (pairedT2_cast_sq_sum_zero_pge5_r2 p hp5)


-- product quadratic lemmas
open scoped BigOperators

lemma sum_powersetCard_one_insert_prod2 {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) (f : α → R) (ha : a ∉ s) :
    (∑ t ∈ s.powersetCard 1, ∏ i ∈ insert a t, f i) = f a * ∑ i ∈ s, f i := by
  classical
  rw [Finset.powersetCard_one]
  rw [Finset.sum_map]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxa : x ≠ a := by intro h; subst h; exact ha hx
  rw [Finset.prod_insert]
  · simp
  · simpa [Finset.mem_singleton] using hxa.symm

lemma e2_insert {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) (f : α → R) (ha : a ∉ s) :
    (∑ t ∈ (insert a s).powersetCard 2, ∏ i ∈ t, f i) =
      (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) + f a * ∑ i ∈ s, f i := by
  classical
  rw [Finset.powersetCard_succ_insert ha 1]
  rw [Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [sum_powersetCard_one_insert_prod2 (s := s) (a := a) (f := f) ha]
    · intro x hx y hy hxy
      have hax : a ∉ x := by intro hmem; exact ha ((Finset.mem_powersetCard.mp hx).1 hmem)
      have hay : a ∉ y := by intro hmem; exact ha ((Finset.mem_powersetCard.mp hy).1 hmem)
      ext z; constructor
      · intro hz
        have hzins : z ∈ insert a y := by rw [← hxy]; exact Finset.mem_insert_of_mem hz
        rw [Finset.mem_insert] at hzins
        rcases hzins with hz_eq | hz_y
        · subst hz_eq; exact False.elim (hax hz)
        · exact hz_y
      · intro hz
        have hzins : z ∈ insert a x := by rw [hxy]; exact Finset.mem_insert_of_mem hz
        rw [Finset.mem_insert] at hzins
        rcases hzins with hz_eq | hz_x
        · subst hz_eq; exact False.elim (hay hz)
        · exact hz_x
  · rw [Finset.disjoint_left]
    intro u hu him
    rw [Finset.mem_image] at him
    rcases him with ⟨t, ht, rfl⟩
    have hsub : insert a t ⊆ s := (Finset.mem_powersetCard.mp hu).1
    have : a ∈ s := hsub (Finset.mem_insert_self a t)
    exact ha this

lemma prod_one_add_c_quad {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (c : R) (f : α → R) (hc3 : c^3 = 0) :
    (∏ i ∈ s, (1 + c * f i)) =
      1 + c * (∑ i ∈ s, f i) + c^2 * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [Finset.powersetCard]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, e2_insert (s := s) (a := a) (f := f) ha]
    rw [ih]
    let E : R := ∑ t ∈ Finset.powersetCard 2 s, ∏ i ∈ t, f i
    let S : R := ∑ i ∈ s, f i
    have hcf : c * f a * (c ^ 2 * E) = 0 := by
      calc
        c * f a * (c ^ 2 * E) = c^3 * (f a * E) := by ring
        _ = 0 := by rw [hc3]; ring
    change (1 + c * f a) * (1 + c * S + c ^ 2 * E) =
      1 + c * (f a + S) + c ^ 2 * (E + f a * S)
    calc
      (1 + c * f a) * (1 + c * S + c ^ 2 * E)
          = (1 + c * (f a + S) + c ^ 2 * (E + f a * S)) + c * f a * (c^2 * E) := by ring
      _ = 1 + c * (f a + S) + c ^ 2 * (E + f a * S) := by rw [hcf, add_zero]

lemma p8_mul_eq_zero_of_cast_p_eq_zero_local
    (p : ℕ) [NeZero (p^9)] (z : ZMod (p^9))
    (h : (ZMod.castHom (dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)) z = 0) :
    ((((p^2 : ℕ) : ZMod (p^9)) ^ 2) ^ 2) * z = 0 := by
  rw [← ZMod.natCast_zmod_val z]
  rw [← Nat.cast_pow]
  rw [← Nat.cast_pow]
  rw [← Nat.cast_mul]
  rw [ZMod.natCast_eq_zero_iff]
  have hdiv : p ∣ p^9 := dvd_pow_self p (by norm_num : 9 ≠ 0)
  have hv : p ∣ z.val := by
    rw [← ZMod.natCast_zmod_val z] at h
    rw [show (ZMod.castHom hdiv (ZMod p)) ((z.val : ℕ) : ZMod (p^9)) = ((z.val : ℕ) : ZMod p) from ZMod.cast_natCast hdiv z.val] at h
    exact (ZMod.natCast_eq_zero_iff z.val p).mp h
  obtain ⟨k, hk⟩ := hv
  rw [hk]
  suffices p ^ 9 ∣ ((p ^ 2) ^ 2) ^ 2 * (p * k) by
    simpa [Nat.cast_mul] using this
  have hpows : ((p ^ 2) ^ 2) ^ 2 * (p * k) = (p^8 * p) * k := by ring
  rw [hpows]
  exact dvd_mul_of_dvd_left (show p^9 ∣ p^8 * p by rw [← pow_succ]) k

lemma pairedProd_eq_one_add_linear_pge5_r2_A
    (p A : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    let q := p^2
    let M := p^9
    pairedProd M q A = 1 + (A : ZMod M) * (q : ZMod M)^2 * Tpair M q := by
  classical
  intro q M
  subst q; subst M
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^9) := ⟨pow_ne_zero 9 hp.ne_zero⟩
  let c : ZMod (p^9) := (((p^2 : ℕ) : ZMod (p^9))^2)
  let f : ℕ → ZMod (p^9) := fun i => (A : ZMod (p^9)) * pairedT2 p i
  have hc3 : c^3 = 0 := by
    dsimp [c]
    rw [← pow_mul]
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    convert pow_dvd_pow p (by norm_num : 9 ≤ 12) using 1
    ring
  have hprod := prod_one_add_c_quad (s := unitReps (p^2)) (c := c) (f := f) hc3
  dsimp [pairedProd, Tpair]
  change (∏ i ∈ unitReps (p ^ 2), (1 + (A : ZMod (p^9)) * ((((p^2 : ℕ) : ZMod (p^9))) ^ 2) * pairedT2 p i)) =
      1 + (A : ZMod (p^9)) * ((((p^2 : ℕ) : ZMod (p^9)))^2) *
        (∑ i ∈ unitReps (p^2), pairedT2 p i)
  have hprod' : (∏ i ∈ unitReps (p ^ 2), (1 + (A : ZMod (p^9)) * ((((p^2 : ℕ) : ZMod (p^9))) ^ 2) * pairedT2 p i)) =
      1 + c * (∑ i ∈ unitReps (p^2), f i) + c^2 * (∑ t ∈ (unitReps (p^2)).powersetCard 2, ∏ i ∈ t, f i) := by
    calc
      (∏ i ∈ unitReps (p ^ 2), (1 + (A : ZMod (p^9)) * ((((p^2 : ℕ) : ZMod (p^9))) ^ 2) * pairedT2 p i))
          = ∏ i ∈ unitReps (p^2), (1 + c * f i) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            dsimp [c, f]
            ring
      _ = 1 + c * (∑ i ∈ unitReps (p^2), f i) + c^2 * (∑ t ∈ (unitReps (p^2)).powersetCard 2, ∏ i ∈ t, f i) := hprod
  rw [hprod']
  have hlin : c * (∑ i ∈ unitReps (p^2), f i) = (A : ZMod (p^9)) * ((((p^2 : ℕ) : ZMod (p^9)))^2) * (∑ i ∈ unitReps (p^2), pairedT2 p i) := by
    dsimp [c, f]
    have hsum : (∑ i ∈ unitReps (p ^ 2), (A : ZMod (p ^ 9)) * pairedT2 p i) =
        (A : ZMod (p ^ 9)) * ∑ i ∈ unitReps (p ^ 2), pairedT2 p i := by
      rw [Finset.mul_sum]
    rw [hsum]
    ring
  rw [hlin]
  have he2f : (∑ t ∈ (unitReps (p^2)).powersetCard 2, ∏ i ∈ t, f i) = (A : ZMod (p^9))^2 * pairedT2_e2 p := by
    dsimp [pairedT2_e2, f]
    calc
      (∑ t ∈ (unitReps (p^2)).powersetCard 2, ∏ i ∈ t, (A : ZMod (p^9)) * pairedT2 p i)
          = ∑ t ∈ (unitReps (p^2)).powersetCard 2, (A : ZMod (p^9))^2 * ∏ i ∈ t, pairedT2 p i := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rw [Finset.prod_mul_distrib]
            have hcard : t.card = 2 := (Finset.mem_powersetCard.mp ht).2
            simp [Finset.prod_const, hcard]
      _ = (A : ZMod (p^9))^2 * ∑ s ∈ (unitReps (p^2)).powersetCard 2, ∏ i ∈ s, pairedT2 p i := by
            rw [Finset.mul_sum]
  rw [he2f]
  have hquad : c^2 * ((A : ZMod (p^9))^2 * pairedT2_e2 p) = 0 := by
    have hkill := p8_mul_eq_zero_of_cast_p_eq_zero_local p ((A : ZMod (p^9))^2 * pairedT2_e2 p) ?_
    · simpa [c, mul_assoc] using hkill
    · rw [map_mul]
      rw [pairedT2_e2_cast_zero_pge5_r2 p hp5]
      simp
  rw [hquad, add_zero]

lemma pairedProd_eq_one_add_linear_pge5_r2_m2_full
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    let q := p^2
    let M := p^9
    pairedProd M q 6 = 1 + (6 : ZMod M) * (q : ZMod M)^2 * Tpair M q := by
  exact pairedProd_eq_one_add_linear_pge5_r2_A p 6 hp5

lemma pairedProd_eq_one_add_linear_pge5_r2_m1_full
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    let q := p^2
    let M := p^9
    pairedProd M q 2 = 1 + (2 : ZMod M) * (q : ZMod M)^2 * Tpair M q := by
  exact pairedProd_eq_one_add_linear_pge5_r2_A p 2 hp5

lemma zmod_sq_eq_zero_of_cast_p5_eq_zero_p9 (p : ℕ) (hp0 : p ≠ 0)
    (z : ZMod (p^9))
    (h : (ZMod.castHom (pow_dvd_pow p (by norm_num : 5 ≤ 9)) (ZMod (p^5))) z = 0) :
    z^2 = 0 := by
  haveI : NeZero (p^9) := ⟨pow_ne_zero 9 hp0⟩
  rw [← ZMod.natCast_zmod_val z]
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hdiv : p^5 ∣ p^9 := pow_dvd_pow p (by norm_num : 5 ≤ 9)
  have hv : p^5 ∣ z.val := by
    rw [← ZMod.natCast_zmod_val z] at h
    rw [show (ZMod.castHom hdiv (ZMod (p^5))) ((z.val : ℕ) : ZMod (p^9)) = ((z.val : ℕ) : ZMod (p^5)) from ZMod.cast_natCast hdiv z.val] at h
    exact (ZMod.natCast_eq_zero_iff z.val (p^5)).mp h
  obtain ⟨k,hk⟩ := hv
  rw [hk]
  suffices p^9 ∣ p^10 * k^2 by
    convert this using 1
    ring
  exact dvd_mul_of_dvd_left (pow_dvd_pow p (by norm_num : 9 ≤ 10)) (k^2)

lemma p4_mul_T_zero_mod_p5_of_T_cast_p2_zero
    (p : ℕ) [NeZero (p^5)] [NeZero (p^9)] (T : ZMod (p^9))
    (hT : (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 9)) (ZMod (p^2))) T = 0) :
    (ZMod.castHom (pow_dvd_pow p (by norm_num : 5 ≤ 9)) (ZMod (p^5)))
      (((p^2 : ℕ) : ZMod (p^9))^2 * T) = 0 := by
  have hdiv2 : p^2 ∣ p^9 := pow_dvd_pow p (by norm_num : 2 ≤ 9)
  have hdiv5 : p^5 ∣ p^9 := pow_dvd_pow p (by norm_num : 5 ≤ 9)
  rw [← ZMod.natCast_zmod_val T]
  rw [map_mul]
  rw [show (ZMod.castHom hdiv5 (ZMod (p^5))) ((((p^2 : ℕ) : ZMod (p^9))^2)) = (((p^2 : ℕ) : ZMod (p^5))^2) by rw [map_pow]; exact congrArg (fun x => x^2) (ZMod.cast_natCast hdiv5 (p^2))]
  rw [show (ZMod.castHom hdiv5 (ZMod (p^5))) ((T.val : ℕ) : ZMod (p^9)) = ((T.val : ℕ) : ZMod (p^5)) from ZMod.cast_natCast hdiv5 T.val]

  rw [← Nat.cast_pow]
  rw [← Nat.cast_mul]
  rw [ZMod.natCast_eq_zero_iff]
  have hv : p^2 ∣ T.val := by
    rw [← ZMod.natCast_zmod_val T] at hT
    rw [show (ZMod.castHom hdiv2 (ZMod (p^2))) ((T.val : ℕ) : ZMod (p^9)) = ((T.val : ℕ) : ZMod (p^2)) from ZMod.cast_natCast hdiv2 T.val] at hT
    exact (ZMod.natCast_eq_zero_iff T.val (p^2)).mp hT
  obtain ⟨k,hk⟩ := hv
  rw [hk]
  suffices p^5 ∣ (p^2)^2 * (p^2 * k) by
    simpa [Nat.cast_mul] using this
  have : (p^2)^2 * (p^2 * k) = p^6 * k := by ring
  rw [this]
  exact dvd_mul_of_dvd_left (pow_dvd_pow p (by norm_num : 5 ≤ 6)) k

lemma ratioProd_sq_sub_one_pge5_r2_full
    (p m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    let q := p^2
    let M := p^9
    ratioProd M q m ^ 2 - 1 = ((m * (m + 1) : ℕ) : ZMod M) * (q : ZMod M)^2 * Tpair M q := by
  intro q M
  subst q; subst M
  have hp : p.Prime := Fact.out
  have hsq := ratioProd_sq_eq_pairedProd (p := p) (r := 2) (m := m) hp (by norm_num : 1 ≤ 2)
  dsimp only at hsq
  rw [hsq]
  have hlin := pairedProd_eq_one_add_linear_pge5_r2_A p (m*(m+1)) hp5
  dsimp only at hlin
  rw [hlin]
  ring

lemma ratioProd_sub_one_sq_zero_pge5_r2_full
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    let q := p^2
    (ratioProd (p^9) q 1 - 1)^2 = 0 := by
  intro q
  subst q
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  let V : ZMod (p^9) := ratioProd (p^9) (p^2) 1
  apply zmod_sq_eq_zero_of_cast_p5_eq_zero_p9 p hp0 (V - 1)
  let V5 : ZMod (p^5) := (ZMod.castHom (pow_dvd_pow p (by norm_num : 5 ≤ 9)) (ZMod (p^5))) V
  have hVsq_high : V^2 - 1 = (2 : ZMod (p^9)) * ((p^2 : ℕ) : ZMod (p^9))^2 * Tpair (p^9) (p^2) := by
    have h := ratioProd_sq_sub_one_pge5_r2_full (p := p) (m := 1) hp5
    dsimp only at h
    norm_num at h
    simpa [V, mul_assoc] using h
  have hT : (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 9)) (ZMod (p^2))) (Tpair (p^9) (p^2)) = 0 := by
    have h := Tpair_cast_zero_pge5 (p := p) (r := 2) hp5 (by norm_num : 1 ≤ 2)
    dsimp only at h
    simpa using h
  have hVsq5 : V5^2 - 1 = 0 := by
    dsimp [V5]
    change ((ZMod.castHom (pow_dvd_pow p (by norm_num : 5 ≤ 9)) (ZMod (p^5))) V)^2 - 1 = 0
    rw [← map_pow (ZMod.castHom (pow_dvd_pow p (by norm_num : 5 ≤ 9)) (ZMod (p^5))) V 2]
    rw [← map_one (ZMod.castHom (pow_dvd_pow p (by norm_num : 5 ≤ 9)) (ZMod (p^5)))]
    rw [← map_sub]
    rw [hVsq_high]
    have hzero := p4_mul_T_zero_mod_p5_of_T_cast_p2_zero p (Tpair (p^9) (p^2)) hT
    rw [show (2 : ZMod (p^9)) * (((p^2 : ℕ) : ZMod (p^9))^2) * Tpair (p^9) (p^2) =
        (2 : ZMod (p^9)) * ((((p^2 : ℕ) : ZMod (p^9))^2) * Tpair (p^9) (p^2)) by ring]
    rw [map_mul]
    rw [hzero]
    simp
  have hVminus_cast_p4 : (ZMod.castHom (show (p^2)^2 ∣ p^5 by
        convert pow_dvd_pow p (by norm_num : 4 ≤ 5) using 1 <;> ring) (ZMod ((p^2)^2))) (V5 - 1) = 0 := by
    dsimp [V5, V]
    change (ZMod.castHom (show (p^2)^2 ∣ p^5 by
        convert pow_dvd_pow p (by norm_num : 4 ≤ 5) using 1 <;> ring) (ZMod ((p^2)^2)))
      ((ZMod.castHom (pow_dvd_pow p (by norm_num : 5 ≤ 9)) (ZMod (p^5))) (ratioProd (p^9) (p^2) 1) - 1) = 0
    rw [map_sub, map_one]
    rw [show (ZMod.castHom (show (p^2)^2 ∣ p^5 by
          convert pow_dvd_pow p (by norm_num : 4 ≤ 5) using 1 <;> ring) (ZMod ((p^2)^2)))
        ((ZMod.castHom (pow_dvd_pow p (by norm_num : 5 ≤ 9)) (ZMod (p^5))) (ratioProd (p^9) (p^2) 1)) =
        (ZMod.castHom (show (p^2)^2 ∣ p^9 by
          convert pow_dvd_pow p (by norm_num : 4 ≤ 9) using 1 <;> ring) (ZMod ((p^2)^2))) (ratioProd (p^9) (p^2) 1) by
      have hcomp := ZMod.castHom_comp (show (p^2)^2 ∣ p^5 by
          convert pow_dvd_pow p (by norm_num : 4 ≤ 5) using 1 <;> ring) (pow_dvd_pow p (by norm_num : 5 ≤ 9))
      exact congrFun (congrArg DFunLike.coe hcomp) (ratioProd (p^9) (p^2) 1)]
    have hcast := ratioProd_cast_to_qsq_pge5 (p := p) (r := 2) (m := 1) hp (by norm_num : 1 ≤ 2)
    dsimp only at hcast
    have hone := ratioProd_eq_one_mod_qsq_pge5 (p := p) (r := 2) (m := 1) hp5 (by norm_num : 1 ≤ 2)
    dsimp only at hone
    rw [show (ZMod.castHom (show (p^2)^2 ∣ p^9 by
          convert pow_dvd_pow p (by norm_num : 4 ≤ 9) using 1 <;> ring) (ZMod ((p^2)^2))) (ratioProd (p^9) (p^2) 1) = ratioProd ((p^2)^2) (p^2) 1 by simpa using hcast]
    rw [hone]
    simp
  -- Direct divisibility in `ZMod (p^5)` from the cast to `ZMod (p^4)`.
  have hsq5' : (V5 - 1)^2 = 0 := by
    haveI : NeZero (p^5) := ⟨pow_ne_zero 5 hp0⟩
    rw [← ZMod.natCast_zmod_val (V5 - 1)]
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    have hv : (p^2)^2 ∣ (V5 - 1).val := by
      rw [← ZMod.natCast_zmod_val (V5 - 1)] at hVminus_cast_p4
      have hdiv45 : (p^2)^2 ∣ p^5 := by
        convert pow_dvd_pow p (by norm_num : 4 ≤ 5) using 1 <;> ring
      rw [show (ZMod.castHom hdiv45 (ZMod ((p^2)^2))) (((V5 - 1).val : ℕ) : ZMod (p^5)) = (((V5 - 1).val : ℕ) : ZMod ((p^2)^2)) from ZMod.cast_natCast hdiv45 _] at hVminus_cast_p4
      exact (ZMod.natCast_eq_zero_iff (V5 - 1).val ((p^2)^2)).mp hVminus_cast_p4
    obtain ⟨k,hk⟩ := hv
    rw [hk]
    suffices p^5 ∣ p^8 * k^2 by
      convert this using 1
      ring
    exact dvd_mul_of_dvd_left (pow_dvd_pow p (by norm_num : 5 ≤ 8)) (k^2)
  have h2cop : Nat.Coprime 2 (p^5) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by intro h; have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h; omega)
  have h2unit : (2 : ZMod (p^5)) * (2 : ZMod (p^5))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one (n := p^5) 2 h2cop
  have hVminus5 : V5 - 1 = 0 := by
    have hhalf := sub_one_eq_inv_two_mul_sq_sub_one_zmod (p^5) V5 h2unit hsq5'
    rw [hVsq5] at hhalf
    simpa using hhalf
  dsimp [V5] at hVminus5
  change (ZMod.castHom (pow_dvd_pow p (by norm_num : 5 ≤ 9)) (ZMod (p^5))) (V - 1) = 0
  rw [map_sub, map_one]
  simpa [V] using hVminus5

lemma ratioProd_sub_one_pge5_r2_full
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    let q := p^2
    let M := p^9
    let V : ZMod M := ratioProd M q 1
    let T : ZMod M := Tpair M q
    V - 1 = (q : ZMod M)^2 * T := by
  intro q M V T
  subst q; subst M; subst V; subst T
  have hp : p.Prime := Fact.out
  have h2cop : Nat.Coprime 2 (p^9) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by intro h; have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h; omega)
  have h2unit : (2 : ZMod (p^9)) * (2 : ZMod (p^9))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one (n := p^9) 2 h2cop
  have hhalf := sub_one_eq_inv_two_mul_sq_sub_one_zmod (p^9) (ratioProd (p^9) (p^2) 1) h2unit
    (ratioProd_sub_one_sq_zero_pge5_r2_full (p := p) hp5)
  have hsq := ratioProd_sq_sub_one_pge5_r2_full (p := p) (m := 1) hp5
  dsimp only at hsq
  norm_num at hsq
  rw [hhalf, hsq]
  have h2unit' : (2 : ZMod (p^9))⁻¹ * (2 : ZMod (p^9)) = 1 := by
    rw [mul_comm]
    exact h2unit
  calc
    (2 : ZMod (p^9))⁻¹ * (2 * (((p : ZMod (p^9)) ^ 2) ^ 2) * Tpair (p ^ 9) (p ^ 2))
        = ((2 : ZMod (p^9))⁻¹ * (2 : ZMod (p^9))) * ((((p : ZMod (p^9)) ^ 2) ^ 2) * Tpair (p^9) (p^2)) := by ring
    _ = ((((p : ZMod (p^9)) ^ 2) ^ 2) * Tpair (p^9) (p^2)) := by rw [h2unit', one_mul]
    _ = ((((p^2 : ℕ) : ZMod (p^9)) ^ 2) * Tpair (p^9) (p^2)) := by
      rw [show ((p^2 : ℕ) : ZMod (p^9)) = (p : ZMod (p^9))^2 by exact (Nat.cast_pow (α := ZMod (p^9)) p 2)]

lemma key_zmod_congruence_pge5_r2_full
    (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    let q := p^2
    let n := p^(2-1)
    let M := p ^ (3 * 2 + 3)
    let A := Nat.choose (3*n) n
    let B := Nat.choose (2*n) n
    let Aq := Nat.choose (3*q) q
    let Bq := Nat.choose (2*q) q
    ((Aq : ZMod M)^2 - (A : ZMod M)^2) =
      (27 : ZMod M) * ((Bq : ZMod M) - (B : ZMod M)) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact key_zmod_congruence_pge5_r2_of_ratio_linear p hp5
    (ratioProd_sq_sub_one_pge5_r2_full (p := p) (m := 2) hp5)
    (ratioProd_sub_one_pge5_r2_full (p := p) hp5)

lemma oeis_357569_conjecture_0_pge5_r2_full
    (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    a (p ^ 2) ≡ a (p ^ (2 - 1)) [ZMOD ((p : ℤ) ^ (3 * 2 + 3))] := by
  letI : Fact p.Prime := ⟨hp⟩
  apply oeis_357569_step_of_key
  exact int_key_congruence_of_zmod_key p 2 (key_zmod_congruence_pge5_r2_full p hp hp5)

-- BEGIN CaseSplitProgress.lean
open Nat

lemma prime_ge3_eq3_or_ge5 (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) : p = 3 ∨ 5 ≤ p := by
  by_cases h : p = 3
  · exact Or.inl h
  · right
    have hpodd : p ≠ 4 := by
      intro hp4
      subst p
      norm_num at hp
    omega

lemma nat_ge2_eq2_or_ge3 (r : ℕ) (hr : 2 ≤ r) : r = 2 ∨ 3 ≤ r := by
  omega

-- BEGIN P3ResiduesProgress.lean
open Nat
open scoped BigOperators
set_option maxRecDepth 1000000

lemma ratioProd_eq_one_mod_3pow5_of_r_ge5 (r m : ℕ) (hr : 5 ≤ r) :
    ratioProd (3^5) (3^r) m = 1 := by
  classical
  dsimp [ratioProd]
  apply Finset.prod_eq_one
  intro i hi
  have hzero : (((m * 3^r : ℕ) : ZMod (3^5))) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact dvd_mul_of_dvd_right (pow_dvd_pow 3 hr) m
  rw [hzero]
  ring

lemma choose_two_three_pow_step_mod_3pow5_eq_self
    (r : ℕ) (hr : 5 ≤ r) :
    ((Nat.choose (2 * 3^r) (3^r) : ℕ) : ZMod (3^5)) =
      ((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5)) := by
  have hp : Nat.Prime 3 := by norm_num
  have hcop : ∀ i ∈ unitReps (3^r), Nat.Coprime i (3^5) := by
    intro i hi
    have hi' : i < 3^r ∧ Nat.Coprime i (3^r) := by
      rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
      exact hi
    have hnot : ¬ 3 ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hi'.2
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot
  have hstep := prime_power_step_product_ratioProd_zmod_mod (N := 3^5) (p := 3) (r := r) (m := 1) hp (by omega : 1 ≤ r) hcop
  rw [ratioProd_eq_one_mod_3pow5_of_r_ge5 r 1 hr] at hstep
  simpa [one_add_one_eq_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hstep

lemma choose_three_three_pow_step_mod_3pow5_eq_self
    (r : ℕ) (hr : 5 ≤ r) :
    ((Nat.choose (3 * 3^r) (3^r) : ℕ) : ZMod (3^5)) =
      ((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod (3^5)) := by
  have hp : Nat.Prime 3 := by norm_num
  have hcop : ∀ i ∈ unitReps (3^r), Nat.Coprime i (3^5) := by
    intro i hi
    have hi' : i < 3^r ∧ Nat.Coprime i (3^r) := by
      rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
      exact hi
    have hnot : ¬ 3 ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hi'.2
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot
  have hstep := prime_power_step_product_ratioProd_zmod_mod (N := 3^5) (p := 3) (r := r) (m := 2) hp (by omega : 1 ≤ r) hcop
  rw [ratioProd_eq_one_mod_3pow5_of_r_ge5 r 2 hr] at hstep
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.succ_eq_add_one] using hstep

lemma choose_two_three_pow_mod_3pow5_residue (s : ℕ) (hs : 1 ≤ s) :
    ((Nat.choose (2 * 3^s) (3^s) : ℕ) : ZMod (3^5)) = 20 := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
      by_cases h1 : s = 1
      · subst s; decide
      by_cases h2 : s = 2
      · subst s; decide
      by_cases h3 : s = 3
      · subst s; decide
      by_cases h4 : s = 4
      · subst s; decide
      have hs5 : 5 ≤ s := by omega
      have hprev := choose_two_three_pow_step_mod_3pow5_eq_self s hs5
      rw [hprev]
      exact ih (s-1) (by omega) (by omega)

lemma choose_three_three_pow_mod_3pow5_residue (s : ℕ) (hs : 1 ≤ s) :
    ((Nat.choose (3 * 3^s) (3^s) : ℕ) : ZMod (3^5)) = 84 := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
      by_cases h1 : s = 1
      · subst s; decide
      by_cases h2 : s = 2
      · subst s; decide
      by_cases h3 : s = 3
      · subst s; decide
      by_cases h4 : s = 4
      · subst s; decide
      have hs5 : 5 ≤ s := by omega
      have hprev := choose_three_three_pow_step_mod_3pow5_eq_self s hs5
      rw [hprev]
      exact ih (s-1) (by omega) (by omega)


lemma coeff_cast_3pow5_p3 (r : ℕ) (hr : 3 ≤ r) :
    let M := 3 ^ (3 * r + 3)
    let A0 : ZMod M := ((Nat.choose (3 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod M)
    let B0 : ZMod M := ((Nat.choose (2 * 3^(r-1)) (3^(r-1)) : ℕ) : ZMod M)
    (ZMod.castHom (show 3^5 ∣ M by
      dsimp
      exact pow_dvd_pow 3 (by omega : 5 ≤ 3 * r + 3)) (ZMod (3^5)))
      ((6 : ZMod M) * A0^2 - (27 : ZMod M) * B0) = 0 := by
  exact coeff_cast_3pow5_p3_of_residues r hr
    (choose_three_three_pow_mod_3pow5_residue (r-1) (by omega))
    (choose_two_three_pow_mod_3pow5_residue (r-1) (by omega))


-- BEGIN P3UnitSumProgress.lean
open scoped BigOperators

lemma zmod_prime_pow_units_sq_sum_mul_three_eq_zero (n : ℕ) (_hn : 1 ≤ n) :
    (3 : ZMod (3^n)) * (∑ x : (ZMod (3 ^ n))ˣ, ((x : ZMod (3 ^ n)) ^ 2)) = 0 := by
  let R := ZMod (3 ^ n)
  let S : R := ∑ x : Rˣ, ((x : R) ^ 2)
  have h2cop : Nat.Coprime 2 (3 ^ n) := by
    apply Nat.Coprime.pow_right
    norm_num
  have h2is : IsUnit (2 : R) := (ZMod.isUnit_iff_coprime 2 (3 ^ n)).mpr h2cop
  let u : Rˣ := h2is.unit
  have hu : (u : R) = 2 := h2is.unit_spec
  have hperm : (∑ x : Rˣ, (((u * x : Rˣ) : R) ^ 2)) = S := by
    simpa [S] using (Equiv.sum_comp (Equiv.mulLeft u) (fun x : Rˣ => ((x : R) ^ 2)))
  have hscale : (∑ x : Rˣ, (((u * x : Rˣ) : R) ^ 2)) = (2 : R) ^ 2 * S := by
    simp [S, hu, mul_pow, Finset.mul_sum]
  have hS : S = (2 : R) ^ 2 * S := hperm.symm.trans hscale
  calc
    (3 : R) * S = ((2 : R) ^ 2 - 1) * S := by ring
    _ = (2 : R) ^ 2 * S - S := by ring
    _ = S - S := by rw [← hS]
    _ = 0 := sub_self S

lemma zmod_prime_pow_units_inv_sq_sum_mul_three_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    (3 : ZMod (3^n)) * (∑ x : (ZMod (3 ^ n))ˣ, (((x : ZMod (3 ^ n))⁻¹) ^ 2)) = 0 := by
  classical
  have hsquares := zmod_prime_pow_units_sq_sum_mul_three_eq_zero n hn
  have hperm :
      (∑ x : (ZMod (3 ^ n))ˣ, (((x : ZMod (3 ^ n))⁻¹) ^ 2)) =
        ∑ x : (ZMod (3 ^ n))ˣ, ((x : ZMod (3 ^ n)) ^ 2) := by
    refine Fintype.sum_equiv (Equiv.inv ((ZMod (3 ^ n))ˣ)) _ _ ?_
    intro x
    rw [Equiv.inv_apply]
    have hinv : ((x : ZMod (3 ^ n))⁻¹) = ((x⁻¹ : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) := by
      exact ZMod.inv_eq_of_mul_eq_one (3 ^ n) (x : ZMod (3 ^ n)) ((x⁻¹ : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) (by exact x.val_inv)
    rw [hinv]
  rw [hperm]
  exact hsquares

-- BEGIN P3LiftScratch.lean

open Nat
open scoped BigOperators

namespace P3LiftScratch

def unitReps (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun i => Nat.Coprime i q)

lemma coprime_prime_pow_iff_not_dvd {p i k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    Nat.Coprime i (p ^ k) ↔ ¬ p ∣ i := by
  constructor
  · intro h hdiv
    have hpdvd : p ∣ p^k := dvd_pow_self p (Nat.ne_of_gt hk)
    have hpdvdg : p ∣ Nat.gcd i (p^k) := Nat.dvd_gcd hdiv hpdvd
    rw [h.gcd_eq_one] at hpdvdg
    exact hp.not_dvd_one hpdvdg
  · intro hnot
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot

lemma three_pow_pred_pos (r : ℕ) : 0 < 3 ^ (r - 1) := pow_pos (by norm_num) _

lemma three_pow_eq_three_mul_pred (r : ℕ) (hr : 1 ≤ r) :
    3 ^ r = 3 * 3 ^ (r - 1) := by
  calc
    3 ^ r = 3 ^ ((r - 1) + 1) := by congr; omega
    _ = 3 ^ (r - 1) * 3 := by rw [pow_succ]
    _ = 3 * 3 ^ (r - 1) := by omega

lemma three_dvd_three_pow_pred (r : ℕ) (hr : 2 ≤ r) : 3 ∣ 3 ^ (r - 1) := by
  exact dvd_pow_self 3 (Nat.ne_of_gt (by omega : 0 < r - 1))

lemma three_dvd_add_mul_three_pow_pred_iff (r a k : ℕ) (hr : 2 ≤ r) :
    3 ∣ a + k * 3 ^ (r - 1) ↔ 3 ∣ a := by
  have hterm : 3 ∣ k * 3 ^ (r - 1) := dvd_mul_of_dvd_right (three_dvd_three_pow_pred r hr) k
  rw [Nat.add_comm]
  exact (Nat.dvd_add_iff_right hterm).symm

lemma coprime_add_mul_three_pow_pred_iff (r a k : ℕ) (hr : 2 ≤ r) :
    Nat.Coprime (a + k * 3 ^ (r - 1)) (3 ^ r) ↔
      Nat.Coprime a (3 ^ (r - 1)) := by
  have hp : Nat.Prime 3 := by norm_num
  rw [coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)]
  rw [coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r - 1)]
  exact not_congr (three_dvd_add_mul_three_pow_pred_iff r a k hr)

lemma three_dvd_mod_three_pow_pred_iff (r i : ℕ) (hr : 2 ≤ r) :
    3 ∣ i % 3 ^ (r - 1) ↔ 3 ∣ i := by
  have hqpos : 0 < 3 ^ (r - 1) := three_pow_pred_pos r
  have hterm : 3 ∣ (i / 3 ^ (r - 1)) * 3 ^ (r - 1) :=
    dvd_mul_of_dvd_right (three_dvd_three_pow_pred r hr) (i / 3 ^ (r - 1))
  constructor
  · intro hmod
    rw [← Nat.mod_add_div i (3 ^ (r - 1))]
    exact dvd_add hmod (by simpa [Nat.mul_comm] using hterm)
  · intro hi
    have hadd : 3 ∣ i % 3 ^ (r - 1) + (i / 3 ^ (r - 1)) * 3 ^ (r - 1) := by
      simpa [Nat.mul_comm, Nat.mod_add_div] using hi
    have hadd' : 3 ∣ (i / 3 ^ (r - 1)) * 3 ^ (r - 1) + i % 3 ^ (r - 1) := by
      simpa [Nat.add_comm] using hadd
    exact (Nat.dvd_add_iff_right hterm).mpr hadd'

lemma coprime_mod_three_pow_pred_iff (r i : ℕ) (hr : 2 ≤ r) :
    Nat.Coprime (i % 3 ^ (r - 1)) (3 ^ (r - 1)) ↔ Nat.Coprime i (3 ^ r) := by
  have hp : Nat.Prime 3 := by norm_num
  rw [coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r - 1)]
  rw [coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)]
  exact not_congr (three_dvd_mod_three_pow_pred_iff r i hr)

lemma div_three_pow_pred_lt_three_of_lt (r i : ℕ) (hr : 1 ≤ r) (hi : i < 3 ^ r) :
    i / 3 ^ (r - 1) < 3 := by
  have hqpos : 0 < 3 ^ (r - 1) := three_pow_pred_pos r
  have hpow : 3 ^ r = 3 * 3 ^ (r - 1) := three_pow_eq_three_mul_pred r hr
  rw [hpow] at hi
  exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm, Nat.mul_assoc] using hi)

lemma sum_units_three_lift_unitReps (r : ℕ) (hr : 2 ≤ r)
    (F : ℕ → R) [CommSemiring R] :
    (∑ i ∈ unitReps (3 ^ r), F (i % 3 ^ (r - 1))) =
      (3 : R) * ∑ a ∈ unitReps (3 ^ (r - 1)), F a := by
  classical
  let q : ℕ := 3 ^ (r - 1)
  let s : Finset ℕ := unitReps (3 ^ r)
  let t : Finset (ℕ × ℕ) := (unitReps q).product (Finset.range 3)
  have hbij :
      (∑ i ∈ s, F (i % q)) = (∑ x ∈ t, F x.1) := by
    refine Finset.sum_bij'
      (s := s) (t := t) (f := fun i => F (i % q)) (g := fun x : ℕ × ℕ => F x.1)
      (fun i _hi => (i % q, i / q))
      (fun x _hx => x.1 + x.2 * q)
      ?hi ?hj ?left_inv ?right_inv ?hfg
    · intro i hi
      change i ∈ unitReps (3 ^ r) at hi
      rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
      apply Finset.mk_mem_product
      · rw [unitReps, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.mod_lt i (three_pow_pred_pos r),
          (coprime_mod_three_pow_pred_iff r i hr).mpr hi.2⟩
      · rw [Finset.mem_range]
        exact div_three_pow_pred_lt_three_of_lt r i (by omega) hi.1
    · intro x hx
      rcases x with ⟨a, k⟩
      have hx' : (a, k) ∈ (unitReps q) ×ˢ (Finset.range 3) := by simpa [t] using hx
      rw [Finset.mem_product] at hx'
      rcases hx' with ⟨ha, hk⟩
      rw [unitReps, Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_range] at hk
      change a + k * q ∈ unitReps (3 ^ r)
      rw [unitReps, Finset.mem_filter, Finset.mem_range]
      constructor
      · have hpow : 3 ^ r = 3 * 3 ^ (r - 1) := three_pow_eq_three_mul_pred r (by omega)
        dsimp [q] at ha ⊢
        rw [hpow]
        nlinarith [ha.1, hk, three_pow_pred_pos r]
      · dsimp [q] at ha ⊢
        exact (coprime_add_mul_three_pow_pred_iff r a k hr).mpr ha.2
    · intro i hi
      dsimp [q]
      simpa [Nat.mul_comm] using (Nat.mod_add_div i (3 ^ (r - 1)))
    · intro x hx
      rcases x with ⟨a, k⟩
      have hx' : (a, k) ∈ (unitReps q) ×ˢ (Finset.range 3) := by simpa [t] using hx
      rw [Finset.mem_product] at hx'
      rcases hx' with ⟨ha, _hk⟩
      rw [unitReps, Finset.mem_filter, Finset.mem_range] at ha
      ext
      · change (a + k * q) % q = a
        exact Nat.add_mul_mod_self_right a k q |>.trans (Nat.mod_eq_of_lt ha.1)
      · change (a + k * q) / q = k
        rw [Nat.add_mul_div_right _ _ (three_pow_pred_pos r), Nat.div_eq_of_lt ha.1, zero_add]
    · intro i hi
      rfl
  calc
    (∑ i ∈ unitReps (3 ^ r), F (i % 3 ^ (r - 1))) = (∑ i ∈ s, F (i % q)) := by rfl
    _ = (∑ x ∈ t, F x.1) := hbij
    _ = (3 : R) * ∑ a ∈ unitReps (3 ^ (r - 1)), F a := by
      simp [t, q, Finset.sum_product, Finset.mul_sum]

lemma sum_units_three_lift (r : ℕ) (hr : 2 ≤ r)
    (F : ℕ → R) [CommSemiring R] :
    (∑ i ∈ (Finset.range (3 ^ r)).filter (Nat.Coprime · (3 ^ r)), F (i % 3 ^ (r - 1))) =
      (3 : R) * ∑ a ∈ (Finset.range (3 ^ (r - 1))).filter (Nat.Coprime · (3 ^ (r - 1))), F a := by
  simpa [unitReps] using sum_units_three_lift_unitReps (r := r) (hr := hr) (F := F)

lemma sum_units_three_lift_zmod_inv_sq (r : ℕ) (hr : 2 ≤ r) :
    (∑ i ∈ (Finset.range (3 ^ r)).filter (Nat.Coprime · (3 ^ r)),
        (((i % 3 ^ (r - 1) : ℕ) : ZMod (3 ^ (r - 1)))⁻¹) ^ 2) =
      (3 : ZMod (3 ^ (r - 1))) *
        ∑ a ∈ (Finset.range (3 ^ (r - 1))).filter (Nat.Coprime · (3 ^ (r - 1))),
          (((a : ℕ) : ZMod (3 ^ (r - 1)))⁻¹) ^ 2 := by
  simpa using
    (sum_units_three_lift (r := r) (hr := hr)
      (R := ZMod (3 ^ (r - 1)))
      (F := fun a : ℕ => (((a : ℕ) : ZMod (3 ^ (r - 1)))⁻¹) ^ 2))


end P3LiftScratch

-- BEGIN P3TpairProgress.lean
open scoped BigOperators
open Nat

lemma cast_inv_mul_three_pow_sub_to_prev
    (r i : ℕ) (hr : 2 ≤ r) (hi_lt : i < 3^r) (hcop : Nat.Coprime i (3^r)) :
    let d := 3^(r-1)
    let q := 3^r
    let M := 3 ^ (3 * r + 3)
    ((ZMod.castHom (show d ∣ M by
        dsimp [d, M]
        exact pow_dvd_pow 3 (by omega : r - 1 ≤ 3 * r + 3)) (ZMod d))
      ((((i : ZMod M) * ((q - i : ℕ) : ZMod M))⁻¹) : ZMod M) : ZMod d) =
      - (((i % d : ℕ) : ZMod d)⁻¹)^2 := by
  intro d q M
  subst d; subst q; subst M
  let d := 3^(r-1)
  have hdvdM : d ∣ 3 ^ (3 * r + 3) := by
    dsimp [d]
    exact pow_dvd_pow 3 (by omega : r - 1 ≤ 3 * r + 3)
  have hdvdq : d ∣ 3^r := by
    dsimp [d]
    exact pow_dvd_pow 3 (by omega : r - 1 ≤ r)
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hcopd_i : Nat.Coprime i d := hcop.coprime_dvd_right hdvdq
  have hcop_mod : Nat.Coprime (i % d) d := by
    dsimp [d]
    exact (P3LiftScratch.coprime_mod_three_pow_pred_iff r i hr).mpr hcop
  have hsub_mod : ((3^r - i : ℕ) : ZMod d) = - ((i % d : ℕ) : ZMod d) := by
    have hle : i ≤ 3^r := le_of_lt hi_lt
    rw [Nat.cast_sub hle]
    have hqzero : ((3^r : ℕ) : ZMod d) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hdvdq
    rw [hqzero]
    simp
  have hprod_cast : ((i * (3^r - i) : ℕ) : ZMod d) = - (((i % d : ℕ) : ZMod d)^2) := by
    rw [Nat.cast_mul, hsub_mod]
    have hi_cast_mod : ((i : ℕ) : ZMod d) = ((i % d : ℕ) : ZMod d) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact (Nat.mod_modEq i d).symm
    rw [hi_cast_mod]
    ring
  have hnot3 : ¬ 3 ∣ i := by
    have hp : Nat.Prime 3 := by norm_num
    exact (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hcop
  have hcopM_i : Nat.Coprime i (3 ^ (3 * r + 3)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact (by norm_num : Nat.Prime 3).coprime_iff_not_dvd.mpr hnot3
  have hcop_sub_q : Nat.Coprime (3^r - i) (3^r) := (Nat.coprime_self_sub_left (le_of_lt hi_lt)).2 hcop
  have hnot3sub : ¬ 3 ∣ (3^r - i) := by
    have hp : Nat.Prime 3 := by norm_num
    exact (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hcop_sub_q
  have hcopM_sub : Nat.Coprime (3^r - i) (3 ^ (3 * r + 3)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact (by norm_num : Nat.Prime 3).coprime_iff_not_dvd.mpr hnot3sub
  have hprodM : Nat.Coprime (i * (3^r - i)) (3 ^ (3 * r + 3)) := hcopM_i.mul_left hcopM_sub
  have hprodd : Nat.Coprime (i * (3^r - i)) d := hprodM.coprime_dvd_right hdvdM
  have hterm_eq : ((i : ZMod (3 ^ (3 * r + 3))) * ((3^r - i : ℕ) : ZMod (3 ^ (3 * r + 3)))) = ((i * (3^r - i) : ℕ) : ZMod (3 ^ (3 * r + 3))) := by
    norm_num [Nat.cast_mul]
  rw [hterm_eq]
  rw [zmod_cast_inv_of_coprime_any (M := 3 ^ (3 * r + 3)) (q := d) (i := i * (3^r - i)) hdvdM hprodM hprodd]
  rw [hprod_cast]
  have hunit : IsUnit ((i % d : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime (i%d) d).mpr hcop_mod
  let u : (ZMod d)ˣ := hunit.unit
  have hu : (u : ZMod d) = (i % d : ℕ) := hunit.unit_spec
  rw [← hu]
  have hmul : (-(u : ZMod d)^2) * ( - (((u⁻¹ : (ZMod d)ˣ) : ZMod d)^2)) = 1 := by
    rw [neg_mul_neg]
    calc
      (u : ZMod d)^2 * (((u⁻¹ : (ZMod d)ˣ) : ZMod d)^2)
          = (((u : ZMod d) * ((u⁻¹ : (ZMod d)ˣ) : ZMod d))^2) := by ring
      _ = 1 := by simp
  have hinv : (-(u : ZMod d)^2)⁻¹ = - (((u⁻¹ : (ZMod d)ˣ) : ZMod d)^2) :=
    ZMod.inv_eq_of_mul_eq_one d (-(u : ZMod d)^2) (- (((u⁻¹ : (ZMod d)ˣ) : ZMod d)^2)) hmul
  rw [hinv]
  have huinv : ((u⁻¹ : (ZMod d)ˣ) : ZMod d) = ((u : ZMod d)⁻¹) := by
    exact (ZMod.inv_eq_of_mul_eq_one d (u : ZMod d) ((u⁻¹ : (ZMod d)ˣ) : ZMod d) (by exact u.val_inv)).symm
  rw [huinv]

lemma Tpair_cast_zero_p3_prev (r : ℕ) (hr : 3 ≤ r) :
    let M := 3 ^ (3 * r + 3)
    let T : ZMod M := Tpair M (3^r)
    (ZMod.castHom (show 3^(r-1) ∣ M by
      change 3^(r-1) ∣ 3^(3 * r + 3)
      exact pow_dvd_pow 3 (by omega : r - 1 ≤ 3 * r + 3)) (ZMod (3^(r-1)))) T = 0 := by
  intro M T
  subst M; subst T
  let d := 3^(r-1)
  have hdiv : d ∣ 3 ^ (3 * r + 3) := by
    dsimp [d]
    exact pow_dvd_pow 3 (by omega : r - 1 ≤ 3 * r + 3)
  dsimp [Tpair, unitReps]
  change (ZMod.castHom hdiv (ZMod d))
    (∑ i ∈ (Finset.range (3^r)).filter (fun i => Nat.Coprime i (3^r)),
      ((((i : ZMod (3 ^ (3 * r + 3))) * ((3^r - i : ℕ) : ZMod (3 ^ (3 * r + 3))))⁻¹))) = 0
  rw [map_sum]
  have hsum : (∑ x ∈ Finset.range (3 ^ r) with x.Coprime (3 ^ r),
      (ZMod.castHom hdiv (ZMod d)) ((↑x * ↑(3 ^ r - x))⁻¹ : ZMod (3 ^ (3 * r + 3)))) =
      - ∑ x ∈ Finset.range (3 ^ r) with x.Coprime (3 ^ r),
        (((x % d : ℕ) : ZMod d)⁻¹)^2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_lt : i < 3^r := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hcop : Nat.Coprime i (3^r) := (Finset.mem_filter.mp hi).2
    exact cast_inv_mul_three_pow_sub_to_prev r i (by omega : 2 ≤ r) hi_lt hcop
  rw [hsum]
  change - (∑ x ∈ Finset.range (3 ^ r) with x.Coprime (3 ^ r),
      (((x % 3 ^ (r - 1) : ℕ) : ZMod (3 ^ (r - 1)))⁻¹) ^ 2) = 0
  have hlift := P3LiftScratch.sum_units_three_lift_zmod_inv_sq r (by omega : 2 ≤ r)
  rw [hlift]
  rw [sum_range_coprime_inv_sq_eq_units]
  have hmul := zmod_prime_pow_units_inv_sq_sum_mul_three_eq_zero (r-1) (by omega : 1 ≤ r-1)
  simpa [d, neg_eq_zero] using congrArg Neg.neg hmul

-- BEGIN P3LinearProgress.lean

open scoped BigOperators
open Nat

lemma zmod_sq_zero_of_cast_q_eq_zero (q : ℕ) [NeZero (q^2)] (z : ZMod (q^2))
    (h : (ZMod.cast z : ZMod q) = 0) : z^2 = 0 := by
  rw [← ZMod.natCast_zmod_val z]
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hdiv : q ∣ q^2 := dvd_pow_self q (by norm_num)
  have hv : q ∣ z.val := by
    rw [← ZMod.natCast_zmod_val z] at h
    rw [ZMod.cast_natCast hdiv] at h
    exact (ZMod.natCast_eq_zero_iff z.val q).mp h
  obtain ⟨k, hk⟩ := hv
  rw [hk]
  rw [show q^2 = q*q by ring, show (q*k)^2 = (q*k)*(q*k) by ring]
  have hnat : (q * k) * (q * k) = q * q * (k * k) := by ring
  rw [hnat]
  exact dvd_mul_right (q*q) (k*k)

lemma ratioProd_cast_to_q_one (q m : ℕ) [NeZero q] [NeZero (q^2)] :
    (ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)) (ratioProd (q^2) q m) = 1 := by
  classical
  dsimp [ratioProd]
  change (ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q))
      (∏ i ∈ unitReps q, (1 + ((m * q : ℕ) : ZMod (q^2)) * ((i : ℕ) : ZMod (q^2))⁻¹)) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [map_add, map_one, map_mul]
  have hqcast : (ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)) (((m * q : ℕ) : ZMod (q^2))) = 0 := by
    rw [show (ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)) (((m * q : ℕ) : ZMod (q^2))) = (((m * q : ℕ) : ZMod q)) from ZMod.cast_natCast (dvd_pow_self q (by norm_num : 2 ≠ 0)) _]
    rw [ZMod.natCast_eq_zero_iff]
    exact dvd_mul_left q m
  rw [hqcast, zero_mul]
  ring

lemma ratioProd_sq_eq_one_mod_qsq_prime_pow
    (p r m : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    let q := p^r
    ratioProd (q^2) q m ^ 2 = 1 := by
  intro q
  subst q
  classical
  have hq1 : 1 < p^r := prime_pow_one_lt hp hr
  have hcopM : ∀ i ∈ unitReps (p^r), Nat.Coprime i ((p^r)^2) := by
    intro i hi
    rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
    exact Nat.Coprime.pow_right 2 hi.2
  have hcopsub : ∀ i ∈ unitReps (p^r), Nat.Coprime (p^r - i) ((p^r)^2) := by
    intro i hi
    have hmem := unitReps_q_sub_mem hq1 hi
    rw [unitReps, Finset.mem_filter, Finset.mem_range] at hmem
    exact Nat.Coprime.pow_right 2 hmem.2
  rw [ratioProd_sq_eq_pairedProd_generic ((p^r)^2) (p^r) m hq1 hcopM hcopsub]
  dsimp [pairedProd]
  apply Finset.prod_eq_one
  intro i hi
  have hzero : (((p^r : ℕ) : ZMod ((p^r)^2))^2) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  rw [hzero]
  ring

lemma ratioProd_eq_one_mod_qsq_prime_pow
    (p r m : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) (h2 : Nat.Coprime 2 (p^r)) :
    let q := p^r
    ratioProd (q^2) q m = 1 := by
  intro q
  subst q
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : NeZero (p^r) := ⟨pow_ne_zero r hp0⟩
  haveI : NeZero ((p^r)^2) := ⟨pow_ne_zero 2 (pow_ne_zero r hp0)⟩
  let x : ZMod ((p^r)^2) := ratioProd ((p^r)^2) (p^r) m
  let z : ZMod ((p^r)^2) := x - 1
  have hx2 : x^2 = 1 := by
    simpa [x] using ratioProd_sq_eq_one_mod_qsq_prime_pow p r m hp hr
  have hcastx : (ZMod.castHom (dvd_pow_self (p^r) (by norm_num : 2 ≠ 0)) (ZMod (p^r))) x = 1 := by
    simpa [x] using ratioProd_cast_to_q_one (p^r) m
  have hcastz : (ZMod.castHom (dvd_pow_self (p^r) (by norm_num : 2 ≠ 0)) (ZMod (p^r))) z = 0 := by
    dsimp [z]
    change (ZMod.castHom (dvd_pow_self (p^r) (by norm_num : 2 ≠ 0)) (ZMod (p^r))) (x - 1) = 0
    rw [map_sub, hcastx, map_one, sub_self]
  have hz2 : z^2 = 0 := zmod_sq_zero_of_cast_q_eq_zero (p^r) z hcastz
  have htwoz : (2 : ZMod ((p^r)^2)) * z = 0 := by
    have hcalc : x^2 - 1 = z^2 + (2 : ZMod ((p^r)^2)) * z := by
      dsimp [z]
      ring
    rw [hx2, sub_self, hz2, zero_add] at hcalc
    exact hcalc.symm
  have h2unit : IsUnit (2 : ZMod ((p^r)^2)) := by
    apply (ZMod.isUnit_iff_coprime 2 ((p^r)^2)).mpr
    exact Nat.Coprime.pow_right 2 h2
  let u : (ZMod ((p^r)^2))ˣ := h2unit.unit
  have hu : (u : ZMod ((p^r)^2)) = 2 := h2unit.unit_spec
  have hz0 : z = 0 := by
    calc z = ((u⁻¹ : (ZMod ((p^r)^2))ˣ) : ZMod ((p^r)^2)) * ((u : ZMod ((p^r)^2)) * z) := by simp
      _ = ((u⁻¹ : (ZMod ((p^r)^2))ˣ) : ZMod ((p^r)^2)) * ((2 : ZMod ((p^r)^2)) * z) := by rw [hu]
      _ = 0 := by rw [htwoz, mul_zero]
  dsimp [z] at hz0
  exact sub_eq_zero.mp hz0

lemma ratioProd_sub_one_sq_zero_high_p3_new
    (r m : ℕ) (hr : 3 ≤ r) :
    let q := 3^r
    (ratioProd (3 ^ (3 * r + 3)) q m - 1)^2 = 0 := by
  intro q
  subst q
  apply zmod_sq_eq_zero_of_cast_qsq_eq_zero_high (p := 3) (r := r) (by norm_num) hr
  rw [map_sub, map_one]
  rw [ratioProd_cast_to_qsq_pge5 (p := 3) (r := r) (m := m) (by norm_num : Nat.Prime 3) (by omega : 1 ≤ r)]
  rw [ratioProd_eq_one_mod_qsq_prime_pow (p := 3) (r := r) (m := m) (by norm_num : Nat.Prime 3) (by omega : 1 ≤ r)]
  · simp
  · apply Nat.Coprime.pow_right
    norm_num

lemma ratioProd_sub_one_high_p3_new
    (r m : ℕ) (hr : 3 ≤ r) :
    let q := 3^r
    let M := 3 ^ (3 * r + 3)
    ratioProd M q m - 1 = (2 : ZMod M)⁻¹ * (((m * (m + 1) : ℕ) : ZMod M) * (q : ZMod M)^2 * Tpair M q) := by
  intro q M
  subst q; subst M
  have h2cop : Nat.Coprime 2 (3 ^ (3 * r + 3)) := by
    apply Nat.Coprime.pow_right
    norm_num
  have h2unit : (2 : ZMod (3 ^ (3 * r + 3))) * (2 : ZMod (3 ^ (3 * r + 3)))⁻¹ = 1 := by
    exact ZMod.coe_mul_inv_eq_one (n := 3 ^ (3 * r + 3)) 2 h2cop
  rw [← ratioProd_sq_sub_one_high_p3 (r := r) (m := m) hr]
  exact sub_one_eq_inv_two_mul_sq_sub_one_zmod (3 ^ (3 * r + 3)) (ratioProd (3 ^ (3 * r + 3)) (3^r) m) h2unit
    (ratioProd_sub_one_sq_zero_high_p3_new (r := r) (m := m) hr)

lemma ratioProd_linear_m1_p3 (r : ℕ) (hr : 3 ≤ r) :
    let q := 3^r
    let M := 3 ^ (3 * r + 3)
    let V : ZMod M := ratioProd M q 1
    let T : ZMod M := Tpair M q
    V - 1 = (q : ZMod M)^2 * T := by
  intro q M V T
  subst q; subst M; subst V; subst T
  have h := ratioProd_sub_one_high_p3_new (r := r) (m := 1) hr
  dsimp only at h
  have h2cop : Nat.Coprime 2 (3 ^ (3 * r + 3)) := by
    apply Nat.Coprime.pow_right
    norm_num
  have h2unit : (2 : ZMod (3 ^ (3 * r + 3)))⁻¹ * (2 : ZMod (3 ^ (3 * r + 3))) = 1 := by
    simpa [mul_comm] using ZMod.coe_mul_inv_eq_one (n := 3 ^ (3 * r + 3)) 2 h2cop
  norm_num at h
  calc
    ratioProd (3 ^ (3 * r + 3)) (3 ^ r) 1 - 1
        = (2 : ZMod (3 ^ (3 * r + 3)))⁻¹ * (2 * (((3 ^ r : ℕ) : ZMod (3 ^ (3 * r + 3)))^2) * Tpair (3 ^ (3 * r + 3)) (3 ^ r)) := by simpa [Nat.cast_pow] using h
    _ = ((2 : ZMod (3 ^ (3 * r + 3)))⁻¹ * (2 : ZMod (3 ^ (3 * r + 3)))) * (((((3 ^ r : ℕ) : ZMod (3 ^ (3 * r + 3)))^2)) * Tpair (3 ^ (3 * r + 3)) (3 ^ r)) := by ring
    _ = ((((3 ^ r : ℕ) : ZMod (3 ^ (3 * r + 3)))^2)) * Tpair (3 ^ (3 * r + 3)) (3 ^ r) := by rw [h2unit, one_mul]


lemma oeis_357569_conjecture_0_p3_rge3_full (r : ℕ) (hr : 3 ≤ r) :
    a (3 ^ r) ≡ a (3 ^ (r - 1)) [ZMOD ((3 : ℤ) ^ (3 * r + 3))] := by
  exact oeis_357569_p3_rge3_of_T_and_linear_V r hr
    (coeff_cast_3pow5_p3 r hr)
    (Tpair_cast_zero_p3_prev r hr)
    (ratioProd_linear_m1_p3 r hr)

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  have hp_cases := prime_ge3_eq3_or_ge5 p hp hp3
  have hr_cases := nat_ge2_eq2_or_ge3 r hr
  rcases hp_cases with hp_eq3 | hp5
  · subst p
    rcases hr_cases with hr_eq2 | hr3
    · subst r
      decide
    · exact oeis_357569_conjecture_0_p3_rge3_full r hr3
  · rcases hr_cases with hr_eq2 | hr3
    · subst r
      exact oeis_357569_conjecture_0_pge5_r2_full p hp hp5
    · exact oeis_357569_conjecture_0_pge5_rge3 p r hp hp5 hr3
