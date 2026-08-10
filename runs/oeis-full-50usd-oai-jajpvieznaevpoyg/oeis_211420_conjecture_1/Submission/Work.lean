import FormalConjectures.Util.ProblemImports

open Nat

/-- A211420: $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$ -/
def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

def denominator_product (n r : ℕ) : ℤ :=
  (List.range r).map (fun k : ℕ => (8 * n : ℤ) - (2 * k + 1 : ℤ)) |>.prod

lemma Int.natAbs_list_prod (l : List ℤ) : l.prod.natAbs = (l.map Int.natAbs).prod := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Int.natAbs_mul]

lemma denominator_product_natAbs (n r : ℕ) :
    (denominator_product n r).natAbs =
      ((List.range r).map (fun k : ℕ => (((8 * n : ℤ) - (2 * k + 1 : ℤ)).natAbs))).prod := by
  simp [denominator_product, Int.natAbs_list_prod, Function.comp_def]


lemma denominator_product_natAbs_finset (n r : ℕ) :
    (denominator_product n r).natAbs =
      ∏ k ∈ Finset.range r, (((8 * n : ℤ) - (2 * k + 1 : ℤ)).natAbs) := by
  rw [denominator_product_natAbs]
  let f : ℕ → ℕ := fun k => (((8 * n : ℤ) - (2 * k + 1 : ℤ)).natAbs)
  have h := @List.prod_toFinset ℕ ℕ _ _ f (List.range r) (List.nodup_range)
  dsimp [f] at h
  rw [← h]
  simpa


lemma list_prod_ne_zero_of_all {l : List ℕ} (h : ∀ x ∈ l, x ≠ 0) : l.prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.prod_cons]
      exact mul_ne_zero (h x (by simp)) (ih (by intro y hy; exact h y (by simp [hy])))

lemma denominator_product_natAbs_ne_zero (n r : ℕ) : (denominator_product n r).natAbs ≠ 0 := by
  rw [denominator_product_natAbs]
  apply list_prod_ne_zero_of_all
  intro x hx
  rw [List.mem_map] at hx
  rcases hx with ⟨k, hk, rfl⟩
  rw [Int.natAbs_ne_zero]
  intro h
  omega


lemma mul_mod_add_div_div (m n q : ℕ) (hq : 0 < q) :
    (m * (n % q + q * (n / q))) / q = m * (n / q) + (m * (n % q)) / q := by
  rw [mul_add]
  have h : m * (q * (n / q)) = q * (m * (n / q)) := by ring
  rw [h]
  rw [Nat.add_mul_div_left _ _ hq]
  omega

lemma small_landau_remainder (c q : ℕ) (hc : c < q) :
    (4*c)/q + (3*c)/q + (2*c)/q ≤ (8*c)/q := by
  have hq : 0 < q := by omega
  have hcases : (8*c < q) ∨ (q ≤ 8*c ∧ 8*c < q*2) ∨
      (2*q ≤ 8*c ∧ 8*c < q*3) ∨ (3*q ≤ 8*c ∧ 8*c < q*4) ∨
      (4*q ≤ 8*c ∧ 8*c < 5*q) ∨ (5*q ≤ 8*c ∧ 8*c < 6*q) ∨
      (6*q ≤ 8*c ∧ 8*c < 7*q) ∨ (7*q ≤ 8*c) := by
    omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have h4 : 4*c < q := by omega
    have h3 : 3*c < q := by omega
    have h2 : 2*c < q := by omega
    simp [Nat.div_eq_of_lt h4, Nat.div_eq_of_lt h3, Nat.div_eq_of_lt h2, Nat.div_eq_of_lt h0]
  · rcases h1 with ⟨hlo, hhi⟩
    have u4 : (4*c)/q ≤ 0 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*1))
    have u3 : (3*c)/q ≤ 0 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*1))
    have u2 : (2*c)/q ≤ 0 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*1))
    have l8 : 1 ≤ (8*c)/q := by exact (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega
  · rcases h2 with ⟨hlo, hhi⟩
    have u4 : (4*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*2))
    have u3 : (3*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*2))
    have u2 : (2*c)/q ≤ 0 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*1))
    have l8 : 2 ≤ (8*c)/q := by exact (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega
  · rcases h3 with ⟨hlo, hhi⟩
    have u4 : (4*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*2))
    have u3 : (3*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*2))
    have u2 : (2*c)/q ≤ 0 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*1))
    have l8 : 3 ≤ (8*c)/q := by exact (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega
  · rcases h4 with ⟨hlo, hhi⟩
    have u4 : (4*c)/q ≤ 2 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*3))
    have u3 : (3*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*2))
    have u2 : (2*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*2))
    have l8 : 4 ≤ (8*c)/q := by exact (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega
  · rcases h5 with ⟨hlo, hhi⟩
    have u4 : (4*c)/q ≤ 2 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*3))
    have u3 : (3*c)/q ≤ 2 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*3))
    have u2 : (2*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*2))
    have l8 : 5 ≤ (8*c)/q := by exact (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega
  · rcases h6 with ⟨hlo, hhi⟩
    have u4 : (4*c)/q ≤ 3 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*4))
    have u3 : (3*c)/q ≤ 2 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*3))
    have u2 : (2*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*2))
    have l8 : 6 ≤ (8*c)/q := by exact (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega
  · have u4 : (4*c)/q ≤ 3 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*4))
    have u3 : (3*c)/q ≤ 2 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*3))
    have u2 : (2*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*2))
    have l8 : 7 ≤ (8*c)/q := by exact (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega


lemma landau_nonneg (n q : ℕ) :
    (4*n)/q + (3*n)/q + (2*n)/q ≤ (8*n)/q + n/q := by
  by_cases hq0 : q = 0
  · simp [hq0]
  have hq : 0 < q := Nat.pos_of_ne_zero hq0
  have e1 : n / q = (n / q) + (n % q) / q := by
    have : n % q < q := Nat.mod_lt n hq
    rw [Nat.div_eq_of_lt this, add_zero]
  have e2 : (2*n)/q = 2*(n/q) + (2*(n%q))/q := by
    calc
      (2*n)/q = (2*(n % q + q * (n / q))) / q := by rw [Nat.mod_add_div]
      _ = 2*(n/q) + (2*(n%q))/q := mul_mod_add_div_div 2 n q hq
  have e3 : (3*n)/q = 3*(n/q) + (3*(n%q))/q := by
    calc
      (3*n)/q = (3*(n % q + q * (n / q))) / q := by rw [Nat.mod_add_div]
      _ = 3*(n/q) + (3*(n%q))/q := mul_mod_add_div_div 3 n q hq
  have e4 : (4*n)/q = 4*(n/q) + (4*(n%q))/q := by
    calc
      (4*n)/q = (4*(n % q + q * (n / q))) / q := by rw [Nat.mod_add_div]
      _ = 4*(n/q) + (4*(n%q))/q := mul_mod_add_div_div 4 n q hq
  have e8 : (8*n)/q = 8*(n/q) + (8*(n%q))/q := by
    calc
      (8*n)/q = (8*(n % q + q * (n / q))) / q := by rw [Nat.mod_add_div]
      _ = 8*(n/q) + (8*(n%q))/q := mul_mod_add_div_div 8 n q hq
  rw [e4, e3, e2, e8, e1]
  have hs := small_landau_remainder (n % q) q (Nat.mod_lt n hq)
  omega


lemma small_good_remainder (c q s : ℕ) (hc : c < q) (hq3 : 3*s < q)
    (hrem : 8*c = q * ((8*c)/q) + s) (hqodd : Odd q) (hsodd : Odd s) :
    (4*c)/q + (3*c)/q + (2*c)/q + 1 ≤ (8*c)/q := by
  have hq : 0 < q := by omega
  have htlt : (8*c)/q < 8 := by
    exact Nat.div_lt_of_lt_mul (by omega : 8*c < q*8)
  interval_cases (8*c)/q <;> try omega
  · rcases hqodd with ⟨u, hu⟩
    rcases hsodd with ⟨v, hv⟩
    omega
  · have u4 : (4*c)/q ≤ 0 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*1))
    have u3 : (3*c)/q ≤ 0 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*1))
    have u2 : (2*c)/q ≤ 0 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*1))
    omega
  · rcases hqodd with ⟨u, hu⟩
    rcases hsodd with ⟨v, hv⟩
    omega
  · have u4 : (4*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*2))
    have u3 : (3*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*2))
    have u2 : (2*c)/q ≤ 0 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*1))
    omega
  · rcases hqodd with ⟨u, hu⟩
    rcases hsodd with ⟨v, hv⟩
    omega
  · have u4 : (4*c)/q ≤ 2 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*3))
    have u3 : (3*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*2))
    have u2 : (2*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*2))
    omega
  · rcases hqodd with ⟨u, hu⟩
    rcases hsodd with ⟨v, hv⟩
    omega
  · have u4 : (4*c)/q ≤ 3 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 4*c < q*4))
    have u3 : (3*c)/q ≤ 2 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 3*c < q*3))
    have u2 : (2*c)/q ≤ 1 := by exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : 2*c < q*2))
    omega


lemma good_floor (n q s : ℕ) (hq : 0 < q) (hq3 : 3*s < q)
    (hrem : 8*(n%q) = q * ((8*(n%q))/q) + s) (hqodd : Odd q) (hsodd : Odd s) :
    (4*n)/q + (3*n)/q + (2*n)/q + 1 ≤ (8*n)/q + n/q := by
  have e1 : n / q = (n / q) + (n % q) / q := by
    have : n % q < q := Nat.mod_lt n hq
    rw [Nat.div_eq_of_lt this, add_zero]
  have e2 : (2*n)/q = 2*(n/q) + (2*(n%q))/q := by
    calc
      (2*n)/q = (2*(n % q + q * (n / q))) / q := by rw [Nat.mod_add_div]
      _ = 2*(n/q) + (2*(n%q))/q := mul_mod_add_div_div 2 n q hq
  have e3 : (3*n)/q = 3*(n/q) + (3*(n%q))/q := by
    calc
      (3*n)/q = (3*(n % q + q * (n / q))) / q := by rw [Nat.mod_add_div]
      _ = 3*(n/q) + (3*(n%q))/q := mul_mod_add_div_div 3 n q hq
  have e4 : (4*n)/q = 4*(n/q) + (4*(n%q))/q := by
    calc
      (4*n)/q = (4*(n % q + q * (n / q))) / q := by rw [Nat.mod_add_div]
      _ = 4*(n/q) + (4*(n%q))/q := mul_mod_add_div_div 4 n q hq
  have e8 : (8*n)/q = 8*(n/q) + (8*(n%q))/q := by
    calc
      (8*n)/q = (8*(n % q + q * (n / q))) / q := by rw [Nat.mod_add_div]
      _ = 8*(n/q) + (8*(n%q))/q := mul_mod_add_div_div 8 n q hq
  rw [e4, e3, e2, e8, e1]
  have hs := small_good_remainder (n%q) q s (Nat.mod_lt n hq) hq3 hrem hqodd hsodd
  omega


lemma modEq_of_pow_dvd_abs_sub (q n s : ℕ)
    (h : q ∣ (((8*n : ℤ) - (s : ℤ)).natAbs)) : (8*n) ≡ s [MOD q] := by
  rw [Nat.modEq_iff_dvd]
  have hz : (q : ℤ) ∣ ((8*n : ℤ) - (s : ℤ)) := (Int.natCast_dvd).2 h
  have hz' : (q : ℤ) ∣ ((s : ℤ) - (8*n : ℤ)) := by
    convert (dvd_neg.mpr hz) using 1
    ring
  simpa using hz'

lemma rem_eq_of_dvd_abs_sub (q n s : ℕ) (hq : 0 < q) (hslt : s < q)
    (h : q ∣ (((8*n : ℤ) - (s : ℤ)).natAbs)) :
    8*(n%q) = q * ((8*(n%q))/q) + s := by
  have h₁ : (8 * (n % q)) ≡ 8*n [MOD q] := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using (Nat.ModEq.mul_left 8 (Nat.mod_modEq n q))
  have h₂ : (8*n) ≡ s [MOD q] := modEq_of_pow_dvd_abs_sub q n s h
  have hmod : (8*(n%q)) % q = s := by
    apply Nat.ModEq.eq_of_lt_of_lt
    · exact (Nat.mod_modEq (8*(n%q)) q).trans (h₁.trans h₂)
    · exact Nat.mod_lt _ hq
    · exact hslt
  conv_lhs => rw [← Nat.mod_add_div (8*(n%q)) q]
  rw [hmod]
  omega






def numN (n : ℕ) : ℕ := (8*n).factorial * n.factorial

def denN (n : ℕ) : ℕ := (4*n).factorial * (3*n).factorial * (2*n).factorial

lemma denN_ne_zero (n : ℕ) : denN n ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (Nat.factorial_pos (4*n)).ne' (Nat.factorial_pos (3*n)).ne')
    (Nat.factorial_pos (2*n)).ne'

lemma numN_ne_zero (n : ℕ) : numN n ≠ 0 := by
  exact mul_ne_zero (Nat.factorial_pos (8*n)).ne' (Nat.factorial_pos n).ne'

lemma denN_dvd_numN (n : ℕ) : denN n ∣ numN n := by
  rw [← Nat.factorization_le_iff_dvd (denN_ne_zero n) (numN_ne_zero n)]
  rw [Finsupp.le_def]
  intro p
  by_cases hp : Nat.Prime p
  · let b := Nat.log p (8*n) + 1
    have hb8 : Nat.log p (8*n) < b := by dsimp [b]; omega
    have hb4 : Nat.log p (4*n) < b := by
      exact (Nat.log_mono_right (by omega : 4*n ≤ 8*n)).trans_lt hb8
    have hb3 : Nat.log p (3*n) < b := by
      exact (Nat.log_mono_right (by omega : 3*n ≤ 8*n)).trans_lt hb8
    have hb2 : Nat.log p (2*n) < b := by
      exact (Nat.log_mono_right (by omega : 2*n ≤ 8*n)).trans_lt hb8
    have hb1 : Nat.log p n < b := by
      exact (Nat.log_mono_right (by omega : n ≤ 8*n)).trans_lt hb8
    simp only [denN, numN]
    rw [Nat.factorization_mul (by positivity : (4*n).factorial * (3*n).factorial ≠ 0) (by positivity : (2*n).factorial ≠ 0)]
    rw [Nat.factorization_mul (by positivity : (4*n).factorial ≠ 0) (by positivity : (3*n).factorial ≠ 0)]
    rw [Nat.factorization_mul (by positivity : (8*n).factorial ≠ 0) (by positivity : n.factorial ≠ 0)]
    change ((4 * n).factorial).factorization p + ((3 * n).factorial).factorization p + ((2 * n).factorial).factorization p ≤
      ((8 * n).factorial).factorization p + (n.factorial).factorization p
    rw [Nat.factorization_factorial hp hb4, Nat.factorization_factorial hp hb3,
      Nat.factorization_factorial hp hb2, Nat.factorization_factorial hp hb8,
      Nat.factorization_factorial hp hb1]
    simpa [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm] using
      (Finset.sum_le_sum (by
        intro i hi
        exact landau_nonneg n (p^i)) :
        (∑ i ∈ Finset.Ico 1 b, ((4*n)/(p^i) + (3*n)/(p^i) + (2*n)/(p^i))) ≤
          ∑ i ∈ Finset.Ico 1 b, ((8*n)/(p^i) + n/(p^i)))
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]



lemma a_eq_num_div_den (n : ℕ) : a n = numN n / denN n := by
  simp [a, numN, denN, mul_assoc]

lemma a_mul_denN_eq_numN (n : ℕ) : a n * denN n = numN n := by
  rw [a_eq_num_div_den]
  exact Nat.div_mul_cancel (denN_dvd_numN n)

lemma a_ne_zero (n : ℕ) : a n ≠ 0 := by
  intro h
  have hmul : a n * denN n = 0 := by simp [h]
  rw [a_mul_denN_eq_numN] at hmul
  exact numN_ne_zero n hmul



lemma a_factorization_eq_sum (n p : ℕ) (hp : Nat.Prime p) :
    (a n).factorization p =
      ∑ i ∈ Finset.Ico 1 (Nat.log p (8*n) + 1),
        ((8*n)/(p^i) + n/(p^i) - ((4*n)/(p^i) + (3*n)/(p^i) + (2*n)/(p^i))) := by
  let b := Nat.log p (8*n) + 1
  have hb8 : Nat.log p (8*n) < b := by dsimp [b]; omega
  have hb4 : Nat.log p (4*n) < b := by
    exact (Nat.log_mono_right (by omega : 4*n ≤ 8*n)).trans_lt hb8
  have hb3 : Nat.log p (3*n) < b := by
    exact (Nat.log_mono_right (by omega : 3*n ≤ 8*n)).trans_lt hb8
  have hb2 : Nat.log p (2*n) < b := by
    exact (Nat.log_mono_right (by omega : 2*n ≤ 8*n)).trans_lt hb8
  have hb1 : Nat.log p n < b := by
    exact (Nat.log_mono_right (by omega : n ≤ 8*n)).trans_lt hb8
  have hdiv := Nat.factorization_div (denN_dvd_numN n)
  have h0 : (a n).factorization = (numN n).factorization - (denN n).factorization := by
    rw [a_eq_num_div_den]
    exact hdiv
  have hpoint := congrFun (congrArg DFunLike.coe h0) p
  rw [Finsupp.coe_tsub] at hpoint
  rw [hpoint]
  simp only [numN, denN]
  rw [Nat.factorization_mul (by positivity : (8*n).factorial ≠ 0) (by positivity : n.factorial ≠ 0)]
  rw [Nat.factorization_mul (by positivity : (4*n).factorial * (3*n).factorial ≠ 0) (by positivity : (2*n).factorial ≠ 0)]
  rw [Nat.factorization_mul (by positivity : (4*n).factorial ≠ 0) (by positivity : (3*n).factorial ≠ 0)]
  change (((8 * n).factorial).factorization p + (n.factorial).factorization p) -
      (((4 * n).factorial).factorization p + ((3 * n).factorial).factorization p + ((2 * n).factorial).factorization p) = _
  rw [Nat.factorization_factorial hp hb8, Nat.factorization_factorial hp hb1,
    Nat.factorization_factorial hp hb4, Nat.factorization_factorial hp hb3,
    Nat.factorization_factorial hp hb2]
  have hnonneg : ∀ i ∈ Finset.Ico 1 b,
      (4*n)/(p^i) + (3*n)/(p^i) + (2*n)/(p^i) ≤ (8*n)/(p^i) + n/(p^i) := by
    intro i hi
    exact landau_nonneg n (p^i)
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [← Finset.sum_tsub_distrib (s := Finset.Ico 1 b) hnonneg]


lemma card_le_sum_of_subset_one_le {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℕ}
    (hst : s ⊆ t) (hone : ∀ x ∈ s, 1 ≤ f x) : s.card ≤ ∑ x ∈ t, f x := by
  calc
    s.card = ∑ x ∈ s, (1 : ℕ) := Finset.card_eq_sum_ones s
    _ ≤ ∑ x ∈ s, f x := by exact Finset.sum_le_sum (by intro x hx; exact hone x hx)
    _ ≤ ∑ x ∈ t, f x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hst (by intro x hx hxs; exact Nat.zero_le _)

lemma Ioc_card_eq_sub (a b : ℕ) : (Finset.Ioc a b).card = b - a := by
  simpa using (Nat.card_Ioc a b)



def dTerm (n k : ℕ) : ℕ := (((8*n : ℤ) - (2*k+1 : ℤ)).natAbs)

lemma dTerm_ne_zero (n k : ℕ) : dTerm n k ≠ 0 := by
  unfold dTerm
  rw [Int.natAbs_ne_zero]
  intro h
  omega


lemma odd_dTerm (n k : ℕ) : Odd (dTerm n k) := by
  unfold dTerm
  rw [Int.natAbs_odd]
  apply Even.sub_odd
  · exact ⟨(4*n : ℤ), by ring⟩
  · exact ⟨(k : ℤ), by ring⟩

lemma odd_two_mul_add_one_nat (k : ℕ) : Odd (2*k+1) := ⟨k, by omega⟩

lemma pow_dvd_dTerm_of_le_factorization {n k p i : ℕ} (hp : p.Prime)
    (hi : i ≤ (dTerm n k).factorization p) : p^i ∣ dTerm n k := by
  exact (hp.pow_dvd_iff_le_factorization (dTerm_ne_zero n k)).2 hi

lemma not_pow_dvd_factorial_of_factorization_lt {m p i : ℕ} (hp : p.Prime)
    (hlt : m.factorial.factorization p < i) : ¬ p^i ∣ m.factorial := by
  intro h
  have := (hp.pow_dvd_iff_le_factorization (Nat.factorial_pos m).ne').1 h
  omega

lemma large_pow_gt_of_not_dvd_factorial {m p i : ℕ} (hp : p.Prime)
    (hnot : ¬ p^i ∣ m.factorial) (hi : 0 < i) : m < p^i := by
  by_contra hleNot
  have hle : p^i ≤ m := by omega
  have hpos : 0 < p^i := pow_pos hp.pos _
  exact hnot (Nat.dvd_factorial hpos hle)


lemma le_eight_mul_of_large_dvd_dTerm (n k q : ℕ) (hqpos : 0 < q)
    (hlarge : 2*k+1 < q) (hdvd : q ∣ dTerm n k) : q ≤ 8*n := by
  have hdpos : 0 < dTerm n k := Nat.pos_iff_ne_zero.mpr (dTerm_ne_zero n k)
  have hqle : q ≤ dTerm n k := Nat.le_of_dvd hdpos hdvd
  by_cases hle : 2*k+1 ≤ 8*n
  · have habs : dTerm n k = 8*n - (2*k+1) := by
      unfold dTerm
      exact Int.natAbs_natCast_sub_natCast_of_ge hle
    rw [habs] at hqle
    omega
  · have hlt : 8*n < 2*k+1 := by omega
    have habs : dTerm n k = (2*k+1) - 8*n := by
      unfold dTerm
      exact Int.natAbs_natCast_sub_natCast_of_le (Nat.le_of_lt hlt)
    rw [habs] at hqle
    omega



lemma large_exponent_contributes (n k p i : ℕ) (hp : p.Prime)
    (hgt : ((3*(2*k+1)).factorial).factorization p < i)
    (hle : i ≤ (dTerm n k).factorization p) :
    1 ≤ (8*n)/(p^i) + n/(p^i) - ((4*n)/(p^i) + (3*n)/(p^i) + (2*n)/(p^i)) := by
  have hi0 : 0 < i := by omega
  have hdvd : p^i ∣ dTerm n k := pow_dvd_dTerm_of_le_factorization hp hle
  have hnot : ¬ p^i ∣ (3*(2*k+1)).factorial :=
    not_pow_dvd_factorial_of_factorization_lt hp hgt
  have hlarge : 3*(2*k+1) < p^i := large_pow_gt_of_not_dvd_factorial hp hnot hi0
  have hqpos : 0 < p^i := pow_pos hp.pos _
  have hqodd : Odd (p^i) := Odd.of_dvd_nat (odd_dTerm n k) hdvd
  have hsodd : Odd (2*k+1) := odd_two_mul_add_one_nat k
  have hslt : 2*k+1 < p^i := by omega
  have hrem : 8*(n%(p^i)) = (p^i) * ((8*(n%(p^i)))/(p^i)) + (2*k+1) := by
    exact rem_eq_of_dvd_abs_sub (p^i) n (2*k+1) hqpos hslt hdvd
  have hg := good_floor n (p^i) (2*k+1) hqpos hlarge hrem hqodd hsodd
  omega




lemma large_prime_power_unique_k (r n p i k l : ℕ) (hp : p.Prime)
    (hk : k ∈ Finset.range r) (hl : l ∈ Finset.range r)
    (hlarge : 3*(2*r+1) < p^i)
    (hdk : p^i ∣ dTerm n k) (hdl : p^i ∣ dTerm n l) : k = l := by
  have hqpos : 0 < p^i := pow_pos hp.pos _
  have hz_k : (p^i : ℤ) ∣ ((8*n : ℤ) - (2*k+1 : ℤ)) := by
    unfold dTerm at hdk
    exact (Int.natCast_dvd).2 hdk
  have hz_l : (p^i : ℤ) ∣ ((8*n : ℤ) - (2*l+1 : ℤ)) := by
    unfold dTerm at hdl
    exact (Int.natCast_dvd).2 hdl
  have hdiffz : (p^i : ℤ) ∣ ((2*l+1 : ℤ) - (2*k+1 : ℤ)) := by
    have hsub := dvd_sub hz_k hz_l
    convert hsub using 1
    ring
  have hdiffnat : p^i ∣ (((2*l+1 : ℤ) - (2*k+1 : ℤ)).natAbs) := (Int.natCast_dvd).1 hdiffz
  by_cases hkl : k = l
  · exact hkl
  have hdiffpos : 0 < (((2*l+1 : ℤ) - (2*k+1 : ℤ)).natAbs) := by
    rw [Int.natAbs_pos]
    intro hzero
    have : k = l := by omega
    exact hkl this
  have hqle := Nat.le_of_dvd hdiffpos hdiffnat
  have hdiffsmall : (((2*l+1 : ℤ) - (2*k+1 : ℤ)).natAbs) < p^i := by
    rw [Finset.mem_range] at hk hl
    by_cases hle : k ≤ l
    · have habs : (((2*l+1 : ℤ) - (2*k+1 : ℤ)).natAbs) = (2*l+1) - (2*k+1) := by
        have hle' : 2*k+1 ≤ 2*l+1 := by omega
        exact Int.natAbs_natCast_sub_natCast_of_ge hle'
      rw [habs]
      omega
    · have hlt : l < k := by omega
      have habs : (((2*l+1 : ℤ) - (2*k+1 : ℤ)).natAbs) = (2*k+1) - (2*l+1) := by
        have hle' : 2*l+1 ≤ 2*k+1 := by omega
        exact Int.natAbs_natCast_sub_natCast_of_le hle'
      rw [habs]
      omega
  omega



lemma individual_factorization_bound (n k p : ℕ) (hp : p.Prime) :
    (dTerm n k).factorization p ≤ (a n).factorization p + ((3*(2*k+1)).factorial).factorization p := by
  let e := (dTerm n k).factorization p
  let t := ((3*(2*k+1)).factorial).factorization p
  by_cases het : e ≤ t
  · omega
  have hte : t < e := by omega
  let b := Nat.log p (8*n) + 1
  let f : ℕ → ℕ := fun i => (8*n)/(p^i) + n/(p^i) - ((4*n)/(p^i) + (3*n)/(p^i) + (2*n)/(p^i))
  have hsubset : Finset.Ioc t e ⊆ Finset.Ico 1 b := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    rw [Finset.mem_Ico]
    constructor
    · omega
    · have hdvd : p^i ∣ dTerm n k := by
        exact pow_dvd_dTerm_of_le_factorization hp (by dsimp [e] at hi; exact hi.2)
      have hnot : ¬ p^i ∣ (3*(2*k+1)).factorial := by
        apply not_pow_dvd_factorial_of_factorization_lt hp
        dsimp [t] at hi
        exact hi.1
      have hi0 : 0 < i := by omega
      have hlarge3 : 3*(2*k+1) < p^i := large_pow_gt_of_not_dvd_factorial hp hnot hi0
      have hlarge1 : 2*k+1 < p^i := by omega
      have hle8 : p^i ≤ 8*n := le_eight_mul_of_large_dvd_dTerm n k (p^i) (pow_pos hp.pos _) hlarge1 hdvd
      have hlelog : i ≤ Nat.log p (8*n) := Nat.le_log_of_pow_le hp.one_lt hle8
      dsimp [b]
      omega
  have hone : ∀ i ∈ Finset.Ioc t e, 1 ≤ f i := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    dsimp [f]
    apply large_exponent_contributes n k p i hp
    · dsimp [t] at hi
      exact hi.1
    · dsimp [e] at hi
      exact hi.2
  have hcardSum : (Finset.Ioc t e).card ≤ ∑ i ∈ Finset.Ico 1 b, f i :=
    card_le_sum_of_subset_one_le hsubset hone
  have hcard : (Finset.Ioc t e).card = e - t := by
    simpa using (Nat.card_Ioc t e)
  have hva : e - t ≤ (a n).factorization p := by
    rw [a_factorization_eq_sum n p hp]
    dsimp [b, f] at hcardSum ⊢
    simpa [hcard, b, f] using hcardSum
  omega

def DNat (n r : ℕ) : ℕ := ∏ k ∈ Finset.range r, dTerm n k

def Cfac (r : ℕ) : ℕ := (3*(2*r+1)).factorial

def KBig (r : ℕ) : ℕ := (Cfac r)^r

lemma DNat_ne_zero (n r : ℕ) : DNat n r ≠ 0 := by
  unfold DNat
  exact Finset.prod_ne_zero_iff.2 (by intro k hk; exact dTerm_ne_zero n k)

lemma Cfac_ne_zero (r : ℕ) : Cfac r ≠ 0 := by unfold Cfac; exact (Nat.factorial_pos _).ne'

lemma KBig_ne_zero (r : ℕ) : KBig r ≠ 0 := by unfold KBig; exact pow_ne_zero _ (Cfac_ne_zero r)

lemma factorization_DNat (n r p : ℕ) :
    (DNat n r).factorization p = ∑ k ∈ Finset.range r, (dTerm n k).factorization p := by
  unfold DNat
  rw [Nat.factorization_prod]
  · simp
  · intro k hk
    exact dTerm_ne_zero n k

lemma factorization_KBig (r p : ℕ) : (KBig r).factorization p = r * (Cfac r).factorization p := by
  unfold KBig
  rw [Nat.factorization_pow]
  rfl

lemma factorization_Cfac_eq_factorial (r p : ℕ) : (Cfac r).factorization p = ((3*(2*r+1)).factorial).factorization p := rfl

lemma small_factorization_le_Cfac {r k p : ℕ} (hk : k ∈ Finset.range r) :
    ((3*(2*k+1)).factorial).factorization p ≤ (Cfac r).factorization p := by
  unfold Cfac
  have hle : 3*(2*k+1) ≤ 3*(2*r+1) := by
    rw [Finset.mem_range] at hk
    omega
  exact (Nat.factorization_le_iff_dvd (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne').2
    (Nat.factorial_dvd_factorial hle) p

lemma product_factorization_bound (n r p : ℕ) (hp : p.Prime) :
    (DNat n r).factorization p ≤ (a n).factorization p + (KBig r).factorization p := by
  let t := (Cfac r).factorization p
  let e : ℕ → ℕ := fun k => (dTerm n k).factorization p
  let b := Nat.log p (8*n) + 1
  let f : ℕ → ℕ := fun i => (8*n)/(p^i) + n/(p^i) - ((4*n)/(p^i) + (3*n)/(p^i) + (2*n)/(p^i))
  let S : Finset (Sigma fun _ : ℕ => ℕ) := (Finset.range r).sigma (fun k => Finset.Ioc t (e k))
  let im : Finset ℕ := S.image (fun x => x.2)
  have hinj : Set.InjOn (fun x : Sigma fun _ : ℕ => ℕ => x.2) (S : Set (Sigma fun _ : ℕ => ℕ)) := by
    intro x hx y hy hxy
    rcases x with ⟨k,i⟩
    rcases y with ⟨l,j⟩
    simp only at hxy
    subst j
    change (⟨k, i⟩ : Sigma fun _ : ℕ => ℕ) ∈ S at hx
    change (⟨l, i⟩ : Sigma fun _ : ℕ => ℕ) ∈ S at hy
    rw [Finset.mem_sigma] at hx hy
    rcases hx with ⟨hk, hi⟩
    rcases hy with ⟨hl, hj⟩
    change i ∈ Finset.Ioc t (e k) at hi
    change i ∈ Finset.Ioc t (e l) at hj

    rw [Finset.mem_Ioc] at hi hj
    have hdvdk : p^i ∣ dTerm n k := pow_dvd_dTerm_of_le_factorization hp (by dsimp [e] at hi; exact hi.2)
    have hdvdl : p^i ∣ dTerm n l := pow_dvd_dTerm_of_le_factorization hp (by dsimp [e] at hj; exact hj.2)
    have hnot : ¬ p^i ∣ (Cfac r) := not_pow_dvd_factorial_of_factorization_lt hp (by dsimp [t] at hi; exact hi.1)
    have hi0 : 0 < i := by omega
    have hlarge : 3*(2*r+1) < p^i := by
      unfold Cfac at hnot
      exact large_pow_gt_of_not_dvd_factorial hp hnot hi0
    have hkl : k = l := large_prime_power_unique_k r n p i k l hp hk hl hlarge hdvdk hdvdl
    subst l
    rfl
  have hcard_image : im.card = S.card := by
    dsimp [im]
    exact Finset.card_image_of_injOn hinj
  have him_subset : im ⊆ Finset.Ico 1 b := by
    intro i hi
    rw [Finset.mem_image] at hi
    rcases hi with ⟨⟨k,j⟩, hxS, hji⟩
    simp only at hji
    subst i
    change (⟨k, j⟩ : Sigma fun _ : ℕ => ℕ) ∈ S at hxS
    rw [Finset.mem_sigma] at hxS
    rcases hxS with ⟨hk, hi⟩
    change j ∈ Finset.Ioc t (e k) at hi
    rw [Finset.mem_Ioc] at hi
    rw [Finset.mem_Ico]
    constructor
    · omega
    · have hdvd : p^j ∣ dTerm n k := pow_dvd_dTerm_of_le_factorization hp (by dsimp [e] at hi; exact hi.2)
      have hnot : ¬ p^j ∣ (Cfac r) := not_pow_dvd_factorial_of_factorization_lt hp (by dsimp [t] at hi; exact hi.1)
      have hj0 : 0 < j := by omega
      have hlargeC : 3*(2*r+1) < p^j := by
        unfold Cfac at hnot
        exact large_pow_gt_of_not_dvd_factorial hp hnot hj0
      have hklt : k < r := by simpa [Finset.mem_range] using hk
      have hslt : 2*k+1 < p^j := by omega
      have hle8 : p^j ≤ 8*n := le_eight_mul_of_large_dvd_dTerm n k (p^j) (pow_pos hp.pos _) hslt hdvd
      have hlelog : j ≤ Nat.log p (8*n) := Nat.le_log_of_pow_le hp.one_lt hle8
      dsimp [b]
      omega
  have him_one : ∀ i ∈ im, 1 ≤ f i := by
    intro i hi
    rw [Finset.mem_image] at hi
    rcases hi with ⟨⟨k,j⟩, hxS, hji⟩
    simp only at hji
    subst i
    change (⟨k, j⟩ : Sigma fun _ : ℕ => ℕ) ∈ S at hxS
    rw [Finset.mem_sigma] at hxS
    rcases hxS with ⟨hk, hi⟩
    change j ∈ Finset.Ioc t (e k) at hi
    rw [Finset.mem_Ioc] at hi
    dsimp [f]
    apply large_exponent_contributes n k p j hp
    · have hsmall := small_factorization_le_Cfac (r := r) (k := k) (p := p) hk
      dsimp [t] at hi
      omega
    · dsimp [e] at hi
      exact hi.2
  have hcard_le_sum : S.card ≤ ∑ i ∈ Finset.Ico 1 b, f i := by
    rw [← hcard_image]
    exact card_le_sum_of_subset_one_le him_subset him_one
  have hcardS : S.card = ∑ k ∈ Finset.range r, (e k - t) := by
    dsimp [S]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro k hk
    simpa [e] using (Nat.card_Ioc t (e k))
  have hsum_e : (∑ k ∈ Finset.range r, e k) ≤ r * t + S.card := by
    rw [hcardS]
    calc
      (∑ k ∈ Finset.range r, e k) ≤ ∑ k ∈ Finset.range r, (t + (e k - t)) := by
        apply Finset.sum_le_sum
        intro k hk
        omega
      _ = (∑ k ∈ Finset.range r, t) + ∑ k ∈ Finset.range r, (e k - t) := by rw [Finset.sum_add_distrib]
      _ = r * t + ∑ k ∈ Finset.range r, (e k - t) := by simp [Finset.sum_const, nsmul_eq_mul]
  dsimp [e, t] at hsum_e

  rw [factorization_DNat, factorization_KBig]
  have hva : S.card ≤ (a n).factorization p := by
    rw [a_factorization_eq_sum n p hp]
    dsimp [b, f] at hcard_le_sum ⊢
    simpa [b, f] using hcard_le_sum
  omega


lemma DNat_dvd_a_mul_KBig (n r : ℕ) : DNat n r ∣ a n * KBig r := by
  rw [← Nat.factorization_le_iff_dvd (DNat_ne_zero n r) (mul_ne_zero (a_ne_zero n) (KBig_ne_zero r))]
  rw [Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (a_ne_zero n) (KBig_ne_zero r)]
    exact product_factorization_bound n r p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma denominator_product_natAbs_eq_DNat (n r : ℕ) : (denominator_product n r).natAbs = DNat n r := by
  rw [denominator_product_natAbs_finset]
  rfl

lemma int_dvd_from_natAbs {z : ℤ} {m : ℕ} (h : z.natAbs ∣ m) : z ∣ (m : ℤ) := by
  rw [← Int.natAbs_dvd_natAbs]
  simpa using h

lemma denominator_product_dvd_int_KBig (n r : ℕ) :
    denominator_product n r ∣ (a n : ℤ) * (KBig r : ℤ) := by
  have hnat : (denominator_product n r).natAbs ∣ a n * KBig r := by
    rw [denominator_product_natAbs_eq_DNat]
    exact DNat_dvd_a_mul_KBig n r
  have hint : denominator_product n r ∣ ((a n * KBig r : ℕ) : ℤ) := int_dvd_from_natAbs hnat
  simpa using hint

lemma KBig_pos (r : ℕ) : 0 < (KBig r : ℤ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (KBig_ne_zero r)

theorem oeis_211420_conjecture_1_work : ∀ r : ℕ, ∃ K : ℤ, K > 0 ∧ ∀ n : ℕ,
    denominator_product n r ∣ (a n : ℤ) * K := by
  intro r
  refine ⟨(KBig r : ℤ), KBig_pos r, ?_⟩
  intro n
  exact denominator_product_dvd_int_KBig n r





