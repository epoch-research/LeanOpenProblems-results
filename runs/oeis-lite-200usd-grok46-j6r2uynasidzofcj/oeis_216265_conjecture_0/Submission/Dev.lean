import FormalConjectures.Util.ProblemImports

open Nat Finset

/-! Clean development of elementary lemmas for A216265. -/

/-- The number of odd elements of `range n` is `n / 2`. -/
lemma card_filter_odd_range (n : ℕ) :
    ((range n).filter Odd).card = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_add_one, filter_insert]
    by_cases h : Odd n
    · rw [if_pos h, card_insert_of_notMem, ih]
      · have : n % 2 = 1 := Nat.odd_iff.mp h
        omega
      · simp [mem_filter]
    · rw [if_neg h, ih]
      have : n % 2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h)
      omega

/-- `π(n) ≤ (n + 1) / 2`. -/
lemma primeCounting_le_succ_div_two (n : ℕ) :
    primeCounting n ≤ (n + 1) / 2 := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> decide
  have heq : primeCounting n = ((range (n + 1)).filter Nat.Prime).card := by
    simp [primeCounting, primeCounting', Nat.count_eq_card_filter_range]
  rw [heq]
  have hsub :
      ((range (n + 1)).filter Nat.Prime) ⊆
        insert 2 (((range (n + 1)).filter Odd).erase 1) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    rcases hp.2.eq_two_or_odd' with h2 | hodd
    · simp [h2]
    · have hp1 : p ≠ 1 := hp.2.ne_one
      have : p ∈ (range (n + 1)).filter Odd := by
        simp [hp.1, hodd]
      simp [mem_erase, this, hp1]
  refine (card_le_card hsub).trans ?_
  have h2n : 2 ∉ ((range (n + 1)).filter Odd).erase 1 := by
    simp [mem_erase, mem_filter]
  rw [card_insert_of_notMem h2n]
  have h1 : 1 ∈ (range (n + 1)).filter Odd := by
    simp; omega
  have herase : (((range (n + 1)).filter Odd).erase 1).card + 1 =
      ((range (n + 1)).filter Odd).card := card_erase_add_one h1
  have hodd := card_filter_odd_range (n + 1)
  omega

lemma n_le_n3 (n : ℕ) (hn : 2 ≤ n) : n ≤ n ^ 3 := by
  calc
    n ≤ n * n := Nat.le_mul_of_pos_right n (by omega)
    _ = n ^ 2 := (pow_two n).symm
    _ ≤ n ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)

lemma descFactorial_eq_prod_Ioc {N K : ℕ} (h : K ≤ N) :
    N.descFactorial K = ∏ i ∈ Ioc (N - K) N, i := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hK : K ≤ N := Nat.le_of_succ_le h
    rw [descFactorial_succ, ih hK]
    have hinsert : Ioc (N - (K + 1)) N = insert (N - K) (Ioc (N - K) N) := by
      ext x
      simp only [mem_Ioc, mem_insert]
      constructor
      · intro ⟨hx1, hx2⟩; omega
      · intro hx
        rcases hx with rfl | ⟨_, _⟩ <;> omega
    have hnotin : N - K ∉ Ioc (N - K) N := by
      simp [mem_Ioc]
    rw [hinsert, prod_insert hnotin]

lemma choose_mul_factorial_eq_prod (n : ℕ) (hn : 2 ≤ n) :
    (n ^ 3).choose n * n.factorial = ∏ i ∈ Ioc (n ^ 3 - n) (n ^ 3), i := by
  have hle := n_le_n3 n hn
  rw [choose_eq_descFactorial_div_factorial]
  rw [Nat.div_mul_cancel (factorial_dvd_descFactorial _ _)]
  exact descFactorial_eq_prod_Ioc hle

lemma prod_Ioc_ge (n : ℕ) (hn : 2 ≤ n) :
    ∏ i ∈ Ioc (n ^ 3 - n) (n ^ 3), i ≥ (n ^ 3 - n + 1) ^ n := by
  have hcard : (Ioc (n ^ 3 - n) (n ^ 3)).card = n := by
    rw [Nat.card_Ioc]
    have := n_le_n3 n hn
    omega
  have hmin : ∀ i ∈ Ioc (n ^ 3 - n) (n ^ 3), n ^ 3 - n + 1 ≤ i := by
    intro i hi; simp at hi; omega
  calc
    ∏ i ∈ Ioc (n ^ 3 - n) (n ^ 3), i
        ≥ ∏ _i ∈ Ioc (n ^ 3 - n) (n ^ 3), (n ^ 3 - n + 1) :=
      prod_le_prod' (fun i hi => hmin i hi)
    _ = (n ^ 3 - n + 1) ^ (Ioc (n ^ 3 - n) (n ^ 3)).card := by simp
    _ = (n ^ 3 - n + 1) ^ n := by rw [hcard]

lemma choose_n3_n_ge (n : ℕ) (hn : 2 ≤ n) :
    (n ^ 3).choose n ≥ (n ^ 2 - 1) ^ n := by
  have hprod := choose_mul_factorial_eq_prod n hn
  have hge := prod_Ioc_ge n hn
  have hmul : (n ^ 3).choose n * n.factorial ≥ (n ^ 3 - n + 1) ^ n := by
    rwa [hprod]
  have hnfac : n.factorial ≤ n ^ n := factorial_le_pow n
  have h1 : (n ^ 3).choose n * n ^ n ≥ (n ^ 3 - n + 1) ^ n :=
    hmul.trans (Nat.mul_le_mul_left _ hnfac)
  have hmuln : n * (n ^ 2 - 1) = n ^ 3 - n := by
    have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n (by omega)
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_three, pow_two]
  have h2 : n * (n ^ 2 - 1) ≤ n ^ 3 - n + 1 := by
    rw [hmuln]; exact Nat.le_succ _
  have h3 : (n * (n ^ 2 - 1)) ^ n ≤ (n ^ 3 - n + 1) ^ n :=
    Nat.pow_le_pow_left h2 n
  have h4 : (n * (n ^ 2 - 1)) ^ n = n ^ n * (n ^ 2 - 1) ^ n := mul_pow _ _ n
  have h5 : n ^ n * (n ^ 2 - 1) ^ n ≤ (n ^ 3).choose n * n ^ n := by
    rw [← h4]; exact h3.trans h1
  have hnpos : 0 < n ^ n := Nat.pow_pos (by omega)
  have : n ^ n * (n ^ 2 - 1) ^ n ≤ n ^ n * (n ^ 3).choose n := by
    simpa [Nat.mul_comm] using h5
  exact Nat.le_of_mul_le_mul_left this hnpos



/-- `(n - 1) ^ 4 > n ^ 3` for `n ≥ 6`. -/
lemma pred_pow_four_gt_n_pow_three (n : ℕ) (hn : 6 ≤ n) : n ^ 3 < (n - 1) ^ 4 := by
  have h1 : 1 ≤ n := by omega
  zify [h1]
  have hm : (6 : ℤ) ≤ n := by exact_mod_cast hn
  have hexp : ((n : ℤ) - 1) ^ 4 = n ^ 4 - 4 * n ^ 3 + 6 * n ^ 2 - 4 * n + 1 := by ring
  have hdiff : ((n : ℤ) - 1) ^ 4 - n ^ 3 = n ^ 2 * (n - 2) * (n - 3) - 4 * n + 1 := by
    rw [hexp]; ring
  have hpos : (0 : ℤ) < n ^ 2 * (n - 2) * (n - 3) - 4 * n + 1 := by
    have ha : (n : ℤ) - 2 ≥ 4 := by nlinarith
    have hb : (n : ℤ) - 3 ≥ 3 := by nlinarith
    have hd : (n : ℤ) ^ 2 * (n - 2) ≥ 4 * n ^ 2 := by nlinarith
    have he : (n : ℤ) ^ 2 * (n - 2) * (n - 3) ≥ 4 * n ^ 2 * 3 := by nlinarith
    nlinarith
  linarith

/-- `(n - 1) ^ n > n ^ 3` for `n ≥ 14`. -/
lemma pred_pow_n_gt_n_pow_three (n : ℕ) (hn : 14 ≤ n) : n ^ 3 < (n - 1) ^ n := by
  have h4 : n ^ 3 < (n - 1) ^ 4 := pred_pow_four_gt_n_pow_three n (by omega)
  have hle : (n - 1) ^ 4 ≤ (n - 1) ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact h4.trans_le hle

/-- `(n ^ 2 - 1) ^ 2 ≥ n ^ 3 * (n - 1)` for `n ≥ 2`. -/
lemma sq_pred_sq_ge (n : ℕ) (hn : 2 ≤ n) :
    n ^ 3 * (n - 1) ≤ (n ^ 2 - 1) ^ 2 := by
  have h1 : 1 ≤ n := by omega
  have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n (by omega)
  zify [h1, hsq]
  nlinarith

/-- For `n ≥ 14`, `(n ^ 3) ^ ((n + 1) / 2) < (n ^ 2 - 1) ^ n`. -/
lemma pow_pred_sq_pow_gt (n : ℕ) (hn : 14 ≤ n) :
    (n ^ 3) ^ ((n + 1) / 2) < (n ^ 2 - 1) ^ n := by
  have hn2 : 2 ≤ n := by omega
  have hmain : (n ^ 3) ^ (n + 1) < (n ^ 2 - 1) ^ (2 * n) := by
    have hA := sq_pred_sq_ge n hn2
    have hB : (n ^ 3 * (n - 1)) ^ n ≤ ((n ^ 2 - 1) ^ 2) ^ n :=
      Nat.pow_le_pow_left hA n
    have hC : (n ^ 3 * (n - 1)) ^ n = (n ^ 3) ^ n * (n - 1) ^ n := mul_pow _ _ n
    have hD := pred_pow_n_gt_n_pow_three n hn
    have hE : (n ^ 3) ^ n * n ^ 3 < (n ^ 3) ^ n * (n - 1) ^ n :=
      Nat.mul_lt_mul_of_pos_left hD (by positivity)
    have hF : (n ^ 3) ^ n * n ^ 3 = (n ^ 3) ^ (n + 1) := (pow_succ _ _).symm
    have hG : (n ^ 2 - 1) ^ (2 * n) = ((n ^ 2 - 1) ^ 2) ^ n := by
      rw [← pow_mul, Nat.mul_comm]
    calc
      (n ^ 3) ^ (n + 1) = (n ^ 3) ^ n * n ^ 3 := hF.symm
      _ < (n ^ 3) ^ n * (n - 1) ^ n := hE
      _ = (n ^ 3 * (n - 1)) ^ n := hC.symm
      _ ≤ ((n ^ 2 - 1) ^ 2) ^ n := hB
      _ = (n ^ 2 - 1) ^ (2 * n) := hG.symm
  have hhalf : ((n + 1) / 2) * 2 ≤ n + 1 := by omega
  have hpow2 : ((n ^ 3) ^ ((n + 1) / 2)) ^ 2 ≤ (n ^ 3) ^ (n + 1) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by positivity) hhalf
  have : ((n ^ 3) ^ ((n + 1) / 2)) ^ 2 < ((n ^ 2 - 1) ^ n) ^ 2 := by
    calc
      ((n ^ 3) ^ ((n + 1) / 2)) ^ 2 ≤ (n ^ 3) ^ (n + 1) := hpow2
      _ < (n ^ 2 - 1) ^ (2 * n) := hmain
      _ = ((n ^ 2 - 1) ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  exact (Nat.pow_lt_pow_iff_left (by omega)).mp this

/-- If `C(n^3, n)` is `n`-smooth then it is `≤ (n^3) ^ π(n)`. -/
lemma choose_n3_le_of_smooth (n : ℕ) (hn : 2 ≤ n)
    (hs : ∀ p, p.Prime → p ∣ (n ^ 3).choose n → p ≤ n) :
    (n ^ 3).choose n ≤ (n ^ 3) ^ n.primeCounting := by
  have hle := n_le_n3 n hn
  have hpos : 0 < (n ^ 3).choose n := Nat.choose_pos hle
  have hn3pos : 0 < n ^ 3 := by omega
  classical
  let S := ((n ^ 3).choose n).primeFactors
  have hdecomp : (n ^ 3).choose n =
      ∏ p ∈ S, p ^ ((n ^ 3).choose n).factorization p :=
    (factorization_prod_pow_eq_self hpos.ne').symm
  rw [hdecomp]
  have hss : S ⊆ (range (n + 1)).filter Nat.Prime := by
    intro p hp
    have hpP : p.Prime := prime_of_mem_primeFactors hp
    have hdvd : p ∣ (n ^ 3).choose n := dvd_of_mem_primeFactors hp
    have hple : p ≤ n := hs p hpP hdvd
    simp [mem_filter, mem_range, hpP]
    omega
  have hpt : ∀ p ∈ S, p ^ ((n ^ 3).choose n).factorization p ≤ n ^ 3 :=
    fun p _ => pow_factorization_choose_le hn3pos
  have hprod : ∏ p ∈ S, p ^ ((n ^ 3).choose n).factorization p ≤
      ∏ _p ∈ S, n ^ 3 := prod_le_prod' hpt
  have hconst : ∏ _p ∈ S, n ^ 3 = (n ^ 3) ^ S.card := by simp
  have hcard : S.card ≤ n.primeCounting := by
    have : n.primeCounting = ((range (n + 1)).filter Nat.Prime).card := by
      simp [primeCounting, primeCounting', Nat.count_eq_card_filter_range]
    rw [this]
    exact card_le_card hss
  calc
    ∏ p ∈ S, p ^ ((n ^ 3).choose n).factorization p ≤ ∏ _p ∈ S, n ^ 3 := hprod
    _ = (n ^ 3) ^ S.card := hconst
    _ ≤ (n ^ 3) ^ n.primeCounting := Nat.pow_le_pow_right (by positivity) hcard

/-- There is a number in `(n^3 - n, n^3]` with a prime factor `> n`, for `n ≥ 14`. -/
lemma exists_large_prime_factor (n : ℕ) (hn : 14 ≤ n) :
    ∃ m p, n ^ 3 - n < m ∧ m ≤ n ^ 3 ∧ p.Prime ∧ p ∣ m ∧ n < p := by
  by_contra h
  push_neg at h
  have hn2 : 2 ≤ n := by omega
  have hsmooth : ∀ p, p.Prime → p ∣ (n ^ 3).choose n → p ≤ n := by
    intro p hp hdvd
    by_contra hgt
    push_neg at hgt
    have hprod := choose_mul_factorial_eq_prod n hn2
    have hdiv : p ∣ (n ^ 3).choose n * n.factorial := dvd_mul_of_dvd_left hdvd _
    rw [hprod] at hdiv
    rw [Prime.dvd_finset_prod_iff hp.prime] at hdiv
    obtain ⟨m, hm, hpm⟩ := hdiv
    simp only [mem_Ioc] at hm
    have := h m p hm.1 hm.2 hp hpm
    omega
  have hupper : (n ^ 3).choose n ≤ (n ^ 3) ^ ((n + 1) / 2) := by
    have := choose_n3_le_of_smooth n hn2 hsmooth
    have hπ := primeCounting_le_succ_div_two n
    exact this.trans (Nat.pow_le_pow_right (by positivity) hπ)
  have hlower := choose_n3_n_ge n hn2
  have hgt := pow_pred_sq_pow_gt n hn
  have : (n ^ 2 - 1) ^ n ≤ (n ^ 3) ^ ((n + 1) / 2) := hlower.trans hupper
  exact (this.trans_lt hgt).false


/-- If `q` is composite and `n`-rough then `q ≥ (n + 1) ^ 2`. -/
lemma composite_rough_ge_sq {n q : ℕ} (hqpos : 0 < q) (hqP : ¬ q.Prime)
    (hmin : n < q.minFac) : (n + 1) ^ 2 ≤ q := by
  have hsq : q.minFac ^ 2 ≤ q := minFac_sq_le_self hqpos hqP
  have hle : n + 1 ≤ q.minFac := Nat.succ_le_of_lt hmin
  exact (Nat.pow_le_pow_left hle 2).trans hsq

/-- A number in `(n^3 - n, n^3]` cannot be a product `p * q` with `p > n` and
`q` composite and `n`-rough. -/
lemma not_mul_of_prime_and_rough_composite {n m p q : ℕ} (hn : 2 ≤ n)
    (hm2 : m ≤ n ^ 3) (hp : p.Prime) (hpn : n < p) (hq : m = p * q)
    (hqpos : 0 < q) (hqP : ¬ q.Prime) (hq1 : 1 < q) (hmin : n < q.minFac) : False := by
  have hqge := composite_rough_ge_sq hqpos hqP hmin
  have hn2 : n ^ 2 < q := by
    have hlt : n ^ 2 < (n + 1) ^ 2 := Nat.pow_lt_pow_left (n.lt_succ_self) (by decide)
    exact hlt.trans_le hqge
  have hmul : n * n ^ 2 < p * q :=
    Nat.mul_lt_mul_of_lt_of_le' hpn hn2.le (Nat.pow_pos (by omega))
  have heq : n * n ^ 2 = n ^ 3 := by
    simp [pow_three, pow_two]
  have : n ^ 3 < p * q := heq ▸ hmul
  rw [hq] at hm2
  exact (not_le_of_gt this) hm2

/-- In the mixed case `m = p * q` with `p > n` and `q ≤ n`, one has `p ≥ n ^ 2 - 1`. -/
lemma mixed_prime_factor_large {n m p q : ℕ} (hn : 2 ≤ n) (hm1 : n ^ 3 - n < m)
    (hpn : n < p) (hq : m = p * q) (hqle : q ≤ n) : n ^ 2 - 1 ≤ p := by
  have hqpos : 0 < q := by
    have : 0 < p * q := by
      rw [← hq]
      have : n ^ 3 - n < n ^ 3 := Nat.sub_lt (by
        have : 0 < n ^ 3 := Nat.pow_pos (by omega)
        omega) (by omega)
      omega
    exact Nat.pos_of_mul_pos_left this
  have hdiv : p = m / q := by
    rw [hq, Nat.mul_div_cancel_left _ hqpos]
  have : n ^ 3 - n < p * q := by rwa [← hq]
  have h1 : n ^ 3 - n < p * n := lt_of_lt_of_le this (Nat.mul_le_mul_left p hqle)
  have h2 : n * (n ^ 2 - 1) = n ^ 3 - n := by
    have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n (by omega)
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_three, pow_two]
  have : n * (n ^ 2 - 1) < p * n := by
    rwa [h2]
  have hnpos : 0 < n := by omega
  exact Nat.le_of_mul_le_mul_left (Nat.succ_le_of_lt this) hnpos |>.trans_eq ?_
  -- wait, we have n*(n^2-1) < p*n so n^2-1 < p, so n^2-1 ≤ p-1? We need n^2-1 ≤ p
  -- n*(n^2-1) < p*n ⇒ n^2-1 < p since n>0. Then n^2-1 ≤ p-1 < p, so n^2-1 ≤ p. Yes.
  · omega


