import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma div_add_div_le (a b m : ℕ) : a/m + b/m ≤ (a+b)/m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · rw [Nat.le_div_iff_mul_le h, add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self a m) (Nat.div_mul_le_self b m)

lemma div_add_le (a b m : ℕ) (hm : 0 < m) : (a+b)/m ≤ a/m + b/m + 1 := by
  have ha := Nat.div_add_mod a m; have hb := Nat.div_add_mod b m
  have ha' := Nat.mod_lt a hm; have hb' := Nat.mod_lt b hm
  have : (a+b) < (a/m + b/m + 2) * m := by nlinarith [ha, hb, ha', hb']
  have := (Nat.div_lt_iff_lt_mul hm).2 this; omega

lemma landau_floor (n m : ℕ) (hm : 0 < m) :
    (5*n/m - 2*n/m + 2)/3 ≤ 6*n/m - 3*n/m - 2*n/m := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < m ∧ n = m*q+s :=
    ⟨n/m, n%m, Nat.mod_lt _ hm, by rw [Nat.div_add_mod]⟩
  have E : ∀ k : ℕ, k*(m*q+s)/m = k*q + (k*s)/m := by
    intro k; have h : k*(m*q+s) = m*(k*q) + k*s := by ring
    rw [h, Nat.mul_add_div hm]
  rw [E 2, E 3, E 5, E 6]
  have hs0 : s/m = 0 := Nat.div_eq_of_lt hs
  have box2 : 2*s/m < 2 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have box3 : 3*s/m < 3 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have box5 : 5*s/m < 5 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have box6 : 6*s/m < 6 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have mono23 : 2*s/m ≤ 3*s/m := Nat.div_le_div_right (by omega)
  have mono35 : 3*s/m ≤ 5*s/m := Nat.div_le_div_right (by omega)
  have mono56 : 5*s/m ≤ 6*s/m := Nat.div_le_div_right (by omega)
  have low5 : 2*s/m + 3*s/m ≤ 5*s/m := by
    have := div_add_div_le (2*s) (3*s) m; rwa [show 2*s+3*s=5*s by ring] at this
  have up5 : 5*s/m ≤ 2*s/m + 3*s/m + 1 := by
    have := div_add_le (2*s) (3*s) m hm; rwa [show 2*s+3*s=5*s by ring] at this
  have low6 : 3*s/m + 3*s/m ≤ 6*s/m := by
    have := div_add_div_le (3*s) (3*s) m; rwa [show 3*s+3*s=6*s by ring] at this
  have up6 : 6*s/m ≤ 3*s/m + 3*s/m + 1 := by
    have := div_add_le (3*s) (3*s) m hm; rwa [show 3*s+3*s=6*s by ring] at this
  have low6b : 2*s/m + 2*s/m + 2*s/m ≤ 6*s/m := by
    have t1 := div_add_div_le (2*s) (2*s) m
    have t2 := div_add_div_le (2*s+2*s) (2*s) m
    rw [show 2*s+2*s+2*s=6*s by ring] at t2; omega
  have up3 : 3*s/m ≤ 2*s/m + 1 := by
    have := div_add_le (2*s) s m hm; rw [show 2*s+s=3*s by ring, hs0] at this; omega
  have up6c : 6*s/m ≤ 5*s/m + 1 := by
    have := div_add_le (5*s) s m hm; rw [show 5*s+s=6*s by ring, hs0] at this; omega
  omega

lemma residue_count_le3 (a b c : ℕ) :
    #{x ∈ Ioc a b | x % 3 = c} ≤ (b - a + 2) / 3 := by
  rw [← Finset.card_range ((b - a + 2) / 3)]
  apply Finset.card_le_card_of_injOn (fun x => (x - 1 - a) / 3)
  · intro x hx; simp only [Finset.mem_coe, mem_filter, mem_Ioc, mem_range] at *; omega
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_filter, mem_Ioc] at hx hy
    simp only at hxy; omega

lemma bij_k_x (n m : ℕ) :
    #{k ∈ Icc 1 n | m ∣ 2*n+3*k}
      = #{x ∈ Ioc (2*n) (5*n) | m ∣ x ∧ x % 3 = (2*n) % 3} := by
  apply Finset.card_bij (fun k _ => 2*n+3*k)
  · intro k hk; rw [mem_filter, mem_Icc] at hk; rw [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hk.2, by omega⟩
  · intro a ha b hb h; rw [mem_filter, mem_Icc] at ha hb; omega
  · intro x hx; rw [mem_filter, mem_Ioc] at hx
    refine ⟨(x - 2*n)/3, ?_, by omega⟩
    rw [mem_filter, mem_Icc]; exact ⟨by omega, by
      have : 2*n+3*((x-2*n)/3) = x := by omega
      rw [this]; exact hx.2.1⟩

lemma mult_count_eq (n m c : ℕ) (hm : 0 < m) :
    #{x ∈ Ioc (2*n) (5*n) | m ∣ x ∧ x % 3 = c}
      = #{t ∈ Ioc (2*n/m) (5*n/m) | (m*t) % 3 = c} := by
  apply Finset.card_bij (fun x _ => x/m)
  · intro x hx
    rw [mem_filter, mem_Ioc] at hx ⊢
    obtain ⟨⟨h1, h2⟩, hd, h3⟩ := hx
    obtain ⟨w, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left w hm]
    refine ⟨⟨(Nat.div_lt_iff_lt_mul hm).2 (by nlinarith [h1]),
            (Nat.le_div_iff_mul_le hm).2 (by nlinarith [h2])⟩, h3⟩
  · intro a ha b hb h
    rw [mem_filter] at ha hb
    obtain ⟨wa, rfl⟩ := ha.2.1; obtain ⟨wb, rfl⟩ := hb.2.1
    rw [Nat.mul_div_cancel_left wa hm, Nat.mul_div_cancel_left wb hm] at h; rw [h]
  · intro t ht
    rw [mem_filter, mem_Ioc] at ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    refine ⟨m*t, ?_, Nat.mul_div_cancel_left t hm⟩
    rw [mem_filter, mem_Ioc]
    have l1 : 2*n < t*m := (Nat.div_lt_iff_lt_mul hm).1 h1
    have l2 : t*m ≤ 5*n := (Nat.le_div_iff_mul_le hm).1 h2
    exact ⟨⟨by nlinarith [l1], by nlinarith [l2]⟩, ⟨t, rfl⟩, h3⟩

lemma count_mt_le (A B m c : ℕ) (hm3 : ¬ 3 ∣ m) (hc : c < 3) :
    #{t ∈ Ioc A B | (m*t) % 3 = c} ≤ (B - A + 2)/3 := by
  have hmod : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have key : ∃ r, {t ∈ Ioc A B | (m*t) % 3 = c} = {t ∈ Ioc A B | t % 3 = r} := by
    rcases hmod with h | h
    · exact ⟨c, Finset.filter_congr (fun t _ => by rw [Nat.mul_mod, h]; omega)⟩
    · refine ⟨(2*c) % 3, Finset.filter_congr (fun t _ => ?_)⟩
      rw [Nat.mul_mod, h]; have : t % 3 < 3 := Nat.mod_lt _ (by norm_num); omega
  obtain ⟨r, hr⟩ := key; rw [hr]; exact residue_count_le3 A B r

lemma term_count_bound (n m : ℕ) (hm : 0 < m) (hm3 : ¬ 3 ∣ m) :
    #{k ∈ Icc 1 n | m ∣ 2*n+3*k} ≤ 6*n/m - 3*n/m - 2*n/m := by
  rw [bij_k_x n m, mult_count_eq n m ((2*n)%3) hm]
  refine le_trans (count_mt_le _ _ m ((2*n)%3) hm3 (Nat.mod_lt _ (by norm_num))) ?_
  exact landau_floor n m hm

def Qseq (n : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 n, (2*n+3*k)

lemma Qseq_ne (n : ℕ) : Qseq n ≠ 0 := by
  unfold Qseq; apply Finset.prod_ne_zero_iff.2; intro k hk; rw [mem_Icc] at hk; omega

-- bound: for k in [1,n], 2n+3k < q^(6n+1) when q ≥ 2
lemma small_bound (n q k : ℕ) (hq : 2 ≤ q) (hk : k ∈ Icc 1 n) : 2*n+3*k < q^(6*n+1) := by
  rw [mem_Icc] at hk
  have h1 : 5*n < 2^(5*n+1) := by
    have : 5*n < 2^(5*n) := Nat.lt_two_pow_self; calc 5*n < 2^(5*n) := this
      _ ≤ 2^(5*n+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2^(6*n+1) ≤ q^(6*n+1) := Nat.pow_le_pow_left hq _
  have h3 : (2:ℕ)^(5*n+1) ≤ 2^(6*n+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma vq_Qseq_swap (n q : ℕ) (hq : q.Prime) :
    (Qseq n).factorization q
      = ∑ i ∈ Ico 1 (6*n+1), #{k ∈ Icc 1 n | q^i ∣ 2*n+3*k} := by
  have hq2 : 2 ≤ q := hq.two_le
  unfold Qseq
  rw [Nat.factorization_prod (by intro k hk; rw [mem_Icc] at hk; omega)]
  simp only [Finsupp.finset_sum_apply]
  have step : ∀ k ∈ Icc 1 n, (2*n+3*k).factorization q
      = ∑ i ∈ Ico 1 (6*n+1), (if q^i ∣ 2*n+3*k then 1 else 0) := by
    intro k hk
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hq (by rw [mem_Icc] at hk; omega)
          (small_bound n q k hq2 hk)]
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.card_filter]

lemma log_bound (q n : ℕ) (hq : 2 ≤ q) (K : ℕ) (hK : K ≤ 6*n) : Nat.log q K < 6*n+1 := by
  rcases Nat.eq_zero_or_pos K with h | h
  · simp [h]
  · have hb : K < q^(6*n+1) := by
      have h2 : 6*n < 2^(6*n) := Nat.lt_two_pow_self
      calc K ≤ 6*n := hK
        _ < 2^(6*n) := h2
        _ ≤ q^(6*n) := Nat.pow_le_pow_left hq _
        _ ≤ q^(6*n+1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.log_lt_of_lt_pow (by omega) hb

lemma vq_prime_bound (n q : ℕ) (hq : q.Prime) (hq3 : q ≠ 3) :
    (3*n)!.factorization q + (2*n)!.factorization q + (Qseq n).factorization q
      ≤ (6*n)!.factorization q := by
  have hq2 := hq.two_le
  have h3p : Nat.Prime 3 := by norm_num
  have h3nd : ∀ i, ¬ (3 ∣ q^i) := by
    intro i hd
    have hdq : (3:ℕ) ∣ q := h3p.dvd_of_dvd_pow hd
    have : (3:ℕ) = q := (Nat.prime_dvd_prime_iff_eq h3p hq).1 hdq
    omega
  rw [Nat.factorization_factorial hq (log_bound q n hq2 (6*n) (by omega)),
      Nat.factorization_factorial hq (log_bound q n hq2 (3*n) (by omega)),
      Nat.factorization_factorial hq (log_bound q n hq2 (2*n) (by omega)),
      vq_Qseq_swap n q hq]
  have key : ∀ i ∈ Ico 1 (6*n+1),
      #{k ∈ Icc 1 n | q^i ∣ 2*n+3*k} ≤ 6*n/q^i - 3*n/q^i - 2*n/q^i := by
    intro i _
    exact term_count_bound n (q^i) (pow_pos hq.pos i) (h3nd i)
  have hSQ : ∑ i ∈ Ico 1 (6*n+1), #{k ∈ Icc 1 n | q^i ∣ 2*n+3*k}
      ≤ ∑ i ∈ Ico 1 (6*n+1), (6*n/q^i - 3*n/q^i - 2*n/q^i) := Finset.sum_le_sum key
  have heq : ∑ i ∈ Ico 1 (6*n+1), 3*n/q^i + ∑ i ∈ Ico 1 (6*n+1), 2*n/q^i
      + ∑ i ∈ Ico 1 (6*n+1), (6*n/q^i - 3*n/q^i - 2*n/q^i)
      = ∑ i ∈ Ico 1 (6*n+1), 6*n/q^i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have hle : 3*n/q^i + 2*n/q^i ≤ 6*n/q^i := by
      have := div_add_div_le (3*n) (2*n) (q^i)
      have h56 : (5*n)/q^i ≤ (6*n)/q^i := Nat.div_le_div_right (by omega)
      rw [show 3*n+2*n=5*n by ring] at this; omega
    omega
  omega

lemma landau_floor3 (a m : ℕ) (hm : 0 < m) :
    9*a/m + 6*a/m + 5*a/m ≤ 18*a/m + 2*a/m := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < m ∧ a = m*q+s :=
    ⟨a/m, a%m, Nat.mod_lt _ hm, by rw [Nat.div_add_mod]⟩
  have E : ∀ k : ℕ, k*(m*q+s)/m = k*q + (k*s)/m := by
    intro k; have h : k*(m*q+s) = m*(k*q) + k*s := by ring
    rw [h, Nat.mul_add_div hm]
  rw [E 9, E 6, E 5, E 18, E 2]
  have hs0 : s/m = 0 := Nat.div_eq_of_lt hs
  have LA : ∀ i j k : ℕ, i + j = k → (i*s)/m + (j*s)/m ≤ (k*s)/m := by
    intro i j k h; have := div_add_div_le (i*s) (j*s) m
    rwa [show i*s+j*s=k*s by rw [← h]; ring] at this
  have UA : ∀ i j k : ℕ, i + j = k → (k*s)/m ≤ (i*s)/m + (j*s)/m + 1 := by
    intro i j k h; have := div_add_le (i*s) (j*s) m hm
    rwa [show i*s+j*s=k*s by rw [← h]; ring] at this
  have r1a := LA 9 9 18 rfl;  have r1b := UA 9 9 18 rfl
  have r2a1 := LA 6 6 12 rfl; have r2a2 := LA 12 6 18 rfl
  have r2b1 := UA 6 6 12 rfl; have r2b2 := UA 12 6 18 rfl
  have r3a1 := LA 5 5 10 rfl; have r3a2 := LA 10 5 15 rfl; have r3a3 := LA 15 3 18 rfl
  have r3b1 := UA 5 5 10 rfl; have r3b2 := UA 10 5 15 rfl; have r3b3 := UA 15 3 18 rfl
  have r4a := LA 3 3 6 rfl;   have r4b := UA 3 3 6 rfl
  have r5a := LA 2 1 3 rfl;   have r5b := UA 2 1 3 rfl
  have r6a := LA 2 3 5 rfl;   have r6b := UA 2 3 5 rfl
  have e1 : (1*s)/m = 0 := by rw [show 1*s=s by ring, hs0]
  have b2 : (2*s)/m < 2 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b3 : (3*s)/m < 3 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b5 : (5*s)/m < 5 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b6 : (6*s)/m < 6 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b9 : (9*s)/m < 9 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have d2a : 3*((6*s)/m) ≤ (18*s)/m := by omega
  have d2b : (18*s)/m ≤ 3*((6*s)/m) + 2 := by omega
  have d3a : 3*((5*s)/m) + (3*s)/m ≤ (18*s)/m := by omega
  have d3b : (18*s)/m ≤ 3*((5*s)/m) + (3*s)/m + 3 := by omega
  clear r2a1 r2a2 r2b1 r2b2 r3a1 r3a2 r3a3 r3b1 r3b2 r3b3 LA UA E
  set A1 := (1*s)/m
  set A2 := (2*s)/m
  set A3 := (3*s)/m
  set A5 := (5*s)/m
  set A6 := (6*s)/m
  set A9 := (9*s)/m
  set A18 := (18*s)/m
  clear_value A1 A2 A3 A5 A6 A9 A18
  omega

lemma prod_Icc_ascFactorial (a K : ℕ) :
    ∏ k ∈ Finset.Icc 1 K, (a + k) = (a+1).ascFactorial K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ K+1), ih, Nat.ascFactorial_succ]
    ring

lemma Qseq_three (n : ℕ) : Qseq (3*n) * (2*n)! = 3^(3*n) * (5*n)! := by
  have key : Qseq (3*n) = 3^(3*n) * (2*n+1).ascFactorial (3*n) := by
    unfold Qseq
    have h1 : ∀ k ∈ Finset.Icc 1 (3*n), 2*(3*n)+3*k = 3*(2*n+k) := by intro k _; ring
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const,
        prod_Icc_ascFactorial, Nat.card_Icc, show (3*n+1)-1 = 3*n from by omega]
  rw [key, mul_assoc, mul_comm ((2*n+1).ascFactorial (3*n)) ((2*n)!),
      Nat.factorial_mul_ascFactorial]
  congr 2
  omega

lemma vq3_B (n : ℕ) :
    (9*n)!.factorization 3 + (6*n)!.factorization 3 + (5*n)!.factorization 3
      ≤ (18*n)!.factorization 3 + (2*n)!.factorization 3 := by
  have h3 : Nat.Prime 3 := by norm_num
  have L : ∀ m : ℕ, m ≤ 18*n → Nat.log 3 m < 18*n+1 := by
    intro m hm; exact lt_of_le_of_lt (Nat.log_le_self 3 m) (by omega)
  rw [Nat.factorization_factorial h3 (L (9*n) (by omega)),
      Nat.factorization_factorial h3 (L (6*n) (by omega)),
      Nat.factorization_factorial h3 (L (5*n) (by omega)),
      Nat.factorization_factorial h3 (L (18*n) (by omega)),
      Nat.factorization_factorial h3 (L (2*n) (by omega))]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact landau_floor3 n (3^i) (pow_pos (by norm_num) i)

lemma vq3_bound (n : ℕ) :
    (3*n)!.factorization 3 + (2*n)!.factorization 3 + (Qseq n).factorization 3
      ≤ n + (6*n)!.factorization 3 := by
  have h3 : Nat.Prime 3 := by norm_num
  rcases Nat.eq_zero_or_pos (n % 3) with hmod | hmod
  · -- 3 ∣ n
    obtain ⟨n', rfl⟩ : ∃ n', n = 3*n' := ⟨n/3, by omega⟩
    -- Qseq (3n') * (2n')! = 3^(3n') * (5n')!
    have hQ := Qseq_three n'
    have hQne : Qseq (3*n') ≠ 0 := Qseq_ne _
    have hfac2 : ((2*n')! : ℕ) ≠ 0 := Nat.factorial_ne_zero _
    have hfac5 : ((5*n')! : ℕ) ≠ 0 := Nat.factorial_ne_zero _
    -- take factorization 3 of both sides
    have hval : (Qseq (3*n')).factorization 3 + (2*n')!.factorization 3
        = 3*n' + (5*n')!.factorization 3 := by
      have := congrArg (fun t => t.factorization 3) hQ
      simp only at this
      rw [Nat.factorization_mul hQne hfac2, Nat.factorization_mul (by positivity) hfac5,
          Nat.factorization_pow] at this
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at this
      rw [Nat.Prime.factorization_self h3] at this
      omega
    have hB := vq3_B n'
    -- goal in terms of 3*n'
    -- (3*(3n'))! = (9n')!, (2*(3n'))! = (6n')!, (6*(3n'))!=(18n')!
    have e9 : 3*(3*n') = 9*n' := by ring
    have e6 : 2*(3*n') = 6*n' := by ring
    have e18 : 6*(3*n') = 18*n' := by ring
    rw [e9, e6, e18]
    omega
  · -- 3 ∤ n : v3(Qseq n) = 0
    have hnd : ¬ (3 ∣ n) := by omega
    have hQ0 : (Qseq n).factorization 3 = 0 := by
      unfold Qseq
      rw [Nat.factorization_prod (fun k hk => by
            simp only [Finset.mem_Icc] at hk; omega), Finsupp.finset_sum_apply]
      apply Finset.sum_eq_zero
      intro k hk
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      have : (3:ℕ) ∣ 2*n := by omega
      omega
    -- (3n)!(2n)! divides (6n)! via multinomial
    have hdvd : (3*n)! * (2*n)! ∣ (6*n)! := by
      have h1 : (3*n)! * (2*n)! ∣ (3*n+2*n)! := Nat.factorial_mul_factorial_dvd_factorial_add _ _
      rw [show 3*n+2*n = 5*n from by ring] at h1
      exact h1.trans (Nat.factorial_dvd_factorial (by omega))
    have hle : (3*n)!.factorization 3 + (2*n)!.factorization 3 ≤ (6*n)!.factorization 3 := by
      have h6 : ((6*n)! : ℕ) ≠ 0 := Nat.factorial_ne_zero _
      have := (Nat.factorization_le_iff_dvd (by positivity) h6).2 hdvd 3
      rwa [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
          Finsupp.add_apply] at this
    omega

lemma integrality (n : ℕ) : (3*n)! * (2*n)! * Qseq n ∣ 3^n * (6*n)! := by
  have hL : ((3*n)! * (2*n)! * Qseq n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (Qseq_ne n)
  have hR : (3^n * (6*n)!) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.factorial_ne_zero _)
  apply (Nat.factorization_le_iff_dvd hL hR).mp
  rw [Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  · rw [Nat.factorization_mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (Qseq_ne n),
        Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (Nat.factorial_ne_zero _),
        Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hq3 : q = 3
    · subst hq3
      rw [Nat.Prime.factorization_self (by norm_num)]
      have := vq3_bound n
      omega
    · have h30 : (3:ℕ).factorization q = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hd
        exact hq3 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 hd)
      have := vq_prime_bound n q hq hq3
      rw [h30]; omega
  · rw [Nat.factorization_eq_zero_of_non_prime _ hq]
    exact Nat.zero_le _

noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

def aexact (n : ℕ) : ℕ := (3^n * (6*n)!) / ((3*n)! * (2*n)! * Qseq n)

lemma aexact_spec (n : ℕ) : ((3*n)! * (2*n)! * Qseq n) * aexact n = 3^n * (6*n)! :=
  Nat.mul_div_cancel' (integrality n)

lemma gamma_shift (x : ℝ) (hx : 0 < x) : ∀ k : ℕ,
    Real.Gamma (x + k) = Real.Gamma x * ∏ i ∈ Finset.range k, (x + i) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hxk : x + (k:ℝ) ≠ 0 := by
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      have : (0:ℝ) < x + (k:ℝ) := by linarith
      exact this.ne'
    rw [Finset.prod_range_succ]
    have hstep : Real.Gamma (x + (↑(k+1))) = (x + k) * Real.Gamma (x + k) := by
      rw [show x + (↑(k+1)) = (x + k) + 1 by push_cast; ring, Real.Gamma_add_one hxk]
    rw [hstep, ih]; ring

lemma hPQ (n : ℕ) :
    (3:ℝ)^n * ∏ i ∈ Finset.range n, (2/3*(n:ℝ)+1+(i:ℝ)) = (Qseq n : ℝ) := by
  have hcard : (3:ℝ)^n = ∏ i ∈ Finset.range n, (3:ℝ) := by
    rw [Finset.prod_const, Finset.card_range]
  have hcast : (Qseq n : ℝ) = ∏ i ∈ Finset.range n, (2*(n:ℝ)+3+3*(i:ℝ)) := by
    rw [Qseq]; push_cast
    rw [show Finset.Icc 1 n = Finset.Ico 1 (n+1) from by
          ext x; simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff],
        Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.prod_congr rfl; intro i _; push_cast; ring
  rw [hcard, ← Finset.prod_mul_distrib, hcast]
  apply Finset.prod_congr rfl; intro i _; ring

lemma val_eq (n : ℕ) :
    (Real.Gamma (6 * (n:ℝ) + 1) * Real.Gamma (2 / 3 * (n:ℝ) + 1)) /
    (Real.Gamma (3 * (n:ℝ) + 1) * Real.Gamma (2 * (n:ℝ) + 1) * Real.Gamma (5 / 3 * (n:ℝ) + 1))
    = (aexact n : ℝ) := by
  have hx : (0:ℝ) < 2 / 3 * (n:ℝ) + 1 := by positivity
  have hG : (0:ℝ) < Real.Gamma (2 / 3 * (n:ℝ) + 1) := Real.Gamma_pos_of_pos hx
  have hf3 : (0:ℝ) < ((3*n)! : ℝ) := by exact_mod_cast (3*n).factorial_pos
  have hf2 : (0:ℝ) < ((2*n)! : ℝ) := by exact_mod_cast (2*n).factorial_pos
  have hPpos : (0:ℝ) < ∏ i ∈ Finset.range n, (2/3*(n:ℝ)+1+(i:ℝ)) :=
    Finset.prod_pos (fun i _ => by positivity)
  have hshift : Real.Gamma (5 / 3 * (n:ℝ) + 1)
      = Real.Gamma (2/3*(n:ℝ)+1) * ∏ i ∈ Finset.range n, (2/3*(n:ℝ)+1+(i:ℝ)) := by
    have h := gamma_shift (2/3*(n:ℝ)+1) hx n
    rw [show (2/3*(n:ℝ)+1)+(n:ℝ) = 5/3*(n:ℝ)+1 by ring] at h
    exact h
  have haex : (aexact n : ℝ) = ↑(3^n*(6*n)!) / ↑((3*n)!*(2*n)!*Qseq n) := by
    rw [eq_div_iff (by exact_mod_cast (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _)
        (Nat.factorial_ne_zero _)) (Qseq_ne n)))]
    have hspec := congrArg (fun t : ℕ => (t : ℝ)) (aexact_spec n)
    push_cast
    push_cast at hspec
    linear_combination hspec
  rw [show (6:ℝ)*(n:ℝ)+1 = ((6*n:ℕ):ℝ)+1 by push_cast; ring,
      show (3:ℝ)*(n:ℝ)+1 = ((3*n:ℕ):ℝ)+1 by push_cast; ring,
      show (2:ℝ)*(n:ℝ)+1 = ((2*n:ℕ):ℝ)+1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      hshift, haex]
  rw [div_eq_div_iff
      (mul_ne_zero (mul_ne_zero hf3.ne' hf2.ne') (mul_ne_zero hG.ne' hPpos.ne'))
      (by exact_mod_cast (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _)
        (Nat.factorial_ne_zero _)) (Qseq_ne n)))]
  push_cast
  linear_combination (-(((6*n)! : ℝ) * ((3*n)! : ℝ) * ((2*n)! : ℝ)
    * Real.Gamma (2 / 3 * (n:ℝ) + 1))) * hPQ n

lemma a_eq (n : ℕ) : a n = aexact n := by
  show (round _).toNat = aexact n
  rw [val_eq n, round_natCast, Int.toNat_natCast]

-- SHARP core lemma (the hard Kazandzidis-type supercongruence)
lemma sharp (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hM : 0 < M) :
    aexact (M * p) ≡ aexact M [MOD p ^ (3 * (M.factorization p + 1))] := by
  sorry

theorem main (p n r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  rw [a_eq, a_eq]
  have hp0 : 0 < p := hp.pos
  set M := n * p ^ (r - 1) with hMdef
  have hMpos : 0 < M := by positivity
  have hMp : n * p ^ r = M * p := by
    rw [hMdef, mul_assoc, ← pow_succ]
    congr 2
    omega
  rw [hMp]
  have hv : r - 1 ≤ M.factorization p := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization hp (by positivity)]
    exact ⟨n, by rw [hMdef]; ring⟩
  refine Nat.ModEq.of_dvd ?_ (sharp p M hp hp5 hMpos)
  exact pow_dvd_pow p (by omega)
