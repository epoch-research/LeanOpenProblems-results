import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A091669: $a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it as a function $\mathbb{N} \to \mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator

namespace A091669

/-- The numerator `2^(m-1) * ∏_{k=1}^{m-1} (2^k - 1)`. -/
def N (m : ℕ) : ℕ := 2 ^ (m - 1) * ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)

lemma a_eq (m : ℕ) (hm : m ≠ 0) : a m = N m / m ! := by
  simp [a, hm, N, Nat.pred_eq_sub_one]

lemma prod_pos (m : ℕ) : 0 < ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) := by
  apply Finset.prod_pos
  intro k hk
  have h1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h1
  omega

lemma N_pos (m : ℕ) : 0 < N m := Nat.mul_pos (by positivity) (prod_pos m)

lemma fermat (q : ℕ) (hq : q.Prime) (hodd : Odd q) : q ∣ 2 ^ (q - 1) - 1 := by
  have hq2 : q ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hodd
    omega
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hq] at h
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h.symm

lemma lte_lite (q : ℕ) (hq : q.Prime) (hodd : Odd q) (j : ℕ) (hj : j ≠ 0) :
    q ^ (padicValNat q j + 1) ∣ 2 ^ ((q - 1) * j) - 1 := by
  haveI := Fact.mk hq
  obtain ⟨v, j', hj', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj q hq.ne_one
  have hj'0 : j' ≠ 0 := by rintro rfl; exact hj' (dvd_zero q)
  have hv : padicValNat q (q ^ v * j') = v := by
    rw [padicValNat.mul (pow_ne_zero _ hq.ne_zero) hj'0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hj', add_zero]
  rw [hv]
  have h1 : q ^ (v + 1) ∣ 2 ^ ((q - 1) * q ^ v) - 1 := by
    have h0 := fermat q hq hodd
    have h2 : ((q : ℤ)) ∣ (2 : ℤ) ^ (q - 1) - 1 := by
      have := Int.natCast_dvd_natCast.mpr h0
      push_cast [Nat.one_le_two_pow] at this
      exact this
    have h3 := dvd_sub_pow_of_dvd_sub h2 v
    rw [one_pow, ← pow_mul] at h3
    have h4 : ((q ^ (v + 1) : ℕ) : ℤ) ∣ ((2 ^ ((q - 1) * q ^ v) - 1 : ℕ) : ℤ) := by
      push_cast [Nat.one_le_two_pow]
      exact h3
    exact Int.natCast_dvd_natCast.mp h4
  calc q ^ (v + 1) ∣ 2 ^ ((q - 1) * q ^ v) - 1 := h1
    _ ∣ (2 ^ ((q - 1) * q ^ v)) ^ j' - 1 ^ j' := Nat.sub_dvd_pow_sub_pow _ _ _
    _ = 2 ^ ((q - 1) * (q ^ v * j')) - 1 := by rw [one_pow, ← pow_mul, mul_assoc]

lemma pow_mul_fact_dvd (q : ℕ) (hq : q.Prime) (hodd : Odd q) (t : ℕ) :
    q ^ (t + padicValNat q t !) ∣ ∏ j ∈ Finset.Icc 1 t, (2 ^ ((q - 1) * j) - 1) := by
  haveI := Fact.mk hq
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero t)]
    have := lte_lite q hq hodd (t + 1) (by omega)
    calc q ^ (t + 1 + (padicValNat q (t + 1) + padicValNat q t !))
        = q ^ (t + padicValNat q t !) * q ^ (padicValNat q (t + 1) + 1) := by ring
      _ ∣ _ := mul_dvd_mul ih this

lemma sub_prod_dvd (q t m : ℕ) (hq : 2 ≤ q) (h : (q - 1) * t < m) :
    ∏ j ∈ Finset.Icc 1 t, (2 ^ ((q - 1) * j) - 1) ∣ ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) := by
  have hinj : ∀ x ∈ Finset.Icc 1 t, ∀ y ∈ Finset.Icc 1 t, (q - 1) * x = (q - 1) * y → x = y := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  have := Finset.prod_image (s := Finset.Icc 1 t) (g := fun j => (q - 1) * j)
    (f := fun k => 2 ^ k - 1) hinj
  simp only at this
  rw [← this]
  apply Finset.prod_dvd_prod_of_subset
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  rw [Finset.mem_Icc] at hj
  rw [Finset.mem_Ico]
  constructor
  · have : 1 ≤ q - 1 := by omega
    calc 1 = 1 * 1 := by norm_num
      _ ≤ (q - 1) * j := Nat.mul_le_mul this hj.1
  · calc (q - 1) * j ≤ (q - 1) * t := Nat.mul_le_mul_left _ hj.2
      _ < m := h

lemma padic_fact_mul_sub_one (q t : ℕ) [hq : Fact q.Prime] (ht : 1 ≤ t) :
    padicValNat q (q * t - 1)! = padicValNat q (t - 1)! + (t - 1) := by
  have hq2 := hq.out.two_le
  have : q * t - 1 = q * (t - 1) + (q - 1) := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel, mul_add, mul_one]
    omega
  rw [this, padicValNat_factorial_mul_add (t - 1) (by omega), padicValNat_factorial_mul]

lemma padic_fact_mono (q u t : ℕ) [Fact q.Prime] (h : u ≤ t) :
    padicValNat q u ! ≤ padicValNat q t ! := by
  have := Nat.factorial_dvd_factorial h
  rw [← padicValNat_dvd_iff_le (Nat.factorial_ne_zero t)]
  exact pow_padicValNat_dvd.trans this

lemma fact_dvd_N (m : ℕ) (hm : m ≠ 0) : m ! ∣ N m := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  haveI := Fact.mk hp
  rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero m)] at hpk
  rw [padicValNat_dvd_iff_le (N_pos m).ne']
  refine le_trans hpk ?_
  unfold N
  rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) (prod_pos m).ne']
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [padicValNat.prime_pow]
    have := padicValNat_factorial_lt_of_ne_zero 2 hm
    omega
  · have hp2 := hp.two_le
    have hu : padicValNat p m ! = padicValNat p (m / p)! + m / p := by
      have h0 : m = p * (m / p) + m % p := (Nat.div_add_mod m p).symm
      conv_lhs => rw [h0]
      rw [padicValNat_factorial_mul_add (m / p) (Nat.mod_lt _ (by omega)), padicValNat_factorial_mul]
    have hut : m / p ≤ (m - 1) / (p - 1) := by
      rcases Nat.eq_zero_or_pos (m / p) with h0 | hpos
      · rw [h0]; exact Nat.zero_le _
      · apply (Nat.le_div_iff_mul_le (by omega)).mpr
        have h1 : m / p * p ≤ m := Nat.div_mul_le_self m p
        have h2 : m / p * (p - 1) = m / p * p - m / p := by rw [Nat.mul_sub, mul_one]
        omega
    have hdvd : p ^ ((m - 1) / (p - 1) + padicValNat p ((m - 1) / (p - 1))!) ∣
        ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) := by
      refine (pow_mul_fact_dvd p hp hodd _).trans (sub_prod_dvd p _ m hp2 ?_)
      have : (p - 1) * ((m - 1) / (p - 1)) ≤ m - 1 := Nat.mul_div_le (m - 1) (p - 1)
      omega
    rw [padicValNat_dvd_iff_le (prod_pos m).ne'] at hdvd
    have hmono := padic_fact_mono p _ _ hut
    rw [hu]
    omega

lemma odd_prime_dvd_a (q t : ℕ) (hq : q.Prime) (hodd : Odd q) (ht : 2 ≤ t) :
    q ∣ a (q * t - 1) := by
  haveI := Fact.mk hq
  have hq2 := hq.two_le
  have hqt : 4 ≤ q * t := Nat.mul_le_mul hq2 ht
  have hsplit : (q - 1) * t + t = q * t := by
    calc (q - 1) * t + t = (q - 1 + 1) * t := by ring
      _ = q * t := by rw [Nat.sub_add_cancel (by omega)]
  set m := q * t - 1 with hm
  have hm0 : m ≠ 0 := by omega
  rw [a_eq m hm0]
  have hdiv := fact_dvd_N m hm0
  have hN : N m / m ! * m ! = N m := Nat.div_mul_cancel hdiv
  have hNm : N m / m ! ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN
    exact (N_pos m).ne' hN.symm
  apply dvd_of_one_le_padicValNat
  have key : q ^ (padicValNat q m ! + 1) ∣ N m := by
    have h1 : q ^ (t + padicValNat q t !) ∣ ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) :=
      (pow_mul_fact_dvd q hq hodd t).trans (sub_prod_dvd q t m hq2 (by omega))
    have h2 : padicValNat q m ! = padicValNat q (t - 1)! + (t - 1) :=
      padic_fact_mul_sub_one q t (by omega)
    have h3 := padic_fact_mono q (t - 1) t (by omega)
    refine (pow_dvd_pow q ?_).trans (h1.trans (dvd_mul_left _ _))
    omega
  rw [← hN, padicValNat_dvd_iff_le (by rw [hN]; exact (N_pos m).ne'),
    padicValNat.mul hNm (Nat.factorial_ne_zero m)] at key
  omega

lemma v2_fact_two_pow_sub_one (e : ℕ) : padicValNat 2 (2 ^ e - 1)! + e = 2 ^ e - 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h : 2 ^ (e + 1) - 1 = 2 * (2 ^ e - 1) + 1 := by
      have := Nat.one_le_two_pow (n := e)
      rw [pow_succ]
      omega
    rw [h, padicValNat_factorial_mul_add (2 ^ e - 1) (by norm_num), padicValNat_factorial_mul]
    have := Nat.one_le_two_pow (n := e)
    omega

lemma prod_odd (m : ℕ) : padicValNat 2 (∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  rw [Prime.dvd_finset_prod_iff Nat.prime_two.prime]
  rintro ⟨k, hk, hdvd⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have h1 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h2 := Nat.dvd_sub h1 hdvd
  have h3 : 2 ^ k - (2 ^ k - 1) = 1 := by
    have := Nat.one_le_two_pow (n := k)
    omega
  rw [h3] at h2
  exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)

lemma two_pow_not_dvd (e : ℕ) (he : 2 ≤ e) : ¬ 2 ^ e ∣ a (2 ^ e - 1) + 2 ^ (2 ^ e - 2) := by
  intro h
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  set m := 2 ^ e - 1 with hm
  have hm0 : m ≠ 0 := by omega
  have hdiv := fact_dvd_N m hm0
  have hN : N m / m ! * m ! = N m := Nat.div_mul_cancel hdiv
  rw [a_eq m hm0] at h
  have he' : e ≤ 2 ^ e - 2 := by
    have h1 := Nat.lt_two_pow_self (n := e - 2)
    have h2 : 2 ^ e = 2 ^ (e - 2) * 4 := by
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel he]
    omega
  have h2 : 2 ^ e ∣ 2 ^ (2 ^ e - 2) := pow_dvd_pow 2 he'
  have h3 : 2 ^ e ∣ N m / m ! := (Nat.dvd_add_left h2).mp h
  have h5 : 2 ^ e * m ! ∣ N m := by
    rw [← hN]
    exact mul_dvd_mul_right h3 _
  have h6 : 2 ^ padicValNat 2 (2 ^ e * m !) ∣ N m := pow_padicValNat_dvd.trans h5
  rw [padicValNat_dvd_iff_le (N_pos m).ne', padicValNat.mul (by positivity) (Nat.factorial_ne_zero m),
    padicValNat.prime_pow] at h6
  unfold N at h6
  rw [padicValNat.mul (by positivity) (prod_pos m).ne', padicValNat.prime_pow, prod_odd] at h6
  have h8 := v2_fact_two_pow_sub_one e
  rw [← hm] at h8
  omega

lemma prime_case (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (h : p ∣ a (p - 1) + 2 ^ (p - 2)) :
    IsPrimitiveRoot (2 : ZMod p) (Nat.totient p) := by
  haveI := Fact.mk hp
  rw [Nat.totient_prime hp, IsPrimitiveRoot.iff_def]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  refine ⟨ZMod.pow_card_sub_one_eq_one h2ne, ?_⟩
  intro l hl
  have hpa : ¬ p ∣ a (p - 1) := by
    intro hpa
    have h1 : p ∣ 2 ^ (p - 2) := (Nat.dvd_add_right hpa).mp h
    have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h1)
    omega
  have hprod : ¬ p ∣ ∏ k ∈ Finset.Ico 1 (p - 1), (2 ^ k - 1) := by
    intro hd
    apply hpa
    have hm0 : p - 1 ≠ 0 := by omega
    have hdiv := fact_dvd_N (p - 1) hm0
    have hN : N (p - 1) / (p - 1)! * (p - 1)! = N (p - 1) := Nat.div_mul_cancel hdiv
    rw [a_eq _ hm0]
    have h1 : p ∣ N (p - 1) := by
      unfold N
      exact hd.trans (dvd_mul_left _ _)
    rw [← hN] at h1
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · exact h2
    · exact absurd ((Nat.Prime.dvd_factorial hp).mp h2) (by omega)
  set r := l % (p - 1) with hr
  have hl' : (2 : ZMod p) ^ r = 1 := by
    have h0 : l = (p - 1) * (l / (p - 1)) + r := (Nat.div_add_mod l (p - 1)).symm
    rw [h0, pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one h2ne, one_pow, one_mul] at hl
    exact hl
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · exact Nat.dvd_of_mod_eq_zero hr0
  · exfalso
    apply hprod
    have hrlt : r < p - 1 := Nat.mod_lt _ (by omega)
    have hmem : r ∈ Finset.Ico 1 (p - 1) := Finset.mem_Ico.mpr ⟨hrpos, hrlt⟩
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
    have : ((2 ^ r - 1 : ℕ) : ZMod p) = 0 := by
      push_cast [Nat.one_le_two_pow]
      rw [hl', sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).mp this

end A091669

-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro h
  have hprime : n.Prime := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨e, rfl⟩ | ⟨q, hq, hqn, hodd⟩
    · exfalso
      have he : 2 ≤ e := by
        by_contra h'
        push_neg at h'
        interval_cases e <;> simp at hn
      exact A091669.two_pow_not_dvd e he h
    · obtain ⟨t, rfl⟩ := hqn
      rcases Nat.lt_or_ge t 2 with ht | ht
      · interval_cases t
        · simp at hn
        · simpa using hq
      · exfalso
        have h1 := A091669.odd_prime_dvd_a q t hq hodd ht
        have h' : q ∣ a (q * t - 1) + 2 ^ (q * t - 2) := (dvd_mul_right q t).trans h
        have h2 : q ∣ 2 ^ (q * t - 2) := (Nat.dvd_add_right h1).mp h'
        have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h2)
        rw [Nat.odd_iff] at hodd
        have := hq.two_le
        omega
  exact ⟨hprime, A091669.prime_case n hprime hn h⟩

theorem a091669_conjecture_primitive_root.disproof : ¬ (type_of% @a091669_conjecture_primitive_root) := sorry
