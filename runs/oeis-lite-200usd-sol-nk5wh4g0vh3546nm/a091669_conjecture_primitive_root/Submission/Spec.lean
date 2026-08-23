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

private lemma a_eq_quotient {m : ℕ} (hm : m ≠ 0) :
    a m = (2 ^ (m - 1) * (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) / m.factorial := by
  simp [a, hm, Nat.pred_eq_sub_one]


private lemma odd_prime_dvd_fermat (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ 2 ^ (p - 1) - 1 := by
  have hnp : ¬ p ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime prime_two).mp h with h1 | h2
    · exact hp.ne_one h1
    · exact hp2 h2
  have hc : p.Coprime 2 := (hp.coprime_iff_not_dvd).2 hnp
  have hic : IsCoprime (2 : ℤ) (p : ℤ) := hc.symm.isCoprime
  have hm : (2 : ℤ) ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] :=
    Int.ModEq.pow_card_sub_one_eq_one hp hic
  have hd : (p : ℤ) ∣ (2 : ℤ) ^ (p - 1) - 1 := Int.ModEq.dvd hm.symm
  have hone : 1 ≤ 2 ^ (p - 1) := Nat.one_le_pow _ _ (by decide)
  have heq : ((2 ^ (p - 1) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (p - 1) - 1 := by
    rw [Nat.cast_sub hone]
    norm_num
  rw [← heq] at hd
  exact Int.natCast_dvd_natCast.mp hd

private lemma prime_pow_dvd_geom_prod (p K M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hbound : K * (p - 1) < M) :
    p ^ K ∣ (Finset.Ico 1 M).prod (fun i => 2 ^ i - 1) := by
  let r := p - 1
  let S : Finset ℕ := (Finset.range K).image (fun j => (j + 1) * r)
  have hr : 0 < r := by
    dsimp [r]
    have := hp.two_le
    omega
  have hinj : Function.Injective (fun j : ℕ => (j + 1) * r) := by
    intro x y hxy
    have : x + 1 = y + 1 := Nat.eq_of_mul_eq_mul_right hr hxy
    omega
  have hcard : S.card = K := by
    rw [show S = (Finset.range K).image (fun j => (j + 1) * r) by rfl,
      Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub : S ⊆ Finset.Ico 1 M := by
    intro i hi
    simp only [S, Finset.mem_image, Finset.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    simp only [Finset.mem_Ico]
    constructor
    · exact Nat.mul_pos (by omega) hr
    · calc
        (j + 1) * r ≤ K * r := Nat.mul_le_mul_right r (by omega)
        _ < M := hbound
  have hterm : ∀ i ∈ S, p ∣ 2 ^ i - 1 := by
    intro i hi
    simp only [S, Finset.mem_image, Finset.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have hdr : r ∣ (j + 1) * r := dvd_mul_left r (j + 1)
    exact (odd_prime_dvd_fermat p hp hp2).trans
      (by simpa [r] using (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hdr))
  calc
    p ^ K = ∏ _i ∈ S, p := by simp [hcard]
    _ ∣ ∏ i ∈ S, (2 ^ i - 1) := Finset.prod_dvd_prod_of_dvd _ _ hterm
    _ ∣ ∏ i ∈ Finset.Ico 1 M, (2 ^ i - 1) :=
      Finset.prod_dvd_prod_of_subset S (Finset.Ico 1 M) _ hsub

private lemma factorial_dvd_numerator (m : ℕ) :
    m.factorial ∣ 2 ^ (m - 1) * (Finset.Ico 1 m).prod (fun i => 2 ^ i - 1) := by
  by_cases hm : m = 0
  · subst m
    norm_num
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  letI : Fact p.Prime := ⟨hp⟩
  have hkval : k ≤ padicValNat p m.factorial :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero m)).mp hpk
  by_cases hp2 : p = 2
  · subst p
    have hvlt : padicValNat 2 m.factorial < m := by
      simpa using sub_one_mul_padicValNat_factorial_lt_of_ne_zero 2 hm
    have hk : k ≤ m - 1 := by omega
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hk) _
  · have hvlt : (p - 1) * padicValNat p m.factorial < m :=
      sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hm
    have hb : k * (p - 1) < m := by
      rw [mul_comm]
      exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hkval) hvlt
    exact dvd_mul_of_dvd_right (prime_pow_dvd_geom_prod p k m hp hp2 hb) _

private lemma prime_dvd_exact_quotient (m p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hbound : (padicValNat p m.factorial + 1) * (p - 1) < m) :
    p ∣ (2 ^ (m - 1) * (Finset.Ico 1 m).prod (fun i => 2 ^ i - 1)) / m.factorial := by
  letI : Fact p.Prime := ⟨hp⟩
  let N := 2 ^ (m - 1) * (Finset.Ico 1 m).prod (fun i => 2 ^ i - 1)
  have hd : m.factorial ∣ N := factorial_dvd_numerator m
  have hpow : p ^ (padicValNat p m.factorial + 1) ∣ N := by
    apply dvd_mul_of_dvd_right
    exact prime_pow_dvd_geom_prod p (padicValNat p m.factorial + 1) m hp hp2 hbound
  have hN : N ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (by decide))
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hip : 1 < 2 ^ i := one_lt_pow₀ (by decide) (by omega)
    omega
  have hvalN : padicValNat p m.factorial + 1 ≤ padicValNat p N :=
    (padicValNat_dvd_iff_le hN).mp hpow
  have hvalQ : 1 ≤ padicValNat p (N / m.factorial) := by
    rw [padicValNat.div_of_dvd hd]
    omega
  have hQ : N / m.factorial ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (by positivity) hd) (Nat.factorial_pos m)).ne'
  exact (dvd_iff_padicValNat_ne_zero hQ).mpr (by omega)

private lemma composite_prime_factor_bound (n p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hnpos : 0 < n) (hpn : p ∣ n) (hne : n ≠ p) :
    (padicValNat p (n - 1).factorial + 1) * (p - 1) < n - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq⟩ := hpn
  have hqpos : 0 < q := by
    by_contra h
    simp only [not_lt, nonpos_iff_eq_zero] at h
    subst q
    simp only [mul_zero] at hq
    exact hnpos.ne' hq
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    apply hne
    simpa using hq
  have hq2 : 2 ≤ q := by omega
  have hp_pos : 0 < p := hp.pos
  have hpq : p * q = p * (q - 1) + p := by
    calc
      p * q = p * ((q - 1) + 1) := by congr 1 <;> omega
      _ = p * (q - 1) + p := by rw [Nat.mul_add, mul_one]
  have hnform : n - 1 = p * (q - 1) + (p - 1) := by
    rw [hq, hpq]
    omega
  have hp_pred_lt : p - 1 < p := by omega
  have hvalform : padicValNat p (n - 1).factorial =
      (q - 1) + padicValNat p (q - 1).factorial := by
    rw [hnform, padicValNat_factorial_mul_add (q - 1) hp_pred_lt,
      padicValNat_factorial_mul, add_comm]
  have hsmall : (p - 1) * padicValNat p (q - 1).factorial < q - 1 :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  rw [hvalform, hq]
  have hp1 : 1 ≤ p := by omega
  have hpm : p - 1 + 1 = p := by omega
  have hqm : q - 1 + 1 = q := by omega
  have hpqpos : 0 < p * q := Nat.mul_pos hp_pos hqpos
  have hpqm : p * q - 1 + 1 = p * q := by omega
  nlinarith

private lemma padicValNat_two_factorial_pow_sub_one (t : ℕ) :
    padicValNat 2 (2 ^ t - 1).factorial = 2 ^ t - 1 - t := by
  letI : Fact (Nat.Prime 2) := ⟨prime_two⟩
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ']
      have hform : 2 ^ (t + 1) - 1 = 2 * (2 ^ t - 1) + 1 := by
        rw [hpow]
        have hp : 0 < 2 ^ t := pow_pos (by decide) _
        omega
      rw [hform, padicValNat_factorial_mul_add (2 ^ t - 1) (by decide : 1 < 2),
        padicValNat_factorial_mul, ih]
      have hlt : t < 2 ^ t := t.lt_two_pow_self
      omega

private lemma two_not_dvd_geom_prod (M : ℕ) :
    ¬ 2 ∣ (Finset.Ico 1 M).prod (fun i => 2 ^ i - 1) := by
  apply prime_two.prime.not_dvd_finset_prod
  intro i hi hdiv
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hpow : 2 ∣ 2 ^ i := dvd_pow_self 2 (by omega)
  apply prime_two.not_dvd_one
  rw [Nat.dvd_add_iff_right hdiv]
  convert hpow using 1
  have hpos : 0 < 2 ^ i := pow_pos (by decide) _
  omega

private lemma padicValNat_two_power_quotient (t : ℕ) (ht : 2 ≤ t) :
    padicValNat 2
      ((2 ^ ((2 ^ t - 1) - 1) *
          (Finset.Ico 1 (2 ^ t - 1)).prod (fun i => 2 ^ i - 1)) /
        (2 ^ t - 1).factorial) = t - 1 := by
  letI : Fact (Nat.Prime 2) := ⟨prime_two⟩
  let m := 2 ^ t - 1
  let P := (Finset.Ico 1 m).prod (fun i => 2 ^ i - 1)
  let N := 2 ^ (m - 1) * P
  have hP : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hip : 1 < 2 ^ i := one_lt_pow₀ (by decide) (by omega)
    omega
  have hPval : padicValNat 2 P = 0 :=
    padicValNat.eq_zero_of_not_dvd (two_not_dvd_geom_prod m)
  have hN : N ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide)) hP
  have hNval : padicValNat 2 N = m - 1 := by
    rw [padicValNat.mul (pow_ne_zero _ (by decide)) hP,
      padicValNat.pow (m - 1) (by decide : (2 : ℕ) ≠ 0), padicValNat_self, hPval]
    simp
  have hd : m.factorial ∣ N := factorial_dvd_numerator m
  rw [show 2 ^ t - 1 = m by rfl, show 2 ^ ((2 ^ t - 1) - 1) *
      (Finset.Ico 1 (2 ^ t - 1)).prod (fun i => 2 ^ i - 1) = N by rfl,
    padicValNat.div_of_dvd hd, hNval, show padicValNat 2 m.factorial = 2 ^ t - 1 - t by
      exact padicValNat_two_factorial_pow_sub_one t]
  dsimp [m]
  have hlt : t < 2 ^ t := t.lt_two_pow_self
  omega

private lemma prime_dvd_quotient_of_dvd_product (m p : ℕ) (hp : p.Prime) (hmp : m < p)
    (hprod : p ∣ (Finset.Ico 1 m).prod (fun i => 2 ^ i - 1)) :
    p ∣ (2 ^ (m - 1) * (Finset.Ico 1 m).prod (fun i => 2 ^ i - 1)) / m.factorial := by
  let N := 2 ^ (m - 1) * (Finset.Ico 1 m).prod (fun i => 2 ^ i - 1)
  have hd : m.factorial ∣ N := factorial_dvd_numerator m
  have hpN : p ∣ N := dvd_mul_of_dvd_right hprod _
  have heq : m.factorial * (N / m.factorial) = N := Nat.mul_div_cancel' hd
  rw [← heq] at hpN
  rcases hp.dvd_mul.mp hpN with hpf | hpq
  · exact False.elim ((Nat.not_le_of_gt hmp) (hp.dvd_factorial.mp hpf))
  · exact hpq

private lemma add_two_le_two_pow (t : ℕ) (ht : 2 ≤ t) : t + 2 ≤ 2 ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht' : 2 ≤ t
      · have h := ih ht'
        rw [pow_succ']
        omega
      · have : t = 1 := by omega
        subst t
        norm_num

-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) :=
by
  intro hdiv
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hm0 : n - 1 ≠ 0 := by omega
  have hodd_eq : ∀ p : ℕ, p.Prime → p ∣ n → p ≠ 2 → n = p := by
    intro p hp hpn hp2
    by_contra hne
    have hb := composite_prime_factor_bound n p hp hp2 (by omega) hpn hne
    have hpa : p ∣ a (n - 1) := by
      rw [a_eq_quotient hm0]
      exact prime_dvd_exact_quotient (n - 1) p hp hp2 hb
    have hpsum : p ∣ a (n - 1) + 2 ^ (n - 2) := hpn.trans hdiv
    have hppow : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_iff_right hpa).mpr hpsum
    have hpbase : p ∣ 2 := hp.dvd_of_dvd_pow hppow
    rcases (Nat.dvd_prime prime_two).mp hpbase with hp1 | hp2'
    · exact hp.ne_one hp1
    · exact hp2 hp2'
  have hnprime : n.Prime := by
    by_contra hnp
    have hunique : ∀ {p : ℕ}, p.Prime → p ∣ n → p = 2 := by
      intro p hp hpn
      by_contra hp2
      have heq : n = p := hodd_eq p hp hpn hp2
      apply hnp
      simpa [heq] using hp
    obtain ⟨t, hpow⟩ : ∃ t : ℕ, n = 2 ^ t :=
      ⟨n.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hn0 hunique⟩
    have ht : 2 ≤ t := by
      rcases t with _ | _ | t <;> simp_all
    subst n
    have htm : t ≤ 2 ^ t - 2 := by
      have := add_two_le_two_pow t ht
      omega
    have hsecond : 2 ^ t ∣ 2 ^ (2 ^ t - 2) := pow_dvd_pow 2 htm
    have hsum : 2 ^ t ∣ a (2 ^ t - 1) + 2 ^ (2 ^ t - 2) := by simpa using hdiv
    have hda : 2 ^ t ∣ a (2 ^ t - 1) := (Nat.dvd_add_iff_left hsecond).mpr hsum
    have hm : 2 ^ t - 1 ≠ 0 := by
      have := pow_pos (by decide : 0 < (2 : ℕ)) t
      omega
    have hva : padicValNat 2 (a (2 ^ t - 1)) = t - 1 := by
      rw [a_eq_quotient hm]
      exact padicValNat_two_power_quotient t ht
    have ha0 : a (2 ^ t - 1) ≠ 0 := by
      intro ha
      rw [ha, padicValNat.zero] at hva
      omega
    letI : Fact (Nat.Prime 2) := ⟨prime_two⟩
    have htle : t ≤ padicValNat 2 (a (2 ^ t - 1)) :=
      (padicValNat_dvd_iff_le ha0).mp hda
    omega
  refine ⟨hnprime, ?_⟩
  letI : Fact n.Prime := ⟨hnprime⟩
  have htwo : (2 : ZMod n) ≠ 0 := by
    intro hz
    have hd2 : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp hz
    have hnle : n ≤ 2 := Nat.le_of_dvd (by decide) hd2
    omega
  let d := orderOf (2 : ZMod n)
  have hddvd : d ∣ n - 1 := ZMod.orderOf_dvd_card_sub_one htwo
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddvd (by omega)
  have hdle : d ≤ n - 1 := Nat.le_of_dvd (by omega) hddvd
  have hdeq : d = n - 1 := by
    by_contra hne
    have hdlt : d < n - 1 := lt_of_le_of_ne hdle hne
    have hdpow : (2 : ZMod n) ^ d = 1 := pow_orderOf_eq_one (2 : ZMod n)
    have hone : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by decide)
    have hcast : ((2 ^ d - 1 : ℕ) : ZMod n) = 0 := by
      rw [Nat.cast_sub hone, Nat.cast_pow]
      norm_num [hdpow]
    have hnfactor : n ∣ 2 ^ d - 1 := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    have hdmem : d ∈ Finset.Ico 1 (n - 1) := Finset.mem_Ico.mpr ⟨hdpos, hdlt⟩
    have hnprod : n ∣ (Finset.Ico 1 (n - 1)).prod (fun i => 2 ^ i - 1) :=
      hnfactor.trans (Finset.dvd_prod_of_mem (fun i => 2 ^ i - 1) hdmem)
    have hna : n ∣ a (n - 1) := by
      rw [a_eq_quotient hm0]
      exact prime_dvd_quotient_of_dvd_product (n - 1) n hnprime (by omega) hnprod
    have hnsum : n ∣ a (n - 1) + 2 ^ (n - 2) := hdiv
    have hnpow : n ∣ 2 ^ (n - 2) := (Nat.dvd_add_iff_right hna).mpr hnsum
    have hn2 : n ∣ 2 := hnprime.dvd_of_dvd_pow hnpow
    have hnle : n ≤ 2 := Nat.le_of_dvd (by decide) hn2
    omega
  rw [IsPrimitiveRoot.iff_orderOf, Nat.totient_prime hnprime]
  exact hdeq
