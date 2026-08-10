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
open Finset

/-- The numerator of `a n`. -/
def numer (n : ℕ) : ℕ := 2 ^ (n - 1) * ∏ k ∈ Finset.Ico 1 n, (2 ^ k - 1)

lemma a_eq (n : ℕ) (hn : n ≠ 0) : a n = numer n / n ! := by
  unfold a numer
  rw [dif_neg hn]
  simp [Nat.pred_eq_sub_one]

lemma factor_pos {k : ℕ} (hk : 1 ≤ k) : 0 < 2 ^ k - 1 := by
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

lemma prod_pos (n : ℕ) : 0 < ∏ k ∈ Finset.Ico 1 n, (2 ^ k - 1) := by
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact factor_pos hk.1

lemma numer_pos (n : ℕ) : 0 < numer n := by
  unfold numer
  exact Nat.mul_pos (pow_pos (by norm_num) _) (prod_pos n)

/-- Order of `2` modulo `p`. -/
noncomputable def d (p : ℕ) : ℕ := orderOf (2 : ZMod p)

lemma two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring]
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  have := hp.two_le
  omega

lemma cast_two_pow_sub_one {p k : ℕ} :
    (((2 ^ k - 1 : ℕ)) : ZMod p) = (2 : ZMod p) ^ k - 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  rw [Nat.cast_sub h1]
  push_cast
  ring

lemma dvd_two_pow_sub_one_iff {p k : ℕ} (hp : p.Prime) :
    p ∣ 2 ^ k - 1 ↔ d p ∣ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff, cast_two_pow_sub_one, sub_eq_zero]
  rw [d, orderOf_dvd_iff_pow_eq_one]

lemma d_pos {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 1 ≤ d p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hfin : IsOfFinOrder (2 : ZMod p) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp hp2)⟩
  exact hfin.orderOf_pos

lemma d_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : d p ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact ZMod.orderOf_dvd_card_sub_one (two_ne_zero_zmod hp hp2)

lemma d_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : d p ≤ p - 1 := by
  have hp2le := hp.two_le
  exact Nat.le_of_dvd (by omega) (d_dvd hp hp2)

lemma p_not_dvd_d {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ d p := by
  intro h
  have h1 := d_pos hp hp2
  have h2 := d_le hp hp2
  have := Nat.le_of_dvd (by omega) h
  have := hp.two_le
  omega

/-- Lifting the exponent for `2^k - 1` at an odd prime `p`. -/
lemma lte_factorization {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : d p ∣ k) (hk0 : k ≠ 0) :
    (2 ^ k - 1).factorization p = (2 ^ (d p) - 1).factorization p + k.factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, rfl⟩ := hk
  have hj0 : j ≠ 0 := by rintro rfl; simp at hk0
  have hd1 : 1 ≤ d p := d_pos hp hp2
  have hpd : p ∣ 2 ^ (d p) - 1 := (dvd_two_pow_sub_one_iff hp).mpr dvd_rfl
  have hx : ¬ p ∣ (2 : ℕ) ^ (d p) := by
    intro h
    have := hp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le; omega
  have key : padicValNat p ((2 ^ (d p)) ^ j - 1 ^ j)
      = padicValNat p (2 ^ (d p) - 1) + padicValNat p j := by
    apply padicValNat.pow_sub_pow (hp1 := hp.odd_of_ne_two hp2)
    · exact Nat.one_lt_two_pow (by omega)
    · simpa using hpd
    · simpa using hx
    · exact hj0
  rw [one_pow, ← pow_mul] at key
  have e4 : (d p * j).factorization p = j.factorization p := by
    rw [Nat.factorization_mul (by omega) hj0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (p_not_dvd_d hp hp2), zero_add]
  rw [e4, Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  exact key

lemma factorization_d_factor_pos {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    1 ≤ (2 ^ (d p) - 1).factorization p := by
  have hne : 2 ^ (d p) - 1 ≠ 0 := (factor_pos (d_pos hp hp2)).ne'
  have hdvd : p ∣ 2 ^ (d p) - 1 := (dvd_two_pow_sub_one_iff hp).mpr dvd_rfl
  exact hp.factorization_pos_of_dvd hne hdvd

lemma factorial_factorization_eq (p M : ℕ) :
    (M !).factorization p = ∑ j ∈ Finset.Ico 1 (M + 1), j.factorization p := by
  rw [← Finset.prod_Ico_id_eq_factorial, Nat.factorization_prod_apply]
  intro x hx
  rw [Finset.mem_Ico] at hx
  omega

/-- Master lower bound: `M + (M!).factorization p ≤ ∑_{k<N} v_p(2^k-1)`, with `M = (N-1)/d`. -/
lemma sum_lower_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) :
    (N - 1) / d p + (((N - 1) / d p)!).factorization p
      ≤ ∑ k ∈ Finset.Ico 1 N, (2 ^ k - 1).factorization p := by
  set dd := d p with hdd
  have hdd1 : 1 ≤ dd := d_pos hp hp2
  set M := (N - 1) / dd with hM
  -- The set of multiples of dd in [1, N)
  have hset : (Finset.Ico 1 N).filter (fun k => dd ∣ k)
      = (Finset.Ico 1 (M + 1)).image (fun j => dd * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨⟨hk1, hkN⟩, j, rfl⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj; simp at hk1
        · exact hj
      · rw [Nat.lt_add_one_iff, hM]
        apply (Nat.le_div_iff_mul_le hdd1).mpr
        rw [mul_comm]; omega
    · rintro ⟨j, ⟨hj1, hjM⟩, rfl⟩
      rw [Nat.lt_add_one_iff] at hjM
      have hjM_le : dd * j ≤ dd * M := by gcongr
      have hMb : dd * M ≤ N - 1 := by rw [mul_comm, hM]; exact Nat.div_mul_le_self _ _
      have hk1 : 1 ≤ dd * j := by
        calc 1 ≤ dd * 1 := by omega
          _ ≤ dd * j := by gcongr
      exact ⟨⟨hk1, by omega⟩, dvd_mul_right dd j⟩
  show M + ((M)!).factorization p ≤ _
  refine le_trans ?_ (Finset.sum_le_sum_of_subset
    (Finset.filter_subset (fun k => dd ∣ k) (Finset.Ico 1 N)))
  rw [hset, Finset.sum_image
    (by intro x _ y _ hxy; exact Nat.eq_of_mul_eq_mul_left (by omega) hxy)]
  show M + ((M)!).factorization p ≤ ∑ j ∈ Finset.Ico 1 (M + 1), (2 ^ (dd * j) - 1).factorization p
  have heq : M + ((M)!).factorization p
      = ∑ j ∈ Finset.Ico 1 (M + 1), (1 + j.factorization p) := by
    rw [Finset.sum_add_distrib, factorial_factorization_eq]
    congr 1
    rw [Finset.sum_const, Nat.card_Ico]; simp
  rw [heq]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mem_Ico] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hjne : j ≠ 0 := by omega
  have hj0 : dd * j ≠ 0 := Nat.mul_ne_zero (by omega) hjne
  rw [lte_factorization hp hp2 (dvd_mul_right dd j) hj0]
  have e4 : (dd * j).factorization p = j.factorization p := by
    rw [Nat.factorization_mul (by omega) hjne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (p_not_dvd_d hp hp2), zero_add]
  rw [e4]
  have := factorization_d_factor_pos hp hp2
  omega

lemma digits_sum_pos {p n : ℕ} (hn : n ≠ 0) : 1 ≤ (Nat.digits p n).sum := by
  have hne : Nat.digits p n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (Nat.digits p n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero p hn
  have hmem : (Nat.digits p n).getLast hne ∈ Nat.digits p n := List.getLast_mem hne
  have hle : (Nat.digits p n).getLast hne ≤ (Nat.digits p n).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
  omega

lemma fact_fact_le {p n : ℕ} (hp : p.Prime) : (n !).factorization p ≤ (n - 1) / (p - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.le_div_iff_mul_le (by have := hp.two_le; omega), mul_comm]
    have h := Nat.sub_one_mul_factorization_factorial (n := n) hp
    have hd := digits_sum_pos (n := n) (p := p) (by omega)
    rw [h]; omega

/-- The factorization of `numer n` at a prime `p`. -/
lemma factorization_numer {p n : ℕ} (hp : p.Prime) :
    (numer n).factorization p
      = (n - 1) * (2 : ℕ).factorization p + ∑ k ∈ Finset.Ico 1 n, (2 ^ k - 1).factorization p := by
  unfold numer
  rw [Nat.factorization_mul (by positivity) (prod_pos n).ne', Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_prod_apply]
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact (factor_pos hk.1).ne'

lemma integrality (n : ℕ) : n ! ∣ numer n := by
  rw [← Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero n) (numer_pos n).ne', Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · rw [factorization_numer hp]
    by_cases hp2 : p = 2
    · -- p = 2 : numer has 2-adic valuation ≥ n-1 ≥ v_2(n!)
      subst hp2
      have hpow : (2 : ℕ).factorization 2 = 1 := by
        rw [Nat.Prime.factorization_self Nat.prime_two]
      have hle : (n !).factorization 2 ≤ n - 1 := by
        have := fact_fact_le (n := n) (p := 2) Nat.prime_two
        simpa using this
      rw [hpow]; omega
    · -- p odd
      have hpow : (2 : ℕ).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by
          intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
      rw [hpow, mul_zero, zero_add]
      have h1 : (n !).factorization p ≤ (n - 1) / (p - 1) := fact_fact_le hp
      have h2 : (n - 1) / (p - 1) ≤ (n - 1) / d p :=
        Nat.div_le_div_left (d_le hp hp2) (d_pos hp hp2)
      have h3 := sum_lower_bound hp hp2 n
      omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma a_mul_factorial {n : ℕ} (hn : n ≠ 0) : a n * n ! = numer n := by
  rw [a_eq n hn, Nat.div_mul_cancel (integrality n)]

lemma a_pos {n : ℕ} (hn : n ≠ 0) : 0 < a n := by
  have h := a_mul_factorial hn
  have := numer_pos n
  rcases Nat.eq_zero_or_pos (a n) with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

/-- `(p*t - 1)!` has `p`-factorization `(t-1) + (t-1)!.factorization p`. -/
lemma fact_factorization_mul_pred {p t : ℕ} (hp : p.Prime) (ht : 1 ≤ t) :
    (p * t - 1)!.factorization p = (t - 1) + ((t - 1)!).factorization p := by
  have hpt : 0 < p * t := by have := hp.pos; positivity
  have e1 : (p * t)!.factorization p = (p * t - 1)!.factorization p + (p * t).factorization p := by
    conv_lhs => rw [← Nat.mul_factorial_pred hpt.ne']
    rw [Nat.factorization_mul hpt.ne' (Nat.factorial_ne_zero _), Finsupp.add_apply]
    ring
  have e2 : (p * t).factorization p = 1 + t.factorization p := by
    rw [Nat.factorization_mul hp.pos.ne' (by omega), Finsupp.add_apply, hp.factorization_self]
  have e3 : (t !).factorization p = (t - 1)!.factorization p + t.factorization p := by
    conv_lhs => rw [← Nat.mul_factorial_pred (show t ≠ 0 by omega)]
    rw [Nat.factorization_mul (by omega) (Nat.factorial_ne_zero _), Finsupp.add_apply]
    ring
  have e4 := Nat.factorization_factorial_mul (n := t) hp
  -- e4 : (p*t)!.factorization p = (t!).factorization p + t
  rw [e1, e2, e3] at e4
  omega

/-- For an odd prime factor `p` of a composite `n`, `p ∣ a (n-1)`. -/
lemma p_dvd_a {n p : ℕ} (hn : 2 < n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ n) (hpltn : p < n) : p ∣ a (n - 1) := by
  obtain ⟨t, rfl⟩ := hpn
  have hp2le := hp.two_le
  have ht : 2 ≤ t := by
    rcases Nat.lt_or_ge t 2 with h | h
    · interval_cases t <;> omega
    · exact h
  set n := p * t with hndef
  -- factorization equation
  have hn1 : n - 1 ≠ 0 := by omega
  have hmul := a_mul_factorial hn1
  -- a(n-1) * (n-1)! = numer (n-1)
  have hane : a (n - 1) ≠ 0 := (a_pos hn1).ne'
  have key : (a (n - 1)).factorization p + ((n - 1)!).factorization p
      = ∑ k ∈ Finset.Ico 1 (n - 1), (2 ^ k - 1).factorization p := by
    have := congrArg (fun m => m.factorization p) hmul
    dsimp only at this
    rw [Nat.factorization_mul hane (Nat.factorial_ne_zero _), Finsupp.add_apply] at this
    rw [this, factorization_numer hp]
    have hpow : (2 : ℕ).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
    rw [hpow, mul_zero, zero_add]
  -- lower bound on RHS sum
  have hlb := sum_lower_bound hp hp2 (n - 1)
  -- (n-1)! factorization via decomposition; n - 1 = p*t - 1
  have hfac : ((n - 1)!).factorization p = (t - 1) + ((t - 1)!).factorization p := by
    rw [hndef]; exact fact_factorization_mul_pred hp (by omega)
  -- M := (n-2)/d p, show M ≥ t
  have hdle := d_le hp hp2
  have hdpos := d_pos hp hp2
  have hadd : t * (p - 1) + t = p * t := by
    have hpp : (p - 1) + 1 = p := Nat.sub_add_cancel hp.pos
    calc t * (p - 1) + t = t * ((p - 1) + 1) := by ring
      _ = t * p := by rw [hpp]
      _ = p * t := by ring
  have hM_ge : t ≤ (n - 1 - 1) / d p := by
    apply (Nat.le_div_iff_mul_le hdpos).mpr
    have hmul_le : t * d p ≤ t * (p - 1) := mul_le_mul_left' hdle t
    rw [hndef]
    omega
  -- monotonicity of factorial factorization
  have hmono : ((t - 1)!).factorization p ≤ (((n - 1 - 1) / d p)!).factorization p := by
    have hdvd : (t - 1)! ∣ ((n - 1 - 1) / d p)! := Nat.factorial_dvd_factorial (by omega)
    have hle := (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero _)
      (Nat.factorial_ne_zero _)).mpr hdvd
    exact Finsupp.le_def.mp hle p
  -- combine
  have : 1 ≤ (a (n - 1)).factorization p := by omega
  exact Nat.dvd_of_factorization_pos (by omega)

lemma digitsum_two_pow_pred (s : ℕ) : (Nat.digits 2 (2 ^ s - 1)).sum = s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hX : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have hY : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
    have h1 : 0 < 2 ^ (s + 1) - 1 := by omega
    have hmod : (2 ^ (s + 1) - 1) % 2 = 1 := by omega
    have hdiv : (2 ^ (s + 1) - 1) / 2 = 2 ^ s - 1 := by omega
    rw [Nat.digits_def' (by norm_num : 2 ≤ 2) h1, hmod, hdiv, List.sum_cons, ih]
    omega

lemma pow_ge (s : ℕ) (hs : 2 ≤ s) : s + 2 ≤ 2 ^ s := by
  induction s with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · omega
      · norm_num
    · have hih := ih hm
      have he : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      omega

lemma factorization_odd_factor (k : ℕ) (hk : 1 ≤ k) : (2 ^ k - 1).factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have heven : 2 ^ k % 2 = 0 := by
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  omega

/-- Power-of-two case: `n = 2^s` with `s ≥ 2` does not satisfy the divisibility. -/
lemma c1b {n s : ℕ} (hn : 2 < n) (hs : 2 ≤ s) (hns : n = 2 ^ s) :
    ¬ n ∣ (a (n - 1) + 2 ^ (n - 2)) := by
  have hn1 : n - 1 ≠ 0 := by omega
  have hmul := a_mul_factorial hn1
  have hane : a (n - 1) ≠ 0 := (a_pos hn1).ne'
  -- factorization of a(n-1) at 2
  have key : (a (n - 1)).factorization 2 + ((n - 1)!).factorization 2 = n - 2 := by
    have h0 := congrArg (fun m => m.factorization 2) hmul
    dsimp only at h0
    rw [Nat.factorization_mul hane (Nat.factorial_ne_zero _), Finsupp.add_apply,
      factorization_numer Nat.prime_two, Nat.Prime.factorization_self Nat.prime_two, mul_one] at h0
    have hsum : ∑ k ∈ Finset.Ico 1 (n - 1), (2 ^ k - 1).factorization 2 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Ico] at hk
      exact factorization_odd_factor k hk.1
    rw [hsum, add_zero] at h0
    omega
  -- v_2((n-1)!) = (n-1) - s
  have hfac : ((n - 1)!).factorization 2 = (n - 1) - s := by
    have h := Nat.sub_one_mul_factorization_factorial (n := n - 1) Nat.prime_two
    simp only [show (2 : ℕ) - 1 = 1 by norm_num, one_mul] at h
    rw [h, hns]
    congr 1
    exact digitsum_two_pow_pred s
  have hsle : s ≤ n - 1 := by rw [hns]; have := pow_ge s hs; omega
  have hva : (a (n - 1)).factorization 2 = s - 1 := by omega
  -- 2^s ∤ a(n-1)
  have hnotdvd : ¬ 2 ^ s ∣ a (n - 1) := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hane, hva]
    omega
  -- 2^s ∣ 2^(n-2)
  have hdvd2 : 2 ^ s ∣ 2 ^ (n - 2) := by
    apply pow_dvd_pow
    have := pow_ge s hs
    rw [hns]; omega
  -- conclude
  intro hdvd
  have hdvd' : 2 ^ s ∣ a (n - 1) + 2 ^ (n - 2) := by rw [← hns]; exact hdvd
  exact hnotdvd ((Nat.dvd_add_right hdvd2).mp (by rwa [add_comm] at hdvd'))

lemma numer_cast_zmod {p : ℕ} (m : ℕ) :
    ((numer m : ℕ) : ZMod p) = (2 : ZMod p) ^ (m - 1) * ∏ k ∈ Finset.Ico 1 m, ((2 : ZMod p) ^ k - 1) := by
  unfold numer
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact cast_two_pow_sub_one

/-- If `p` is an odd prime and the divisibility holds, then `2` is a primitive root mod `p`. -/
lemma prime_root_of_dvd {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hdvd : p ∣ a (p - 1) + 2 ^ (p - 2)) : orderOf (2 : ZMod p) = Nat.totient p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpne2 : p ≠ 2 := by omega
  have hp1 : p - 1 ≠ 0 := by omega
  have hmul := a_mul_factorial hp1
  -- cast the multiplicative identity to ZMod p
  have hcast : (a (p - 1) : ZMod p) * (((p - 1)! : ℕ) : ZMod p)
      = (2 : ZMod p) ^ (p - 2) * ∏ k ∈ Finset.Ico 1 (p - 1), ((2 : ZMod p) ^ k - 1) := by
    have h := congrArg (fun m => ((m : ℕ) : ZMod p)) hmul
    dsimp only at h
    rw [Nat.cast_mul, numer_cast_zmod] at h
    rw [h, show p - 1 - 1 = p - 2 by omega]
  -- Wilson
  have hwil : (((p - 1)! : ℕ) : ZMod p) = -1 := ZMod.wilsons_lemma p
  -- divisibility in ZMod p
  have hdvd0 : (a (p - 1) : ZMod p) + (2 : ZMod p) ^ (p - 2) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
    push_cast at this
    convert this using 2
  have h2ne : (2 : ZMod p) ^ (p - 2) ≠ 0 := pow_ne_zero _ (two_ne_zero_zmod hp hpne2)
  -- Derive Fbar = 1
  set Fbar := ∏ k ∈ Finset.Ico 1 (p - 1), ((2 : ZMod p) ^ k - 1) with hFbar
  have ha : (a (p - 1) : ZMod p) = -(2 : ZMod p) ^ (p - 2) := by linear_combination hdvd0
  rw [hwil, ha] at hcast
  -- hcast : (-(2)^(p-2)) * (-1) = (2)^(p-2) * Fbar
  have hFbar1 : Fbar = 1 := by
    have h1 : (2 : ZMod p) ^ (p - 2) * Fbar = (2 : ZMod p) ^ (p - 2) * 1 := by
      rw [mul_one]; linear_combination -hcast
    exact (mul_left_cancel₀ h2ne h1)
  -- Now show orderOf = p - 1
  have hord_dvd : orderOf (2 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one (two_ne_zero_zmod hp hpne2)
  have hord_pos : 1 ≤ orderOf (2 : ZMod p) := d_pos hp hpne2
  have hord_eq : orderOf (2 : ZMod p) = p - 1 := by
    by_contra hne
    have hlt : orderOf (2 : ZMod p) < p - 1 :=
      lt_of_le_of_ne (Nat.le_of_dvd (by omega) hord_dvd) hne
    -- the factor at k = orderOf is zero
    have hmem : orderOf (2 : ZMod p) ∈ Finset.Ico 1 (p - 1) := by
      rw [Finset.mem_Ico]; exact ⟨hord_pos, hlt⟩
    have hzero : (2 : ZMod p) ^ orderOf (2 : ZMod p) - 1 = 0 := by
      rw [pow_orderOf_eq_one]; ring
    have : Fbar = 0 := Finset.prod_eq_zero hmem hzero
    rw [hFbar1] at this
    exact one_ne_zero this
  rw [hord_eq, Nat.totient_prime hp]

lemma composite_fails {n : ℕ} (hn : 2 < n) (hnp : ¬ n.Prime) :
    ¬ n ∣ (a (n - 1) + 2 ^ (n - 2)) := by
  by_cases hodd : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ n
  · obtain ⟨p, hp, hp2, hpn⟩ := hodd
    have hp2le := hp.two_le
    have hpltn : p < n := by
      rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hpn) with h | h
      · exact h
      · exact absurd (h ▸ hp) hnp
    have hpa : p ∣ a (n - 1) := p_dvd_a hn hp hp2 hpn hpltn
    intro hdvd
    have hpX : p ∣ a (n - 1) + 2 ^ (n - 2) := dvd_trans hpn hdvd
    have hp2pow : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_right hpa).mp hpX
    have hpd2 : p ∣ 2 := hp.dvd_of_dvd_pow hp2pow
    have := Nat.le_of_dvd (by norm_num) hpd2
    omega
  · push_neg at hodd
    have huniq : ∀ {d}, d.Prime → d ∣ n → d = 2 := by
      intro d hd hdn
      by_contra hd2
      exact (hodd d hd hd2) hdn
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : n ≠ 0) huniq
    set k := n.primeFactorsList.length with hk_def
    have hk : 2 ≤ k := by
      by_contra hkk
      push_neg at hkk
      interval_cases k
      · rw [pow_zero] at hpow; omega
      · rw [pow_one] at hpow; omega
    exact c1b hn hk hpow

end A091669

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
  intro hdvd
  have hprime : n.Prime := by
    by_contra hnp
    exact A091669.composite_fails hn hnp hdvd
  refine ⟨hprime, ?_, ?_⟩
  · have hord := A091669.prime_root_of_dvd hprime hn hdvd
    rw [← hord]; exact pow_orderOf_eq_one _
  · intro l hl
    have hord := A091669.prime_root_of_dvd hprime hn hdvd
    rw [← hord]; exact orderOf_dvd_of_pow_eq_one hl
