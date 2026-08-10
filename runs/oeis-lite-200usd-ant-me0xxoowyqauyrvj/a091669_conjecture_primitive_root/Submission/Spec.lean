import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

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

/-- The numerator of `a n`. -/
def num (m : ℕ) : ℕ := 2 ^ (m - 1) * (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)

lemma a_eq_num_div (n : ℕ) (hn : n ≠ 0) : a n = num n / n.factorial := by
  unfold a num
  simp [hn, Nat.pred_eq_sub_one]

lemma num_factor_pos {k : ℕ} (hk : 1 ≤ k) : 0 < 2 ^ k - 1 := by
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2^1 := by ring
    _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  omega

lemma num_pos (m : ℕ) : 0 < num m := by
  unfold num
  apply Nat.mul_pos
  · positivity
  · apply Finset.prod_pos
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact num_factor_pos hk.1

lemma num_succ {m : ℕ} (hm : 1 ≤ m) : num (m + 1) = 2 * (2 ^ m - 1) * num m := by
  unfold num
  rw [Finset.prod_Ico_succ_top hm]
  have h2 : 2 ^ (m + 1 - 1) = 2 * 2 ^ (m - 1) := by
    have : m + 1 - 1 = (m - 1) + 1 := by omega
    rw [this, pow_succ]; ring
  rw [h2]; ring

-- Arithmetic helper: m/p ≤ (m-1)/d  when 0 < d ≤ p-1 and 2 ≤ p
lemma q_bound {m p d : ℕ} (hp : 2 ≤ p) (hd : 0 < d) (hdp : d ≤ p - 1) :
    m / p ≤ (m - 1) / d := by
  have h1 : m / p ≤ (m - 1) / (p - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    rcases Nat.eq_zero_or_pos (m / p) with h0 | h0
    · simp [h0]
    · have hpm : m / p * p ≤ m := Nat.div_mul_le_self m p
      have : m / p * (p - 1) = m / p * p - m / p := by
        rw [Nat.mul_sub, mul_one]
      omega
  have h2 : (m - 1) / (p - 1) ≤ (m - 1) / d := Nat.div_le_div_left hdp hd
  exact le_trans h1 h2

lemma sum_div_pow_le {B p m Q : ℕ} (hp : 2 ≤ p) (hq : m / p ≤ Q) :
    ∑ i ∈ Ico 1 B, m / p ^ i ≤ Q + ∑ i ∈ Ico 1 B, Q / p ^ i := by
  -- termwise: m/p^i ≤ Q/p^(i-1)
  have hterm : ∀ i ∈ Ico 1 B, m / p ^ i ≤ Q / p ^ (i - 1) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi1 : 1 ≤ i := hi.1
    have hpe : p ^ i = p * p ^ (i - 1) := by
      conv_lhs => rw [show i = 1 + (i - 1) by omega]
      rw [pow_add, pow_one]
    rw [hpe, ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_right hq
  have h1 : ∑ i ∈ Ico 1 B, m / p ^ i ≤ ∑ i ∈ Ico 1 B, Q / p ^ (i - 1) :=
    Finset.sum_le_sum hterm
  have h2 : ∑ i ∈ Ico 1 B, Q / p ^ (i - 1) = ∑ k ∈ range (B - 1), Q / p ^ k := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have : 1 + k - 1 = k := by omega
    rw [this]
  have h3 : ∑ k ∈ range (B - 1), Q / p ^ k ≤ Q + ∑ i ∈ Ico 1 B, Q / p ^ i := by
    rcases Nat.eq_zero_or_pos B with hB | hB
    · subst hB; simp
    · have hsub : range (B - 1) ⊆ range B := by
        intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      calc ∑ k ∈ range (B - 1), Q / p ^ k
          ≤ ∑ k ∈ range B, Q / p ^ k := Finset.sum_le_sum_of_subset hsub
        _ = Q + ∑ i ∈ Ico 1 B, Q / p ^ i := by
            rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hB]
            simp
  calc ∑ i ∈ Ico 1 B, m / p ^ i ≤ ∑ i ∈ Ico 1 B, Q / p ^ (i - 1) := h1
    _ = ∑ k ∈ range (B - 1), Q / p ^ k := h2
    _ ≤ Q + ∑ i ∈ Ico 1 B, Q / p ^ i := h3

-- Legendre comparison (Step D')
lemma legendre_le {m p d : ℕ} (hp : p.Prime) (hd : 0 < d) (hdp : d ≤ p - 1) :
    (m.factorial).factorization p ≤ (m - 1) / d + (((m - 1) / d).factorial).factorization p := by
  set Q := (m - 1) / d with hQ
  have hp2 : 2 ≤ p := hp.two_le
  have hQm : Q ≤ m := by rw [hQ]; exact le_trans (Nat.div_le_self _ _) (by omega)
  have hbm : Nat.log p m < m + 1 := Nat.lt_succ_of_le (Nat.log_le_self p m)
  have hbQ : Nat.log p Q < m + 1 := Nat.lt_succ_of_le (le_trans (Nat.log_le_self p Q) hQm)
  rw [Nat.factorization_factorial hp hbm, Nat.factorization_factorial hp hbQ]
  have hq : m / p ≤ Q := q_bound hp2 hd hdp
  exact sum_div_pow_le hp2 hq

lemma order_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    0 < orderOf (2 : ZMod p) ∧ orderOf (2 : ZMod p) ≤ p - 1 ∧
      p ∣ 2 ^ orderOf (2 : ZMod p) - 1 := by
  haveI := Fact.mk hp
  set d := orderOf (2 : ZMod p) with hd
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : ¬ (p ∣ 2) := by
      intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    rw [show (2 : ZMod p) = ((2:ℕ) : ZMod p) by push_cast; ring]
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact this
  have hpow : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd1 : d ∣ p - 1 := orderOf_dvd_of_pow_eq_one hpow
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  refine ⟨Nat.pos_of_dvd_of_pos hdvd1 hp1, Nat.le_of_dvd hp1 hdvd1, ?_⟩
  have hpe : (2 : ZMod p) ^ d = 1 := pow_orderOf_eq_one (2 : ZMod p)
  have : ((2 ^ d - 1 : ℕ) : ZMod p) = 0 := by
    have h1 : (1:ℕ) ≤ 2 ^ d := Nat.one_le_two_pow
    push_cast [h1]
    rw [hpe]; ring
  rwa [ZMod.natCast_eq_zero_iff] at this

-- LTE termwise step (Step B')
lemma lte_step {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d ℓ : ℕ} (hd : 0 < d)
    (hpd : p ∣ 2 ^ d - 1) (hℓ : 1 ≤ ℓ) :
    1 + (ℓ).factorization p ≤ (2 ^ (d * ℓ) - 1).factorization p := by
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hx : ¬ p ∣ 2 ^ d := by
    intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hyx : (1:ℕ) < 2 ^ d := by
    calc (1:ℕ) < 2 := by norm_num
    _ = 2^1 := by ring
    _ ≤ 2^d := Nat.pow_le_pow_right (by norm_num) hd
  have key := padicValNat.pow_sub_pow (p := p) hodd hyx hpd hx (n := ℓ) (by omega)
  rw [one_pow, ← pow_mul] at key
  have hfac1 : (2 ^ (d * ℓ) - 1).factorization p = padicValNat p (2 ^ (d * ℓ) - 1) :=
    Nat.factorization_def _ hp
  have hfac2 : (ℓ).factorization p = padicValNat p ℓ := Nat.factorization_def _ hp
  have hge1 : 1 ≤ padicValNat p (2 ^ d - 1) := one_le_padicValNat_of_dvd (by omega) hpd
  rw [hfac1, hfac2, key]; omega

-- Odd-prime integrality bound
lemma odd_integrality {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (m.factorial).factorization p ≤ ∑ k ∈ Ico 1 m, (2 ^ k - 1).factorization p := by
  obtain ⟨hd0, hdp, hpd⟩ := order_facts hp hp2
  set d := orderOf (2 : ZMod p) with hd
  set Q := (m - 1) / d with hQ
  -- (Q!).factorization p = ∑_{ℓ∈Ico 1 (Q+1)} (ℓ).factorization p
  have hCfac : (Q.factorial).factorization p = ∑ ℓ ∈ Ico 1 (Q + 1), (ℓ).factorization p := by
    rw [← Finset.prod_Ico_id_eq_factorial Q]
    rw [Nat.factorization_prod_apply]
    intro x hx; rw [Finset.mem_Ico] at hx; omega
  have hcard : ∑ _ℓ ∈ Ico 1 (Q + 1), (1 : ℕ) = Q := by
    rw [Finset.sum_const, Nat.card_Ico]; simp
  -- subset: image of Ico 1 (Q+1) under (d * ·) ⊆ Ico 1 m
  have hdQ : d * Q ≤ m - 1 := by rw [hQ]; rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have hmem : ∀ ℓ ∈ Ico 1 (Q + 1), d * ℓ ∈ Ico 1 m := by
    intro ℓ hℓ; rw [Finset.mem_Ico] at hℓ ⊢
    obtain ⟨hℓ1, hℓ2⟩ := hℓ
    have hle : d * ℓ ≤ d * Q := Nat.mul_le_mul_left d (by omega)
    have hmpos : 1 ≤ m := by
      by_contra h; push_neg at h; interval_cases m <;> simp_all <;> omega
    constructor
    · have : 1 ≤ d * ℓ := by
        have : 1 ≤ d := hd0
        calc 1 = 1 * 1 := by ring
        _ ≤ d * ℓ := Nat.mul_le_mul (by omega) (by omega)
      omega
    · omega
  have hinj : Set.InjOn (fun ℓ => d * ℓ) ↑(Ico 1 (Q + 1)) := by
    intro x _ y _ hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left hd0 hxy
  refine le_trans (legendre_le hp hd0 hdp) ?_
  have step1 : Q + (Q.factorial).factorization p
      = ∑ ℓ ∈ Ico 1 (Q + 1), (1 + (ℓ).factorization p) := by
    rw [Finset.sum_add_distrib, hcard, hCfac]
  have step2 : ∑ ℓ ∈ Ico 1 (Q + 1), (1 + (ℓ).factorization p)
      ≤ ∑ ℓ ∈ Ico 1 (Q + 1), (2 ^ (d * ℓ) - 1).factorization p := by
    apply Finset.sum_le_sum
    intro ℓ hℓ; rw [Finset.mem_Ico] at hℓ
    exact lte_step hp hp2 hd0 hpd hℓ.1
  have step3 : ∑ ℓ ∈ Ico 1 (Q + 1), (2 ^ (d * ℓ) - 1).factorization p
      = ∑ k ∈ (Ico 1 (Q + 1)).image (fun ℓ => d * ℓ), (2 ^ k - 1).factorization p := by
    rw [Finset.sum_image hinj]
  have hsub : (Ico 1 (Q + 1)).image (fun ℓ => d * ℓ) ⊆ Ico 1 m := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨ℓ, hℓ, rfl⟩ := hk
    exact hmem ℓ hℓ
  have step4 : ∑ k ∈ (Ico 1 (Q + 1)).image (fun ℓ => d * ℓ), (2 ^ k - 1).factorization p
      ≤ ∑ k ∈ Ico 1 m, (2 ^ k - 1).factorization p := Finset.sum_le_sum_of_subset hsub
  rw [step1]
  exact le_trans step2 (le_of_eq step3 |>.trans step4)

lemma prod_factor_pos (m : ℕ) : 0 < (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) := by
  apply Finset.prod_pos
  intro k hk; rw [Finset.mem_Ico] at hk
  exact num_factor_pos hk.1

-- (num m).factorization at p, expanded
lemma factorization_num (m p : ℕ) (hp : p.Prime) :
    (num m).factorization p
      = (m - 1) * (2 : ℕ).factorization p + ∑ k ∈ Ico 1 m, (2 ^ k - 1).factorization p := by
  unfold num
  rw [Nat.factorization_mul (by positivity) (prod_factor_pos m).ne']
  rw [Finsupp.add_apply]
  rw [Nat.factorization_pow]
  rw [Nat.factorization_prod_apply (by intro x hx; rw [Finset.mem_Ico] at hx; exact (num_factor_pos hx.1).ne')]
  simp [Finsupp.smul_apply, smul_eq_mul]

lemma integrality_factorization (m p : ℕ) (hp : p.Prime) :
    (m.factorial).factorization p ≤ (num m).factorization p := by
  rw [factorization_num m p hp]
  by_cases hp2 : p = 2
  · subst hp2
    have hsum0 : ∑ k ∈ Ico 1 m, (2 ^ k - 1).factorization 2 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk; rw [Finset.mem_Ico] at hk
      apply Nat.factorization_eq_zero_of_not_dvd
      -- 2 ∤ (2^k - 1)
      have : Odd (2 ^ k - 1) := by
        have h2 : 2 ≤ 2 ^ k := by
          calc 2 = 2^1 := by ring
          _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk.1
        rcases Nat.even_or_odd (2 ^ k - 1) with he | ho
        · exfalso
          have hev : Even (2 ^ k) := by
            rcases hk.1.lt_or_eq with h | h
            · exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
            · simp [← h]
          obtain ⟨t, ht⟩ := he; obtain ⟨s, hs⟩ := hev; omega
        · exact ho
      rw [Nat.odd_iff] at this
      omega
    rw [hsum0, Nat.Prime.factorization_self Nat.prime_two, mul_one, add_zero]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have := padicValNat_factorial_lt_of_ne_zero (p := 2) (n := m) (by omega)
      rw [Nat.factorization_def _ Nat.prime_two]
      omega
  · have h20 : (2 : ℕ).factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    rw [h20, mul_zero, zero_add]
    exact odd_integrality hp hp2

lemma num_factorial_dvd (m : ℕ) : m.factorial ∣ num m := by
  rw [← Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero m) (num_pos m).ne']
  intro p
  by_cases hp : p.Prime
  · exact integrality_factorization m p hp
  · rw [Nat.factorization_eq_zero_of_non_prime _ hp]; exact Nat.zero_le _

lemma a_mul (m : ℕ) (hm : m ≠ 0) : a m * m.factorial = num m := by
  rw [a_eq_num_div m hm]
  exact Nat.div_mul_cancel (num_factorial_dvd m)

lemma a_recurrence {m : ℕ} (hm : 1 ≤ m) :
    (m + 1) * a (m + 1) = 2 * (2 ^ m - 1) * a m := by
  have h1 : a (m + 1) * (m + 1).factorial = num (m + 1) := a_mul (m + 1) (by omega)
  have h2 : a m * m.factorial = num m := a_mul m (by omega)
  rw [num_succ hm] at h1
  rw [← h2] at h1
  -- h1 : a(m+1) * (m+1)! = 2*(2^m-1) * (a m * m!)
  have hfac : (m + 1).factorial = (m + 1) * m.factorial := by
    rw [Nat.factorial_succ]
  rw [hfac] at h1
  -- a(m+1) * ((m+1) * m!) = 2(2^m-1) * (a m * m!)
  have hpos : 0 < m.factorial := Nat.factorial_pos m
  -- cancel m!
  have : a (m + 1) * (m + 1) * m.factorial = 2 * (2 ^ m - 1) * a m * m.factorial := by
    ring_nf; ring_nf at h1; linarith [h1]
  have := Nat.eq_of_mul_eq_mul_right hpos this
  linarith [this]

-- Telescoping identity from the recurrence
lemma telescope (L : ℕ) (hL : 1 ≤ L) : ∀ i : ℕ,
    (∏ l ∈ range i, (L + 1 + l)) * a (L + i)
      = (∏ l ∈ range i, 2 * (2 ^ (L + l) - 1)) * a L := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    -- recurrence at j = L + i
    have hrec : (L + i + 1) * a (L + i + 1) = 2 * (2 ^ (L + i) - 1) * a (L + i) :=
      a_recurrence (by omega)
    have hL1i : L + 1 + i = L + i + 1 := by omega
    have hLii : L + (i + 1) = L + i + 1 := by omega
    rw [hLii, hL1i]
    -- goal: (∏ range i (L+1+l)) * (L+i+1) * a(L+i+1) = (∏ range i ...) * (2*(2^(L+i)-1)) * a L
    calc (∏ l ∈ range i, (L + 1 + l)) * (L + i + 1) * a (L + i + 1)
        = (∏ l ∈ range i, (L + 1 + l)) * ((L + i + 1) * a (L + i + 1)) := by ring
      _ = (∏ l ∈ range i, (L + 1 + l)) * (2 * (2 ^ (L + i) - 1) * a (L + i)) := by rw [hrec]
      _ = (2 * (2 ^ (L + i) - 1)) * ((∏ l ∈ range i, (L + 1 + l)) * a (L + i)) := by ring
      _ = (2 * (2 ^ (L + i) - 1)) * ((∏ l ∈ range i, 2 * (2 ^ (L + l) - 1)) * a L) := by rw [ih]
      _ = (∏ l ∈ range i, 2 * (2 ^ (L + l) - 1)) * (2 * (2 ^ (L + i) - 1)) * a L := by ring

-- existence of a multiple of d in a window
lemma exists_mult_in_window (d L : ℕ) (hd : 0 < d) : ∃ l, l < d ∧ d ∣ (L + l) := by
  refine ⟨(d - L % d) % d, Nat.mod_lt _ hd, ?_⟩
  rcases Nat.eq_zero_or_pos (L % d) with h | h
  · simp only [h, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    exact Nat.dvd_of_mod_eq_zero h
  · have hr : L % d < d := Nat.mod_lt _ hd
    have he : (d - L % d) % d = d - L % d := Nat.mod_eq_of_lt (by omega)
    rw [he]
    have hle : L % d ≤ L := Nat.mod_le L d
    have heq : L + (d - L % d) = (L - L % d) + d := by omega
    rw [heq]
    exact Nat.dvd_add (Nat.dvd_sub_mod L) (dvd_refl d)

lemma pow_order_dvd {p d m : ℕ} (hpd : p ∣ 2 ^ d - 1) (h : d ∣ m) : p ∣ 2 ^ m - 1 := by
  obtain ⟨j, rfl⟩ := h
  have hdvd : 2 ^ d - 1 ∣ 2 ^ (d * j) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ d) 1 j
    simpa [← pow_mul] using this
  exact dvd_trans hpd hdvd

-- Composite case: odd prime factor divides a(n-1)
lemma composite_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n) (hlt : p < n) :
    p ∣ a (n - 1) := by
  obtain ⟨hd0, hdp, hpd⟩ := order_facts hp hp2
  set d := orderOf (2 : ZMod p) with hd
  -- n ≥ 2p
  obtain ⟨k, hk⟩ := hpn
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp_all <;> omega
    · exact h
  have hp2le : 2 * p ≤ n := by rw [hk]; nlinarith [hp.two_le]
  have hp1 : 1 ≤ p := hp.one_lt.le
  set L := n - p with hLdef
  have hL1 : 1 ≤ L := by omega
  -- telescope at i = p - 1
  have htel := telescope L hL1 (p - 1)
  have hLp1 : L + (p - 1) = n - 1 := by omega
  rw [hLp1] at htel
  -- p ∣ L (since p ∣ n and p ∣ p)
  have hpn' : p ∣ n := ⟨k, hk⟩
  have hpL : p ∣ L := by rw [hLdef]; exact Nat.dvd_sub hpn' (dvd_refl p)
  -- RHS divisible by p
  obtain ⟨l₀, hl₀d, hl₀dvd⟩ := exists_mult_in_window d L hd0
  have hl₀range : l₀ ∈ range (p - 1) := by
    rw [Finset.mem_range]; omega
  have hpfac : p ∣ 2 * (2 ^ (L + l₀) - 1) := by
    have : p ∣ 2 ^ (L + l₀) - 1 := pow_order_dvd hpd hl₀dvd
    exact Dvd.dvd.mul_left this 2
  have hpRHS : p ∣ (∏ l ∈ range (p - 1), 2 * (2 ^ (L + l) - 1)) * a L := by
    apply Dvd.dvd.mul_right
    exact dvd_trans hpfac (Finset.dvd_prod_of_mem _ hl₀range)
  rw [← htel] at hpRHS
  -- hpRHS : p ∣ (∏ left) * a (n-1)
  -- p ∤ ∏ left
  have hnotprod : ¬ p ∣ (∏ l ∈ range (p - 1), (L + 1 + l)) := by
    rw [hp.prime.dvd_finset_prod_iff]
    rintro ⟨l, hl, hdvd⟩
    rw [Finset.mem_range] at hl
    -- p ∣ L + 1 + l and p ∣ L ⟹ p ∣ 1 + l, but 1 + l < p
    have hp1l : p ∣ (1 + l) := by
      have heq : (L + 1 + l) - L = 1 + l := by omega
      have hsub := Nat.dvd_sub hdvd hpL
      rwa [heq] at hsub
    have := Nat.le_of_dvd (by omega) hp1l
    omega
  rcases (hp.dvd_mul.mp hpRHS) with h | h
  · exact absurd h hnotprod
  · exact h

-- Prime, 2 not a primitive root ⟹ p ∣ a(p-1)
lemma prime_smallorder_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsmall : orderOf (2 : ZMod p) < p - 1) : p ∣ a (p - 1) := by
  obtain ⟨hd0, hdp, hpd⟩ := order_facts hp hp2
  set d := orderOf (2 : ZMod p) with hd
  -- d ∈ Ico 1 (p-1)
  have hdmem : d ∈ Ico 1 (p - 1) := by rw [Finset.mem_Ico]; exact ⟨hd0, hsmall⟩
  -- p ∣ product
  have hpprod : p ∣ (Finset.Ico 1 (p - 1)).prod (fun k => 2 ^ k - 1) := by
    exact dvd_trans hpd (Finset.dvd_prod_of_mem _ hdmem)
  have hpnum : p ∣ num (p - 1) := by
    unfold num
    exact Dvd.dvd.mul_left hpprod _
  have hamul : a (p - 1) * (p - 1).factorial = num (p - 1) :=
    a_mul (p - 1) (by have := hp.two_le; omega)
  rw [← hamul] at hpnum
  rcases hp.dvd_mul.mp hpnum with h | h
  · exact h
  · exfalso
    rw [hp.dvd_factorial] at h
    have := hp.two_le; omega

-- digit sum of 2^a - 1 in base 2 is a
lemma digit_sum_two_pow (a : ℕ) : (Nat.digits 2 (2 ^ a - 1)).sum = a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hx : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have he : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    have hpos : 0 < 2 ^ (a + 1) - 1 := by omega
    have hstep : Nat.digits 2 (2 ^ (a + 1) - 1) = 1 :: Nat.digits 2 (2 ^ a - 1) := by
      rw [Nat.digits_def' (by norm_num) hpos]
      congr 1
      · omega
      · congr 1; omega
    rw [hstep, List.sum_cons, ih]; omega

lemma fact2_eq {a : ℕ} : ((2 ^ a - 1).factorial).factorization 2 = 2 ^ a - 1 - a := by
  have := Nat.sub_one_mul_factorization_factorial (n := 2 ^ a - 1) Nat.prime_two
  rw [digit_sum_two_pow a] at this
  simpa using this

lemma a_pos {m : ℕ} (hm : 1 ≤ m) : 0 < a m := by
  have h := a_mul m (by omega)
  have hnum := num_pos m
  rcases Nat.eq_zero_or_pos (a m) with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

lemma num_fact2 (m : ℕ) : (num m).factorization 2 = m - 1 := by
  rw [factorization_num m 2 Nat.prime_two, Nat.Prime.factorization_self Nat.prime_two, mul_one]
  have hsum0 : ∑ k ∈ Ico 1 m, (2 ^ k - 1).factorization 2 = 0 := by
    apply Finset.sum_eq_zero
    intro k hk; rw [Finset.mem_Ico] at hk
    apply Nat.factorization_eq_zero_of_not_dvd
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2^1 := by ring
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk.1
    have hodd : ¬ (2 ∣ 2 ^ k - 1) := by
      have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega : k ≠ 0)
      omega
    exact hodd
  rw [hsum0, add_zero]

lemma a_fact2 {m : ℕ} (hm : 1 ≤ m) :
    (a m).factorization 2 = (m - 1) - (m.factorial).factorization 2 := by
  have h := a_mul m (by omega)
  have hap : 0 < a m := a_pos hm
  have : (num m).factorization 2 = (a m).factorization 2 + (m.factorial).factorization 2 := by
    rw [← h, Nat.factorization_mul hap.ne' (Nat.factorial_ne_zero m)]
    simp
  rw [num_fact2] at this
  omega

lemma a_fact2_two_pow {e : ℕ} (he : 1 ≤ e) :
    (a (2 ^ e - 1)).factorization 2 = e - 1 := by
  have hm : 1 ≤ 2 ^ e - 1 := by
    have : 2 ≤ 2 ^ e := by
      calc 2 = 2^1 := by ring
      _ ≤ 2^e := Nat.pow_le_pow_right (by norm_num) he
    omega
  rw [a_fact2 hm, fact2_eq]
  have h1 : e < 2 ^ e := Nat.lt_two_pow_self
  omega

-- Power of 2 case
lemma pow2_not_dvd {e : ℕ} (he : 2 ≤ e) :
    ¬ (2 ^ e ∣ a (2 ^ e - 1) + 2 ^ (2 ^ e - 2)) := by
  intro hdvd
  -- 2^e ∣ 2^(2^e - 2)
  have hge : e ≤ 2 ^ e - 2 := by
    have hlt : e - 1 < 2 ^ (e - 1) := Nat.lt_two_pow_self
    have heq : 2 ^ e = 2 * 2 ^ (e - 1) := by
      conv_lhs => rw [show e = (e - 1) + 1 by omega]
      rw [pow_succ]; ring
    omega
  have hdvd2 : 2 ^ e ∣ 2 ^ (2 ^ e - 2) := pow_dvd_pow 2 hge
  have hdvda : 2 ^ e ∣ a (2 ^ e - 1) := by
    have := Nat.dvd_sub hdvd hdvd2
    simpa using this
  have he1 : 1 ≤ e := by omega
  have hapos : a (2 ^ e - 1) ≠ 0 := by
    have hge1 : 1 ≤ 2 ^ e - 1 := by
      have : 2 ≤ 2 ^ e := by
        calc 2 = 2^1 := by ring
        _ ≤ 2^e := Nat.pow_le_pow_right (by norm_num) he1
      omega
    exact (a_pos hge1).ne'
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hapos, a_fact2_two_pow he1] at hdvda
  omega

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
  -- Step 1: n is prime
  have hn2 : n ≠ 2 := by omega
  have hprime : Nat.Prime n := by
    by_contra hnp
    by_cases hodd : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ n
    · -- odd prime factor
      obtain ⟨p, hp, hp2, hpn⟩ := hodd
      have hpltn : p < n := by
        rcases (Nat.le_of_dvd (by omega) hpn).lt_or_eq with h | h
        · exact h
        · exact absurd (h ▸ hp) hnp
      have hpa : p ∣ a (n - 1) := composite_dvd hp hp2 hpn hpltn
      have hp2pow : ¬ p ∣ 2 ^ (n - 2) := by
        intro h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      have hpsum : p ∣ a (n - 1) + 2 ^ (n - 2) := dvd_trans hpn hdvd
      have : p ∣ 2 ^ (n - 2) := by
        have := Nat.dvd_sub hpsum hpa
        simpa using this
      exact hp2pow this
    · -- no odd prime factor ⟹ n is a power of 2
      push_neg at hodd
      have hall : ∀ {d}, Nat.Prime d → d ∣ n → d = 2 := by
        intro d hd hdn
        by_contra hd2
        exact (hodd d hd hd2) hdn
      have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : n ≠ 0) hall
      set e := n.primeFactorsList.length with he
      -- n = 2^e, n > 2 ⟹ e ≥ 2
      have he2 : 2 ≤ e := by
        by_contra h
        push_neg at h
        have hle : 2 ^ e ≤ 2 := by
          calc 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
        omega
      rw [hpow] at hdvd
      exact pow2_not_dvd he2 hdvd
  -- Step 2: primitive root
  refine ⟨hprime, ?_⟩
  rw [Nat.totient_prime hprime]
  obtain ⟨hd0, hdple, hpd⟩ := order_facts hprime hn2
  have hge : n - 1 ≤ orderOf (2 : ZMod n) := by
    by_contra hlt
    push_neg at hlt
    have hna : n ∣ a (n - 1) := prime_smallorder_dvd hprime hn2 hlt
    have hn2pow : ¬ n ∣ 2 ^ (n - 2) := by
      intro h
      exact hn2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 (hprime.dvd_of_dvd_pow h))
    have : n ∣ 2 ^ (n - 2) := by
      have := Nat.dvd_sub hdvd hna
      simpa using this
    exact hn2pow this
  have hord : orderOf (2 : ZMod n) = n - 1 := le_antisymm hdple hge
  exact IsPrimitiveRoot.iff_orderOf.mpr hord
