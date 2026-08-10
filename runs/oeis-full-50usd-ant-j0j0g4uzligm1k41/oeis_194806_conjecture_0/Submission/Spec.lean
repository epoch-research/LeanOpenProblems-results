import FormalConjectures.Util.ProblemImports

open Finset Nat

/-- The set of all products of elements from a Finset S. -/
def set_prod (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image fun p : ℕ × ℕ => p.fst * p.snd

/--
A194806: Size of the smallest subset $S$ of $T = \{1,2,3,\dots,n\}$ such that $S \cdot S$ contains $T$,
where $S \cdot S$ is the set of all products of elements of $S$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let T_n := Icc 1 n

    -- The set of subsets $S \subseteq T_n$ such that $T_n \subseteq S \cdot S$.
    let valid_subsets : Finset (Finset ℕ) :=
      T_n.powerset.filter (fun S : Finset ℕ => T_n ⊆ set_prod S)

    -- Proof that $T_n$ is guaranteed to be a valid subset, ensuring `valid_subsets` is non-empty.
    have T_n_is_valid : T_n ∈ valid_subsets := by
      apply mem_filter.mpr
      constructor
      -- 1. T_n ∈ T_n.powerset (i.e., T_n ⊆ T_n)
      apply mem_powerset.mpr; rfl
      -- 2. T_n ⊆ set_prod T_n
      intro k hk

      have one_le_n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
      have h1 : 1 ∈ T_n := mem_Icc.mpr ⟨Nat.le_refl 1, one_le_n⟩

      -- We show k = k * 1 is in set_prod T_n
      -- set_prod T_n is the image of T_n × T_n under multiplication.
      simp only [set_prod, mem_image, Prod.exists]
      use k, 1
      constructor
      -- Show that (k, 1) ∈ T_n × T_n
      · exact mem_product.mpr ⟨hk, h1⟩
      -- Show that k * 1 = k
      · exact Nat.mul_one k

    have h_nonempty : valid_subsets.Nonempty := ⟨T_n, T_n_is_valid⟩

    let sizes := valid_subsets.image Finset.card

    -- The min' function requires proof that the finset is non-empty.
    have h_sizes_nonempty : sizes.Nonempty := h_nonempty.image Finset.card

    -- We return the minimum card of all valid subsets.
    sizes.min' h_sizes_nonempty

open scoped Nat.Prime

namespace A194806Aux

/-- The central binomial coefficient is at most `(2m)^{π(2m)}`. -/
theorem centralBinom_le_pow (m : ℕ) (hm : 0 < m) :
    Nat.centralBinom m ≤ (2 * m) ^ (Nat.primeCounting (2 * m)) := by
  rw [← Nat.prod_pow_factorization_centralBinom m]
  -- bound each factor
  calc ∏ p ∈ Finset.range (2 * m + 1), p ^ (Nat.centralBinom m).factorization p
      ≤ ∏ p ∈ Finset.range (2 * m + 1), (if p.Prime then 2 * m else 1) := by
        apply Finset.prod_le_prod
        · intro p _; positivity
        · intro p hp
          by_cases hpp : p.Prime
          · simp only [hpp, if_true]
            -- p^{factorization} ≤ 2m
            have := Nat.pow_factorization_choose_le (n := 2 * m) (k := m) (p := p) (by omega)
            simpa [Nat.centralBinom] using this
          · simp only [hpp, if_false]
            rw [Nat.factorization_eq_zero_of_not_prime _ hpp, pow_zero]
    _ = (2 * m) ^ (Nat.primeCounting (2 * m)) := by
        rw [← Finset.prod_filter, Finset.prod_const]
        congr 1
        rw [show (Finset.filter (fun p => p.Prime) (Finset.range (2 * m + 1)))
              = Nat.primesBelow (2 * m + 1) from rfl,
            Nat.primesBelow_card_eq_primeCounting']
        rfl

/-- Chebyshev-type lower bound: for `N ≥ 8`,
`N ≤ (log₂ N + 1) * (π N + 1)`. -/
theorem cheb (N : ℕ) (hN : 8 ≤ N) :
    N ≤ (Nat.log 2 N + 1) * (Nat.primeCounting N + 1) := by
  set m := N / 2 with hm
  have hm4 : 4 ≤ m := by omega
  have h2mN : 2 * m ≤ N := by omega
  have hmN : m ≤ N := by omega
  -- central binomial inequalities
  have h1 : 4 ^ m < m * Nat.centralBinom m := Nat.four_pow_lt_mul_centralBinom m hm4
  have h2 : Nat.centralBinom m ≤ (2 * m) ^ (Nat.primeCounting (2 * m)) :=
    centralBinom_le_pow m (by omega)
  have hple : Nat.primeCounting (2 * m) ≤ Nat.primeCounting N :=
    Nat.monotone_primeCounting h2mN
  have h3 : (2 * m) ^ (Nat.primeCounting (2 * m)) ≤ N ^ (Nat.primeCounting N) := by
    calc (2 * m) ^ (Nat.primeCounting (2 * m))
        ≤ N ^ (Nat.primeCounting (2 * m)) := Nat.pow_le_pow_left h2mN _
      _ ≤ N ^ (Nat.primeCounting N) := Nat.pow_le_pow_right (by omega) hple
  -- combine
  have h4 : m * Nat.centralBinom m ≤ N ^ (Nat.primeCounting N + 1) := by
    calc m * Nat.centralBinom m
        ≤ N * (N ^ (Nat.primeCounting N)) := Nat.mul_le_mul hmN (h2.trans h3)
      _ = N ^ (Nat.primeCounting N + 1) := by rw [pow_succ]; ring
  have h5 : 2 ^ (N - 1) ≤ 4 ^ m := by
    calc 2 ^ (N - 1) ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 ^ m := by rw [pow_mul]; norm_num
  have h6 : 2 ^ (N - 1) < N ^ (Nat.primeCounting N + 1) := lt_of_le_of_lt h5 (lt_of_lt_of_le h1 h4)
  -- N < 2^(ℓ+1)
  have hNlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h7 : N ^ (Nat.primeCounting N + 1) ≤ 2 ^ ((Nat.log 2 N + 1) * (Nat.primeCounting N + 1)) := by
    calc N ^ (Nat.primeCounting N + 1)
        ≤ (2 ^ (Nat.log 2 N + 1)) ^ (Nat.primeCounting N + 1) :=
          Nat.pow_le_pow_left (le_of_lt hNlt) _
      _ = 2 ^ ((Nat.log 2 N + 1) * (Nat.primeCounting N + 1)) := by rw [← pow_mul]
  have h8 : 2 ^ (N - 1) < 2 ^ ((Nat.log 2 N + 1) * (Nat.primeCounting N + 1)) :=
    lt_of_lt_of_le h6 h7
  have h9 : N - 1 < (Nat.log 2 N + 1) * (Nat.primeCounting N + 1) := by
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp h8
    exact this
  omega

/-- `(k+1)^3 ≤ 2^(k+3)` for all `k`. -/
theorem cube_le (k : ℕ) : (k + 1) ^ 3 ≤ 2 ^ (k + 3) := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num
    · have hn2 : 9 ≤ n * n := Nat.mul_le_mul h h
      have hn3 : 9 * n ≤ n * n * n := Nat.mul_le_mul_right n hn2
      have hstep : (n + 2) ^ 3 ≤ 2 * (n + 1) ^ 3 := by nlinarith [h, hn3]
      calc (n + 1 + 1) ^ 3 = (n + 2) ^ 3 := by ring
        _ ≤ 2 * (n + 1) ^ 3 := hstep
        _ ≤ 2 * 2 ^ (n + 3) := by nlinarith [ih]
        _ = 2 ^ (n + 1 + 3) := by rw [show n + 1 + 3 = (n + 3) + 1 from rfl, pow_succ]; ring

/-- `(log₂ N + 1)^3 ≤ 8 N` for `N ≥ 1`. -/
theorem log_cube_le (N : ℕ) (hN : 1 ≤ N) : (Nat.log 2 N + 1) ^ 3 ≤ 8 * N := by
  have hlog : 2 ^ (Nat.log 2 N) ≤ N := Nat.pow_log_le_self 2 (by omega)
  calc (Nat.log 2 N + 1) ^ 3 ≤ 2 ^ (Nat.log 2 N + 3) := cube_le _
    _ = 2 ^ (Nat.log 2 N) * 8 := by rw [pow_add]; norm_num
    _ ≤ N * 8 := by gcongr
    _ = 8 * N := by ring

/-- Combined: `N^2 ≤ 8 (π N + 1)^3` for `N ≥ 2`. -/
theorem key_pi (N : ℕ) (hN : 2 ≤ N) :
    N ^ 2 ≤ 8 * (Nat.primeCounting N + 1) ^ 3 := by
  have hpi1 : 1 ≤ Nat.primeCounting N := by
    have : Nat.primeCounting 2 ≤ Nat.primeCounting N := Nat.monotone_primeCounting hN
    have h2 : Nat.primeCounting 2 = 1 := by decide
    omega
  rcases Nat.lt_or_ge N 8 with h | h
  · -- small N: N^2 ≤ 49 ≤ 64 ≤ 8*(π+1)^3
    have hb : 2 ≤ Nat.primeCounting N + 1 := by omega
    have hpow : (2 : ℕ) ^ 3 ≤ (Nat.primeCounting N + 1) ^ 3 := Nat.pow_le_pow_left hb 3
    have hN7 : N ≤ 7 := by omega
    calc N ^ 2 ≤ 49 := by nlinarith [hN7]
      _ ≤ 8 * 2 ^ 3 := by norm_num
      _ ≤ 8 * (Nat.primeCounting N + 1) ^ 3 := by gcongr
  · set a := Nat.log 2 N + 1 with ha
    set b := Nat.primeCounting N + 1 with hb
    have c1 : N ≤ a * b := cheb N h
    have c2 : a ^ 3 ≤ 8 * N := log_cube_le N (by omega)
    have e1 : N * N ≤ (a * b) * (a * b) := Nat.mul_le_mul c1 c1
    have e2 : a * a ≤ 8 * b := by
      have t1 : a ^ 3 ≤ 8 * (a * b) := le_trans c2 (by nlinarith [c1])
      have t2 : a * (a * a) ≤ a * (8 * b) := by nlinarith [t1]
      exact Nat.le_of_mul_le_mul_left t2 (by omega)
    nlinarith [e1, e2, Nat.zero_le b]

theorem mem_set_prod {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) :
    a * b ∈ set_prod S := by
  simp only [set_prod, Finset.mem_image, Prod.exists]
  exact ⟨a, b, Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

theorem a_le_card (n : ℕ) (hn : n ≠ 0) (S : Finset ℕ)
    (hsub : S ⊆ Icc 1 n) (hcov : Icc 1 n ⊆ set_prod S) :
    a n ≤ S.card := by
  have hSmem : S ∈ (Icc 1 n).powerset.filter (fun S : Finset ℕ => Icc 1 n ⊆ set_prod S) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hsub, hcov⟩
  unfold a
  rw [dif_neg hn]
  apply Finset.min'_le
  exact Finset.mem_image_of_mem _ hSmem

/-- The covering set. -/
def Scov (n K : ℕ) : Finset ℕ :=
  Finset.Icc 1 K ∪ (Finset.Icc 1 n).filter Nat.Prime

theorem coverage (n K : ℕ) (hn : 1 ≤ n) (hK1 : 1 ≤ K) (hKn : K ≤ n)
    (hK3 : n ^ 2 ≤ K ^ 3) :
    ∀ m, 1 ≤ m → m ≤ n → m ∈ set_prod (Scov n K) := by
  intro m hm1 hmn
  -- the finset of divisors of m that are ≤ K
  have hm0 : m ≠ 0 := by omega
  set D := (m.divisors).filter (fun t => t ≤ K) with hD
  have h1mem : 1 ∈ D := by
    rw [hD, Finset.mem_filter]
    exact ⟨Nat.one_mem_divisors.mpr hm0, hK1⟩
  have hDne : D.Nonempty := ⟨1, h1mem⟩
  set d := D.max' hDne with hd
  have hd_mem : d ∈ D := D.max'_mem hDne
  have hd_dvd : d ∣ m := by
    have := (Finset.mem_filter.mp hd_mem).1
    exact (Nat.mem_divisors.mp this).1
  have hd_leK : d ≤ K := (Finset.mem_filter.mp hd_mem).2
  have hd_pos : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso; rw [h] at hd_dvd; exact hm0 (Nat.eq_zero_of_zero_dvd hd_dvd)
    · exact h
  set e := m / d with he
  have hde : d * e = m := Nat.mul_div_cancel' hd_dvd
  have he_pos : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso; rw [h, Nat.mul_zero] at hde; omega
    · exact h
  have he_len : e ≤ n := by
    have : e ≤ m := by nlinarith [hde, hd_pos, he_pos]
    omega
  -- maximality: any divisor ≤ K is ≤ d
  have hmax : ∀ t, t ∣ m → t ≤ K → t ≤ d := by
    intro t ht htK
    apply Finset.le_max'
    rw [hD, Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨ht, hm0⟩, htK⟩
  -- d ∈ S
  have hdS : d ∈ Scov n K := by
    rw [Scov, Finset.mem_union]
    left; exact Finset.mem_Icc.mpr ⟨hd_pos, hd_leK⟩
  -- now show e ∈ S
  have heS : e ∈ Scov n K := by
    by_cases hek : e ≤ K
    · -- e ≤ K
      rw [Scov, Finset.mem_union]
      left; exact Finset.mem_Icc.mpr ⟨he_pos, hek⟩
    · -- e > K, show e prime
      have hek : K < e := by omega
      have heprime : e.Prime := by
        by_contra hnp
        -- e ≥ 2
        have he2 : 2 ≤ e := by omega
        set q := e.minFac with hq
        have hqp : q.Prime := Nat.minFac_prime (by omega)
        have hq2 : 2 ≤ q := hqp.two_le
        have hqe : q ∣ e := Nat.minFac_dvd e
        have hqsq : q ^ 2 ≤ e := Nat.minFac_sq_le_self (by omega) hnp
        -- d*q divides m
        have hdq_dvd : d * q ∣ m := by
          rw [← hde]; exact Nat.mul_dvd_mul_left d hqe
        -- d*q > K
        have hdqK : K < d * q := by
          by_contra hle
          push_neg at hle
          have := hmax (d * q) hdq_dvd hle
          nlinarith [hd_pos, hq2]
        -- (K+1)^2 ≤ d*n
        have hI : (K + 1) ^ 2 ≤ d * n := by
          have step1 : (d * q) ^ 2 ≤ d * m := by
            have : (d * q) ^ 2 = d * (d * (q ^ 2)) := by ring
            rw [this]
            calc d * (d * (q ^ 2)) ≤ d * (d * e) := by
                  apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; exact hqsq
              _ = d * m := by rw [hde]
          have step2 : (K + 1) ^ 2 ≤ (d * q) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          calc (K + 1) ^ 2 ≤ (d * q) ^ 2 := step2
            _ ≤ d * m := step1
            _ ≤ d * n := by apply Nat.mul_le_mul_left; exact hmn
        -- d*(K+1) ≤ n
        have hII : d * (K + 1) ≤ n := by
          calc d * (K + 1) ≤ d * e := by apply Nat.mul_le_mul_left; omega
            _ = m := hde
            _ ≤ n := hmn
        -- combine: (K+1)^3 ≤ n^2
        have hcube : (K + 1) ^ 3 ≤ n ^ 2 := by
          have : (K + 1) ^ 3 = (K + 1) * (K + 1) ^ 2 := by ring
          rw [this]
          calc (K + 1) * (K + 1) ^ 2 ≤ (K + 1) * (d * n) := by
                apply Nat.mul_le_mul_left; exact hI
            _ = n * (d * (K + 1)) := by ring
            _ ≤ n * n := by apply Nat.mul_le_mul_left; exact hII
            _ = n ^ 2 := by ring
        nlinarith [hcube, hK3]
      rw [Scov, Finset.mem_union]
      right
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨he_pos, he_len⟩, heprime⟩
  -- conclude
  have : d * e = m := hde
  rw [← this]
  exact mem_set_prod hdS heS

theorem card_prime_filter (n : ℕ) :
    (Finset.filter Nat.Prime (Finset.Icc 1 n)).card = Nat.primeCounting n := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  congr 1
  rw [Nat.primesBelow]
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, hxn⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨hx, hp⟩
    have := hp.two_le
    exact ⟨⟨by omega, by omega⟩, hp⟩

theorem Scov_sub (n K : ℕ) (hKn : K ≤ n) : Scov n K ⊆ Finset.Icc 1 n := by
  rw [Scov]
  apply Finset.union_subset
  · intro x hx
    rw [Finset.mem_Icc] at hx ⊢; omega
  · exact Finset.filter_subset _ _

theorem Scov_card (n K : ℕ) : (Scov n K).card ≤ K + Nat.primeCounting n := by
  rw [Scov]
  calc (Finset.Icc 1 K ∪ Finset.filter Nat.Prime (Finset.Icc 1 n)).card
      ≤ (Finset.Icc 1 K).card + (Finset.filter Nat.Prime (Finset.Icc 1 n)).card :=
        Finset.card_union_le _ _
    _ = K + Nat.primeCounting n := by rw [Nat.card_Icc, card_prime_filter]; omega

theorem main_nat (n : ℕ) (hn : 2 ≤ n) : a n ≤ 5 * Nat.primeCounting n := by
  have hn1 : 1 ≤ n := by omega
  have hpi1 : 1 ≤ Nat.primeCounting n := by
    have h := Nat.monotone_primeCounting hn
    have h2 : Nat.primeCounting 2 = 1 := by decide
    omega
  have hex : n ^ 2 ≤ n ^ 3 := by nlinarith [hn1]
  have hpred : ∃ k, n ^ 2 ≤ k ^ 3 := ⟨n, hex⟩
  set K := Nat.find hpred with hK
  have hKspec : n ^ 2 ≤ K ^ 3 := Nat.find_spec hpred
  have hKn : K ≤ n := Nat.find_min' hpred hex
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · exfalso; rw [h] at hKspec; norm_num at hKspec; nlinarith [hn1, hKspec]
    · exact h
  have hKpi : K ≤ 2 * (Nat.primeCounting n + 1) := by
    apply Nat.find_min' hpred
    calc n ^ 2 ≤ 8 * (Nat.primeCounting n + 1) ^ 3 := key_pi n hn
      _ = (2 * (Nat.primeCounting n + 1)) ^ 3 := by ring
  have hcov : Icc 1 n ⊆ set_prod (Scov n K) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact coverage n K hn1 hK1 hKn hKspec m hm.1 hm.2
  have hsub : Scov n K ⊆ Icc 1 n := Scov_sub n K hKn
  have h1 : a n ≤ (Scov n K).card := a_le_card n (by omega) (Scov n K) hsub hcov
  have h2 : (Scov n K).card ≤ K + Nat.primeCounting n := Scov_card n K
  omega

end A194806Aux

/--
**OEIS A194806 Conjecture:** Is $a(n)/\pi(n)$ bounded as $n \to \infty$?
(Where $\pi(n) = A000720(n)$ is the prime counting function `Nat.primeCounting n`).
-/
theorem oeis_194806_conjecture_0 :
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    (a n : ℝ) / (Nat.primeCounting n : ℝ) ≤ C :=
  by
  refine ⟨5, ?_⟩
  intro n hn
  have hpi1 : 1 ≤ Nat.primeCounting n := by
    have h := Nat.monotone_primeCounting hn
    have h2 : Nat.primeCounting 2 = 1 := by decide
    omega
  have hmain : a n ≤ 5 * Nat.primeCounting n := A194806Aux.main_nat n hn
  have hpos : (0 : ℝ) < (Nat.primeCounting n : ℝ) := by
    have : (1 : ℝ) ≤ (Nat.primeCounting n : ℝ) := by exact_mod_cast hpi1
    linarith
  rw [div_le_iff₀ hpos]
  have hcast : (a n : ℝ) ≤ ((5 * Nat.primeCounting n : ℕ) : ℝ) := by exact_mod_cast hmain
  push_cast at hcast
  linarith [hcast]

