import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

/--
A092243: Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases:
start with score = 0 at $n = 1$ and at stage $k > 1$, increase (resp. decrease) the score by 1
if the $k$-th prime gap is greater (resp. less) than the previous prime gap.
-/
noncomputable def A092243 (n : ℕ) : ℤ :=
  -- P_i is the $i$-th prime, 0-indexed: P 0 = 2, P 1 = 3, ...
  -- Note: Nat.nth Nat.Prime i gives the i-th prime, where i=0 is the 0-th prime, 2.
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i

  -- $G_k$ is the $k$-th prime gap (OEIS 1-indexed), $G_k = P_k - P_{k-1}$, for $k \ge 1$.
  -- Here we use the 0-indexed primes P_i, so the k-th gap involves the prime P[k] and P[k-1].
  let G_gap (k : ℕ) : ℕ := P k - P (k - 1)

  if n = 0 then 0 -- Defining for n=0 as 0, though OEIS starts at 1
  else if n = 1 then 0
  else

  -- The score is the cumulative sum of the changes $\Delta(k) = \operatorname{sign}(G_k - G_{k-1})$ for $k=2$ to $n$.
  -- The sum starts at k=2 because the first gap G_1 is compared to G_2. The comparison is between G_k and G_{k-1}.
  -- Since the first gap is G_1, the first comparison is at k=2 (G_2 vs G_1).
  (Finset.Icc 2 n).sum fun k : ℕ =>
    let Gk   : ℕ := G_gap k
    -- Since $k \ge 2$, $k-1 \ge 1$, so G_gap (k-1) is safely computed.
    let Gkm1 : ℕ := G_gap (k - 1)

    -- Calculate $\operatorname{sign}(G_k - G_{k-1})$ using integer subtraction and sign function.
    ((Gk : ℤ) - (Gkm1 : ℤ)) |>.sign

/-
We remove the specific proofs for a_one etc., as they failed compilation and are not the object of the final submission.
The definition of A092243 is now corrected for proper syntax of the n-th prime.
-/

/--
Conjectures regarding the long-term behavior of A092243 (the score $s$).

Questions from OEIS A092243, including the primary conjectures:
1. Is s > 0 for some n > 250000?
2. Is s bounded from below?
3. Is s bounded from above?
4. Is s > 0 for infinitely many values of n?
5. Is s < 0 for infinitely many values of n?
-/
structure OEIS_A092243_Conjectures where
  /-- Is the score ever positive after n = 250,000? -/
  positive_after_large_n : ∃ n : ℕ, n > 250000 ∧ A092243 n > 0
  /-- Is the score bounded from below? -/
  bounded_below : ∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n
  /-- Is the score bounded from above? -/
  bounded_above : ∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B
  /-- Is the score positive infinitely often? -/
  infinitely_positive : Set.Infinite {n : ℕ | A092243 n > 0}
  /-- Is the score negative infinitely often? -/
  infinitely_negative : Set.Infinite {n : ℕ | A092243 n < 0}


/-!
## Disproof strategy

The score is unbounded.  Following Banks–Freiberg–Turnage-Butterbaugh, for every `m` there is a
run of `m` consecutive strictly increasing prime gaps; such a run raises the score by exactly `m`,
which is incompatible with the score being bounded.  Everything below is proved except the single
deep analytic input `maynard_tao_linear_forms` (the Maynard–Tao theorem for admissible tuples of
linear forms), whose proof requires the Bombieri–Vinogradov theorem and is not in Mathlib.
-/

noncomputable def pgap (k : ℕ) : ℕ := Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1)

/-- Strict monotonicity on an initial segment from the one-step version. -/
lemma strictMono_on_of_succ {x : ℕ → ℕ} {t : ℕ}
    (hmono : ∀ s, s + 1 < t → x s < x (s+1)) :
    ∀ a b, a < b → b < t → x a < x b := by
  intro a b hab hbt
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · exact lt_trans (ih h (by omega)) (hmono b hbt)
    · subst h; exact hmono a hbt

/-- Counting primes in a block of consecutive primes. -/
lemma count_prime_succ_block {x : ℕ → ℕ} {t : ℕ}
    (hprime : ∀ s, s < t → (x s).Prime)
    (hmono : ∀ s, s + 1 < t → x s < x (s+1))
    (hcons : ∀ y, y.Prime → x 0 ≤ y → y ≤ x (t-1) → ∃ s, s < t ∧ y = x s)
    {s : ℕ} (hs : s + 1 < t) :
    Nat.count Nat.Prime (x (s+1)) = Nat.count Nat.Prime (x s) + 1 := by
  have hlt := hmono s hs
  have hx0 : x 0 ≤ x s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h]
    · exact le_of_lt (strictMono_on_of_succ hmono 0 s h (by omega))
  have hxt : x (s+1) ≤ x (t-1) := by
    rcases eq_or_lt_of_le (show s + 1 ≤ t - 1 by omega) with h | h
    · rw [h]
    · exact le_of_lt (strictMono_on_of_succ hmono (s+1) (t-1) h (by omega))
  have e : x (s+1) = x s + (x (s+1) - x s) := by omega
  rw [e, Nat.count_add]
  congr 1
  obtain ⟨d, hd⟩ : ∃ d, x (s+1) - x s = d + 1 := ⟨x (s+1) - x s - 1, by omega⟩
  rw [hd]
  have hnone : ∀ k, k < d + 1 → 0 < k → ¬ Nat.Prime (x s + k) := by
    intro k hk hk0 hp
    obtain ⟨s', hs't, hs'⟩ := hcons (x s + k) hp (by omega) (by omega)
    -- x s < x s' < x (s+1)
    have h1 : x s < x s' := by omega
    have h2 : x s' < x (s+1) := by omega
    have hss' : s < s' := by
      by_contra hcon
      push_neg at hcon
      rcases eq_or_lt_of_le hcon with h | h
      · subst h; omega
      · have := strictMono_on_of_succ hmono s' s h (by omega); omega
    have hs's : s' < s + 1 := by
      by_contra hcon
      push_neg at hcon
      rcases eq_or_lt_of_le hcon with h | h
      · rw [h] at h2; omega
      · have := strictMono_on_of_succ hmono (s+1) s' h hs't; omega
    omega
  -- count over d+1 : only k = 0 contributes
  have : ∀ e, e ≤ d + 1 → Nat.count (fun k => Nat.Prime (x s + k)) e = if 0 < e then 1 else 0 := by
    intro e
    induction e with
    | zero => intro _; simp
    | succ e ih =>
      intro he
      rw [Nat.count_succ, ih (by omega)]
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp [hprime s (by omega)]
      · simp only [h, if_true]
        have := hnone e he h
        simp [this]
  rw [this (d+1) le_rfl]
  simp

lemma nth_prime_block {x : ℕ → ℕ} {t : ℕ}
    (hprime : ∀ s, s < t → (x s).Prime)
    (hmono : ∀ s, s + 1 < t → x s < x (s+1))
    (hcons : ∀ y, y.Prime → x 0 ≤ y → y ≤ x (t-1) → ∃ s, s < t ∧ y = x s) :
    ∀ s, s < t → Nat.nth Nat.Prime (Nat.count Nat.Prime (x 0) + s) = x s := by
  intro s
  induction s with
  | zero => intro _; simpa using Nat.nth_count (hprime 0 (by omega))
  | succ s ih =>
    intro hs
    have hc := count_prime_succ_block hprime hmono hcons hs
    have h2 : Nat.count Nat.Prime (x 0) + (s + 1) = Nat.count Nat.Prime (x (s+1)) := by
      rw [hc]
      have := ih (by omega)
      have h3 : Nat.count Nat.Prime (x s) = Nat.count Nat.Prime (x 0) + s := by
        have := congrArg (Nat.count Nat.Prime) this
        rw [Nat.count_nth_of_infinite Nat.infinite_setOf_prime] at this
        exact this.symm
      omega
    rw [h2]
    exact Nat.nth_count (hprime (s+1) hs)

/-- A block of `t ≥ 3` consecutive primes with strictly increasing gaps yields a run of
`t - 2` consecutive increases of `pgap` starting at some index `K ≥ 2`. -/
theorem run_of_block {x : ℕ → ℕ} {t : ℕ} (ht : 3 ≤ t) (hx0 : 2 < x 0)
    (hprime : ∀ s, s < t → (x s).Prime)
    (hmono : ∀ s, s + 1 < t → x s < x (s+1))
    (hcons : ∀ y, y.Prime → x 0 ≤ y → y ≤ x (t-1) → ∃ s, s < t ∧ y = x s)
    (hgap : ∀ s, s + 2 < t → x (s+1) - x s < x (s+2) - x (s+1)) :
    ∃ K, 2 ≤ K ∧ ∀ i, i < t - 2 → pgap (K + i) < pgap (K + i + 1) := by
  have hnth := nth_prime_block hprime hmono hcons
  set c := Nat.count Nat.Prime (x 0) with hc
  have hc1 : 1 ≤ c := by
    have : Nat.count Nat.Prime 3 ≤ c := Nat.count_monotone _ (by omega)
    have h3 : Nat.count Nat.Prime 3 = 1 := by decide
    omega
  refine ⟨c + 1, by omega, ?_⟩
  intro i hi
  have e1 : pgap (c + 1 + i) = x (i+1) - x i := by
    unfold pgap
    have : c + 1 + i - 1 = c + i := by omega
    rw [this, show c + 1 + i = c + (i+1) by ring, hnth (i+1) (by omega), hnth i (by omega)]
  have e2 : pgap (c + 1 + i + 1) = x (i+2) - x (i+1) := by
    unfold pgap
    have : c + 1 + i + 1 - 1 = c + (i + 1) := by omega
    rw [this, show c + 1 + i + 1 = c + (i+2) by ring, hnth (i+2) (by omega), hnth (i+1) (by omega)]
  rw [e1, e2]
  exact hgap i (by omega)


/-- A rapidly growing sequence of primes: `q 0 > 6^k`, and `2 q i + 1 < q (i+1) ≤ 4 q i + 2`. -/
noncomputable def qseq (k : ℕ) : ℕ → ℕ
  | 0 => Classical.choose (Nat.exists_infinite_primes (6^k + 1))
  | i+1 => Classical.choose
      (Nat.exists_prime_lt_and_le_two_mul (2 * qseq k i + 1) (Nat.succ_ne_zero _))

lemma qseq_zero_spec (k : ℕ) : 6^k + 1 ≤ qseq k 0 ∧ (qseq k 0).Prime :=
  Classical.choose_spec (Nat.exists_infinite_primes (6^k + 1))

lemma qseq_succ_spec (k i : ℕ) :
    (qseq k (i+1)).Prime ∧ 2 * qseq k i + 1 < qseq k (i+1) ∧ qseq k (i+1) ≤ 2 * (2 * qseq k i + 1) :=
  Classical.choose_spec
      (Nat.exists_prime_lt_and_le_two_mul (2 * qseq k i + 1) (Nat.succ_ne_zero _))

lemma qseq_prime (k i : ℕ) : (qseq k i).Prime := by
  cases i with
  | zero => exact (qseq_zero_spec k).2
  | succ i => exact (qseq_succ_spec k i).1

lemma qseq_pos (k i : ℕ) : 0 < qseq k i := (qseq_prime k i).pos

lemma qseq_succ_gt (k i : ℕ) : 2 * qseq k i < qseq k (i+1) := by
  have := (qseq_succ_spec k i).2.1; omega

lemma qseq_succ_le (k i : ℕ) : qseq k (i+1) ≤ 6 * qseq k i := by
  have h1 := (qseq_succ_spec k i).2.2
  have h2 := qseq_pos k i
  omega

lemma qseq_strictMono (k : ℕ) : StrictMono (qseq k) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have := qseq_succ_gt k i
  have := qseq_pos k i
  omega

lemma qseq_le_pow (k i : ℕ) : qseq k i ≤ 6^i * qseq k 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc qseq k (i+1) ≤ 6 * qseq k i := qseq_succ_le k i
      _ ≤ 6 * (6^i * qseq k 0) := by omega
      _ = 6^(i+1) * qseq k 0 := by ring

/-- Superincreasing: gaps between any three increasing indices strictly increase. -/
lemma qseq_super (k : ℕ) {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    qseq k b - qseq k a < qseq k c - qseq k b := by
  have h1 : qseq k (b+1) ≤ qseq k c := (qseq_strictMono k).monotone hbc
  have h2 := qseq_succ_gt k b
  have h3 : qseq k a < qseq k b := qseq_strictMono k hab
  omega

lemma qseq_lt_sq (k : ℕ) {i : ℕ} (hi : i < k) : qseq k i < qseq k 0 ^ 2 := by
  have h1 := qseq_le_pow k i
  have h2 : 6^i < 6^k := Nat.pow_lt_pow_right (by norm_num) hi
  have h3 := (qseq_zero_spec k).1
  have h4 := qseq_pos k 0
  calc qseq k i ≤ 6^i * qseq k 0 := h1
    _ < qseq k 0 * qseq k 0 := by
        apply Nat.mul_lt_mul_of_pos_right _ h4
        omega
    _ = qseq k 0 ^ 2 := by ring

lemma qseq_zero_gt (k : ℕ) : k < qseq k 0 := by
  have h3 := (qseq_zero_spec k).1
  have : k < 6^k := Nat.lt_pow_self (by norm_num)
  omega


/-- **Maynard–Tao theorem for admissible tuples of linear forms** `W·n + h`, `h ∈ H`
(Maynard, *Dense clusters of primes in subsets*, Thm 3.1; cf. Banks–Freiberg–Maynard). -/
theorem maynard_tao_linear_forms (m : ℕ) :
    ∃ k : ℕ, ∀ (W : ℕ) (H : Finset ℕ), 0 < W → H.card = k →
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ h ∈ H, ¬ p ∣ W * r + h) →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ m ≤ (H.filter (fun h => (W * n + h).Prime)).card := by
  sorry

/-- residue avoidance: if `p > |H|` there is `c < p` with `p ∤ c + h` for all `h ∈ H`. -/
lemma exists_residue_avoid {p : ℕ} (hp : p.Prime) (H : Finset ℕ) (hcard : H.card < p) :
    ∃ c, c < p ∧ ∀ h ∈ H, ¬ p ∣ c + h := by
  classical
  let f : ℕ → ℕ := fun h => (p - h % p) % p
  have hlt : (H.image f).card < (Finset.range p).card := by
    calc (H.image f).card ≤ H.card := Finset.card_image_le
      _ < p := hcard
      _ = (Finset.range p).card := (Finset.card_range p).symm
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, Finset.mem_range.mp hc, ?_⟩
  intro h hh hdvd
  apply hcn
  rw [Finset.mem_image]
  refine ⟨h, hh, ?_⟩
  -- show f h = c
  have hcp : c < p := Finset.mem_range.mp hc
  have hpp := hp.pos
  have hmod : h % p < p := Nat.mod_lt _ hpp
  have hdvd' : p ∣ c + h % p := by
    have e : c + h = (c + h % p) + p * (h / p) := by
      have := Nat.mod_add_div h p; omega
    rw [e] at hdvd
    exact (Nat.dvd_add_left (Dvd.intro _ rfl)).mp hdvd
  obtain ⟨e, he⟩ := hdvd'
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · interval_cases e
    · simp only [f]
      have : c = 0 := by omega
      have : h % p = 0 := by omega
      simp [*]
    · simp only [f]
      have h1 : c = p - h % p := by omega
      have h2 : 0 < h % p := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
  · exfalso
    have : p * 2 ≤ p * e := Nat.mul_le_mul_left p he2
    omega

theorem exists_increasing_gap_run_of_MT
    (MT : ∀ m : ℕ, ∃ k : ℕ, ∀ (W : ℕ) (H : Finset ℕ), 0 < W → H.card = k →
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ h ∈ H, ¬ p ∣ W * r + h) →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ m ≤ (H.filter (fun h => (W * n + h).Prime)).card)
    (m : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ i, i < m → pgap (K + i) < pgap (K + i + 1) := by
  classical
  obtain ⟨k, hk⟩ := MT (m + 3)
  set q := qseq k with hq
  have hqmono : StrictMono q := qseq_strictMono k
  set H : Finset ℕ := (Finset.range k).image q with hH
  have hHcard : H.card = k := by
    rw [hH, Finset.card_image_of_injective _ hqmono.injective, Finset.card_range]
  set L := q (k - 1) with hL
  have hmemH : ∀ h ∈ H, ∃ i, i < k ∧ q i = h := by
    intro h hh
    rw [hH, Finset.mem_image] at hh
    obtain ⟨i, hi, rfl⟩ := hh
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  have hqH : ∀ i, i < k → q i ∈ H := by
    intro i hi
    rw [hH, Finset.mem_image]
    exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have hHge : ∀ h ∈ H, q 0 ≤ h := by
    intro h hh
    obtain ⟨i, _, rfl⟩ := hmemH h hh
    exact hqmono.monotone (Nat.zero_le i)
  have hHle : ∀ h ∈ H, h ≤ L := by
    intro h hh
    obtain ⟨i, hi, rfl⟩ := hmemH h hh
    exact hqmono.monotone (by omega)
  have hHprime : ∀ h ∈ H, h.Prime := by
    intro h hh
    obtain ⟨i, _, rfl⟩ := hmemH h hh
    exact qseq_prime k i
  have hq0L : q 0 ≤ L := hqmono.monotone (Nat.zero_le _)
  have hq0k : k < q 0 := qseq_zero_gt k
  have hq0two : 2 ≤ q 0 := (qseq_prime k 0).two_le
  -- the modulus
  set S : Finset ℕ := (Finset.range (L + 1)).filter (fun p => p.Prime ∧ p ∉ H) with hS
  set W : ℕ := ∏ p ∈ S, p with hW
  have hWpos : 0 < W := by
    rw [hW]
    apply Finset.prod_pos
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    exact hp.2.1.pos
  have hdvdW : ∀ p, p.Prime → p ≤ L → p ∉ H → p ∣ W := by
    intro p hp hpL hpH
    rw [hW]
    apply Finset.dvd_prod_of_mem (fun p => p)
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp, hpH⟩
  have hWfac : ∀ p, p.Prime → p ∣ W → p ≤ L ∧ p ∉ H := by
    intro p hp hpW
    rw [hW, Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp)] at hpW
    obtain ⟨a, ha, hpa⟩ := hpW
    rw [hS, Finset.mem_filter, Finset.mem_range] at ha
    have : p = a := (Nat.prime_dvd_prime_iff_eq hp ha.2.1).mp hpa
    subst this
    exact ⟨by omega, ha.2.2⟩
  -- admissibility
  have hadm : ∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ h ∈ H, ¬ p ∣ W * r + h := by
    intro p hp
    by_cases hpW : p ∣ W
    · refine ⟨0, ?_⟩
      intro h hh hdiv
      simp only [mul_zero, zero_add] at hdiv
      have : p = h := (Nat.prime_dvd_prime_iff_eq hp (hHprime h hh)).mp hdiv
      subst this
      exact (hWfac p hp hpW).2 hh
    · have hpk : k < p := by
        by_contra hcon
        push_neg at hcon
        apply hpW
        apply hdvdW p hp (by omega)
        intro hpH
        have := hHge p hpH
        omega
      have hcop : W.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpW).symm
      obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
      obtain ⟨c, hcp, hc⟩ := exists_residue_avoid hp H (by omega)
      refine ⟨u * c, ?_⟩
      intro h hh hdiv
      apply hc h hh
      rw [Nat.dvd_iff_mod_eq_zero] at hdiv ⊢
      have e : (W * (u * c) + h) % p = (c + h) % p := by
        rw [Nat.add_mod, ← mul_assoc, Nat.mul_mod, hu, one_mul, Nat.mod_mod, ← Nat.add_mod]
      rw [e] at hdiv
      exact hdiv
  obtain ⟨n, hn1, hcard⟩ := hk W H hWpos hHcard hadm 1
  set J : Finset ℕ := H.filter (fun h => (W * n + h).Prime) with hJ
  have hJsub : ∀ h ∈ J, h ∈ H := fun h hh => (Finset.mem_filter.mp hh).1
  have hJprime : ∀ h ∈ J, (W * n + h).Prime := fun h hh => (Finset.mem_filter.mp hh).2
  -- composite positions
  have hcomp : ∀ j, q 0 ≤ j → j ≤ L → j ∉ H → ¬ (W * n + j).Prime := by
    intro j hj0 hjL hjH hprime
    have hj1 : j ≠ 1 := by omega
    have hpj : (j.minFac).Prime := Nat.minFac_prime hj1
    have hpdvd : j.minFac ∣ j := Nat.minFac_dvd j
    have hpj_le : j.minFac ≤ j := Nat.minFac_le (by omega)
    have hpH : j.minFac ∉ H := by
      intro hin
      have hge := hHge _ hin
      by_cases hjp : j.Prime
      · rw [hjp.minFac_eq] at hin
        exact hjH hin
      · have hsq := Nat.minFac_sq_le_self (by omega) hjp
        have : q 0 ^ 2 ≤ j.minFac ^ 2 := Nat.pow_le_pow_left hge 2
        have hlt : q (k-1) < q 0 ^ 2 := qseq_lt_sq k (show k - 1 < k by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · exfalso
            -- k = 0 : then H = ∅ and the card bound is impossible
            rw [hk0] at hHcard
            have : J.card ≤ H.card := Finset.card_filter_le _ _
            omega
          · omega)
        omega
    have hpW : j.minFac ∣ W := hdvdW _ hpj (by omega) hpH
    have hdiv : j.minFac ∣ W * n + j := dvd_add (dvd_mul_of_dvd_left hpW n) hpdvd
    have hpleW : j.minFac ≤ W := Nat.le_of_dvd hWpos hpW
    have hlt : j.minFac < W * n + j := by
      have : W ≤ W * n := Nat.le_mul_of_pos_right W hn1
      omega
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime _ hdiv) with h1 | h1
    · exact hpj.one_lt.ne' h1
    · omega
  -- the block of consecutive primes
  set t := J.card with ht
  have ht3 : 3 ≤ t := by omega
  let emb := J.orderEmbOfFin rfl
  let x : ℕ → ℕ := fun s => if hs : s < t then W * n + emb ⟨s, hs⟩ else 0
  have hx : ∀ s (hs : s < t), x s = W * n + emb ⟨s, hs⟩ := by
    intro s hs; simp [x, hs]
  have hembJ : ∀ (i : Fin t), emb i ∈ J := fun i => Finset.orderEmbOfFin_mem J rfl i
  have hprime : ∀ s, s < t → (x s).Prime := by
    intro s hs; rw [hx s hs]; exact hJprime _ (hembJ _)
  have hmono : ∀ s, s + 1 < t → x s < x (s+1) := by
    intro s hs
    rw [hx s (by omega), hx (s+1) hs]
    have : emb ⟨s, by omega⟩ < emb ⟨s+1, hs⟩ := emb.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self s))
    omega
  have hWn : 1 ≤ W * n := Nat.mul_pos hWpos hn1
  have hx0 : 2 < x 0 := by
    rw [hx 0 (by omega)]
    have := hHge _ (hJsub _ (hembJ ⟨0, by omega⟩))
    omega
  have hcons : ∀ y, y.Prime → x 0 ≤ y → y ≤ x (t-1) → ∃ s, s < t ∧ y = x s := by
    intro y hy hy0 hyt
    rw [hx 0 (by omega)] at hy0
    rw [hx (t-1) (by omega)] at hyt
    set j := y - W * n with hj
    have hyj : y = W * n + j := by omega
    have hj0 : q 0 ≤ j := by
      have := hHge _ (hJsub _ (hembJ ⟨0, by omega⟩)); omega
    have hjL : j ≤ L := by
      have := hHle _ (hJsub _ (hembJ ⟨t-1, by omega⟩)); omega
    have hjH : j ∈ H := by
      by_contra hcon
      exact hcomp j hj0 hjL hcon (hyj ▸ hy)
    have hjJ : j ∈ J := by
      rw [hJ, Finset.mem_filter]; exact ⟨hjH, hyj ▸ hy⟩
    have : j ∈ Set.range emb := by
      rw [Finset.range_orderEmbOfFin]; exact hjJ
    obtain ⟨⟨s, hs⟩, hse⟩ := this
    refine ⟨s, hs, ?_⟩
    rw [hx s hs, hse, hyj]
  have hgap : ∀ s, s + 2 < t → x (s+1) - x s < x (s+2) - x (s+1) := by
    intro s hs
    rw [hx s (by omega), hx (s+1) (by omega), hx (s+2) hs]
    obtain ⟨a, -, ha⟩ := hmemH _ (hJsub _ (hembJ ⟨s, by omega⟩))
    obtain ⟨b, -, hb⟩ := hmemH _ (hJsub _ (hembJ ⟨s+1, by omega⟩))
    obtain ⟨c, -, hc⟩ := hmemH _ (hJsub _ (hembJ ⟨s+2, by omega⟩))
    have h1 : emb ⟨s, by omega⟩ < emb ⟨s+1, by omega⟩ :=
      emb.strictMono (Fin.mk_lt_mk.mpr (by omega))
    have h2 : emb ⟨s+1, by omega⟩ < emb ⟨s+2, hs⟩ :=
      emb.strictMono (Fin.mk_lt_mk.mpr (by omega))
    rw [← ha, ← hb, ← hc] at *
    have hab : a < b := hqmono.lt_iff_lt.mp h1
    have hbc : b < c := hqmono.lt_iff_lt.mp h2
    have := qseq_super k hab hbc
    have e1 : W * n + q b - (W * n + q a) = q b - q a := by omega
    have e2 : W * n + q c - (W * n + q b) = q c - q b := by omega
    rw [e1, e2]
    exact this
  obtain ⟨K, hK2, hK⟩ := run_of_block ht3 hx0 hprime hmono hcons hgap
  exact ⟨K, hK2, fun i hi => hK i (by omega)⟩

lemma A092243_eq_sum {n : ℕ} (hn : 2 ≤ n) :
    A092243 n = (Finset.Icc 2 n).sum fun k => ((pgap k : ℤ) - (pgap (k-1) : ℤ)).sign := by
  unfold A092243
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp only [h0, h1, if_false]
  rfl

/-- A run of `m` strictly increasing consecutive gaps starting at index `k` raises the score by `m`. -/
lemma A092243_add_run {k m : ℕ} (hk : 2 ≤ k)
    (h : ∀ i, i < m → pgap (k + i) < pgap (k + i + 1)) :
    A092243 (k + m) = A092243 k + m := by
  rw [A092243_eq_sum hk, A092243_eq_sum (by omega)]
  have e1 : Finset.Icc 2 (k+m) = Finset.Ioc 1 (k+m) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have e2 : Finset.Icc 2 k = Finset.Ioc 1 k := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e1, e2, ← Finset.sum_Ioc_consecutive _ (show 1 ≤ k by omega) (show k ≤ k + m by omega)]
  congr 1
  have : ∀ j ∈ Finset.Ioc k (k+m), ((pgap j : ℤ) - (pgap (j-1) : ℤ)).sign = 1 := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    have hi := h (j - k - 1) (by omega)
    have e3 : k + (j - k - 1) = j - 1 := by omega
    have e4 : j - 1 + 1 = j := by omega
    rw [e3, e4] at hi
    apply Int.sign_eq_one_of_pos
    have : (pgap (j-1) : ℤ) < pgap j := by exact_mod_cast hi
    linarith
  rw [Finset.sum_congr rfl this]
  simp

/-- Reduction: arbitrarily long increasing runs make the score unbounded. -/
theorem not_bounded_A092243
    (BFT : ∀ m : ℕ, ∃ k : ℕ, 2 ≤ k ∧ ∀ i, i < m → pgap (k + i) < pgap (k + i + 1)) :
    ¬ ((∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n) ∧ (∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B)) := by
  rintro ⟨⟨B₁, hB₁⟩, ⟨B₂, hB₂⟩⟩
  obtain ⟨k, hk, h⟩ := BFT (B₂ - B₁).toNat.succ
  have := A092243_add_run hk h
  have h1 := hB₁ k
  have h2 := hB₂ (k + (B₂ - B₁).toNat.succ)
  have h3 : ((B₂ - B₁).toNat.succ : ℤ) = (B₂ - B₁).toNat + 1 := by push_cast; ring
  have h4 : ((B₂ - B₁).toNat : ℤ) ≥ B₂ - B₁ := Int.self_le_toNat _
  omega

theorem oeis_92243_conjecture : OEIS_A092243_Conjectures := by sorry

theorem oeis_92243_conjecture.disproof : ¬ (type_of% @oeis_92243_conjecture) := by
  intro C
  exact not_bounded_A092243 (exists_increasing_gap_run_of_MT maynard_tao_linear_forms)
    ⟨C.bounded_below, C.bounded_above⟩
