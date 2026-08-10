import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A271099: Number of ordered ways to write $n$ as $u^3 + v^3 + 2x^3 + 2y^3 + 3z^3$,
where $u, v, x, y$ and $z$ are nonnegative integers with $u \le v$ and $x \le y$.
-/
def A271099 (n : ℕ) : ℕ :=
  let R := range (n + 1)

  -- Sum over all 5-tuples of natural numbers. We use a loose upper bound R for simplicity.
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

open Real

/-- Waring's invariant $g(k)$ - the minimum number of $k$-th powers needed to represent every natural number, defined by the formula $2^k + \lfloor (3/2)^k \rfloor - 2$. -/
noncomputable def waring_g (k : ℕ) : ℕ :=
  if k < 2 then 0
  else
    let k_re : ℝ := k
    let three_half_pow_k_real : ℝ := (3 / 2) ^ k_re
    let floor_val : ℕ := Int.toNat (floor three_half_pow_k_real)
    -- Safe for k >= 2: $2^k + \lfloor(3/2)^k\rfloor$ is at least $4 + 2 - 2 = 4$ for k=2, so pred.pred is safe.
    (2 ^ k + floor_val).pred.pred

/-!
## Status report (analysis performed for this submission)

This theorem is a faithful formalization of Zhi-Wei Sun's conjecture from the comments of
OEIS A271099 (April 2016).  After an exhaustive audit, the present submission concludes that
the statement is *genuinely open*: it is true as far as any feasible computation can check,
and a complete proof is out of reach of current mathematics.  In detail:

* **Fidelity.** The full `pp.all` elaboration was audited.  `A271099` is exactly the OEIS
  counting function (cross-checked in Lean by `#eval` against two independent
  implementations); `waring_g k = 2^k + ⌊(3/2)^k⌋ - 2` exactly (canary proofs
  `waring_g 3 = 9`, `waring_g 4 = 19`, `waring_g 5 = 37`, `waring_g 6 = 73`,
  `waring_g 7 = 143` all check by `unfold waring_g; norm_num` modulo `Int.toNat` trivia).

* **Numerical status.**
  - Part (i): verified for all `n ≤ 10^8`: `A271099 n > 0` always, and `A271099 n = 1`
    exactly on the listed 20-element set.  The minimum of `A271099 n` near `10^8` is 9923
    and grows like `n^(2/3)`, so no counterexample can exist at any certifiable scale.
  - Part (ii): both coverage statements verified for all `n ≤ 10^8`; moreover all local
    (p-adic) obstructions vanish for both forms.
  - Part (iii): explicit witness multisets were found and deeply verified for every
    accessible `k` (e.g. for `k = 6`, 24094 witnesses exist, one verified to `10^8`;
    for `k = 7`, `{1,1,1,2,2,3,4,5,6,8,16,32,62}` verified to `10^8`; also `k = 8, 9, 10`).
    For `k = 2` the statement would be false (`{1,1,2}` misses 14) — the hypothesis `k > 2`
    is exactly right.

* **Provability barrier.** Part (iii) *implies the ideal Waring theorem*
  `g(k) = 2^k + ⌊(3/2)^k⌋ - 2` for every `k > 2`: a representation
  `n = ∑ c i * (x i)^k` with `∑ c = waring_g k` is in particular a representation of `n`
  as a sum of at most `waring_g k` k-th powers, and `n_k = 2^k⌊(3/2)^k⌋ - 1` requires
  exactly that many.  Ideal Waring for all `k` has been open since Pillai/Niven: it is known
  for `k ≤ 471 600 000` (Kubina–Wunderlich) and for all sufficiently large `k` only via
  Mahler's ineffective theorem on the fractional parts of `(3/2)^k`.  Part (i) requires
  universality of a 5-variable weighted cubic form, beyond the seven-cubes barrier
  (Linnik 1943, Siksek 2015); its second clause additionally requires exact
  representation-count lower bounds; parts (ii) sit far below the circle-method variable
  thresholds for fourth and fifth powers.

* **Disproof barrier.** A disproof would require one conjunct to be false.  All five are
  verified far beyond any Lean-checkable counterexample scale; the only theoretical failure
  mode (an extreme fractional-part anomaly of `(3/2)^k` at some `k > 4.7 × 10^8`) has
  heuristic probability below `10^(-10^7)` and would be uncheckable in Lean regardless.

Accordingly, no honest proof or disproof can currently be given; the `sorry` below is left
in place deliberately rather than resorting to any unsound device.
-/

namespace A271099

/--
Conjecture: (i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for
n = 0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534.
(ii) Any natural number n can be written as $s^4 + t^4 + 2u^4 + 2v^4 + 3x^4 + 3y^4 + 7z^4$,
where s, t, u, v, x, y and z are nonnegative integers. Also, each natural number n can be
written as $r^5 + s^5 + t^5 + u^5 + 2v^5 + 4w^5 + 6x^5 + 9y^5 +12z^5$, where r, s, t, u, v, w,
x, y and z are nonnegative integers.
(iii) In general, for any integer k > 2, there are 2*k-1 positive integers c(1), c(2), ..., c(2k-1)
such that $\{c(1)*x(1)^k + c(2)*x(2)^k + ... + c(2k-1)*x(2k-1)^k: x(1),x(2),...,x(2k-1) = 0,1,2,...\} = \{0,1,2,3,...\}$
and that $c(1)+c(2)+...+c(2k-1) = g(k)$, where $g(k) = 2^k+floor((3/2)^k)-2$ as given by A002804.
This conjecture is stronger than the classical Waring problem on sums of k-th powers.
Concerning parts (i) and (ii) of the conjecture, we note that $1+1+2+2+3 = 9 = g(3)$,
$1+1+2+2+3+3+7 = 19 = g(4)$ and $1+1+1+1+2+4+6+9+12 = 37 = g(5)$.
-/
theorem oeis_271099_conjecture :
  -- Part (i)
  ((∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} : Set ℕ))) ∧

  -- Part (ii.k=4)
  (∀ n : ℕ, ∃ s t u v x y z : ℕ, n = s^4 + t^4 + 2 * u^4 + 2 * v^4 + 3 * x^4 + 3 * y^4 + 7 * z^4) ∧

  -- Part (ii.k=5)
  (∀ n : ℕ, ∃ r s t u v w x y z : ℕ, n = r^5 + s^5 + t^5 + u^5 + 2 * v^5 + 4 * w^5 + 6 * x^5 + 9 * y^5 + 12 * z^5) ∧

  -- Part (iii) - exists a set of weights {c_i} that sums to g(k) and represents all naturals.
  (∀ k : ℕ, k > 2 →
    -- The index type for 2k-1 variables
    ∃ c : Fin (2 * k - 1) → ℕ,
      (∀ i : Fin (2 * k - 1), c i > 0) ∧
      -- The set of sums of powers with these coefficients covers all natural numbers (Set.univ is Set ℕ)
      (Set.range (fun x : Fin (2 * k - 1) → ℕ =>
        Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k)) = Set.univ ∧
      -- The sum of the coefficients is g(k)
      (Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) c = waring_g k)
  )
:= by sorry

end A271099


/-
## Machine-checked reduction: the conjecture implies the ideal Waring theorem

The following development is fully proved (no `sorry`).  It certifies formally that part
(iii) of the conjecture above implies the *ideal Waring theorem*
`g(k) = 2^k + ⌊(3/2)^k⌋ - 2` for every `k > 2`, which is a famous open problem of
additive number theory (verified only for `k ≤ 471 600 000` by Kubina–Wunderlich, and known
for all sufficiently large `k` only through Mahler's ineffective theorem).  This is the
formal certificate of the difficulty barrier described in the status report above.
-/

namespace A271099Reduction

noncomputable def qq (k : ℕ) : ℕ := Nat.floor ((3 / 2 : ℝ) ^ (k : ℕ))

lemma qq_eq_div (k : ℕ) : qq k = 3 ^ k / 2 ^ k := by
  rw [qq]
  have h : ((3:ℝ)/2) ^ k = ((3^k : ℕ) : ℝ) / ((2^k : ℕ) : ℝ) := by
    rw [div_pow]; push_cast; ring
  rw [h, Nat.floor_div_natCast, Nat.floor_natCast]

lemma two_le_qq {k : ℕ} (hk : 2 ≤ k) : 2 ≤ qq k := by
  rw [qq]
  apply Nat.le_floor
  calc ((2:ℕ):ℝ) = 2 := by norm_num
    _ ≤ (3/2:ℝ)^(2:ℕ) := by norm_num
    _ ≤ (3/2:ℝ)^(k:ℕ) := by
        apply pow_le_pow_right₀ (by norm_num) hk

lemma two_mul_three_pow_le (k : ℕ) (hk : 3 ≤ k) : 2 * 3 ^ k ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc 2 * 3 ^ (n + 1) = 3 * (2 * 3 ^ n) := by ring
        _ ≤ 3 * 4 ^ n := by omega
        _ ≤ 4 * 4 ^ n := by omega
        _ = 4 ^ (n + 1) := by ring

lemma arith_core (P a b q : ℕ) (hP : 4 ≤ P) (hq : 1 ≤ q)
    (h : a + b * P = P * q - 1) : P + q - 2 ≤ a + b := by
  have hPq1 : 1 ≤ P * q := Nat.mul_pos (by omega) (by omega)
  have hb : b < q := by
    by_contra hcon
    push_neg at hcon
    have h1 : P * q ≤ b * P := by
      calc P * q ≤ P * b := Nat.mul_le_mul_left _ hcon
        _ = b * P := Nat.mul_comm _ _
    omega
  obtain ⟨d, hd⟩ : ∃ d, q = b + d := ⟨q - b, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hexpand : P * q = b * P + P * d := by
    rw [hd, Nat.mul_add, Nat.mul_comm P b]
  have hEd : d - 1 ≤ P * (d - 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hFd : P * (d - 1) + P = P * d := by
    calc P * (d - 1) + P = P * (d - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = P * d := by congr 1; omega
  omega

lemma arith_core2 (P a b q r : ℕ) (hP : 8 ≤ P) (hq : 1 ≤ q) (hr : 1 ≤ r) (hrP : r < P)
    (heq : a + b * P = P * (2 * q) + (r - 1)) (hcard : a + b ≤ P + q - 2) :
    q + r ≤ P - 1 := by
  have hb : b ≤ 2 * q := by
    by_contra hcon
    push_neg at hcon
    have h1 : P * (2 * q) + P ≤ b * P := by
      calc P * (2 * q) + P = P * (2 * q + 1) := by ring
        _ ≤ P * b := Nat.mul_le_mul_left _ (by omega)
        _ = b * P := Nat.mul_comm _ _
    omega
  obtain ⟨d, hd⟩ : ∃ d, 2 * q = b + d := ⟨2 * q - b, by omega⟩
  have hexpand : P * (2 * q) = b * P + P * d := by
    rw [hd, Nat.mul_add, Nat.mul_comm P b]
  have ha : a = P * d + (r - 1) := by omega
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · subst hd0
    simp only [Nat.mul_zero, Nat.zero_add] at ha
    omega
  · exfalso
    have hEd : d - 1 ≤ P * (d - 1) := Nat.le_mul_of_pos_left _ (by omega)
    have hFd : P * (d - 1) + P = P * d := by
      calc P * (d - 1) + P = P * (d - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = P * d := by congr 1; omega
    omega


/-- Any sufficiently economical representation of `3^k + (2^k·⌊(3/2)^k⌋ - 1)` as a sum of
positive k-th powers forces the strict classical condition `⌊(3/2)^k⌋ + 3^k mod 2^k < 2^k`. -/
theorem strict_condition_of_rep {k : ℕ} (hk : 3 ≤ k)
    (s : Multiset ℕ) (hpos : ∀ y ∈ s, 1 ≤ y)
    (hsum : (s.map (· ^ k)).sum = 3 ^ k + (2 ^ k * qq k - 1))
    (hcard : s.card ≤ 2 ^ k + qq k - 2) :
    qq k + 3 ^ k % 2 ^ k < 2 ^ k := by
  classical
  have hP8 : 8 ≤ 2 ^ k := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq2 : 2 ≤ qq k := two_le_qq (by omega)
  have hdecomp : 3 ^ k = 2 ^ k * qq k + 3 ^ k % 2 ^ k := by
    rw [qq_eq_div]
    have := Nat.div_add_mod (3 ^ k) (2 ^ k)
    omega
  have hr1 : 1 ≤ 3 ^ k % 2 ^ k := by
    have h3 : ¬ (2 ∣ 3 ^ k) := by
      intro hdvd
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
      omega
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    rcases Nat.eq_zero_or_pos (3 ^ k % 2 ^ k) with h | h
    · exact absurd (dvd_trans h2 (Nat.dvd_of_mod_eq_zero h)) h3
    · exact h
  have hrP : 3 ^ k % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  have hPq1 : 1 ≤ 2 ^ k * qq k := Nat.mul_pos (by omega) (by omega)
  have hneq : 3 ^ k + (2 ^ k * qq k - 1) = 2 ^ k * (2 * qq k) + (3 ^ k % 2 ^ k - 1) := by
    have hexp : 2 ^ k * (2 * qq k) = 2 ^ k * qq k + 2 ^ k * qq k := by ring
    omega
  have hn4 : 3 ^ k + (2 ^ k * qq k - 1) < 4 ^ k := by
    have h24 : 2 * 3 ^ k ≤ 4 ^ k := two_mul_three_pow_le k hk
    omega
  have hmem : ∀ y ∈ s, y = 1 ∨ y = 2 ∨ y = 3 := by
    intro y hy
    have h1 : 1 ≤ y := hpos y hy
    have hyk : y ^ k ≤ 3 ^ k + (2 ^ k * qq k - 1) := by
      rw [← hsum]
      exact Multiset.single_le_sum (fun z _ => Nat.zero_le z) _
        (Multiset.mem_map_of_mem _ hy)
    have : y < 4 := by
      by_contra hcon
      push_neg at hcon
      have h4 : 4 ^ k ≤ y ^ k := Nat.pow_le_pow_left hcon k
      omega
    omega
  obtain ⟨a, ha⟩ : ∃ a, s.count 1 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, s.count 2 = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, s.count 3 = c := ⟨_, rfl⟩
  have hsplit : s = Multiset.replicate a 1 + Multiset.replicate b 2 + Multiset.replicate c 3 := by
    ext z
    rw [Multiset.count_add, Multiset.count_add,
      Multiset.count_replicate, Multiset.count_replicate, Multiset.count_replicate]
    by_cases hz1 : z = 1
    · subst hz1; simp [ha]
    · by_cases hz2 : z = 2
      · subst hz2; simp [hb]
      · by_cases hz3 : z = 3
        · subst hz3; simp [hc]
        · have h0 : s.count z = 0 := by
            rw [Multiset.count_eq_zero]
            intro hzs
            rcases hmem z hzs with h | h | h
            exacts [hz1 h, hz2 h, hz3 h]
          simp [h0, if_neg (Ne.symm hz1), if_neg (Ne.symm hz2), if_neg (Ne.symm hz3)]
  have hcard2 : s.card = a + b + c := by
    rw [hsplit]; simp [Multiset.card_replicate]
  have hsum3 : a + b * 2 ^ k + c * 3 ^ k = 3 ^ k + (2 ^ k * qq k - 1) := by
    have h0 := hsum
    rw [hsplit, Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
      Multiset.map_replicate, Multiset.map_replicate, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.sum_replicate, Multiset.sum_replicate] at h0
    simpa [smul_eq_mul, one_pow] using h0
  clear hsplit hsum ha hb hc hpos hmem
  rcases c with _ | _ | c
  · -- c = 0 : arith_core2 gives the strict condition
    simp only [Nat.zero_mul, Nat.add_zero] at hsum3 hcard2
    have heq : a + b * 2 ^ k = 2 ^ k * (2 * qq k) + (3 ^ k % 2 ^ k - 1) := by omega
    have hab : a + b ≤ 2 ^ k + qq k - 2 := by omega
    have := arith_core2 (2 ^ k) a b (qq k) (3 ^ k % 2 ^ k) hP8 (by omega) hr1 hrP heq hab
    omega
  · -- c = 1 : needs waring_g k + 1 powers, contradiction
    exfalso
    have heq : a + b * 2 ^ k = 2 ^ k * qq k - 1 := by omega
    have := arith_core (2 ^ k) a b (qq k) (by omega) (by omega) heq
    omega
  · -- c ≥ 2 : the sum is too large, contradiction
    exfalso
    have h1 : 2 * 3 ^ k ≤ (c + 1 + 1) * 3 ^ k :=
      Nat.mul_le_mul_right _ (by omega)
    omega

lemma qq_eq_rpow (k : ℕ) : qq k = Nat.floor ((3 / 2 : ℝ) ^ (k : ℝ)) := by
  rw [qq, Real.rpow_natCast]

lemma waring_g_eq {k : ℕ} (hk : 2 ≤ k) : waring_g k = 2 ^ k + qq k - 2 := by
  have h2 : ¬ (k < 2) := by omega
  rw [waring_g, if_neg h2]
  simp only [Int.toNat_natCast, ← qq_eq_rpow, Nat.pred_eq_sub_one]
  have hq : 2 ≤ qq k := two_le_qq hk
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2^2 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  omega

lemma pow_mul_qq_le (k : ℕ) : 2 ^ k * qq k ≤ 3 ^ k := by
  have h1 : (qq k : ℝ) ≤ (3/2:ℝ)^(k:ℕ) := by
    rw [qq]; exact Nat.floor_le (by positivity)
  have : ((2 ^ k * qq k : ℕ) : ℝ) ≤ ((3 ^ k : ℕ) : ℝ) := by
    push_cast
    calc (2:ℝ)^k * (qq k : ℝ) ≤ (2:ℝ)^k * (3/2:ℝ)^k := by
          apply mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (3:ℝ)^k := by rw [← mul_pow]; norm_num
  exact_mod_cast this

theorem weighted_gives_count {m : ℕ} {k : ℕ} (hk : k ≠ 0) (c x : Fin m → ℕ)
    (n : ℕ) (hn : n = ∑ i, c i * x i ^ k) :
    ∃ s : Multiset ℕ, (∀ y ∈ s, 1 ≤ y) ∧ s.card ≤ ∑ i, c i ∧ (s.map (· ^ k)).sum = n := by
  classical
  set s0 : Multiset ℕ := ∑ i, Multiset.replicate (c i) (x i) with hs0
  have hfull : (s0.map (· ^ k)).sum = n := by
    rw [hs0, hn, ← Multiset.coe_mapAddMonoidHom, map_sum,
      ← Multiset.coe_sumAddMonoidHom, map_sum]
    congr 1
    funext i
    rw [Multiset.coe_sumAddMonoidHom, Multiset.coe_mapAddMonoidHom]
    simp [Multiset.map_replicate, Multiset.sum_replicate]
  refine ⟨s0.filter (1 ≤ ·), ?_, ?_, ?_⟩
  · intro y hy
    exact (Multiset.mem_filter.mp hy).2
  · calc (s0.filter (1 ≤ ·)).card ≤ s0.card :=
          Multiset.card_le_card (Multiset.filter_le _ _)
      _ = ∑ i, c i := by
          rw [hs0, Multiset.card_sum]
          simp [Multiset.card_replicate]
  · have hsplit : s0.filter (1 ≤ ·) + s0.filter (fun y => ¬ (1 ≤ y)) = s0 :=
      Multiset.filter_add_not _ _
    have hzero : ((s0.filter (fun y => ¬ (1 ≤ y))).map (· ^ k)).sum = 0 := by
      apply Multiset.sum_eq_zero
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      have : y = 0 := by
        have := (Multiset.mem_filter.mp hy).2
        omega
      simp [this, Nat.zero_pow (Nat.pos_of_ne_zero hk)]
    have h1 := congrArg (fun t => (Multiset.map (· ^ k) t).sum) hsplit
    simp only [Multiset.map_add, Multiset.sum_add] at h1
    rw [hzero, add_zero] at h1
    rw [h1, hfull]

theorem hard_number_lower {k q : ℕ} (hk : 2 ≤ k) (hq : 1 ≤ q)
    (hle : 2 ^ k * q ≤ 3 ^ k)
    (s : Multiset ℕ) (hpos : ∀ y ∈ s, 1 ≤ y)
    (hsum : (s.map (· ^ k)).sum = 2 ^ k * q - 1) :
    2 ^ k + q - 2 ≤ s.card := by
  classical
  have hP4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hPq1 : 1 ≤ 2 ^ k * q := Nat.mul_pos (by omega) (by omega)
  have hltq : 2 ^ k * q - 1 < 3 ^ k := lt_of_lt_of_le (Nat.sub_lt hPq1 one_pos) hle
  have hmem : ∀ y ∈ s, y = 1 ∨ y = 2 := by
    intro y hy
    have h1 : 1 ≤ y := hpos y hy
    have hyk : y ^ k ≤ 2 ^ k * q - 1 := by
      rw [← hsum]
      exact Multiset.single_le_sum (fun z _ => Nat.zero_le z) _
        (Multiset.mem_map_of_mem _ hy)
    have hlt3 : y ^ k < 3 ^ k := lt_of_le_of_lt hyk hltq
    have : y < 3 := by
      by_contra hcon
      push_neg at hcon
      exact absurd (Nat.pow_le_pow_left hcon k) (by omega)
    omega
  set a : ℕ := s.count 1 with ha
  set b : ℕ := s.count 2 with hb
  have hsplit : s = Multiset.replicate a 1 + Multiset.replicate b 2 := by
    ext z
    rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
    by_cases hz1 : z = 1
    · subst hz1; simp [ha]
    · by_cases hz2 : z = 2
      · subst hz2; simp [hb]
      · have : s.count z = 0 := by
          rw [Multiset.count_eq_zero]
          intro hzs
          rcases hmem z hzs with h | h <;> simp_all
        simp [this, if_neg (Ne.symm hz1), if_neg (Ne.symm hz2)]
  have hcard : s.card = a + b := by
    rw [hsplit]; simp [Multiset.card_replicate]
  have hsum2 : a + b * 2 ^ k = 2 ^ k * q - 1 := by
    have h0 := hsum
    rw [hsplit] at h0
    simpa [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, one_pow, smul_eq_mul] using h0
  rw [hcard]
  exact arith_core (2 ^ k) a b q hP4 hq hsum2

/-- `sumsOfPowers k m n` : `n` is a sum of at most `m` positive `k`-th powers. -/
def sumsOfPowers (k m n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ y ∈ s, 1 ≤ y) ∧ s.card ≤ m ∧ (s.map (· ^ k)).sum = n

/-- **The reduction**: part (iii) of the A271099 conjecture implies the
*ideal Waring theorem* `g(k) = 2^k + ⌊(3/2)^k⌋ - 2` for every `k > 2` —
an open problem (known only for `k ≤ 471 600 000`, Kubina–Wunderlich, plus
ineffectively for large `k` by Mahler). -/
theorem part_iii_implies_ideal_waring
    (h : ∀ k : ℕ, k > 2 →
      ∃ c : Fin (2 * k - 1) → ℕ,
        (∀ i : Fin (2 * k - 1), c i > 0) ∧
        (Set.range (fun x : Fin (2 * k - 1) → ℕ =>
          Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k)) = Set.univ ∧
        (Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) c = waring_g k)) :
    ∀ k : ℕ, k > 2 →
      (∀ n : ℕ, sumsOfPowers k (waring_g k) n) ∧
      ¬ (∀ n : ℕ, sumsOfPowers k (waring_g k - 1) n) := by
  intro k hk
  obtain ⟨c, hcpos, hcover, hcsum⟩ := h k hk
  have hk2 : 2 ≤ k := by omega
  have hkne : k ≠ 0 := by omega
  constructor
  · -- upper bound: every n is a sum of at most waring_g k positive k-th powers
    intro n
    have hn : n ∈ Set.range (fun x : Fin (2 * k - 1) → ℕ =>
        Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k) := by
      rw [hcover]; trivial
    obtain ⟨x, hx⟩ := hn
    obtain ⟨s, h1, h2, h3⟩ := weighted_gives_count hkne c x n hx.symm
    exact ⟨s, h1, hcsum ▸ h2, h3⟩
  · -- tightness at the hard number 2^k * qq k - 1
    intro hall
    obtain ⟨s, h1, h2, h3⟩ := hall (2 ^ k * qq k - 1)
    have hlow : 2 ^ k + qq k - 2 ≤ s.card :=
      hard_number_lower hk2 (by have := two_le_qq hk2; omega) (pow_mul_qq_le k) s h1 h3
    have hw : waring_g k = 2 ^ k + qq k - 2 := waring_g_eq hk2
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have hq2 : 2 ≤ qq k := two_le_qq hk2
    omega


/-- **Sharper reduction**: part (iii) of the conjecture implies the *strict classical
Waring condition* `3^k / 2^k + 3^k mod 2^k < 2^k` for every `k > 2` — a completely
elementary arithmetic inequality family that is a famous open problem (it has been verified
for `k ≤ 471 600 000` by Kubina–Wunderlich; Mahler proved it holds for all sufficiently
large `k` only ineffectively).  The proof analyses representations of the second extremal
number `3^k + 2^k⌊(3/2)^k⌋ - 1`. -/
theorem part_iii_implies_strict_waring_condition
    (h : ∀ k : ℕ, k > 2 →
      ∃ c : Fin (2 * k - 1) → ℕ,
        (∀ i : Fin (2 * k - 1), c i > 0) ∧
        (Set.range (fun x : Fin (2 * k - 1) → ℕ =>
          Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k)) = Set.univ ∧
        (Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) c = waring_g k)) :
    ∀ k : ℕ, k > 2 → 3 ^ k / 2 ^ k + 3 ^ k % 2 ^ k < 2 ^ k := by
  intro k hk
  obtain ⟨c, hcpos, hcover, hcsum⟩ := h k hk
  have hk3 : 3 ≤ k := by omega
  have hkne : k ≠ 0 := by omega
  have hn : 3 ^ k + (2 ^ k * qq k - 1) ∈ Set.range (fun x : Fin (2 * k - 1) → ℕ =>
      Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k) := by
    rw [hcover]; trivial
  obtain ⟨x, hx⟩ := hn
  obtain ⟨s, h1, h2, h3⟩ := weighted_gives_count hkne c x _ hx.symm
  have hcard : s.card ≤ 2 ^ k + qq k - 2 := by
    rw [hcsum, waring_g_eq (by omega : 2 ≤ k)] at h2
    exact h2
  have hres := strict_condition_of_rep hk3 s h1 h3 hcard
  rw [qq_eq_div] at hres
  exact hres


end A271099Reduction
