import Submission.Richness

/-!
# Conditional translation and witness extraction for Erdős problem 647

Complementary divisor pairs give an upper bound for `σ 0 t` using the small
(divisor-square at most `t`) divisors of `t`. If all of these divide `m`, they
also divide `Nat.gcd m t`. Combining this with the complementary-divisor lower
bound from `Submission.Reductions` transfers divisor-count inequalities from
`m + t` to `t` below a specified threshold `j`.

The optional final section defines the least positive nondivisor `Q m` and
identifies `(Q m)²` as the sharp first failure of the intermediate gcd comparison.
This is not a claim that the translated comparison or the original condition
fails at that point.

The witness-extraction results below are conditional: they require small-divisor
closure, a size bound, and **all** of the exact prefix inequalities. This file
does not construct those hypotheses and does not settle the original problem.
It imports the verified helper `Submission.Richness`, not `Submission.Spec`.
-/

namespace Erdos647

open scoped ArithmeticFunction.sigma

/-- Every divisor is either small or the complement of a small divisor.
The two sets may overlap at the square root, which is harmless for this bound. -/
theorem card_divisors_le_two_mul_card_small_divisors (t : ℕ) :
    t.divisors.card ≤ 2 * (t.divisors.filter (fun d => d * d ≤ t)).card := by
  let s := t.divisors.filter (fun d => d * d ≤ t)
  have hcover : t.divisors ⊆ s ∪ s.image (fun d => t / d) := by
    intro d hd
    have hdt : d ∣ t := Nat.dvd_of_mem_divisors hd
    have ht0 : t ≠ 0 := Nat.ne_zero_of_mem_divisors hd
    by_cases hsmall : d * d ≤ t
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hd, hsmall⟩))
    · have hcomp : t / d < d :=
        (Nat.div_lt_iff_lt_mul (Nat.pos_of_mem_divisors hd)).mpr
          (Nat.lt_of_not_ge hsmall)
      have hcomp_sq : (t / d) * (t / d) ≤ t := calc
        (t / d) * (t / d) ≤ (t / d) * d := Nat.mul_le_mul_left _ hcomp.le
        _ = t := Nat.div_mul_cancel hdt
      apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_image.mpr ⟨t / d,
        Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdt, ht0⟩, hcomp_sq⟩,
        Nat.div_div_self hdt ht0⟩
  calc
    t.divisors.card ≤ (s ∪ s.image (fun d => t / d)).card :=
      Finset.card_le_card hcover
    _ ≤ s.card + (s.image (fun d => t / d)).card := Finset.card_union_le _ _
    _ ≤ s.card + s.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * s.card := by omega

/-- If each small divisor of a positive `t` divides `m`, the divisor count of
`t` is at most twice that of `gcd(m,t)`. No factorization is used. -/
theorem card_divisors_le_two_mul_card_gcd_of_small_divisors {m t : ℕ}
    (ht : 0 < t) (hsmall : ∀ d : ℕ, d ∣ t → d * d ≤ t → d ∣ m) :
    t.divisors.card ≤ 2 * (Nat.gcd m t).divisors.card := by
  have hsubset : t.divisors.filter (fun d => d * d ≤ t) ⊆
      (Nat.gcd m t).divisors := by
    intro d hd
    obtain ⟨hdt, hsq⟩ := Finset.mem_filter.mp hd
    exact Nat.mem_divisors.mpr
      ⟨Nat.dvd_gcd (hsmall d (Nat.dvd_of_mem_divisors hdt) hsq)
          (Nat.dvd_of_mem_divisors hdt),
        (Nat.gcd_pos_of_pos_right m ht).ne'⟩
  exact (card_divisors_le_two_mul_card_small_divisors t).trans
    (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset))

/-- The small-divisor bound in divisor-count notation. -/
theorem sigma_zero_le_two_mul_gcd_of_small_divisors {m t : ℕ}
    (ht : 0 < t) (hsmall : ∀ d : ℕ, d ∣ t → d * d ≤ t → d ∣ m) :
    σ 0 t ≤ 2 * σ 0 (Nat.gcd m t) := by
  simpa only [ArithmeticFunction.sigma_zero_apply] using
    card_divisors_le_two_mul_card_gcd_of_small_divisors ht hsmall

/-- Closure under all positive `d` with `d² < j` supplies the small divisors
needed for every positive `t < j`. -/
theorem sigma_zero_le_two_mul_gcd_below {m j : ℕ}
    (hsmall : ∀ d : ℕ, 0 < d → d * d < j → d ∣ m)
    {t : ℕ} (ht : 0 < t) (htj : t < j) :
    σ 0 t ≤ 2 * σ 0 (Nat.gcd m t) := by
  apply sigma_zero_le_two_mul_gcd_of_small_divisors ht
  intro d hdt hsq
  exact hsmall d (Nat.pos_of_dvd_of_pos hdt ht) (lt_of_le_of_lt hsq htj)

/-- Divisor-count translation below `j`. The usual hypothesis `1 ≤ j` is
unnecessary here, since it follows whenever a positive `t < j` is supplied. -/
theorem sigma_zero_le_add_of_small_divisors {m j : ℕ}
    (hm : j * j < m)
    (hsmall : ∀ d : ℕ, 0 < d → d * d < j → d ∣ m)
    {t : ℕ} (ht : 0 < t) (htj : t < j) :
    σ 0 t ≤ σ 0 (m + t) := by
  have hgdvd : Nat.gcd m t ∣ m + t :=
    dvd_add (Nat.gcd_dvd_left m t) (Nat.gcd_dvd_right m t)
  have hgj : Nat.gcd m t ≤ j := (Nat.gcd_le_right m ht).trans htj.le
  have hsq : Nat.gcd m t * Nat.gcd m t < m + t :=
    lt_of_le_of_lt (Nat.mul_self_le_mul_self hgj)
      (lt_of_lt_of_le hm (Nat.le_add_right m t))
  exact (sigma_zero_le_two_mul_gcd_below hsmall ht htj).trans
    (two_mul_sigma_zero_le hgdvd hsq)

/-- Reindexing the exact offsets `1 ≤ k < j` gives precisely the positive
shifted prefix `0 < t < j`. There is deliberately no condition at `t = 0`. -/
theorem exact_prefix_iff_positive_shifted_prefix {m j : ℕ} :
    (∀ k : ℕ, 1 ≤ k → k < j → σ 0 (m + j - k) ≤ k + 2) ↔
      (∀ t : ℕ, 0 < t → t < j → t + σ 0 (m + t) ≤ j + 2) := by
  constructor
  · intro h t ht htj
    have hb := h (j - t) (by omega) (by omega)
    have heq : m + j - (j - t) = m + t := by omega
    rw [heq] at hb
    omega
  · intro h k hk hkj
    have hb := h (j - k) (by omega) (by omega)
    have heq : m + (j - k) = m + j - k := by omega
    rw [heq] at hb
    omega

/-- A translated positive prefix yields `P j`; the value at zero is automatic. -/
theorem p_of_positive_shifted_prefix {m j : ℕ}
    (hm : j * j < m)
    (hsmall : ∀ d : ℕ, 0 < d → d * d < j → d ∣ m)
    (hprefix : ∀ t : ℕ, 0 < t → t < j → t + σ 0 (m + t) ≤ j + 2) :
    P j := by
  intro t htj
  by_cases ht : t = 0
  · simp [ht]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    exact (Nat.add_le_add_left
      (sigma_zero_le_add_of_small_divisors hm hsmall htpos htj) t).trans
      (hprefix t htpos htj)

/-- Conditional witness extraction from **all** exact prefix inequalities.
The size, small-divisor closure, and prefix hypotheses are not constructed here. -/
theorem p_of_exact_prefix {m j : ℕ} (hj : 1 ≤ j)
    (hm : j * j < m)
    (hsmall : ∀ d : ℕ, 0 < d → d * d < j → d ∣ m)
    (hprefix : ∀ k : ℕ, 1 ≤ k → k < j → σ 0 (m + j - k) ≤ k + 2) :
    P j := by
  apply p_of_positive_shifted_prefix hm hsmall
  intro t ht htj
  have hkj : j - t < j := Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hj) ht
  have hb := hprefix (j - t) (by omega) hkj
  have heq : m + j - (j - t) = m + t := by omega
  rw [heq] at hb
  omega

/-- If the conditional hypotheses hold with `j > 24`, `j` itself supplies the
original finite-supremum witness. This does not assert existence of the hypotheses. -/
theorem exists_fin_iSup_bound_of_exact_prefix {m j : ℕ} (hj : 24 < j)
    (hm : j * j < m)
    (hsmall : ∀ d : ℕ, 0 < d → d * d < j → d ∣ m)
    (hprefix : ∀ k : ℕ, 1 ≤ k → k < j → σ 0 (m + j - k) ≤ k + 2) :
    ∃ n : ℕ, 24 < n ∧ (⨆ t : Fin n, (t : ℕ) + σ 0 (t : ℕ)) ≤ n + 2 := by
  exact ⟨j, hj, (p_iff_fin_iSup_bound (by omega)).mp
    (p_of_exact_prefix (by omega) hm hsmall hprefix)⟩

/- ## The least positive nondivisor -/

/-- A positive natural number has a positive nondivisor, for example `m + 1`. -/
theorem exists_positive_nondivisor {m : ℕ} (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧ ¬ q ∣ m := by
  refine ⟨m + 1, by omega, ?_⟩
  intro h
  have := Nat.le_of_dvd hm h
  omega

/-- For `m > 0`, `Q m` is its least positive nondivisor. We set `Q 0 = 0`,
since every positive natural number divides zero. -/
noncomputable def Q (m : ℕ) : ℕ :=
  if hm : 0 < m then Nat.find (exists_positive_nondivisor hm) else 0

@[simp] theorem Q_zero : Q 0 = 0 := by simp [Q]

/-- Positivity and nondivisibility for the least positive nondivisor. -/
theorem Q_spec {m : ℕ} (hm : 0 < m) : 0 < Q m ∧ ¬ Q m ∣ m := by
  simpa only [Q, dif_pos hm] using Nat.find_spec (exists_positive_nondivisor hm)

/-- Every positive integer strictly below `Q m` divides `m`. -/
theorem dvd_of_lt_Q {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (hlt : d < Q m) :
    d ∣ m := by
  have hfind : d < Nat.find (exists_positive_nondivisor hm) := by
    simpa only [Q, dif_pos hm] using hlt
  by_contra hnot
  exact Nat.find_min (exists_positive_nondivisor hm) hfind ⟨hd, hnot⟩

/-- For positive `m`, the small-divisor closure used above holds exactly when
`j ≤ (Q m)²`. This statement concerns closure, not existence of a full prefix. -/
theorem small_divisor_closure_iff_le_Q_sq {m j : ℕ} (hm : 0 < m) :
    (∀ d : ℕ, 0 < d → d * d < j → d ∣ m) ↔ j ≤ Q m * Q m := by
  constructor
  · intro hsmall
    by_contra hsq
    exact (Q_spec hm).2
      (hsmall (Q m) (Q_spec hm).1 (Nat.lt_of_not_ge hsq))
  · intro hsq d hd hdj
    apply dvd_of_lt_Q hm hd
    by_contra hlt
    have hle : Q m ≤ d := Nat.le_of_not_gt hlt
    have := Nat.mul_self_le_mul_self hle
    omega

/-- The `Q`-threshold supplies the closure hypothesis of the translation theorem. -/
theorem sigma_zero_le_add_of_le_Q_sq {m j : ℕ}
    (hm : j * j < m) (hQ : j ≤ Q m * Q m)
    {t : ℕ} (ht : 0 < t) (htj : t < j) :
    σ 0 t ≤ σ 0 (m + t) := by
  exact sigma_zero_le_add_of_small_divisors hm
    ((small_divisor_closure_iff_le_Q_sq (lt_of_le_of_lt (Nat.zero_le _) hm)).mpr hQ)
    ht htj

/-- Conditional witness extraction using the least-positive-nondivisor threshold.
The exact prefix inequalities remain hypotheses, not conclusions of the threshold. -/
theorem p_of_exact_prefix_of_le_Q_sq {m j : ℕ} (hj : 1 ≤ j)
    (hm : j * j < m) (hQ : j ≤ Q m * Q m)
    (hprefix : ∀ k : ℕ, 1 ≤ k → k < j → σ 0 (m + j - k) ≤ k + 2) :
    P j := by
  exact p_of_exact_prefix hj hm
    ((small_divisor_closure_iff_le_Q_sq (lt_of_le_of_lt (Nat.zero_le _) hm)).mpr hQ)
    hprefix

/-- The least positive nondivisor of a positive integer is a prime power.
Only this optional sharp-threshold section uses the prime-power divisibility criterion. -/
theorem Q_isPrimePow {m : ℕ} (hm : 0 < m) : IsPrimePow (Q m) := by
  by_contra hnot
  apply (Q_spec hm).2
  apply (Nat.dvd_iff_prime_pow_dvd_dvd m (Q m)).mpr
  intro p k hp hdiv
  by_cases hk : k = 0
  · simp [hk]
  · have hlt : p ^ k < Q m := lt_of_le_of_ne
        (Nat.le_of_dvd (Q_spec hm).1 hdiv) (by
          intro heq
          exact hnot ((isPrimePow_nat_iff _).mpr
            ⟨p, k, hp, Nat.pos_of_ne_zero hk, heq⟩))
    exact dvd_of_lt_Q hm (pow_pos hp.pos _) hlt

/-- Write `Q m = p^(a+1)`. Minimality says that `p^a`, and no higher power
of `p`, divides `m`; in particular this is its gcd with `(Q m)²`. -/
theorem gcd_Q_sq_of_eq_prime_pow {m p a : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hQ : Q m = p ^ (a + 1)) :
    Nat.gcd m (Q m * Q m) = p ^ a := by
  have hsq : Q m * Q m = p ^ ((a + 1) + (a + 1)) := by
    rw [hQ, ← pow_add]
  have hpa : p ^ a ∣ m := dvd_of_lt_Q hm (pow_pos hp.pos _) (by
    rw [hQ]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega))
  have hgdiv : Nat.gcd m (Q m * Q m) ∣ p ^ ((a + 1) + (a + 1)) := by
    rw [← hsq]
    exact Nat.gcd_dvd_right _ _
  obtain ⟨b, _, hgb⟩ := (Nat.dvd_prime_pow hp).mp hgdiv
  have hba : b ≤ a := by
    by_contra hnot
    have hqg : Q m ∣ Nat.gcd m (Q m * Q m) := by
      rw [hgb, hQ]
      exact pow_dvd_pow p (by omega)
    exact (Q_spec hm).2 (hqg.trans (Nat.gcd_dvd_left _ _))
  apply Nat.dvd_antisymm
  · rw [hgb]
    exact pow_dvd_pow p hba
  · apply Nat.dvd_gcd hpa
    rw [hsq]
    exact pow_dvd_pow p (by omega)

/-- The gcd comparison fails by exactly one at `t = (Q m)²`.
This is a statement about that comparison, not about the original prefix condition. -/
theorem sigma_zero_Q_sq_eq_two_mul_gcd_add_one {m : ℕ} (hm : 0 < m) :
    σ 0 (Q m * Q m) = 2 * σ 0 (Nat.gcd m (Q m * Q m)) + 1 := by
  obtain ⟨p, k, hp, hk, heq⟩ := (isPrimePow_nat_iff _).mp (Q_isPrimePow hm)
  cases k with
  | zero => omega
  | succ a =>
      have hQ : Q m = p ^ (a + 1) := heq.symm
      rw [gcd_Q_sq_of_eq_prime_pow hm hp hQ, hQ, ← pow_add]
      simp only [ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      omega

/-- In particular, the divisor-count comparison is strictly reversed at `(Q m)²`. -/
theorem two_mul_gcd_lt_sigma_zero_Q_sq {m : ℕ} (hm : 0 < m) :
    2 * σ 0 (Nat.gcd m (Q m * Q m)) < σ 0 (Q m * Q m) := by
  rw [sigma_zero_Q_sq_eq_two_mul_gcd_add_one hm]
  omega

/-- `(Q m)²` is the exact first positive failure of the gcd divisor-count
comparison. No corresponding failure of the translated count is claimed. -/
theorem gcd_comparison_below_iff_le_Q_sq {m j : ℕ} (hm : 0 < m) :
    (∀ t : ℕ, 0 < t → t < j → σ 0 t ≤ 2 * σ 0 (Nat.gcd m t)) ↔
      j ≤ Q m * Q m := by
  constructor
  · intro h
    by_contra hsq
    have hb := h (Q m * Q m) (Nat.mul_pos (Q_spec hm).1 (Q_spec hm).1)
      (Nat.lt_of_not_ge hsq)
    exact (Nat.not_le_of_lt (two_mul_gcd_lt_sigma_zero_Q_sq hm)) hb
  · intro hsq t ht htj
    exact sigma_zero_le_two_mul_gcd_below
      ((small_divisor_closure_iff_le_Q_sq hm).mpr hsq) ht htj

end Erdos647

#print axioms Erdos647.card_divisors_le_two_mul_card_gcd_of_small_divisors
#print axioms Erdos647.sigma_zero_le_add_of_small_divisors
#print axioms Erdos647.p_of_exact_prefix
#print axioms Erdos647.exists_fin_iSup_bound_of_exact_prefix
#print axioms Erdos647.small_divisor_closure_iff_le_Q_sq
#print axioms Erdos647.p_of_exact_prefix_of_le_Q_sq
#print axioms Erdos647.Q_isPrimePow
#print axioms Erdos647.sigma_zero_Q_sq_eq_two_mul_gcd_add_one
#print axioms Erdos647.gcd_comparison_below_iff_le_Q_sq
