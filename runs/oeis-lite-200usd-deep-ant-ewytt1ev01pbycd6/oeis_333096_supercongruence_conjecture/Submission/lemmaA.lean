import Submission.mainformula

open PowerSeries Finset

/-!
# Lemma A' (clean divisibility form)

We prove:
`(p:ℤ)^(2·v_p(M)) ∣ (p:ℤ)^(2·v_p((2μ)!)) · ℓ (ψ p j) (A·M) M`,
where `μ = (j-1)/2`.

Following `/tmp/proof.md`, this reduces (via the regime split) to the
dominant-regime bound (Prop 5): when `2μ < p^E` (E = v_p(M)),
`v_p(ℓ) ≥ 2E - 2 v_p((2μ)!)`, i.e. the same divisibility.
-/

/-- Arithmetic lemma: if `p^E ≤ n` then `E ≤ v_p(n!)` (Legendre). -/
lemma pow_le_imp_valNat_le (p : ℕ) (hp : p.Prime) (E n : ℕ) (hn : 0 < n)
    (h : p ^ E ≤ n) : E ≤ padicValNat p n.factorial := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  -- E ≤ log p n
  have hElog : E ≤ Nat.log p n := (Nat.le_log_iff_pow_le hp1 (by omega)).mpr h
  -- Legendre with bound b = log p n + 1
  have hb : Nat.log p n < Nat.log p n + 1 := by omega
  rw [padicValNat_factorial hb]
  -- E ≤ ∑_{i ∈ Ico 1 (E+1)} n/p^i ≤ ∑_{i ∈ Ico 1 (log+1)} n/p^i
  have hsub : Finset.Ico 1 (E + 1) ⊆ Finset.Ico 1 (Nat.log p n + 1) := by
    apply Finset.Ico_subset_Ico (le_refl 1)
    omega
  have hlow : E ≤ ∑ i ∈ Finset.Ico 1 (E + 1), n / p ^ i := by
    have hcard : (Finset.Ico 1 (E + 1)).card = E := by
      rw [Nat.card_Ico]; omega
    calc E = ∑ _i ∈ Finset.Ico 1 (E + 1), 1 := by rw [Finset.sum_const, hcard]; ring
      _ ≤ ∑ i ∈ Finset.Ico 1 (E + 1), n / p ^ i := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_Ico] at hi
          have hpi : p ^ i ≤ n := le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h
          exact Nat.one_le_div_iff (by positivity) |>.mpr hpi
  have hmono : ∑ i ∈ Finset.Ico 1 (E + 1), n / p ^ i
      ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ i :=
    Finset.sum_le_sum_of_subset hsub
  omega

/- ## Verified building block: the descent identity (Prop 1 core)

The pure `Ring.choose` identity underlying the descent step (§1 of proof.md):
`s·(C(s-1,k) - C(s-1,k+1)) = (2(k+1) - s)·C(s,k+1)`. -/

/-- Absorption identity for `Ring.choose` (as in `p1.lean`). -/
lemma ABS' (N : ℤ) (k : ℕ) :
    ((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1) = (N - (k:ℤ)) * Ring.choose N k := by
  have hk : ((k.factorial : ℤ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hk
  have e1 : (k.factorial : ℤ) * (((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1))
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    have hpk : (∏ i ∈ range (k+1), (N - (i:ℤ)))
        = ((k+1).factorial : ℤ) * Ring.choose N (k+1) := by
      have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N (k+1)
      rw [nsmul_eq_mul] at h
      rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
      exact h
    rw [hpk]
    have : ((k + 1).factorial : ℤ) = ((k + 1 : ℕ) : ℤ) * (k.factorial : ℤ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this]; ring
  have e2 : (k.factorial : ℤ) * ((N - (k:ℤ)) * Ring.choose N k)
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    have hpk : (∏ i ∈ range k, (N - (i:ℤ))) = (k.factorial : ℤ) * Ring.choose N k := by
      have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N k
      rw [nsmul_eq_mul] at h
      rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
      exact h
    rw [Finset.prod_range_succ, hpk]; ring
  rw [e1, e2]

/-- **Prop 1 (descent identity core).** Pure generalized-binomial identity. -/
lemma descKey (s : ℤ) (k : ℕ) :
    s * (Ring.choose (s - 1) k - Ring.choose (s - 1) (k + 1))
      = (2 * ((k : ℤ) + 1) - s) * Ring.choose s (k + 1) := by
  have P1 : Ring.choose s (k + 1) = Ring.choose (s - 1) k + Ring.choose (s - 1) (k + 1) := by
    have h := Ring.choose_succ_succ (s - 1) k
    rw [sub_add_cancel] at h
    exact h
  have A2 := ABS' (s - 1) k
  push_cast at A2
  rw [P1]
  linear_combination (-2 : ℤ) * A2

/- ## Verified building block: the finite closed form (§0 of proof.md)

`ψ p j = (1+X)^{-j} · Wⱼ`, where `Wⱼ = Cart p (qser p ^ j * Gser)`.  Consequently
`ℓ` has the finite closed form below.  Note: the sum is naturally finite (`k ≤ M`),
so no polynomial/finite-support argument for `Wⱼ` is needed here. -/

lemma infl_pow (p : ℕ) (hp0 : 0 < p) (a : PowerSeries ℤ) (j : ℕ) :
    (infl p a) ^ j = infl p (a ^ j) := by
  induction j with
  | zero => simp [infl_one p hp0]
  | succ n ih => rw [pow_succ, ih, infl_mul p hp0, pow_succ]

lemma binNeg1 : binomialSeries ℤ (-1 : ℤ) = Xinv := by
  have h1 : binomialSeries ℤ (1 : ℤ) = 1 + PowerSeries.X := by
    have := binomialSeries_nat (A := ℤ) (R := ℤ) 1
    simpa using this
  have hmul : ((1 : PowerSeries ℤ) + PowerSeries.X) * binomialSeries ℤ (-1 : ℤ) = 1 := by
    rw [← h1, ← binomialSeries_add]; norm_num
  have hne : ((1 : PowerSeries ℤ) + PowerSeries.X) ≠ 0 := by
    intro h; have := congrArg (PowerSeries.coeff 0) h; simp at this
  apply mul_left_cancel₀ hne
  rw [hmul, oneAddX_mul_Xinv]

lemma binomialSeries_negNat (j : ℕ) : binomialSeries ℤ (-(j : ℤ)) = Xinv ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    have : (-(↑(n+1) : ℤ)) = (-(n:ℤ)) + (-1) := by push_cast; ring
    rw [this, binomialSeries_add, ih, binNeg1, pow_succ]

lemma psi_eq (p j : ℕ) (hp0 : 0 < p) :
    ψ p j = Xinv ^ j * Cart p (qser p ^ j * Gser) := by
  unfold ψ rho
  rw [mul_pow, infl_pow p hp0, mul_comm (qser p ^ j) (infl p (Xinv ^ j)), mul_assoc,
      cart_infl_mul p hp0]

/-- **Closed form (§0).** `ℓ (ψ p j) (A·M) M = ∑_{k≤M} C(A·M - j, k)·(qser^j·G)_{p(M-k)}`. -/
lemma closed_form_ell (p : ℕ) (hp0 : 0 < p) (A : ℤ) (M j : ℕ) :
    ℓ (ψ p j) (A * (M : ℤ)) M
      = ∑ k ∈ range (M + 1),
          Ring.choose (A * (M : ℤ) - (j : ℤ)) k
            * PowerSeries.coeff (p * (M - k)) (qser p ^ j * Gser) := by
  unfold ℓ
  rw [psi_eq p j hp0]
  have hcomb : binomialSeries ℤ (A * (M : ℤ)) * (Xinv ^ j * Cart p (qser p ^ j * Gser))
      = binomialSeries ℤ (A * (M : ℤ) - (j : ℤ)) * Cart p (qser p ^ j * Gser) := by
    rw [← binomialSeries_negNat, ← mul_assoc, ← binomialSeries_add]; ring_nf
  rw [hcomb, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => (PowerSeries.coeff a) (binomialSeries ℤ (A * (M:ℤ) - (j:ℤ)))
          * (PowerSeries.coeff b) (Cart p (qser p ^ j * Gser))) M]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_coeff, coeff_Cart]
  simp

/-- **Denominator exactness (§5).** If `p^E ∣ M` and `0 < t < p^E`, then subtracting `t`
from the multiple `M` does not change the `p`-adic valuation: `v_p(M - t) = v_p(t)`.
This is the exact-cancellation fact used to evaluate the descent denominators
`∏_r (M - i - r)` in the dominant regime. -/
lemma vp_sub_eq (p : ℕ) (hp : p.Prime) (E M t : ℕ) (hM : 0 < M) (hpE : p ^ E ∣ M)
    (ht0 : 0 < t) (htE : t < p ^ E) : padicValNat p (M - t) = padicValNat p t := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  set w := padicValNat p t with hwdef
  -- w < E
  have hwt : p ^ w ∣ t := pow_padicValNat_dvd
  have hwE : w < E := by
    by_contra hge
    push_neg at hge
    have : p ^ E ∣ t := dvd_trans (pow_dvd_pow p hge) hwt
    have := Nat.le_of_dvd ht0 this
    omega
  have hMle : p ^ E ≤ M := Nat.le_of_dvd (by omega) hpE
  have hMt : t ≤ M := by omega
  have hMtpos : 0 < M - t := by omega
  -- p^w ∣ (M - t)
  have hdvdM : p ^ w ∣ M := dvd_trans (pow_dvd_pow p (le_of_lt hwE)) hpE
  have h1 : p ^ w ∣ (M - t) := Nat.dvd_sub hdvdM hwt
  -- ¬ p^(w+1) ∣ (M - t)
  have h2 : ¬ p ^ (w + 1) ∣ (M - t) := by
    intro hcon
    have hdvdM' : p ^ (w + 1) ∣ M := dvd_trans (pow_dvd_pow p (by omega)) hpE
    have : p ^ (w + 1) ∣ (M - (M - t)) := Nat.dvd_sub hdvdM' hcon
    rw [Nat.sub_sub_self hMt] at this
    exact pow_succ_padicValNat_not_dvd (by omega) this
  -- conclude
  have hle : w ≤ padicValNat p (M - t) :=
    (padicValNat_dvd_iff_le (by omega)).mp h1
  have hlt : ¬ (w + 1 ≤ padicValNat p (M - t)) := by
    intro hc; exact h2 ((padicValNat_dvd_iff_le (by omega)).mpr hc)
  omega

/-- **Descent engine (§2–§3), summed form of `descKey`.**  For a coefficient
sequence `c` supported in `[0, n)` (i.e. `c i = 0` for `i ≥ n`), and any `s : ℤ`,
```
s · Σ_i c_i (C(s-1, n-i-1) - C(s-1, n-i)) = Σ_i (2(n-i) - s) c_i · C(s, n-i).
```
This is the exact discrete form of the descent identity `(★)` of `/tmp/proof.md`,
obtained by summing `descKey` term by term; the left side is `s·ℓ`, the right the
raw combination that (after the palindrome/center substitution `2(n-i)-s ↦
-(A-2)N + 2(c-i)`) becomes `-(A-2)N·P₁ + 2·(next level)`. -/
lemma descent_sum (s : ℤ) (n : ℕ) (c : ℕ → ℤ) (hsupp : ∀ i, n ≤ i → c i = 0) :
    s * (∑ i ∈ range (n + 1), c i *
          (Ring.choose (s - 1) (n - i - 1) - Ring.choose (s - 1) (n - i)))
      = ∑ i ∈ range (n + 1), (2 * ((n : ℤ) - (i : ℤ)) - s) * c i * Ring.choose s (n - i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
  · -- i < n
    have hk : n - i - 1 + 1 = n - i := by omega
    have hcast : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := by
      rw [Nat.cast_sub (le_of_lt hlt)]
    have hdk := descKey s (n - i - 1)
    rw [hk] at hdk
    -- hdk : s * (C(s-1, n-i-1) - C(s-1, n-i)) = (2*((n-i-1:ℕ)+1) - s) * C(s, n-i)
    have hcast2 : ((n - i - 1 : ℕ) : ℤ) + 1 = (n : ℤ) - (i : ℤ) := by
      have : ((n - i - 1 : ℕ) : ℤ) + 1 = ((n - i : ℕ) : ℤ) := by
        rw [← hk]; push_cast; ring
      rw [this, hcast]
    calc s * (c i * (Ring.choose (s - 1) (n - i - 1) - Ring.choose (s - 1) (n - i)))
        = c i * (s * (Ring.choose (s - 1) (n - i - 1) - Ring.choose (s - 1) (n - i))) := by ring
      _ = c i * ((2 * (((n - i - 1 : ℕ) : ℤ) + 1) - s) * Ring.choose s (n - i)) := by rw [hdk]
      _ = (2 * ((n : ℤ) - (i : ℤ)) - s) * c i * Ring.choose s (n - i) := by rw [hcast2]; ring
  · -- i = n : c i = 0
    subst heq
    rw [hsupp i (le_refl i)]; ring

/-- **Prop 5 (dominant-regime bound).** For `2μ < p^E`,
`(p:ℤ)^(2E) ∣ (p:ℤ)^(2·v_p((2μ)!)) · ℓ (ψ p j) (A·M) M`.

This is the analytic heart (§0–§5 of `/tmp/proof.md`) and the ONLY remaining
`sorry`.  With `closed_form_ell` above (§0) and `descKey` (§1) already verified,
the remaining work is:
  * the polynomial refinement `Wⱼ = Cart p (qser^j·G) = (X-1)·Sⱼ` with `Sⱼ`
    palindromic about `μ`, supported in `[t₀, 2μ-t₀]` — this needs
    `(1+X+X²) ∣ qser p` (i.e. `qser` vanishes at cube roots of unity for `p ≥ 5`);
  * the descent chain / master unrolling (§2–§3) built from `descKey`;
  * the generalized Kummer bound (§4, Prop 4):
    `v_p (Ring.choose (A·M - a) (M - b)) ≥ v_p M - v_p ((a-1)!)` for `a > b > 0`;
  * the term-by-term valuation bookkeeping (§5) giving `v_p(ℓ) ≥ 2E - 2 v_p((2μ)!)`. -/
lemma prop5 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ) (M : ℕ) (hM : 0 < M) (j : ℕ)
    (hj : 3 ≤ j) (hE : 2 * ((j - 1) / 2) < p ^ (padicValNat p M)) :
    (p : ℤ) ^ (2 * padicValNat p M)
      ∣ (p : ℤ) ^ (2 * padicValNat p (2 * ((j - 1) / 2)).factorial) * ℓ (ψ p j) (A * (M : ℤ)) M := by
  sorry

theorem lemmaA (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ) (M : ℕ) (hM : 0 < M) (j : ℕ)
    (hj : 3 ≤ j) :
    (p : ℤ) ^ (2 * padicValNat p M)
      ∣ (p : ℤ) ^ (2 * padicValNat p (2 * ((j - 1) / 2)).factorial) * ℓ (ψ p j) (A * (M : ℤ)) M := by
  set E := padicValNat p M with hEdef
  set μ := (j - 1) / 2 with hμdef
  set F := padicValNat p (2 * μ).factorial with hFdef
  by_cases hEF : E ≤ F
  · -- trivial regime: 2E ≤ 2F
    exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) (dvd_mul_right _ _)
  · -- F < E, so p^E > 2μ, apply Prop 5
    push_neg at hEF
    have hμpos : 0 < μ := by rw [hμdef]; omega
    have hpe : 2 * μ < p ^ E := by
      by_contra hle
      push_neg at hle
      have := pow_le_imp_valNat_le p hp E (2 * μ) (by omega) hle
      omega
    exact prop5 p hp hp5 A M hM j hj hpe

#print axioms lemmaA
