import Mathlib

/-!
# The requested "strong single-step Kazandzidis congruence" is FALSE as stated

The task asked to prove, over `ℤ`:

    (p : ℤ)^3 * M * K * ((M : ℤ) - K) ∣ (p*M).choose (p*K) - M.choose K

for every prime `p ≥ 5` and `K ≤ M`.

This *literal integer divisibility* statement is **false**.  The genuine classical
theorem (Kazandzidis 1968) is a **p-adic** statement:

    v_p ( C(pM,pK) - C(M,K) )  ≥  3 + v_p(M) + v_p(K) + v_p(M-K),

equivalently `C(pM,pK)/C(M,K) ≡ 1  (mod  p^3·M·K·(M-K)·ℤ_p)`, an inequality of
`p`-adic valuations.  It does NOT assert divisibility by the *whole* integer
`p^3·M·K·(M-K)`, because the non-`p` part of `M·K·(M-K)` (e.g. a factor of `2`
or another prime `ℓ ≠ p`) need not divide the difference at all.

Concrete counterexample (checked below by the Lean kernel):
`p = 5, M = 4, K = 2`.  Then
* `C(20,10) - C(4,2) = 184756 - 6 = 184750`,
* `p^3·M·K·(M-K) = 125·4·2·2 = 2000`,
* but `2000 ∤ 184750` (indeed `184750 = 2000·92 + 750`; note `v_2(184750)=1 < 4 = v_2(2000)`).

The `p`-adic part *does* hold here: `v_5(184750) = 3 ≥ 3`.

Since the stated proposition is false, there is no `sorry`-free / axiom-free proof of
`theorem kazandzidis` (Lean's logic is sound).  Below we instead give a fully
verified DISPROOF of the exact statement, plus a positive check of the true
`p`-adic content at the same point.
-/

/-- The exact proposition requested in the task, packaged as a `Prop`. -/
def KazandzidisStatement : Prop :=
  ∀ (p : ℕ) (_hp : p.Prime) (_h5 : 5 ≤ p) (M K : ℕ) (_hKM : K ≤ M),
    (p : ℤ) ^ 3 * M * K * ((M : ℤ) - K) ∣ ((p * M).choose (p * K) : ℤ) - (M.choose K : ℤ)

/-- The requested statement is FALSE: a Lean-kernel-checked counterexample at
`p = 5, M = 4, K = 2`, where `2000 ∤ 184750`. -/
theorem kazandzidis_statement_is_false : ¬ KazandzidisStatement := by
  intro h
  -- Instantiate at the counterexample.
  have H := h 5 (by norm_num) (by norm_num) 4 2 (by norm_num)
  -- Evaluate the two binomial coefficients.
  have e1 : (5 * 4).choose (5 * 2) = 184756 := by decide
  have e2 : (4 : ℕ).choose 2 = 6 := by decide
  rw [e1, e2] at H
  -- Now `H : (5:ℤ)^3 * 4 * 2 * (4 - 2) ∣ (184756:ℤ) - 6`, i.e. `2000 ∣ 184750`.
  norm_num at H

/-- The genuine `p`-adic content DOES hold at the same point:
`v_5(184750) = 3`, so `5^3 = 125` divides the difference (the `p`-power part). -/
theorem kazandzidis_padic_holds_at_counterexample :
    (5 : ℤ) ^ 3 ∣ ((5 * 4).choose (5 * 2) : ℤ) - ((4 : ℕ).choose 2 : ℤ) := by
  have e1 : (5 * 4).choose (5 * 2) = 184756 := by decide
  have e2 : (4 : ℕ).choose 2 = 6 := by decide
  rw [e1, e2]
  norm_num
