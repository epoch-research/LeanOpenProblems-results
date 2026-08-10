import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

/-- Copy of the sequence from `Spec.lean`. -/
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

/-- The summand. -/
noncomputable def term (k : ℕ) : ℤ := (-1 : ℤ) ^ (⌊((3:ℝ)/2)^(k+1)⌋).toNat

lemma a_eq (n : ℕ) : a n = - Finset.sum (Finset.range n) term := rfl

/-- `(3/2)^(k+1) ≥ 1`. -/
lemma one_le_pow32 (k : ℕ) : (1:ℝ) ≤ ((3:ℝ)/2)^(k+1) := by
  calc (1:ℝ) = 1^(k+1) := (one_pow _).symm
    _ ≤ ((3:ℝ)/2)^(k+1) := by gcongr; norm_num

/-- The floor is positive. -/
lemma floor_pos32 (k : ℕ) : 0 < ⌊((3:ℝ)/2)^(k+1)⌋ := by
  have h1 : (1:ℤ) ≤ ⌊((3:ℝ)/2)^(k+1)⌋ := by
    apply Int.le_floor.mpr
    exact_mod_cast one_le_pow32 k
  omega

/-- Each summand is `≤ 1`. -/
lemma term_le_one (k : ℕ) : term k ≤ 1 := by
  have habs : |term k| = 1 := by
    unfold term; rw [abs_pow]; norm_num
  calc term k ≤ |term k| := le_abs_self _
    _ = 1 := habs

/-- If the floor is odd, the summand equals `-1`. -/
lemma term_of_odd {k : ℕ} (h : Odd (⌊((3:ℝ)/2)^(k+1)⌋)) : term k = -1 := by
  unfold term
  have hnn : 0 ≤ ⌊((3:ℝ)/2)^(k+1)⌋ := le_of_lt (floor_pos32 k)
  have hodd : Odd ((⌊((3:ℝ)/2)^(k+1)⌋).toNat) := by
    have heq : ((⌊((3:ℝ)/2)^(k+1)⌋).toNat : ℤ) = ⌊((3:ℝ)/2)^(k+1)⌋ :=
      Int.toNat_of_nonneg hnn
    rw [← Int.odd_coe_nat, heq]
    exact h
  exact Odd.neg_one_pow hodd

/-- Recurrence: `a (n+1) = a n - term n`. -/
lemma a_succ (n : ℕ) : a (n+1) = a n - term n := by
  simp only [a_eq, Finset.sum_range_succ]
  ring

/-- If from `M` on the floor is always odd, then `a (M + j) = a M + j`. -/
lemma a_linear {M : ℕ} (hodd : ∀ k, M ≤ k → Odd (⌊((3:ℝ)/2)^(k+1)⌋)) :
    ∀ j : ℕ, a (M + j) = a M + j := by
  intro j
  induction j with
  | zero => simp
  | succ i ih =>
      have hrec : a (M + i + 1) = a (M + i) - term (M + i) := a_succ (M + i)
      have ht : term (M + i) = -1 := term_of_odd (hodd (M + i) (Nat.le_add_right M i))
      rw [show M + (i+1) = (M + i) + 1 from by ring, hrec, ht, ih]
      push_cast
      ring

/-- **Reduction lemma.** If `⌊(3/2)ᵏ⌋` is odd for all large `k`
    (equivalently: `⌊(3/2)ᵏ⌋` is even only finitely often), then the
    OEIS A071532 conjecture `C : ∃ N, ∀ n ≥ N, a n > √n` holds.

    Contrapositively, the disproof `¬C` implies `⌊(3/2)ᵏ⌋` is even for
    infinitely many `k` — a recognized open problem in the theory of the
    distribution of `(3/2)ⁿ mod 1`. This is why the conjecture cannot be
    settled by elementary means. -/
theorem reduction
    (h : ∃ M : ℕ, ∀ k : ℕ, M ≤ k → Odd (⌊((3:ℝ)/2)^(k+1)⌋)) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > Real.sqrt (n : ℝ) := by
  obtain ⟨M, hM⟩ := h
  set c : ℤ := a M - M with hc
  -- For n ≥ M, a n = n + c  (as reals).
  have key : ∀ n : ℕ, M ≤ n → (a n : ℝ) = (n : ℝ) + (c : ℝ) := by
    intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [a_linear hM j]
    simp only [hc]
    push_cast
    ring
  -- a M ≥ -M since every summand is ≤ 1.
  have haM : (-(M:ℤ)) ≤ a M := by
    rw [a_eq]
    have hle : Finset.sum (Finset.range M) term ≤ (M : ℤ) := by
      calc Finset.sum (Finset.range M) term
          ≤ Finset.sum (Finset.range M) (fun _ => (1:ℤ)) :=
            Finset.sum_le_sum (fun k _ => term_le_one k)
        _ = (M : ℤ) := by simp
    linarith
  refine ⟨4 * M + 5, ?_⟩
  intro n hn
  have hMn : M ≤ n := by omega
  have hn4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 4 ≤ n by omega)
  have hnbig : (4 * (M:ℝ)) < (n:ℝ) := by exact_mod_cast (show 4 * M < n by omega)
  rw [key n hMn]
  -- bounds
  have haMr : (-(M:ℝ)) ≤ (a M : ℝ) := by exact_mod_cast haM
  have hcr : (c:ℝ) = (a M : ℝ) - (M:ℝ) := by rw [hc]; push_cast; ring
  have hc_ge : -(2 * (M:ℝ)) ≤ (c:ℝ) := by rw [hcr]; linarith
  have hsqrt : Real.sqrt (n:ℝ) ≤ (n:ℝ)/2 := by
    rw [show (n:ℝ)/2 = Real.sqrt (((n:ℝ)/2)^2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [hn4, mul_nonneg (by linarith [hn4] : (0:ℝ) ≤ (n:ℝ))
      (by linarith [hn4] : (0:ℝ) ≤ (n:ℝ) - 4)]
  have hstep : (n:ℝ)/2 < (n:ℝ) + (c:ℝ) := by linarith [hc_ge, hnbig]
  linarith [hsqrt, hstep]

/-- **Contrapositive.** Any proof of the *disproof* `¬C` of the A071532
    conjecture yields a proof that `⌊(3/2)ᵏ⌋` is **even for infinitely many
    `k`** (for every `M` there is `k ≥ M` with even floor).

    The latter is an acknowledged open problem on the distribution of
    `(3/2)ⁿ mod 1`; hence the disproof cannot be obtained by elementary
    means. Combined with the fact that the conjecture `C` itself is
    (empirically) false, this shows the statement is genuinely open. -/
theorem disproof_needs_even_infinitely_often
    (hC : ¬ (∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > Real.sqrt (n : ℝ))) :
    ∀ M : ℕ, ∃ k : ℕ, M ≤ k ∧ Even (⌊((3:ℝ)/2)^(k+1)⌋) := by
  intro M
  by_contra hcon
  push_neg at hcon
  exact hC (reduction ⟨M, fun k hk => Int.not_even_iff_odd.mp (hcon k hk)⟩)

/-- A clean *sufficient* condition for the disproof: if `a n ≤ 0` for
    infinitely many `n`, then the conjecture `C` is false. Numerically
    `a n < 0` does occur (e.g. `a 400000 < 0`), but proving that it recurs
    for arbitrarily large `n` is a recurrence statement about the ±1 walk
    `a`, again equivalent in difficulty to the open distribution problem
    for `(3/2)ⁿ mod 1`. -/
theorem disproof_of_nonpos_infinitely_often
    (h : ∀ M : ℕ, ∃ n : ℕ, M ≤ n ∧ a n ≤ 0) :
    ¬ (∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > Real.sqrt (n : ℝ)) := by
  rintro ⟨N, hN⟩
  obtain ⟨n, hNn, hn0⟩ := h N
  have h1 : (a n : ℝ) > Real.sqrt (n : ℝ) := hN n hNn
  have h2 : (a n : ℝ) ≤ 0 := by exact_mod_cast hn0
  have h3 : (0:ℝ) ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
  linarith

/-- **Skew‑product structural identity.** For every `n`,
    `3·⌊(3/2)ⁿ⌋ − 2·⌊(3/2)ⁿ⁺¹⌋ ∈ {−2,−1,0,1}`. Since this quantity is
    `≡ ⌊(3/2)ⁿ⌋ (mod 2)`, the floor `⌊(3/2)ⁿ⌋` is **even** iff it equals
    `−2` or `0`. This exhibits the exact coupling (parity ↔ an expanding
    `×3/2` skew map on fractional parts) that makes the parity sequence
    intractable by elementary means. -/
theorem floor_skew_relation (n : ℕ) :
    -2 ≤ 3 * ⌊((3:ℝ)/2)^n⌋ - 2 * ⌊((3:ℝ)/2)^(n+1)⌋ ∧
      3 * ⌊((3:ℝ)/2)^n⌋ - 2 * ⌊((3:ℝ)/2)^(n+1)⌋ ≤ 1 := by
  have hx : ((3:ℝ)/2)^(n+1) = (3/2) * ((3:ℝ)/2)^n := by rw [pow_succ]; ring
  have h1 : (⌊((3:ℝ)/2)^n⌋ : ℝ) ≤ ((3:ℝ)/2)^n := Int.floor_le _
  have h2 : ((3:ℝ)/2)^n < (⌊((3:ℝ)/2)^n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (⌊((3:ℝ)/2)^(n+1)⌋ : ℝ) ≤ (3/2) * ((3:ℝ)/2)^n := by
    rw [hx]; exact Int.floor_le _
  have h4 : (3/2) * ((3:ℝ)/2)^n < (⌊((3:ℝ)/2)^(n+1)⌋ : ℝ) + 1 := by
    rw [hx]; exact Int.lt_floor_add_one _
  constructor
  · have hr : (-3 : ℝ) < ((3 * ⌊((3:ℝ)/2)^n⌋ - 2 * ⌊((3:ℝ)/2)^(n+1)⌋ : ℤ) : ℝ) := by
      push_cast; linarith [h2, h3]
    have : (-3 : ℤ) < 3 * ⌊((3:ℝ)/2)^n⌋ - 2 * ⌊((3:ℝ)/2)^(n+1)⌋ := by exact_mod_cast hr
    omega
  · have hr : ((3 * ⌊((3:ℝ)/2)^n⌋ - 2 * ⌊((3:ℝ)/2)^(n+1)⌋ : ℤ) : ℝ) < 2 := by
      push_cast; linarith [h1, h4]
    have : 3 * ⌊((3:ℝ)/2)^n⌋ - 2 * ⌊((3:ℝ)/2)^(n+1)⌋ < (2:ℤ) := by exact_mod_cast hr
    omega
