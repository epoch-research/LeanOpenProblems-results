import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A236998: a(n) = |{0 < k < n/2: phi(k)*phi(n-k) is a square}|, where phi(.) is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

/-- A fast, factorization-based reformulation of Euler's totient, used only to make the
finite range verification computationally tractable. It agrees with `Nat.totient`
(see `T_eq`). -/
private def T (n : ℕ) : ℕ := (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1)

private lemma T_eq (n : ℕ) : T n = Nat.totient n :=
  (Nat.totient_eq_div_primeFactors_mul n).symm

/-- A decidable predicate witnessing `a n > 0`: there is some `0 < k ≤ (n-1)/2` with
`φ(k) * φ(n-k)` a perfect square. -/
private def good (n : ℕ) : Bool :=
  (List.range ((n - 1) / 2)).any (fun i =>
    let m := T (i + 1) * T (n - (i + 1)); Nat.sqrt m ^ 2 == m)

/-- If the witness predicate `good n` holds (for `n ≥ 9`), then `a n > 0`. This is the
mathematical content connecting the efficient check to the definition of `a`. -/
private lemma good_imp {n : ℕ} (hn : 9 ≤ n) (h : good n = true) : a n > 0 := by
  unfold good at h
  rw [List.any_eq_true] at h
  obtain ⟨i, hi_mem, hi⟩ := h
  rw [List.mem_range] at hi_mem
  simp only [beq_iff_eq] at hi
  set k := i + 1 with hk
  have hk1 : 1 ≤ k := Nat.le_add_left 1 i
  have hkn : k ≤ (n - 1) / 2 := hi_mem
  have hcond : Nat.sqrt (Nat.totient k * Nat.totient (n - k)) ^ 2
      = Nat.totient k * Nat.totient (n - k) := by
    rw [← T_eq k, ← T_eq (n - k)]; exact hi
  have hmem : k ∈ Ico 1 ((n - 1) / 2 + 1) := by
    rw [mem_Ico]; exact ⟨hk1, by omega⟩
  have hterm : (fun k => let m := totient k * totient (n - k);
      if sqrt m ^ 2 = m then (1 : ℕ) else 0) k = 1 := by
    simp only [hcond, if_pos]
  have hle := Finset.single_le_sum
    (f := fun k => let m := totient k * totient (n - k);
      if sqrt m ^ 2 = m then (1 : ℕ) else 0)
    (fun j _ => Nat.zero_le _) hmem
  rw [hterm] at hle
  exact lt_of_lt_of_le Nat.one_pos hle

/--
OEIS A236998 Conjecture (i) states that a(n) > 0 for all n > 8.
This theorem formalizes the claim about the verified range:
"For n from 9 to 2*10^6, a(n) > 0."
%C A236998 a(n) > 0 for all n > 8 has been verified for n up to 2*10^6.
-/
theorem oeis_236977_conjecture_1 (n : ℕ) (h_n : 9 ≤ n ∧ n ≤ 2 * 10^6) : a n > 0 := by
  have hrange : ∀ m ∈ Finset.Icc 9 2000000, good m = true := by native_decide
  exact good_imp h_n.1 (hrange n (Finset.mem_Icc.mpr ⟨h_n.1, h_n.2⟩))
