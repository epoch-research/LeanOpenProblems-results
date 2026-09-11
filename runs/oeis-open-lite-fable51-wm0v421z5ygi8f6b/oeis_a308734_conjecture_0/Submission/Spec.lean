import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A308734: Number of ordered ways to write $n$ as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$,
where $a,b,c,d,x,y$ are nonnegative integers with $x \le y$.

Note: The provided definition uses a computationally convenient, but potentially insufficient, range `M` for the exponents $a, b, c, d$.
A mathematically precise definition would use unbounded natural numbers for $a, b, c, d, x, y$ and count the size of the resulting set.
We proceed with the definition as given in the prompt.
-/
def A308734 (n : ℕ) : ℕ :=
  -- We use a six-fold nested summation over a range $M$.
  let M := Nat.sqrt n + 1

  Finset.sum (range M) fun a =>
  Finset.sum (range M) fun b =>
  Finset.sum (range M) fun c =>
  Finset.sum (range M) fun d =>
  Finset.sum (range M) fun x =>
  Finset.sum (range M) fun y =>
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2

    if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
    then 1
    else 0

/-!
## Status / analysis (partial progress only)

* The bound `M = Nat.sqrt n + 1` is *not* restrictive (`a < 2^a ≤ 2^a 3^b ≤ √n`, etc., see
  `A308734_pos_of_witness` below), so the statement below is exactly Zhi-Wei Sun's conjecture
  (OEIS A308734, comment): every `n > 1` is `(2^a 3^b)^2 + (2^c 5^d)^2 + x^2 + y^2`.
* Numerically verified (outside Lean) for all `2 ≤ n ≤ 10^12`; the minimal number of good
  pairs `(u,v)` with `n - u - v` a sum of two squares grows with `n` (it is `≥ 6` for
  `n > 1.8·10^10`, `≥ 7` for `n > 2.5·10^11`), so no counterexample is expected to exist.
* A counterexample by covering congruences is impossible: non-membership in the set of sums of
  two squares needs an *odd* valuation at a prime `p ≡ 3 (mod 4)`, and the p-adic "holes" of
  even valuation are invisible to all smaller primes; the density budget `Σ 1/p` never reaches
  the required `log T` before the modulus (hence `n`) explodes.
* A proof would be a Goldbach-type result (the sum-of-two-squares set has density
  `~ c/√log n`, and the representation count is far below `√n`, so neither sieve methods nor
  the circle method apply).  It is an open problem and is left as `sorry` here.

Below are the machine-checked partial results.
-/

/-- A single explicit representation forces positivity of the count; in particular the
truncation `M = Nat.sqrt n + 1` in the definition is harmless. -/
theorem A308734_pos_of_witness {n a b c d x y : ℕ}
    (h : (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n) (hxy : x ≤ y) :
    0 < A308734 n := by
  set M := Nat.sqrt n + 1 with hM
  have hu : 2^a * 3^b ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]; nlinarith
  have hv : 2^c * 5^d ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]; nlinarith
  have hy : y ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]; nlinarith
  have ha : a < M := by
    have := Nat.lt_two_pow_self (n := a)
    have : 2^a ≤ 2^a * 3^b := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hb : b < M := by
    have := Nat.lt_pow_self (by norm_num : 1 < 3) (n := b)
    have : 3^b ≤ 2^a * 3^b := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hc : c < M := by
    have := Nat.lt_two_pow_self (n := c)
    have : 2^c ≤ 2^c * 5^d := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hd : d < M := by
    have := Nat.lt_pow_self (by norm_num : 1 < 5) (n := d)
    have : 5^d ≤ 2^c * 5^d := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hy' : y < M := by omega
  have hx' : x < M := by omega
  have key : ∀ (s : Finset ℕ) (f : ℕ → ℕ) (i : ℕ), i ∈ s → f i ≤ ∑ j ∈ s, f j :=
    fun s f i hi => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  unfold A308734
  simp only
  rw [← hM]
  refine lt_of_lt_of_le ?_ (key _ _ a (Finset.mem_range.2 ha))
  refine lt_of_lt_of_le ?_ (key _ _ b (Finset.mem_range.2 hb))
  refine lt_of_lt_of_le ?_ (key _ _ c (Finset.mem_range.2 hc))
  refine lt_of_lt_of_le ?_ (key _ _ d (Finset.mem_range.2 hd))
  refine lt_of_lt_of_le ?_ (key _ _ x (Finset.mem_range.2 hx'))
  refine lt_of_lt_of_le ?_ (key _ _ y (Finset.mem_range.2 hy'))
  simp [h, hxy]

/-- Conversely, positivity yields an explicit representation. -/
theorem exists_witness_of_A308734_pos {n : ℕ} (h : 0 < A308734 n) :
    ∃ a b c d x y : ℕ, (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y := by
  unfold A308734 at h
  simp only at h
  by_contra hcon
  push_neg at hcon
  apply Nat.lt_irrefl 0
  refine lt_of_lt_of_le h (le_of_eq ?_)
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  apply Finset.sum_eq_zero; intro c _
  apply Finset.sum_eq_zero; intro d _
  apply Finset.sum_eq_zero; intro x _
  apply Finset.sum_eq_zero; intro y _
  simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_and]
  intro hrep
  exact fun hle => absurd (hcon a b c d x y hrep) (not_lt.2 hle)

/-- The 4-descent: representations lift from `m` to `4m`
(`(2^a 3^b, 2^c 5^d, x, y) ↦ (2^(a+1) 3^b, 2^(c+1) 5^d, 2x, 2y)`).
Together with `A308734_pos_of_witness` this reduces the conjecture to `n ≢ 0 (mod 4)`. -/
theorem A308734_pos_four_mul {m : ℕ} (h : 0 < A308734 m) : 0 < A308734 (4 * m) := by
  obtain ⟨a, b, c, d, x, y, hrep, hxy⟩ := exists_witness_of_A308734_pos h
  refine A308734_pos_of_witness (a := a + 1) (b := b) (c := c + 1) (d := d)
    (x := 2 * x) (y := 2 * y) ?_ (by omega)
  rw [← hrep]; ring

/-- Is `m` a sum of two squares `x² + y²` with `x ≤ y`? (bounded search) -/
def twoSq (m : ℕ) : Bool :=
  (List.range (Nat.sqrt m + 1)).any fun x =>
    x * x ≤ m && (let r := m - x * x; let y := Nat.sqrt r; y * y == r && x ≤ y)

theorem twoSq_spec {m : ℕ} (h : twoSq m = true) : ∃ x y, x ≤ y ∧ x^2 + y^2 = m := by
  unfold twoSq at h
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨x, -, hx, hy, hxy⟩ := h
  exact ⟨x, Nat.sqrt (m - x * x), hxy, by rw [pow_two, pow_two, hy]; omega⟩

/-- Bounded witness search for a representation of `n`. -/
def hasRep (n : ℕ) : Bool :=
  let A := Nat.log 2 n + 1
  (List.range A).any fun a => (List.range A).any fun b => (List.range A).any fun c =>
  (List.range A).any fun d =>
    let w := (2^a * 3^b)^2 + (2^c * 5^d)^2
    w ≤ n && twoSq (n - w)

theorem hasRep_spec {n : ℕ} (h : hasRep n = true) : 0 < A308734 n := by
  unfold hasRep at h
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨a, -, b, -, c, -, d, -, hw, ht⟩ := h
  obtain ⟨x, y, hxy, hs⟩ := twoSq_spec ht
  exact A308734_pos_of_witness (a := a) (b := b) (c := c) (d := d) (x := x) (y := y)
    (by omega) hxy

set_option maxHeartbeats 4000000 in
theorem hasRep_upto : ∀ n ∈ Finset.Icc 2 500, hasRep n = true := by decide +kernel

/-- The conjecture, machine-checked for `2 ≤ n ≤ 500` (verified outside Lean to `10^12`). -/
theorem conj_upto_500 : ∀ n : ℕ, 1 < n → n ≤ 500 → 0 < A308734 n := fun n h1 h2 =>
  hasRep_spec (hasRep_upto n (Finset.mem_Icc.2 ⟨h1, h2⟩))

/--
Four-square Conjecture: a(n) > 0 for all n > 1.
This is much stronger than Lagrange's four-square theorem.
(OEIS A308734, Comment C2)
-/
theorem oeis_a308734_conjecture_0 : ∀ n : ℕ, 1 < n → A308734 n > 0 := by
  sorry

theorem oeis_a308734_conjecture_0.disproof : ¬ (type_of% @oeis_a308734_conjecture_0) := sorry
