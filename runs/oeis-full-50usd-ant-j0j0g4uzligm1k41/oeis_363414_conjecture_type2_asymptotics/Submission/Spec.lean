import FormalConjectures.Util.ProblemImports

open Nat Finset Complex Real

/--
A363414: $a(n) = (1/2) \cdot \operatorname{Im}\left( \prod_{k = 0}^{n} (1 + k\sqrt{-4}) \right)$.
The sequence values are integers.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Complex :=
    Finset.prod (range (n + 1))
    (fun k : ℕ ↦ (1 : Complex) + ((2 * k : ℕ) : ℝ) * Complex.I)

  Int.floor (P_n.im / 2)

open Filter Asymptotics ZMod Int

/--
The set of primes of type 2 for A363414 is conjecturally
$\mathbb{P}_2 = \{p \mid p \equiv 1 \pmod 4\}$.
-/
def type_two_primes_conjectured : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ (p : ZMod 4) = 1}

/-
### Reduction infrastructure

We record the integer real and imaginary parts of the Gaussian product
`P n = ∏_{k=0}^{n} (1 + 2ki)` via the recurrence coming from multiplication by
`(1 + 2(n+1)i)`, and reduce the statement about `padicValInt p (a n)` to a
statement about `padicValInt p (Y n)`, where `Y n = 2 * a n` is the imaginary
part of `P n`.
-/

/-- Integer real/imaginary parts of `∏_{k=0}^{n}(1+2ki)` via the recurrence. -/
def xy : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | (n+1) => let p := xy n; (p.1 - 2*(n+1)*p.2, 2*(n+1)*p.1 + p.2)

/-- Real part `Re(∏_{k=0}^{n}(1+2ki))`. -/
def X (n : ℕ) : ℤ := (xy n).1
/-- Imaginary part `Im(∏_{k=0}^{n}(1+2ki))`. -/
def Y (n : ℕ) : ℤ := (xy n).2

/-- The complex product `∏_{k=0}^{n}(1+2ki)`. -/
noncomputable def P (n : ℕ) : Complex :=
  Finset.prod (range (n + 1)) (fun k : ℕ ↦ (1 : Complex) + ((2 * k : ℕ) : ℝ) * Complex.I)

theorem P_re_im (n : ℕ) : P n = (X n : ℂ) + (Y n : ℂ) * Complex.I := by
  induction n with
  | zero => simp [P, X, Y, xy]
  | succ m ih =>
    rw [P, Finset.prod_range_succ, ← P, ih]
    simp only [X, Y, xy]
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring

/-- The norm `Dn n = ∏_{k=0}^{n}(1 + 4 k^2)`. -/
def Dn (n : ℕ) : ℤ := Finset.prod (range (n+1)) (fun k => 1 + 4 * (k:ℤ)^2)

theorem Dn_succ (n : ℕ) : Dn (n+1) = Dn n * (1 + 4 * ((n:ℤ)+1)^2) := by
  simp only [Dn, Finset.prod_range_succ]
  push_cast; ring

/-- The norm identity `X n ^ 2 + Y n ^ 2 = ∏_{k=0}^{n}(1 + 4 k^2)`. -/
theorem norm_identity (n : ℕ) : (X n)^2 + (Y n)^2 = Dn n := by
  induction n with
  | zero => simp [X, Y, xy, Dn]
  | succ m ih =>
    rw [Dn_succ, ← ih]
    simp only [X, Y, xy]
    ring

theorem P_im (n : ℕ) : (P n).im = (Y n : ℝ) := by
  rw [P_re_im]; simp

/-- The recurrence `xy (n+1)` in terms of `xy n`. -/
theorem xy_succ (n : ℕ) :
    X (n+1) = X n - 2*((n:ℤ)+1) * Y n ∧ Y (n+1) = 2*((n:ℤ)+1) * X n + Y n := by
  refine ⟨?_, ?_⟩ <;>
    · simp only [X, Y, xy]
      try push_cast
      try ring

/-- A clean second–order linear recurrence with polynomial coefficients for
`Y n = Im(∏_{k=0}^{n}(1+2ki))`:
`(k+1) · Y (k+2) = (2k+3) · Y (k+1) − (k+2)(1+4(k+1)²) · Y k`.
(Obtained by eliminating `X` from the two first–order relations.) -/
theorem Y_recurrence (k : ℕ) :
    ((k:ℤ)+1) * Y (k+2)
      = (2*(k:ℤ)+3) * Y (k+1) - ((k:ℤ)+2) * (1 + 4*((k:ℤ)+1)^2) * Y k := by
  obtain ⟨hX1, hY1⟩ := xy_succ k
  obtain ⟨hX2, hY2⟩ := xy_succ (k+1)
  rw [hY2, hX1, hY1]
  push_cast
  ring

theorem Y_even (n : ℕ) : (2 : ℤ) ∣ Y n := by
  induction n with
  | zero => simp [Y, xy]
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(m+1) * X m + c, ?_⟩
    have : Y (m+1) = 2*((m:ℤ)+1) * X m + Y m := by
      simp only [Y, X, xy]
    rw [this, hc]; ring

/-- `a n = Y n / 2` (exact, since `Y n` is even). -/
theorem a_eq (n : ℕ) : a n = Y n / 2 := by
  have h : a n = ⌊(P n).im / 2⌋ := rfl
  rw [h, P_im]
  obtain ⟨c, hc⟩ := Y_even n
  rw [hc]
  push_cast
  have : (2 * (c:ℝ)) / 2 = (c:ℝ) := by ring
  rw [this, Int.floor_intCast, Int.mul_ediv_cancel_left _ (by norm_num : (2:ℤ) ≠ 0)]

/-- `Y n = 2 * a n`. -/
theorem Y_eq (n : ℕ) : Y n = 2 * a n := by
  rw [a_eq]
  obtain ⟨c, hc⟩ := Y_even n
  rw [hc, Int.mul_ediv_cancel_left _ (by norm_num : (2:ℤ) ≠ 0)]

/-- For odd `p`, `padicValInt p (a n) = padicValInt p (Y n)`. -/
theorem val_reduction (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (n : ℕ) :
    padicValInt p (a n) = padicValInt p (Y n) := by
  haveI := Fact.mk hp
  rcases eq_or_ne (a n) 0 with h0 | h0
  · rw [Y_eq, h0]; simp
  · rw [Y_eq, padicValInt.mul (by norm_num) h0]
    have h2 : padicValInt p 2 = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro hd
      have : p ∣ 2 := by exact_mod_cast hd
      rw [Nat.dvd_prime (by norm_num)] at this
      rcases this with h | h
      · exact hp.ne_one h
      · exact hodd h
    rw [h2, zero_add]

/-
### The analytic core

By the above reduction, the conjecture is equivalent to the statement that the
`p`-adic valuation of the imaginary part `Y n = Im(∏_{k=0}^{n}(1+2ki))` is
asymptotically `n / (p - 1)`.

Since `p ≡ 1 (mod 4)`, the prime `p` splits in `ℤ[i]` as `p = π · π̄` and there is
a square root `j` of `-1` in `ℤ_p`. Writing `u n = ∏(1+2kj)` and `w n = ∏(1-2kj)`
(the images of `P n` and its conjugate under `i ↦ j`), one has
`Y n = (u n - w n)/(2j)` and `X n ^ 2 + Y n ^ 2 = u n · w n = ∏(1+4k^2)`.

* A Legendre / lattice-point count over the residues `k ≡ ∓(2j)⁻¹ (mod p^m)`
  gives `ν_p(u n), ν_p(w n) = n/(p-1) + o(n)`, from which
  `ν_p(Y n) ≥ min(ν_p(u n), ν_p(w n)) = n/(p-1) - o(n)` (lower bound), and
  `ν_p(∏(1+4k^2)) = 2n/(p-1) + o(n)` (using that each factor `1+4k^2 ≤ 1+4n^2`
  has valuation `O(log n)`).

* The remaining "excess" `ν_p(Y n) - min(ν_p(u n), ν_p(w n))`, nonzero exactly when
  `ν_p(u n) = ν_p(w n)` and measuring the extra `p`-adic cancellation in
  `u n - w n`, is empirically `O(log n) = o(n)`; its rigorous control is the
  content of Moll's conjecture 5.5 for this sequence (a `p`-adic Γ /
  non-vanishing estimate).
-/
theorem core_asymptotic (p : ℕ) (hp : Nat.Prime p)
    (hmem : p ∈ type_two_primes_conjectured) :
    (fun n ↦ (padicValInt p (Y n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) / ((p : ℝ) - 1)) := by
  sorry

/--
Moll's conjecture 5.5 extends to this sequence:
for the primes of type 2, the p-adic valuation $\nu_p(a(n)) \sim n/(p - 1)$ as $n \to \infty$.
This is formalized using asymptotic equivalence (`~[atTop]`) for the p-adic valuation
(`padicValInt`) converted to a real number.
-/
theorem oeis_363414_conjecture_type2_asymptotics :
  ∀ p : ℕ, Nat.Prime p → p ∈ type_two_primes_conjectured →
  (fun n ↦ (padicValInt p (a n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) / ((p : ℝ) - 1)) := by
  intro p hp hmem
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hmem.2 (by decide)
  have hfun : (fun n ↦ (padicValInt p (a n) : ℝ)) = (fun n ↦ (padicValInt p (Y n) : ℝ)) := by
    funext n; rw [val_reduction p hp hp2 n]
  rw [hfun]
  exact core_asymptotic p hp hmem
