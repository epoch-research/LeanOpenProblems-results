import FormalConjectures.Util.ProblemImports

open Nat Classical

/--
Riesel problem: let $k=2n-1$; then $a(n)=$smallest $m \ge 1$ such that $k \cdot 2^m-1$ is prime, or $-1$ if no such prime exists.
We use PNat for the exponent $m$ to correctly model $m \ge 1$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let k : ℕ := 2 * n - 1
    -- The predicate P(m) for m in PNat (m >= 1).
    let P (m : PNat) : Prop := (k * (2 ^ (m : ℕ)) - 1).Prime

    -- Use classical choice to find the minimum, or return -1 if no such prime exists.
    dite (∃ m : PNat, P m)
    (fun h_exists : ∃ m : PNat, P m =>
      -- PNat.find returns the minimum element. We coerce it to ℕ, then to ℤ.
      let m_min := PNat.find h_exists
      (m_min : ℕ)
    )
    (fun _ : ¬ ∃ m : PNat, P m =>
      (-1 : ℤ)
    )

/-!
### Machinery for the proof

We first prove that `509203` is a Riesel number: for every exponent `m ≥ 1`, the
number `509203 * 2 ^ m - 1` is composite.  This is witnessed by the classical
covering set `{3, 5, 7, 13, 17, 241}` of period `24`.
-/

/-- If `2 ^ 24 ≡ 1 [MOD p]`, then `2 ^ m ≡ 2 ^ (m % 24) [MOD p]`. -/
theorem pow2_mod (m p : ℕ) (h : (2:ℕ) ^ 24 ≡ 1 [MOD p]) :
    (2:ℕ) ^ m ≡ 2 ^ (m % 24) [MOD p] := by
  conv_lhs => rw [← Nat.div_add_mod m 24, pow_add, pow_mul]
  calc ((2:ℕ) ^ 24) ^ (m / 24) * 2 ^ (m % 24)
      ≡ 1 ^ (m / 24) * 2 ^ (m % 24) [MOD p] := Nat.ModEq.mul_right _ (h.pow _)
    _ = 2 ^ (m % 24) := by ring

/-- If `2 ^ 24 ≡ 1 [MOD p]` and `509203 * 2 ^ (m % 24) ≡ 1 [MOD p]`, then
`p ∣ 509203 * 2 ^ m - 1`. -/
theorem dvd_from (m p : ℕ) (h24 : (2:ℕ) ^ 24 ≡ 1 [MOD p])
    (hres : 509203 * 2 ^ (m % 24) ≡ 1 [MOD p]) : p ∣ (509203 * 2 ^ m - 1) := by
  have hmod : 509203 * 2 ^ m ≡ 1 [MOD p] :=
    (Nat.ModEq.mul_left 509203 (pow2_mod m p h24)).trans hres
  have hge : 1 ≤ 509203 * 2 ^ m := by
    have : 0 < 509203 * 2 ^ m := by positivity
    omega
  exact (Nat.modEq_iff_dvd' hge).mp hmod.symm

/-- `509203` is a Riesel number: `509203 * 2 ^ m - 1` is never prime for `m ≥ 1`.
The covering set `{3, 5, 7, 13, 17, 241}` (period 24) provides, for each residue
`m % 24`, a proper divisor. -/
theorem cover (m : ℕ) (hm : 1 ≤ m) : ¬ (509203 * 2 ^ m - 1).Prime := by
  intro hP
  have hNbig : 241 < 509203 * 2 ^ m - 1 := by
    have h2 : (2:ℕ) ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h3 : 509203 * 2 ^ 1 ≤ 509203 * 2 ^ m := Nat.mul_le_mul_left _ h2
    simp only [pow_one] at h3
    omega
  have close : ∀ p : ℕ, 2 ≤ p → p ≤ 241 → p ∣ (509203 * 2 ^ m - 1) → False := by
    intro p hp2 hp241 hdvd
    rcases hP.eq_one_or_self_of_dvd p hdvd with h1 | h1 <;> omega
  rcases (show m % 24 = 0 ∨ m % 24 = 1 ∨ m % 24 = 2 ∨ m % 24 = 3 ∨ m % 24 = 4 ∨
    m % 24 = 5 ∨ m % 24 = 6 ∨ m % 24 = 7 ∨ m % 24 = 8 ∨ m % 24 = 9 ∨ m % 24 = 10 ∨
    m % 24 = 11 ∨ m % 24 = 12 ∨ m % 24 = 13 ∨ m % 24 = 14 ∨ m % 24 = 15 ∨ m % 24 = 16 ∨
    m % 24 = 17 ∨ m % 24 = 18 ∨ m % 24 = 19 ∨ m % 24 = 20 ∨ m % 24 = 21 ∨ m % 24 = 22 ∨
    m % 24 = 23 by omega) with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 5 (by norm_num) (by norm_num) (dvd_from m 5 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 241 (by norm_num) (by norm_num) (dvd_from m 241 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 5 (by norm_num) (by norm_num) (dvd_from m 5 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 13 (by norm_num) (by norm_num) (dvd_from m 13 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 5 (by norm_num) (by norm_num) (dvd_from m 5 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 7 (by norm_num) (by norm_num) (dvd_from m 7 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 5 (by norm_num) (by norm_num) (dvd_from m 5 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 17 (by norm_num) (by norm_num) (dvd_from m 17 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 5 (by norm_num) (by norm_num) (dvd_from m 5 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 13 (by norm_num) (by norm_num) (dvd_from m 13 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 5 (by norm_num) (by norm_num) (dvd_from m 5 (by decide) (by rw [h]; decide))
  · exact close 3 (by norm_num) (by norm_num) (dvd_from m 3 (by decide) (by rw [h]; decide))
  · exact close 7 (by norm_num) (by norm_num) (dvd_from m 7 (by decide) (by rw [h]; decide))

/-- The first conjunct: `a 254602 = -1`, i.e. `509203` is a Riesel number. -/
theorem a_254602 : a 254602 = -1 := by
  unfold a
  rw [if_neg (by norm_num)]
  have hne : ¬ ∃ m : PNat, ((2 * 254602 - 1) * (2 ^ (m : ℕ)) - 1).Prime := by
    rintro ⟨m, hm⟩
    have h509203 : (2 * 254602 - 1) = 509203 := by norm_num
    rw [h509203] at hm
    exact cover (m : ℕ) m.pos hm
  rw [dif_neg hne]

/-- The reduction underlying the second conjunct: `a n ≠ -1` holds as soon as
`(2 * n - 1) * 2 ^ m - 1` is prime for some `m ≥ 1`. -/
theorem a_ne_neg_one (n : ℕ) (hn : n ≠ 0)
    (h : ∃ m : PNat, ((2 * n - 1) * 2 ^ (m : ℕ) - 1).Prime) : a n ≠ -1 := by
  unfold a
  rw [if_neg hn, dif_pos h]
  show (((PNat.find h : ℕ) : ℤ)) ≠ -1
  have hpos : (0:ℤ) ≤ ((PNat.find h : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

/--
It is conjectured that the integer k = 509203 is the smallest Riesel number,
that is, the first n such that a(n) = -1 is 254602.
-/
theorem oeis_a108129_conjecture_0 :
  a 254602 = -1 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 254602 → a n ≠ -1) :=
⟨a_254602, by sorry⟩
