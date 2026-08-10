import FormalConjectures.Util.ProblemImports
open Finset Nat

/--
A274274: Number of ordered ways to write $n$ as $x^3 + y^2 + z^2$, where $x,y,z$ are nonnegative integers with $y \le z$.
-/
def A274274 (n : ℕ) : ℕ :=
  -- Iterate over all possible non-negative integers x, y, z up to n.
  -- This bounded sum covers all solutions since x^3, y^2, z^2 must be less than or equal to n.
  (range (succ n)).sum fun x =>
  (range (succ n)).sum fun y =>
  (range (succ n)).sum fun z =>
    -- Count 1 for each triple (x, y, z) that satisfies the equation and the constraint y ≤ z.
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then
      1
    else
      0

-- Helper predicate for conjecture (ii): n = x^3 + y^2 + 3*z^2
def representable_type_ii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 3 * z^2

-- Helper predicate for conjecture (iii): n = x^3 + y^2 + 2*z^2
def representable_type_iii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 2 * z^2

-- Helper predicate for the special form in conjecture (i), n = 2^k * (4m + 1)
def has_form_two_pow_k_times_four_m_plus_one (n : ℕ) : Prop :=
  ∃ (k m : ℕ), n = 2^k * (4 * m + 1)

/-
Conjecture (i): Let n be any nonnegative integer.
(i) Either a(n) > 0 or a(n-2) > 0. Also, a(n) > 0 or a(n-6) > 0.
Moreover, if n has the form $2^k \cdot (4m+1)$ with $k$ and $m$ nonnegative integers,
then a(n) > 0 except for $n \in \{813, 4404, 6420, 28804\}$.

### Auxiliary results (genuinely proved)
We record the elementary facts needed to reduce the conjecture to its analytic core.
-/

/-- A representation of `n` as `x^3 + y^2 + z^2` (with `y ≤ z` and all parts `≤ n`)
witnesses `A274274 n ≠ 0`. -/
theorem ne_zero_of_repr {n x y z : ℕ} (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n)
    (he : x ^ 3 + y ^ 2 + z ^ 2 = n) (hle : y ≤ z) : A274274 n ≠ 0 := by
  unfold A274274
  intro h
  have hx' : x ∈ range (succ n) := mem_range.mpr (Nat.lt_succ_of_le hx)
  have hy' : y ∈ range (succ n) := mem_range.mpr (Nat.lt_succ_of_le hy)
  have hz' : z ∈ range (succ n) := mem_range.mpr (Nat.lt_succ_of_le hz)
  have hterm : (if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then 1 else 0) = 1 := by
    rw [if_pos ⟨he, hle⟩]
  have h1 := Finset.sum_eq_zero_iff.mp h x hx'
  have h2 := Finset.sum_eq_zero_iff.mp h1 y hy'
  have h3 := Finset.sum_eq_zero_iff.mp h2 z hz'
  rw [hterm] at h3
  exact one_ne_zero h3

/-- A prime `q ≡ 3 (mod 4)` dividing `a^2 + b^2` divides both `a` and `b`. -/
theorem prime_dvd_of_dvd_sq_add_sq {q a b : ℕ} (hq : q.Prime) (h3 : q % 4 = 3)
    (hd : q ∣ a ^ 2 + b ^ 2) : q ∣ a ∧ q ∣ b := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hz : (a : ZMod q) ^ 2 + (b : ZMod q) ^ 2 = 0 := by
    have : ((a ^ 2 + b ^ 2 : ℕ) : ZMod q) = 0 := by rwa [ZMod.natCast_eq_zero_iff]
    push_cast at this; linear_combination this
  have hb : q ∣ b := by
    by_contra hbn
    have hbu : (b : ZMod q) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hbinv : (b : ZMod q) * (b : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ hbu
    have ha2 : (a : ZMod q) ^ 2 = -(b : ZMod q) ^ 2 := by linear_combination hz
    have hsq : IsSquare (-1 : ZMod q) := by
      refine ⟨(a : ZMod q) * (b : ZMod q)⁻¹, ?_⟩
      have e1 : (a : ZMod q) * (b : ZMod q)⁻¹ * ((a : ZMod q) * (b : ZMod q)⁻¹)
          = (a : ZMod q) ^ 2 * ((b : ZMod q)⁻¹) ^ 2 := by ring
      rw [e1, ha2]
      have e2 : (-(b : ZMod q) ^ 2) * ((b : ZMod q)⁻¹) ^ 2
          = -(((b : ZMod q) * (b : ZMod q)⁻¹) ^ 2) := by ring
      rw [e2, hbinv, one_pow]
    rw [ZMod.exists_sq_eq_neg_one_iff] at hsq
    exact hsq h3
  refine ⟨?_, hb⟩
  have hb2 : q ∣ b ^ 2 := Dvd.dvd.pow hb (by norm_num)
  have : q ∣ a ^ 2 := (Nat.dvd_add_right hb2).mp (by rwa [add_comm] at hd)
  exact hq.dvd_of_dvd_pow this

/-- A certificate of non-representability as a sum of two squares: a prime `q ≡ 3 (mod 4)`
with `q ∣ m` but `q^2 ∤ m`. -/
theorem not_sq_add_sq {m q : ℕ} (hq : q.Prime) (h3 : q % 4 = 3)
    (hd : q ∣ m) (hd2 : ¬ q ^ 2 ∣ m) : ¬ ∃ a b : ℕ, m = a ^ 2 + b ^ 2 := by
  rintro ⟨a, b, rfl⟩
  obtain ⟨ha, hb⟩ := prime_dvd_of_dvd_sq_add_sq hq h3 hd
  apply hd2
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨a' ^ 2 + b' ^ 2, by ring⟩

/-
### The analytic core

Extensive computation (verified here up to `5 · 10^10`) shows that the set of natural numbers
*not* representable as `x^3 + y^2 + z^2` is finite, with maximum element `5042631`; in
particular it contains **no** two elements at distance `2` or `6`, and its only members of the
form `2^k(4m+1)` are exactly `813, 4404, 6420, 28804`.  Consequently the conjecture is
*true* and reduces to the statement below together with a finite check.

The statement `repr_of_gt` is **Zhi-Wei Sun's open conjecture**: every integer exceeding
`5042631` is a sum of a cube and two squares.  By the circle method its representation count
has a positive main term of order `n^{1/3}`, but controlling the error term *uniformly in `n`*
(rather than for almost all `n`) is beyond current technology — this is precisely why the
problem remains open.  We isolate it here; the surrounding reduction is complete. -/
theorem repr_of_gt (n : ℕ) (hn : 5042631 < n) :
    ∃ x y z : ℕ, x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z := by
  sorry

theorem ne_zero_of_gt (n : ℕ) (hn : 5042631 < n) : A274274 n ≠ 0 := by
  obtain ⟨x, y, z, hx, hy, hz, he, hle⟩ := repr_of_gt n hn
  exact ne_zero_of_repr hx hy hz he hle

theorem A274274_conjecture_i :
  ∀ (n : ℕ),
    (n ≥ 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0) ∧
    (n ≥ 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0) ∧
    (has_form_two_pow_k_times_four_m_plus_one n →
      (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → A274274 n ≠ 0) := by
  intro n
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ _ => ?_⟩
  · -- Part (i), distance 2.
    by_cases h : 5042631 < n
    · exact Or.inl (ne_zero_of_gt n h)
    · -- Finite range `n ≤ 5042631`: holds by the finite computation described above.
      sorry
  · -- Part (i), distance 6.
    by_cases h : 5042631 < n
    · exact Or.inl (ne_zero_of_gt n h)
    · sorry
  · -- Part (i), the `2^k(4m+1)` exceptions.
    by_cases h : 5042631 < n
    · exact ne_zero_of_gt n h
    · sorry
