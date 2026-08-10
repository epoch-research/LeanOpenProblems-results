import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A335624: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + 3y + 4z$ a square,
where $x, y, z, w$ are nonnegative integers.
-/
def A335624 (n : ℕ) : ℕ :=
  -- The variables x, y, z, w are bounded by sqrt(n), since they are non-negative.
  let B : ℕ := Nat.sqrt n + 1
  let R := range B

  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n
      -- The term x + 3*y + 4*z must be a perfect square.
      ∧ (let m := x + 3 * y + 4 * z; Nat.sqrt m ^ 2 = m)
    then 1 else 0

/- ### Reformulation as an existence statement

`A335624 n = 0` is equivalent to the *non-existence* of a representation. We package the
representation as a clean predicate `Repr335624`. -/

/-- `n` is representable as `x²+y²+z²+w²` with `x+3y+4z` a perfect square. -/
def Repr335624 (n : ℕ) : Prop :=
  ∃ x y z w : ℕ, x^2 + y^2 + z^2 + w^2 = n ∧ IsSquare (x + 3 * y + 4 * z)

theorem isSquare_iff_sqrt (m : ℕ) : IsSquare m ↔ Nat.sqrt m ^ 2 = m := by
  constructor
  · rintro ⟨r, rfl⟩; rw [Nat.sqrt_eq, pow_two]
  · intro h; exact ⟨Nat.sqrt m, by rw [pow_two] at h; exact h.symm⟩

/-- The counting function vanishes iff there is no representation at all. -/
theorem A335624_eq_zero_iff (n : ℕ) : A335624 n = 0 ↔ ¬ Repr335624 n := by
  unfold A335624 Repr335624
  simp only [Finset.sum_eq_zero_iff, Finset.mem_range, ite_eq_right_iff, one_ne_zero,
    imp_false, not_and, not_exists]
  constructor
  · intro h x y z w hsum hsq
    have hb : ∀ t : ℕ, t^2 ≤ n → t < Nat.sqrt n + 1 := by
      intro t ht; have := Nat.le_sqrt.mpr (by simpa [pow_two] using ht); omega
    have hx : x < Nat.sqrt n + 1 := hb x (by nlinarith [hsum, sq_nonneg y, sq_nonneg z, sq_nonneg w])
    have hy : y < Nat.sqrt n + 1 := hb y (by nlinarith [hsum, sq_nonneg x, sq_nonneg z, sq_nonneg w])
    have hz : z < Nat.sqrt n + 1 := hb z (by nlinarith [hsum, sq_nonneg x, sq_nonneg y, sq_nonneg w])
    have hw : w < Nat.sqrt n + 1 := hb w (by nlinarith [hsum, sq_nonneg x, sq_nonneg y, sq_nonneg z])
    have := h x hx y hy z hz w hw hsum
    rw [← isSquare_iff_sqrt] at this
    exact this hsq
  · intro h x _ y _ z _ w _ hsum
    rw [← isSquare_iff_sqrt]
    intro hsq
    exact h x y z w hsum hsq

/- ### The "if" direction (`⟸`): the exceptional values are not representable.

The key engine is a `16`-descent: if `16·N` is representable and `N` is even, then `N` is
representable. This rests on the fact that a sum of four squares divisible by `8` must have all
four entries even (four odd squares sum to `4 mod 8`). Two rounds of this descent halve all
variables twice and divide the square value `s²` of the linear form by `4`, returning a genuine
representation of `N`. -/

theorem sq_mod_eight (t : ℕ) :
    (t % 2 = 0 ∧ (t^2 % 8 = 0 ∨ t^2 % 8 = 4)) ∨ (t % 2 = 1 ∧ t^2 % 8 = 1) := by
  rcases Nat.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
  · left
    subst hs; refine ⟨by omega, ?_⟩
    have h1 : (s + s) ^ 2 = 4 * s ^ 2 := by ring
    have hs2 : s ^ 2 % 2 = s % 2 := by
      rw [Nat.pow_mod]; rcases Nat.mod_two_eq_zero_or_one s with h | h <;> rw [h]
    rw [h1]; omega
  · right
    subst hs; refine ⟨by omega, ?_⟩
    have h1 : (2 * s + 1) ^ 2 = 4 * (s ^ 2 + s) + 1 := by ring
    have hp : (s ^ 2 + s) % 2 = 0 := by
      have hs2 : s ^ 2 % 2 = s % 2 := by
        rw [Nat.pow_mod]; rcases Nat.mod_two_eq_zero_or_one s with h | h <;> rw [h]
      omega
    rw [h1]; omega

theorem all_even_of_sq_sum {a b c d : ℕ} (h : (a^2 + b^2 + c^2 + d^2) % 8 = 0) :
    a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0 := by
  have fa := sq_mod_eight a; have fb := sq_mod_eight b
  have fc := sq_mod_eight c; have fd := sq_mod_eight d
  omega

theorem even_of_sq_even {s : ℕ} (h : s * s % 2 = 0) : s % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one s with e | e
  · exact e
  · exfalso; rw [Nat.mul_mod, e] at h; simp at h

set_option maxHeartbeats 1000000 in
theorem descent {N : ℕ} (hN : N % 2 = 0) (h : Repr335624 (16 * N)) : Repr335624 N := by
  obtain ⟨a, b, c, d, hsum, s, hs⟩ := h
  have h8 : (a^2 + b^2 + c^2 + d^2) % 8 = 0 := by rw [hsum]; omega
  obtain ⟨ea, eb, ec, ed⟩ := all_even_of_sq_sum h8
  obtain ⟨a1, rfl⟩ : ∃ a1, a = 2 * a1 := ⟨a / 2, by omega⟩
  obtain ⟨b1, rfl⟩ : ∃ b1, b = 2 * b1 := ⟨b / 2, by omega⟩
  obtain ⟨c1, rfl⟩ : ∃ c1, c = 2 * c1 := ⟨c / 2, by omega⟩
  obtain ⟨d1, rfl⟩ : ∃ d1, d = 2 * d1 := ⟨d / 2, by omega⟩
  have e1 : (2*a1)^2 + (2*b1)^2 + (2*c1)^2 + (2*d1)^2
            = 4 * (a1^2 + b1^2 + c1^2 + d1^2) := by ring
  rw [e1] at hsum
  have hsum1 : a1^2 + b1^2 + c1^2 + d1^2 = 4 * N := by omega
  have hs1 : s * s = 2 * (a1 + 3 * b1 + 4 * c1) := by rw [← hs]; ring
  have es : s % 2 = 0 := even_of_sq_even (by omega)
  obtain ⟨s1, rfl⟩ : ∃ s1, s = 2 * s1 := ⟨s / 2, by omega⟩
  have e2 : (2*s1) * (2*s1) = 4 * (s1 * s1) := by ring
  rw [e2] at hs1
  have hL1 : a1 + 3 * b1 + 4 * c1 = 2 * (s1 * s1) := by omega
  have h8' : (a1^2 + b1^2 + c1^2 + d1^2) % 8 = 0 := by rw [hsum1]; omega
  obtain ⟨ea', eb', ec', ed'⟩ := all_even_of_sq_sum h8'
  obtain ⟨a2, rfl⟩ : ∃ a2, a1 = 2 * a2 := ⟨a1 / 2, by omega⟩
  obtain ⟨b2, rfl⟩ : ∃ b2, b1 = 2 * b2 := ⟨b1 / 2, by omega⟩
  obtain ⟨c2, rfl⟩ : ∃ c2, c1 = 2 * c2 := ⟨c1 / 2, by omega⟩
  obtain ⟨d2, rfl⟩ : ∃ d2, d1 = 2 * d2 := ⟨d1 / 2, by omega⟩
  have e3 : (2*a2)^2 + (2*b2)^2 + (2*c2)^2 + (2*d2)^2
            = 4 * (a2^2 + b2^2 + c2^2 + d2^2) := by ring
  rw [e3] at hsum1
  have hsum2 : a2^2 + b2^2 + c2^2 + d2^2 = N := by omega
  have hL2 : a2 + 3 * b2 + 4 * c2 = s1 * s1 := by omega
  exact ⟨a2, b2, c2, d2, hsum2, s1, hL2⟩

/-- A `Nat.sqrt`-free, kernel-computable test of non-representability over `[0,B)⁴`. -/
def noRepBool (n B : ℕ) : Bool :=
  (List.range B).all fun x => (List.range B).all fun y => (List.range B).all fun z =>
    (List.range B).all fun w =>
      !((x*x+y*y+z*z+w*w == n) &&
        (List.range (x+3*y+4*z+1)).any (fun r => r*r == x+3*y+4*z))

theorem noRep_of_bool {n B : ℕ} (hB : noRepBool n B = true)
    (hbd : ∀ t : ℕ, t * t ≤ n → t < B) : ¬ Repr335624 n := by
  rintro ⟨x, y, z, w, hsum, r, hr⟩
  have hx : x < B := hbd x (by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg w, hsum])
  have hy : y < B := hbd y (by nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg w, hsum])
  have hz : z < B := hbd z (by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg w, hsum])
  have hw : w < B := hbd w (by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, hsum])
  rw [noRepBool, List.all_eq_true] at hB
  have h1 := hB x (List.mem_range.mpr hx); rw [List.all_eq_true] at h1
  have h2 := h1 y (List.mem_range.mpr hy); rw [List.all_eq_true] at h2
  have h3 := h2 z (List.mem_range.mpr hz); rw [List.all_eq_true] at h3
  have h4 := h3 w (List.mem_range.mpr hw)
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at h4
  have hsumb : (x*x + y*y + z*z + w*w == n) = true := by
    have : x*x + y*y + z*z + w*w = n := by nlinarith [hsum]
    simpa using this
  have hanyb : ((List.range (x+3*y+4*z+1)).any (fun r => r*r == x+3*y+4*z)) = true := by
    rw [List.any_eq_true]
    refine ⟨r, List.mem_range.mpr ?_, by simpa using hr.symm⟩
    have : r * r = x + 3*y + 4*z := hr.symm
    nlinarith [this]
  rcases h4 with h4 | h4
  · rw [hsumb] at h4; exact Bool.noConfusion h4
  · rw [hanyb] at h4; exact Bool.noConfusion h4

theorem boundlem (n B : ℕ) (h : n < B * B) : ∀ t : ℕ, t * t ≤ n → t < B := by
  intro t ht; by_contra hc; push_neg at hc; nlinarith [Nat.mul_le_mul hc hc]

theorem base8   : ¬ Repr335624 8   := noRep_of_bool (by decide) (boundlem 8 3 (by norm_num))
theorem base24  : ¬ Repr335624 24  := noRep_of_bool (by decide) (boundlem 24 5 (by norm_num))
theorem base40  : ¬ Repr335624 40  := noRep_of_bool (by decide) (boundlem 40 7 (by norm_num))
set_option maxHeartbeats 4000000 in
theorem base344 : ¬ Repr335624 344 := noRep_of_bool (by decide) (boundlem 344 19 (by norm_num))

/-- The exceptional values `2^(4k+3)·m` (`m ∈ {1,3,5,43}`) admit no representation. -/
theorem easy_dir (k m : ℕ) (hm : m ∈ ({1, 3, 5, 43} : Set ℕ)) :
    ¬ Repr335624 (2 ^ (4 * k + 3) * m) := by
  induction k with
  | zero =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · rw [show (2:ℕ)^(4*0+3)*1 = 8 from by norm_num]; exact base8
    · rw [show (2:ℕ)^(4*0+3)*3 = 24 from by norm_num]; exact base24
    · rw [show (2:ℕ)^(4*0+3)*5 = 40 from by norm_num]; exact base40
    · rw [show (2:ℕ)^(4*0+3)*43 = 344 from by norm_num]; exact base344
  | succ k ih =>
    have key : (2:ℕ)^(4*(k+1)+3)*m = 16 * (2^(4*k+3)*m) := by
      rw [show 4*(k+1)+3 = (4*k+3)+4 by ring, pow_add]; ring
    rw [key]
    intro hr
    have hNeven : (2^(4*k+3)*m) % 2 = 0 := by
      have hd : 2 ∣ 2^(4*k+3)*m := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) m
      omega
    exact ih (descent hNeven hr)

/--
Conjecture: a(n) = 0 if and only if n has the form $2^{4k+3} \cdot m$ (k >= 0 and m = 1, 3, 5, 43).
This is the main part of the OEIS conjecture.
-/
theorem A335624_conjecture_zero_iff (n : ℕ) :
  A335624 n = 0 ↔
    ∃ (k : ℕ) (m : ℕ),
      m ∈ ({1, 3, 5, 43} : Set ℕ) ∧
      n = 2 ^ (4 * k + 3) * m :=
by
  rw [A335624_eq_zero_iff]
  constructor
  · -- (⟹) The hard direction: every non-exceptional `n` is representable.
    -- This is Zhi-Wei Sun's open conjecture A335624; it lies beyond Lagrange's
    -- four-square theorem (the only such result available in Mathlib).
    intro h
    sorry
  · -- (⟸) The exceptional values are not representable (fully proved above).
    rintro ⟨k, m, hm, rfl⟩
    exact easy_dir k m hm
