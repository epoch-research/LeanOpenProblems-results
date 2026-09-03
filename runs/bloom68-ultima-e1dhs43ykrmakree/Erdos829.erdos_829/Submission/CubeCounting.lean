import FormalConjecturesUtil

/-!
# Elementary counting of sums of two natural cubes

The convolution `AdditiveCombinatorics.sumRep` counts ordered pairs of cube values.
Here it is identified with a finite set of ordered pairs of their natural roots.
For a nonzero target, the sum of the roots is a divisor of the target; together
with the orientation of the pair it determines the pair uniquely. This gives
an elementary bound by twice the number of divisors.

An exact divisor-square criterion is also proved: a positive target `n` has a
root pair with sum `s` if and only if `s` divides `n`, `n ≤ s ^ 3 ≤ 4 * n`, and
`3 * t ^ 2 = 4 * (n / s) - s ^ 2` for some integer `t`.
-/

namespace CubeCounting

/-- The set of natural cubes, including zero. -/
def cubes : Set ℕ := {n : ℕ | ∃ k : ℕ, k ^ 3 = n}

/-- Ordered pairs of natural roots whose cubes sum to `n`.
The range bounds are redundant, as recorded in `mem_rootPairs`. -/
def rootPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => p.1 ^ 3 + p.2 ^ 3 = n)

/-- Each root is at most the target, even when the target is zero. -/
theorem roots_le_target {n a b : ℕ} (h : a ^ 3 + b ^ 3 = n) : a ≤ n ∧ b ≤ n := by
  have ha := Nat.le_self_pow (by decide : 3 ≠ 0) a
  have hb := Nat.le_self_pow (by decide : 3 ≠ 0) b
  omega

@[simp]
theorem mem_rootPairs {n : ℕ} {p : ℕ × ℕ} :
    p ∈ rootPairs n ↔ p.1 ^ 3 + p.2 ^ 3 = n := by
  simp only [rootPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨ha, hb⟩ := roots_le_target h
    exact ⟨⟨by omega, by omega⟩, h⟩

/-- Cubing both coordinates is a bijection between root pairs and the ordered
cube-value pairs counted by the exact convolution definition of `sumRep`. -/
theorem sumRep_eq_card_rootPairs (n : ℕ) :
    AdditiveCombinatorics.sumRep cubes n = (rootPairs n).card := by
  classical
  rw [AdditiveCombinatorics.sumRep_def]
  symm
  apply Finset.card_bij (fun p _ => (p.1 ^ 3, p.2 ^ 3))
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_antidiagonal.mpr (mem_rootPairs.mp hp),
        ⟨⟨p.1, rfl⟩, ⟨p.2, rfl⟩⟩⟩
  · intro p _ q _ h
    exact Prod.ext
      (Nat.pow_left_injective (by decide : 3 ≠ 0) (congrArg Prod.fst h))
      (Nat.pow_left_injective (by decide : 3 ≠ 0) (congrArg Prod.snd h))
  · rintro ⟨x, y⟩ hp
    obtain ⟨hxy, hx, hy⟩ := Finset.mem_filter.mp hp
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨(a, b), mem_rootPairs.mpr (Finset.mem_antidiagonal.mp hxy), rfl⟩

@[simp]
theorem rootPairs_zero : rootPairs 0 = {(0, 0)} := by decide

@[simp]
theorem sumRep_zero : AdditiveCombinatorics.sumRep cubes 0 = 1 := by
  rw [sumRep_eq_card_rootPairs, rootPairs_zero]
  simp

/-- The sum of the roots divides the sum of their cubes. -/
theorem rootSum_dvd {n a b : ℕ} (h : a ^ 3 + b ^ 3 = n) : a + b ∣ n := by
  rw [← h]
  exact Odd.nat_add_dvd_pow_add_pow a b (by decide : Odd 3)

/-- Equal sums and equal sums of cubes give equal products for natural roots. -/
theorem mul_eq_of_sum_eq_of_cube_sum_eq {a b c d : ℕ}
    (hs : a + b = c + d) (hc : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) :
    a * b = c * d := by
  by_cases hz : a + b = 0
  · have hz' : c + d = 0 := hs.symm.trans hz
    obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hz
    obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hz'
    rfl
  have hpos : 0 < 3 * (a + b) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  apply Nat.add_left_cancel (n := c ^ 3 + d ^ 3)
  calc
    c ^ 3 + d ^ 3 + 3 * (a + b) * (a * b) = (a + b) ^ 3 := by rw [← hc]; ring
    _ = (c + d) ^ 3 := congrArg (fun t : ℕ => t ^ 3) hs
    _ = c ^ 3 + d ^ 3 + 3 * (a + b) * (c * d) := by rw [hs]; ring

/-- A fixed sum and cube sum determine a natural pair up to interchange. -/
theorem eq_or_swap_of_sum_eq_of_cube_sum_eq {a b c d : ℕ}
    (hs : a + b = c + d) (hc : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hp := mul_eq_of_sum_eq_of_cube_sum_eq hs hc
  have hsZ : (a : ℤ) + b = c + d := by exact_mod_cast hs
  have hpZ : (a : ℤ) * b = c * d := by exact_mod_cast hp
  have hf : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by
    nlinarith [congrArg (fun t : ℤ => (a : ℤ) * t) hsZ]
  rcases mul_eq_zero.mp hf with h | h
  · have hac : a = c := by exact_mod_cast sub_eq_zero.mp h
    exact Or.inl ⟨hac, by omega⟩
  · have had : a = d := by exact_mod_cast sub_eq_zero.mp h
    exact Or.inr ⟨had, by omega⟩

/-- The sum of the roots and one bit specifying their orientation. -/
def divisorCode (p : ℕ × ℕ) : ℕ × Bool := (p.1 + p.2, decide (p.1 ≤ p.2))

/-- No two root pairs for the same target have the same divisor/orientation code. -/
theorem divisorCode_injOn (n : ℕ) :
    Set.InjOn divisorCode (rootPairs n : Set (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
  have hs : a + b = c + d := congrArg Prod.fst h
  have ho : decide (a ≤ b) = decide (c ≤ d) := congrArg Prod.snd h
  have hc : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 :=
    (mem_rootPairs.mp hp).trans (mem_rootPairs.mp hq).symm
  rcases eq_or_swap_of_sum_eq_of_cube_sum_eq hs hc with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · exact Prod.ext hac hbd
  · have hcd : c = d := by
      by_cases hab : a ≤ b <;> by_cases hcd : c ≤ d <;>
        simp [hab, hcd] at ho <;> omega
    apply Prod.ext <;> omega

/-- The ordered root-pair count is at most twice the divisor count. -/
theorem card_rootPairs_le_two_mul_card_divisors {n : ℕ} (hn : n ≠ 0) :
    (rootPairs n).card ≤ 2 * n.divisors.card := by
  calc
    (rootPairs n).card ≤ (n.divisors.product (Finset.univ : Finset Bool)).card := by
      apply Finset.card_le_card_of_injOn divisorCode
      · intro p hp
        exact Finset.mem_product.mpr
          ⟨Nat.mem_divisors.mpr ⟨rootSum_dvd (mem_rootPairs.mp hp), hn⟩,
            Finset.mem_univ _⟩
      · exact divisorCode_injOn n
    _ = 2 * n.divisors.card := by simp [Nat.mul_comm]

/-- An elementary bound for the exact ordered convolution representation count.
The nonzero hypothesis is necessary since `Nat.divisors 0` is empty. -/
theorem sumRep_le_two_mul_card_divisors {n : ℕ} (hn : n ≠ 0) :
    AdditiveCombinatorics.sumRep cubes n ≤ 2 * n.divisors.card := by
  rw [sumRep_eq_card_rootPairs]
  exact card_rootPairs_le_two_mul_card_divisors hn

/- The divisor-square criterion. -/

/-- The sum of two nonnegative roots lies in a short cubed interval. -/
theorem rootSum_interval {n a b : ℕ} (h : a ^ 3 + b ^ 3 = n) :
    n ≤ (a + b) ^ 3 ∧ (a + b) ^ 3 ≤ 4 * n := by
  rw [← h]
  constructor
  · calc
      a ^ 3 + b ^ 3 ≤ a ^ 3 + b ^ 3 + 3 * (a + b) * (a * b) := Nat.le_add_right _ _
      _ = (a + b) ^ 3 := by ring
  · have hnonneg : (0 : ℤ) ≤ ((a : ℤ) + b) * ((a : ℤ) - b) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    have hi : ((a : ℤ) + b) ^ 3 ≤ 4 * ((a : ℤ) ^ 3 + (b : ℤ) ^ 3) := by
      nlinarith [hnonneg]
    exact_mod_cast hi

/-- The quotient by the root sum is the quadratic factor of a sum of cubes.
Integer subtraction is used here, not truncated natural subtraction. -/
theorem quotient_eq_quadratic {n a b : ℕ} (hn : n ≠ 0) (h : a ^ 3 + b ^ 3 = n) :
    ((n / (a + b) : ℕ) : ℤ) = (a : ℤ) ^ 2 - (a : ℤ) * b + (b : ℤ) ^ 2 := by
  have hs : a + b ≠ 0 :=
    (Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨rootSum_dvd h, hn⟩)).ne'
  apply mul_right_cancel₀ (show ((a + b : ℕ) : ℤ) ≠ 0 by exact_mod_cast hs)
  calc
    ((n / (a + b) : ℕ) : ℤ) * (a + b : ℕ) = (n : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel (rootSum_dvd h)
    _ = ((a : ℤ) ^ 2 - (a : ℤ) * b + (b : ℤ) ^ 2) * (a + b : ℕ) := by
      rw [← h]
      push_cast
      ring

/-- The square discriminant identity, with the signed root difference as witness. -/
theorem rootSum_square_identity {n a b : ℕ} (hn : n ≠ 0) (h : a ^ 3 + b ^ 3 = n) :
    3 * ((a : ℤ) - b) ^ 2 = 4 * ((n / (a + b) : ℕ) : ℤ) - ((a + b : ℕ) : ℤ) ^ 2 := by
  rw [quotient_eq_quadratic hn h]
  push_cast
  ring

/-- An exact criterion for `s` to be the sum of roots of a representation of `n`.
The quotient `n / s` is natural division; all subtraction in the square equation
is in the integers. No extra parity condition is needed. -/
def divisorSquareCriterion (n s : ℕ) : Prop :=
  s ∈ n.divisors ∧ n ≤ s ^ 3 ∧ s ^ 3 ≤ 4 * n ∧
    ∃ t : ℤ, 3 * t ^ 2 = 4 * ((n / s : ℕ) : ℤ) - (s : ℤ) ^ 2

/-- The square equation already forces the parity needed to halve `s + t`. -/
theorem even_add_of_square_identity {s q t : ℤ}
    (h : 3 * t ^ 2 = 4 * q - s ^ 2) : Even (s + t) := by
  have he : Even (s ^ 2 + t ^ 2) := ⟨2 * q - t ^ 2, by nlinarith [h]⟩
  simpa [Int.even_add, Int.even_pow] using he

/-- The divisor, interval and integer-square conditions are both necessary and
sufficient. In the reverse direction the natural roots are `(s + t) / 2` and
`(s - t) / 2`; integrality and nonnegativity are proved, not assumed. -/
theorem exists_roots_iff_divisorSquareCriterion {n s : ℕ} (hn : n ≠ 0) :
    (∃ a b : ℕ, a + b = s ∧ a ^ 3 + b ^ 3 = n) ↔ divisorSquareCriterion n s := by
  constructor
  · rintro ⟨a, b, rfl, h⟩
    obtain ⟨hlo, hhi⟩ := rootSum_interval h
    exact ⟨Nat.mem_divisors.mpr ⟨rootSum_dvd h, hn⟩, hlo, hhi,
      ⟨(a : ℤ) - b, rootSum_square_identity hn h⟩⟩
  · rintro ⟨hs, hlo, _, t, ht⟩
    have hspos : 0 < (s : ℤ) := by exact_mod_cast Nat.pos_of_mem_divisors hs
    have hmul : ((n / s : ℕ) : ℤ) * s = n := by
      exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hs)
    have hq : ((n / s : ℕ) : ℤ) ≤ (s : ℤ) ^ 2 := by
      apply (mul_le_mul_iff_of_pos_right hspos).mp
      calc
        ((n / s : ℕ) : ℤ) * s = n := hmul
        _ ≤ (s : ℤ) ^ 3 := by exact_mod_cast hlo
        _ = (s : ℤ) ^ 2 * s := by ring
    have ht2 : t ^ 2 ≤ (s : ℤ) ^ 2 := by nlinarith [ht]
    have hbound : -(s : ℤ) ≤ t ∧ t ≤ s := abs_le_of_sq_le_sq' ht2 hspos.le
    obtain ⟨u, hu⟩ := even_add_of_square_identity ht
    have hu0 : 0 ≤ u := by omega
    let v : ℤ := (s : ℤ) - u
    have hv0 : 0 ≤ v := by dsimp [v]; omega
    have hsum : u + v = (s : ℤ) := by dsimp [v]; ring
    have hdiff : u - v = t := by dsimp [v]; omega
    have hcube : u ^ 3 + v ^ 3 = (n : ℤ) := by
      have hi : 4 * (u ^ 3 + v ^ 3) = (u + v) * ((u + v) ^ 2 + 3 * (u - v) ^ 2) := by
        ring
      rw [hsum, hdiff, ht] at hi
      nlinarith [hmul]
    refine ⟨u.toNat, v.toNat, ?_, ?_⟩
    · apply Int.natCast_inj.mp
      push_cast
      rw [Int.toNat_of_nonneg hu0, Int.toNat_of_nonneg hv0]
      exact hsum
    · apply Int.natCast_inj.mp
      push_cast
      rw [Int.toNat_of_nonneg hu0, Int.toNat_of_nonneg hv0]
      exact hcube

/-- Representability by two natural cubes is exactly existence of a divisor
satisfying the interval and integer-square criterion. -/
theorem sumRep_pos_iff_exists_divisorSquareCriterion {n : ℕ} (hn : n ≠ 0) :
    0 < AdditiveCombinatorics.sumRep cubes n ↔ ∃ s : ℕ, divisorSquareCriterion n s := by
  rw [sumRep_eq_card_rootPairs, Finset.card_pos]
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩
    exact ⟨a + b, (exists_roots_iff_divisorSquareCriterion hn).mp
      ⟨a, b, rfl, mem_rootPairs.mp hab⟩⟩
  · rintro ⟨s, hs⟩
    obtain ⟨a, b, _, h⟩ := (exists_roots_iff_divisorSquareCriterion hn).mpr hs
    exact ⟨(a, b), mem_rootPairs.mpr h⟩

/-- The distinct sums of roots of representations of `n`. -/
def rootSums (n : ℕ) : Finset ℕ :=
  (rootPairs n).image (fun p => p.1 + p.2)

@[simp]
theorem mem_rootSums {n s : ℕ} :
    s ∈ rootSums n ↔ ∃ a b : ℕ, a + b = s ∧ a ^ 3 + b ^ 3 = n := by
  simp only [rootSums, Finset.mem_image, mem_rootPairs, Prod.exists]
  constructor
  · rintro ⟨a, b, hab, hs⟩
    exact ⟨a, b, hs, hab⟩
  · rintro ⟨a, b, hs, hab⟩
    exact ⟨a, b, hab, hs⟩

/-- Square-admissible divisors, without using the root-pair definition. -/
noncomputable def squareDivisors (n : ℕ) : Finset ℕ := by
  classical
  exact n.divisors.filter (divisorSquareCriterion n)

/-- For positive targets the two finite sets coincide exactly. -/
theorem rootSums_eq_squareDivisors {n : ℕ} (hn : n ≠ 0) :
    rootSums n = squareDivisors n := by
  classical
  ext s
  simp only [mem_rootSums, squareDivisors, Finset.mem_filter,
    exists_roots_iff_divisorSquareCriterion hn]
  exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩

/-- Forgetting the orientation loses at most a factor of two. -/
theorem rootSums_card_bounds (n : ℕ) :
    (rootSums n).card ≤ AdditiveCombinatorics.sumRep cubes n ∧
      AdditiveCombinatorics.sumRep cubes n ≤ 2 * (rootSums n).card := by
  rw [sumRep_eq_card_rootPairs]
  constructor
  · exact Finset.card_image_le
  · calc
      (rootPairs n).card ≤ ((rootSums n).product (Finset.univ : Finset Bool)).card := by
        apply Finset.card_le_card_of_injOn divisorCode
        · intro p hp
          exact Finset.mem_product.mpr
            ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_univ _⟩
        · exact divisorCode_injOn n
      _ = 2 * (rootSums n).card := by simp [Nat.mul_comm]

open Asymptotics Filter in
/-- An asymptotic bound on root sums is equivalent to the same bound on the
ordered representation count. This holds for any real comparison function. -/
theorem sumRep_isBigO_iff_rootSums (g : ℕ → ℝ) :
    (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) =O[atTop] g ↔
      (fun n : ℕ => ((rootSums n).card : ℝ)) =O[atTop] g := by
  have h₁ : (fun n : ℕ => ((rootSums n).card : ℝ)) =O[atTop]
      (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) := by
    apply Asymptotics.IsBigO.of_norm_le
    intro n
    rw [Real.norm_natCast]
    exact_mod_cast (rootSums_card_bounds n).1
  have h₂ : (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => ((rootSums n).card : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 2
    apply Filter.Eventually.of_forall
    intro n
    simp only [Real.norm_natCast]
    exact_mod_cast (rootSums_card_bounds n).2
  exact ⟨fun h => h₁.trans h, fun h => h₂.trans h⟩

open Asymptotics Filter in
/-- The original polylogarithmic conjecture is exactly the corresponding
polylogarithmic bound for the square-admissible divisors. This equivalence
proves neither side of the conjecture. -/
theorem polylog_sumRep_iff_squareDivisors :
    (∃ C : ℕ, (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => (Real.log n) ^ C)) ↔
    (∃ C : ℕ, (fun n : ℕ => ((squareDivisors n).card : ℝ)) =O[atTop]
      (fun n : ℕ => (Real.log n) ^ C)) := by
  have heq : (fun n : ℕ => ((rootSums n).card : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => ((squareDivisors n).card : ℝ)) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨1, fun n hn => ?_⟩
    change ((rootSums n).card : ℝ) = ((squareDivisors n).card : ℝ)
    rw [rootSums_eq_squareDivisors (by omega : n ≠ 0)]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, ((sumRep_isBigO_iff_rootSums _).mp hC).congr' heq Filter.EventuallyEq.rfl⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (sumRep_isBigO_iff_rootSums _).mpr
      (hC.congr' heq.symm Filter.EventuallyEq.rfl)⟩

end CubeCounting
