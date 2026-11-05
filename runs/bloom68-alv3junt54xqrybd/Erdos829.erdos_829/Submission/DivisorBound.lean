import Submission.Representation

/-!
# A divisor bound for ordered sums of two cubes

The cube-root parametrization preserves the number of representations. A root
pair is determined by its sum and its orientation, and its sum divides the
represented number. These are counting lemmas, not an assertion of the conjecture.
-/

namespace Erdos829Aux

/-- The range restrictions in `rootPairs` do not exclude any natural cube roots. -/
@[simp] theorem mem_rootPairs {n : ℕ} {p : ℕ × ℕ} :
    p ∈ rootPairs n ↔ p.1 ^ 3 + p.2 ^ 3 = n := by
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hp⟩
    · apply Finset.mem_range.mpr
      have hroot := Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) p.1
      omega
    · apply Finset.mem_range.mpr
      have hroot := Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) p.2
      omega

/-- Cubing each coordinate bijects root pairs with the filtered antidiagonal
that counts ordered representations by two cubes. -/
theorem sumRep_cubes_eq_card_rootPairs (n : ℕ) :
    AdditiveCombinatorics.sumRep cubes n = (rootPairs n).card := by
  classical
  rw [AdditiveCombinatorics.sumRep_def]
  symm
  refine Finset.card_bij (fun p _ => (p.1 ^ 3, p.2 ^ 3)) ?_ ?_ ?_
  · intro p hp
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_antidiagonal.mpr (mem_rootPairs.mp hp)
    · exact ⟨⟨p.1, rfl⟩, ⟨p.2, rfl⟩⟩
  · intro p hp q hq hpq
    apply Prod.ext
    · exact Nat.pow_left_injective (by decide : (3 : ℕ) ≠ 0)
        (congrArg Prod.fst hpq)
    · exact Nat.pow_left_injective (by decide : (3 : ℕ) ≠ 0)
        (congrArg Prod.snd hpq)
  · rintro ⟨a, b⟩ hab
    rcases Finset.mem_filter.mp hab with ⟨hab_sum, ha, hb⟩
    rcases ha with ⟨x, hx⟩
    rcases hb with ⟨y, hy⟩
    refine ⟨(x, y), mem_rootPairs.mpr ?_, Prod.ext hx hy⟩
    simpa only [hx, hy] using (Finset.mem_antidiagonal.mp hab_sum)

/-- Equal root sums and equal cube sums determine the two roots up to swapping.
The cubic identity first determines their product, and then they are the roots
of the same quadratic. -/
theorem roots_eq_or_swap_of_sum_cube_eq {x y u v : ℕ}
    (hs : x + y = u + v) (hc : x ^ 3 + y ^ 3 = u ^ 3 + v ^ 3) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  by_cases hz : x + y = 0
  · left
    omega
  · have hmul : (3 * (x + y)) * (x * y) = (3 * (x + y)) * (u * v) := by
      apply Nat.add_left_cancel (n := x ^ 3 + y ^ 3)
      calc
        x ^ 3 + y ^ 3 + (3 * (x + y)) * (x * y) = (x + y) ^ 3 := by ring
        _ = (u + v) ^ 3 := by rw [hs]
        _ = u ^ 3 + v ^ 3 + (3 * (u + v)) * (u * v) := by ring
        _ = x ^ 3 + y ^ 3 + (3 * (x + y)) * (u * v) := by rw [← hc, ← hs]
    have hp : x * y = u * v :=
      mul_left_cancel₀ (mul_ne_zero (by decide : (3 : ℕ) ≠ 0) hz) hmul
    have hsZ : (x : ℤ) + y = (u : ℤ) + v := by exact_mod_cast hs
    have hpZ : (x : ℤ) * y = (u : ℤ) * v := by exact_mod_cast hp
    have hfactor : ((x : ℤ) - u) * ((x : ℤ) - v) = 0 := by
      calc
        ((x : ℤ) - u) * ((x : ℤ) - v) =
            (x : ℤ) * ((x : ℤ) + y - ((u : ℤ) + v)) +
              ((u : ℤ) * v - (x : ℤ) * y) := by ring
        _ = 0 := by rw [hsZ, hpZ]; simp
    rcases mul_eq_zero.mp hfactor with hx | hx
    · have hxu : x = u := by exact_mod_cast (sub_eq_zero.mp hx)
      left
      exact ⟨hxu, by omega⟩
    · have hxv : x = v := by exact_mod_cast (sub_eq_zero.mp hx)
      right
      exact ⟨hxv, by omega⟩

/-- The orientation resolves the swapping ambiguity, including the diagonal case. -/
theorem roots_eq_of_sum_cube_eq_orientation_eq {p q : ℕ × ℕ}
    (hs : p.1 + p.2 = q.1 + q.2)
    (hc : p.1 ^ 3 + p.2 ^ 3 = q.1 ^ 3 + q.2 ^ 3)
    (ho : decide (p.1 ≤ p.2) = decide (q.1 ≤ q.2)) : p = q := by
  have hord : p.1 ≤ p.2 ↔ q.1 ≤ q.2 := decide_eq_decide.mp ho
  rcases roots_eq_or_swap_of_sum_cube_eq hs hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · apply Prod.ext <;> omega

/-- A cube-root sum is a divisor of the represented nonzero number. -/
theorem sum_mem_divisors_of_mem_rootPairs {n : ℕ} (hn : n ≠ 0)
    {p : ℕ × ℕ} (hp : p ∈ rootPairs n) : p.1 + p.2 ∈ n.divisors := by
  apply Nat.mem_divisors.mpr
  refine ⟨?_, hn⟩
  rw [← mem_rootPairs.mp hp]
  exact Odd.nat_add_dvd_pow_add_pow p.1 p.2 (by decide : Odd 3)

/-- Encoding a root pair by its sum and its Boolean orientation is injective. -/
theorem sum_orientation_injOn_rootPairs (n : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => (p.1 + p.2, decide (p.1 ≤ p.2)))
      (↑(rootPairs n) : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  apply roots_eq_of_sum_cube_eq_orientation_eq
  · exact congrArg Prod.fst heq
  · exact (mem_rootPairs.mp hp).trans (mem_rootPairs.mp hq).symm
  · exact congrArg Prod.snd heq

/-- There are at most two ordered root pairs for each divisor of a nonzero `n`. -/
theorem card_rootPairs_le_two_mul_card_divisors {n : ℕ} (hn : n ≠ 0) :
    (rootPairs n).card ≤ 2 * n.divisors.card := by
  have hcard : (rootPairs n).card ≤
      (n.divisors.product (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn
      (fun p : ℕ × ℕ => (p.1 + p.2, decide (p.1 ≤ p.2)))
    · intro p hp
      exact Finset.mem_product.mpr
        ⟨sum_mem_divisors_of_mem_rootPairs hn hp, Finset.mem_univ _⟩
    · exact sum_orientation_injOn_rootPairs n
  simpa [Finset.card_product, Nat.mul_comm] using hcard

end Erdos829Aux
