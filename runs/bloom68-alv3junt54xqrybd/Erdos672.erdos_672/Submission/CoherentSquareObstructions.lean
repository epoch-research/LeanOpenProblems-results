import Submission.FourTerms

/-!
# Coherent endpoint squareclass obstructions

For a positive progression, the endpoint coefficient pattern prescribes
squareclasses `3, 1, 6, 3` at distances `3, 4, 6, 12` from that endpoint.
Four suitably scaled terms then form a positive AP with square product, which
Euler's four-term theorem excludes. This proves impossibility of these actual
squareclass equations; it does not assume or prove a uniform classification
of all progression coefficient profiles.
-/

namespace Erdos672.Progression

/-- The left-endpoint squareclass equations at offsets `3, 4, 6, 12`
cannot simultaneously hold in a positive progression. -/
theorem coherent_left_squareclass_obstruction (n d a b c e : ℕ)
    (hn : 0 < n)
    (h3 : n + 3 * d = 3 * a ^ 2)
    (h4 : n + 4 * d = b ^ 2)
    (h6 : n + 6 * d = 6 * c ^ 2)
    (h12 : n + 12 * d = 3 * e ^ 2) : False := by
  have hA : 0 < n + 12 * d := by positivity
  apply four_term_product_ne_square (n + 12 * d) n (36 * a * b * c * e) hA hn
  calc
    (n + 12 * d) * ((n + 12 * d) + n) *
        ((n + 12 * d) + 2 * n) * ((n + 12 * d) + 3 * n) =
        (n + 12 * d) * (2 * (n + 6 * d)) *
          (3 * (n + 4 * d)) * (4 * (n + 3 * d)) := by ring
    _ = (3 * e ^ 2) * (2 * (6 * c ^ 2)) *
          (3 * b ^ 2) * (4 * (3 * a ^ 2)) := by rw [h12, h6, h4, h3]
    _ = (36 * a * b * c * e) ^ 2 := by ring

/-- The corresponding equations measured backwards from the right endpoint
of a twelve-step positive block are also impossible. -/
theorem coherent_right_squareclass_obstruction (n d a b c e : ℕ)
    (hn : 0 < n)
    (h9 : n + 9 * d = 3 * a ^ 2)
    (h8 : n + 8 * d = b ^ 2)
    (h6 : n + 6 * d = 6 * c ^ 2)
    (h0 : n = 3 * e ^ 2) : False := by
  have hS : 0 < n + 12 * d := by positivity
  apply four_term_product_ne_square n (n + 12 * d) (36 * a * b * c * e) hn hS
  calc
    n * (n + (n + 12 * d)) *
        (n + 2 * (n + 12 * d)) * (n + 3 * (n + 12 * d)) =
        n * (2 * (n + 6 * d)) * (3 * (n + 8 * d)) * (4 * (n + 9 * d)) := by ring
    _ = (3 * e ^ 2) * (2 * (6 * c ^ 2)) *
          (3 * b ^ 2) * (4 * (3 * a ^ 2)) := by rw [h6, h8, h9, h0]
    _ = (36 * a * b * c * e) ^ 2 := by ring

/-- Even-power versions reduce to the same four squareclass equations. -/
theorem coherent_left_even_power_obstruction (n d a b c e l : ℕ)
    (hn : 0 < n) (hl : 2 ∣ l)
    (h3 : n + 3 * d = 3 * a ^ l)
    (h4 : n + 4 * d = b ^ l)
    (h6 : n + 6 * d = 6 * c ^ l)
    (h12 : n + 12 * d = 3 * e ^ l) : False := by
  have hp : ∀ x : ℕ, x ^ l = (x ^ (l / 2)) ^ 2 := by
    intro x
    rw [← pow_mul, Nat.div_mul_cancel hl]
  apply coherent_left_squareclass_obstruction n d
    (a ^ (l / 2)) (b ^ (l / 2)) (c ^ (l / 2)) (e ^ (l / 2)) hn
  · simpa only [hp a] using h3
  · simpa only [hp b] using h4
  · simpa only [hp c] using h6
  · simpa only [hp e] using h12

end Erdos672.Progression
