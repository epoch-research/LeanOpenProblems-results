import Mathlib

/-!
# Erdős–Straus: elementary residue classes and prime reduction

This file proves partial results for the ordered, *distinct* denominator version of
`Submission/Spec.lean`. It does not prove the Erdős–Straus conjecture.
-/

namespace Erdos242

/-- The statement of the Erdős–Straus conjecture at an individual natural number,
with strictly increasing natural denominators, as in `Submission/Spec.lean`. -/
def Good (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

private theorem good_8k5 (k : ℕ) : Good (8 * k + 5) := by
  let a := k + 1
  let n := 8 * k + 5
  refine ⟨2 * a, a * n, 2 * a * n, ?_, ?_, ?_, ?_⟩
  · dsimp [a]; omega
  · dsimp [a, n]; nlinarith
  · dsimp [a, n]; nlinarith
  · dsimp [a, n]
    push_cast
    have ha : (k : ℚ) + 1 ≠ 0 := by positivity
    have hn : 8 * (k : ℚ) + 5 ≠ 0 := by positivity
    field_simp
    ring

private theorem good_3k5 (k : ℕ) : Good (3 * k + 5) := by
  let a := k + 2
  let n := 3 * k + 5
  refine ⟨a, n, a * n, ?_, ?_, ?_, ?_⟩
  · dsimp [a]; omega
  · dsimp [a, n]; omega
  · dsimp [a, n]; nlinarith
  · dsimp [a, n]
    push_cast
    field_simp
    ring

private theorem good_4k3 (k : ℕ) : Good (4 * k + 3) := by
  let a := k + 1
  let n := 4 * k + 3
  let q := a * n
  refine ⟨a, q + 1, q * (q + 1), ?_, ?_, ?_, ?_⟩
  · dsimp [a]; omega
  · dsimp [a, n, q]; nlinarith
  · have hq : 2 ≤ q := by dsimp [q, a, n]; nlinarith
    calc
      q + 1 < 2 * (q + 1) := by omega
      _ ≤ q * (q + 1) := Nat.mul_le_mul_right _ hq
  · dsimp [a, n, q]
    push_cast
    field_simp
    ring

private theorem good_3k3 (k : ℕ) : Good (3 * k + 3) := by
  let a := k + 1
  let n := 3 * k + 3
  refine ⟨a, n + 1, n * (n + 1), ?_, ?_, ?_, ?_⟩
  · dsimp [a]; omega
  · dsimp [a, n]; omega
  · dsimp [a, n]; nlinarith
  · dsimp [a, n]
    push_cast
    field_simp
    ring

private theorem good_4k4 (k : ℕ) : Good (4 * k + 4) := by
  let a := k + 1
  let q := a * (a + 1)
  refine ⟨a + 1, q + 1, q * (q + 1), ?_, ?_, ?_, ?_⟩
  · dsimp [a]; omega
  · dsimp [a, q]; nlinarith
  · have hq : 2 ≤ q := by dsimp [q, a]; nlinarith
    calc
      q + 1 < 2 * (q + 1) := by omega
      _ ≤ q * (q + 1) := Nat.mul_le_mul_right _ hq
  · dsimp [a, q]
    push_cast
    field_simp
    ring

private theorem good_4k6 (k : ℕ) : Good (4 * k + 6) := by
  let a := k + 2
  let q := (2 * k + 3) * a
  refine ⟨a, q + 1, q * (q + 1), ?_, ?_, ?_, ?_⟩
  · dsimp [a]; omega
  · dsimp [a, q]; nlinarith
  · have hq : 2 ≤ q := by dsimp [q, a]; nlinarith
    calc
      q + 1 < 2 * (q + 1) := by omega
      _ ≤ q * (q + 1) := Nat.mul_le_mul_right _ hq
  · dsimp [a, q]
    push_cast
    field_simp
    ring

/-- Every `n > 2` outside the residue class `1 (mod 24)` has three strictly
increasing denominators. -/
theorem good_outside_24 (n : ℕ) (hn : 2 < n) (hr : n % 24 ≠ 1) : Good n := by
  have hcases : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3 ∨
      n % 3 = 0 ∨ n % 3 = 2 ∨ n % 8 = 5 := by omega
  rcases hcases with h | h | h | h | h | h
  · have heq : n = 4 * (n / 4 - 1) + 4 := by omega
    rw [heq]
    exact good_4k4 _
  · have heq : n = 4 * (n / 4 - 1) + 6 := by omega
    rw [heq]
    exact good_4k6 _
  · have heq : n = 4 * (n / 4) + 3 := by omega
    rw [heq]
    exact good_4k3 _
  · have heq : n = 3 * (n / 3 - 1) + 3 := by omega
    rw [heq]
    exact good_3k3 _
  · have heq : n = 3 * (n / 3 - 1) + 5 := by omega
    rw [heq]
    exact good_3k5 _
  · have heq : n = 8 * (n / 8) + 5 := by omega
    rw [heq]
    exact good_8k5 _

/-- Scaling all three denominators preserves their order and the identity. -/
theorem good_mul {n k : ℕ} (h : Good n) (hk : 0 < k) : Good (n * k) := by
  rcases h with ⟨x, y, z, hx, hxy, hyz, heq⟩
  refine ⟨x * k, y * k, z * k, ?_, ?_, ?_, ?_⟩
  · have : 0 < x * k := Nat.mul_pos (by omega) hk
    omega
  · exact Nat.mul_lt_mul_of_pos_right hxy hk
  · exact Nat.mul_lt_mul_of_pos_right hyz hk
  · simp only [Nat.cast_mul]
    calc
      (4 / (↑n * ↑k) : ℚ) = (4 / ↑n : ℚ) / ↑k := by rw [div_mul_eq_div_div]
      _ = (1 / ↑x + 1 / ↑y + 1 / ↑z) / ↑k := by rw [heq]
      _ = (1 / (↑x * ↑k) + 1 / (↑y * ↑k) + 1 / (↑z * ↑k) : ℚ) := by
        simp only [add_div, div_mul_eq_div_div]

/-- To prove the original conjecture it suffices to handle primes congruent
 to `1 (mod 24)`. This theorem does *not* supply those missing cases. -/
theorem good_of_hard_primes
    (hard : ∀ p : ℕ, p.Prime → p % 24 = 1 → Good p) :
    ∀ n : ℕ, 2 < n → Good n := by
  intro n hn
  by_cases hrem : n % 24 = 1
  · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hpgt : 2 < p := by
      have hp2 : 2 ≤ p := hp.two_le
      by_contra ht
      have peq : p = 2 := by omega
      subst p
      have heven : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hpn
      omega
    have hgood : Good p := by
      by_cases hprem : p % 24 = 1
      · exact hard p hp hprem
      · exact good_outside_24 p hpgt hprem
    rcases hpn with ⟨k, rfl⟩
    have hk : 0 < k := by
      by_contra ht
      have : k = 0 := by omega
      simp [this] at hn
    exact good_mul hgood hk
  · exact good_outside_24 n hn hrem

/-- A conditional modular (type-II) witness construction, requiring no primality
assumption on `p`. The denominators are explicitly
`x = (p*m+d)/(4*m-1)`, `y = p*m` and `z = p*(m*x/d)`.
The divisibility assumptions ensure both natural-number quotients are exact;
`d < x` ensures that the three denominators are strictly increasing. -/
theorem good_of_modular_witness (p m d : ℕ)
    (hp : 0 < p) (hm : 0 < m) (hd : 0 < d)
    (hdsq : d ∣ m ^ 2)
    (hpos : 0 < 4 * m - 1)
    (hdiv : 4 * m - 1 ∣ p + 4 * d)
    (hxd : d < (p * m + d) / (4 * m - 1)) : Good p := by
  let h := 4 * m - 1
  let x := (p * m + d) / h
  let t := (p + 4 * d) / h
  have hh : 0 < h := hpos
  have hfour : h + 1 = 4 * m := by dsimp [h]; omega
  have ht : h * t = p + 4 * d := Nat.mul_div_cancel' hdiv
  have hsum : p * m + d + h * d = h * (m * t) := by
    calc
      p * m + d + h * d = p * m + (h + 1) * d := by ring
      _ = (p + 4 * d) * m := by rw [hfour]; ring
      _ = h * (m * t) := by rw [← ht]; ring
  have hnum : h ∣ p * m + d := by
    have hnumadd : h ∣ p * m + d + h * d := by
      rw [hsum]
      exact dvd_mul_right h (m * t)
    exact (Nat.dvd_add_iff_left (dvd_mul_right h d)).mpr hnumadd
  have hx : h * x = p * m + d := Nat.mul_div_cancel' hnum
  have hxt : x + d = m * t := by
    apply Nat.eq_of_mul_eq_mul_left hh
    calc
      h * (x + d) = p * m + d + h * d := by rw [mul_add, hx]
      _ = h * (m * t) := hsum
  have hdmx : d ∣ m * x := by
    have hdmm : d ∣ m * m := by simpa only [pow_two] using hdsq
    have hmult : m * x + m * d = (m * m) * t := by
      calc
        m * x + m * d = m * (x + d) := by ring
        _ = m * (m * t) := by rw [hxt]
        _ = (m * m) * t := by ring
    have hdall : d ∣ m * x + m * d := by
      rw [hmult]
      exact dvd_mul_of_dvd_left hdmm t
    exact (Nat.dvd_add_iff_left (Nat.dvd_mul_left d m)).mpr hdall
  let u := m * x / d
  have hu : d * u = m * x := Nat.mul_div_cancel' hdmx
  have hdx : d < x := hxd
  have hxpos : 0 < x := lt_trans hd hdx
  have hh3 : 3 ≤ h := by dsimp [h]; omega
  have hxy : x < p * m := by
    have hbound : 3 * x ≤ h * x := Nat.mul_le_mul_right x hh3
    omega
  have hmu : m < u := Nat.lt_of_mul_lt_mul_left (by
    calc
      d * m = m * d := by ring
      _ < m * x := Nat.mul_lt_mul_of_pos_left hdx hm
      _ = d * u := hu.symm)
  refine ⟨x, p * m, p * u, Nat.succ_le_iff.mpr hxpos, hxy,
    Nat.mul_lt_mul_of_pos_left hmu hp, ?_⟩
  have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
  have hfourq : (h : ℚ) + 1 = 4 * m := by exact_mod_cast hfour
  have hxqeq : (h : ℚ) * x = (p : ℚ) * m + d := by exact_mod_cast hx
  have huqeq : (d : ℚ) * u = (m : ℚ) * x := by exact_mod_cast hu
  have hstep : 4 * (m : ℚ) * x = (p : ℚ) * m + x + d := by
    calc
      4 * (m : ℚ) * x = ((h : ℚ) + 1) * x := by rw [hfourq]
      _ = (h : ℚ) * x + x := by ring
      _ = ((p : ℚ) * m + d) + x := by rw [hxqeq]
      _ = (p : ℚ) * m + x + d := by ring
  push_cast
  field_simp
  calc
    4 * (x : ℚ) * m * u = (4 * (m : ℚ) * x) * u := by ring
    _ = ((p : ℚ) * m + x + d) * u := by rw [hstep]
    _ = ((p : ℚ) * m + x) * u + x * m := by
      calc
        ((p : ℚ) * m + x + d) * u = ((p : ℚ) * m + x) * u + d * u := by ring
        _ = ((p : ℚ) * m + x) * u + x * m := by rw [huqeq]; ring

end Erdos242
