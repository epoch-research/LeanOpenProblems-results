import Submission.AdjacentShiftMoments

/-! A finite adjacent-position certificate using the same-modulus difference
bound. It proves a length20 bound for five distinct odd prime classes. This is
not an asymptotic result or a comparison with the best known finite bound. -/
namespace Erdos970.AdjacentShift.Example
open Finset

def bit (b : Bool) : ℚ := if b then 1 else 0

def polynomial (x : Fin 5 → Fin 2 → Bool) : ℚ :=
  bit (x 1 1) + bit (x 2 1) + bit (x 3 1) + bit (x 4 1) +
  bit (x 0 1) * (bit (x 1 0) - bit (x 1 1)) +
  bit (x 0 1) * (bit (x 2 0) - bit (x 2 1)) +
  bit (x 0 1) * bit (x 3 0) + bit (x 0 1) * bit (x 4 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pointwise_table :
    ∀ x : Fin 5 → Fin 2 → Bool,
      (x 0 0 = false ∨ x 0 1 = false) →
      (∀ t : Fin 2, ∃ i : Fin 5, x i t = true) → 1 ≤ polynomial x := by
  decide +kernel

noncomputable def pattern (p r : Fin 5 → ℕ) (j : ℕ) : Fin 5 → Fin 2 → Bool :=
  fun i t => decide (j+t.val ≡ r i [MOD p i])

noncomputable def density (p : Fin 5 → ℕ) : ℝ :=
  1/(p 1 : ℝ) + 1/(p 2 : ℝ) + (1+1/(p 0 : ℝ)) * (1/(p 3 : ℝ)+1/(p 4 : ℝ))

def baseline : Fin 5 → ℕ := ![3,5,7,11,13]

lemma density_le (p : Fin 5 → ℕ) (hb : ∀ i, baseline i ≤ p i) :
    density p ≤ (2836/5005 : ℝ) := by
  have hp (i : Fin 5) : (0 : ℝ) < baseline i := by
    fin_cases i <;> norm_num [baseline]
  have hq (i : Fin 5) : 1/(p i : ℝ) ≤ 1/(baseline i : ℝ) :=
    one_div_le_one_div_of_le (hp i) (by exact_mod_cast hb i)
  have h0 := hq 0
  have h1 := hq 1
  have h2 := hq 2
  have h3 := hq 3
  have h4 := hq 4
  change 1/(p 0 : ℝ) ≤ 1/3 at h0
  change 1/(p 1 : ℝ) ≤ 1/5 at h1
  change 1/(p 2 : ℝ) ≤ 1/7 at h2
  change 1/(p 3 : ℝ) ≤ 1/11 at h3
  change 1/(p 4 : ℝ) ≤ 1/13 at h4
  have hs : 1/(p 3 : ℝ)+1/(p 4 : ℝ) ≤ (1/11+1/13 : ℝ) := by linarith
  have hm := mul_le_mul (show 1+1/(p 0 : ℝ) ≤ (1+1/3 : ℝ) by linarith)
    hs (by positivity : (0 : ℝ) ≤ 1/(p 3 : ℝ)+1/(p 4 : ℝ)) (by norm_num)
  unfold density
  linarith

lemma cast_polynomial_pattern (p r : Fin 5 → ℕ) (j : ℕ) :
    (polynomial (pattern p r j) : ℝ) =
      hit (p 1) (r 1) 1 j + hit (p 2) (r 2) 1 j +
      hit (p 3) (r 3) 1 j + hit (p 4) (r 4) 1 j +
      hit (p 0) (r 0) 1 j * (hit (p 1) (r 1) 0 j - hit (p 1) (r 1) 1 j) +
      hit (p 0) (r 0) 1 j * (hit (p 2) (r 2) 0 j - hit (p 2) (r 2) 1 j) +
      hit (p 0) (r 0) 1 j * hit (p 3) (r 3) 0 j +
      hit (p 0) (r 0) 1 j * hit (p 4) (r 4) 0 j := by
  have hb (i : Fin 5) (t : Fin 2) : (bit (pattern p r j i t) : ℝ) =
      hit (p i) (r i) t.val j := by
    simp only [bit, pattern, decide_eq_true_eq, hit,
      apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_one, Rat.cast_zero]
  simp only [polynomial, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, hb]
  rfl

lemma sum_polynomial (p r : Fin 5 → ℕ) (m : ℕ) :
    (∑ j ∈ range m, (polynomial (pattern p r j) : ℝ)) =
      count m (p 1) (r 1) 1 + count m (p 2) (r 2) 1 +
      count m (p 3) (r 3) 1 + count m (p 4) (r 4) 1 +
      (pairCount m (p 0) (p 1) (r 0) (r 1) 1 0 -
        pairCount m (p 0) (p 1) (r 0) (r 1) 1 1) +
      (pairCount m (p 0) (p 2) (r 0) (r 2) 1 0 -
        pairCount m (p 0) (p 2) (r 0) (r 2) 1 1) +
      pairCount m (p 0) (p 3) (r 0) (r 3) 1 0 +
      pairCount m (p 0) (p 4) (r 0) (r 4) 1 0 := by
  simp_rw [cast_polynomial_pattern, mul_sub, sum_add_distrib, sum_sub_distrib]
  rfl

/-- Eight is the full uniform error budget. Treating the ten coefficients
independently would instead give ten. -/
theorem polynomial_interval_upper (p r : Fin 5 → ℕ) (m : ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (∑ j ∈ range m, (polynomial (pattern p r j) : ℝ)) ≤
      (m : ℝ) * density p + 8 := by
  have hn (i : Fin 5) (hi : i ≠ 0) : p 0 ≠ p i := fun h => hi (hinj h).symm
  have h1 := (abs_le.mp (count_error m (p 1) (r 1) 1 (hp 1).pos)).2
  have h2 := (abs_le.mp (count_error m (p 2) (r 2) 1 (hp 2).pos)).2
  have h3 := (abs_le.mp (count_error m (p 3) (r 3) 1 (hp 3).pos)).2
  have h4 := (abs_le.mp (count_error m (p 4) (r 4) 1 (hp 4).pos)).2
  have hd1 := (abs_le.mp (pairCount_difference_error m (p 0) (p 1) (r 0) (r 1)
    1 0 1 1 (hp 0) (hp 1) (hn 1 (by decide)))).2
  have hd2 := (abs_le.mp (pairCount_difference_error m (p 0) (p 2) (r 0) (r 2)
    1 0 1 1 (hp 0) (hp 2) (hn 2 (by decide)))).2
  have hd3 := (abs_le.mp (pairCount_error m (p 0) (p 3) (r 0) (r 3)
    1 0 (hp 0) (hp 3) (hn 3 (by decide)))).2
  have hd4 := (abs_le.mp (pairCount_error m (p 0) (p 4) (r 0) (r 4)
    1 0 (hp 0) (hp 4) (hn 4 (by decide)))).2
  have he : (m : ℝ) * density p + 8 =
      (m : ℝ)/(p 1) + (m : ℝ)/(p 2) + (m : ℝ)/(p 3) + (m : ℝ)/(p 4) +
      (m : ℝ)/((p 0 : ℝ)*p 3) + (m : ℝ)/((p 0 : ℝ)*p 4) + 8 := by
    simp only [density, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [sum_polynomial, he]
  linarith

lemma pattern_exclusive (p r : Fin 5 → ℕ) (hp : (p 0).Prime) (j : ℕ) :
    pattern p r j 0 0 = false ∨ pattern p r j 0 1 = false := by
  classical
  by_contra h
  simp only [pattern, Fin.val_zero, Fin.val_one, add_zero, decide_eq_false_iff_not,
    not_or, not_not] at h
  have hh : j+1 ≡ j [MOD p 0] := h.2.trans h.1.symm
  have h1 : 1 ≡ 0 [MOD p 0] := Nat.ModEq.add_left_cancel' j (by simpa using hh)
  have hp1 : 1 < p 0 := hp.one_lt
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hp1] using h1

/-- For arbitrary distinct prime classes dominating the five smallest odd
primes, twenty consecutive offsets contain a survivor. -/
theorem five_odd_survivor (p r : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hb : ∀ i, baseline i ≤ p i) :
    ∃ j < 20, ∀ i, ¬j ≡ r i [MOD p i] := by
  classical
  by_contra hbad
  push_neg at hbad
  have hpoint (j : ℕ) (hj : j < 19) : (1 : ℝ) ≤ polynomial (pattern p r j) := by
    have hr : (1 : ℚ) ≤ polynomial (pattern p r j) := by
      apply pointwise_table _ (pattern_exclusive p r (hp 0) j)
      intro t
      obtain ⟨i, hi⟩ := hbad (j+t.val) (by have := t.isLt; omega)
      exact ⟨i, by simpa only [pattern, decide_eq_true_eq] using hi⟩
    exact_mod_cast hr
  have hl : (19 : ℝ) ≤ ∑ j ∈ range 19, (polynomial (pattern p r j) : ℝ) := by
    calc
      _ = ∑ j ∈ range 19, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum (fun j hj => hpoint j (mem_range.mp hj))
  have hu := polynomial_interval_upper p r 19 hp hinj
  have hd := density_le p hb
  norm_num only [Nat.cast_ofNat] at hu
  linarith

#print axioms pointwise_table
#print axioms polynomial_interval_upper
#print axioms five_odd_survivor
end Erdos970.AdjacentShift.Example
