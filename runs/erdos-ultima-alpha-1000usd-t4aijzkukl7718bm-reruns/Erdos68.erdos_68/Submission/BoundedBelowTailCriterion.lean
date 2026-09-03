import Submission.SubquadraticTailCriterion

/-!
# Prime-unit tail criteria with a fixed negative lower bound

The nonnegative-tail hypothesis can be weakened to a constant lower bound.
This is an auxiliary criterion: no representation satisfying its hypotheses
has been established for the series in `Spec.lean`.
-/

namespace BoundedBelowTailCriterion

open CongruentTailSeparation Filter

lemma unit_predecessor_nonneg (t : ℕ → ℤ) (B n : ℕ) (hn : B < n)
    (hu : t (n + 1) = (n + 1 : ℤ) * t n - 1)
    (hlo : -(B : ℤ) ≤ t (n + 1)) : 0 ≤ t n := by
  have hn' : (B : ℤ) < n := by exact_mod_cast hn
  by_contra h
  have ht : t n ≤ -1 := by omega
  have hm := mul_le_mul_of_nonneg_left ht (show (0 : ℤ) ≤ n + 1 by omega)
  rw [hu] at hlo
  nlinarith

lemma increment_nonneg (t : ℕ → ℤ) (B n : ℕ) (hn : B < n)
    (hlo : -(B : ℤ) ≤ t (n + 1)) : 0 ≤ increment t n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnB : (B : ℝ) < n := by exact_mod_cast hn
  have ht : -(B : ℝ) ≤ (t (n + 1) : ℝ) := by exact_mod_cast hlo
  have he : increment t n = ((n : ℝ) + 1 + t (n + 1)) / (n * (n + 1) : ℝ) := by
    unfold increment
    field_simp
  rw [he]
  exact div_nonneg (by linarith) (by positivity)

lemma no_small_increment_return (t : ℕ → ℤ) (a L : ℕ)
    (ha : 0 < a) (hL : 0 < L)
    (hstartInt : 0 ≤ t a) (hendInt : 0 ≤ t (a + L))
    (hinc : ∀ i < L, 0 ≤ increment t (a + i))
    (hunit : t (a + 1) = (a + 1 : ℤ) * t a - 1)
    (hd : ∀ i < L, ((a + i : ℕ) : ℤ) ∣ t (a + i + 1) - t (a + i) + 1)
    (hsmall : (∑ i ∈ Finset.range L, increment t (a + i)) +
      (t (a + L) : ℝ) / (a + L : ℝ) < 1) : False := by
  let D : ℝ := ∑ i ∈ Finset.range L, increment t (a + i)
  let z : ℤ := ∑ i ∈ Finset.range L, quotient t (a + i)
  have he : D = (t a : ℝ) / a - (t (a + L) : ℝ) / (a + L : ℝ) + z :=
    sum_increment_eq t a L ha hd
  have hfirst : increment t a ≤ D := by
    simpa [D] using Finset.single_le_sum
      (fun i hi => hinc i (Finset.mem_range.mp hi))
      (show 0 ∈ Finset.range L by simpa using hL)
  have hstrict : (t a : ℝ) / a < D := by
    rw [UnitTailSeparation.increment_at_unit t a ha hunit] at hfirst
    have hp : (0 : ℝ) < 1 / (a + 1 : ℝ) := by positivity
    linarith
  have hstart : (0 : ℝ) ≤ (t a : ℝ) / a := by
    have ht : (0 : ℝ) ≤ t a := by exact_mod_cast hstartInt
    positivity
  have hend : (0 : ℝ) ≤ (t (a + L) : ℝ) / (a + L : ℝ) := by
    have ht : (0 : ℝ) ≤ t (a + L) := by exact_mod_cast hendInt
    positivity
  have hzpos : (0 : ℝ) < z := by linarith
  have hzlt : (z : ℝ) < 1 := by change D + _ < 1 at hsmall; linarith
  have hzpos' : (0 : ℤ) < z := by exact_mod_cast hzpos
  have hzlt' : z < (1 : ℤ) := by exact_mod_cast hzlt
  omega

theorem no_close_unit_returns (t : ℕ → ℤ) (B a L H : ℕ)
    (haB : B < a) (hL : 0 < L)
    (hsize : a * L + (L + 1) * H + 1 < a ^ 2)
    (hb : ∀ i ≤ L + 1, -(B : ℤ) ≤ t (a + i) ∧ t (a + i) ≤ H)
    (hfirst : t (a + 1) = (a + 1 : ℤ) * t a - 1)
    (hlast : t (a + L + 1) = (a + L + 1 : ℤ) * t (a + L) - 1)
    (hd : ∀ i < L, ((a + i : ℕ) : ℤ) ∣ t (a + i + 1) - t (a + i) + 1) : False := by
  have ha : 0 < a := by omega
  have hap : (0 : ℝ) < a := by positivity
  have hap2 : (0 : ℝ) < (a : ℝ) ^ 2 := by positivity
  have hupper (i : ℕ) (hi : i < L) :
      increment t (a + i) ≤ 1 / (a : ℝ) + H / (a : ℝ) ^ 2 := by
    have ht : (t (a + i + 1) : ℝ) ≤ H := by
      exact_mod_cast (by simpa [Nat.add_assoc] using (hb (i + 1) (by omega)).2 :
        t (a + i + 1) ≤ H)
    have hden : (a : ℝ) ^ 2 ≤ (a + i : ℝ) * (a + i + 1) := by
      have hi0 : (0 : ℝ) ≤ i := by positivity
      nlinarith
    unfold increment
    push_cast
    calc
      _ ≤ 1 / (a + i : ℝ) + (H : ℝ) / ((a + i) * (a + i + 1)) := by
        gcongr
      _ ≤ 1 / (a : ℝ) + (H : ℝ) / (a : ℝ) ^ 2 := by
        gcongr
        · exact_mod_cast Nat.le_add_right a i
  have hsum : (∑ i ∈ Finset.range L, increment t (a + i)) ≤
      (L : ℝ) * (1 / (a : ℝ) + H / (a : ℝ) ^ 2) := by
    have h := Finset.sum_le_sum (fun i hi => hupper i (Finset.mem_range.mp hi))
    simpa [mul_add] using h
  have hbend : (a + L + 1 : ℝ) * t (a + L) ≤ (H : ℝ) + 1 := by
    have he : (t (a + L + 1) : ℝ) =
        (a + L + 1 : ℝ) * t (a + L) - 1 := by exact_mod_cast hlast
    have ht : (t (a + L + 1) : ℝ) ≤ H := by
      exact_mod_cast (by simpa [Nat.add_assoc] using (hb (L + 1) le_rfl).2 :
        t (a + L + 1) ≤ H)
    linarith
  have hend : (t (a + L) : ℝ) / (a + L : ℝ) ≤ ((H : ℝ) + 1) / (a : ℝ) ^ 2 := by
    have ht : (t (a + L) : ℝ) ≤ ((H : ℝ) + 1) / (a + L + 1 : ℝ) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hbend])
    calc
      _ ≤ (((H : ℝ) + 1) / (a + L + 1 : ℝ)) / (a + L : ℝ) := by gcongr
      _ = ((H : ℝ) + 1) / ((a + L + 1) * (a + L) : ℝ) := by rw [div_div]
      _ ≤ ((H : ℝ) + 1) / (a : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) hap2
        have hL0 : (0 : ℝ) ≤ L := by positivity
        nlinarith
  have hsize' : (a : ℝ) * L + (L + 1 : ℝ) * H + 1 < (a : ℝ) ^ 2 := by
    exact_mod_cast hsize
  have hfinal : (L : ℝ) * (1 / (a : ℝ) + H / (a : ℝ) ^ 2) +
      ((H : ℝ) + 1) / (a : ℝ) ^ 2 < 1 := by
    have he : (L : ℝ) * (1 / (a : ℝ) + H / (a : ℝ) ^ 2) +
        ((H : ℝ) + 1) / (a : ℝ) ^ 2 =
        ((a : ℝ) * L + (L + 1 : ℝ) * H + 1) / (a : ℝ) ^ 2 := by
      field_simp
      ring
    rw [he]
    exact (div_lt_one hap2).mpr hsize'
  have hs0 : 0 ≤ t a :=
    unit_predecessor_nonneg t B a haB hfirst
      (by simpa using (hb 1 (by omega)).1)
  have he0 : 0 ≤ t (a + L) :=
    unit_predecessor_nonneg t B (a + L) (by omega) hlast
      (by simpa [Nat.add_assoc] using (hb (L + 1) le_rfl).1)
  apply no_small_increment_return t a L ha hL hs0 he0
    (fun i hi => increment_nonneg t B (a + i) (by omega)
      (by simpa [Nat.add_assoc] using (hb (i + 1) (by omega)).1)) hfirst hd
  linarith

/-- A local criterion allowing a fixed negative lower bound on the tails. -/
theorem irrational_of_local_tails_and_unit_pairs (c : ℕ → ℤ) (B N : ℕ)
    (hc : ∀ n ≥ N, (n : ℤ) ∣ c (n + 1) - 1)
    (hpairs : ∀ M : ℕ, ∃ a ≥ M, ∃ L H : ℕ, 0 < L ∧
      a * L + (L + 1) * H + 1 < a ^ 2 ∧
      c (a + 1) = 1 ∧ c (a + L + 1) = 1 ∧
      ∀ i ≤ L + 1, -(B : ℝ) ≤ FactorialTailCriterion.scaledTail c (a + i) ∧
        FactorialTailCriterion.scaledTail c (a + i) ≤ H) :
    Irrational (∑' k : ℕ, (c k : ℝ) / k.factorial) := by
  rintro ⟨q, hq⟩
  let t : ℕ → ℤ := fun n => q.num * (n.factorial / q.den : ℕ) -
    FactorialTailCriterion.factorialPrefix c n
  have htcast (n : ℕ) (hn : q.den ≤ n) :
      (t n : ℝ) = FactorialTailCriterion.scaledTail c n := by
    have hd : q.den ∣ n.factorial := Nat.dvd_factorial q.pos hn
    have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    simp only [t, FactorialTailCriterion.scaledTail, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [← hq, FactorialTailCriterion.cast_factorialPrefix, Nat.cast_div hd hden, Rat.cast_def]
    ring
  obtain ⟨a, ha, L, H, hL, hsize, hfirst, hlast, hb⟩ := hpairs (max (max N q.den) B + 1)
  have hrec (n : ℕ) (hn : a ≤ n) :
      t (n + 1) = (n + 1 : ℤ) * t n - c (n + 1) := by
    have h := FactorialTailCriterion.scaledTail_succ c n
    rw [← htcast n (by omega), ← htcast (n + 1) (by omega)] at h
    exact_mod_cast h
  apply no_close_unit_returns t B a L H (by omega) hL hsize
  · intro i hi
    have h := hb i hi
    rw [← htcast (a + i) (by omega)] at h
    exact_mod_cast h
  · rw [hrec a le_rfl, hfirst]
  · rw [hrec (a + L) (by omega), hlast]
    push_cast
    ring
  · intro i hi
    rw [hrec (a + i) (by omega)]
    have hd := hc (a + i) (by omega)
    convert dvd_sub (dvd_mul_right (a + i : ℤ) (t (a + i))) hd using 1; push_cast; ring

/-- A fixed negative lower bound is compatible with the square-root-tail
criterion. Its hypotheses have not been proved for the target series. -/
theorem irrational_of_sqrt_tails_prime_coefficients (c : ℕ → ℤ) (B C N : ℕ)
    (hc : ∀ n ≥ N, (n : ℤ) ∣ c (n + 1) - 1)
    (ht : ∀ n ≥ N, -(B : ℝ) ≤ FactorialTailCriterion.scaledTail c n ∧
      FactorialTailCriterion.scaledTail c n ≤ (C : ℝ) * n * (Nat.sqrt n + 1 : ℝ))
    (hp : ∀ p ≥ N, p.Prime → c p = 1) :
    Irrational (∑' k : ℕ, (c k : ℝ) / k.factorial) := by
  apply irrational_of_local_tails_and_unit_pairs c B N hc
  intro M
  obtain ⟨a, ha, L, hL, hgap, hpa, hpb⟩ :=
    SubquadraticTailCriterion.prime_predecessor_pairs_square ((16 * (C + 1)) ^ 2) (max M N)
  obtain ⟨hsize, hb⟩ := SubquadraticTailCriterion.local_sqrt_bounds C a L hL hgap
  refine ⟨a, by omega, L, 8 * C * a * Nat.sqrt a, hL, hsize,
    hp (a + 1) (by omega) hpa, hp (a + L + 1) (by omega) hpb, ?_⟩
  intro i hi
  have ht' := ht (a + i) (by omega)
  refine ⟨ht'.1, ht'.2.trans ?_⟩
  exact_mod_cast hb i hi

end BoundedBelowTailCriterion

#print axioms BoundedBelowTailCriterion.no_close_unit_returns

#print axioms BoundedBelowTailCriterion.irrational_of_local_tails_and_unit_pairs
#print axioms BoundedBelowTailCriterion.irrational_of_sqrt_tails_prime_coefficients
