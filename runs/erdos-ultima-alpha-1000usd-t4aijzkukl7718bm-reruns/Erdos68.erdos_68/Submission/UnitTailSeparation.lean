import Submission.CongruentTailSeparation

/-!
# A sharper separation lemma using the first unit coefficient

Auxiliary work only. The original conjecture in Spec.lean is not settled.
Unlike `no_close_small_returns`, this lemma uses the exact unit recurrence
at the first endpoint, and does not require a lower bound on the gap beyond
positivity. The upper bound on the tails may depend on the chosen interval.
-/

namespace UnitTailSeparation

open CongruentTailSeparation

lemma increment_at_unit (t : ℕ → ℤ) (a : ℕ) (ha : 0 < a)
    (hu : t (a + 1) = (a + 1 : ℤ) * t a - 1) :
    increment t a = (t a : ℝ) / a + 1 / (a + 1 : ℝ) := by
  have hr : (t (a + 1) : ℝ) = (a + 1 : ℝ) * t a - 1 := by
    exact_mod_cast hu
  have ha' : (a : ℝ) ≠ 0 := by positivity
  have hs : (a + 1 : ℝ) ≠ 0 := by positivity
  unfold increment
  rw [hr]
  field_simp
  ring

/-- The first unit recurrence forces the total increment past the initial
normalized tail. An integer congruence then rules out a sufficiently short
return, without needing a separate lower bound on the gap. -/
theorem no_small_increment_return (t : ℕ → ℤ) (a L : ℕ)
    (ha : 0 < a) (hL : 0 < L)
    (hnn : ∀ i ≤ L, 0 ≤ t (a + i))
    (hunit : t (a + 1) = (a + 1 : ℤ) * t a - 1)
    (hd : ∀ i < L, ((a + i : ℕ) : ℤ) ∣ t (a + i + 1) - t (a + i) + 1)
    (hsmall : (∑ i ∈ Finset.range L, increment t (a + i)) +
      (t (a + L) : ℝ) / (a + L : ℝ) < 1) : False := by
  let D : ℝ := ∑ i ∈ Finset.range L, increment t (a + i)
  let z : ℤ := ∑ i ∈ Finset.range L, quotient t (a + i)
  have he : D = (t a : ℝ) / a - (t (a + L) : ℝ) / (a + L : ℝ) + z :=
    sum_increment_eq t a L ha hd
  have hinc (i : ℕ) (hi : i < L) : 0 ≤ increment t (a + i) := by
    have ht : (0 : ℝ) ≤ t (a + i + 1) := by
      exact_mod_cast (by simpa [Nat.add_assoc] using hnn (i + 1) (by omega) :
        0 ≤ t (a + i + 1))
    unfold increment
    positivity
  have hfirst : increment t a ≤ D := by
    simpa [D] using Finset.single_le_sum
      (fun i hi => hinc i (Finset.mem_range.mp hi))
      (show 0 ∈ Finset.range L by simpa using hL)
  have hstrict : (t a : ℝ) / a < D := by
    rw [increment_at_unit t a ha hunit] at hfirst
    have hp : (0 : ℝ) < 1 / (a + 1 : ℝ) := by positivity
    linarith
  have hstart : (0 : ℝ) ≤ (t a : ℝ) / a := by
    have ht : (0 : ℝ) ≤ t a := by exact_mod_cast (by simpa using hnn 0 (by omega) : 0 ≤ t a)
    positivity
  have hend : (0 : ℝ) ≤ (t (a + L) : ℝ) / (a + L : ℝ) := by
    have ht : (0 : ℝ) ≤ t (a + L) := by exact_mod_cast hnn L le_rfl
    positivity
  have hzpos : (0 : ℝ) < z := by linarith
  have hzlt : (z : ℝ) < 1 := by change D + _ < 1 at hsmall; linarith
  have hzpos' : (0 : ℤ) < z := by exact_mod_cast hzpos
  have hzlt' : z < (1 : ℤ) := by exact_mod_cast hzlt
  omega

/-- A uniform absolute bound on the tails over one interval suffices. In
particular, the bound `H` is allowed to grow with `a`. -/
theorem no_close_unit_returns (t : ℕ → ℤ) (a L H : ℕ)
    (ha : 0 < a) (hL : 0 < L)
    (hsize : a * L + (L + 1) * H + 1 < a ^ 2)
    (hb : ∀ i ≤ L + 1, 0 ≤ t (a + i) ∧ t (a + i) ≤ H)
    (hfirst : t (a + 1) = (a + 1 : ℤ) * t a - 1)
    (hlast : t (a + L + 1) = (a + L + 1 : ℤ) * t (a + L) - 1)
    (hd : ∀ i < L, ((a + i : ℕ) : ℤ) ∣ t (a + i + 1) - t (a + i) + 1) : False := by
  have hap : (0 : ℝ) < a := by positivity
  have hap2 : (0 : ℝ) < (a : ℝ) ^ 2 := by positivity
  have hupper (i : ℕ) (hi : i < L) :
      increment t (a + i) ≤ 1 / (a : ℝ) + H / (a : ℝ) ^ 2 := by
    have ht : (t (a + i + 1) : ℝ) ≤ H := by
      exact_mod_cast (by simpa [Nat.add_assoc] using (hb (i + 1) (by omega)).2 :
        t (a + i + 1) ≤ H)
    have ht0 : (0 : ℝ) ≤ t (a + i + 1) := by
      exact_mod_cast (by simpa [Nat.add_assoc] using (hb (i + 1) (by omega)).1 :
        0 ≤ t (a + i + 1))
    have hden : (a : ℝ) ^ 2 ≤ (a + i : ℝ) * (a + i + 1) := by
      have hi0 : (0 : ℝ) ≤ i := by positivity
      nlinarith
    unfold increment
    push_cast
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
  apply no_small_increment_return t a L ha hL
    (fun i hi => (hb i (by omega)).1) hfirst hd
  linarith

#print axioms no_small_increment_return
#print axioms no_close_unit_returns

end UnitTailSeparation
