import Submission.FactorialTailCriterion

/-!
# Separation of small integer tails under a factorial congruence

An auxiliary arithmetic obstruction. The Lambert representation of Erdős 68
has tails too large for the linear bound here; the small-tail rowwise
representation does not have the required congruence.
-/

namespace CongruentTailSeparation

noncomputable def increment (t : ℕ → ℤ) (n : ℕ) : ℝ :=
  1 / (n : ℝ) + (t (n + 1) : ℝ) / ((n : ℝ) * (n + 1 : ℝ))

def quotient (t : ℕ → ℤ) (n : ℕ) : ℤ :=
  (t (n + 1) - t n + 1) / (n : ℤ)

lemma increment_eq (t : ℕ → ℤ) (n : ℕ) (hn : 0 < n)
    (hd : (n : ℤ) ∣ t (n + 1) - t n + 1) :
    increment t n = (t n : ℝ) / n - (t (n + 1) : ℝ) / (n + 1 : ℝ) +
      (quotient t n : ℝ) := by
  have hrec : (n : ℝ) * (quotient t n : ℝ) =
      (t (n + 1) : ℝ) - (t n : ℝ) + 1 := by
    exact_mod_cast Int.mul_ediv_cancel' hd
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hs : (n + 1 : ℝ) ≠ 0 := by positivity
  unfold increment
  field_simp
  nlinarith [hrec]

lemma sum_increment_eq (t : ℕ → ℤ) (a L : ℕ) (ha : 0 < a)
    (hd : ∀ i < L, ((a + i : ℕ) : ℤ) ∣ t (a + i + 1) - t (a + i) + 1) :
    (∑ i ∈ Finset.range L, increment t (a + i)) =
      (t a : ℝ) / a - (t (a + L) : ℝ) / (a + L : ℝ) +
        ((∑ i ∈ Finset.range L, quotient t (a + i) : ℤ) : ℝ) := by
  simp_rw [Int.cast_sum]
  have he := Finset.sum_range_sub' (fun i => (t (a + i) : ℝ) / (a + i : ℝ)) L
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at he
  rw [← he, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, add_assoc] using
    increment_eq t (a + i) (by omega) (hd i (Finset.mem_range.mp hi))

/-- A nonnegative, linearly bounded congruent integer tail cannot revisit
small values after a moderately long but relatively short interval. -/
theorem no_close_small_returns (t : ℕ → ℤ) (C a L : ℕ)
    (hgap : 2 * C < L) (hlarge : (C + 1) * L + C < a)
    (hb : ∀ i ≤ L, 0 ≤ t (a + i) ∧ t (a + i) ≤ (C : ℤ) * (a + i : ℕ))
    (hfirst : t a ≤ C) (hlast : t (a + L) ≤ C)
    (hd : ∀ i < L, ((a + i : ℕ) : ℤ) ∣ t (a + i + 1) - t (a + i) + 1) : False := by
  have ha : 0 < a := by omega
  have hL : 0 < L := by omega
  have hLa : L < a := by nlinarith
  have hap : (0 : ℝ) < a := by positivity
  have hbp : (0 : ℝ) < (a + L : ℝ) := by positivity
  have hgap' : (2 : ℝ) * C < L := by exact_mod_cast hgap
  have hlarge' : ((C : ℝ) + 1) * L + C < a := by exact_mod_cast hlarge
  have hLa' : (L : ℝ) < a := by exact_mod_cast hLa
  have h0 : 0 ≤ (t a : ℝ) := by exact_mod_cast (by simpa using (hb 0 (by omega)).1 : 0 ≤ t a)
  have h1 : 0 ≤ (t (a + L) : ℝ) := by exact_mod_cast (hb L le_rfl).1
  have hf : (t a : ℝ) ≤ C := by exact_mod_cast hfirst
  have hl : (t (a + L) : ℝ) ≤ C := by exact_mod_cast hlast
  let D : ℝ := ∑ i ∈ Finset.range L, increment t (a + i)
  let z : ℤ := ∑ i ∈ Finset.range L, quotient t (a + i)
  have he : D = (t a : ℝ) / a - (t (a + L) : ℝ) / (a + L : ℝ) + z :=
    sum_increment_eq t a L ha hd
  have hbounds (i : ℕ) (hi : i < L) :
      1 / (a + L : ℝ) ≤ increment t (a + i) ∧
      increment t (a + i) ≤ ((C : ℝ) + 1) / a := by
    have hn : (0 : ℝ) < a + i := by positivity
    have hs : (0 : ℝ) < a + i + 1 := by positivity
    have hnn : 0 ≤ (t (a + i + 1) : ℝ) := by
      exact_mod_cast (by simpa [Nat.add_assoc] using (hb (i + 1) (by omega)).1 :
        0 ≤ t (a + i + 1))
    have hupper : (t (a + i + 1) : ℝ) ≤ (C : ℝ) * (a + i + 1) := by
      exact_mod_cast (by simpa [Nat.add_assoc] using (hb (i + 1) (by omega)).2 :
        t (a + i + 1) ≤ (C : ℤ) * (a + i + 1 : ℕ))
    have hil : (i : ℝ) ≤ L := by exact_mod_cast hi.le
    unfold increment
    push_cast
    constructor
    · have hrec : 1 / (a + L : ℝ) ≤ 1 / (a + i : ℝ) :=
        one_div_le_one_div_of_le hn (by linarith)
      have hnn' : 0 ≤ (t (a + i + 1) : ℝ) / ((a + i) * (a + i + 1) : ℝ) :=
        div_nonneg hnn (by positivity)
      linarith
    · calc
        _ ≤ 1 / (a + i : ℝ) + ((C : ℝ) * (a + i + 1)) / ((a + i) * (a + i + 1)) := by
          gcongr
        _ = ((C : ℝ) + 1) / (a + i) := by field_simp; ring
        _ ≤ ((C : ℝ) + 1) / a := by gcongr; (first | positivity | linarith)
  have hlo : (L : ℝ) / (a + L) ≤ D := by
    have h := Finset.sum_le_sum (fun i hi => (hbounds i (Finset.mem_range.mp hi)).1)
    simpa [D, nsmul_eq_mul, div_eq_mul_inv] using h
  have hup : D ≤ ((C : ℝ) + 1) * L / a := by
    have h := Finset.sum_le_sum (fun i hi => (hbounds i (Finset.mem_range.mp hi)).2)
    simpa [D, nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hy0 : 0 ≤ (t a : ℝ) / a := div_nonneg h0 hap.le
  have hy1 : 0 ≤ (t (a + L) : ℝ) / (a + L : ℝ) := div_nonneg h1 hbp.le
  have hy0u : (t a : ℝ) / a ≤ (C : ℝ) / a := by gcongr
  have hy1u : (t (a + L) : ℝ) / (a + L : ℝ) ≤ (C : ℝ) / a := by
    calc
      _ ≤ (C : ℝ) / (a + L) := by gcongr
      _ ≤ (C : ℝ) / a := by gcongr; (first | positivity | linarith)
  have hca : (C : ℝ) / a < 1 := (div_lt_one hap).mpr (by nlinarith)
  have hsumlt : ((C : ℝ) + 1) * L / a + (C : ℝ) / a < 1 := by
    rw [← add_div]
    exact (div_lt_one hap).mpr hlarge'
  have hzlo : (-1 : ℝ) < z := by
    have : 0 ≤ D := (by positivity : (0 : ℝ) ≤ L / (a + L)).trans hlo
    linarith
  have hzhi : (z : ℝ) < 1 := by linarith
  have hz : z = 0 := by
    have hh0 : (-1 : ℤ) < z := by exact_mod_cast hzlo
    have hh1 : z < (1 : ℤ) := by exact_mod_cast hzhi
    omega
  rw [hz, Int.cast_zero, add_zero] at he
  have hfinal : (L : ℝ) / (a + L) ≤ (C : ℝ) / a := by linarith
  have hc := (div_le_div_iff₀ hbp hap).mp hfinal
  have hCp : (0 : ℝ) ≤ C := by positivity
  nlinarith

/-- A factorial-series irrationality criterion allowing a linear tail bound,
provided unit coefficients occur in suitable pairs. -/
theorem irrational_of_linear_tails_and_unit_pairs (c : ℕ → ℤ) (C N : ℕ)
    (hc : ∀ n ≥ N, (n : ℤ) ∣ c (n + 1) - 1)
    (ht : ∀ n ≥ N, 0 ≤ FactorialTailCriterion.scaledTail c n ∧
      FactorialTailCriterion.scaledTail c n ≤ (C : ℝ) * n)
    (hpairs : ∀ M : ℕ, ∃ a ≥ M, ∃ L : ℕ,
      2 * C < L ∧ (C + 1) * L + C < a ∧
        c (a + 1) = 1 ∧ c (a + L + 1) = 1) :
    Irrational (∑' k : ℕ, (c k : ℝ) / k.factorial) := by
  open FactorialTailCriterion in
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
  obtain ⟨a, ha, L, hgap, hlarge, hfirst, hlast⟩ := hpairs (max N q.den + 1)
  have hapos : 0 < a := by omega
  have hrec (n : ℕ) (hn : a ≤ n) :
      t (n + 1) = (n + 1 : ℤ) * t n - c (n + 1) := by
    have h := FactorialTailCriterion.scaledTail_succ c n
    rw [← htcast n (by omega), ← htcast (n + 1) (by omega)] at h
    exact_mod_cast h
  have hb (n : ℕ) (hn : a ≤ n) : 0 ≤ t n ∧ t n ≤ (C : ℤ) * n := by
    have h := ht n (by omega)
    rw [← htcast n (by omega)] at h
    exact_mod_cast h
  have hsmall (n : ℕ) (hn : a ≤ n) (hu : c (n + 1) = 1) : t n ≤ C := by
    have h := (hb (n + 1) (by omega)).2
    rw [hrec n hn, hu] at h
    have hn' : (0 : ℤ) < n := by omega
    by_contra hbad
    have : (C : ℤ) + 1 ≤ t n := by omega
    have hh := mul_le_mul_of_nonneg_left this (show 0 ≤ (n + 1 : ℤ) by omega)
    push_cast at h
    nlinarith
  apply no_close_small_returns t C a L hgap hlarge
  · intro i hi
    exact hb (a + i) (by omega)
  · exact hsmall a le_rfl hfirst
  · exact hsmall (a + L) (by omega) hlast
  · intro i hi
    rw [hrec (a + i) (by omega)]
    have hd := hc (a + i) (by omega)
    convert dvd_sub (dvd_mul_right (a + i : ℤ) (t (a + i))) hd using 1 <;> push_cast <;> ring

#print axioms no_close_small_returns
#print axioms irrational_of_linear_tails_and_unit_pairs

end CongruentTailSeparation
