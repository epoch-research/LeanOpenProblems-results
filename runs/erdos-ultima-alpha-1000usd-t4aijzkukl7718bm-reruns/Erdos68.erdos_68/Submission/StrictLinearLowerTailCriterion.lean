import Submission.SubquadraticTailCriterion

/-!
# A strict linear lower bound for congruent integer tails

Auxiliary work. No application to the conjecture in `Spec.lean` is asserted.
-/

namespace StrictLinearLowerTailCriterion

open CongruentTailSeparation

def lift (t : ℕ → ℤ) (p : ℕ) : ℕ → ℤ
  | 0 => t (p - 1) + 1
  | i + 1 => lift t p i + quotient t (p + i)

def liftSum (t : ℕ → ℤ) (p i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range i, lift t p (j + 1)

lemma liftSum_zero (t : ℕ → ℤ) (p : ℕ) : liftSum t p 0 = 0 := by
  simp [liftSum]

lemma liftSum_succ (t : ℕ → ℤ) (p i : ℕ) :
    liftSum t p (i + 1) = liftSum t p i + lift t p (i + 1) := by
  simp [liftSum, Finset.sum_range_succ]

lemma lifted_identity (t : ℕ → ℤ) (p L : ℕ)
    (hfirst : t p = (p : ℤ) * t (p - 1) - 1)
    (hd : ∀ i < L, ((p + i : ℕ) : ℤ) ∣ t (p + i + 1) - t (p + i) + 1) :
    ∀ i ≤ L, t (p + i) + (p + i : ℕ) + 1 =
      (p + i : ℕ) * lift t p i - liftSum t p i := by
  intro i hi
  induction i with
  | zero => simp [lift, liftSum_zero, hfirst]; ring
  | succ i ih =>
    have he := ih (by omega)
    have hq : ((p + i : ℕ) : ℤ) * quotient t (p + i) =
        t (p + i + 1) - t (p + i) + 1 := Int.mul_ediv_cancel' (hd i (by omega))
    rw [liftSum_succ, lift]
    simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] at *
    nlinarith

lemma lift_nonneg (t : ℕ → ℤ) (p L : ℕ) (hp : 0 < p)
    (hfirst : t p = (p : ℤ) * t (p - 1) - 1)
    (hd : ∀ i < L, ((p + i : ℕ) : ℤ) ∣ t (p + i + 1) - t (p + i) + 1)
    (hlo : ∀ i ≤ L, -2 * ((p + i : ℕ) : ℤ) < t (p + i)) :
    ∀ i ≤ L, 0 ≤ lift t p i ∧ 0 ≤ liftSum t p i := by
  have hid := lifted_identity t p L hfirst hd
  intro i hi
  induction i with
  | zero =>
    have h := hlo 0 (by omega)
    simp only [Nat.add_zero] at h
    rw [hfirst] at h
    have ht : -1 ≤ t (p - 1) := by
      by_contra hn
      have hh : t (p - 1) ≤ -2 := by omega
      have hm := mul_le_mul_of_nonneg_left hh (show (0 : ℤ) ≤ p by omega)
      nlinarith
    simp only [lift, liftSum_zero]
    omega
  | succ i ih =>
    have hprev := ih (by omega)
    have he := hid (i + 1) hi
    rw [liftSum_succ] at he
    have h := hlo (i + 1) hi
    have hp' : (0 : ℤ) < p + i := by omega
    have hs : 0 ≤ lift t p (i + 1) := by
      by_contra hn
      have hn' : lift t p (i + 1) ≤ -1 := by omega
      have hm := mul_le_mul_of_nonneg_left hn' hp'.le
      push_cast at he h
      nlinarith
    exact ⟨hs, by rw [liftSum_succ]; omega⟩

lemma liftSum_mono (t : ℕ → ℤ) (p L : ℕ)
    (hpos : ∀ i ≤ L, 0 ≤ lift t p i) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ L) :
    liftSum t p i ≤ liftSum t p j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
  intro k hk _
  exact hpos (k + 1) (by have := Finset.mem_range.mp hk; omega)

/-- Two unit indices separated by at least two are impossible on an interval
with a sufficiently small upper bound and the strict lower bound `-2n`.
The condition on the gap is essential. -/
theorem no_close_unit_returns (t : ℕ → ℤ) (p L H : ℕ)
    (hp : 0 < p) (hL : 2 ≤ L)
    (hsize : L * H + p * L + 2 * L ^ 2 + L < p ^ 2)
    (hb : ∀ i ≤ L, -2 * ((p + i : ℕ) : ℤ) < t (p + i) ∧ t (p + i) ≤ H)
    (hfirst : t p = (p : ℤ) * t (p - 1) - 1)
    (hlast : t (p + L) = (p + L : ℕ) * t (p + L - 1) - 1)
    (hd : ∀ i < L, ((p + i : ℕ) : ℤ) ∣ t (p + i + 1) - t (p + i) + 1) : False := by
  have hid := lifted_identity t p L hfirst hd
  have hnonneg := lift_nonneg t p L hp hfirst hd (fun i hi => (hb i hi).1)
  have hmono := liftSum_mono t p L (fun i hi => (hnonneg i hi).1)
  have hsbound (j : ℕ) (hj : j < L) :
      (p : ℤ) * lift t p (j + 1) ≤ (H : ℤ) + p + L + 1 + liftSum t p L := by
    have he := hid (j + 1) (by omega)
    rw [liftSum_succ] at he
    have hsum := hmono j L (by omega) le_rfl
    have hsup := (hb (j + 1) (by omega)).2
    have hs := (hnonneg (j + 1) (by omega)).1
    have hj' : (j : ℤ) + 1 ≤ L := by omega
    have hm := mul_nonneg (show (0 : ℤ) ≤ j by omega) hs
    push_cast at he hsup
    nlinarith
  have hsum : (p : ℤ) * liftSum t p L ≤
      (L : ℤ) * ((H : ℤ) + p + L + 1 + liftSum t p L) := by
    have h := Finset.sum_le_sum (fun j hj => hsbound j (Finset.mem_range.mp hj))
    simpa [← Finset.mul_sum, liftSum] using h
  have hgap : L < p := by
    by_contra h
    have hh := Nat.mul_le_mul_left p (show p ≤ L by omega)
    nlinarith
  have hsize' : (L : ℤ) * H + p * L + 2 * (L : ℤ) ^ 2 + L < (p : ℤ) ^ 2 := by
    exact_mod_cast hsize
  have hslt : liftSum t p L < (p + L : ℕ) := by
    by_contra h
    have hge : (p : ℤ) + L ≤ liftSum t p L := by push_cast at h; omega
    have hm := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - L by omega)
      (show 0 ≤ liftSum t p L - ((p : ℤ) + L) by omega)
    nlinarith
  have hsdiv : ((p + L : ℕ) : ℤ) ∣ liftSum t p L := by
    use lift t p L - t (p + L - 1) - 1
    have he := hid L le_rfl
    rw [hlast] at he
    nlinarith
  have hs0 : liftSum t p L = 0 := by
    obtain ⟨z, hz⟩ := hsdiv
    have hnn := (hnonneg L le_rfl).2
    have hpL : (0 : ℤ) < (p + L : ℕ) := by omega
    have hz0 : z = 0 := by
      by_contra hz0
      rcases lt_or_gt_of_ne hz0 with hzneg | hzpos
      · have hh := mul_le_mul_of_nonneg_left (show z ≤ -1 by omega) hpL.le
        rw [hz] at hnn
        nlinarith
      · have hh := mul_le_mul_of_nonneg_left (show 1 ≤ z by omega) hpL.le
        rw [hz] at hslt
        omega
    rw [hz, hz0, mul_zero]
  have hsall (j : ℕ) (hj : j < L) : lift t p (j + 1) = 0 := by
    have hh : lift t p (j + 1) ≤ liftSum t p L := by
      unfold liftSum
      apply Finset.single_le_sum (f := fun k => lift t p (k + 1))
      · intro k hk
        exact (hnonneg (k + 1) (by have := Finset.mem_range.mp hk; omega)).1
      · exact Finset.mem_range.mpr hj
    have hn := (hnonneg (j + 1) (by omega)).1
    omega
  have hslast : lift t p L = 0 := by
    simpa [show L - 1 + 1 = L by omega] using hsall (L - 1) (by omega)
  have hsprev : lift t p (L - 1) = 0 := by
    simpa [show L - 2 + 1 = L - 1 by omega] using hsall (L - 2) (by omega)
  have hSprev : liftSum t p (L - 1) = 0 := by
    have hn := (hnonneg (L - 1) (by omega)).2
    have hm := hmono (L - 1) L (by omega) le_rfl
    omega
  have heprev := hid (L - 1) (by omega)
  have helast := hid L le_rfl
  rw [hsprev, hSprev, mul_zero, sub_zero] at heprev
  rw [hslast, hs0, mul_zero, sub_zero, hlast] at helast
  have heindex : p + (L - 1) = p + L - 1 := by omega
  rw [heindex] at heprev
  have hidx : ((p + L - 1 : ℕ) : ℤ) = (p : ℤ) + L - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  push_cast at helast
  rw [hidx] at heprev
  have hpL : (2 : ℤ) ≤ p + L := by omega
  nlinarith

/-- A local irrationality criterion with lower tail bound strictly above
`-2n`. All bounds are required only along the chosen unit-index intervals. -/
theorem irrational_of_local_tails_and_unit_pairs (c : ℕ → ℤ) (N : ℕ)
    (hc : ∀ n ≥ N, (n : ℤ) ∣ c (n + 1) - 1)
    (hpairs : ∀ M : ℕ, ∃ p ≥ M, ∃ L H : ℕ, 2 ≤ L ∧
      L * H + p * L + 2 * L ^ 2 + L < p ^ 2 ∧
      c p = 1 ∧ c (p + L) = 1 ∧
      ∀ i ≤ L, -2 * (p + i : ℝ) < FactorialTailCriterion.scaledTail c (p + i) ∧
        FactorialTailCriterion.scaledTail c (p + i) ≤ H) :
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
  obtain ⟨p, hp, L, H, hL, hsize, hfirst, hlast, hb⟩ := hpairs (max N q.den + 1)
  have hrec (n : ℕ) (hn : p - 1 ≤ n) :
      t (n + 1) = (n + 1 : ℤ) * t n - c (n + 1) := by
    have h := FactorialTailCriterion.scaledTail_succ c n
    rw [← htcast n (by omega), ← htcast (n + 1) (by omega)] at h
    exact_mod_cast h
  apply no_close_unit_returns t p L H (by omega) hL hsize
  · intro i hi
    have h := hb i hi
    rw [← htcast (p + i) (by omega)] at h
    exact_mod_cast h
  · have h := hrec (p - 1) le_rfl
    have he : p - 1 + 1 = p := by omega
    have he' : ((p - 1 : ℕ) : ℤ) + 1 = p := by exact_mod_cast he
    rw [he, he', hfirst] at h
    exact h
  · have h := hrec (p + L - 1) (by omega)
    have he : p + L - 1 + 1 = p + L := by omega
    have he' : ((p + L - 1 : ℕ) : ℤ) + 1 = (p + L : ℕ) := by exact_mod_cast he
    rw [he, he', hlast] at h
    exact h
  · intro i hi
    rw [hrec (p + i) (by omega)]
    have hd := hc (p + i) (by omega)
    convert dvd_sub (dvd_mul_right (p + i : ℤ) (t (p + i))) hd using 1; push_cast; ring

lemma local_sqrt_bounds (C a L : ℕ) (hL : 0 < L)
    (hgap : ((16 * (C + 1 + 1)) ^ 2 + 1) * (L + 1) ^ 2 < a) :
    L * (8 * C * a * Nat.sqrt a) + (a + 1) * L + 2 * L ^ 2 + L < (a + 1) ^ 2 ∧
      ∀ i ≤ L, C * (a + 1 + i) * (Nat.sqrt (a + 1 + i) + 1) ≤
        8 * C * a * Nat.sqrt a := by
  obtain ⟨hsize, _⟩ := SubquadraticTailCriterion.local_sqrt_bounds (C + 1) a L hL hgap
  have hgap' : ((16 * (C + 1)) ^ 2 + 1) * (L + 1) ^ 2 < a := by
    apply lt_of_le_of_lt _ hgap
    gcongr
    omega
  obtain ⟨_, hb⟩ := SubquadraticTailCriterion.local_sqrt_bounds C a L hL hgap'
  have hLa : L ≤ a := by
    have hsq : (L + 1) ^ 2 ≤ ((16 * (C + 1 + 1)) ^ 2 + 1) * (L + 1) ^ 2 :=
      Nat.le_mul_of_pos_left _ (by positivity)
    nlinarith
  have ha : 1 ≤ a := by omega
  have hs : 1 ≤ Nat.sqrt a := by
    exact Nat.le_sqrt'.mpr (by simpa using ha)
  have hslack : 2 * L * (L + 1) ≤ 8 * a * Nat.sqrt a * (L + 1) := by
    apply Nat.mul_le_mul_right (L + 1)
    have hh := Nat.mul_le_mul_left (8 * a) hs
    nlinarith
  constructor
  · calc
      _ = a * L + L * (8 * C * a * Nat.sqrt a) + 2 * L * (L + 1) := by ring
      _ ≤ a * L + L * (8 * C * a * Nat.sqrt a) +
          8 * a * Nat.sqrt a * (L + 1) := Nat.add_le_add_left hslack _
      _ ≤ a * L + (L + 1) * (8 * (C + 1) * a * Nat.sqrt a) + 1 := by
        nlinarith only [Nat.zero_le (8 * C * a * Nat.sqrt a)]
      _ < a ^ 2 := hsize
      _ ≤ (a + 1) ^ 2 := by nlinarith
  · intro i hi
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb (i + 1) (by omega)

/-- Congruent integer factorial coefficients with prime coefficients one
have irrational sum when their scaled tails are strictly above `-2n` and
at most `C n (sqrt n + 1)` eventually. -/
theorem irrational_of_sqrt_tails_prime_coefficients (c : ℕ → ℤ) (C N : ℕ)
    (hc : ∀ n ≥ N, (n : ℤ) ∣ c (n + 1) - 1)
    (ht : ∀ n ≥ N, -2 * (n : ℝ) < FactorialTailCriterion.scaledTail c n ∧
      FactorialTailCriterion.scaledTail c n ≤ (C : ℝ) * n * (Nat.sqrt n + 1 : ℝ))
    (hp : ∀ p ≥ N, p.Prime → c p = 1) :
    Irrational (∑' k : ℕ, (c k : ℝ) / k.factorial) := by
  apply irrational_of_local_tails_and_unit_pairs c N hc
  intro M
  obtain ⟨a, ha, L, hL, hgap, hpa, hpb⟩ :=
    SubquadraticTailCriterion.prime_predecessor_pairs_square
      ((16 * (C + 1 + 1)) ^ 2) (max M N + 3)
  obtain ⟨hsize, hb⟩ := local_sqrt_bounds C a L hL hgap
  have hL2 : 2 ≤ L := by
    have hpa2 := hpa.eq_two_or_odd
    have hpb2 := hpb.eq_two_or_odd
    omega
  refine ⟨a + 1, by omega, L, 8 * C * a * Nat.sqrt a, hL2, hsize,
    hp (a + 1) (by omega) hpa, hp (a + 1 + L) (by omega) (by convert hpb using 1; omega), ?_⟩
  intro i hi
  have ht' := ht (a + 1 + i) (by omega)
  refine ⟨by simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using ht'.1, ht'.2.trans ?_⟩
  exact_mod_cast hb i hi

#print axioms irrational_of_local_tails_and_unit_pairs
#print axioms irrational_of_sqrt_tails_prime_coefficients

#print axioms lifted_identity
#print axioms lift_nonneg
#print axioms no_close_unit_returns

end StrictLinearLowerTailCriterion
