import FormalConjecturesUtil

/-!
# Exact local identities for comparisons of greatest prime factors

These are elementary helper lemmas only. In particular, this file makes no
assumption or assertion about a density of prime-factor comparisons.
-/

namespace Erdos371

/-- Consecutive natural numbers never have the same greatest prime factor,
including the conventions at zero and one. -/
theorem no_adjacent_tie (n : ℕ) :
    Nat.maxPrimeFac (n + 1) ≠ Nat.maxPrimeFac n := by
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simpa using (show Nat.maxPrimeFac 2 ≠ 1 by
      rw [Nat.prime_two.maxPrimeFac_eq_self]
      omega)
  · intro h
    have hp : (Nat.maxPrimeFac (n + 2)).Prime :=
      Nat.prime_maxPrimeFac_of_one_lt (n + 2) (by omega)
    have hd : Nat.maxPrimeFac (n + 2) ∣ n + 2 := Nat.maxPrimeFac_dvd
    have hd_next : Nat.maxPrimeFac (n + 2) ∣ (n + 2) + 1 := by
      simpa only [h] using (Nat.maxPrimeFac_dvd (n := (n + 2) + 1))
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hd).mpr hd_next)

/-- The sign of the strict comparison; `no_adjacent_tie` excludes a third case. -/
def comparisonSign (n : ℕ) : ℤ :=
  if Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) then 1 else -1

/-- Every comparison sign is either `1` or `-1`. -/
theorem comparisonSign_eq_one_or_neg_one (n : ℕ) :
    comparisonSign n = 1 ∨ comparisonSign n = -1 := by
  unfold comparisonSign
  split_ifs <;> simp

/-- The negative sign is exactly the strictly decreasing case. -/
theorem comparisonSign_eq_neg_one_iff (n : ℕ) :
    comparisonSign n = -1 ↔ Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n := by
  have hne := no_adjacent_tie n
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) <;>
    simp [comparisonSign, h] <;> omega

/-- Multiplication by two does not change the greatest prime factor above one. -/
theorem maxPrimeFac_double {m : ℕ} (hm : 2 ≤ m) :
    Nat.maxPrimeFac (2 * m) = Nat.maxPrimeFac m := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt m (by omega)
  have htwo : 2 ≤ Nat.maxPrimeFac m := hp.two_le
  rw [Nat.maxPrimeFac_mul (by omega) (by omega),
    Nat.prime_two.maxPrimeFac_eq_self, max_eq_right htwo]

/-- A prime factor common to `2*m+1` and `m` would divide one. -/
theorem maxPrimeFac_odd_ne_left {m : ℕ} (hm : 2 ≤ m) :
    Nat.maxPrimeFac (2 * m + 1) ≠ Nat.maxPrimeFac m := by
  intro h
  have hp := Nat.prime_maxPrimeFac_of_one_lt m (by omega)
  have hd : Nat.maxPrimeFac m ∣ 2 * m + 1 := by
    simpa only [h] using (Nat.maxPrimeFac_dvd (n := 2 * m + 1))
  have htwo : Nat.maxPrimeFac m ∣ 2 * m :=
    dvd_mul_of_dvd_right Nat.maxPrimeFac_dvd 2
  have hone : Nat.maxPrimeFac m ∣ 1 :=
    (Nat.dvd_add_iff_right htwo).mpr hd
  exact hp.not_dvd_one hone

/-- A prime factor common to `2*m+1` and `m+1` would divide
`2*(m+1) - (2*m+1) = 1`. -/
theorem maxPrimeFac_odd_ne_right {m : ℕ} (hm : 2 ≤ m) :
    Nat.maxPrimeFac (2 * m + 1) ≠ Nat.maxPrimeFac (m + 1) := by
  intro h
  have hp := Nat.prime_maxPrimeFac_of_one_lt (m + 1) (by omega)
  have hd : Nat.maxPrimeFac (m + 1) ∣ 2 * m + 1 := by
    simpa only [h] using (Nat.maxPrimeFac_dvd (n := 2 * m + 1))
  have htwo : Nat.maxPrimeFac (m + 1) ∣ 2 * (m + 1) :=
    dvd_mul_of_dvd_right Nat.maxPrimeFac_dvd 2
  have hone : Nat.maxPrimeFac (m + 1) ∣ 1 := by
    have hsub : 2 * (m + 1) - (2 * m + 1) = 1 := by omega
    simpa only [hsub] using (Nat.dvd_sub htwo hd)
  exact hp.not_dvd_one hone

/-- Inserting a distinct center between two distinct endpoints doubles the
endpoint sign exactly when the center lies strictly between the endpoints. -/
theorem sign_insertion (a b c : ℕ) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (if a < c then (1 : ℤ) else -1) + (if c < b then (1 : ℤ) else -1) =
      if min a b < c ∧ c < max a b then
        2 * (if a < b then (1 : ℤ) else -1)
      else 0 := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    split_ifs <;> omega
  · rw [min_eq_right h.le, max_eq_left h.le]
    split_ifs <;> omega

/-- Exact local insertion identity for greatest-prime-factor comparisons. -/
theorem comparisonSign_local_insertion {m : ℕ} (hm : 2 ≤ m) :
    comparisonSign (2 * m) + comparisonSign (2 * m + 1) =
      if min (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) <
            Nat.maxPrimeFac (2 * m + 1) ∧
          Nat.maxPrimeFac (2 * m + 1) <
            max (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) then
        2 * comparisonSign m
      else 0 := by
  have hdouble := maxPrimeFac_double hm
  have hdouble_next := maxPrimeFac_double (m := m + 1) (by omega)
  have hnext : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  unfold comparisonSign
  rw [hdouble, hnext, hdouble_next]
  exact sign_insertion _ _ _ (no_adjacent_tie m).symm
    (maxPrimeFac_odd_ne_left hm) (maxPrimeFac_odd_ne_right hm)

/-- The exceptional first pair of comparison signs cancels. -/
theorem comparisonSign_start_sum : comparisonSign 2 + comparisonSign 3 = 0 := by
  have hfour : Nat.maxPrimeFac 4 = 2 := by
    simpa only [Nat.prime_two.maxPrimeFac_eq_self] using
      (maxPrimeFac_double (m := 2) (by omega))
  change (if Nat.maxPrimeFac 2 < Nat.maxPrimeFac 3 then (1 : ℤ) else -1) +
    (if Nat.maxPrimeFac 3 < Nat.maxPrimeFac 4 then (1 : ℤ) else -1) = 0
  norm_num [Nat.prime_two.maxPrimeFac_eq_self, Nat.prime_three.maxPrimeFac_eq_self,
    hfour]

/-- Extending an interval sum to the next odd endpoint adds one even/odd pair. -/
theorem sum_Icc_even_odd_pair (f : ℕ → ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 (2 * (N + 1) + 1), f n) =
      (∑ n ∈ Finset.Icc 2 (2 * N + 1), f n) +
        (f (2 * (N + 1)) + f (2 * (N + 1) + 1)) := by
  calc
    _ = (∑ n ∈ Finset.Icc 2 (2 * (N + 1)), f n) +
          f (2 * (N + 1) + 1) :=
      Finset.sum_Icc_succ_top (by omega) f
    _ = ((∑ n ∈ Finset.Icc 2 (2 * N + 1), f n) + f (2 * (N + 1))) +
          f (2 * (N + 1) + 1) := by
      have hmid : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
      rw [hmid, Finset.sum_Icc_succ_top (by omega) f]
    _ = _ := add_assoc _ _ _

/-- The comparison-sign sum starts at two, so that its first even/odd pair
has sum zero. -/
def comparisonSum (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 2 N, comparisonSign n

/-- Exact finite-sum version of the local insertion identity. It is valid also
for `N = 0` and `N = 1`, when the right-hand interval is empty. -/
theorem comparisonSum_odd (N : ℕ) :
    comparisonSum (2 * N + 1) =
      2 * ∑ m ∈ Finset.Icc 2 N,
        if min (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) <
              Nat.maxPrimeFac (2 * m + 1) ∧
            Nat.maxPrimeFac (2 * m + 1) <
              max (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) then
          comparisonSign m
        else 0 := by
  let f : ℕ → ℤ := fun m ↦
    if min (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) <
          Nat.maxPrimeFac (2 * m + 1) ∧
        Nat.maxPrimeFac (2 * m + 1) <
          max (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) then
      comparisonSign m
    else 0
  change comparisonSum (2 * N + 1) = 2 * ∑ m ∈ Finset.Icc 2 N, f m
  have hlocal (m : ℕ) (hm : 2 ≤ m) :
      comparisonSign (2 * m) + comparisonSign (2 * m + 1) = 2 * f m := by
    rw [comparisonSign_local_insertion hm]
    dsimp only [f]
    split_ifs <;> ring
  induction N with
  | zero => simp [comparisonSum]
  | succ N ih =>
    calc
      comparisonSum (2 * (N + 1) + 1) = comparisonSum (2 * N + 1) +
          (comparisonSign (2 * (N + 1)) + comparisonSign (2 * (N + 1) + 1)) :=
        sum_Icc_even_odd_pair comparisonSign N
      _ = 2 * (∑ m ∈ Finset.Icc 2 N, f m) +
          (comparisonSign (2 * (N + 1)) + comparisonSign (2 * (N + 1) + 1)) := by
        rw [ih]
      _ = 2 * ∑ m ∈ Finset.Icc 2 (N + 1), f m := by
        by_cases hN : N = 0
        · subst N
          change 2 * (∑ m ∈ Finset.Icc 2 0, f m) +
            (comparisonSign 2 + comparisonSign 3) =
              2 * ∑ m ∈ Finset.Icc 2 1, f m
          rw [comparisonSign_start_sum]
          simp
        · rw [hlocal (N + 1) (by omega), Finset.sum_Icc_succ_top (by omega) f]
          ring

end Erdos371

#print axioms Erdos371.no_adjacent_tie
#print axioms Erdos371.comparisonSign
#print axioms Erdos371.comparisonSign_eq_one_or_neg_one
#print axioms Erdos371.comparisonSign_eq_neg_one_iff
#print axioms Erdos371.maxPrimeFac_double
#print axioms Erdos371.maxPrimeFac_odd_ne_left
#print axioms Erdos371.maxPrimeFac_odd_ne_right
#print axioms Erdos371.sign_insertion
#print axioms Erdos371.comparisonSign_local_insertion
#print axioms Erdos371.comparisonSign_start_sum
#print axioms Erdos371.sum_Icc_even_odd_pair
#print axioms Erdos371.comparisonSum
#print axioms Erdos371.comparisonSum_odd
