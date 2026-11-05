import FormalConjecturesUtil

/-!
# Elementary reductions for three distinct unit fractions

These lemmas establish equivalence with the usual Erdős–Straus equation and
reduce the universal problem to primes congruent to one modulo twenty-four.
-/

namespace Erdos242Aux

/-- The usual Erdős–Straus equation, allowing repeated denominators. -/
def Ordinary (n : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (4 / n : ℚ) = 1 / a + 1 / b + 1 / c

/-- Exactly the positive, strictly ordered statement in the task. -/
def Distinct (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

lemma even_solution (k : ℕ) (hk : 2 ≤ k) : Distinct (2 * k) := by
  refine ⟨k, k + 1, k * (k + 1), by omega, by omega, ?_, ?_⟩
  · nlinarith
  · have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hk10 : ((k : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hk0, hk10]
    ring

lemma split_larger (n a b : ℕ) (ha : 0 < a) (hab : a < b)
    (h : (4 / n : ℚ) = 1 / a + 1 / b) : Distinct n := by
  refine ⟨a, b + 1, b * (b + 1), by omega, by omega, ?_, ?_⟩
  · have hb : 2 ≤ b := by omega
    nlinarith
  · calc
      (4 / n : ℚ) = 1 / a + 1 / b := h
      _ = 1 / a + 1 / (b + 1 : ℕ) + 1 / (b * (b + 1) : ℕ) := by
        have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
        have hb10 : ((b : ℚ) + 1) ≠ 0 := by positivity
        push_cast
        field_simp [hb0, hb10]
        ring

lemma two_solution (n : ℕ) (hn : 2 < n) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (h : (4 / n : ℚ) = 1 / a + 1 / b) : Distinct n := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact split_larger n a b ha hab h
  · subst b
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
    have hq := h
    field_simp [hn0, ha0] at hq
    have hna : n = 2 * a := by
      have he : (n : ℚ) = 2 * (a : ℚ) := by nlinarith
      exact_mod_cast he
    rw [hna]
    exact even_solution a (by omega)
  · exact split_larger n b a hb hab (by simpa [add_comm] using h)

lemma repeated_solution (n d e : ℕ) (hn : 2 < n)
    (hd : 0 < d) (he : 0 < e)
    (h : (4 / n : ℚ) = 1 / d + 1 / d + 1 / e) : Distinct n := by
  by_cases hnEven : Even n
  · obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hnEven
    rw [hk]
    exact even_solution k (by omega)
  · have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
    have hq := h
    field_simp [hn0, hd0, he0] at hq
    have hpoly : 4 * d * e = n * (d + 2 * e) := by
      have hpolyQ : (4 : ℚ) * d * e = n * ((d : ℚ) + 2 * e) := by
        nlinarith
      exact_mod_cast hpolyQ
    have hprod : Even (n * (d + 2 * e)) := by
      rw [← hpoly]
      exact ⟨2 * d * e, by ring⟩
    have hsum : Even (d + 2 * e) := (Nat.even_mul.mp hprod).resolve_left hnEven
    have hdEven : Even d := (Nat.even_add.mp hsum).mpr ⟨e, by omega⟩
    obtain ⟨s, hs⟩ := even_iff_exists_two_mul.mp hdEven
    have hspos : 0 < s := by omega
    apply two_solution n hn s e hspos he
    have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
    have hds : (d : ℚ) = 2 * (s : ℚ) := by exact_mod_cast hs
    calc
      (4 / n : ℚ) = 1 / d + 1 / d + 1 / e := h
      _ = 1 / s + 1 / e := by
        rw [hds]
        field_simp [hs0, he0]
        ring

lemma sort_three (n a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : (4 / n : ℚ) = 1 / a + 1 / b + 1 / c) : Distinct n := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact ⟨a, b, c, by omega, hab, hbc, h⟩
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact ⟨a, c, b, by omega, hac, hcb, by simpa [add_comm, add_left_comm, add_assoc] using h⟩
      · exact ⟨c, a, b, by omega, hca, hab, by simpa [add_comm, add_left_comm, add_assoc] using h⟩
  · rcases lt_or_gt_of_ne hac with hac | hca
    · exact ⟨b, a, c, by omega, hba, hac, by simpa [add_comm, add_left_comm, add_assoc] using h⟩
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact ⟨b, c, a, by omega, hbc, hca, by simpa [add_comm, add_left_comm, add_assoc] using h⟩
      · exact ⟨c, b, a, by omega, hcb, hba, by simpa [add_comm, add_left_comm, add_assoc] using h⟩

/-- Distinctness makes no difference for any individual n>2. -/
theorem ordinary_iff_distinct (n : ℕ) (hn : 2 < n) : Ordinary n ↔ Distinct n := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, h⟩
    by_cases hab : a = b
    · subst b
      exact repeated_solution n a c hn ha hc h
    by_cases hac : a = c
    · subst c
      exact repeated_solution n a b hn ha hb (by simpa [add_comm, add_left_comm, add_assoc] using h)
    by_cases hbc : b = c
    · subst c
      exact repeated_solution n b a hn hb ha (by simpa [add_comm, add_left_comm, add_assoc] using h)
    exact sort_three n a b c ha hb hc hab hac hbc h
  · rintro ⟨a, b, c, ha, hab, hbc, h⟩
    exact ⟨a, b, c, by omega, by omega, by omega, h⟩

/-- The sole omitted n=2 is an ordinary solution, but does not have three distinct denominators. -/
lemma ordinary_two : Ordinary 2 := by
  refine ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

lemma distinct_three : Distinct 3 := by
  refine ⟨1, 4, 12, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- The universal statements, including the usual n=2 case, are equivalent. -/
theorem global_equivalence :
    (∀ n : ℕ, 2 ≤ n → Ordinary n) ↔ (∀ n : ℕ, 2 < n → Distinct n) := by
  constructor
  · intro h n hn
    exact (ordinary_iff_distinct n hn).mp (h n (by omega))
  · intro h n hn
    by_cases htwo : n = 2
    · subst n
      exact ordinary_two
    · have hn' : 2 < n := by omega
      exact (ordinary_iff_distinct n hn').mpr (h n hn')

lemma not_distinct_two : ¬ Distinct 2 := by
  rintro ⟨x, y, z, hx, hxy, hyz, h⟩
  have hxQ : (1 : ℚ) ≤ x := by exact_mod_cast hx
  have hyQ : (2 : ℚ) ≤ y := by exact_mod_cast (by omega : 2 ≤ y)
  have hzQ : (3 : ℚ) ≤ z := by exact_mod_cast (by omega : 3 ≤ z)
  have hxb := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hxQ
  have hyb := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) hyQ
  have hzb := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) hzQ
  norm_num at h hxb hyb hzb
  linarith

lemma scale_solution (n k : ℕ) (h : Distinct n) (hk : 0 < k) : Distinct (k * n) := by
  rcases h with ⟨x, y, z, hx, hxy, hyz, heq⟩
  refine ⟨k * x, k * y, k * z, ?_, ?_, ?_, ?_⟩
  · have hpos : 0 < k * x := Nat.mul_pos hk (by omega)
    omega
  · exact Nat.mul_lt_mul_of_pos_left hxy hk
  · exact Nat.mul_lt_mul_of_pos_left hyz hk
  · push_cast
    calc
      (4 : ℚ) / ((k : ℚ) * n) = (4 / (n : ℚ)) / k := by
        rw [mul_comm, div_mul_eq_div_div]
      _ = (1 / (x : ℚ) + 1 / y + 1 / z) / k := by rw [heq]
      _ = 1 / ((k : ℚ) * x) + 1 / ((k : ℚ) * y) + 1 / ((k : ℚ) * z) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

/-- For the strictly ordered problem, even n are handled explicitly before prime reduction. -/
theorem prime_reduction :
    (∀ n : ℕ, 2 < n → Distinct n) ↔
      (∀ p : ℕ, p.Prime → 2 < p → Distinct p) := by
  constructor
  · intro h p _ hp
    exact h p hp
  · intro h n hn
    by_cases hnEven : Even n
    · obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hnEven
      rw [hk]
      exact even_solution k (by omega)
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      have hp2 : 2 < p := by
        have hple := hp.two_le
        have hne : p ≠ 2 := by
          intro heq
          subst p
          exact hnEven (even_iff_two_dvd.mpr hpn)
        omega
      obtain ⟨k, hk⟩ := hpn
      have hkpos : 0 < k := by nlinarith
      have hs := scale_solution p k (h p hp hp2) hkpos
      simpa [hk, Nat.mul_comm] using hs

lemma three_mod_four_solution (k : ℕ) : Distinct (4 * k + 3) := by
  apply split_larger (4 * k + 3) (k + 1) ((k + 1) * (4 * k + 3)) (by omega)
  · nlinarith
  · have hk0 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hn0 : ((4 : ℚ) * k + 3) ≠ 0 := by positivity
    push_cast
    field_simp [hk0, hn0]
    ring

lemma two_mod_three_solution (k : ℕ) (hk : 1 ≤ k) : Distinct (3 * k + 2) := by
  refine ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1), by omega, by omega, ?_, ?_⟩
  · nlinarith
  · have hk0 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hn0 : ((3 : ℚ) * k + 2) ≠ 0 := by positivity
    push_cast
    field_simp [hk0, hn0]
    ring

lemma thirteen_mod_twentyfour_solution (k : ℕ) : Distinct (24 * k + 13) := by
  refine ⟨6 * k + 4, (24 * k + 13) * (3 * k + 2),
    (24 * k + 13) * (6 * k + 4), by omega, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have hn0 : ((24 : ℚ) * k + 13) ≠ 0 := by positivity
    have ha0 : ((6 : ℚ) * k + 4) ≠ 0 := by positivity
    have hb0 : ((3 : ℚ) * k + 2) ≠ 0 := by positivity
    push_cast
    field_simp [hn0, ha0, hb0]
    ring

/-- All remaining possibilities are n≡1 (mod 24). -/
theorem non_one_mod_twentyfour_solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 24 ≠ 1) : Distinct n := by
  by_cases hnEven : Even n
  · obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hnEven
    rw [hk]
    exact even_solution k (by omega)
  have hnOdd : n % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hnEven)
  by_cases hn4 : n % 4 = 3
  · have hform : n = 4 * (n / 4) + 3 := by omega
    rw [hform]
    exact three_mod_four_solution (n / 4)
  by_cases hn30 : n % 3 = 0
  · have hform : n = (n / 3) * 3 := by omega
    have hkpos : 0 < n / 3 := by omega
    rw [hform]
    exact scale_solution 3 (n / 3) distinct_three hkpos
  by_cases hn32 : n % 3 = 2
  · have hform : n = 3 * (n / 3) + 2 := by omega
    have hkpos : 1 ≤ n / 3 := by omega
    rw [hform]
    exact two_mod_three_solution (n / 3) hkpos
  have hform : n = 24 * (n / 24) + 13 := by omega
  rw [hform]
  exact thirteen_mod_twentyfour_solution (n / 24)

/-- Equivalent to the conjecture just on primes congruent to 1 modulo 24. -/
theorem prime_one_mod_twentyfour_reduction :
    (∀ n : ℕ, 2 < n → Distinct n) ↔
      (∀ p : ℕ, p.Prime → p % 24 = 1 → Ordinary p) := by
  constructor
  · intro h p hp hmod
    have hp2 : 2 < p := by have := hp.two_le; omega
    exact (ordinary_iff_distinct p hp2).mpr (h p hp2)
  · intro h
    apply prime_reduction.mpr
    intro p hp hp2
    by_cases hmod : p % 24 = 1
    · exact (ordinary_iff_distinct p hp2).mp (h p hp hmod)
    · exact non_one_mod_twentyfour_solution p hp2 hmod


end Erdos242Aux
