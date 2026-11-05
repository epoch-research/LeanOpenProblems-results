import FormalConjecturesUtil

/-!
# Structure and centered-product reductions for powerful numbers

These are unconditional helper theorems for Erdős problem 364, not a proof or
refutation of the conjecture. In particular, the original specification is not
imported, and no assertion of existence or nonexistence of a powerful triple is
used here. The convention that `0` is powerful is retained.
-/

namespace Erdos364.PowerfulStructure

/-- A formulation that handles the powerful number `0` as well as positive numbers. -/
theorem powerful_iff_prime_sq_divides (m : ℕ) :
    Nat.Powerful m ↔ ∀ p : ℕ, Nat.Prime p → p ∣ m → p ^ 2 ∣ m := by
  constructor
  · intro hm p hp hpm
    by_cases hzero : m = 0
    · simp [hzero]
    · exact hm p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hzero⟩)
  · intro hm p hpf
    exact hm p (Nat.mem_primeFactors.mp hpf).1 (Nat.mem_primeFactors.mp hpf).2.1

/-- Products of powerful numbers are powerful, without a coprimality assumption. -/
theorem powerful_mul {a b : ℕ} (ha : Nat.Powerful a) (hb : Nat.Powerful b) :
    Nat.Powerful (a * b) := by
  apply (powerful_iff_prime_sq_divides (a * b)).mpr
  intro p hp hdiv
  rcases hp.dvd_mul.mp hdiv with hpa | hpb
  · exact dvd_mul_of_dvd_left ((powerful_iff_prime_sq_divides a).mp ha p hp hpa) b
  · exact dvd_mul_of_dvd_right ((powerful_iff_prime_sq_divides b).mp hb p hp hpb) a

/-- A coprime factor of a powerful product is powerful. This includes zero factors. -/
theorem powerful_of_coprime_mul_left {a b : ℕ} (hab : Nat.Coprime a b)
    (h : Nat.Powerful (a * b)) : Nat.Powerful a := by
  apply (powerful_iff_prime_sq_divides a).mpr
  intro p hp hpa
  have hpb : Nat.Coprime p b := hab.coprime_dvd_left hpa
  exact (hpb.pow_left 2).dvd_of_dvd_mul_right
    ((powerful_iff_prime_sq_divides (a * b)).mp h p hp (dvd_mul_of_dvd_left hpa b))

/-- The right-hand version of coprime-factor extraction. -/
theorem powerful_of_coprime_mul_right {a b : ℕ} (hab : Nat.Coprime a b)
    (h : Nat.Powerful (a * b)) : Nat.Powerful b := by
  apply powerful_of_coprime_mul_left hab.symm
  simpa only [mul_comm] using h

/-- On coprime products, powerfulness is equivalent to powerfulness of both factors. -/
theorem powerful_mul_iff_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    Nat.Powerful (a * b) ↔ Nat.Powerful a ∧ Nat.Powerful b :=
  ⟨fun h => ⟨powerful_of_coprime_mul_left hab h, powerful_of_coprime_mul_right hab h⟩,
    fun h => powerful_mul h.1 h.2⟩

theorem powerful_square (a : ℕ) : Nat.Powerful (a ^ 2) := by
  apply (powerful_iff_prime_sq_divides (a ^ 2)).mpr
  intro p hp hdiv
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hdiv) 2

theorem powerful_cube (a : ℕ) : Nat.Powerful (a ^ 3) := by
  apply (powerful_iff_prime_sq_divides (a ^ 3)).mpr
  intro p hp hdiv
  have hsq : p ^ 2 ∣ a ^ 2 := pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hdiv) 2
  simpa only [pow_succ] using dvd_mul_of_dvd_left hsq a

/-- In a prime factorization, powerfulness says precisely that exponent `1` is absent.
The zero factorization of `0` makes this formulation valid at zero too. -/
theorem powerful_iff_factorization_ne_one (m : ℕ) :
    Nat.Powerful m ↔ ∀ p : ℕ, m.factorization p ≠ 1 := by
  by_cases hm : m = 0
  · subst m
    simp [Nat.Powerful, Nat.Full]
  constructor
  · intro h p hpone
    have hp : Nat.Prime p := by
      by_contra hnp
      have := Nat.factorization_eq_zero_of_not_prime m hnp
      omega
    have hpm : p ∣ m := (hp.dvd_iff_one_le_factorization hm).mpr (by omega)
    have htwo := (hp.pow_dvd_iff_le_factorization hm).mp
      ((powerful_iff_prime_sq_divides m).mp h p hp hpm)
    omega
  · intro h
    apply (powerful_iff_prime_sq_divides m).mpr
    intro p hp hpm
    apply (hp.pow_dvd_iff_le_factorization hm).mpr
    have hpos := hp.factorization_pos_of_dvd hm hpm
    have hne := h p
    omega

/-- A powerful number has a square–cube representation with squarefree cube factor.
At `m = 0`, one may take `a = 0`, `b = 1`. -/
theorem powerful_iff_sq_mul_cube_squarefree (m : ℕ) :
    Nat.Powerful m ↔ ∃ a b : ℕ, Squarefree b ∧ m = a ^ 2 * b ^ 3 := by
  constructor
  · intro hm
    by_cases hz : m = 0
    · exact ⟨0, 1, squarefree_one, by simp [hz]⟩
    obtain ⟨b, c, hb, hc, hrep, hsf⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hz)
    have hbc : b ∣ c := by
      apply (Nat.factorization_prime_le_iff_dvd hsf.ne_zero hc.ne').mp
      intro p hp
      by_cases hpb : p ∣ b
      · have hbf := Nat.factorization_eq_one_of_squarefree hsf hp hpb
        have hpm : p ∣ m := hrep ▸ dvd_mul_of_dvd_right hpb (c ^ 2)
        have htwo := (hp.pow_dvd_iff_le_factorization hz).mp
          ((powerful_iff_prime_sq_divides m).mp hm p hp hpm)
        rw [← hrep, Nat.factorization_mul (pow_ne_zero 2 hc.ne') hsf.ne_zero,
          Nat.factorization_pow] at htwo
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hbf] at htwo
        rw [hbf]
        omega
      · simp [Nat.factorization_eq_zero_of_not_dvd hpb]
    obtain ⟨a, ha⟩ := hbc
    refine ⟨a, b, hsf, ?_⟩
    rw [← hrep, ha]
    ring
  · rintro ⟨a, b, _, rfl⟩
    exact powerful_mul (powerful_square a) (powerful_cube b)

/-- The unrestricted global square–cube characterization, including `0`. -/
theorem powerful_iff_sq_mul_cube (m : ℕ) :
    Nat.Powerful m ↔ ∃ a b : ℕ, m = a ^ 2 * b ^ 3 := by
  constructor
  · intro hm
    obtain ⟨a, b, _, hab⟩ := (powerful_iff_sq_mul_cube_squarefree m).mp hm
    exact ⟨a, b, hab⟩
  · rintro ⟨a, b, rfl⟩
    exact powerful_mul (powerful_square a) (powerful_cube b)

/-- Positivity of the canonical factors for a positive powerful number. -/
theorem powerful_iff_positive_sq_mul_cube_squarefree {m : ℕ} (hm : 0 < m) :
    Nat.Powerful m ↔
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree b ∧ m = a ^ 2 * b ^ 3 := by
  constructor
  · intro h
    obtain ⟨a, b, hb, hab⟩ := (powerful_iff_sq_mul_cube_squarefree m).mp h
    have ha : a ≠ 0 := by
      intro hz
      simp [hz] at hab
      omega
    exact ⟨a, b, Nat.pos_of_ne_zero ha, Nat.pos_of_ne_zero hb.ne_zero, hb, hab⟩
  · rintro ⟨a, b, _, _, _, hab⟩
    exact (powerful_iff_sq_mul_cube m).mpr ⟨a, b, hab⟩

/-- The square–cube form with squarefree cube factor is unique away from zero.
No coprimality of the square and cube factors is asserted or needed. -/
theorem sq_mul_cube_squarefree_unique {m a b c d : ℕ} (hm : m ≠ 0)
    (hb : Squarefree b) (hd : Squarefree d)
    (hab : m = a ^ 2 * b ^ 3) (hcd : m = c ^ 2 * d ^ 3) :
    a = c ∧ b = d := by
  have ha : a ≠ 0 := by
    intro hz
    simp [hz] at hab
    exact hm hab
  have hc : c ≠ 0 := by
    intro hz
    simp [hz] at hcd
    exact hm hcd
  have hexp (p : ℕ) :
      2 * a.factorization p + 3 * b.factorization p =
        2 * c.factorization p + 3 * d.factorization p := by
    have hfac := congrArg (fun x : ℕ => x.factorization p) (hab.symm.trans hcd)
    simpa only [Nat.factorization_mul (pow_ne_zero 2 ha) (pow_ne_zero 3 hb.ne_zero),
      Nat.factorization_mul (pow_ne_zero 2 hc) (pow_ne_zero 3 hd.ne_zero),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] using hfac
  have hbeq (p : ℕ) : b.factorization p = d.factorization p := by
    have := hexp p
    have := hb.natFactorization_le_one p
    have := hd.natFactorization_le_one p
    omega
  constructor
  · apply Nat.eq_of_factorization_eq ha hc
    intro p
    have := hexp p
    have := hbeq p
    omega
  · exact Nat.eq_of_factorization_eq hb.ne_zero hd.ne_zero hbeq

/-- A powerful number cannot be `2` modulo `4`. -/
theorem powerful_mod_four_ne_two {m : ℕ} (hm : Nat.Powerful m) : m % 4 ≠ 2 := by
  intro hmod
  exact (Nat.not_full_of_prime_mod_prime_sq m 1 Nat.prime_two
    (by simpa using hmod)) hm

/-- Any powerful consecutive triple must start at `3` modulo `4`. -/
theorem triple_mod_four {n : ℕ}
    (h : Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) :
    n % 4 = 3 := by
  have h0 := powerful_mod_four_ne_two h.1
  have h1 := powerful_mod_four_ne_two h.2.1
  have h2 := powerful_mod_four_ne_two h.2.2
  omega

/-- In particular, the middle of a powerful triple is at least `4` and divisible by `4`. -/
theorem triple_middle_properties {n : ℕ}
    (h : Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) :
    4 ≤ n + 1 ∧ (n + 1) % 4 = 0 ∧ Even (n + 1) := by
  have hmod := triple_mod_four h
  refine ⟨by omega, by omega, Nat.even_iff.mpr ?_⟩
  omega

/-- An even-centered consecutive triple has pairwise coprime entries. -/
theorem centered_pairwise_coprime {t : ℕ} (ht : 2 ≤ t) (he : Even t) :
    Nat.Coprime (t - 1) t ∧ Nat.Coprime (t - 1) (t + 1) ∧ Nat.Coprime t (t + 1) := by
  have hconsecutive (a : ℕ) : Nat.Coprime a (a + 1) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right a
  have hprev : t - 1 + 1 = t := by omega
  have hodd : Odd (t - 1) := Nat.odd_iff.mpr (by
    have := Nat.even_iff.mp he
    omega)
  refine ⟨hprev ▸ hconsecutive (t - 1), ?_, hconsecutive t⟩
  have heq : t + 1 = 2 + (t - 1) := by omega
  rw [heq, Nat.coprime_add_self_right]
  exact Nat.coprime_two_right.mpr hodd

/-- Consequently, all three entries of any powerful consecutive triple are pairwise coprime. -/
theorem triple_pairwise_coprime {n : ℕ}
    (h : Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) :
    Nat.Coprime n (n + 1) ∧ Nat.Coprime n (n + 2) ∧ Nat.Coprime (n + 1) (n + 2) := by
  have hp := triple_middle_properties h
  have hc := centered_pairwise_coprime (t := n + 1) (by omega) hp.2.2
  simpa only [Nat.add_sub_cancel, Nat.add_assoc] using hc

/-- Powerfulness of a product of three pairwise coprime numbers can be extracted factorwise. -/
theorem powerful_mul_three_iff_of_pairwise_coprime {a b c : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    Nat.Powerful (a * b * c) ↔ Nat.Powerful a ∧ Nat.Powerful b ∧ Nat.Powerful c := by
  rw [powerful_mul_iff_of_coprime (hac.mul_left hbc), powerful_mul_iff_of_coprime hab]
  exact and_assoc

/-- The centered product identity is valid even with natural-number subtraction. -/
theorem cube_sub_self_eq_centered_product (t : ℕ) :
    t ^ 3 - t = (t - 1) * t * (t + 1) := by
  cases t with
  | zero => simp
  | succ u =>
    apply (Nat.sub_eq_iff_eq_add (Nat.le_self_pow (by norm_num : 3 ≠ 0) (u + 1))).mpr
    simp only [Nat.add_sub_cancel]
    ring

/-- The product is strictly positive once the center is at least two. -/
theorem cube_sub_self_pos {t : ℕ} (ht : 2 ≤ t) : 0 < t ^ 3 - t := by
  rw [cube_sub_self_eq_centered_product]
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

/-- For an even center at least two, powerfulness of the cubic product is exactly
powerfulness of all three consecutive entries, not merely of the outside entries. -/
theorem powerful_cube_sub_self_iff {t : ℕ} (ht : 2 ≤ t) (he : Even t) :
    Nat.Powerful (t ^ 3 - t) ↔
      Nat.Powerful (t - 1) ∧ Nat.Powerful t ∧ Nat.Powerful (t + 1) := by
  rw [cube_sub_self_eq_centered_product]
  have hc := centered_pairwise_coprime ht he
  exact powerful_mul_three_iff_of_pairwise_coprime hc.1 hc.2.1 hc.2.2

/-- Pointwise canonical equation for the positive centered product.
Evenness is unnecessary for this representation alone. -/
theorem powerful_cube_sub_self_iff_squarefree_cubic {t : ℕ} (ht : 2 ≤ t) :
    Nat.Powerful (t ^ 3 - t) ↔
      ∃ D S : ℕ, 0 < D ∧ 0 < S ∧ Squarefree D ∧ t ^ 3 - t = D ^ 3 * S ^ 2 := by
  constructor
  · intro h
    obtain ⟨S, D, hS, hD, hsf, heq⟩ :=
      (powerful_iff_positive_sq_mul_cube_squarefree (cube_sub_self_pos ht)).mp h
    exact ⟨D, S, hD, hS, hsf, by simpa only [mul_comm] using heq⟩
  · rintro ⟨D, S, _, _, _, heq⟩
    rw [heq]
    exact powerful_mul (powerful_cube D) (powerful_square S)

/-- Pointwise equivalence of an even-centered powerful triple with the squarefree cubic equation. -/
theorem centered_triple_iff_squarefree_cubic {t : ℕ} (ht : 2 ≤ t) (he : Even t) :
    (Nat.Powerful (t - 1) ∧ Nat.Powerful t ∧ Nat.Powerful (t + 1)) ↔
      ∃ D S : ℕ, 0 < D ∧ 0 < S ∧ Squarefree D ∧ t ^ 3 - t = D ^ 3 * S ^ 2 :=
  (powerful_cube_sub_self_iff ht he).symm.trans
    (powerful_cube_sub_self_iff_squarefree_cubic ht)

/-- The full, unbounded triple-existence problem is equivalent to an even-centered
powerful cubic product. The bound excludes the degenerate products at `0` and `1`. -/
theorem exists_powerful_triple_iff_even_powerful_cubic :
    (∃ n : ℕ, Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) ↔
      ∃ t : ℕ, Even t ∧ 2 ≤ t ∧ Nat.Powerful (t ^ 3 - t) := by
  constructor
  · rintro ⟨n, hn⟩
    have hp := triple_middle_properties hn
    refine ⟨n + 1, hp.2.2, by omega, ?_⟩
    apply (powerful_cube_sub_self_iff (by omega) hp.2.2).mpr
    simpa only [Nat.add_sub_cancel, Nat.add_assoc] using hn
  · rintro ⟨t, he, ht, hprod⟩
    have h := (powerful_cube_sub_self_iff ht he).mp hprod
    refine ⟨t - 1, h.1, ?_, ?_⟩
    · have heq : t - 1 + 1 = t := by omega
      simpa only [heq] using h.2.1
    · have heq : t - 1 + 2 = t + 1 := by omega
      simpa only [heq] using h.2.2

/-- The requested exact global reduction with positive squarefree `D`.
Positivity of `S` follows automatically from `2 ≤ t` and the equation. -/
theorem exists_powerful_triple_iff_squarefree_cubic :
    (∃ n : ℕ, Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) ↔
      ∃ t D S : ℕ, Even t ∧ 2 ≤ t ∧ 0 < D ∧ Squarefree D ∧
        t ^ 3 - t = D ^ 3 * S ^ 2 := by
  rw [exists_powerful_triple_iff_even_powerful_cubic]
  constructor
  · rintro ⟨t, he, ht, hp⟩
    obtain ⟨D, S, hD, _, hsf, heq⟩ :=
      (powerful_cube_sub_self_iff_squarefree_cubic ht).mp hp
    exact ⟨t, D, S, he, ht, hD, hsf, heq⟩
  · rintro ⟨t, D, S, he, ht, _, _, heq⟩
    refine ⟨t, he, ht, ?_⟩
    rw [heq]
    exact powerful_mul (powerful_cube D) (powerful_square S)

/-- The weaker reduction does not require squarefreeness or explicit positivity of the factors. -/
theorem exists_powerful_triple_iff_cubic :
    (∃ n : ℕ, Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) ↔
      ∃ t D S : ℕ, Even t ∧ 2 ≤ t ∧ t ^ 3 - t = D ^ 3 * S ^ 2 := by
  rw [exists_powerful_triple_iff_even_powerful_cubic]
  constructor
  · rintro ⟨t, he, ht, hp⟩
    obtain ⟨S, D, heq⟩ := (powerful_iff_sq_mul_cube (t ^ 3 - t)).mp hp
    exact ⟨t, D, S, he, ht, by simpa only [mul_comm] using heq⟩
  · rintro ⟨t, D, S, he, ht, heq⟩
    refine ⟨t, he, ht, ?_⟩
    rw [heq]
    exact powerful_mul (powerful_cube D) (powerful_square S)

/-- Any even-centered cubic solution already yields the full powerful triple,
a powerful product, pairwise coprime entries, and a center divisible by four.
Squarefreeness need not be assumed for this implication. -/
theorem cubic_solution_structure {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) :
    Nat.Powerful (t ^ 3 - t) ∧
      (Nat.Powerful (t - 1) ∧ Nat.Powerful t ∧ Nat.Powerful (t + 1)) ∧
      (Nat.Coprime (t - 1) t ∧ Nat.Coprime (t - 1) (t + 1) ∧ Nat.Coprime t (t + 1)) ∧
      t % 4 = 0 ∧ 4 ≤ t ∧ 0 < D ∧ 0 < S := by
  have hp : Nat.Powerful (t ^ 3 - t) := by
    rw [heq]
    exact powerful_mul (powerful_cube D) (powerful_square S)
  have htriple := (powerful_cube_sub_self_iff ht he).mp hp
  have hn : Nat.Powerful (t - 1) ∧ Nat.Powerful (t - 1 + 1) ∧
      Nat.Powerful (t - 1 + 2) := by
    have h1 : t - 1 + 1 = t := by omega
    have h2 : t - 1 + 2 = t + 1 := by omega
    simpa only [h1, h2] using htriple
  have hmid := triple_middle_properties hn
  have hD : D ≠ 0 := by
    intro hz
    have hpos := cube_sub_self_pos ht
    simp [hz] at heq
    omega
  have hS : S ≠ 0 := by
    intro hz
    have hpos := cube_sub_self_pos ht
    simp [hz] at heq
    omega
  exact ⟨hp, htriple, centered_pairwise_coprime ht he, by omega, by omega,
    Nat.pos_of_ne_zero hD, Nat.pos_of_ne_zero hS⟩

end Erdos364.PowerfulStructure

-- Exhaustive axiom audit of this helper module.
#print axioms Erdos364.PowerfulStructure.powerful_iff_prime_sq_divides
#print axioms Erdos364.PowerfulStructure.powerful_mul
#print axioms Erdos364.PowerfulStructure.powerful_of_coprime_mul_left
#print axioms Erdos364.PowerfulStructure.powerful_of_coprime_mul_right
#print axioms Erdos364.PowerfulStructure.powerful_mul_iff_of_coprime
#print axioms Erdos364.PowerfulStructure.powerful_square
#print axioms Erdos364.PowerfulStructure.powerful_cube
#print axioms Erdos364.PowerfulStructure.powerful_iff_factorization_ne_one
#print axioms Erdos364.PowerfulStructure.powerful_iff_sq_mul_cube_squarefree
#print axioms Erdos364.PowerfulStructure.powerful_iff_sq_mul_cube
#print axioms Erdos364.PowerfulStructure.powerful_iff_positive_sq_mul_cube_squarefree
#print axioms Erdos364.PowerfulStructure.sq_mul_cube_squarefree_unique
#print axioms Erdos364.PowerfulStructure.powerful_mod_four_ne_two
#print axioms Erdos364.PowerfulStructure.triple_mod_four
#print axioms Erdos364.PowerfulStructure.triple_middle_properties
#print axioms Erdos364.PowerfulStructure.centered_pairwise_coprime
#print axioms Erdos364.PowerfulStructure.triple_pairwise_coprime
#print axioms Erdos364.PowerfulStructure.powerful_mul_three_iff_of_pairwise_coprime
#print axioms Erdos364.PowerfulStructure.cube_sub_self_eq_centered_product
#print axioms Erdos364.PowerfulStructure.cube_sub_self_pos
#print axioms Erdos364.PowerfulStructure.powerful_cube_sub_self_iff
#print axioms Erdos364.PowerfulStructure.powerful_cube_sub_self_iff_squarefree_cubic
#print axioms Erdos364.PowerfulStructure.centered_triple_iff_squarefree_cubic
#print axioms Erdos364.PowerfulStructure.exists_powerful_triple_iff_even_powerful_cubic
#print axioms Erdos364.PowerfulStructure.exists_powerful_triple_iff_squarefree_cubic
#print axioms Erdos364.PowerfulStructure.exists_powerful_triple_iff_cubic
#print axioms Erdos364.PowerfulStructure.cubic_solution_structure
