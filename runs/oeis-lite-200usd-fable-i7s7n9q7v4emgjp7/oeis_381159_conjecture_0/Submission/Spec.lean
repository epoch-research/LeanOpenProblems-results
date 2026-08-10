import FormalConjectures.Util.ProblemImports

open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end
with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

The answer to the question is in fact NO.  Key observation: if `p` and `q` are primes with
different last digits, neither of which divides the common difference `d`, and `p * q ≤ 150`,
then among the 150 terms of the progression some term is divisible by `p * q`
(the indices cover all residues modulo `p * q`), and this term is not lopsided.
Hence for each such pair `(p, q)` we must have `p ∣ d` or `q ∣ d`.  Running through
the pairs `(2, q)`, `(3, q)`, `(5, q)`, `(7, q)`, `(11, 13)` forces
`2 * 3 * 5 * 7 * 11 = 2310 ≤ d` or `2 * 3 * 5 * 7 * 13 = 2730 ≤ d`, both exceeding `2025`.
-/
theorem oeis_381159_conjecture_0.disproof :
  ¬(∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)) := by
  rintro ⟨a, d, ha, hd1, hd2, hall⟩
  -- Key step: for primes `p ≠ q` with different last digits and `p * q ≤ 150`,
  -- either `p ∣ d` or `q ∣ d`.
  have key : ∀ p q : ℕ, p.Prime → q.Prime → p * q ≤ 150 → p % 10 ≠ q % 10 →
      p ∣ d ∨ q ∣ d := by
    intro p q hp hq hle hdig
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpd, hqd⟩ := hcon
    have hcop : Nat.Coprime d (p * q) :=
      Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hpd).symm
        (hq.coprime_iff_not_dvd.mpr hqd).symm
    have hm0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
    haveI : NeZero (p * q) := ⟨hm0.ne'⟩
    -- Solve `a + x * d ≡ 0 (mod p * q)` using the inverse of `d` modulo `p * q`.
    obtain ⟨u, hu⟩ : ∃ u : (ZMod (p * q))ˣ, (u : ZMod (p * q)) = (d : ZMod (p * q)) :=
      ⟨ZMod.unitOfCoprime d hcop, ZMod.coe_unitOfCoprime d hcop⟩
    set x : ZMod (p * q) := (-(a : ZMod (p * q))) * ↑u⁻¹ with hxdef
    have hi_lt : x.val < 150 := lt_of_lt_of_le (ZMod.val_lt x) hle
    have hxd : x * (d : ZMod (p * q)) = -(a : ZMod (p * q)) := by
      rw [hxdef, ← hu, mul_assoc, u.inv_mul, mul_one]
    have hdvd : p * q ∣ a + x.val * d := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, hxd]
      ring
    -- The corresponding term of the progression is divisible by both `p` and `q`,
    -- so its prime factors do not all end in the same digit.
    have hcond : Finset.card ((a + x.val * d).primeFactors.image (fun r => r % 10)) ≤ 1 :=
      hall ⟨x.val, hi_lt⟩
    have hne0 : a + x.val * d ≠ 0 :=
      (Nat.lt_of_lt_of_le (Nat.zero_lt_two) (ha.trans (Nat.le_add_right a _))).ne'
    have hpn : p ∣ a + x.val * d := dvd_trans (dvd_mul_right p q) hdvd
    have hqn : q ∣ a + x.val * d := dvd_trans (dvd_mul_left q p) hdvd
    have hpmem : p % 10 ∈ (a + x.val * d).primeFactors.image (fun r => r % 10) :=
      Finset.mem_image_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hpn, hne0⟩)
    have hqmem : q % 10 ∈ (a + x.val * d).primeFactors.image (fun r => r % 10) :=
      Finset.mem_image_of_mem _ (Nat.mem_primeFactors.mpr ⟨hq, hqn, hne0⟩)
    have h2card : 1 < Finset.card ((a + x.val * d).primeFactors.image (fun r => r % 10)) :=
      Finset.one_lt_card.mpr ⟨p % 10, hpmem, q % 10, hqmem, hdig⟩
    exact Nat.lt_irrefl 1 (Nat.lt_of_lt_of_le h2card hcond)
  -- Primality facts for the primes we will use.
  have hP2 : Nat.Prime 2 := Nat.prime_two
  have hP3 : Nat.Prime 3 := Nat.prime_three
  have hP5 : Nat.Prime 5 := Nat.prime_five
  have hP7 : Nat.Prime 7 := Nat.prime_seven
  have hP11 : Nat.Prime 11 := Nat.prime_eleven
  have hP13 : Nat.Prime 13 := by decide
  have hP17 : Nat.Prime 17 := by decide
  -- Instantiate the key step at the relevant pairs of primes.
  have h23 := key 2 3 hP2 hP3 (by decide) (by decide)
  have h25 := key 2 5 hP2 hP5 (by decide) (by decide)
  have h27 := key 2 7 hP2 hP7 (by decide) (by decide)
  have h211 := key 2 11 hP2 hP11 (by decide) (by decide)
  have h213 := key 2 13 hP2 hP13 (by decide) (by decide)
  have h35 := key 3 5 hP3 hP5 (by decide) (by decide)
  have h37 := key 3 7 hP3 hP7 (by decide) (by decide)
  have h311 := key 3 11 hP3 hP11 (by decide) (by decide)
  have h317 := key 3 17 hP3 hP17 (by decide) (by decide)
  have h57 := key 5 7 hP5 hP7 (by decide) (by decide)
  have h511 := key 5 11 hP5 hP11 (by decide) (by decide)
  have h513 := key 5 13 hP5 hP13 (by decide) (by decide)
  have h711 := key 7 11 hP7 hP11 (by decide) (by decide)
  have h713 := key 7 13 hP7 hP13 (by decide) (by decide)
  have h1113 := key 11 13 hP11 hP13 (by decide) (by decide)
  -- Now derive `2 ∣ d`, `3 ∣ d`, `5 ∣ d`, `7 ∣ d` and `11 ∣ d ∨ 13 ∣ d`,
  -- which forces `d ≥ 2310 > 2025`, a contradiction.
  have hd0 : 0 < d := hd1
  have mul_dvd : ∀ m k : ℕ, Nat.Coprime m k → m ∣ d → k ∣ d → m * k ∣ d :=
    fun m k h hm hk => h.mul_dvd_of_dvd_of_dvd hm hk
  have too_big : ∀ m : ℕ, 2026 ≤ m → m ∣ d → False := fun m hm hdvd =>
    Nat.lt_irrefl 2025 (Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (by decide : (2025 : ℕ) < 2026) hm)
      ((Nat.le_of_dvd hd0 hdvd).trans hd2))
  have h2 : 2 ∣ d := by
    by_contra h2
    have h3 := h23.resolve_left h2
    have h5 := h25.resolve_left h2
    have h7 := h27.resolve_left h2
    have h11 := h211.resolve_left h2
    have h13 := h213.resolve_left h2
    have h15 : 15 ∣ d := mul_dvd 3 5 (by decide) h3 h5
    have h105 : 105 ∣ d := mul_dvd 15 7 (by decide) h15 h7
    have h1155 : 1155 ∣ d := mul_dvd 105 11 (by decide) h105 h11
    have h15015 : 15015 ∣ d := mul_dvd 1155 13 (by decide) h1155 h13
    exact too_big 15015 (by decide) h15015
  have h3 : 3 ∣ d := by
    by_contra h3
    have h5 := h35.resolve_left h3
    have h7 := h37.resolve_left h3
    have h11 := h311.resolve_left h3
    have h17 := h317.resolve_left h3
    have h10 : 10 ∣ d := mul_dvd 2 5 (by decide) h2 h5
    have h70 : 70 ∣ d := mul_dvd 10 7 (by decide) h10 h7
    have h770 : 770 ∣ d := mul_dvd 70 11 (by decide) h70 h11
    have h13090 : 13090 ∣ d := mul_dvd 770 17 (by decide) h770 h17
    exact too_big 13090 (by decide) h13090
  have h5 : 5 ∣ d := by
    by_contra h5
    have h7 := h57.resolve_left h5
    have h11 := h511.resolve_left h5
    have h13 := h513.resolve_left h5
    have h6 : 6 ∣ d := mul_dvd 2 3 (by decide) h2 h3
    have h42 : 42 ∣ d := mul_dvd 6 7 (by decide) h6 h7
    have h462 : 462 ∣ d := mul_dvd 42 11 (by decide) h42 h11
    have h6006 : 6006 ∣ d := mul_dvd 462 13 (by decide) h462 h13
    exact too_big 6006 (by decide) h6006
  have h7 : 7 ∣ d := by
    by_contra h7
    have h11 := h711.resolve_left h7
    have h13 := h713.resolve_left h7
    have h6 : 6 ∣ d := mul_dvd 2 3 (by decide) h2 h3
    have h30 : 30 ∣ d := mul_dvd 6 5 (by decide) h6 h5
    have h330 : 330 ∣ d := mul_dvd 30 11 (by decide) h30 h11
    have h4290 : 4290 ∣ d := mul_dvd 330 13 (by decide) h330 h13
    exact too_big 4290 (by decide) h4290
  have h6 : 6 ∣ d := mul_dvd 2 3 (by decide) h2 h3
  have h30 : 30 ∣ d := mul_dvd 6 5 (by decide) h6 h5
  have h210 : 210 ∣ d := mul_dvd 30 7 (by decide) h30 h7
  rcases h1113 with h11 | h13
  · exact too_big 2310 (by decide) (mul_dvd 210 11 (by decide) h210 h11)
  · exact too_big 2730 (by decide) (mul_dvd 210 13 (by decide) h210 h13)
