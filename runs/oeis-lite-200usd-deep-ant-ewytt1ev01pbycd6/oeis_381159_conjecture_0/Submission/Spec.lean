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

/-!
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

The condition for "lopsided" for n > 1 is exactly A381159_condition n.
The original conjecture asserted the positive answer; we show it is false.
-/
/-
The answer to the olympiad question is in fact **NO**: there is no such arithmetic
progression when the common difference is bounded by `2025`.

The key structural facts: primes other than `2` and `5` end in `1, 3, 7, 9`, so a
"lopsided" number cannot be divisible by two primes with different last digits.  If all
`150` terms `a + i * d` (`0 ≤ i ≤ 149`) were lopsided, then for every pair of primes
`p ≠ q` with different last digits and `p * q ≤ 150`, at least one of `p, q` must divide
`d` (otherwise the Chinese Remainder Theorem produces a term divisible by both `p` and
`q`, which then is not lopsided).  Covering all such pairs forces `2 · 3 · 5 · 7 · 11 =
2310` to divide `d`, contradicting `d ≤ 2025`.  Concretely, for any `d ≤ 2025` one can
always exhibit an uncovered pair, yielding a non-lopsided term.

We therefore prove the negation of the conjecture below.
-/

/-- If `p, q` are primes not dividing `d` with `p * q ≤ 150`, then some term `a + i * d`
with `i < 150` is divisible by `p * q`. -/
private theorem A381159_idx {p q a d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpd : ¬ p ∣ d) (hqd : ¬ q ∣ d) (hbound : p * q ≤ 150) :
    ∃ i : Fin 150, (p * q) ∣ (a + i.val * d) := by
  set m := p * q with hm
  have hmpos : 0 < m := by
    have := hp.pos; have := hq.pos; positivity
  have : NeZero m := ⟨by omega⟩
  have hcp : Nat.Coprime d p := ((hp.coprime_iff_not_dvd).mpr hpd).symm
  have hcq : Nat.Coprime d q := ((hq.coprime_iff_not_dvd).mpr hqd).symm
  have hcop : Nat.Coprime d m := hcp.mul_right hcq
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime d hcop
  have hu : (↑u : ZMod m) = (d : ZMod m) := ZMod.coe_unitOfCoprime d hcop
  have hunit : (↑u⁻¹ : ZMod m) * (d : ZMod m) = 1 := by
    rw [← hu]; exact_mod_cast (Units.inv_mul u)
  set x : ZMod m := (-(a : ZMod m)) * (↑u⁻¹) with hx
  refine ⟨⟨x.val, ?_⟩, ?_⟩
  · have := ZMod.val_lt x
    omega
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_rightInverse x, hx, mul_assoc, hunit]
    ring

/-- A number divisible by two primes with different last digits is not lopsided. -/
private theorem A381159_notlop {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : p ∣ N) (hqN : q ∣ N) (hN : N ≠ 0) (hne : p % 10 ≠ q % 10) :
    ¬ A381159_condition N := by
  intro h
  unfold A381159_condition at h
  have hpm : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, hN⟩
  have hqm : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, hN⟩
  have hsub : ({p % 10, q % 10} : Finset ℕ) ⊆ N.primeFactors.image (fun p => p % 10) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_image_of_mem _ hpm
    · exact Finset.mem_image_of_mem _ hqm
  have hcard : ({p % 10, q % 10} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have : 2 ≤ (N.primeFactors.image (fun p => p % 10)).card := by
    rw [← hcard]; exact Finset.card_le_card hsub
  omega

private theorem A381159_dvd_false {d P : ℕ} (hd1 : 1 ≤ d) (hd : d ≤ 2025)
    (hP : 2025 < P) (h : P ∣ d) : False := by
  have := Nat.le_of_dvd (by omega) h; omega

/-- Given an uncovered cross-class prime pair, one term of the progression is not
lopsided, contradicting the assumption that all terms are lopsided. -/
private theorem A381159_conflict {a d p q : ℕ} (ha : 2 ≤ a) (hp : p.Prime) (hq : q.Prime)
    (hpd : ¬ p ∣ d) (hqd : ¬ q ∣ d) (hbound : p * q ≤ 150) (hne : p % 10 ≠ q % 10)
    (hall : ∀ i : Fin 150, A381159_condition (a + i.val * d)) : False := by
  obtain ⟨i, hi⟩ := A381159_idx (a := a) (d := d) hp hq hpd hqd hbound
  have hN : a + i.val * d ≠ 0 := by omega
  have hpN : p ∣ a + i.val * d := (dvd_mul_right p q).trans hi
  have hqN : q ∣ a + i.val * d := (dvd_mul_left q p).trans hi
  exact A381159_notlop hp hq hpN hqN hN hne (hall i)

/--
Disproof of `oeis_381159_conjecture_0`: there is *no* increasing arithmetic progression
of `150` lopsided numbers with common difference at most `2025`.  (This is the correct
answer to the olympiad problem; the common difference would need to be divisible by
`2 · 3 · 5 · 7 · 11 = 2310 > 2025`.)
-/
theorem oeis_381159_conjecture_0.disproof :
    ¬ (∃ (a d : ℕ),
        2 ≤ a ∧
        1 ≤ d ∧
        d ≤ 2025 ∧
        ∀ (i : Fin 150), A381159_condition (a + i.val * d)) := by
  rintro ⟨a, d, ha, hd1, hd, hall⟩
  by_cases h2 : (2:ℕ) ∣ d
  · by_cases h5 : (5:ℕ) ∣ d
    · -- 10 | d
      by_cases h3 : (3:ℕ) ∣ d
      · by_cases h7 : (7:ℕ) ∣ d
        · -- 2,3,5,7 | d ; hence 11 ∤ d and 13 ∤ d ; use pair (11,13)
          have h11 : ¬ (11:ℕ) ∣ d := by
            intro h11
            have c1 : (2*3:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
            have c2 : (2*3*5:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c1 h5
            have c3 : (2*3*5*7:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c2 h7
            have c4 : (2*3*5*7*11:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c3 h11
            exact A381159_dvd_false hd1 hd (by norm_num) c4
          have h13 : ¬ (13:ℕ) ∣ d := by
            intro h13
            have c1 : (2*3:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
            have c2 : (2*3*5:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c1 h5
            have c3 : (2*3*5*7:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c2 h7
            have c4 : (2*3*5*7*13:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c3 h13
            exact A381159_dvd_false hd1 hd (by norm_num) c4
          exact A381159_conflict ha (by norm_num) (by norm_num) h11 h13 (by norm_num) (by norm_num) hall
        · -- 7 ∤ d
          by_cases h11 : (11:ℕ) ∣ d
          · have h13 : ¬ (13:ℕ) ∣ d := by
              intro h13
              have c1 : (2*3:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
              have c2 : (2*3*5:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c1 h5
              have c3 : (2*3*5*11:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c2 h11
              have c4 : (2*3*5*11*13:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c3 h13
              exact A381159_dvd_false hd1 hd (by norm_num) c4
            exact A381159_conflict ha (by norm_num) (by norm_num) h7 h13 (by norm_num) (by norm_num) hall
          · exact A381159_conflict ha (by norm_num) (by norm_num) h7 h11 (by norm_num) (by norm_num) hall
      · -- 3 ∤ d
        by_cases h7 : (7:ℕ) ∣ d
        · by_cases h11 : (11:ℕ) ∣ d
          · have h17 : ¬ (17:ℕ) ∣ d := by
              intro h17
              have c1 : (2*5:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h5
              have c2 : (2*5*7:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c1 h7
              have c3 : (2*5*7*11:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c2 h11
              have c4 : (2*5*7*11*17:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c3 h17
              exact A381159_dvd_false hd1 hd (by norm_num) c4
            exact A381159_conflict ha (by norm_num) (by norm_num) h3 h17 (by norm_num) (by norm_num) hall
          · exact A381159_conflict ha (by norm_num) (by norm_num) h3 h11 (by norm_num) (by norm_num) hall
        · exact A381159_conflict ha (by norm_num) (by norm_num) h3 h7 (by norm_num) (by norm_num) hall
    · -- 5 ∤ d
      by_cases h3 : (3:ℕ) ∣ d
      · by_cases h7 : (7:ℕ) ∣ d
        · by_cases h11 : (11:ℕ) ∣ d
          · have h13 : ¬ (13:ℕ) ∣ d := by
              intro h13
              have c1 : (3*7:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h7
              have c2 : (3*7*11:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c1 h11
              have c3 : (3*7*11*13:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c2 h13
              exact A381159_dvd_false hd1 hd (by norm_num) c3
            exact A381159_conflict ha (by norm_num) (by norm_num) h5 h13 (by norm_num) (by norm_num) hall
          · exact A381159_conflict ha (by norm_num) (by norm_num) h5 h11 (by norm_num) (by norm_num) hall
        · exact A381159_conflict ha (by norm_num) (by norm_num) h5 h7 (by norm_num) (by norm_num) hall
      · exact A381159_conflict ha (by norm_num) (by norm_num) h5 h3 (by norm_num) (by norm_num) hall
  · -- 2 ∤ d
    by_cases h3 : (3:ℕ) ∣ d
    · by_cases h7 : (7:ℕ) ∣ d
      · by_cases h11 : (11:ℕ) ∣ d
        · have h13 : ¬ (13:ℕ) ∣ d := by
            intro h13
            have c1 : (3*7:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h7
            have c2 : (3*7*11:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c1 h11
            have c3 : (3*7*11*13:ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) c2 h13
            exact A381159_dvd_false hd1 hd (by norm_num) c3
          exact A381159_conflict ha (by norm_num) (by norm_num) h2 h13 (by norm_num) (by norm_num) hall
        · exact A381159_conflict ha (by norm_num) (by norm_num) h2 h11 (by norm_num) (by norm_num) hall
      · exact A381159_conflict ha (by norm_num) (by norm_num) h2 h7 (by norm_num) (by norm_num) hall
    · exact A381159_conflict ha (by norm_num) (by norm_num) h2 h3 (by norm_num) (by norm_num) hall
