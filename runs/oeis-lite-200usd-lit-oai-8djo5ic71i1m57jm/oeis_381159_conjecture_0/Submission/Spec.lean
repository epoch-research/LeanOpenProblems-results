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
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/
lemma exists_i_dvd_of_coprime (a d m : ℕ) [NeZero m]
    (hc : d.Coprime m) (hm : m ≤ 150) :
    ∃ i < 150, m ∣ a + i * d := by
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime d hc
  let x : ZMod m := - (a : ZMod m) * ↑u⁻¹
  refine ⟨x.val, lt_of_lt_of_le (ZMod.val_lt x) hm, ?_⟩
  rw [← Int.natCast_dvd_natCast]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_cast
  calc
    ((a + x.val * d : ℕ) : ZMod m) = (a : ZMod m) + (x.val : ZMod m) * (d : ZMod m) := by
      norm_num
    _ = (a : ZMod m) + x * (d : ZMod m) := by
      simp [ZMod.natCast_val]
    _ = (a : ZMod m) + (- (a : ZMod m) * ↑u⁻¹) * (u : ZMod m) := by
      rfl
    _ = 0 := by
      rw [mul_assoc, Units.inv_mul]
      simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma exists_bad_pair_fin : ∀ (d : Fin 2026), 1 ≤ d.val →
    ∃ p q : Fin 18, Nat.Prime p.val ∧ Nat.Prime q.val ∧ p.val % 10 ≠ q.val % 10 ∧
      p.val * q.val ≤ 150 ∧ ¬ p.val ∣ d.val ∧ ¬ q.val ∣ d.val := by
  decide

lemma exists_bad_pair (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2025) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % 10 ≠ q % 10 ∧
      p * q ≤ 150 ∧ ¬ p ∣ d ∧ ¬ q ∣ d := by
  have hdlt : d < 2026 := by omega
  rcases exists_bad_pair_fin ⟨d, hdlt⟩ hd1 with ⟨p, q, hp, hq, hmod, hmul, hpd, hqd⟩
  exact ⟨p.val, q.val, hp, hq, hmod, hmul, hpd, hqd⟩

lemma not_A381159_condition_of_two_prime_dvd {n p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hmod : p % 10 ≠ q % 10)
    (hn : n ≠ 0) (hpdvd : p ∣ n) (hqdvd : q ∣ n) :
    ¬ A381159_condition n := by
  intro h
  have hp_mem : p ∈ n.primeFactors := hp.mem_primeFactors hpdvd hn
  have hq_mem : q ∈ n.primeFactors := hq.mem_primeFactors hqdvd hn
  have hp_img : p % 10 ∈ n.primeFactors.image (fun p => p % 10) := by
    exact Finset.mem_image.mpr ⟨p, hp_mem, rfl⟩
  have hq_img : q % 10 ∈ n.primeFactors.image (fun p => p % 10) := by
    exact Finset.mem_image.mpr ⟨q, hq_mem, rfl⟩
  exact hmod ((Finset.card_le_one.mp h) (p % 10) hp_img (q % 10) hq_img)

theorem oeis_381159_conjecture_0.disproof :
  ¬ (∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)) := by
  rintro ⟨a, d, ha, hd1, hd2, hall⟩
  rcases exists_bad_pair d hd1 hd2 with ⟨p, q, hp, hq, hmod, hmul, hpd, hqd⟩
  have hdp : d.Coprime p := ((hp.coprime_iff_not_dvd).mpr hpd).symm
  have hdq : d.Coprime q := ((hq.coprime_iff_not_dvd).mpr hqd).symm
  have hcop : d.Coprime (p * q) := hdp.mul_right hdq
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  rcases exists_i_dvd_of_coprime a d (p * q) hcop hmul with ⟨i, hi, hidvd⟩
  have hn_pos : 0 < a + i * d := by omega
  have hn_ne : a + i * d ≠ 0 := Nat.ne_of_gt hn_pos
  have hp_dvd : p ∣ a + i * d := (dvd_mul_right p q).trans hidvd
  have hq_dvd : q ∣ a + i * d := (dvd_mul_left q p).trans (by simpa [mul_comm] using hidvd)
  have hbad := not_A381159_condition_of_two_prime_dvd hp hq hmod hn_ne hp_dvd hq_dvd
  exact hbad (hall ⟨i, hi⟩)
