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
theorem oeis_381159_conjecture_0 :
  ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)
  := by sorry

def good_pairs : List (ℕ × ℕ) := [(2, 17), (3, 17), (5, 23), (7, 19), (11, 13)]

def check_d (d : ℕ) : Bool :=
  good_pairs.any (fun p => d % p.1 ≠ 0 ∧ d % p.2 ≠ 0)

set_option maxRecDepth 100000
lemma check_d_all : ((List.range 2025).map (· + 1) |>.all check_d) = true := by decide

lemma get_pair (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ 2025) : ∃ p ∈ good_pairs, ¬ (p.1 ∣ d) ∧ ¬ (p.2 ∣ d) := by
  have H := check_d_all
  rw [List.all_eq_true] at H
  have H2 := H d (by
    rw [List.mem_map]
    refine ⟨d - 1, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · omega)
  unfold check_d at H2
  rw [List.any_eq_true] at H2
  rcases H2 with ⟨p, hp1, hp2⟩
  use p, hp1
  simp only [decide_eq_true_eq, ne_eq] at hp2
  constructor
  · intro hd
    apply hp2.1
    exact Nat.mod_eq_zero_of_dvd hd
  · intro hd
    apply hp2.2
    exact Nat.mod_eq_zero_of_dvd hd

lemma good_pairs_props : ∀ p ∈ good_pairs,
  p.1.Prime ∧ p.2.Prime ∧ p.1 * p.2 ≤ 150 ∧ p.1 % 10 ≠ p.2 % 10 ∧ p.1 ≠ p.2 := by
  decide

lemma exists_mod_zero (a d N : ℕ) (hN : 0 < N) (h_coprime : Nat.Coprime d N) :
  ∃ i < N, (a + i * d) % N = 0 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  let u := ZMod.unitOfCoprime d h_coprime
  let i_zmod : ZMod N := - (a : ZMod N) * (u⁻¹ : ZMod N)
  use i_zmod.val
  constructor
  · exact ZMod.val_lt i_zmod
  · have h1 : (a : ZMod N) + i_zmod * d = 0 := by
      dsimp [i_zmod]
      rw [mul_assoc]
      have h_mul : (u⁻¹ : ZMod N) * d = 1 := Units.inv_mul u
      rw [h_mul, mul_one, add_neg_cancel]
    have h2 : ((a + i_zmod.val * d : ℕ) : ZMod N) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact h1
    apply Nat.mod_eq_zero_of_dvd
    exact (CharP.cast_eq_zero_iff (ZMod N) N (a + i_zmod.val * d)).mp h2

lemma not_A381159_condition {n q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q % 10 ≠ r % 10)
  (hqn : q ∣ n) (hrn : r ∣ n) (hn : 2 ≤ n) : ¬ A381159_condition n := by
  intro h
  unfold A381159_condition at h
  have hn_ne : n ≠ 0 := by omega
  have h1 : q % 10 ∈ n.primeFactors.image (fun p => p % 10) := by
    rw [Finset.mem_image]
    refine ⟨q, ?_, rfl⟩
    rw [Nat.mem_primeFactors]
    exact ⟨hq, hqn, hn_ne⟩
  have h2 : r % 10 ∈ n.primeFactors.image (fun p => p % 10) := by
    rw [Finset.mem_image]
    refine ⟨r, ?_, rfl⟩
    rw [Nat.mem_primeFactors]
    exact ⟨hr, hrn, hn_ne⟩
  have h3 : q % 10 = r % 10 := Finset.card_le_one.mp h _ h1 _ h2
  exact hqr h3

theorem oeis_381159_conjecture_0.disproof : ¬ (type_of% @oeis_381159_conjecture_0) := by
  intro ⟨a, d, ha, hd1, hd2, H⟩
  rcases get_pair d hd1 hd2 with ⟨⟨q, r⟩, hp, hdq, hdr⟩
  rcases good_pairs_props (q, r) hp with ⟨hq, hr, hqr_le, hqr_neq, hqr_distinct⟩
  have hd_coprime_q : Nat.Coprime q d := (Nat.Prime.coprime_iff_not_dvd hq).mpr hdq
  have hd_coprime_r : Nat.Coprime r d := (Nat.Prime.coprime_iff_not_dvd hr).mpr hdr
  have hd_coprime_N : Nat.Coprime d (q * r) := Nat.Coprime.mul_right hd_coprime_q.symm hd_coprime_r.symm
  have hN_pos : 0 < q * r := mul_pos hq.pos hr.pos
  rcases exists_mod_zero a d (q * r) hN_pos hd_coprime_N with ⟨i, hi, hmod⟩
  have hi_le : i < 150 := by linarith
  have h_cond := H ⟨i, hi_le⟩
  have h_dvd : q * r ∣ a + i * d := Nat.dvd_of_mod_eq_zero hmod
  have hq_dvd : q ∣ a + i * d := dvd_trans ⟨r, rfl⟩ h_dvd
  have hr_dvd : r ∣ a + i * d := dvd_trans ⟨q, mul_comm q r⟩ h_dvd
  have hn_ge : 2 ≤ a + i * d := by omega
  exact not_A381159_condition hq hr hqr_neq hq_dvd hr_dvd hn_ge h_cond

