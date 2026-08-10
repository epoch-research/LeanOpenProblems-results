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
private lemma not_dvd_of_pos_lt {m d : ℕ} (hd0 : 0 < d) (hdm : d < m) : ¬ m ∣ d := by
  rintro ⟨k, rfl⟩
  cases k with
  | zero => simp at hd0
  | succ k =>
      exact (not_lt_of_ge (Nat.le_mul_of_pos_right m (Nat.succ_pos k))) hdm


private lemma impossible_cover_with17 {d : ℕ} (hd0 : 0 < d) (hd : d ≤ 2025)
    (h17 : 17 ∣ d) (h523 : 5 ∣ d ∨ 23 ∣ d) (h719 : 7 ∣ d ∨ 19 ∣ d)
    (h1113 : 11 ∣ d ∨ 13 ∣ d) : False := by
  rcases h523 with hu | hu <;> rcases h719 with hv | hv <;> rcases h1113 with hw | hw
  all_goals
    have hdvd := Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd h17 hu) hv) hw
    norm_num at hdvd
    exact (not_dvd_of_pos_lt hd0 (lt_of_le_of_lt hd (by norm_num))) hdvd

private lemma impossible_cover_without17 {d : ℕ} (hd0 : 0 < d) (hd : d ≤ 2025)
    (h2 : 2 ∣ d) (h3 : 3 ∣ d) (h523 : 5 ∣ d ∨ 23 ∣ d) (h719 : 7 ∣ d ∨ 19 ∣ d)
    (h1113 : 11 ∣ d ∨ 13 ∣ d) : False := by
  rcases h523 with hu | hu <;> rcases h719 with hv | hv <;> rcases h1113 with hw | hw
  all_goals
    have hdvd := Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd h2 h3) hu) hv) hw
    norm_num at hdvd
    exact (not_dvd_of_pos_lt hd0 (lt_of_le_of_lt hd (by norm_num))) hdvd

private theorem pair_disj (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 2025) :
    (¬ 2 ∣ d ∧ ¬ 17 ∣ d) ∨ (¬ 3 ∣ d ∧ ¬ 17 ∣ d) ∨
    (¬ 5 ∣ d ∧ ¬ 23 ∣ d) ∨ (¬ 7 ∣ d ∧ ¬ 19 ∣ d) ∨
    (¬ 11 ∣ d ∧ ¬ 13 ∣ d) := by
  by_contra h
  push_neg at h
  rcases h with ⟨h217, h317, h523, h719, h1113⟩
  by_cases h17 : 17 ∣ d
  · exact impossible_cover_with17 hd0 hd h17
      (by by_cases h5 : 5 ∣ d; exact Or.inl h5; exact Or.inr (h523 h5))
      (by by_cases h7 : 7 ∣ d; exact Or.inl h7; exact Or.inr (h719 h7))
      (by by_cases h11 : 11 ∣ d; exact Or.inl h11; exact Or.inr (h1113 h11))
  · have h2 : 2 ∣ d := by
      by_contra h2
      exact h17 (h217 h2)
    have h3 : 3 ∣ d := by
      by_contra h3
      exact h17 (h317 h3)
    exact impossible_cover_without17 hd0 hd h2 h3
      (by by_cases h5 : 5 ∣ d; exact Or.inl h5; exact Or.inr (h523 h5))
      (by by_cases h7 : 7 ∣ d; exact Or.inl h7; exact Or.inr (h719 h7))
      (by by_cases h11 : 11 ∣ d; exact Or.inl h11; exact Or.inr (h1113 h11))

private theorem exists_pair_not_dvd (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 2025) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 10 ≠ q % 10 ∧ p * q ≤ 150 ∧
      ¬ p ∣ d ∧ ¬ q ∣ d := by
  rcases pair_disj d hd0 hd with h | h | h | h | h
  · exact ⟨2, 17, by norm_num, by norm_num, by norm_num, by norm_num, h⟩
  · exact ⟨3, 17, by norm_num, by norm_num, by norm_num, by norm_num, h⟩
  · exact ⟨5, 23, by norm_num, by norm_num, by norm_num, by norm_num, h⟩
  · exact ⟨7, 19, by norm_num, by norm_num, by norm_num, by norm_num, h⟩
  · exact ⟨11, 13, by norm_num, by norm_num, by norm_num, by norm_num, h⟩

private lemma exists_i_mod_zero {a d m : ℕ} (hm1 : 1 < m) (hdm : d.Coprime m) :
    ∃ i < m, (a % m + i*d) % m = 0 := by
  have hmpos : 0 < m := Nat.lt_trans zero_lt_one hm1
  rcases Nat.exists_mul_mod_eq_one_of_coprime hdm hm1 with ⟨t, _htlt, ht⟩
  let target := (m - a % m) % m
  let i := (target * t) % m
  refine ⟨i, Nat.mod_lt _ hmpos, ?_⟩
  have htarget_zero : (a % m + target) % m = 0 := by
    have ha_lt : a % m < m := Nat.mod_lt a hmpos
    have hle : a % m ≤ m := Nat.le_of_lt ha_lt
    have htarget_cong : a % m + target ≡ 0 [MOD m] := by
      dsimp [target]
      calc
        a % m + (m - a % m) % m ≡ a % m + (m - a % m) [MOD m] :=
          Nat.ModEq.add_left (a % m) (Nat.mod_modEq _ _)
        _ = m := by rw [Nat.add_sub_of_le hle]
        _ ≡ 0 [MOD m] := by rw [Nat.ModEq]; simp
    rw [Nat.ModEq] at htarget_cong
    simpa using htarget_cong
  have htmod : d * t ≡ 1 [MOD m] := by
    rw [Nat.ModEq]
    rw [ht]
    exact (Nat.mod_eq_of_lt hm1).symm
  have hi_cong : i * d ≡ target [MOD m] := by
    dsimp [i]
    have h1 : (target * t) % m ≡ target * t [MOD m] := Nat.mod_modEq _ _
    have h2 : ((target * t) % m) * d ≡ (target * t) * d [MOD m] :=
      Nat.ModEq.mul_right d h1
    have h3 : (target * t) * d ≡ target [MOD m] := by
      calc
        (target * t) * d = target * (d * t) := by ac_rfl
        _ ≡ target * 1 [MOD m] := Nat.ModEq.mul_left target htmod
        _ = target := by simp
    exact h2.trans h3
  have hadd : a % m + i*d ≡ a % m + target [MOD m] := Nat.ModEq.add_left (a % m) hi_cong
  rw [Nat.ModEq] at hadd
  rw [htarget_zero] at hadd
  exact hadd

private lemma dvd_of_mod_aux {a m i d : ℕ} (h : (a % m + i*d) % m = 0) :
    m ∣ a + i*d := by
  rw [Nat.dvd_iff_mod_eq_zero]
  simpa [Nat.mod_add_mod] using h

private lemma not_condition_of_two_primes {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpdvd : p ∣ n) (hqdvd : q ∣ n) (hn : n ≠ 0) (hdigits : p % 10 ≠ q % 10) :
    ¬ A381159_condition n := by
  intro hcond
  rw [A381159_condition] at hcond
  have hp_mem : p ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hp, hpdvd, hn⟩
  have hq_mem : q ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hq, hqdvd, hn⟩
  have hp_img : p % 10 ∈ n.primeFactors.image (fun p => p % 10) := by
    exact Finset.mem_image.mpr ⟨p, hp_mem, rfl⟩
  have hq_img : q % 10 ∈ n.primeFactors.image (fun p => p % 10) := by
    exact Finset.mem_image.mpr ⟨q, hq_mem, rfl⟩
  have heq := (Finset.card_le_one.mp hcond) (p % 10) hp_img (q % 10) hq_img
  exact hdigits heq

theorem oeis_381159_conjecture_0.disproof :
  ¬ (∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)) := by
  rintro ⟨a, d, ha, hd1, hd2025, hall⟩
  rcases exists_pair_not_dvd d hd1 hd2025 with
    ⟨p, q, hp, hq, hdigit, hpq_le, hpnd, hqnd⟩
  have hm1 : 1 < p * q := lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_right p hq.pos)
  have hpcop : p.Coprime d := (hp.coprime_iff_not_dvd).mpr hpnd
  have hqcop : q.Coprime d := (hq.coprime_iff_not_dvd).mpr hqnd
  have hdcop : d.Coprime (p * q) := (Nat.Coprime.mul_left hpcop hqcop).symm
  rcases exists_i_mod_zero (a := a) (d := d) (m := p*q) hm1 hdcop with ⟨i, hi_lt_m, hmod⟩
  have hi_lt : i < 150 := lt_of_lt_of_le hi_lt_m hpq_le
  have hmdvd : p * q ∣ a + i*d := dvd_of_mod_aux hmod
  have hpdvd : p ∣ a + i*d := dvd_trans (dvd_mul_right p q) hmdvd
  have hqdvd : q ∣ a + i*d := by
    exact dvd_trans (by exact ⟨p, by rw [Nat.mul_comm]⟩) hmdvd
  have hn : a + i*d ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_two ha) (Nat.le_add_right a (i*d)))
  exact not_condition_of_two_primes hp hq hpdvd hqdvd hn hdigit (hall ⟨i, hi_lt⟩)
