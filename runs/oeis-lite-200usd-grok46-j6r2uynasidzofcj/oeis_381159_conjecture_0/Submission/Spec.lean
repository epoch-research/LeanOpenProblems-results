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

lemma one_le_pos {n : ℕ} (h : 1 ≤ n) : 0 < n := Nat.succ_le_iff.1 h

lemma term_ne_zero {a d : ℕ} {i : Fin 150} (ha : 2 ≤ a) : a + i.val * d ≠ 0 :=
  Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2)
    (ha.trans (Nat.le_add_right _ _)))

lemma not_condition_of_two_primes {n p q : ℕ}
    (hn : n ≠ 0) (hp : p.Prime) (hq : q.Prime)
    (hpn : p ∣ n) (hqn : q ∣ n) (hdiff : p % 10 ≠ q % 10) :
    ¬ A381159_condition n := by
  intro h
  have hp' : p ∈ n.primeFactors := mem_primeFactors.2 ⟨hp, hpn, hn⟩
  have hq' : q ∈ n.primeFactors := mem_primeFactors.2 ⟨hq, hqn, hn⟩
  exact hdiff <| Finset.card_le_one_iff.1 h
    (Finset.mem_image_of_mem _ hp') (Finset.mem_image_of_mem _ hq')

lemma exists_lt_dvd_add_mul (a d m : ℕ) (hm : 0 < m) (hcop : Coprime d m) :
    ∃ i < m, m ∣ a + i * d := by
  obtain ⟨i, hi, hieq⟩ :=
    Nat.exists_mul_mod_eq_of_coprime ((m - a % m) % m) hcop hm.ne'
  refine ⟨i, hi, ?_⟩
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_comm i d, hieq, Nat.mod_mod]
  by_cases hz : a % m = 0
  · simp [hz]
  · have ha : a % m < m := Nat.mod_lt a hm
    have hsub : m - a % m < m := Nat.sub_lt hm (Nat.pos_of_ne_zero hz)
    rw [Nat.mod_eq_of_lt hsub, Nat.add_sub_of_le (le_of_lt ha), Nat.mod_self]

lemma exists_fin150_dvd (a d m : ℕ) (hm : 0 < m) (hle : m ≤ 150)
    (hcop : Coprime d m) : ∃ i : Fin 150, m ∣ a + i.val * d := by
  obtain ⟨i, hi, hid⟩ := exists_lt_dvd_add_mul a d m hm hcop
  exact ⟨⟨i, hi.trans_le hle⟩, hid⟩

lemma coprime_of_primes {d p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpd : ¬ p ∣ d) (hqd : ¬ q ∣ d) : Coprime d (p * q) := by
  rw [Nat.coprime_mul_iff_right]
  exact ⟨(hp.coprime_iff_not_dvd.2 hpd).symm, (hq.coprime_iff_not_dvd.2 hqd).symm⟩

lemma hit_mixed {a d p q : ℕ} (ha : 2 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hdiff : p % 10 ≠ q % 10)
    (hmul : p * q ≤ 150) (hcop : Coprime d (p * q))
    (hAll : ∀ i : Fin 150, A381159_condition (a + i.val * d)) : False := by
  obtain ⟨i, hid⟩ :=
    exists_fin150_dvd a d (p * q) (Nat.mul_pos hp.pos hq.pos) hmul hcop
  exact not_condition_of_two_primes (term_ne_zero ha) hp hq
    (dvd_trans (dvd_mul_right p q) hid)
    (dvd_trans (dvd_mul_left q p) hid) hdiff (hAll i)

lemma hit_mixed_pair {a d p q : ℕ} (ha : 2 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hdiff : p % 10 ≠ q % 10)
    (hmul : p * q ≤ 150) (hpd : ¬ p ∣ d) (hqd : ¬ q ∣ d)
    (hAll : ∀ i : Fin 150, A381159_condition (a + i.val * d)) : False :=
  hit_mixed ha hp hq hdiff hmul (coprime_of_primes hp hq hpd hqd) hAll

lemma hit_with_forced {a d p q : ℕ} (ha : 2 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hdiff : p % 10 ≠ q % 10)
    (hpa : p ∣ a) (hpd : p ∣ d) (hqd : ¬ q ∣ d) (hqle : q ≤ 150)
    (hAll : ∀ i : Fin 150, A381159_condition (a + i.val * d)) : False := by
  obtain ⟨i, hid⟩ :=
    exists_fin150_dvd a d q hq.pos hqle (hq.coprime_iff_not_dvd.2 hqd).symm
  exact not_condition_of_two_primes (term_ne_zero ha) hp hq
    (dvd_add hpa (dvd_mul_of_dvd_right hpd _)) hid hdiff (hAll i)

lemma first_mixed {a p q : ℕ} (ha : 2 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hdiff : p % 10 ≠ q % 10)
    (hpa : p ∣ a) (hqa : q ∣ a) (h0 : A381159_condition a) : False :=
  not_condition_of_two_primes (by
    exact (Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) ha).ne.symm) hp hq hpa hqa hdiff h0

lemma prime_13 : Nat.Prime 13 := by norm_num
lemma prime_17 : Nat.Prime 17 := by norm_num

lemma coprime_primes_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Coprime p q := (Nat.coprime_primes hp hq).2 hne

lemma not_dvd_of_mod {p n : ℕ} (h : n % p ≠ 0) : ¬ p ∣ n :=
  mt Nat.dvd_iff_mod_eq_zero.1 h

lemma coprime_right_prime {n p : ℕ} (hp : p.Prime) (h : n % p ≠ 0) : Coprime n p :=
  (hp.coprime_iff_not_dvd.2 (not_dvd_of_mod h)).symm

lemma mul_dvd_coprime {m n k : ℕ} (hm : m ∣ k) (hn : n ∣ k) (h : Coprime m n) :
    m * n ∣ k := h.mul_dvd_of_dvd_of_dvd hm hn

lemma term0 {a d : ℕ} (hAll : ∀ i : Fin 150, A381159_condition (a + i.val * d)) :
    A381159_condition a := by
  simpa using hAll ⟨0, by decide⟩

lemma ne_2_3 : (2 : ℕ) ≠ 3 := by decide
lemma ne_2_5 : (2 : ℕ) ≠ 5 := by decide
lemma ne_2_7 : (2 : ℕ) ≠ 7 := by decide
lemma ne_2_11 : (2 : ℕ) ≠ 11 := by decide
lemma ne_3_5 : (3 : ℕ) ≠ 5 := by decide
lemma ne_3_7 : (3 : ℕ) ≠ 7 := by decide
lemma mod2_3 : (2 : ℕ) % 10 ≠ 3 % 10 := by decide
lemma mod2_5 : (2 : ℕ) % 10 ≠ 5 % 10 := by decide
lemma mod2_7 : (2 : ℕ) % 10 ≠ 7 % 10 := by decide
lemma mod2_11 : (2 : ℕ) % 10 ≠ 11 % 10 := by decide
lemma mod2_13 : (2 : ℕ) % 10 ≠ 13 % 10 := by decide
lemma mod3_5 : (3 : ℕ) % 10 ≠ 5 % 10 := by decide
lemma mod3_7 : (3 : ℕ) % 10 ≠ 7 % 10 := by decide
lemma mod3_11 : (3 : ℕ) % 10 ≠ 11 % 10 := by decide
lemma mod3_17 : (3 : ℕ) % 10 ≠ 17 % 10 := by decide
lemma mod5_3 : (5 : ℕ) % 10 ≠ 3 % 10 := by decide
lemma mod5_7 : (5 : ℕ) % 10 ≠ 7 % 10 := by decide
lemma mod5_11 : (5 : ℕ) % 10 ≠ 11 % 10 := by decide
lemma mod5_13 : (5 : ℕ) % 10 ≠ 13 % 10 := by decide
lemma mod7_11 : (7 : ℕ) % 10 ≠ 11 % 10 := by decide
lemma mod7_13 : (7 : ℕ) % 10 ≠ 13 % 10 := by decide
lemma mod11_13 : (11 : ℕ) % 10 ≠ 13 % 10 := by decide

lemma le6 : 2 * 3 ≤ 150 := by decide
lemma le10 : 2 * 5 ≤ 150 := by decide
lemma le14 : 2 * 7 ≤ 150 := by decide
lemma le22 : 2 * 11 ≤ 150 := by decide
lemma le26 : 2 * 13 ≤ 150 := by decide
lemma le15 : 3 * 5 ≤ 150 := by decide
lemma le21 : 3 * 7 ≤ 150 := by decide
lemma le33 : 3 * 11 ≤ 150 := by decide
lemma le51 : 3 * 17 ≤ 150 := by decide
lemma le35 : 5 * 7 ≤ 150 := by decide
lemma le55 : 5 * 11 ≤ 150 := by decide
lemma le65 : 5 * 13 ≤ 150 := by decide
lemma le77 : 7 * 11 ≤ 150 := by decide
lemma le91 : 7 * 13 ≤ 150 := by decide
lemma le143 : 11 * 13 ≤ 150 := by decide
lemma le3 : 3 ≤ 150 := by decide
lemma le5 : 5 ≤ 150 := by decide
lemma le7 : 7 ≤ 150 := by decide
lemma le11 : 11 ≤ 150 := by decide

lemma two_dvd_d {a d : ℕ} (ha : 2 ≤ a) (hdpos : 1 ≤ d) (hd2 : d ≤ 2025)
    (hAll : ∀ i : Fin 150, A381159_condition (a + i.val * d)) : 2 ∣ d := by
  by_contra h2
  have h3 : 3 ∣ d := by
    by_contra h3; exact hit_mixed_pair ha prime_two prime_three mod2_3 le6 h2 h3 hAll
  have h5 : 5 ∣ d := by
    by_contra h5; exact hit_mixed_pair ha prime_two prime_five mod2_5 le10 h2 h5 hAll
  have h7 : 7 ∣ d := by
    by_contra h7; exact hit_mixed_pair ha prime_two prime_seven mod2_7 le14 h2 h7 hAll
  have h11 : 11 ∣ d := by
    by_contra h11; exact hit_mixed_pair ha prime_two prime_eleven mod2_11 le22 h2 h11 hAll
  have h13 : 13 ∣ d := by
    by_contra h13; exact hit_mixed_pair ha prime_two prime_13 mod2_13 le26 h2 h13 hAll
  have h15 : 15 ∣ d := mul_dvd_coprime h3 h5 (coprime_primes_ne prime_three prime_five ne_3_5)
  have h105 : 105 ∣ d := by
    have : 15 * 7 = 105 := rfl
    rw [← this]
    exact mul_dvd_coprime h15 h7 (coprime_right_prime prime_seven (by decide))
  have h1155 : 1155 ∣ d := by
    have : 105 * 11 = 1155 := rfl
    rw [← this]
    exact mul_dvd_coprime h105 h11 (coprime_right_prime prime_eleven (by decide))
  have h15015 : 15015 ∣ d := by
    have : 1155 * 13 = 15015 := rfl
    rw [← this]
    exact mul_dvd_coprime h1155 h13 (coprime_right_prime prime_13 (by decide))
  have hle : 15015 ≤ d := le_of_dvd (one_le_pos hdpos) h15015
  exact Nat.not_le.2 (by decide : 2025 < 15015) (le_trans hle hd2)


lemma five_dvd_d {a d : ℕ} (ha : 2 ≤ a) (hdpos : 1 ≤ d) (hd2le : d ≤ 2025)
    (hAll : ∀ i : Fin 150, A381159_condition (a + i.val * d))
    (hd2 : 2 ∣ d) : 5 ∣ d := by
  by_contra h5
  have h3 : 3 ∣ d := by
    by_contra h3; exact hit_mixed_pair ha prime_three prime_five mod3_5 le15 h3 h5 hAll
  have h7 : 7 ∣ d := by
    by_contra h7; exact hit_mixed_pair ha prime_five prime_seven mod5_7 le35 h5 h7 hAll
  have h11 : 11 ∣ d := by
    by_contra h11; exact hit_mixed_pair ha prime_five prime_eleven mod5_11 le55 h5 h11 hAll
  have h13 : 13 ∣ d := by
    by_contra h13; exact hit_mixed_pair ha prime_five prime_13 mod5_13 le65 h5 h13 hAll
  have h6 : 6 ∣ d := mul_dvd_coprime hd2 h3 (coprime_primes_ne prime_two prime_three ne_2_3)
  have h42 : 42 ∣ d := by
    have : 6 * 7 = 42 := rfl
    rw [← this]
    exact mul_dvd_coprime h6 h7 (coprime_right_prime prime_seven (by decide))
  have h462 : 462 ∣ d := by
    have : 42 * 11 = 462 := rfl
    rw [← this]
    exact mul_dvd_coprime h42 h11 (coprime_right_prime prime_eleven (by decide))
  have h6006 : 6006 ∣ d := by
    have : 462 * 13 = 6006 := rfl
    rw [← this]
    exact mul_dvd_coprime h462 h13 (coprime_right_prime prime_13 (by decide))
  have hle : 6006 ≤ d := le_of_dvd (one_le_pos hdpos) h6006
  exact Nat.not_le.2 (by decide : 2025 < 6006) (le_trans hle hd2le)


lemma three_dvd_d {a d : ℕ} (ha : 2 ≤ a) (hdpos : 1 ≤ d) (hd2le : d ≤ 2025)
    (hAll : ∀ i : Fin 150, A381159_condition (a + i.val * d))
    (hd2 : 2 ∣ d) (hd5 : 5 ∣ d) : 3 ∣ d := by
  by_contra h3
  have h7 : 7 ∣ d := by
    by_contra h7; exact hit_mixed_pair ha prime_three prime_seven mod3_7 le21 h3 h7 hAll
  have h11 : 11 ∣ d := by
    by_contra h11; exact hit_mixed_pair ha prime_three prime_eleven mod3_11 le33 h3 h11 hAll
  have h17 : 17 ∣ d := by
    by_contra h17; exact hit_mixed_pair ha prime_three prime_17 mod3_17 le51 h3 h17 hAll
  have h10 : 10 ∣ d := mul_dvd_coprime hd2 hd5 (coprime_primes_ne prime_two prime_five ne_2_5)
  have h70 : 70 ∣ d := by
    have : 10 * 7 = 70 := rfl
    rw [← this]
    exact mul_dvd_coprime h10 h7 (coprime_right_prime prime_seven (by decide))
  have h770 : 770 ∣ d := by
    have : 70 * 11 = 770 := rfl
    rw [← this]
    exact mul_dvd_coprime h70 h11 (coprime_right_prime prime_eleven (by decide))
  have h13090 : 13090 ∣ d := by
    have : 770 * 17 = 13090 := rfl
    rw [← this]
    exact mul_dvd_coprime h770 h17 (coprime_right_prime prime_17 (by decide))
  have hle : 13090 ≤ d := le_of_dvd (one_le_pos hdpos) h13090
  exact Nat.not_le.2 (by decide : 2025 < 13090) (le_trans hle hd2le)

lemma seven_dvd_d {a d : ℕ} (ha : 2 ≤ a) (hdpos : 1 ≤ d) (hd2le : d ≤ 2025)
    (hAll : ∀ i : Fin 150, A381159_condition (a + i.val * d))
    (hd2 : 2 ∣ d) (hd3 : 3 ∣ d) (hd5 : 5 ∣ d) : 7 ∣ d := by
  by_contra h7
  have h11 : 11 ∣ d := by
    by_contra h11; exact hit_mixed_pair ha prime_seven prime_eleven mod7_11 le77 h7 h11 hAll
  have h13 : 13 ∣ d := by
    by_contra h13; exact hit_mixed_pair ha prime_seven prime_13 mod7_13 le91 h7 h13 hAll
  have h6 : 6 ∣ d := mul_dvd_coprime hd2 hd3 (coprime_primes_ne prime_two prime_three ne_2_3)
  have h30 : 30 ∣ d := by
    have : 6 * 5 = 30 := rfl
    rw [← this]
    exact mul_dvd_coprime h6 hd5 (coprime_right_prime prime_five (by decide))
  have h330 : 330 ∣ d := by
    have : 30 * 11 = 330 := rfl
    rw [← this]
    exact mul_dvd_coprime h30 h11 (coprime_right_prime prime_eleven (by decide))
  have h4290 : 4290 ∣ d := by
    have : 330 * 13 = 4290 := rfl
    rw [← this]
    exact mul_dvd_coprime h330 h13 (coprime_right_prime prime_13 (by decide))
  have hle : 4290 ≤ d := le_of_dvd (one_le_pos hdpos) h4290
  exact Nat.not_le.2 (by decide : 2025 < 4290) (le_trans hle hd2le)

theorem oeis_381159_conjecture_0.disproof :
    ¬ ∃ (a d : ℕ),
      2 ≤ a ∧
      1 ≤ d ∧
      d ≤ 2025 ∧
      ∀ (i : Fin 150), A381159_condition (a + i.val * d) := by
  rintro ⟨a, d, ha, hd1, hd2, hAll⟩
  have h2d : 2 ∣ d := two_dvd_d ha hd1 hd2 hAll
  have h5d : 5 ∣ d := five_dvd_d ha hd1 hd2 hAll h2d
  have h3d : 3 ∣ d := three_dvd_d ha hd1 hd2 hAll h2d h5d
  have h7d : 7 ∣ d := seven_dvd_d ha hd1 hd2 hAll h2d h3d h5d
  have h6 : 6 ∣ d := mul_dvd_coprime h2d h3d (coprime_primes_ne prime_two prime_three ne_2_3)
  have h30 : 30 ∣ d := by
    have : 6 * 5 = 30 := rfl
    rw [← this]
    exact mul_dvd_coprime h6 h5d (coprime_right_prime prime_five (by decide))
  have h210 : 210 ∣ d := by
    have : 30 * 7 = 210 := rfl
    rw [← this]
    exact mul_dvd_coprime h30 h7d (coprime_right_prime prime_seven (by decide))
  have h11 : ¬ 11 ∣ d := by
    intro h
    have h2310 : 2310 ∣ d := by
      have : 210 * 11 = 2310 := rfl
      rw [← this]
      exact mul_dvd_coprime h210 h (coprime_right_prime prime_eleven (by decide))
    have hle : 2310 ≤ d := le_of_dvd (one_le_pos hd1) h2310
    exact Nat.not_le.2 (by decide : 2025 < 2310) (le_trans hle hd2)
  have h13 : ¬ 13 ∣ d := by
    intro h
    have h2730 : 2730 ∣ d := by
      have : 210 * 13 = 2730 := rfl
      rw [← this]
      exact mul_dvd_coprime h210 h (coprime_right_prime prime_13 (by decide))
    have hle : 2730 ≤ d := le_of_dvd (one_le_pos hd1) h2730
    exact Nat.not_le.2 (by decide : 2025 < 2730) (le_trans hle hd2)
  exact hit_mixed_pair ha prime_eleven prime_13 mod11_13 le143 h11 h13 hAll
