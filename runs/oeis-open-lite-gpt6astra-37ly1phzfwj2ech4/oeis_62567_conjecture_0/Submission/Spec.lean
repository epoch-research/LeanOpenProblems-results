import FormalConjectures.Util.ProblemImports

open Nat Classical

/-- The number whose digits in base 10 are $n$'s digits reversed. -/
def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

/--
A062567: First multiple of $n$ whose reverse is also divisible by $n$, or 0 if no such multiple exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- P(k) is the predicate for the multiplier k: k > 0 and n divides the reverse of (k*n).
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)

    -- We check if a solution exists (using classical reasoning, since P is decidable).
    if h_ex : ∃ k, P k then
      -- Nat.find requires a DecidablePred instance, which holds for this property on ℕ.
      have HP : DecidablePred P := by infer_instance
      -- k_min is the smallest multiplier k >= 1.
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

namespace ReverseMultiples

lemma pow_ten {R : Type*} [CommRing R] (h81 : (81 : R) = 0) (k : ℕ) :
    (10 : R)^k = 1 + 9 * (k : R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : R) * h81

lemma scaled_digits {R : Type*} [CommRing R] (h81 : (81 : R) = 0) (L : List ℕ) :
    9 * ofDigits (10 : R) L = 9 * (L.sum : R) := by
  induction L with
  | nil => simp [ofDigits]
  | cons a L ih =>
    simp only [ofDigits, List.sum_cons, Nat.cast_add]
    linear_combination 10 * ih + (L.sum : R) * h81

lemma reverse_cons {R : Type*} [CommRing R] (a : ℕ) (L : List ℕ) :
    ofDigits (10 : R) (a :: L).reverse = ofDigits (10 : R) L.reverse + 10^L.length * a := by
  have h := congrArg (fun x : ℕ => (x : R)) (ofDigits_reverse_cons (b := 10) L a)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, coe_ofDigits] using h

lemma paired_digits {R : Type*} [CommRing R] (h81 : (81 : R) = 0) (L : List ℕ) :
    10 * (ofDigits (10 : R) L + ofDigits (10 : R) L.reverse) =
      (11 + 9 * (L.length : R)) * (L.sum : R) := by
  induction L with
  | nil => simp [ofDigits]
  | cons a L ih =>
    rw [reverse_cons, pow_ten h81]
    simp only [ofDigits, List.length_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    linear_combination ih + 10 * scaled_digits h81 L +
      ((L.sum : R) + (L.length : R) * a) * h81

lemma sum_zero {R : Type*} [CommRing R] (h81 : (81 : R) = 0) (L : List ℕ)
    (hN : ofDigits (10 : R) L = 0) (hR : ofDigits (10 : R) L.reverse = 0) :
    (L.sum : R) = 0 := by
  have h := paired_digits h81 L
  rw [hN, hR] at h
  linear_combination -(59 - 63 * (L.length : R)) * h -
    (8 - 2 * (L.length : R) - 7 * (L.length : R)^2) * (L.sum : R) * h81

lemma sum_dvd (d N : ℕ) (hd : d ∣ 81) (hN : d ∣ N)
    (hR : d ∣ ofDigits 10 (digits 10 N).reverse) : d ∣ (digits 10 N).sum := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  apply sum_zero (R := ZMod d)
  · exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  · have he := coe_ofDigits (ZMod d) 10 (digits 10 N)
    norm_num only [Nat.cast_ofNat, ofDigits_digits] at he
    rw [← he]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hN
  · simpa only [coe_ofDigits, Nat.cast_ofNat] using
      (ZMod.natCast_eq_zero_iff _ _).mpr hR

lemma sum_bound (L : List ℕ) (h : ∀ x ∈ L, x ≤ 9) : L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons, List.length_cons]
    omega

lemma sum_max (L : List ℕ) (h : ∀ x ∈ L, x ≤ 9) (hs : L.sum = 9 * L.length) :
    L = List.replicate L.length 9 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (by simp)
    have ht : ∀ x ∈ L, x ≤ 9 := fun x hx => h x (by simp [hx])
    have hb := sum_bound L ht
    simp only [List.sum_cons, List.length_cons] at hs
    have ha9 : a = 9 := by omega
    have he : L.sum = 9 * L.length := by omega
    simpa [ha9, List.replicate_succ] using congrArg (List.cons 9) (ih ht he)

lemma ofDigits_nines (k : ℕ) : ofDigits 10 (List.replicate k 9) + 1 = 10^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, ofDigits_cons, pow_succ]
    omega

lemma sum_pos_of_ofDigits_pos (L : List ℕ) (h : 0 < ofDigits 10 L) : 0 < L.sum := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    simp only [ofDigits_cons] at h
    simp only [List.sum_cons]
    by_cases ha : a = 0
    · have ht : 0 < ofDigits 10 L := by omega
      have := ih ht
      omega
    · omega

lemma lower_bound (d t N : ℕ) (hd : d ∣ 81) (ht : d = 9 * t)
    (hpos : 0 < N) (hN : d ∣ N) (hR : d ∣ ofDigits 10 (digits 10 N).reverse) :
    10^t - 1 ≤ N := by
  by_contra h
  have hlt : N < 10^t := by omega
  have hlen := (digits_length_le_iff (by decide : 1 < 10) N).mpr hlt
  have hs := sum_dvd d N hd hN hR
  have hp : 0 < (digits 10 N).sum :=
    sum_pos_of_ofDigits_pos _ (by simpa only [ofDigits_digits] using hpos)
  have hsle := Nat.le_of_dvd hp hs
  have hdigits : ∀ x ∈ digits 10 N, x ≤ 9 :=
    fun x hx => by have := digits_lt_base (by decide : 1 < 10) hx; omega
  have hbound := sum_bound _ hdigits
  have he : (digits 10 N).sum = 9 * (digits 10 N).length := by omega
  have hlen_eq : (digits 10 N).length = t := by omega
  have hrep := sum_max _ hdigits he
  rw [hlen_eq] at hrep
  have hnines := ofDigits_nines t
  rw [← hrep, ofDigits_digits] at hnines
  omega

lemma a_le_candidate (d N : ℕ) (hpos : 0 < N) (hdiv : d ∣ N)
    (hrev : d ∣ reverse_nat N) : a d ≤ N := by
  have hd : d ≠ 0 := by rintro rfl; simp only [zero_dvd_iff] at hdiv; omega
  obtain ⟨k, rfl⟩ := hdiv
  have hk : 0 < k := by nlinarith
  have hsol : 0 < k ∧ d ∣ reverse_nat (k * d) := by simpa [mul_comm] using And.intro hk hrev
  have hex : ∃ k, 0 < k ∧ d ∣ reverse_nat (k * d) := ⟨k, hsol⟩
  unfold a
  rw [if_neg hd, dif_pos hex]
  simpa [mul_comm] using Nat.mul_le_mul_right d (Nat.find_min' hex hsol)

lemma a_eq_min (d N : ℕ) (hpos : 0 < N) (hdiv : d ∣ N)
    (hrev : d ∣ reverse_nat N)
    (hmin : ∀ M, 0 < M → d ∣ M → d ∣ reverse_nat M → N ≤ M) : a d = N := by
  apply le_antisymm (a_le_candidate d N hpos hdiv hrev)
  have hd : d ≠ 0 := by rintro rfl; simp only [zero_dvd_iff] at hdiv; omega
  obtain ⟨k, he⟩ := hdiv
  have hk : 0 < k := by nlinarith
  have hsol : 0 < k ∧ d ∣ reverse_nat (k * d) := by
    constructor
    · exact hk
    · simpa [he, mul_comm] using hrev
  have hex : ∃ k, 0 < k ∧ d ∣ reverse_nat (k * d) := ⟨k, hsol⟩
  unfold a
  rw [if_neg hd, dif_pos hex]
  have hs := Nat.find_spec hex
  apply hmin
  · exact Nat.mul_pos hs.1 (Nat.pos_of_ne_zero hd)
  · exact dvd_mul_left _ _
  · exact hs.2

lemma small_two : a (3^2) = 10^(3^(2-2)) - 1 := by
  apply a_eq_min
  · norm_num
  · norm_num
  · norm_num [reverse_nat, ofDigits, List.reverse_cons]
  · intro M hp hd hr
    exact lower_bound 9 1 M (by norm_num) (by norm_num) hp hd hr

lemma small_three : a (3^3) = 10^(3^(3-2)) - 1 := by
  apply a_eq_min
  · norm_num
  · norm_num
  · norm_num [reverse_nat, ofDigits, List.reverse_cons]
  · intro M hp hd hr
    exact lower_bound 27 3 M (by norm_num) (by norm_num) hp hd hr

lemma small_four : a (3^4) = 10^(3^(4-2)) - 1 := by
  apply a_eq_min
  · norm_num
  · norm_num
  · norm_num [reverse_nat, ofDigits, List.reverse_cons]
  · intro M hp hd hr
    exact lower_bound 81 9 M (by norm_num) (by norm_num) hp hd hr

lemma palindrome_blocks (k : ℕ) :
    ∃ L : List ℕ, L.length = 11 * 3^k ∧
      (∀ x ∈ L, x < 10) ∧ (∀ h : L ≠ [], L.getLast h ≠ 0) ∧
      L.reverse = L ∧ 3^(k+5) ∣ ofDigits 10 L ∧ 0 < ofDigits 10 L := by
  induction k with
  | zero =>
    refine ⟨[2, 9, 7, 9, 9, 9, 9, 9, 7, 9, 2], ?_⟩
    norm_num [ofDigits, List.reverse_cons]
  | succ k ih =>
    obtain ⟨L, hlen, hdigs, hlast, hpal, hdiv, hpos⟩ := ih
    have hne : L ≠ [] := by
      intro he
      have hp : 0 < 3^k := by positivity
      simp [he] at hlen
    have hval : ofDigits 10 (L ++ L ++ L) =
        ofDigits 10 L * (1 + 10^L.length + 10^(2*L.length)) := by
      simp only [ofDigits_append, List.length_append, pow_add]
      rw [show 2 * L.length = L.length + L.length by omega, pow_add]
      ring
    have hthree : 3 ∣ 1 + 10^L.length + 10^(2*L.length) := by
      apply Nat.dvd_of_mod_eq_zero
      norm_num [Nat.add_mod, Nat.pow_mod]
    refine ⟨L ++ L ++ L, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, hlen, pow_succ]
      ring
    · intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx <;> exact hdigs x hx
    · intro h
      rw [List.getLast_append_of_right_ne_nil _ _ hne]
      exact hlast hne
    · simp only [List.reverse_append, hpal, List.append_assoc]
    · rw [hval, show k.succ + 5 = (k+5)+1 by omega, pow_succ]
      exact Nat.mul_dvd_mul hdiv hthree
    · rw [hval]
      exact Nat.mul_pos hpos (by positivity)

lemma large (k : ℕ) : a (3^(k+5)) < 10^(3^(k+3)) - 1 := by
  obtain ⟨L, hlen, hdigs, hlast, hpal, hdiv, hpos⟩ := palindrome_blocks k
  have hcanon : digits 10 (ofDigits 10 L) = L :=
    digits_ofDigits 10 (by decide) L hdigs hlast
  have hrev : reverse_nat (ofDigits 10 L) = ofDigits 10 L := by
    unfold reverse_nat
    rw [hcanon, hpal]
  have ha := a_le_candidate (3^(k+5)) (ofDigits 10 L) hpos hdiv (by rwa [hrev])
  have hlen_lt : L.length < 3^(k+3) := by
    rw [hlen, pow_add]
    have hp : 0 < 3^k := by positivity
    norm_num
    omega
  have hb := ofDigits_lt_base_pow_length (by decide : 1 < 10) hdigs
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 10) (Nat.succ_le_of_lt hlen_lt)
  rw [pow_succ] at hpow
  have hp : 0 < 10^L.length := by positivity
  omega


end ReverseMultiples

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) :=
by
  intro hn
  constructor
  · intro he
    by_contra h
    have hn5 : 5 ≤ n := by omega
    have hlarge := ReverseMultiples.large (n-5)
    have h1 : n - 5 + 5 = n := by omega
    have h2 : n - 5 + 3 = n - 2 := by omega
    rw [h1, h2, he] at hlarge
    exact (lt_irrefl _) hlarge
  · rintro (rfl | rfl | rfl)
    · exact ReverseMultiples.small_two
    · exact ReverseMultiples.small_three
    · exact ReverseMultiples.small_four

theorem oeis_62567_conjecture_0.disproof : ¬ (type_of% @oeis_62567_conjecture_0) := sorry
