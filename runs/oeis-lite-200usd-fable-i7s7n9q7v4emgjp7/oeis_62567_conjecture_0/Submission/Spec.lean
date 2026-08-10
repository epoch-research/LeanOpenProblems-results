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

namespace Aux62567

/-!
Auxiliary results for A062567.

Mathematical outline.

For every `n ≥ 2` the number `10 ^ 3 ^ (n - 2) - 1` (a string of `3 ^ (n - 2)` nines)
is a palindromic multiple of `3 ^ n` (by lifting-the-exponent,
`v₃(10 ^ k - 1) = 2 + v₃(k)`), so `a (3 ^ n)` is at most this number.

* For `n = 2, 3, 4` we show that this bound is attained.  The point is that modulo `81`
  one has `10 ^ i ≡ 1 + 9 i`, so a number `N` with digits `d₀, …, d_{m-1}` satisfies
  `N ≡ S + 9 W (mod 81)` where `S` is the digit sum and `W = ∑ i dᵢ`, and the reversed
  number satisfies `rev N ≡ S + 9 ((m - 1) S - W) (mod 81)`.  If `81 ∣ N` and
  `81 ∣ rev N`, adding the two congruences gives `S (9 m - 7) ≡ 0 (mod 81)`; since
  `9 m - 7` is coprime to `3`, this forces `81 ∣ S`.  As `S ≤ 9 m`, for `m ≤ 9` this
  forces either `N = 0` or `m = 9` and all digits equal to `9`, i.e. `N = 10 ^ 9 - 1`.
  The same computation modulo `27` (with `m ≤ 3`) handles `n = 3`, and `n = 2` is
  immediate.

* For `n ≥ 5` the bound is not attained: `29799999792 = 243 · 122633744` is an
  11-digit palindromic multiple of `3 ^ 5`, and concatenating three copies of a
  palindromic multiple of `3 ^ j` (with `L` digits) produces a palindromic multiple of
  `3 ^ (j + 1)` with `3 L` digits (multiplication by `1 + 10 ^ L + 10 ^ (2 L) ≡ 3`
  modulo `9` contributes exactly one more factor of `3`).  Hence `3 ^ n` has a
  palindromic multiple with `11 · 3 ^ (n - 5) < 3 ^ (n - 2)` digits, which is a
  strictly smaller witness than `10 ^ 3 ^ (n - 2) - 1`.
-/

private lemma a_of_exists (n : ℕ) (hn : n ≠ 0)
    (h : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n)) :
    ∃ k, (k > 0 ∧ n ∣ reverse_nat (k * n)) ∧ a n = k * n ∧
      ∀ j, j > 0 → n ∣ reverse_nat (j * n) → k ≤ j := by
  unfold a
  rw [if_neg hn]
  simp only []
  rw [dif_pos h]
  exact ⟨_, Nat.find_spec h, rfl, fun j hj hdj => Nat.find_min' h ⟨hj, hdj⟩⟩

/- ### Digit-sum arithmetic modulo divisors of 81 -/

/-- Weighted digit sum: `w [d₀, d₁, …] = ∑ i • dᵢ`. -/
private def w : List ℕ → ℕ
  | [] => 0
  | _ :: t => w t + t.sum

private lemma pow_ten {R : Type*} [CommRing R] (h81 : (81 : R) = 0) (k : ℕ) :
    (10 : R) ^ k = 1 + 9 * (k : R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : R) * h81

private lemma ofDigits_cast {R : Type*} [CommRing R] (h81 : (81 : R) = 0) (l : List ℕ) :
    ((Nat.ofDigits 10 l : ℕ) : R) = (l.sum : R) + 9 * (w l : R) := by
  induction l with
  | nil => simp [Nat.ofDigits_nil, w]
  | cons d t ih =>
    rw [Nat.ofDigits_cons]
    simp only [w, List.sum_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [ih]
    linear_combination (w t : R) * h81

private lemma ofDigits_reverse_cast {R : Type*} [CommRing R] (h81 : (81 : R) = 0)
    (l : List ℕ) :
    ((Nat.ofDigits 10 l.reverse : ℕ) : R)
      = (l.sum : R) + 9 * (l.length : R) * (l.sum : R) - 9 * (l.sum : R) - 9 * (w l : R) := by
  induction l with
  | nil => simp [Nat.ofDigits_nil, w]
  | cons d t ih =>
    rw [List.reverse_cons, Nat.ofDigits_append, Nat.ofDigits_singleton]
    simp only [w, List.sum_cons, List.length_cons, List.length_reverse,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [ih, pow_ten h81 t.length]
    ring

/-- If `M ∣ N` and `M ∣ reverse_nat N` where `81 ≡ 0 (mod M)`, then the digit sum `S`
and the number of digits `m` of `N` satisfy `S * (9 m - 7) = 0` in `ZMod M`. -/
private lemma sum_mul_eq_zero (M : ℕ) (h81 : (81 : ZMod M) = 0) (N : ℕ)
    (h1 : M ∣ N) (h2 : M ∣ reverse_nat N) :
    ((Nat.digits 10 N).sum : ZMod M) *
      (9 * ((Nat.digits 10 N).length : ZMod M) - 7) = 0 := by
  have c1 : ((N : ℕ) : ZMod M) = 0 := (ZMod.natCast_eq_zero_iff N M).mpr h1
  have c2 : ((reverse_nat N : ℕ) : ZMod M) = 0 := (ZMod.natCast_eq_zero_iff _ M).mpr h2
  rw [show N = Nat.ofDigits 10 (Nat.digits 10 N) from (Nat.ofDigits_digits 10 N).symm,
    ofDigits_cast h81] at c1
  rw [show reverse_nat N = Nat.ofDigits 10 (Nat.digits 10 N).reverse from rfl,
    ofDigits_reverse_cast h81] at c2
  linear_combination c1 + c2

/- ### Lists with maximal digit sum are constant -/

private lemma eq_replicate_of_sum : ∀ l : List ℕ, (∀ x ∈ l, x ≤ 9) →
    l.sum = 9 * l.length → l = List.replicate l.length 9
  | [], _, _ => rfl
  | d :: t, hb, hs => by
    have hd9 : d ≤ 9 := hb d List.mem_cons_self
    have hts : t.sum ≤ 9 * t.length := by
      have h := List.sum_le_card_nsmul t 9 (fun x hx => hb x (List.mem_cons_of_mem d hx))
      simpa [smul_eq_mul, Nat.mul_comm] using h
    rw [List.sum_cons, List.length_cons] at hs
    have hd : d = 9 := by omega
    have ht : t.sum = 9 * t.length := by omega
    have hrec := eq_replicate_of_sum t (fun x hx => hb x (List.mem_cons_of_mem d hx)) ht
    rw [List.length_cons, List.replicate_succ, ← hrec, hd]

/- ### The key rigidity lemmas modulo 27 and 81 -/

private lemma eq_of_dvd_27 (N : ℕ) (hN : N < 10 ^ 3) (h1 : 27 ∣ N)
    (h2 : 27 ∣ reverse_nat N) : N = 0 ∨ N = 999 := by
  have key := sum_mul_eq_zero 27 (by decide) N h1 h2
  have hmlen : (Nat.digits 10 N).length ≤ 3 :=
    (Nat.digits_length_le_iff (by norm_num) N).mpr hN
  have hd : ∀ x ∈ Nat.digits 10 N, x ≤ 9 := fun x hx =>
    Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hx)
  have hS9 : (Nat.digits 10 N).sum ≤ 9 * (Nat.digits 10 N).length := by
    have h := List.sum_le_card_nsmul (Nat.digits 10 N) 9 hd
    simpa [smul_eq_mul, Nat.mul_comm] using h
  have hSdvd : (27:ℕ) ∣ (Nat.digits 10 N).sum := by
    rw [← ZMod.natCast_eq_zero_iff]
    obtain ⟨m, hm⟩ : ∃ m, (Nat.digits 10 N).length = m := ⟨_, rfl⟩
    rw [hm] at hmlen key
    generalize ((Nat.digits 10 N).sum : ZMod 27) = x at key ⊢
    interval_cases m <;> revert key <;> revert x <;> decide
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · exact Or.inl h0
  right
  have hsum : (Nat.digits 10 N).sum = 0 ∨ (Nat.digits 10 N).sum = 27 := by omega
  rcases hsum with hs | hs
  · exfalso
    have hne : Nat.digits 10 N ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hpos.ne'
    have hmem : (Nat.digits 10 N).getLast hne ∈ Nat.digits 10 N := List.getLast_mem hne
    have hle := List.single_le_sum (fun x (_ : x ∈ Nat.digits 10 N) => Nat.zero_le x) _ hmem
    rw [hs] at hle
    exact Nat.getLast_digit_ne_zero 10 hpos.ne' (Nat.le_zero.mp hle)
  · have h3 : (Nat.digits 10 N).length = 3 := by omega
    have hrepl := eq_replicate_of_sum (Nat.digits 10 N) hd (by rw [h3, hs])
    rw [h3] at hrepl
    have hN' : N = Nat.ofDigits 10 (Nat.digits 10 N) := (Nat.ofDigits_digits 10 N).symm
    rw [hrepl] at hN'
    norm_num [Nat.ofDigits, List.replicate] at hN'
    exact hN'

private lemma eq_of_dvd_81 (N : ℕ) (hN : N < 10 ^ 9) (h1 : 81 ∣ N)
    (h2 : 81 ∣ reverse_nat N) : N = 0 ∨ N = 999999999 := by
  have key := sum_mul_eq_zero 81 (by decide) N h1 h2
  have hmlen : (Nat.digits 10 N).length ≤ 9 :=
    (Nat.digits_length_le_iff (by norm_num) N).mpr hN
  have hd : ∀ x ∈ Nat.digits 10 N, x ≤ 9 := fun x hx =>
    Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hx)
  have hS9 : (Nat.digits 10 N).sum ≤ 9 * (Nat.digits 10 N).length := by
    have h := List.sum_le_card_nsmul (Nat.digits 10 N) 9 hd
    simpa [smul_eq_mul, Nat.mul_comm] using h
  have hSdvd : (81:ℕ) ∣ (Nat.digits 10 N).sum := by
    rw [← ZMod.natCast_eq_zero_iff]
    obtain ⟨m, hm⟩ : ∃ m, (Nat.digits 10 N).length = m := ⟨_, rfl⟩
    rw [hm] at hmlen key
    generalize ((Nat.digits 10 N).sum : ZMod 81) = x at key ⊢
    interval_cases m <;> revert key <;> revert x <;> decide
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · exact Or.inl h0
  right
  have hsum : (Nat.digits 10 N).sum = 0 ∨ (Nat.digits 10 N).sum = 81 := by omega
  rcases hsum with hs | hs
  · exfalso
    have hne : Nat.digits 10 N ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hpos.ne'
    have hmem : (Nat.digits 10 N).getLast hne ∈ Nat.digits 10 N := List.getLast_mem hne
    have hle := List.single_le_sum (fun x (_ : x ∈ Nat.digits 10 N) => Nat.zero_le x) _ hmem
    rw [hs] at hle
    exact Nat.getLast_digit_ne_zero 10 hpos.ne' (Nat.le_zero.mp hle)
  · have h9 : (Nat.digits 10 N).length = 9 := by omega
    have hrepl := eq_replicate_of_sum (Nat.digits 10 N) hd (by rw [h9, hs])
    rw [h9] at hrepl
    have hN' : N = Nat.ofDigits 10 (Nat.digits 10 N) := (Nat.ofDigits_digits 10 N).symm
    rw [hrepl] at hN'
    norm_num [Nat.ofDigits, List.replicate] at hN'
    exact hN'

/- ### Concrete values of `reverse_nat` -/

private lemma rev_9 : reverse_nat 9 = 9 := by
  rw [reverse_nat]; norm_num [Nat.digits_def', Nat.ofDigits]

private lemma rev_999 : reverse_nat 999 = 999 := by
  rw [reverse_nat]; norm_num [Nat.digits_def', Nat.ofDigits]

private lemma rev_nines9 : reverse_nat 999999999 = 999999999 := by
  rw [reverse_nat]; norm_num [Nat.digits_def', Nat.ofDigits]

/- ### The values `a 9`, `a 27`, `a 81` -/

private lemma a_9 : a 9 = 9 := by
  obtain ⟨k, ⟨hk0, _⟩, hak, hmin⟩ := a_of_exists 9 (by norm_num)
    ⟨1, by norm_num, by rw [one_mul, rev_9]⟩
  have hk1 : k ≤ 1 := hmin 1 (by norm_num) (by rw [one_mul, rev_9])
  have : k = 1 := by omega
  rw [hak, this, one_mul]

private lemma a_27 : a 27 = 999 := by
  obtain ⟨k, ⟨hk0, hkd⟩, hak, hmin⟩ := a_of_exists 27 (by norm_num)
    ⟨37, by norm_num, by rw [show 37 * 27 = 999 from rfl, rev_999]; norm_num⟩
  have hk37 : k ≤ 37 := hmin 37 (by norm_num)
    (by rw [show 37 * 27 = 999 from rfl, rev_999]; norm_num)
  have hcase := eq_of_dvd_27 (k * 27) (by omega) (dvd_mul_left _ _) hkd
  rw [hak]
  omega

private lemma a_81 : a 81 = 999999999 := by
  obtain ⟨k, ⟨hk0, hkd⟩, hak, hmin⟩ := a_of_exists 81 (by norm_num)
    ⟨12345679, by norm_num, by rw [show 12345679 * 81 = 999999999 from rfl, rev_nines9]; norm_num⟩
  have hkb : k ≤ 12345679 := hmin 12345679 (by norm_num)
    (by rw [show 12345679 * 81 = 999999999 from rfl, rev_nines9]; norm_num)
  have hcase := eq_of_dvd_81 (k * 81) (by omega) (dvd_mul_left _ _) hkd
  rw [hak]
  omega

/- ### Small palindromic multiples of `3 ^ (5 + p)` -/

private lemma witness : ∀ p : ℕ, ∃ N : ℕ, 0 < N ∧ 3 ^ (5 + p) ∣ N ∧
    (Nat.digits 10 N).reverse = Nat.digits 10 N ∧
    (Nat.digits 10 N).length = 11 * 3 ^ p := by
  intro p
  induction p with
  | zero =>
    refine ⟨29799999792, by norm_num, by norm_num, ?_, ?_⟩ <;>
    · rw [show Nat.digits 10 29799999792 = [2,9,7,9,9,9,9,9,7,9,2] by
        norm_num [Nat.digits_def']]
      rfl
  | succ p ih =>
    obtain ⟨N, hN0, hdvd, hrev, hlen⟩ := ih
    refine ⟨N + 10 ^ (Nat.digits 10 N).length *
        (N + 10 ^ (Nat.digits 10 N).length * N), ?_, ?_, ?_, ?_⟩
    · exact Nat.lt_of_lt_of_le hN0 (Nat.le_add_right N _)
    · have h3 : (3:ℕ) ∣ 1 + 10 ^ (Nat.digits 10 N).length *
          (1 + 10 ^ (Nat.digits 10 N).length) := by
        obtain ⟨q, hq⟩ : ∃ q, (10:ℕ) ^ (Nat.digits 10 N).length = 3 * q + 1 := by
          have h10 : (10:ℕ) ^ (Nat.digits 10 N).length % 3 = 1 := by
            rw [Nat.pow_mod]; simp
          exact ⟨10 ^ (Nat.digits 10 N).length / 3, by omega⟩
        exact ⟨3*q*q + 3*q + 1, by rw [hq]; ring⟩
      have heq : N + 10 ^ (Nat.digits 10 N).length *
          (N + 10 ^ (Nat.digits 10 N).length * N)
          = N * (1 + 10 ^ (Nat.digits 10 N).length *
            (1 + 10 ^ (Nat.digits 10 N).length)) := by ring
      rw [heq, show 5 + (p + 1) = (5 + p) + 1 from rfl, pow_succ]
      exact mul_dvd_mul hdvd h3
    · rw [← Nat.digits_append_digits (by norm_num), ← Nat.digits_append_digits (by norm_num)]
      simp only [List.reverse_append, hrev]
      rw [List.append_assoc]
    · rw [← Nat.digits_append_digits (by norm_num), ← Nat.digits_append_digits (by norm_num)]
      simp only [List.length_append, hlen]
      rw [pow_succ]
      ring

private lemma a_lt (p : ℕ) : a (3 ^ (5 + p)) < 10 ^ (11 * 3 ^ p) := by
  obtain ⟨N, hN0, hdvd, hrev, hlen⟩ := witness p
  have hrevN : reverse_nat N = N := by
    rw [reverse_nat, hrev, Nat.ofDigits_digits]
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k > 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [Nat.mul_zero] at hk; omega
    · exact h
  obtain ⟨k', ⟨_, _⟩, hak, hmin⟩ := a_of_exists (3 ^ (5 + p)) (by positivity)
    ⟨k, hk0, by rw [mul_comm, ← hk, hrevN]; exact ⟨k, hk⟩⟩
  have hk'k : k' ≤ k := hmin k hk0 (by rw [mul_comm, ← hk, hrevN]; exact ⟨k, hk⟩)
  have hNlt : N < 10 ^ (11 * 3 ^ p) := by
    rw [← hlen]
    exact Nat.lt_base_pow_length_digits (by norm_num)
  calc a (3 ^ (5 + p)) = k' * 3 ^ (5 + p) := hak
    _ ≤ k * 3 ^ (5 + p) := Nat.mul_le_mul_right _ hk'k
    _ = N := by rw [mul_comm, ← hk]
    _ < 10 ^ (11 * 3 ^ p) := hNlt

end Aux62567

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n from by omega) with rfl | rfl | rfl | h5
  · norm_num [Aux62567.a_9]
  · norm_num [Aux62567.a_27]
  · norm_num [Aux62567.a_81]
  · obtain ⟨p, rfl⟩ : ∃ p, n = 5 + p := ⟨n - 5, by omega⟩
    have h1 := Aux62567.a_lt p
    have h2 : (10:ℕ) ^ (11 * 3 ^ p) < 10 ^ (3 ^ (5 + p - 2)) := by
      apply Nat.pow_lt_pow_right (by norm_num)
      rw [show 5 + p - 2 = 3 + p from by omega, pow_add]
      have h3p : 0 < 3 ^ p := by positivity
      omega
    have h4 : (0:ℕ) < 10 ^ (3 ^ (5 + p - 2)) := by positivity
    constructor
    · intro h
      omega
    · rintro (h | h | h) <;> omega
