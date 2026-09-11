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

namespace OEIS62567

/-- `h [d₀, d₁, …] = Σ i * dᵢ` -/
def h : List ℕ → ℕ
  | [] => 0
  | _ :: l => h l + l.sum

lemma h_append_singleton (l : List ℕ) (x : ℕ) : h (l ++ [x]) = h l + l.length * x := by
  induction l with
  | nil => simp [h]
  | cons b l ih => simp [h, ih, List.sum_append]; ring

lemma h_add_h_reverse (l : List ℕ) : h l + h l.reverse = (l.length - 1) * l.sum := by
  induction l with
  | nil => simp [h]
  | cons x l ih =>
    rw [List.reverse_cons, h_append_singleton]
    simp only [h, List.sum_cons, List.length_cons, List.length_reverse, Nat.add_sub_cancel]
    cases l with
    | nil => simp [h]
    | cons b l' =>
      simp only [List.length_cons, Nat.add_sub_cancel, List.sum_cons] at ih ⊢
      nlinarith [ih]

lemma ofDigits_mod81 (l : List ℕ) : ofDigits 10 l % 81 = (l.sum + 9 * h l) % 81 := by
  induction l with
  | nil => simp [h]
  | cons x l ih =>
    rw [ofDigits_cons]
    simp only [h, List.sum_cons]
    omega

lemma sum_dvd_of_dvd (e : ℕ) (he : e ≤ 4) (l : List ℕ) (h1 : 3^e ∣ ofDigits 10 l)
    (h2 : 3^e ∣ ofDigits 10 l.reverse) : 3^e ∣ l.sum := by
  have h81 : 3^e ∣ 81 := by
    have : (81:ℕ) = 3^4 := by norm_num
    rw [this]; exact Nat.pow_dvd_pow 3 he
  have m1 : ofDigits 10 l ≡ l.sum + 9 * h l [MOD 81] := ofDigits_mod81 l
  have m2 : ofDigits 10 l.reverse ≡ l.sum + 9 * h l.reverse [MOD 81] := by
    have := ofDigits_mod81 l.reverse
    rwa [List.sum_reverse] at this
  have d1 : 3^e ∣ l.sum + 9 * h l := (m1.dvd_iff h81).1 h1
  have d2 : 3^e ∣ l.sum + 9 * h l.reverse := (m2.dvd_iff h81).1 h2
  have m3 := h_add_h_reverse l
  have key : 3^e ∣ l.sum * (2 + 9 * (l.length - 1)) := by
    have : l.sum * (2 + 9 * (l.length - 1)) = (l.sum + 9 * h l) + (l.sum + 9 * h l.reverse) := by
      have : l.sum * (2 + 9 * (l.length - 1)) = 2 * l.sum + 9 * (h l + h l.reverse) := by
        rw [m3]; ring
      omega
    rw [this]; exact dvd_add d1 d2
  have hcop : Nat.Coprime (3^e) (2 + 9 * (l.length - 1)) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  exact hcop.dvd_of_dvd_mul_right key

lemma eq_replicate_of_sum (l : List ℕ) (hl : ∀ x ∈ l, x ≤ 9) (hs : l.sum = 9 * l.length) :
    l = List.replicate l.length 9 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx : x ≤ 9 := hl x (by simp)
    have hl' : ∀ y ∈ l, y ≤ 9 := fun y hy => hl y (by simp [hy])
    have hle : l.sum ≤ 9 * l.length := by
      have := List.sum_le_card_nsmul l 9 hl'
      simpa [smul_eq_mul, mul_comm] using this
    simp only [List.sum_cons, List.length_cons] at hs
    have hx9 : x = 9 := by omega
    have hs' : l.sum = 9 * l.length := by omega
    have := ih hl' hs'
    rw [List.length_cons, List.replicate_succ, hx9]
    simp only [List.cons.injEq, true_and]
    exact this

lemma ofDigits_eq_zero_of_sum (l : List ℕ) (h0 : l.sum = 0) : ofDigits 10 l = 0 := by
  induction l with
  | nil => simp [ofDigits]
  | cons x l ih =>
    simp only [List.sum_cons] at h0
    rw [ofDigits_cons, ih (by omega)]
    omega

lemma ofDigits_replicate_nine (N : ℕ) : ofDigits 10 (List.replicate N 9) = 10^N - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.replicate_succ, ofDigits_cons, ih, pow_succ]
    have := Nat.one_le_pow N 10 (by norm_num)
    omega

lemma no_small (e N : ℕ) (he : e ≤ 4) (heN : 3^e = 9 * N) (m : ℕ) (hm : 0 < m)
    (hlt : m < 10^N - 1) (h1 : 3^e ∣ m) (h2 : 3^e ∣ reverse_nat m) : False := by
  have hm' : ofDigits 10 (digits 10 m) = m := ofDigits_digits 10 m
  have h1' : 3^e ∣ ofDigits 10 (digits 10 m) := by rwa [hm']
  have hS := sum_dvd_of_dvd e he (digits 10 m) h1' h2
  have hlen : (digits 10 m).length ≤ N := (digits_length_le_iff (by norm_num) m).2 (by omega)
  have hdig : ∀ x ∈ digits 10 m, x ≤ 9 :=
    fun x hx => Nat.le_of_lt_succ (digits_lt_base (by norm_num) hx)
  have hle : (digits 10 m).sum ≤ 9 * (digits 10 m).length := by
    have := List.sum_le_card_nsmul (digits 10 m) 9 hdig
    simpa [smul_eq_mul, mul_comm] using this
  have hpos : (digits 10 m).sum ≠ 0 := by
    intro h0
    have := ofDigits_eq_zero_of_sum _ h0
    omega
  have hge : 9 * N ≤ (digits 10 m).sum := by
    rw [← heN]; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hS
  have hlenN : (digits 10 m).length = N := by omega
  have hsum : (digits 10 m).sum = 9 * (digits 10 m).length := by omega
  have hrep := eq_replicate_of_sum _ hdig hsum
  rw [hlenN] at hrep
  have : m = 10^N - 1 := by
    rw [← hm', hrep, ofDigits_replicate_nine]
  omega

lemma a_eq_small (e N : ℕ) (he : e ≤ 4) (heN : 3^e = 9 * N) (hN : 0 < N)
    (hdiv : 3^e ∣ 10^N - 1) (hrev : 3^e ∣ reverse_nat (10^N - 1)) : a (3^e) = 10^N - 1 := by
  have hne : 3^e ≠ 0 := by positivity
  have hk0 : (10^N - 1) / 3^e * 3^e = 10^N - 1 := Nat.div_mul_cancel hdiv
  have hpos : 0 < 10^N - 1 := by
    have : 10 ≤ 10^N := by
      calc 10 = 10^1 := by norm_num
        _ ≤ 10^N := Nat.pow_le_pow_right (by norm_num) hN
    omega
  have hk0pos : 0 < (10^N - 1) / 3^e := by
    rcases Nat.eq_zero_or_pos ((10^N - 1) / 3^e) with h | h
    · rw [h, zero_mul] at hk0; omega
    · exact h
  have hP : (10^N - 1) / 3^e > 0 ∧ 3^e ∣ reverse_nat ((10^N - 1) / 3^e * 3^e) :=
    ⟨hk0pos, by rw [hk0]; exact hrev⟩
  have hex : ∃ k, k > 0 ∧ 3^e ∣ reverse_nat (k * 3^e) := ⟨_, hP⟩
  unfold a
  rw [if_neg hne]
  simp only
  rw [dif_pos hex]
  have : Nat.find hex = (10^N - 1) / 3^e := by
    rw [Nat.find_eq_iff]
    refine ⟨hP, fun k hk hk' => ?_⟩
    obtain ⟨hkpos, hkdvd⟩ := hk'
    apply no_small e N he heN (k * 3^e) (by positivity) ?_ (dvd_mul_left _ _) hkdvd
    rw [← hk0]
    exact Nat.mul_lt_mul_of_pos_right hk (by positivity)
  rw [this, hk0]

/-- The repetition multiplier: `c j = Σ_{i < 3^j} 10^(10 i)`. -/
def c : ℕ → ℕ
  | 0 => 1
  | j+1 => c j * (1 + 10^(10 * 3^j) + 10^(2 * (10 * 3^j)))

lemma three_dvd (k : ℕ) : 3 ∣ 1 + 10^k + 10^(2 * k) := by
  have h1 : 10^k % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have h2 : 10^(2 * k) % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  omega

lemma three_pow_dvd_c (j : ℕ) : 3^j ∣ c j := by
  induction j with
  | zero => simp [c]
  | succ j ih =>
    rw [c, pow_succ]
    exact Nat.mul_dvd_mul ih (three_dvd _)

lemma c_pos (j : ℕ) : 0 < c j := by
  induction j with
  | zero => simp [c]
  | succ j ih => rw [c]; positivity

lemma digits_rev_big (j : ℕ) :
    (digits 10 (4899999987 * c j)).length = 10 * 3^j ∧
    ofDigits 10 (digits 10 (4899999987 * c j)).reverse = 7899999984 * c j := by
  induction j with
  | zero =>
    simp only [c, mul_one, pow_zero]
    constructor
    · norm_num
    · norm_num [Nat.ofDigits]
  | succ j ih =>
    obtain ⟨hk, hr⟩ := ih
    have heq : 4899999987 * c (j+1) =
        4899999987 * c j + 10 ^ (digits 10 (4899999987 * c j)).length *
          (4899999987 * c j + 10 ^ (digits 10 (4899999987 * c j)).length * (4899999987 * c j)) := by
      rw [hk, c]; ring
    rw [heq, ← digits_append_digits (by norm_num), ← digits_append_digits (by norm_num)]
    constructor
    · simp only [List.length_append, hk]; rw [pow_succ]; ring
    · simp only [List.reverse_append, ofDigits_append, List.length_append, List.length_reverse, hk, hr]
      rw [c]; ring

lemma big_lt (j : ℕ) : 4899999987 * c j < 10^(3^(j+3)) - 1 := by
  have h1 : 4899999987 * c j < 10^(10 * 3^j) :=
    (digits_length_le_iff (by norm_num) _).1 (digits_rev_big j).1.le
  have h2 : 10^(10 * 3^j) < 10^(3^(j+3)) := by
    apply Nat.pow_lt_pow_right (by norm_num)
    have : 3^(j+3) = 27 * 3^j := by rw [pow_add]; ring
    rw [this]
    have : 0 < 3^j := by positivity
    omega
  omega

lemma a_le_big (j : ℕ) : a (3^(j+5)) ≤ 4899999987 * c j := by
  have hne : 3^(j+5) ≠ 0 := by positivity
  have hdvd : 3^(j+5) ∣ 4899999987 * c j := by
    rw [pow_add, mul_comm (3^j)]
    exact Nat.mul_dvd_mul (by norm_num) (three_pow_dvd_c j)
  have hrev : 3^(j+5) ∣ reverse_nat (4899999987 * c j) := by
    unfold reverse_nat
    rw [(digits_rev_big j).2, pow_add, mul_comm (3^j)]
    exact Nat.mul_dvd_mul (by norm_num) (three_pow_dvd_c j)
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      have := c_pos j
      omega
    · exact h
  have hP : k > 0 ∧ 3^(j+5) ∣ reverse_nat (k * 3^(j+5)) :=
    ⟨hkpos, by rw [mul_comm, ← hk]; exact hrev⟩
  have hex : ∃ k, k > 0 ∧ 3^(j+5) ∣ reverse_nat (k * 3^(j+5)) := ⟨k, hP⟩
  unfold a
  rw [if_neg hne]
  simp only
  rw [dif_pos hex]
  calc Nat.find hex * 3^(j+5) ≤ k * 3^(j+5) := Nat.mul_le_mul_right _ (Nat.find_min' hex hP)
    _ = 4899999987 * c j := by rw [mul_comm, ← hk]

end OEIS62567

open OEIS62567 in
/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | h5
  · have := a_eq_small 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [reverse_nat, Nat.ofDigits])
    simpa using this
  · have := a_eq_small 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [reverse_nat, Nat.ofDigits])
    simpa using this
  · have := a_eq_small 4 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [reverse_nat, Nat.ofDigits])
    simpa using this
  · have hne : ¬ (n = 2 ∨ n = 3 ∨ n = 4) := by omega
    simp only [hne, iff_false]
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
    have hbig := a_le_big j
    have hlt := big_lt j
    have : j + 5 - 2 = j + 3 := by omega
    rw [this]
    omega

theorem oeis_62567_conjecture_0.disproof : ¬ (type_of% @oeis_62567_conjecture_0) := sorry
