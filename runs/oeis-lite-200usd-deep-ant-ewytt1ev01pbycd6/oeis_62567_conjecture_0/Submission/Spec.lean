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

/- ## Helper lemmas for settling the conjecture -/

variable {R : Type*} [CommRing R] (h81 : (81 : R) = 0)

-- weighted sum W(L) = Σ i * L[i]
def W : List ℕ → R
  | [] => 0
  | _ :: t => (t.sum : R) + W t

@[simp] lemma W_nil : (W [] : R) = 0 := rfl
lemma W_cons (d : ℕ) (t : List ℕ) : (W (d :: t) : R) = (t.sum : R) + W t := rfl

include h81 in
-- 10^i = 1 + 9 i in R
lemma pow10 (i : ℕ) : (10:R)^i = 1 + 9 * (i : R) := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]; push_cast; linear_combination (k : R) * h81

include h81 in
-- ofDigits 10 L = L.sum + 9 * W L  in R
lemma ofDigits_eq (L : List ℕ) :
    ofDigits (10:R) L = (L.sum : R) + 9 * W L := by
  induction L with
  | nil => simp [ofDigits]
  | cons d t ih =>
    have e : ofDigits (10:R) (d :: t) = (d:R) + 10 * ofDigits (10:R) t := rfl
    rw [e, ih, W_cons, List.sum_cons, Nat.cast_add]
    linear_combination (W t : R) * h81

-- append formula for W
lemma W_append (A B : List ℕ) :
    (W (A ++ B) : R) = W A + (A.length : R) * (B.sum : R) + W B := by
  induction A with
  | nil => simp [W_nil]
  | cons d t ih =>
    rw [List.cons_append, W_cons, W_cons, ih, List.length_cons, List.sum_append,
      Nat.cast_add, Nat.cast_add]
    ring

-- key reverse identity
lemma W_add_reverse (L : List ℕ) :
    (W L : R) + W L.reverse = ((L.length : R) - 1) * (L.sum : R) := by
  induction L with
  | nil => simp [W_nil]
  | cons d t ih =>
    rw [List.reverse_cons, W_cons, W_append]
    simp only [List.length_reverse, W_cons, W_nil, List.sum_cons, List.sum_nil, List.length_cons,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    linear_combination ih



include h81 in
lemma m_add_rev (m : ℕ) :
    (m : R) + (reverse_nat m : R)
      = (2 + 9 * (((digits 10 m).length : R) - 1)) * ((digits 10 m).sum : R) := by
  set L := digits 10 m with hL
  have hm : (m : R) = ofDigits (10:R) L := by
    conv_lhs => rw [← ofDigits_digits 10 m, ← hL]
    rw [coe_ofDigits]; norm_num
  have hrev : (reverse_nat m : R) = ofDigits (10:R) L.reverse := by
    rw [reverse_nat, ← hL, coe_ofDigits]; norm_num
  rw [hm, hrev, ofDigits_eq h81, ofDigits_eq h81, List.sum_reverse]
  have := W_add_reverse (R := R) L
  linear_combination 9 * this

-- ¬ 3 ∣ (2 + 9k)
lemma coprime_coef (k n : ℕ) : Nat.Coprime (2 + 9 * k) (3 ^ n) := by
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm]
  exact (Nat.prime_three.coprime_iff_not_dvd).mpr (by omega)

lemma digitsum_dvd (n m : ℕ) (hn : n ≤ 4) (hm : 3 ^ n ∣ m)
    (hr : 3 ^ n ∣ reverse_nat m) : 3 ^ n ∣ (digits 10 m).sum := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp
  have hNe : NeZero (3 ^ n) := ⟨by positivity⟩
  -- work in ZMod (3^n)
  have h81 : (81 : ZMod (3 ^ n)) = 0 := by
    have : (3 : ℕ) ^ n ∣ 81 := by
      have : (81 : ℕ) = 3 ^ 4 := by norm_num
      rw [this]; exact pow_dvd_pow 3 hn
    have := (ZMod.natCast_eq_zero_iff 81 (3 ^ n)).mpr this
    simpa using this
  have hm0 : (m : ZMod (3 ^ n)) = 0 := (ZMod.natCast_eq_zero_iff m (3 ^ n)).mpr hm
  have hr0 : (reverse_nat m : ZMod (3 ^ n)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ (3 ^ n)).mpr hr
  have key := m_add_rev h81 m
  rw [hm0, hr0, add_zero] at key
  -- 0 = coef * S
  set L := digits 10 m with hL
  have hlen : 1 ≤ L.length := by
    rw [hL]; exact Nat.one_le_iff_ne_zero.mpr (by
      simp [Nat.digits_ne_nil_iff_ne_zero, hmpos.ne'])
  -- rewrite coef as cast of a nat
  have hcoef : (2 + 9 * (((L.length : ZMod (3^n))) - 1)) = ((2 + 9 * (L.length - 1) : ℕ) : ZMod (3^n)) := by
    push_cast [Nat.cast_sub hlen]
    ring
  rw [hcoef] at key
  have hu : IsUnit ((2 + 9 * (L.length - 1) : ℕ) : ZMod (3 ^ n)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (coprime_coef (L.length - 1) n)
  have hS : ((L.sum : ℕ) : ZMod (3 ^ n)) = 0 := by
    have := (hu.mul_right_eq_zero).mp key.symm
    exact this
  exact (ZMod.natCast_eq_zero_iff _ (3 ^ n)).mp hS

-- ofDigits of all-nines list
lemma ofDigits_replicate_nine (L : ℕ) :
    Nat.ofDigits 10 (List.replicate L 9) = 10 ^ L - 1 := by
  induction L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih]
    have : (10:ℕ) ^ k ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

-- digit sum bound
lemma digitsum_le (m L : ℕ) (h : m < 10 ^ L) : (Nat.digits 10 m).sum ≤ 9 * L := by
  have hlen : (Nat.digits 10 m).length ≤ L := (Nat.digits_length_le_iff (by norm_num) m).mpr h
  have hbound : (Nat.digits 10 m).sum ≤ (Nat.digits 10 m).length * 9 := by
    apply List.sum_le_card_nsmul
    intro x hx
    exact Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hx)
  calc (Nat.digits 10 m).sum ≤ (Nat.digits 10 m).length * 9 := hbound
    _ ≤ L * 9 := by exact Nat.mul_le_mul_right 9 hlen
    _ = 9 * L := by ring

lemma list_all_eq (l : List ℕ) (c : ℕ) (hle : ∀ x ∈ l, x ≤ c)
    (hsum : l.sum = l.length * c) : ∀ x ∈ l, x = c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hta : t.sum ≤ t.length * c := by
      have := List.sum_le_card_nsmul t c (fun x hx => hle x (List.mem_cons_of_mem a hx))
      simpa [smul_eq_mul] using this
    rw [List.sum_cons, List.length_cons, add_mul, one_mul] at hsum
    have hac : a ≤ c := hle a (by simp)
    have ha : a = c := by omega
    have hts : t.sum = t.length * c := by omega
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; exact ha
    · exact ih (fun y hy => hle y (List.mem_cons_of_mem a hy)) hts x h

-- equality forces all nines
lemma digitsum_eq_max (m L : ℕ) (h : m < 10 ^ L)
    (heq : (Nat.digits 10 m).sum = 9 * L) : m = 10 ^ L - 1 := by
  have hlen : (Nat.digits 10 m).length ≤ L := (Nat.digits_length_le_iff (by norm_num) m).mpr h
  have hbound : (Nat.digits 10 m).sum ≤ (Nat.digits 10 m).length * 9 := by
    apply List.sum_le_card_nsmul
    intro x hx
    exact Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hx)
  -- length = L
  have hlenL : (Nat.digits 10 m).length = L := by
    have : 9 * L ≤ (Nat.digits 10 m).length * 9 := heq ▸ hbound
    have : L ≤ (Nat.digits 10 m).length := by omega
    omega
  -- all digits are 9
  have hall : ∀ x ∈ Nat.digits 10 m, x = 9 := by
    apply list_all_eq _ 9
    · intro x hx; exact Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hx)
    · rw [heq, hlenL]; ring
  -- digits 10 m = replicate L 9
  have hdig : Nat.digits 10 m = List.replicate L 9 := by
    apply List.eq_replicate_iff.mpr
    exact ⟨hlenL, hall⟩
  have : m = Nat.ofDigits 10 (Nat.digits 10 m) := (Nat.ofDigits_digits 10 m).symm
  rw [this, hdig, ofDigits_replicate_nine]

-- digits of all-nines number
lemma digits_all9 (L : ℕ) : Nat.digits 10 (10 ^ L - 1) = List.replicate L 9 := by
  rw [← ofDigits_replicate_nine]
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro x hx; rw [List.eq_of_mem_replicate hx]; norm_num
  · intro hne
    have hm := List.getLast_mem hne
    rw [List.eq_of_mem_replicate hm]; norm_num

lemma reverse_all9 (L : ℕ) : reverse_nat (10 ^ L - 1) = 10 ^ L - 1 := by
  rw [reverse_nat, digits_all9, List.reverse_replicate, ofDigits_replicate_nine]

lemma digitsum_all9 (L : ℕ) : (Nat.digits 10 (10 ^ L - 1)).sum = 9 * L := by
  rw [digits_all9, List.sum_replicate, smul_eq_mul]; ring


lemma a_eq (N : ℕ) (hN : N ≠ 0) (k0 : ℕ)
    (hk0 : 0 < k0 ∧ N ∣ reverse_nat (k0 * N))
    (hmin : ∀ j, 0 < j → j < k0 → ¬ (N ∣ reverse_nat (j * N))) :
    a N = k0 * N := by
  have h_ex : ∃ k, k > 0 ∧ N ∣ reverse_nat (k * N) := ⟨k0, hk0.1, hk0.2⟩
  unfold a
  rw [if_neg hN, dif_pos h_ex]
  show Nat.find h_ex * N = k0 * N
  congr 1
  rw [Nat.find_eq_iff]
  refine ⟨⟨hk0.1, hk0.2⟩, ?_⟩
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · exact fun h => absurd h.1 (by norm_num)
  · exact fun h => hmin j hjpos hj h.2

lemma backward (n : ℕ) (hn2 : 2 ≤ n) (hn4 : n ≤ 4)
    (hdvd : 3 ^ n ∣ 10 ^ (3 ^ (n - 2)) - 1) :
    a (3 ^ n) = 10 ^ (3 ^ (n - 2)) - 1 := by
  set L0 := 3 ^ (n - 2) with hL0
  set N := 3 ^ n with hN
  set A := 10 ^ L0 - 1 with hAdef
  have hApos : 0 < A := by
    have : 1 ≤ (10:ℕ) ^ L0 := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (10:ℕ) ^ L0 ≠ 1 := by
      have : (10:ℕ) ^ 1 ≤ 10 ^ L0 := Nat.pow_le_pow_right (by norm_num)
        (Nat.one_le_iff_ne_zero.mpr (by positivity))
      omega
    omega
  have hNpos : 0 < N := by positivity
  have hAN : N ≤ A := Nat.le_of_dvd hApos hdvd
  set k0 := A / N with hk0def
  have hk0N : k0 * N = A := Nat.div_mul_cancel hdvd
  have hk0pos : 0 < k0 := Nat.one_le_div_iff hNpos |>.mpr hAN
  -- digit sum of A equals N
  have hLmul : 9 * L0 = N := by
    rw [hN, hL0]
    have : (9:ℕ) = 3 ^ 2 := by norm_num
    rw [this, ← pow_add]
    congr 1
    omega
  rw [← hk0N]
  apply a_eq N (by positivity) k0 ⟨hk0pos, ?_⟩ ?_
  · -- N ∣ reverse_nat (k0 * N)
    rw [hk0N, hAdef, reverse_all9]
    exact hdvd
  · -- minimality
    intro j hjpos hjlt hcontra
    set m := j * N with hm
    have hmpos : 0 < m := Nat.mul_pos hjpos hNpos
    have hmlt : m < A := by rw [hm, ← hk0N]; exact (Nat.mul_lt_mul_right hNpos).mpr hjlt
    have hmdvd : N ∣ m := ⟨j, by rw [hm, Nat.mul_comm]⟩
    -- digit sum divisible by N
    have hsum : N ∣ (Nat.digits 10 m).sum := digitsum_dvd n m hn4 hmdvd hcontra
    -- digit sum ≤ N
    have hmlt10 : m < 10 ^ L0 := lt_of_lt_of_le hmlt (by rw [hAdef]; omega)
    have hle : (Nat.digits 10 m).sum ≤ N := by
      rw [← hLmul]; exact digitsum_le m L0 hmlt10
    -- digit sum > 0
    have hpos : 0 < (Nat.digits 10 m).sum := by
      have hne : Nat.digits 10 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hmpos.ne'
      have hmem := List.getLast_mem hne
      have hlast : (Nat.digits 10 m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 10 hmpos.ne'
      have : (Nat.digits 10 m).getLast hne ≤ (Nat.digits 10 m).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
      omega
    -- N ∣ s, s < N or s = N
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- s = N = 9 * L0 ⟹ m = A, contra
      have : m = 10 ^ L0 - 1 := digitsum_eq_max m L0 hmlt10 (by rw [heq, ← hLmul])
      rw [← hAdef] at this
      omega
    · -- s < N and N ∣ s ⟹ s = 0, contra pos
      have := Nat.eq_zero_of_dvd_of_lt hsum hlt
      omega

/-! ### Forward direction (n ≥ 5): tripling construction -/

-- a ≤ k*N when k qualifies
lemma a_le (N : ℕ) (hN : N ≠ 0) (k : ℕ) (hk : 0 < k)
    (hkd : N ∣ reverse_nat (k * N)) : a N ≤ k * N := by
  have h_ex : ∃ k, k > 0 ∧ N ∣ reverse_nat (k * N) := ⟨k, hk, hkd⟩
  unfold a
  rw [if_neg hN, dif_pos h_ex]
  show Nat.find h_ex * N ≤ k * N
  apply Nat.mul_le_mul_right
  exact Nat.find_le ⟨hk, hkd⟩

def Dseq : ℕ → List ℕ
  | 0 => [2, 9, 7, 9, 9, 9, 9, 9, 7, 9, 2]
  | (j + 1) => Dseq j ++ Dseq j ++ Dseq j

def Pseq (j : ℕ) : ℕ := Nat.ofDigits 10 (Dseq j)

lemma Dseq_len (j : ℕ) : (Dseq j).length = 11 * 3 ^ j := by
  induction j with
  | zero => rfl
  | succ k ih =>
    simp only [Dseq, List.length_append, ih]
    ring

lemma Dseq_reverse (j : ℕ) : (Dseq j).reverse = Dseq j := by
  induction j with
  | zero => rfl
  | succ k ih =>
    simp only [Dseq, List.reverse_append, ih]
    rw [List.append_assoc]

lemma Dseq_lt (j : ℕ) : ∀ x ∈ Dseq j, x < 10 := by
  induction j with
  | zero => decide
  | succ k ih =>
    intro x hx
    simp only [Dseq, List.mem_append] at hx
    rcases hx with (h | h) | h <;> exact ih x h

lemma Dseq_ne (j : ℕ) : Dseq j ≠ [] := by
  have hlen : (Dseq j).length ≠ 0 := by rw [Dseq_len]; positivity
  intro h; rw [h] at hlen; simp at hlen

lemma Dseq_pos (j : ℕ) : ∀ x ∈ Dseq j, x ≠ 0 := by
  induction j with
  | zero => decide
  | succ k ih =>
    intro x hx
    simp only [Dseq, List.mem_append] at hx
    rcases hx with (h | h) | h <;> exact ih x h

lemma digits_Pseq (j : ℕ) : Nat.digits 10 (Pseq j) = Dseq j := by
  rw [Pseq]
  apply Nat.digits_ofDigits 10 (by norm_num) _ (Dseq_lt j)
  intro h
  exact Dseq_pos j _ (List.getLast_mem h)

lemma reverse_Pseq (j : ℕ) : reverse_nat (Pseq j) = Pseq j := by
  rw [reverse_nat, digits_Pseq, Dseq_reverse, ← Pseq]

lemma Pseq_lt (j : ℕ) : Pseq j < 10 ^ (11 * 3 ^ j) := by
  have hlen : (Nat.digits 10 (Pseq j)).length ≤ 11 * 3 ^ j := by
    rw [digits_Pseq, Dseq_len]
  exact (Nat.digits_length_le_iff (by norm_num) (Pseq j)).mp hlen

-- recursion for Pseq
lemma Pseq_succ (j : ℕ) :
    Pseq (j + 1) = Pseq j * (1 + 10 ^ (11 * 3 ^ j) + 10 ^ (2 * (11 * 3 ^ j))) := by
  rw [Pseq, show Dseq (j+1) = Dseq j ++ (Dseq j ++ Dseq j) from by rw [Dseq, List.append_assoc]]
  rw [Nat.ofDigits_append, Nat.ofDigits_append, Dseq_len, ← Pseq]
  have hx2 : (10:ℕ) ^ (2 * (11 * 3 ^ j)) = 10 ^ (11 * 3 ^ j) * 10 ^ (11 * 3 ^ j) := by
    rw [two_mul, pow_add]
  rw [hx2]
  ring

lemma Pseq_dvd (j : ℕ) : 3 ^ (5 + j) ∣ Pseq j := by
  induction j with
  | zero =>
    show (243 : ℕ) ∣ Pseq 0
    rw [Pseq]
    decide
  | succ k ih =>
    rw [Pseq_succ]
    have h3 : (3:ℕ) ∣ (1 + 10 ^ (11 * 3 ^ k) + 10 ^ (2 * (11 * 3 ^ k))) := by
      have e1 : (10:ℕ) ^ (11 * 3 ^ k) ≡ 1 [MOD 3] := by
        simpa using Nat.ModEq.pow (11 * 3 ^ k) (show (10:ℕ) ≡ 1 [MOD 3] by decide)
      have e2 : (10:ℕ) ^ (2 * (11 * 3 ^ k)) ≡ 1 [MOD 3] := by
        simpa using Nat.ModEq.pow (2 * (11 * 3 ^ k)) (show (10:ℕ) ≡ 1 [MOD 3] by decide)
      have : (1 + 10 ^ (11 * 3 ^ k) + 10 ^ (2 * (11 * 3 ^ k))) ≡ 1 + 1 + 1 [MOD 3] :=
        (Nat.ModEq.add (Nat.ModEq.add (by rfl) e1) e2)
      have h0 : (1 + 1 + 1 : ℕ) ≡ 0 [MOD 3] := by decide
      exact (Nat.modEq_zero_iff_dvd).mp (this.trans h0)
    rw [show 5 + (k + 1) = (5 + k) + 1 from by ring, pow_succ]
    exact Nat.mul_dvd_mul ih h3

lemma Pseq_pos (j : ℕ) : 0 < Pseq j := by
  rcases Nat.eq_zero_or_pos (Pseq j) with h | h
  · exfalso
    have : Nat.digits 10 (Pseq j) = [] := by rw [h]; simp
    rw [digits_Pseq] at this
    exact Dseq_ne j this
  · exact h

lemma forward (n : ℕ) (hn5 : 5 ≤ n) : a (3 ^ n) ≠ 10 ^ (3 ^ (n - 2)) - 1 := by
  set j := n - 5 with hj
  have hnj : n = 5 + j := by omega
  have hdvd : 3 ^ n ∣ Pseq j := by rw [hnj]; exact Pseq_dvd j
  set N := 3 ^ n with hN
  have hNpos : 0 < N := by positivity
  set k := Pseq j / N with hk
  have hkN : k * N = Pseq j := Nat.div_mul_cancel hdvd
  have hkpos : 0 < k := by
    rw [hk]; exact Nat.div_pos (Nat.le_of_dvd (Pseq_pos j) hdvd) hNpos
  have hale : a N ≤ Pseq j := by
    rw [← hkN]
    apply a_le N (by positivity) k hkpos
    rw [hkN, reverse_Pseq]
    exact hdvd
  -- Pseq j < all9s
  set b := 3 ^ (n - 2) with hb
  have hb1 : 1 ≤ b := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 11 * 3 ^ j < b := by
    rw [hb, show n - 2 = 3 + j from by omega, pow_add]
    calc 11 * 3 ^ j < 27 * 3 ^ j :=
          (Nat.mul_lt_mul_right (show 0 < 3 ^ j by positivity)).mpr (by norm_num)
      _ = 3 ^ 3 * 3 ^ j := by norm_num
  have hpow1 : (10:ℕ) ^ (11 * 3 ^ j) ≤ 10 ^ (b - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpowb : (10:ℕ) ^ b = 10 * 10 ^ (b - 1) := by
    conv_lhs => rw [show b = (b - 1) + 1 from by omega]
    rw [pow_succ']
  have hpge : (1:ℕ) ≤ 10 ^ (b - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hplt : Pseq j < 10 ^ (11 * 3 ^ j) := Pseq_lt j
  have hlt : Pseq j < 10 ^ b - 1 := by omega
  intro heq
  rw [heq] at hale
  omega


/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) :=
by
  intro hn2
  constructor
  · intro heq
    by_contra hcon
    push_neg at hcon
    exact forward n (by omega) heq
  · intro h
    rcases h with rfl | rfl | rfl
    · exact backward 2 (by norm_num) (by norm_num) (by norm_num)
    · exact backward 3 (by norm_num) (by norm_num) (by norm_num)
    · exact backward 4 (by norm_num) (by norm_num) (by norm_num)
