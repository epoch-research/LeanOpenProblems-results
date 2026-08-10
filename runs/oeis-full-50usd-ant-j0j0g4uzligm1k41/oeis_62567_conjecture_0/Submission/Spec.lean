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

namespace A062567

/-- weighted digit sum: wsum [d0,d1,...] = Σ i * d_i -/
def wsum : List ℕ → ℕ
  | [] => 0
  | _ :: L => wsum L + L.sum

lemma wsum_append (A B : List ℕ) :
    wsum (A ++ B) = wsum A + wsum B + A.length * B.sum := by
  induction A with
  | nil => simp [wsum]
  | cons a A ih =>
    simp only [List.cons_append, wsum, List.length_cons, List.sum_append] at *
    rw [ih]
    ring

lemma wsum_reverse_add (L : List ℕ) :
    wsum L + wsum L.reverse + L.sum = L.length * L.sum := by
  induction L with
  | nil => simp [wsum]
  | cons a t ih =>
    simp only [List.reverse_cons, wsum, List.length_cons, List.sum_cons]
    rw [wsum_append]
    simp only [wsum, List.length_reverse, List.sum_cons, List.sum_nil, add_zero,
      List.length_singleton, mul_one]
    -- goal in terms of wsum t, wsum t.reverse, t.sum, t.length
    -- use ih: wsum t + wsum t.reverse + t.sum = t.length * t.sum
    have h := ih
    ring_nf
    ring_nf at h
    omega

lemma key_cong (N : ℕ) (h81 : (81 : ZMod N) = 0) (L : List ℕ) :
    (Nat.ofDigits (10 : ZMod N) L)
      = (L.sum : ZMod N) + 9 * (wsum L : ZMod N) := by
  induction L with
  | nil => simp [Nat.ofDigits, wsum]
  | cons d L ih =>
    rw [show Nat.ofDigits (10 : ZMod N) (d :: L)
          = (d : ZMod N) + 10 * Nat.ofDigits (10 : ZMod N) L from rfl, ih]
    simp only [wsum, List.sum_cons]
    push_cast
    linear_combination (wsum L : ZMod N) * h81

lemma key_cong' (N : ℕ) (h81 : (81 : ZMod N) = 0) (L : List ℕ) :
    ((Nat.ofDigits 10 L : ℕ) : ZMod N)
      = (L.sum : ZMod N) + 9 * (wsum L : ZMod N) := by
  rw [Nat.coe_ofDigits]
  exact key_cong N h81 L

/-- Core: if `N = 3^j` with `N ∣ 81`, `0 < m`, `N ∣ m`, `N ∣ reverse_nat m`,
then `N` divides the digit sum of `m`. -/
lemma sum_dvd (j : ℕ) (hj81 : (3:ℕ)^j ∣ 81) (m : ℕ) (hm0 : 0 < m)
    (hm : (3:ℕ)^j ∣ m) (hrev : (3:ℕ)^j ∣ reverse_nat m) :
    (3:ℕ)^j ∣ (digits 10 m).sum := by
  set N : ℕ := 3^j with hN
  have hNe : NeZero N := ⟨by positivity⟩
  have h81 : (81 : ZMod N) = 0 := by
    have : ((81:ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff 81 N).2 hj81
    simpa using this
  set L := digits 10 m with hL
  set ℓ := L.length with hℓ
  set S := L.sum with hS
  -- ℓ ≥ 1 since m > 0
  have hLne : L ≠ [] := by
    rw [hL]; exact Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ]; exact List.length_pos_of_ne_nil hLne
  -- cast equations
  have hmcast : ((m : ℕ) : ZMod N) = (S : ZMod N) + 9 * (wsum L : ZMod N) := by
    conv_lhs => rw [← Nat.ofDigits_digits 10 m]
    rw [← hL]; exact key_cong' N h81 L
  have hrevcast : ((reverse_nat m : ℕ) : ZMod N)
      = (S : ZMod N) + 9 * (wsum L.reverse : ZMod N) := by
    rw [reverse_nat, ← hL, key_cong' N h81 L.reverse, List.sum_reverse]
  have hm00 : ((m:ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff m N).2 hm
  have hr00 : ((reverse_nat m : ℕ) : ZMod N) = 0 :=
    (ZMod.natCast_eq_zero_iff _ N).2 hrev
  have e1 : (S : ZMod N) + 9 * (wsum L : ZMod N) = 0 := by rw [← hmcast]; exact hm00
  have e2 : (S : ZMod N) + 9 * (wsum L.reverse : ZMod N) = 0 := by
    rw [← hrevcast]; exact hr00
  -- wsum reverse identity, cast
  have hWR : ((wsum L : ZMod N) + (wsum L.reverse : ZMod N)) + (S : ZMod N)
      = (ℓ : ZMod N) * (S : ZMod N) := by
    have h := congrArg (fun t : ℕ => (t : ZMod N)) (wsum_reverse_add L)
    rw [← hS, ← hℓ] at h
    push_cast at h
    linear_combination h
  -- derive S * (9ℓ - 7) = 0
  have key0 : (S : ZMod N) * (9 * (ℓ : ZMod N) - 7) = 0 := by
    linear_combination e1 + e2 - 9 * hWR
  -- transfer to ℕ divisibility
  have hcast : (((S * (9 * ℓ - 7) : ℕ)) : ZMod N) = 0 := by
    have h7 : (7 : ℕ) ≤ 9 * ℓ := by omega
    push_cast [Nat.cast_sub h7]
    linear_combination key0
  have hdvd : N ∣ S * (9 * ℓ - 7) := (ZMod.natCast_eq_zero_iff _ N).1 hcast
  -- coprimality
  have hnd : ¬ (3 : ℕ) ∣ (9 * ℓ - 7) := by omega
  have hco3 : Nat.Coprime 3 (9 * ℓ - 7) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hnd
  have hcoN : Nat.Coprime N (9 * ℓ - 7) := by
    rw [hN]; exact hco3.pow_left j
  exact hcoN.dvd_of_dvd_mul_right hdvd

/-- If all entries of `L` are `≤ c` and the sum is `c * length`, every entry equals `c`. -/
lemma all_eq_of_sum (c : ℕ) : ∀ (L : List ℕ), (∀ x ∈ L, x ≤ c) →
    L.sum = c * L.length → ∀ x ∈ L, x = c := by
  intro L
  induction L with
  | nil => intro _ _ x hx; simp at hx
  | cons a t ih =>
    intro hle hsum
    have hat : t.sum ≤ c * t.length := by
      have := List.sum_le_card_nsmul t c (fun x hx => hle x (List.mem_cons_of_mem _ hx))
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have ha : a ≤ c := hle a (List.mem_cons_self ..)
    simp only [List.sum_cons, List.length_cons] at hsum
    have ha' : a = c ∧ t.sum = c * t.length := by
      constructor <;> nlinarith [Nat.mul_succ c t.length]
    intro x hx
    rcases List.mem_cons.1 hx with h | h
    · rw [h]; exact ha'.1
    · exact ih (fun y hy => hle y (List.mem_cons_of_mem _ hy)) ha'.2 x h

lemma reverse_nat_palindrome (L : List ℕ) (hlt : ∀ x ∈ L, x < 10)
    (hlast : ∀ h : L ≠ [], L.getLast h ≠ 0) (hpal : L.reverse = L) :
    reverse_nat (Nat.ofDigits 10 L) = Nat.ofDigits 10 L := by
  unfold reverse_nat
  rw [Nat.digits_ofDigits 10 (by norm_num) L hlt hlast, hpal]

lemma three_dvd_geom (k : ℕ) : (3:ℕ)^(k+2) ∣ 10 ^ (3 ^ k) - 1 := by
  have hint : ((3:ℤ)^(k+2)) ∣ ((10:ℤ)^(3^k) - 1) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      have e : (10:ℤ)^(3^(k+1)) = ((10:ℤ)^(3^k))^3 := by
        rw [← pow_mul, pow_succ]
      set a : ℤ := (10:ℤ)^(3^k) with ha
      have factor : a^3 - 1 = (a - 1) * (a^2 + a + 1) := by ring
      have h10 : (10:ℤ) ≡ 1 [ZMOD 3] := by decide
      have ha1 : a ≡ 1 [ZMOD 3] := by
        rw [ha]; simpa using h10.pow (3^k)
      have h3 : (3:ℤ) ∣ (a^2 + a + 1) := by
        have : a^2 + a + 1 ≡ 0 [ZMOD 3] := by
          calc a^2 + a + 1 ≡ 1^2 + 1 + 1 [ZMOD 3] := by
                exact (ha1.pow 2).add (ha1) |>.add_right 1
            _ ≡ 0 [ZMOD 3] := by decide
        exact (Int.modEq_zero_iff_dvd).1 this
      rw [e, factor, pow_succ]
      exact mul_dvd_mul ih h3
  have h1 : (1:ℕ) ≤ 10 ^ (3^k) := Nat.one_le_pow _ _ (by norm_num)
  have : ((3:ℕ)^(k+2) : ℤ) ∣ ((10 ^ (3^k) - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1]
    exact_mod_cast hint
  exact_mod_cast this

lemma ofDigits_replicate_nine (k : ℕ) :
    Nat.ofDigits 10 (List.replicate k 9) + 1 = 10 ^ k := by
  induction k with
  | zero => simp [Nat.ofDigits]
  | succ k ih =>
    rw [List.replicate_succ, show Nat.ofDigits 10 (9 :: List.replicate k 9)
        = 9 + 10 * Nat.ofDigits 10 (List.replicate k 9) from rfl]
    rw [pow_succ]
    omega

lemma reverse_nat_allnines (s : ℕ) (hs : 1 ≤ s) :
    reverse_nat (10 ^ s - 1) = 10 ^ s - 1 := by
  have hV : (10:ℕ) ^ s - 1 = Nat.ofDigits 10 (List.replicate s 9) := by
    have := ofDigits_replicate_nine s; omega
  rw [hV]
  apply reverse_nat_palindrome
  · intro x hx; rw [List.eq_of_mem_replicate hx]; norm_num
  · intro h
    rw [List.eq_of_mem_replicate (List.getLast_mem h)]; norm_num
  · rw [List.reverse_replicate]

/-- Minimality: any valid `m` (positive, divisible together with its reverse) is `≥ V`. -/
lemma valid_ge (j : ℕ) (hj81 : (3:ℕ)^j ∣ 81) (hj2 : 2 ≤ j) (m : ℕ)
    (hm0 : 0 < m) (hm : (3:ℕ)^j ∣ m) (hrev : (3:ℕ)^j ∣ reverse_nat m) :
    10 ^ (3 ^ (j - 2)) - 1 ≤ m := by
  by_contra hlt
  push_neg at hlt
  set s := 3 ^ (j - 2) with hs
  have hms : m < 10 ^ s := by
    have : (10:ℕ) ^ s - 1 < 10 ^ s := by
      have : (1:ℕ) ≤ 10 ^ s := Nat.one_le_pow _ _ (by norm_num)
      omega
    omega
  set L := digits 10 m with hLdef
  have hℓle : L.length ≤ s := (Nat.digits_length_le_iff (by norm_num) m).2 hms
  have hSdvd : (3:ℕ)^j ∣ L.sum := sum_dvd j hj81 m hm0 hm hrev
  have hdig9 : ∀ x ∈ L, x ≤ 9 := fun x hx => by
    have := Nat.digits_lt_base (by norm_num) hx; omega
  have hSle : L.sum ≤ 9 * L.length := by
    have := List.sum_le_card_nsmul L 9 hdig9
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hjeq : 9 * s = 3 ^ j := by
    rw [hs, show (9:ℕ) = 3 ^ 2 from rfl, ← pow_add]
    congr 1; omega
  have hSpos : 0 < L.sum := by
    have hne : m ≠ 0 := by omega
    have hlast := Nat.getLast_digit_ne_zero 10 hne
    have hmem : L.getLast (Nat.digits_ne_nil_iff_ne_zero.2 hne) ∈ L := List.getLast_mem _
    have : 1 ≤ L.getLast (Nat.digits_ne_nil_iff_ne_zero.2 hne) := by
      rcases Nat.eq_zero_or_pos (L.getLast _) with h | h
      · exact absurd h hlast
      · exact h
    calc 0 < L.getLast _ := this
      _ ≤ L.sum := List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
  have hSeq : L.sum = 3 ^ j := by
    have hle2 : L.sum ≤ 3 ^ j := by
      calc L.sum ≤ 9 * L.length := hSle
        _ ≤ 9 * s := by exact Nat.mul_le_mul_left 9 hℓle
        _ = 3 ^ j := hjeq
    have hge := Nat.le_of_dvd hSpos hSdvd
    omega
  have hℓeq : L.length = s := by
    have : 9 * s ≤ 9 * L.length := by rw [← hjeq] at hSeq; omega
    have h2 : s ≤ L.length := Nat.le_of_mul_le_mul_left this (by norm_num)
    omega
  have hsumeq : L.sum = 9 * L.length := by rw [hSeq, hℓeq, hjeq]
  have hall : ∀ x ∈ L, x = 9 := all_eq_of_sum 9 L hdig9 hsumeq
  have hLrep : L = List.replicate L.length 9 :=
    List.eq_replicate_iff.2 ⟨rfl, hall⟩
  have hmval : m = 10 ^ s - 1 := by
    have : m = Nat.ofDigits 10 L := by rw [hLdef, Nat.ofDigits_digits]
    rw [this, hLrep, hℓeq]
    have := ofDigits_replicate_nine s; omega
  omega

lemma a_spec (N : ℕ) (hN : N ≠ 0)
    (h : ∃ k, k > 0 ∧ N ∣ reverse_nat (k * N)) :
    a N = Nat.find h * N := by
  unfold a
  rw [if_neg hN]
  simp only
  rw [dif_pos h]

lemma a_le (N : ℕ) (hN : N ≠ 0) (k : ℕ) (hk0 : 0 < k)
    (hrev : N ∣ reverse_nat (k * N)) :
    a N ≤ k * N := by
  have hex : ∃ k, k > 0 ∧ N ∣ reverse_nat (k * N) := ⟨k, hk0, hrev⟩
  rw [a_spec N hN hex]
  exact Nat.mul_le_mul_right N (Nat.find_le ⟨hk0, hrev⟩)

lemma digits_allnines (s : ℕ) (hs : 1 ≤ s) :
    digits 10 (10 ^ s - 1) = List.replicate s 9 := by
  have hV : (10:ℕ) ^ s - 1 = Nat.ofDigits 10 (List.replicate s 9) := by
    have := ofDigits_replicate_nine s; omega
  rw [hV, Nat.digits_ofDigits 10 (by norm_num)]
  · intro x hx; rw [List.eq_of_mem_replicate hx]; norm_num
  · intro h
    rw [List.eq_of_mem_replicate (List.getLast_mem h)]; norm_num

/-- geometric-sum divisibility over `ℤ`. -/
lemma geom_three_dvd (r : ℤ) (hr : (3:ℤ) ∣ r - 1) (hr1 : r ≠ 1) (j : ℕ) :
    (3:ℤ) ^ j ∣ ∑ i ∈ Finset.range (3 ^ j), r ^ i := by
  induction j with
  | zero => simp
  | succ j ih =>
    set A := ∑ i ∈ Finset.range (3 ^ j), r ^ i with hA
    set B := ∑ i ∈ Finset.range (3 ^ (j + 1)), r ^ i with hB
    have hmulA : A * (r - 1) = r ^ (3 ^ j) - 1 := geom_sum_mul r (3 ^ j)
    have hmulB : B * (r - 1) = r ^ (3 ^ (j + 1)) - 1 := geom_sum_mul r (3 ^ (j + 1))
    have e3 : r ^ (3 ^ (j + 1)) = (r ^ (3 ^ j)) ^ 3 := by rw [← pow_mul, pow_succ]
    set a := r ^ (3 ^ j) with ha
    have hBe : B = A * (a ^ 2 + a + 1) := by
      have hne : (r - 1) ≠ 0 := sub_ne_zero.2 hr1
      apply mul_right_cancel₀ hne
      rw [hmulB, e3]
      have h2 : a ^ 3 - 1 = (A * (r - 1)) * (a ^ 2 + a + 1) := by rw [hmulA]; ring
      rw [h2]; ring
    have ha1 : (3:ℤ) ∣ a - 1 := by
      have hpow := sub_dvd_pow_sub_pow r 1 (3 ^ j)
      simpa [ha, one_pow] using hr.trans hpow
    have h3f : (3:ℤ) ∣ (a ^ 2 + a + 1) := by
      obtain ⟨c, hc⟩ := ha1
      refine ⟨c * (a + 2) + 1, ?_⟩
      have hae : a = 3 * c + 1 := by omega
      rw [hae]; ring
    rw [hBe, pow_succ]
    exact mul_dvd_mul ih h3f

lemma ofDigits_flatten_replicate (b : ℕ) (L : List ℕ) (k : ℕ) :
    Nat.ofDigits b (List.flatten (List.replicate k L))
      = Nat.ofDigits b L * (∑ i ∈ Finset.range k, (b ^ L.length) ^ i) := by
  induction k with
  | zero => simp [Nat.ofDigits]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, ih, geom_sum_succ]
    ring

def blockList : List ℕ :=
  [1,0,0,0,0,0,0,0,1,9,7,9,9,9,9,9,7,9,1,0,0,0,0,0,0,0,1]

lemma mem_flatten_replicate {α : Type*} {x : α} {L : List α} {k : ℕ}
    (h : x ∈ List.flatten (List.replicate k L)) : x ∈ L := by
  rw [List.mem_flatten] at h
  obtain ⟨l, hl, hx⟩ := h
  rwa [List.eq_of_mem_replicate hl] at hx

lemma a_lt_V (n : ℕ) (hn5 : 5 ≤ n) :
    a (3 ^ n) < 10 ^ (3 ^ (n - 2)) - 1 := by
  set N : ℕ := 3 ^ n with hN
  have hN0 : N ≠ 0 := by positivity
  set k : ℕ := 3 ^ (n - 5) with hk
  set joined : List ℕ := List.flatten (List.replicate k blockList) with hjoined
  set W : ℕ := Nat.ofDigits 10 joined with hW
  -- block facts
  have hblen : blockList.length = 27 := by decide
  have hbpal : blockList.reverse = blockList := by decide
  have hblt : ∀ x ∈ blockList, x < 10 := by decide
  have hb243 : (3:ℕ) ^ 5 ∣ Nat.ofDigits 10 blockList := by decide
  have hb0 : (0 : ℕ) ∈ blockList := by decide
  have hblast : blockList.getLast? = some 1 := by decide
  -- length of joined
  have hjlen : joined.length = 3 ^ (n - 2) := by
    rw [hjoined, List.length_flatten, List.map_replicate, List.sum_replicate, hblen,
      smul_eq_mul]
    rw [hk, show (27:ℕ) = 3 ^ 3 from rfl, ← pow_add]
    congr 1; omega
  -- entries < 10
  have hjlt : ∀ x ∈ joined, x < 10 := fun x hx => hblt x (mem_flatten_replicate hx)
  -- nonempty
  have hkpos : 0 < k := by rw [hk]; positivity
  have hjne : joined ≠ [] := by
    rw [hjoined]
    intro hcon
    have : joined.length = 0 := by rw [hjoined, hcon]; rfl
    rw [hjlen] at this; simp at this
  -- last entry nonzero
  have hjlast : ∀ h : joined ≠ [], joined.getLast h ≠ 0 := by
    intro h
    have hg : joined.getLast? = some 1 := by
      rw [hjoined, List.getLast?_flatten_replicate (by omega) blockList, hblast]
    have hge := List.getLast?_eq_some_getLast h
    rw [hg] at hge
    intro hc; rw [hc] at hge; simp at hge
  -- palindrome
  have hjpal : joined.reverse = joined := by
    rw [hjoined, List.reverse_flatten, List.map_replicate, List.reverse_replicate, hbpal]
  -- reverse_nat W = W
  have hrevW : reverse_nat W = W := by
    rw [hW]; exact reverse_nat_palindrome joined hjlt hjlast hjpal
  -- divisibility 3^n | W
  have hWfac : W = Nat.ofDigits 10 blockList * (∑ i ∈ Finset.range k, (10 ^ 27) ^ i) := by
    rw [hW, hjoined, ofDigits_flatten_replicate, hblen]
  have hGdvd : (3:ℕ) ^ (n - 5) ∣ (∑ i ∈ Finset.range k, (10 ^ 27) ^ i) := by
    have hint : (3:ℤ) ^ (n - 5) ∣ ∑ i ∈ Finset.range (3 ^ (n - 5)), ((10:ℤ) ^ 27) ^ i := by
      apply geom_three_dvd
      · decide
      · norm_num
    rw [hk]
    have hcast : ((∑ i ∈ Finset.range (3 ^ (n - 5)), ((10:ℕ) ^ 27) ^ i : ℕ) : ℤ)
        = ∑ i ∈ Finset.range (3 ^ (n - 5)), ((10:ℤ) ^ 27) ^ i := by push_cast; ring
    have : ((3:ℕ) ^ (n - 5) : ℤ) ∣ ((∑ i ∈ Finset.range (3 ^ (n - 5)), ((10:ℕ) ^ 27) ^ i : ℕ) : ℤ) := by
      rw [hcast]; exact_mod_cast hint
    exact_mod_cast this
  have hWdvd : N ∣ W := by
    rw [hN, hWfac, show n = 5 + (n - 5) from by omega, pow_add]
    exact mul_dvd_mul hb243 hGdvd
  have hWpos : 0 < W := by
    rw [hWfac]
    have hB0 : 0 < Nat.ofDigits 10 blockList := by decide
    have hG0 : 0 < ∑ i ∈ Finset.range k, (10 ^ 27) ^ i := by
      apply Finset.sum_pos
      · intro i _; positivity
      · exact ⟨0, Finset.mem_range.2 hkpos⟩
    exact Nat.mul_pos hB0 hG0
  -- W < V
  have hWlt10 : W < 10 ^ (3 ^ (n - 2)) := by
    rw [hW, ← hjlen]
    exact Nat.ofDigits_lt_base_pow_length (by norm_num) hjlt
  have hVpos : 1 ≤ (10:ℕ) ^ (3 ^ (n - 2)) := Nat.one_le_pow _ _ (by norm_num)
  have hWleV : W ≤ 10 ^ (3 ^ (n - 2)) - 1 := by omega
  have hWneV : W ≠ 10 ^ (3 ^ (n - 2)) - 1 := by
    intro hc
    have hdW : digits 10 W = joined := by
      rw [hW, Nat.digits_ofDigits 10 (by norm_num) joined hjlt hjlast]
    have hdV : digits 10 (10 ^ (3 ^ (n - 2)) - 1) = List.replicate (3 ^ (n - 2)) 9 :=
      digits_allnines _ (Nat.one_le_pow _ _ (by norm_num))
    rw [hc, hdV] at hdW
    -- joined = replicate ... 9, but 0 ∈ joined
    have h0j : (0:ℕ) ∈ joined := by
      rw [hjoined]
      exact List.mem_flatten.2 ⟨blockList, List.mem_replicate.2 ⟨by omega, rfl⟩, hb0⟩
    rw [← hdW] at h0j
    rw [List.mem_replicate] at h0j
    omega
  have hWV : W < 10 ^ (3 ^ (n - 2)) - 1 := lt_of_le_of_ne hWleV hWneV
  -- a (3^n) ≤ W
  have hkW : 0 < W / N := Nat.div_pos (Nat.le_of_dvd hWpos hWdvd) (Nat.pos_of_ne_zero hN0)
  have hWmul : W / N * N = W := Nat.div_mul_cancel hWdvd
  have haW : a N ≤ W := by
    have := a_le N hN0 (W / N) hkW (by rw [hWmul, hrevW]; exact hWdvd)
    rw [hWmul] at this; exact this
  omega

lemma a_eq_V (n : ℕ) (hn2 : 2 ≤ n) (hn81 : (3:ℕ)^n ∣ 81) :
    a (3 ^ n) = 10 ^ (3 ^ (n - 2)) - 1 := by
  set N : ℕ := 3 ^ n with hN
  set V : ℕ := 10 ^ (3 ^ (n - 2)) - 1 with hVdef
  have hN0 : N ≠ 0 := by positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  -- N divides V
  have hNV : N ∣ V := by
    have := three_dvd_geom (n - 2)
    rw [Nat.sub_add_cancel hn2] at this
    exact this
  have hVpos : 0 < V := by
    rw [hVdef]
    have h1 : (10:ℕ) ≤ 10 ^ (3 ^ (n - 2)) :=
      Nat.le_self_pow (by positivity) 10
    omega
  have hrevV : reverse_nat V = V := by
    rw [hVdef]; exact reverse_nat_allnines _ (Nat.one_le_pow _ _ (by norm_num))
  have hk0 : V / N > 0 ∧ N ∣ reverse_nat (V / N * N) := by
    have hmul : V / N * N = V := Nat.div_mul_cancel hNV
    refine ⟨Nat.div_pos (Nat.le_of_dvd hVpos hNV) hNpos, ?_⟩
    rw [hmul, hrevV]; exact hNV
  have hex : ∃ k, k > 0 ∧ N ∣ reverse_nat (k * N) := ⟨V / N, hk0⟩
  rw [a_spec N hN0 hex]
  -- minimality
  set k := Nat.find hex with hkdef
  have hspec : k > 0 ∧ N ∣ reverse_nat (k * N) := Nat.find_spec hex
  have hkpos : 0 < k := hspec.1
  have hmpos : 0 < k * N := Nat.mul_pos hkpos hNpos
  have hmdvd : N ∣ k * N := Dvd.intro_left k rfl
  have hrev : N ∣ reverse_nat (k * N) := hspec.2
  have hge : V ≤ k * N := by
    have := valid_ge n hn81 hn2 (k * N) hmpos hmdvd hrev
    rw [hVdef]; exact this
  have hle : k * N ≤ V := by
    have hkle : k ≤ V / N := Nat.find_le hk0
    calc k * N ≤ (V / N) * N := Nat.mul_le_mul_right N hkle
      _ = V := Nat.div_mul_cancel hNV
  omega


end A062567

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
    obtain ⟨h2, h3, h4⟩ := hcon
    have hn5 : 5 ≤ n := by omega
    have := A062567.a_lt_V n hn5
    omega
  · intro h
    rcases h with rfl | rfl | rfl
    · exact A062567.a_eq_V 2 (by norm_num) (by norm_num)
    · exact A062567.a_eq_V 3 (by norm_num) (by norm_num)
    · exact A062567.a_eq_V 4 (by norm_num) (by norm_num)
