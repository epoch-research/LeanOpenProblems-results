import FormalConjectures.Util.ProblemImports

open Nat

/--
A030101: The number whose binary expansion is the reversal of the binary expansion of $n$.
This is computed by taking the list of digits of $n$ in base 2 (LSB first), reversing the list, and interpreting the result as a number.
-/
def A030101 (n : ℕ) : ℕ := Nat.ofDigits 2 (List.reverse (Nat.digits 2 n))
/--
A339602: $a(n) = (a(n-2) \oplus A030101(a(n-1))) + 1$, $a(0) = 0$, $a(1) = 1$.
-/
def a : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => (a n).xor (A030101 (a (n + 1))) + 1
termination_by n => n
theorem a_succ_succ (n : ℕ) : a (n + 2) = (a n).xor (A030101 (a (n + 1))) + 1 := by simp only [a]
def len (v : ℕ) : ℕ := (Nat.digits 2 v).length

-- length lemmas
theorem val_lt (v : ℕ) : v < 2 ^ (len v) := by
  conv_lhs => rw [← Nat.ofDigits_digits 2 v]
  exact Nat.ofDigits_lt_base_pow_length (by norm_num) (fun d hd => Nat.digits_lt_base (by norm_num) hd)
theorem rev_lt (v : ℕ) : A030101 v < 2 ^ (len v) := by
  unfold A030101 len
  have : (Nat.digits 2 v).length = (List.reverse (Nat.digits 2 v)).length := (List.length_reverse).symm
  rw [this]
  exact Nat.ofDigits_lt_base_pow_length (by norm_num) (fun d hd => Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hd))
theorem le_val (v : ℕ) (hv : v ≠ 0) : 2 ^ (len v - 1) ≤ v := by
  have hlen : len v = Nat.log 2 v + 1 := Nat.digits_len 2 v (by norm_num) hv
  rw [hlen]; simp only [Nat.add_sub_cancel]; exact Nat.pow_log_le_self 2 hv
theorem rev_even_lt (v : ℕ) (hv : v ≠ 0) (he : v % 2 = 0) : A030101 v < 2 ^ (len v - 1) := by
  unfold A030101 len
  have hd : Nat.digits 2 v = 0 :: Nat.digits 2 (v / 2) := by
    rw [Nat.digits_def' (b := 2) (by norm_num) (Nat.pos_of_ne_zero hv), he]
  rw [hd]; simp only [List.reverse_cons, List.length_cons]
  rw [Nat.ofDigits_append]
  have h0 : Nat.ofDigits 2 [(0:ℕ)] = 0 := by simp [Nat.ofDigits]
  rw [h0, mul_zero, add_zero, Nat.add_sub_cancel, ← List.length_reverse]
  exact Nat.ofDigits_lt_base_pow_length (b := 2) (by norm_num) (fun d hd2 => Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hd2))
theorem len_le_iff (v m : ℕ) : len v ≤ m ↔ v < 2 ^ m := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp [len]
  · unfold len; rw [Nat.digits_len 2 v (by norm_num) h, Nat.lt_pow_iff_log_lt (by norm_num) h]; omega
theorem len_le (v m : ℕ) (h : v < 2 ^ m) : len v ≤ m := (len_le_iff v m).mpr h
theorem lt_len (v m : ℕ) (h : 2 ^ m ≤ v) : m < len v := by
  by_contra hc; push_neg at hc; have := (len_le_iff v m).mp hc; omega
theorem xor_ge (m x y : ℕ) (h1 : 2^m ≤ x) (h2 : x < 2^(m+1)) (hy : y < 2^m) : 2^m ≤ x ^^^ y := by
  apply Nat.ge_two_pow_of_testBit; rw [Nat.testBit_xor]
  have hx : x.testBit m = true := by
    have hb : x - 2^m < 2^m := by rw [pow_succ] at h2; omega
    have hxe : x = 2^m * 1 + (x - 2^m) := by omega
    rw [hxe, Nat.testBit_two_pow_mul_add _ hb]; simp
  have hy2 : y.testBit m = false := by
    have : y = 2^m * 0 + y := by ring
    rw [this, Nat.testBit_two_pow_mul_add _ hy]; simp
  rw [hx, hy2]; rfl

-- lower bound on len for even positive numbers: len ≥ 2
theorem len_ge_two_even (v : ℕ) (hv : v ≠ 0) (he : v % 2 = 0) : 2 ≤ len v := by
  have : 2 ≤ v := by omega
  have := lt_len v 1 (by simpa using this); omega

theorem S_step (n : ℕ) (hev : a (n+1) % 2 = 0) (hpos : a (n+1) ≠ 0)
    (hodd : a (n+2) % 2 = 1) (hlt : len (a n) < len (a (n+1))) :
    len (a (n+2)) < len (a (n+1)) := by
  set L := len (a (n+1)) with hL
  have hL2 : 2 ≤ L := len_ge_two_even _ hpos hev
  have han : a n < 2 ^ (L - 1) := by
    have : a n < 2 ^ (len (a n)) := val_lt _
    have hle : 2 ^ (len (a n)) ≤ 2 ^ (L-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrev : A030101 (a (n+1)) < 2 ^ (L - 1) := rev_even_lt _ hpos hev
  have hxor : (a n) ^^^ (A030101 (a (n+1))) < 2 ^ (L-1) := Nat.xor_lt_two_pow han hrev
  have hxeq : (a n).xor (A030101 (a (n+1))) = a n ^^^ A030101 (a (n+1)) := rfl
  have hval : a (n+2) ≤ 2 ^ (L-1) := by rw [a_succ_succ, hxeq]; omega
  have hne : a (n+2) ≠ 2 ^ (L-1) := by
    intro hcon
    have hdvd : 2 ∣ 2 ^ (L-1) := dvd_pow_self 2 (by omega)
    omega
  have : a (n+2) < 2 ^ (L-1) := lt_of_le_of_ne hval hne
  have := len_le _ _ this; omega

theorem M_step (n : ℕ) (hev : a n % 2 = 0) (hpos : a n ≠ 0)
    (hlt : len (a (n+1)) < len (a n)) : len (a n) ≤ len (a (n+2)) := by
  set L := len (a n) with hL
  have hL2 : 2 ≤ L := len_ge_two_even _ hpos hev
  have hge : 2 ^ (L-1) ≤ a n := le_val _ hpos
  have hlt2 : a n < 2 ^ (L-1+1) := by
    have : a n < 2 ^ L := val_lt _
    have : L - 1 + 1 = L := by omega
    rw [this]; exact val_lt _
  have hrev : A030101 (a (n+1)) < 2 ^ (L-1) := by
    have h1 : A030101 (a (n+1)) < 2 ^ (len (a (n+1))) := rev_lt _
    have h2 : 2 ^ (len (a (n+1))) ≤ 2 ^ (L-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hxor : 2 ^ (L-1) ≤ (a n) ^^^ (A030101 (a (n+1))) := xor_ge _ _ _ hge hlt2 hrev
  have hxeq : (a n).xor (A030101 (a (n+1))) = a n ^^^ A030101 (a (n+1)) := rfl
  have hval : 2 ^ (L-1) ≤ a (n+2) := by rw [a_succ_succ, hxeq]; omega
  have := lt_len _ _ hval; omega

-- parity infrastructure
theorem a_pos : ∀ n, 1 ≤ a (n + 1) := by
  intro n; match n with
  | 0 => simp [a]
  | (k + 1) => simp [a]
theorem ofDigits_two_mod (L : List ℕ) : Nat.ofDigits 2 L % 2 = (L.headI) % 2 := by
  cases L with
  | nil => simp [Nat.ofDigits]
  | cons d t => simp [Nat.ofDigits, Nat.add_mul_mod_self_left]
theorem A030101_odd (m : ℕ) (hm : m ≠ 0) : A030101 m % 2 = 1 := by
  unfold A030101; rw [ofDigits_two_mod]
  have hne : Nat.digits 2 m ≠ [] := (Nat.digits_ne_nil_iff_ne_zero).mpr hm
  obtain ⟨e, rest, hrev⟩ : ∃ e rest, (Nat.digits 2 m).reverse = e :: rest := by
    cases h : (Nat.digits 2 m).reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp h) hne
    | cons e rest => exact ⟨e, rest, rfl⟩
  have hlast : (Nat.digits 2 m).getLast? = some e := by rw [← List.head?_reverse, hrev]; rfl
  have he : e = (Nat.digits 2 m).getLast hne := by
    rw [List.getLast?_eq_some_getLast hne] at hlast; exact (Option.some_inj).mp hlast.symm
  have hlt : (Nat.digits 2 m).getLast hne < 2 := Nat.digits_lt_base (by norm_num) (List.getLast_mem hne)
  have hnz : (Nat.digits 2 m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 hm
  rw [hrev]; simp only [List.headI]; rw [he]; omega
theorem xor_mod_two (x y : ℕ) : (x.xor y) % 2 = (x % 2 + y % 2) % 2 := by
  show (x ^^^ y) % 2 = (x % 2 + y % 2) % 2
  have h := Nat.testBit_xor x y 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one (x ^^^ y) with hz | hz <;>
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
    rw [hz, hx, hy] at h ⊢ <;> revert h <;> decide
theorem a_parity : ∀ n, a n % 2 = n % 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [a]
    | 1 => simp [a]
    | (k + 2) =>
      rw [a_succ_succ]
      have hk : a k % 2 = k % 2 := ih k (by omega)
      have hpos : a (k + 1) ≠ 0 := by have := a_pos k; omega
      have hodd : A030101 (a (k + 1)) % 2 = 1 := A030101_odd _ hpos
      rw [Nat.add_mod, xor_mod_two, hk, hodd]; omega

-- base values
theorem a0 : a 0 = 0 := by simp only [a]
theorem a1 : a 1 = 1 := by simp only [a]
theorem dig1 : Nat.digits 2 1 = [1] := by simp
theorem dig2 : Nat.digits 2 2 = [0,1] := by rw [Nat.digits_def' (by norm_num) (by norm_num)]; norm_num
theorem dig4 : Nat.digits 2 4 = [0,0,1] := by
  rw [Nat.digits_def' (by norm_num) (by norm_num)]; norm_num [Nat.digits_def' (show 1<2 by norm_num) (show 0<2 by norm_num)]
theorem A1 : A030101 1 = 1 := by unfold A030101; rw [dig1]; rfl
theorem A2 : A030101 2 = 1 := by unfold A030101; rw [dig2]; decide
theorem a2 : a 2 = 2 := by rw [show (2:ℕ)=0+2 from rfl, a_succ_succ, a0, a1, A1]; decide
theorem a3 : a 3 = 1 := by rw [show (3:ℕ)=1+2 from rfl, a_succ_succ, a1, a2, A2]; decide
theorem a4 : a 4 = 4 := by rw [show (4:ℕ)=2+2 from rfl, a_succ_succ, a2, a3, A1]; decide
theorem len1 : len 1 = 1 := by unfold len; rw [dig1]; rfl
theorem len2 : len 2 = 2 := by unfold len; rw [dig2]; rfl
theorem len4 : len 4 = 3 := by unfold len; rw [dig4]; rfl

-- Joint S/M induction
theorem SM : ∀ k, 1 ≤ k →
    len (a (2*k+1)) < len (a (2*k)) ∧ len (a (2*k)) ≤ len (a (2*k+2)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨?_, ?_⟩
    · show len (a 3) < len (a 2); rw [a2, a3, len1, len2]; norm_num
    · show len (a 2) ≤ len (a 4); rw [a2, a4, len2, len4]; norm_num
  | succ k hk ih =>
    obtain ⟨ihS, ihM⟩ := ih
    have hevn : a (2*k+2) % 2 = 0 := by rw [a_parity]; omega
    have hpos2 : a (2*k+2) ≠ 0 := by have := a_pos (2*k+1); rw [show 2*k+1+1 = 2*k+2 from rfl] at this; omega
    have hodd3 : a (2*k+3) % 2 = 1 := by rw [a_parity]; omega
    -- S at k+1
    have hSarg : len (a (2*k+1)) < len (a (2*k+2)) := lt_of_lt_of_le ihS ihM
    have hSnew : len (a (2*k+3)) < len (a (2*k+2)) := by
      have := S_step (2*k+1) (by rw [show 2*k+1+1 = 2*k+2 from rfl]; exact hevn)
        (by rw [show 2*k+1+1 = 2*k+2 from rfl]; exact hpos2)
        (by rw [show 2*k+1+2 = 2*k+3 from rfl]; exact hodd3)
        (by rw [show 2*k+1+1 = 2*k+2 from rfl]; exact hSarg)
      rw [show 2*k+1+2 = 2*k+3 from rfl, show 2*k+1+1 = 2*k+2 from rfl] at this
      exact this
    -- M at k+1
    have hMnew : len (a (2*k+2)) ≤ len (a (2*k+4)) := by
      have := M_step (2*k+2) hevn hpos2
        (by rw [show 2*k+2+1 = 2*k+3 from rfl]; exact hSnew)
      rw [show 2*k+2+2 = 2*k+4 from rfl] at this
      exact this
    refine ⟨?_, ?_⟩
    · have e1 : 2*(k+1)+1 = 2*k+3 := by ring
      have e2 : 2*(k+1) = 2*k+2 := by ring
      show len (a (2*(k+1)+1)) < len (a (2*(k+1)))
      rw [e1, e2]; exact hSnew
    · have e1 : 2*(k+1) = 2*k+2 := by ring
      have e2 : 2*(k+1)+2 = 2*k+4 := by ring
      show len (a (2*(k+1))) ≤ len (a (2*(k+1)+2))
      rw [e2, e1]; exact hMnew

-- backward determinism
theorem back_det (n : ℕ) : a n = (a (n+2) - 1) ^^^ A030101 (a (n+1)) := by
  have h := a_succ_succ n
  have hx : (a n).xor (A030101 (a (n+1))) = a n ^^^ A030101 (a (n+1)) := rfl
  rw [hx] at h
  have hs : a (n+2) - 1 = a n ^^^ A030101 (a (n+1)) := by omega
  rw [hs, Nat.xor_xor_cancel_right]

theorem back_step (k k' : ℕ) (h1 : a (k+1) = a (k'+1)) (h2 : a (k+2) = a (k'+2)) :
    a k = a k' := by rw [back_det k, back_det k', h1, h2]

theorem state_inj : ∀ n1 n2, a n1 = a n2 → a (n1+1) = a (n2+1) → n1 = n2 := by
  intro n1
  induction n1 with
  | zero =>
    intro n2 h0 h1
    rw [a0] at h0
    cases n2 with
    | zero => rfl
    | succ m => exfalso; have := a_pos m; omega
  | succ k ih =>
    intro n2 h0 h1
    cases n2 with
    | zero => exfalso; rw [a0] at h0; have := a_pos k; omega
    | succ m =>
      have hb : a k = a m := back_step k m h0 h1
      have : k = m := ih m hb h0
      rw [this]

theorem occ_bound (w n : ℕ) (hw : w % 2 = 0) (hw0 : w ≠ 0) (hn : a n = w) :
    a (n+1) < 2 ^ (len w - 1) := by
  have hpar : a n % 2 = n % 2 := a_parity n
  rw [hn] at hpar
  have hne : n ≠ 0 := by intro h; rw [h, a0] at hn; omega
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n/2, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hSM := (SM k hk1).1
  rw [← hk] at hSM
  rw [hn] at hSM
  have h1 : a (n+1) < 2^(len (a (n+1))) := val_lt _
  have h2 : len (a (n+1)) ≤ len w - 1 := by omega
  have h3 : 2^(len (a (n+1))) ≤ 2^(len w - 1) := Nat.pow_le_pow_right (by norm_num) h2
  omega

theorem count_bounded (p : ℕ) (hp : p % 2 = 1) :
    ∃ B, ∀ N, (Finset.filter (fun n => a n = p + 1) (Finset.range N)).card ≤ B := by
  refine ⟨2 ^ (len (p+1) - 1), fun N => ?_⟩
  have := Finset.card_le_card_of_injOn (s := Finset.filter (fun n => a n = p + 1) (Finset.range N))
    (t := Finset.range (2 ^ (len (p+1) - 1))) (f := fun n => a (n+1)) ?_ ?_
  · simpa using this
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact occ_bound (p+1) n (by omega) (by omega) hn.2
  · intro n1 hn1 n2 hn2 heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn1 hn2
    exact state_inj n1 n2 (by rw [hn1.2, hn2.2]) heq


open Finset

/-- **(B')** count of the odd value `p` is unbounded.

This is the crux of the conjecture: every odd value recurs infinitely often. It is a
recurrence/equidistribution property of the chaotic bit-reversal dynamical system and is
left as the single remaining lemma. -/
theorem count_unbounded (p : ℕ) (hp : p % 2 = 1) :
    ∀ M, ∃ N, M < (Finset.filter (fun n : ℕ => a n = p) (Finset.range N)).card := by
  sorry

/--
Conjecture: Let p be an odd number, then a(n) = p will be more frequently found in this sequence than a(n) = p+1.
This is formalized as: for any odd p, the count of p in the sequence up to index N eventually always exceeds the count of p+1.
-/
theorem oeis_339602_conjecture_1 (p : ℕ) (hp_odd : p % 2 = 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (filter (fun n : ℕ => a n = p) (range N)).card > (filter (fun n : ℕ => a n = p + 1) (range N)).card := by
  obtain ⟨B, hB⟩ := count_bounded p hp_odd
  obtain ⟨N₀, hN₀⟩ := count_unbounded p hp_odd B
  refine ⟨N₀, fun N hN => ?_⟩
  calc (filter (fun n : ℕ => a n = p + 1) (range N)).card
        ≤ B := hB N
    _ < (filter (fun n : ℕ => a n = p) (range N₀)).card := hN₀
    _ ≤ (filter (fun n : ℕ => a n = p) (range N)).card :=
        card_le_card (filter_subset_filter _ (Finset.range_mono hN))
