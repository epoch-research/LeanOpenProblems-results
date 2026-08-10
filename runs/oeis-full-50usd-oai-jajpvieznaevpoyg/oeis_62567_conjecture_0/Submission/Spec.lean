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



private lemma a_eq_of_min (N w : ℕ) (hN : N ≠ 0)
    (hw : w > 0 ∧ N ∣ reverse_nat (w * N))
    (hmin : ∀ k, k > 0 → N ∣ reverse_nat (k * N) → w ≤ k) : a N = w * N := by
  unfold a
  simp [hN]
  let P : ℕ → Prop := fun k => k > 0 ∧ N ∣ reverse_nat (k * N)
  have hex : ∃ k, P k := ⟨w, hw⟩
  simp [P, hex]
  have hfind : Nat.find hex = w := by
    apply le_antisymm
    · exact Nat.find_min' hex hw
    · exact hmin _ (Nat.find_spec hex).1 (Nat.find_spec hex).2
  simp [hfind]

private lemma a_le_of_witness (N k : ℕ) (hN : N ≠ 0)
    (hk : k > 0 ∧ N ∣ reverse_nat (k * N)) : a N ≤ k * N := by
  unfold a
  simp [hN]
  let P : ℕ → Prop := fun k => k > 0 ∧ N ∣ reverse_nat (k * N)
  have hex : ∃ j, P j := ⟨k, hk⟩
  simp [P, hex]
  exact Nat.mul_le_mul_right N (Nat.find_min' hex hk)


private lemma digits9 : digits 10 9 = [9] := by
  rw [← digits_ofDigits 10 (by norm_num : 1 < 10) [9]]
  · norm_num [ofDigits]
  · intro l hl; simp at hl; omega
  · intro h; simp

private lemma reverse9 : reverse_nat 9 = 9 := by
  unfold reverse_nat
  rw [digits9]
  norm_num [ofDigits]

private lemma digits999 : digits 10 999 = [9,9,9] := by
  rw [← digits_ofDigits 10 (by norm_num : 1 < 10) [9,9,9]]
  · norm_num [ofDigits]
  · intro l hl; simp at hl; omega
  · intro h; simp

private lemma reverse999 : reverse_nat 999 = 999 := by
  unfold reverse_nat
  rw [digits999]
  norm_num [ofDigits]

private lemma digits999999999 : digits 10 999999999 = [9,9,9,9,9,9,9,9,9] := by
  rw [← digits_ofDigits 10 (by norm_num : 1 < 10) [9,9,9,9,9,9,9,9,9]]
  · norm_num [ofDigits]
  · intro l hl; simp at hl; omega
  · intro h; simp

private lemma reverse999999999 : reverse_nat 999999999 = 999999999 := by
  unfold reverse_nat
  rw [digits999999999]
  norm_num [ofDigits]

private lemma a9 : a 9 = 9 := by
  apply a_eq_of_min 9 1 (by norm_num)
  · rw [show 1 * 9 = 9 by norm_num, reverse9]
    norm_num
  · intro k hkpos hkdvd
    omega

private def block : List ℕ := [7,8,9,9,9,9,9,9,8,4]
private def blockR : List ℕ := block.reverse

private def repBlock : ℕ → List ℕ
  | 0 => []
  | q + 1 => block ++ repBlock q

private def repBlockR : ℕ → List ℕ
  | 0 => []
  | q + 1 => blockR ++ repBlockR q

private def W (t : ℕ) : ℕ := ofDigits 10 (repBlock (3^t))
private def WR (t : ℕ) : ℕ := ofDigits 10 (repBlockR (3^t))

private lemma mem_repBlock {x q : ℕ} (h : x ∈ repBlock q) : x < 10 := by
  revert x
  induction q with
  | zero => intro x h; simp [repBlock] at h
  | succ q ih =>
    intro x h
    have hs : x ∈ block ∨ x ∈ repBlock q := by
      simpa [repBlock] using (List.mem_append.mp (by simpa [repBlock] using h))
    rcases hs with hb | hr
    · simp [block] at hb
      omega
    · exact ih hr

private lemma mem_repBlockR {x q : ℕ} (h : x ∈ repBlockR q) : x < 10 := by
  revert x
  induction q with
  | zero => intro x h; simp [repBlockR] at h
  | succ q ih =>
    intro x h
    have hs : x ∈ blockR ∨ x ∈ repBlockR q := by
      simpa [repBlockR] using (List.mem_append.mp (by simpa [repBlockR] using h))
    rcases hs with hb | hr
    · simp [blockR, block] at hb
      omega
    · exact ih hr

private lemma last_repBlock_ne_zero {q : ℕ} (hq : q ≠ 0) (h : repBlock q ≠ []) :
    (repBlock q).getLast h ≠ 0 := by
  induction q with
  | zero => contradiction
  | succ q ih =>
    cases q with
    | zero => simp [repBlock, block]
    | succ q =>
      simp [repBlock]
      exact ih (by omega) (by simp [repBlock, block])

private lemma last_repBlockR_ne_zero {q : ℕ} (hq : q ≠ 0) (h : repBlockR q ≠ []) :
    (repBlockR q).getLast h ≠ 0 := by
  induction q with
  | zero => contradiction
  | succ q ih =>
    cases q with
    | zero => simp [repBlockR, blockR, block]
    | succ q =>
      simp [repBlockR]
      exact ih (by omega) (by simp [repBlockR, blockR, block])

private lemma digits_W (t : ℕ) : digits 10 (W t) = repBlock (3^t) := by
  unfold W
  apply digits_ofDigits
  · norm_num
  · intro l hl; exact mem_repBlock hl
  · intro h; exact last_repBlock_ne_zero (by positivity) h

private lemma repBlockR_append_blockR (q : ℕ) : repBlockR q ++ blockR = blockR ++ repBlockR q := by
  induction q with
  | zero => simp [repBlockR]
  | succ q ih =>
    rw [repBlockR, List.append_assoc, ih]


private lemma reverse_repBlock (q : ℕ) : (repBlock q).reverse = repBlockR q := by
  induction q with
  | zero => simp [repBlock, repBlockR]
  | succ q ih =>
    rw [repBlock, List.reverse_append, ih]
    change repBlockR q ++ blockR = repBlockR (q + 1)
    rw [repBlockR, repBlockR_append_blockR]

private lemma reverse_W (t : ℕ) : reverse_nat (W t) = WR t := by
  unfold reverse_nat WR
  rw [digits_W, reverse_repBlock]

private lemma length_block : block.length = 10 := by rfl
private lemma length_blockR : blockR.length = 10 := by rfl

private lemma repBlock_add (a b : ℕ) : repBlock (a + b) = repBlock a ++ repBlock b := by
  induction a with
  | zero => simp [repBlock]
  | succ a ih =>
    simp [Nat.succ_add, repBlock, ih, List.append_assoc]

private lemma repBlockR_add (a b : ℕ) : repBlockR (a + b) = repBlockR a ++ repBlockR b := by
  induction a with
  | zero => simp [repBlockR]
  | succ a ih =>
    simp [Nat.succ_add, repBlockR, ih, List.append_assoc]

private lemma length_repBlock (q : ℕ) : (repBlock q).length = 10 * q := by
  induction q with
  | zero => simp [repBlock]
  | succ q ih =>
    rw [repBlock, List.length_append, ih, length_block]
    ring

private lemma length_repBlockR (q : ℕ) : (repBlockR q).length = 10 * q := by
  induction q with
  | zero => simp [repBlockR]
  | succ q ih =>
    rw [repBlockR, List.length_append, ih, length_blockR]
    ring

private lemma W_succ (t : ℕ) :
    W (t+1) = W t * (1 + 10^(10*3^t) + (10^(10*3^t))^2) := by
  unfold W
  have hpow : 3^(t+1) = 3^t + (3^t + 3^t) := by ring
  rw [hpow, repBlock_add, repBlock_add]
  rw [ofDigits_append, ofDigits_append]
  simp [length_repBlock]
  ring

private lemma WR_succ (t : ℕ) :
    WR (t+1) = WR t * (1 + 10^(10*3^t) + (10^(10*3^t))^2) := by
  unfold WR
  have hpow : 3^(t+1) = 3^t + (3^t + 3^t) := by ring
  rw [hpow, repBlockR_add, repBlockR_add]
  rw [ofDigits_append, ofDigits_append]
  simp [length_repBlockR]
  ring

private lemma ten_pow_mod3 (m : ℕ) : 10^m % 3 = 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ]
    omega

private lemma factor_dvd3 (m : ℕ) : 3 ∣ (1 + 10^m + (10^m)^2) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have h : 10^m % 3 = 1 := ten_pow_mod3 m
  have h2 : ((10^m)^2) % 3 = 1 := by rw [pow_two, Nat.mul_mod, h]
  simp [Nat.add_mod, h, h2]

private lemma pow3_dvd_W (t : ℕ) : 3^(t+5) ∣ W t := by
  induction t with
  | zero =>
    unfold W repBlock block
    change 243 ∣ 4899999987
    norm_num
  | succ t ih =>
    rw [W_succ]
    have hf : 3 ∣ (1 + 10 ^ (10 * 3 ^ t) + (10 ^ (10 * 3 ^ t)) ^ 2) := factor_dvd3 (10*3^t)
    have hmul : 3^(t+5) * 3 ∣ W t * (1 + 10 ^ (10 * 3 ^ t) + (10 ^ (10 * 3 ^ t)) ^ 2) := Nat.mul_dvd_mul ih hf
    convert hmul using 1

private lemma pow3_dvd_WR (t : ℕ) : 3^(t+5) ∣ WR t := by
  induction t with
  | zero =>
    unfold WR repBlockR blockR block
    change 243 ∣ 7899999984
    norm_num
  | succ t ih =>
    rw [WR_succ]
    have hf : 3 ∣ (1 + 10 ^ (10 * 3 ^ t) + (10 ^ (10 * 3 ^ t)) ^ 2) := factor_dvd3 (10*3^t)
    have hmul : 3^(t+5) * 3 ∣ WR t * (1 + 10 ^ (10 * 3 ^ t) + (10 ^ (10 * 3 ^ t)) ^ 2) := Nat.mul_dvd_mul ih hf
    convert hmul using 1

private lemma W_pos (t : ℕ) : 0 < W t := by
  unfold W
  have hp : 3^t ≠ 0 := by positivity
  cases hq : 3^t with
  | zero => contradiction
  | succ q =>
    simp [repBlock, block, ofDigits]

private lemma W_lt_pow (t : ℕ) : W t < 10 ^ (10 * 3^t) := by
  unfold W
  rw [← length_repBlock (3^t)]
  apply ofDigits_lt_base_pow_length
  · norm_num
  · intro x hx; exact mem_repBlock hx

private lemma a_pow3_le_W (t : ℕ) : a (3^(t+5)) ≤ W t := by
  obtain ⟨k, hk⟩ := pow3_dvd_W t
  have hkpos : k > 0 := by
    have hpos := W_pos t
    rw [hk] at hpos
    have hp : 0 < 3^(t+5) := by positivity
    nlinarith
  have hmul : k * 3^(t+5) = W t := by rw [hk, mul_comm]
  have hwit : k > 0 ∧ 3^(t+5) ∣ reverse_nat (k * 3^(t+5)) := by
    refine ⟨hkpos, ?_⟩
    rw [hmul, reverse_W]
    exact pow3_dvd_WR t
  simpa [hmul] using a_le_of_witness (3^(t+5)) k (by positivity) hwit

private lemma W_lt_rhs (t : ℕ) : W t < 10 ^ (3 ^ (t+3)) - 1 := by
  have hW := W_lt_pow t
  have hpos : 0 < 10 ^ (3 ^ (t+3)) := by positivity
  have hexp : 10 * 3^t < 3^(t+3) := by
    have h3 : 3^(t+3) = 27 * 3^t := by ring
    rw [h3]
    have hp : 0 < 3^t := by positivity
    nlinarith
  have hpowlt : 10 ^ (10 * 3^t) < 10 ^ (3^(t+3)) := by
    exact Nat.pow_lt_pow_right (by norm_num) hexp
  omega


private lemma dvd_padded_reverse {N l m : ℕ} (h : N ∣ reverse_nat m) :
    N ∣ ofDigits 10 (digitsAppend 10 l m).reverse := by
  unfold reverse_nat at h
  unfold digitsAppend
  rw [List.reverse_append, List.reverse_replicate, ofDigits_append, ofDigits_replicate_zero, zero_add]
  exact dvd_mul_of_dvd_right h _

private lemma explicit3_all9 (d0 d1 d2 : ℕ) (h0 : d0 < 10) (h1 : d1 < 10) (h2 : d2 < 10)
    (hSpos : 0 < d0 + d1 + d2)
    (hA : 27 ∣ ofDigits 10 [d0,d1,d2])
    (hB : 27 ∣ ofDigits 10 (List.reverse [d0,d1,d2])) :
    ofDigits 10 [d0,d1,d2] = 999 := by
  let S := d0+d1+d2
  let T := d1+2*d2
  have hSle : S ≤ 27 := by dsimp [S]; omega
  have hSpos' : 0 < S := by dsimp [S]; exact hSpos
  have haNat : 27 ∣ S + 9*T := by
    clear h0 h1 h2 hSpos hB
    dsimp [S,T]
    norm_num [ofDigits] at hA ⊢
    omega
  have ha : (27:ℤ) ∣ (S:ℤ) + 9*(T:ℤ) := by exact_mod_cast haNat
  have hb : (27:ℤ) ∣ 19*(S:ℤ) - 9*(T:ℤ) := by
    clear h0 h1 h2 hSpos hA haNat ha
    have hBint : (27:ℤ) ∣ (ofDigits 10 (List.reverse [d0,d1,d2]) : ℤ) := by exact_mod_cast hB
    rw [Int.dvd_iff_emod_eq_zero] at hBint ⊢
    dsimp [S,T]
    norm_num [ofDigits] at hBint ⊢
    omega
  have hadd : (27:ℤ) ∣ 20*(S:ℤ) := by
    have := dvd_add ha hb
    convert this using 1
    ring
  have hSdvd : (27:ℤ) ∣ (S:ℤ) := by
    have h1 : (27:ℤ) ∣ 23 * (20*(S:ℤ)) := dvd_mul_of_dvd_right hadd 23
    have h2 : (27:ℤ) ∣ 27 * (17*(S:ℤ)) := dvd_mul_right 27 (17*(S:ℤ))
    have h3 : (27:ℤ) ∣ 23 * (20*(S:ℤ)) - 27 * (17*(S:ℤ)) := dvd_sub h1 h2
    convert h3 using 1
    ring
  have hSdvdNat : (27:ℕ) ∣ S := by exact_mod_cast hSdvd
  have hSeq : S = 27 := by
    clear hA hB haNat ha hb hadd hSdvd T
    omega
  have hall : d0=9 ∧ d1=9 ∧ d2=9 := by
    clear hA hB haNat ha hb hadd hSdvd hSdvdNat hSle hSpos' T
    dsimp [S] at hSeq
    omega
  rcases hall with ⟨rfl,rfl,rfl⟩
  norm_num [ofDigits]

private lemma list3_all9 (L : List ℕ) (hlen : L.length = 3) (hdig : ∀ x ∈ L, x < 10)
    (hpos : 0 < ofDigits 10 L) (hA : 27 ∣ ofDigits 10 L) (hB : 27 ∣ ofDigits 10 L.reverse) :
    ofDigits 10 L = 999 := by
  rcases L with _ | ⟨d0,L⟩; · simp at hlen
  rcases L with _ | ⟨d1,L⟩; · simp at hlen
  rcases L with _ | ⟨d2,L⟩; · simp at hlen
  have hnil : L = [] := by simpa using hlen
  subst L
  have hspos : 0 < d0+d1+d2 := by
    norm_num [ofDigits] at hpos
    omega
  apply explicit3_all9 d0 d1 d2
  · apply hdig; simp
  · apply hdig; simp
  · apply hdig; simp
  · exact hspos
  · simpa using hA
  · simpa using hB

private lemma explicit9_all9 (d0 d1 d2 d3 d4 d5 d6 d7 d8 : ℕ)
    (h0 : d0 < 10) (h1 : d1 < 10) (h2 : d2 < 10) (h3 : d3 < 10) (h4 : d4 < 10)
    (h5 : d5 < 10) (h6 : d6 < 10) (h7 : d7 < 10) (h8 : d8 < 10)
    (hSpos : 0 < d0+d1+d2+d3+d4+d5+d6+d7+d8)
    (hA : 81 ∣ ofDigits 10 [d0,d1,d2,d3,d4,d5,d6,d7,d8])
    (hB : 81 ∣ ofDigits 10 (List.reverse [d0,d1,d2,d3,d4,d5,d6,d7,d8])) :
    ofDigits 10 [d0,d1,d2,d3,d4,d5,d6,d7,d8] = 999999999 := by
  let S := d0+d1+d2+d3+d4+d5+d6+d7+d8
  let T := d1+2*d2+3*d3+4*d4+5*d5+6*d6+7*d7+8*d8
  have hSle : S ≤ 81 := by dsimp [S]; omega
  have hSpos' : 0 < S := by dsimp [S]; exact hSpos
  have haNat : 81 ∣ S + 9*T := by
    clear h0 h1 h2 h3 h4 h5 h6 h7 h8 hSpos hB
    dsimp [S,T]
    norm_num [ofDigits] at hA ⊢
    omega
  have ha : (81:ℤ) ∣ (S:ℤ) + 9*(T:ℤ) := by exact_mod_cast haNat
  have hb : (81:ℤ) ∣ 73*(S:ℤ) - 9*(T:ℤ) := by
    clear h0 h1 h2 h3 h4 h5 h6 h7 h8 hSpos hA haNat ha
    have hBint : (81:ℤ) ∣ (ofDigits 10 (List.reverse [d0,d1,d2,d3,d4,d5,d6,d7,d8]) : ℤ) := by exact_mod_cast hB
    rw [Int.dvd_iff_emod_eq_zero] at hBint ⊢
    dsimp [S,T]
    norm_num [ofDigits] at hBint ⊢
    omega
  have hadd : (81:ℤ) ∣ 74*(S:ℤ) := by
    have := dvd_add ha hb
    convert this using 1
    ring
  have hSdvd : (81:ℤ) ∣ (S:ℤ) := by
    have h1 : (81:ℤ) ∣ 23 * (74*(S:ℤ)) := dvd_mul_of_dvd_right hadd 23
    have h2 : (81:ℤ) ∣ 81 * (21*(S:ℤ)) := dvd_mul_right 81 (21*(S:ℤ))
    have h3 : (81:ℤ) ∣ 23 * (74*(S:ℤ)) - 81 * (21*(S:ℤ)) := dvd_sub h1 h2
    convert h3 using 1
    ring
  have hSdvdNat : (81:ℕ) ∣ S := by exact_mod_cast hSdvd
  have hSeq : S = 81 := by
    clear hA hB haNat ha hb hadd hSdvd T
    omega
  have hall : d0=9∧d1=9∧d2=9∧d3=9∧d4=9∧d5=9∧d6=9∧d7=9∧d8=9 := by
    clear hA hB haNat ha hb hadd hSdvd hSdvdNat hSle hSpos' T
    dsimp [S] at hSeq
    omega
  rcases hall with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  norm_num [ofDigits]

private lemma list9_all9 (L : List ℕ) (hlen : L.length = 9) (hdig : ∀ x ∈ L, x < 10)
    (hpos : 0 < ofDigits 10 L) (hA : 81 ∣ ofDigits 10 L) (hB : 81 ∣ ofDigits 10 L.reverse) :
    ofDigits 10 L = 999999999 := by
  rcases L with _ | ⟨d0,L⟩; · simp at hlen
  rcases L with _ | ⟨d1,L⟩; · simp at hlen
  rcases L with _ | ⟨d2,L⟩; · simp at hlen
  rcases L with _ | ⟨d3,L⟩; · simp at hlen
  rcases L with _ | ⟨d4,L⟩; · simp at hlen
  rcases L with _ | ⟨d5,L⟩; · simp at hlen
  rcases L with _ | ⟨d6,L⟩; · simp at hlen
  rcases L with _ | ⟨d7,L⟩; · simp at hlen
  rcases L with _ | ⟨d8,L⟩; · simp at hlen
  have hnil : L = [] := by simpa using hlen
  subst L
  have hspos : 0 < d0+d1+d2+d3+d4+d5+d6+d7+d8 := by
    norm_num [ofDigits] at hpos
    omega
  apply explicit9_all9 d0 d1 d2 d3 d4 d5 d6 d7 d8
  · apply hdig; simp
  · apply hdig; simp
  · apply hdig; simp
  · apply hdig; simp
  · apply hdig; simp
  · apply hdig; simp
  · apply hdig; simp
  · apply hdig; simp
  · apply hdig; simp
  · exact hspos
  · simpa using hA
  · simpa using hB

private lemma a27_clean : a 27 = 999 := by
  apply a_eq_of_min 27 37 (by norm_num)
  · rw [show 37 * 27 = 999 by norm_num, reverse999]
    norm_num
  · intro k hkpos hkdvd
    by_contra hlt
    have hklt : k < 37 := by omega
    let m := k * 27
    have hm_lt : m < 10^3 := by dsimp [m]; omega
    have hm_pos : 0 < m := by dsimp [m]; nlinarith
    let L := digitsAppend 10 3 m
    have hLlen : L.length = 3 := by dsimp [L]; exact length_digitsAppend (by norm_num) 3 hm_lt
    have hLdig : ∀ x ∈ L, x < 10 := by intro x hx; dsimp [L] at hx; exact lt_of_mem_digitsAppend (by norm_num) 3 x hx
    have hLm : ofDigits 10 L = m := by dsimp [L, digitsAppend]; rw [ofDigits_append_replicate_zero, ofDigits_digits]
    have hA : 27 ∣ ofDigits 10 L := by rw [hLm]; exact dvd_mul_left 27 k
    have hB : 27 ∣ ofDigits 10 L.reverse := by dsimp [L]; exact dvd_padded_reverse hkdvd
    have hpos : 0 < ofDigits 10 L := by rw [hLm]; exact hm_pos
    have hEq := list3_all9 L hLlen hLdig hpos hA hB
    rw [hLm] at hEq
    have : m < 999 := by dsimp [m]; omega
    omega

private lemma a81_clean : a 81 = 999999999 := by
  apply a_eq_of_min 81 12345679 (by norm_num)
  · rw [show 12345679 * 81 = 999999999 by norm_num, reverse999999999]
    norm_num
  · intro k hkpos hkdvd
    by_contra hlt
    have hklt : k < 12345679 := by omega
    let m := k * 81
    have hm_lt : m < 10^9 := by dsimp [m]; omega
    have hm_pos : 0 < m := by dsimp [m]; nlinarith
    let L := digitsAppend 10 9 m
    have hLlen : L.length = 9 := by dsimp [L]; exact length_digitsAppend (by norm_num) 9 hm_lt
    have hLdig : ∀ x ∈ L, x < 10 := by intro x hx; dsimp [L] at hx; exact lt_of_mem_digitsAppend (by norm_num) 9 x hx
    have hLm : ofDigits 10 L = m := by dsimp [L, digitsAppend]; rw [ofDigits_append_replicate_zero, ofDigits_digits]
    have hA : 81 ∣ ofDigits 10 L := by rw [hLm]; exact dvd_mul_left 81 k
    have hB : 81 ∣ ofDigits 10 L.reverse := by dsimp [L]; exact dvd_padded_reverse hkdvd
    have hpos : 0 < ofDigits 10 L := by rw [hLm]; exact hm_pos
    have hEq := list9_all9 L hLlen hLdig hpos hA hB
    rw [hLm] at hEq
    have : m < 999999999 := by dsimp [m]; omega
    omega

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) :=
by
  intro hn
  constructor
  · intro h
    by_cases h2 : n = 2
    · exact Or.inl h2
    by_cases h3 : n = 3
    · exact Or.inr (Or.inl h3)
    by_cases h4 : n = 4
    · exact Or.inr (Or.inr h4)
    have hn5 : 5 ≤ n := by omega
    have hn_eq : n = (n - 5) + 5 := by omega
    have hn2_eq : n - 2 = (n - 5) + 3 := by omega
    have ha_le : a (3^n) ≤ W (n - 5) := by
      rw [hn_eq]
      exact a_pow3_le_W (n - 5)
    have hWlt : W (n - 5) < 10 ^ (3 ^ (n - 2)) - 1 := by
      rw [hn2_eq]
      exact W_lt_rhs (n - 5)
    rw [h] at ha_le
    omega
  · intro h
    rcases h with rfl | rfl | rfl
    · norm_num [a9]
    · norm_num [a27_clean]
    · norm_num [a81_clean]
