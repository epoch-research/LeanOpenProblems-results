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

/-! ### Auxiliary lemmas for the proof of the conjecture -/

def wsum : List ℕ → ℕ
  | [] => 0
  | _ :: t => wsum t + t.sum

lemma ofDigits_zmod (q : ℕ) (hq : q ∣ 81) (E : List ℕ) :
    ((Nat.ofDigits 10 E : ℕ) : ZMod q) = (E.sum : ZMod q) + 9 * (wsum E : ZMod q) := by
  have h81 : (81 : ZMod q) = 0 := by
    have : ((81 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff 81 q).mpr hq
    simpa using this
  induction E with
  | nil => simp [wsum]
  | cons d t ih =>
    rw [Nat.ofDigits_cons, Nat.cast_add, Nat.cast_mul, ih]
    simp only [wsum, List.sum_cons, Nat.cast_add]
    push_cast
    linear_combination (wsum t : ZMod q) * h81

lemma wsum_append (A B : List ℕ) :
    wsum (A ++ B) = wsum A + A.length * B.sum + wsum B := by
  induction A with
  | nil => simp [wsum]
  | cons a A' ih =>
    simp only [List.cons_append, wsum, List.length_cons, List.sum_append] at *
    rw [ih]
    ring

lemma hwsum (E : List ℕ) :
    wsum E + wsum E.reverse + E.sum = E.length * E.sum := by
  induction E with
  | nil => simp [wsum]
  | cons d t ih =>
    have hrev : (d :: t).reverse = t.reverse ++ [d] := by simp
    rw [hrev, wsum_append]
    simp only [wsum, List.sum_cons, List.length_cons, List.length_reverse,
      List.sum_nil] at *
    have hwd : wsum [d] = 0 := by simp [wsum]
    nlinarith [ih, hwd]

lemma ofDigits_replicate_nine (L : ℕ) :
    Nat.ofDigits 10 (List.replicate L 9) = 10 ^ L - 1 := by
  induction L with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, pow_succ]
    have : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
    omega

lemma all_eq_replicate (E : List ℕ) (c : ℕ)
    (hle : ∀ x ∈ E, x ≤ c) (hsum : E.sum = c * E.length) :
    E = List.replicate E.length c := by
  induction E with
  | nil => simp
  | cons d t ih =>
    simp only [List.sum_cons, List.length_cons] at hsum
    have hd : d ≤ c := hle d (by simp)
    have htle : ∀ x ∈ t, x ≤ c := fun x hx => hle x (by simp [hx])
    have htsum : t.sum ≤ c * t.length := by
      have := List.sum_le_card_nsmul t c htle
      simpa [Nat.smul_one_eq_cast, mul_comm, smul_eq_mul] using this
    have hde : d = c ∧ t.sum = c * t.length := by
      constructor <;> nlinarith [hsum, htsum, hd]
    simp only [List.length_cons]
    rw [List.replicate_succ, hde.1]
    congr 1
    exact ih htle hde.2

lemma reverse_nat_eq (M : ℕ) :
    reverse_nat M = Nat.ofDigits 10 (Nat.digits 10 M).reverse := rfl

lemma KEY (n : ℕ) (hn2 : 2 ≤ n) (hn4 : n ≤ 4) (M : ℕ)
    (hM0 : 0 < M) (hML : M < 10 ^ (3 ^ (n - 2)))
    (hdvd : 3 ^ n ∣ M) (hrev : 3 ^ n ∣ reverse_nat M) :
    M = 10 ^ (3 ^ (n - 2)) - 1 := by
  set q := 3 ^ n with hq_def
  set L := 3 ^ (n - 2) with hL_def
  -- basic facts about q, L
  have hqL : 9 * L = q := by
    rw [hq_def, hL_def, show (9 : ℕ) = 3 ^ 2 from rfl, ← pow_add]
    congr 1; omega
  have hq81 : q ∣ 81 := by
    rw [hq_def, show (81 : ℕ) = 3 ^ 4 from rfl]
    exact pow_dvd_pow 3 hn4
  have hq1 : 1 < q := by
    rw [hq_def]; calc (1:ℕ) < 9 := by norm_num
                       _ = 3 ^ 2 := by norm_num
                       _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  -- digit list
  set D := Nat.digits 10 M with hD_def
  have hofd : Nat.ofDigits 10 D = M := Nat.ofDigits_digits 10 M
  have hlen : D.length ≤ L := (Nat.digits_length_le_iff (by norm_num) M).mpr hML
  have hltbase : ∀ d ∈ D, d < 10 := fun d hd => Nat.digits_lt_base (by norm_num) hd
  have hne : D ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hM0.ne'
  have hlen1 : 1 ≤ D.length := by
    rcases D with _ | _ <;> simp_all
  -- ZMod computation
  have eM : ((M : ℕ) : ZMod q) = (D.sum : ZMod q) + 9 * (wsum D : ZMod q) := by
    rw [← hofd]; exact ofDigits_zmod q hq81 D
  have erev : ((reverse_nat M : ℕ) : ZMod q)
      = (D.sum : ZMod q) + 9 * (wsum D.reverse : ZMod q) := by
    rw [reverse_nat_eq, ← hD_def, ofDigits_zmod q hq81 D.reverse, List.sum_reverse]
  have e3 : (wsum D : ZMod q) + (wsum D.reverse : ZMod q) + (D.sum : ZMod q)
      = (D.length : ZMod q) * (D.sum : ZMod q) := by
    have h2 := congrArg (fun x : ℕ => (x : ZMod q)) (hwsum D)
    simp only [Nat.cast_add, Nat.cast_mul] at h2
    exact h2
  -- combine into the key equation
  have hMz : ((M : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff M q).mpr hdvd
  have hrz : ((reverse_nat M : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (reverse_nat M) q).mpr hrev
  have hsum0 : (D.sum : ZMod q) + 9 * (wsum D : ZMod q)
      + ((D.sum : ZMod q) + 9 * (wsum D.reverse : ZMod q)) = 0 := by
    rw [← eM, ← erev, hMz, hrz]; ring
  have hkey : (D.sum : ZMod q) * (9 * (D.length : ZMod q) - 7) = 0 := by
    linear_combination hsum0 - 9 * e3
  -- transfer to ℕ divisibility
  have h7 : 7 ≤ 9 * D.length := by omega
  have hcast : ((D.sum * (9 * D.length - 7) : ℕ) : ZMod q)
      = (D.sum : ZMod q) * (9 * (D.length : ZMod q) - 7) := by
    rw [Nat.cast_mul, Nat.cast_sub h7]; push_cast; ring
  have hdvd_s : q ∣ D.sum * (9 * D.length - 7) := by
    apply (ZMod.natCast_eq_zero_iff _ q).mp
    rw [hcast]; exact hkey
  -- coprimality
  have hcop : Nat.Coprime q (9 * D.length - 7) := by
    have h3 : ¬ (3 ∣ (9 * D.length - 7)) := by omega
    have hc3 : Nat.Coprime 3 (9 * D.length - 7) :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3
    have hc81 : Nat.Coprime 81 (9 * D.length - 7) := by
      have h4 : Nat.Coprime (3 ^ 4) (9 * D.length - 7) := Nat.Coprime.pow_left 4 hc3
      simpa using h4
    exact Nat.Coprime.coprime_dvd_left hq81 hc81
  have hqS : q ∣ D.sum := hcop.dvd_of_dvd_mul_right hdvd_s
  -- bounds on the digit sum
  have hb9 : ∀ x ∈ D, x ≤ 9 := fun x hx => Nat.lt_succ_iff.mp (hltbase x hx)
  have hSle9 : D.sum ≤ 9 * D.length := by
    have := List.sum_le_card_nsmul D 9 hb9
    simpa [smul_eq_mul, mul_comm] using this
  have hSpos : 0 < D.sum := by
    have hlast : D.getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 10 hM0.ne'
    have hmem : D.getLast hne ∈ D := List.getLast_mem hne
    have hle : D.getLast hne ≤ D.sum := List.le_sum_of_mem hmem
    omega
  -- conclude D.sum = q, D.length = L
  have hSeq : D.sum = q := le_antisymm (by omega) (Nat.le_of_dvd hSpos hqS)
  have hlenL : D.length = L := by omega
  -- all digits are 9
  have hrepl : D = List.replicate D.length 9 := by
    apply all_eq_replicate D 9 hb9
    omega
  -- compute M
  rw [← hofd, hrepl, hlenL, ofDigits_replicate_nine]

-- Characterization lemmas for `a`
lemma a_eq (n : ℕ) (hn : n ≠ 0) (h : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n)) :
    a n = Nat.find h * n := by
  unfold a
  rw [if_neg hn, dif_pos h]

lemma a_le (n : ℕ) (hn : n ≠ 0) (k : ℕ) (hk : k > 0 ∧ n ∣ reverse_nat (k * n)) :
    a n ≤ k * n := by
  have h : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n) := ⟨k, hk⟩
  rw [a_eq n hn h]
  exact Nat.mul_le_mul_right n (Nat.find_le hk)

lemma a_valid (n : ℕ) (hn : n ≠ 0) (h : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n)) :
    0 < a n ∧ n ∣ a n ∧ n ∣ reverse_nat (a n) := by
  rw [a_eq n hn h]
  obtain ⟨hpos, hdvd⟩ := Nat.find_spec h
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.mul_pos hpos (Nat.pos_of_ne_zero hn)
  · exact Dvd.intro_left _ rfl
  · exact hdvd

lemma geom_triple (N : ℕ) :
    (∑ i ∈ Finset.range (3 * N), ((10 : ℤ) ^ 11) ^ i)
      = (∑ i ∈ Finset.range N, ((10 : ℤ) ^ 11) ^ i)
        * (((10 : ℤ) ^ 11) ^ (2 * N) + ((10 : ℤ) ^ 11) ^ N + 1) := by
  set x : ℤ := (10 : ℤ) ^ 11 with hx
  have hx1 : x - 1 ≠ 0 := by rw [hx]; norm_num
  have e2 : x ^ (2 * N) = (x ^ N) ^ 2 := by rw [mul_comm, pow_mul]
  have e3 : x ^ (3 * N) = (x ^ N) ^ 3 := by rw [mul_comm, pow_mul]
  apply mul_right_cancel₀ hx1
  rw [geom_sum_mul, mul_right_comm, geom_sum_mul, e2, e3]
  ring

lemma three_dvd_factor (N : ℕ) :
    (3 : ℤ) ∣ (((10 : ℤ) ^ 11) ^ (2 * N) + ((10 : ℤ) ^ 11) ^ N + 1) := by
  have hx : ((10 : ℤ) ^ 11) ≡ 1 [ZMOD 3] := by decide
  have h1 : ((10 : ℤ) ^ 11) ^ (2 * N) ≡ 1 [ZMOD 3] := by
    simpa using hx.pow (2 * N)
  have h2 : ((10 : ℤ) ^ 11) ^ N ≡ 1 [ZMOD 3] := by simpa using hx.pow N
  have : (((10 : ℤ) ^ 11) ^ (2 * N) + ((10 : ℤ) ^ 11) ^ N + 1) ≡ 1 + 1 + 1 [ZMOD 3] :=
    (h1.add h2).add (Int.ModEq.refl 1)
  have h3 : (((10 : ℤ) ^ 11) ^ (2 * N) + ((10 : ℤ) ^ 11) ^ N + 1) ≡ 0 [ZMOD 3] := by
    calc _ ≡ 1 + 1 + 1 [ZMOD 3] := this
      _ ≡ 0 [ZMOD 3] := by decide
  exact (Int.modEq_zero_iff_dvd).mp h3

lemma geom_dvd (m : ℕ) :
    (3 : ℤ) ^ m ∣ ∑ i ∈ Finset.range (3 ^ m), ((10 : ℤ) ^ 11) ^ i := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hstep : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
    rw [hstep, geom_triple]
    rw [pow_succ]
    exact mul_dvd_mul ih (three_dvd_factor (3 ^ k))

open Finset in
lemma ofDigits_flatten_replicate (X : List ℕ) (k : ℕ) :
    Nat.ofDigits 10 (List.flatten (List.replicate k X))
      = Nat.ofDigits 10 X * ∑ i ∈ Finset.range k, (10 ^ X.length) ^ i := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, ih, geom_sum_succ]
    ring

-- Palindrome list facts
lemma flatten_replicate_palindrome (X : List ℕ) (hX : X.reverse = X) (k : ℕ) :
    (List.flatten (List.replicate k X)).reverse = List.flatten (List.replicate k X) := by
  rw [List.reverse_flatten, List.map_replicate, hX, List.reverse_replicate]

lemma mem_flatten_replicate (X : List ℕ) (k : ℕ) (x : ℕ)
    (hx : x ∈ List.flatten (List.replicate k X)) : x ∈ X := by
  rw [List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rwa [List.eq_of_mem_replicate hl] at hxl

-- The witness for n ≥ 5
lemma witness_lt (n : ℕ) (hn : 5 ≤ n) :
    ∃ M : ℕ, 0 < M ∧ M < 10 ^ (3 ^ (n - 2)) - 1 ∧ 3 ^ n ∣ M ∧ reverse_nat M = M := by
  set X : List ℕ := [2,9,7,9,9,9,9,9,7,9,2] with hXdef
  set k : ℕ := 3 ^ (n - 5) with hkdef
  set L : List ℕ := List.flatten (List.replicate k X) with hLdef
  set M : ℕ := Nat.ofDigits 10 L with hMdef
  -- X facts
  have hXlen : X.length = 11 := by decide
  have hXval : Nat.ofDigits 10 X = 29799999792 := by decide
  have hXrev : X.reverse = X := by decide
  have hXlt : ∀ x ∈ X, x < 10 := by decide
  have hXne0 : ∀ x ∈ X, x ≠ 0 := by decide
  have hX35 : (3:ℕ) ^ 5 ∣ Nat.ofDigits 10 X := by rw [hXval]; decide
  have hkpos : 0 < k := pow_pos (by norm_num) _
  -- length of L
  have hLlen : L.length = k * 11 := by
    rw [hLdef, List.length_flatten, List.map_replicate, hXlen, List.sum_replicate_nat]
  have hLne : L ≠ [] := by
    rw [← List.length_pos_iff, hLlen]; positivity
  -- all entries of L are < 10
  have hLlt : ∀ x ∈ L, x < 10 := fun x hx => hXlt x (mem_flatten_replicate X k x hx)
  -- M as product
  have hMprod : M = Nat.ofDigits 10 X * ∑ i ∈ Finset.range k, (10 ^ 11) ^ i := by
    rw [hMdef, hLdef, ofDigits_flatten_replicate, hXlen]
  -- divisibility of the geometric sum
  have hGdvd : (3:ℕ) ^ (n - 5) ∣ ∑ i ∈ Finset.range k, (10 ^ 11) ^ i := by
    have hz := geom_dvd (n - 5)
    have e1 : (3 : ℤ) ^ (n - 5) = ((3 ^ (n - 5) : ℕ) : ℤ) := by push_cast; ring
    have e2 : (∑ i ∈ Finset.range (3 ^ (n - 5)), ((10 : ℤ) ^ 11) ^ i)
        = ((∑ i ∈ Finset.range k, (10 ^ 11 : ℕ) ^ i : ℕ) : ℤ) := by
      rw [hkdef]; push_cast; ring
    rw [e1, e2] at hz
    exact_mod_cast hz
  -- 3^n ∣ M
  have hdvd : 3 ^ n ∣ M := by
    rw [hMprod]
    have hsplit : (3:ℕ) ^ n = 3 ^ 5 * 3 ^ (n - 5) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    exact mul_dvd_mul hX35 hGdvd
  -- G ≥ 1, hence M > 0
  have hG1 : 1 ≤ ∑ i ∈ Finset.range k, (10 ^ 11) ^ i := by
    have h0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr hkpos
    have := Finset.single_le_sum (f := fun i => (10 ^ 11 : ℕ) ^ i)
      (fun i _ => Nat.zero_le _) h0
    simpa using this
  have hMpos : 0 < M := by
    rw [hMprod, hXval]
    have : 0 < 29799999792 * ∑ i ∈ Finset.range k, (10 ^ 11 : ℕ) ^ i :=
      Nat.mul_pos (by norm_num) hG1
    exact this
  -- palindrome
  have hrev : reverse_nat M = M := by
    have hdig : Nat.digits 10 M = L := by
      rw [hMdef]
      apply Nat.digits_ofDigits 10 (by norm_num) L hLlt
      intro hne
      have hmem : L.getLast hne ∈ L := List.getLast_mem hne
      exact hXne0 _ (mem_flatten_replicate X k _ hmem)
    rw [reverse_nat, hdig, hMdef, flatten_replicate_palindrome X hXrev k]
  -- M < 10 ^ (3 ^ (n-2)) - 1
  have hMlt : M < 10 ^ (3 ^ (n - 2)) - 1 := by
    have h1 : M < 10 ^ L.length := by
      rw [hMdef]; exact Nat.ofDigits_lt_base_pow_length (by norm_num) hLlt
    have hpow5 : 0 < 3 ^ (n - 5) := pow_pos (by norm_num) _
    have h2 : L.length < 3 ^ (n - 2) := by
      rw [hLlen, hkdef]
      have he : (3:ℕ) ^ (n - 2) = 27 * 3 ^ (n - 5) := by
        rw [show (27:ℕ) = 3 ^ 3 from rfl, ← pow_add]; congr 1; omega
      rw [he]; nlinarith [hpow5]
    have ht1 : 1 ≤ 3 ^ (n - 2) := Nat.one_le_pow _ _ (by norm_num)
    have h3 : 10 ^ L.length ≤ 10 ^ (3 ^ (n - 2) - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsplit : (10:ℕ) ^ (3 ^ (n - 2)) = 10 * 10 ^ (3 ^ (n - 2) - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hp1 : 1 ≤ 10 ^ (3 ^ (n - 2) - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  exact ⟨M, hMpos, hMlt, hdvd, hrev⟩

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) :=
by
  intro hn
  have h3n : (3:ℕ) ^ n ≠ 0 := by positivity
  constructor
  · -- forward: equality forces n ∈ {2,3,4}
    intro haR
    by_contra hc
    push_neg at hc
    have hn5 : 5 ≤ n := by omega
    obtain ⟨M, hMpos, hMlt, hMdvd, hMrev⟩ := witness_lt n hn5
    -- a (3^n) ≤ M
    have hkpos : 0 < M / 3 ^ n := Nat.div_pos (Nat.le_of_dvd hMpos hMdvd) (Nat.pos_of_ne_zero h3n)
    have hkmul : M / 3 ^ n * 3 ^ n = M := Nat.div_mul_cancel hMdvd
    have hP : M / 3 ^ n > 0 ∧ 3 ^ n ∣ reverse_nat (M / 3 ^ n * 3 ^ n) := by
      refine ⟨hkpos, ?_⟩
      rw [hkmul, hMrev]; exact hMdvd
    have hle : a (3 ^ n) ≤ M / 3 ^ n * 3 ^ n := a_le (3 ^ n) h3n (M / 3 ^ n) hP
    rw [hkmul] at hle
    rw [haR] at hle
    omega
  · -- backward: n ∈ {2,3,4} gives equality
    intro h
    have hn4 : n ≤ 4 := by rcases h with rfl | rfl | rfl <;> norm_num
    set R : ℕ := 10 ^ (3 ^ (n - 2)) - 1 with hRdef
    have hRdvd : 3 ^ n ∣ R := by rw [hRdef]; rcases h with rfl | rfl | rfl <;> decide
    have hRrev : reverse_nat R = R := by
      rw [hRdef]
      rcases h with rfl | rfl | rfl <;>
        · simp only [reverse_nat]; norm_num [Nat.ofDigits]
    have hRpos : 0 < R := by rw [hRdef]; rcases h with rfl | rfl | rfl <;> norm_num
    -- existence
    have hkmul : R / 3 ^ n * 3 ^ n = R := Nat.div_mul_cancel hRdvd
    have hkpos : 0 < R / 3 ^ n := Nat.div_pos (Nat.le_of_dvd hRpos hRdvd) (Nat.pos_of_ne_zero h3n)
    have hex : ∃ k, k > 0 ∧ 3 ^ n ∣ reverse_nat (k * 3 ^ n) := by
      refine ⟨R / 3 ^ n, hkpos, ?_⟩
      rw [hkmul, hRrev]; exact hRdvd
    -- a is a valid multiple
    obtain ⟨hapos, hadvd, harev⟩ := a_valid (3 ^ n) h3n hex
    -- a ≤ R
    have haleR : a (3 ^ n) ≤ R := by
      have := a_le (3 ^ n) h3n (R / 3 ^ n) ⟨hkpos, by rw [hkmul, hRrev]; exact hRdvd⟩
      rwa [hkmul] at this
    -- a < 10 ^ (3 ^ (n-2))
    have haLT : a (3 ^ n) < 10 ^ (3 ^ (n - 2)) := by
      have hRlt : R < 10 ^ (3 ^ (n - 2)) := by
        rw [hRdef]; rcases h with rfl | rfl | rfl <;> norm_num
      omega
    -- apply KEY
    have := KEY n hn hn4 (a (3 ^ n)) hapos haLT hadvd harev
    rw [hRdef]; exact this

