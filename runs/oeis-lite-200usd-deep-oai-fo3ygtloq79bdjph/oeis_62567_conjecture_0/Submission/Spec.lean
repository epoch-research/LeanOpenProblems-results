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

lemma a_le_of_witness {m k : ℕ} (hm : m ≠ 0) (hk : 0 < k)
    (hr : m ∣ reverse_nat (k*m)) : a m ≤ k*m := by
  unfold a
  simp [hm]
  have hw : ∃ j, j > 0 ∧ m ∣ reverse_nat (j * m) := ⟨k, hk, hr⟩
  rw [dif_pos hw]
  exact Nat.mul_le_mul_right m (Nat.find_min' hw ⟨hk, hr⟩)


lemma a_eq_of_min {m k : ℕ} (hm : m ≠ 0)
    (hk : k > 0 ∧ m ∣ reverse_nat (k*m))
    (hmin : ∀ j < k, ¬ (j > 0 ∧ m ∣ reverse_nat (j*m))) : a m = k*m := by
  unfold a
  simp [hm]
  let P : ℕ → Prop := fun j => j > 0 ∧ m ∣ reverse_nat (j * m)
  have hw : ∃ j, P j := ⟨k, hk⟩
  rw [dif_pos hw]
  have hf : Nat.find hw = k := by
    rw [Nat.find_eq_iff]
    exact ⟨hk, hmin⟩
  rw [hf]


lemma a9 : a 9 = 9 := by
  have hk : (1:ℕ) > 0 ∧ 9 ∣ reverse_nat (1*9) := by norm_num [reverse_nat, Nat.ofDigits]
  have hmin : ∀ j < (1:ℕ), ¬ (j > 0 ∧ 9 ∣ reverse_nat (j*9)) := by
    intro j hj
    have : j = 0 := by omega
    subst j
    norm_num
  simpa using a_eq_of_min (m:=9) (k:=1) (by norm_num) hk hmin

lemma a27 : a 27 = 999 := by
  have hk : (37:ℕ) > 0 ∧ 27 ∣ reverse_nat (37*27) := by norm_num [reverse_nat, Nat.ofDigits]
  have hmin : ∀ j < (37:ℕ), ¬ (j > 0 ∧ 27 ∣ reverse_nat (j*27)) := by
    intro j hj hp
    interval_cases j <;> norm_num [reverse_nat, Nat.ofDigits] at hp
  simpa using a_eq_of_min (m:=27) (k:=37) (by norm_num) hk hmin


def digitWeight : List ℕ → ℕ
| [] => 0
| _ :: L => digitWeight L + L.sum

lemma ofDigits_mod81' (L : List ℕ) :
    Nat.ofDigits (10 : ZMod 81) L = (L.sum : ZMod 81) + (9 : ZMod 81) * (digitWeight L : ZMod 81) := by
  induction L with
  | nil => simp [Nat.ofDigits, digitWeight]
  | cons d L ih =>
      simp [Nat.ofDigits, digitWeight, ih]
      have h90 : (90 : ZMod 81) = (9 : ZMod 81) := by
        change ((90:ℕ) : ZMod 81) = ((9:ℕ) : ZMod 81)
        rw [ZMod.natCast_eq_natCast_iff]
        norm_num [Nat.ModEq]
      ring_nf
      rw [h90]

lemma ofDigits_mod81 (L : List ℕ) :
    ((Nat.ofDigits 10 L : ℕ) : ZMod 81) = (L.sum : ZMod 81) + (9 : ZMod 81) * (digitWeight L : ZMod 81) := by
  rw [Nat.coe_ofDigits]
  exact ofDigits_mod81' L

lemma digitWeight_append_singleton (L : List ℕ) (d : ℕ) :
    digitWeight (L ++ [d]) = digitWeight L + L.length * d := by
  induction L with
  | nil => simp [digitWeight]
  | cons a L ih =>
      simp [digitWeight, ih, Nat.succ_mul]
      omega

lemma digitWeight_reverse_add (L : List ℕ) :
    digitWeight L + digitWeight L.reverse = (L.length - 1) * L.sum := by
  induction L with
  | nil => simp [digitWeight]
  | cons d L ih =>
      rw [List.reverse_cons, digitWeight_append_singleton]
      simp only [List.length_reverse]
      by_cases h : L.length = 0
      · have hnil : L = [] := List.eq_nil_iff_forall_not_mem.mpr (by intro a ha; have := List.length_pos_of_mem ha; omega)
        subst L
        simp [digitWeight]
      · have hpos : 0 < L.length := Nat.pos_of_ne_zero h
        have hsucc : L.length - 1 + 1 = L.length := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
        simp only [digitWeight, List.sum_cons, List.length_cons]
        calc
          digitWeight L + L.sum + (digitWeight L.reverse + L.length * d)
              = (digitWeight L + digitWeight L.reverse) + (L.sum + L.length * d) := by ac_rfl
          _ = (L.length - 1) * L.sum + (L.sum + L.length * d) := by rw [ih]
          _ = L.length * (d + L.sum) := by
              rw [show (L.length - 1) * L.sum + (L.sum + L.length * d) = ((L.length - 1)+1)*L.sum + L.length*d by ring]
              rw [hsucc]
              ring

lemma zmod81_unit_coeff (len : ℕ) : IsUnit ((2 + 9*(len-1) : ℕ) : ZMod 81) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Prime.coprime_pow_of_not_dvd (p:=3) (m:=4) (by norm_num)
  intro hd
  have hmod : (2 + 9 * (len - 1)) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega


lemma list_sum_le_nine_mul_length {L : List ℕ} (hB : ∀ d ∈ L, d ≤ 9) : L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons d L ih =>
      simp at hB ⊢
      have hd := hB.1
      have ht := ih hB.2
      omega

lemma list_eq_replicate_of_sum_eq_nine_mul_length {L : List ℕ}
    (hB : ∀ d ∈ L, d ≤ 9) (hs : L.sum = 9 * L.length) : L = List.replicate L.length 9 := by
  induction L with
  | nil => simp
  | cons d L ih =>
      simp at hB hs ⊢
      have hle := list_sum_le_nine_mul_length hB.2
      have hd : d = 9 := by omega
      subst d
      have hsL : L.sum = 9 * L.length := by omega
      rw [ih hB.2 hsL]
      rw [List.replicate_succ]
      simp

lemma ofDigits_replicate9_9 : Nat.ofDigits 10 (List.replicate 9 9) = 999999999 := by
  norm_num [Nat.ofDigits, List.replicate]

lemma digit_sum_lt_81_of_lt (x : ℕ) (hx0 : 0 < x) (hx : x < 999999999) : (digits 10 x).sum < 81 := by
  let L := digits 10 x
  have hlen : L.length ≤ 9 := by
    dsimp [L]
    rw [Nat.digits_length_le_iff (by norm_num)]
    omega
  have hdle : ∀ d ∈ L, d ≤ 9 := by
    intro d hd
    exact Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num : 1 < 10) hd)
  have hsumle : L.sum ≤ 81 := by
    have := list_sum_le_nine_mul_length hdle
    nlinarith
  have hne : L.sum ≠ 81 := by
    intro hs
    have hlen9 : L.length = 9 := by
      have := list_sum_le_nine_mul_length hdle
      omega
    have hsmax : L.sum = 9 * L.length := by omega
    have hrep : L = List.replicate L.length 9 := list_eq_replicate_of_sum_eq_nine_mul_length hdle hsmax
    have hxval : x = Nat.ofDigits 10 L := by
      dsimp [L]
      exact (Nat.ofDigits_digits 10 x).symm
    have hx999 : x = 999999999 := by
      rw [hxval, hrep, hlen9, ofDigits_replicate9_9]
    omega
  show L.sum < 81
  omega

lemma no_81_reverse_below (x : ℕ) (hx0 : 0 < x) (hxlt : x < 999999999)
    (hxdiv : 81 ∣ x) (hrdiv : 81 ∣ (Nat.ofDigits 10 (digits 10 x).reverse)) : False := by
  let L := digits 10 x
  let S : ZMod 81 := (L.sum : ZMod 81)
  let W : ZMod 81 := (digitWeight L : ZMod 81)
  let WR : ZMod 81 := (digitWeight L.reverse : ZMod 81)
  have hxz : ((x : ℕ) : ZMod 81) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hxdiv
  have h1 : S + (9 : ZMod 81) * W = 0 := by
    dsimp [S, W, L]
    rw [← ofDigits_mod81]
    rwa [Nat.ofDigits_digits]
  have h2 : S + (9 : ZMod 81) * WR = 0 := by
    dsimp [S, WR, L]
    rw [← List.sum_reverse]
    rw [← ofDigits_mod81]
    rw [ZMod.natCast_eq_zero_iff]
    exact hrdiv
  have hw : W + WR = (((L.length - 1) * L.sum : ℕ) : ZMod 81) := by
    dsimp [W, WR]
    rw [← Nat.cast_add, digitWeight_reverse_add]
  have hcoeff : (((2 + 9*(L.length - 1) : ℕ) : ZMod 81) * S) = 0 := by
    calc
      (((2 + 9*(L.length - 1) : ℕ) : ZMod 81) * S)
          = (2 : ZMod 81) * S + (9 : ZMod 81) * (((L.length - 1) * L.sum : ℕ) : ZMod 81) := by
              dsimp [S]
              push_cast
              ring
      _ = (2 : ZMod 81) * S + (9 : ZMod 81) * (W + WR) := by rw [← hw]
      _ = (S + (9 : ZMod 81) * W) + (S + (9 : ZMod 81) * WR) := by ring
      _ = 0 := by rw [h1, h2]; simp
  have hSzero : S = 0 := by
    have hu := zmod81_unit_coeff L.length
    exact (IsUnit.mul_left_eq_zero hu).mp (by simpa [mul_comm] using hcoeff)
  have h81S : 81 ∣ L.sum := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact hSzero
  have hSpos : 0 < L.sum := by
    dsimp [L]
    have hne : digits 10 x ≠ [] := (Nat.digits_ne_nil_iff_ne_zero).mpr (Nat.ne_of_gt hx0)
    -- a nonempty digit list of a positive number has positive sum since last digit is nonzero
    by_contra hz
    have hsum0 : (digits 10 x).sum = 0 := Nat.eq_zero_of_not_pos hz
    have hall0 : ∀ d ∈ digits 10 x, d = 0 := by
      intro d hd
      have d_le_sum : d ≤ (digits 10 x).sum := List.le_sum_of_mem hd
      omega
    have hlast0 := hall0 ((digits 10 x).getLast hne) (List.getLast_mem hne)
    exact (Nat.getLast_digit_ne_zero 10 (Nat.ne_of_gt hx0)) hlast0
  have hSlt : L.sum < 81 := by
    dsimp [L]
    exact digit_sum_lt_81_of_lt x hx0 hxlt
  rcases h81S with ⟨c, hc⟩
  omega


lemma a81 : a 81 = 999999999 := by
  have hk : (12345679:ℕ) > 0 ∧ 81 ∣ reverse_nat (12345679*81) := by
    norm_num [reverse_nat, Nat.ofDigits]
  have hmin : ∀ j < (12345679:ℕ), ¬ (j > 0 ∧ 81 ∣ reverse_nat (j*81)) := by
    intro j hj hp
    have hx0 : 0 < j * 81 := by nlinarith [hp.1]
    have hxlt : j * 81 < 999999999 := by nlinarith [hj]
    have hxdiv : 81 ∣ j * 81 := by exact dvd_mul_left 81 j
    have hrdiv : 81 ∣ Nat.ofDigits 10 (digits 10 (j*81)).reverse := by
      simpa [reverse_nat] using hp.2
    exact no_81_reverse_below (j*81) hx0 hxlt hxdiv hrdiv
  simpa using a_eq_of_min (m:=81) (k:=12345679) (by norm_num) hk hmin

def blockDigits : List ℕ := [7,8,9,9,9,9,9,9,8,4]

def tripleBlocks : ℕ → List ℕ
  | 0 => blockDigits
  | m+1 => let l := tripleBlocks m; l ++ l ++ l

lemma len_tripleBlocks (m : ℕ) : (tripleBlocks m).length = 10 * 3^m := by
  induction m with
  | zero => norm_num [tripleBlocks, blockDigits]
  | succ m ih =>
      simp [tripleBlocks, ih, pow_succ]
      ring

lemma three_dvd_factor (len : ℕ) : 3 ∣ (1 + 10^len + 10^(2*len)) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have h1 : 10 ^ len % 3 = 1 := by
    induction len with
    | zero => norm_num
    | succ len ih => simp [pow_succ, Nat.mul_mod, ih]
  have h2 : 10 ^ (2*len) % 3 = 1 := by
    simp [show 2*len = len+len by omega, pow_add, Nat.mul_mod, h1]
  omega

lemma ofDigits_triple (l : List ℕ) :
    Nat.ofDigits 10 (l ++ l ++ l) =
      Nat.ofDigits 10 l * (1 + 10 ^ l.length + 10 ^ (2*l.length)) := by
  rw [Nat.ofDigits_append, Nat.ofDigits_append]
  simp [List.length_append]
  ring

lemma reverse_tripleBlocks (m : ℕ) : (tripleBlocks m).reverse =
    (let l := (tripleBlocks m).reverse; l) := by rfl

lemma dvd_step {m v len : ℕ} (hv : 3^(m+5) ∣ v)
    (hf : 3 ∣ (1 + 10^len + 10^(2*len))) :
    3^(m+6) ∣ v * (1 + 10^len + 10^(2*len)) := by
  rcases hv with ⟨a, rfl⟩
  rcases hf with ⟨b, hb⟩
  use a*b
  rw [hb]
  ring_nf

lemma dvd_tripleBlocks_val (m : ℕ) :
    3^(m+5) ∣ Nat.ofDigits 10 (tripleBlocks m) ∧
    3^(m+5) ∣ Nat.ofDigits 10 (tripleBlocks m).reverse := by
  induction m with
  | zero =>
      constructor <;> norm_num [tripleBlocks, blockDigits, Nat.ofDigits]
  | succ m ih =>
      constructor
      · rw [tripleBlocks, ofDigits_triple]
        exact dvd_step ih.1 (three_dvd_factor (tripleBlocks m).length)
      · rw [tripleBlocks]
        simp only [List.reverse_append]
        rw [← List.append_assoc]
        rw [ofDigits_triple]
        exact dvd_step ih.2 (three_dvd_factor (tripleBlocks m).reverse.length)


lemma mem_tripleBlocks_lt10 (m : ℕ) : ∀ d ∈ tripleBlocks m, d < 10 := by
  induction m with
  | zero =>
      intro d hd
      simp [tripleBlocks, blockDigits] at hd
      omega
  | succ m ih =>
      intro d hd
      have hd' : d ∈ tripleBlocks m ∨ d ∈ tripleBlocks m ∨ d ∈ tripleBlocks m := by
        simpa [tripleBlocks, List.mem_append] using hd
      rcases hd' with hd | hd | hd <;> exact ih d hd

lemma tripleBlocks_ne_nil (m : ℕ) : tripleBlocks m ≠ [] := by
  have hlen := len_tripleBlocks m
  intro h
  rw [h] at hlen
  simp at hlen

lemma getLast?_tripleBlocks (m : ℕ) : (tripleBlocks m).getLast? = some 4 := by
  induction m with
  | zero => norm_num [tripleBlocks, blockDigits]
  | succ m ih =>
      simp [tripleBlocks, ih]

lemma last_tripleBlocks_ne_zero (m : ℕ) :
    (tripleBlocks m).getLast (tripleBlocks_ne_nil m) ≠ 0 := by
  have h := List.getLast?_eq_getLast_of_ne_nil (tripleBlocks_ne_nil m)
  rw [getLast?_tripleBlocks m] at h
  injection h with h4
  rw [← h4]
  norm_num

lemma reverse_nat_of_tripleBlocks (m : ℕ) :
    reverse_nat (Nat.ofDigits 10 (tripleBlocks m)) =
      Nat.ofDigits 10 (tripleBlocks m).reverse := by
  unfold reverse_nat
  have hd := Nat.digits_ofDigits 10 (by norm_num) (tripleBlocks m)
      (mem_tripleBlocks_lt10 m) (fun _ => last_tripleBlocks_ne_zero m)
  rw [hd]


lemma val_tripleBlocks_pos (m : ℕ) : 0 < Nat.ofDigits 10 (tripleBlocks m) := by
  induction m with
  | zero => norm_num [tripleBlocks, blockDigits, Nat.ofDigits]
  | succ m ih =>
      rw [tripleBlocks, ofDigits_triple]
      positivity


lemma a_lt_rhs_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    a (3^n) < 10 ^ (3 ^ (n - 2)) - 1 := by
  let m := n - 5
  let V := Nat.ofDigits 10 (tripleBlocks m)
  have hn_eq : n = m + 5 := by
    dsimp [m]
    omega
  have hpow : 3^n = 3^(m+5) := by rw [hn_eq]
  have hdvdV : 3^n ∣ V := by
    rw [hpow]
    exact (dvd_tripleBlocks_val m).1
  let k := V / 3^n
  have hkprod : k * 3^n = V := by
    dsimp [k]
    exact Nat.div_mul_cancel hdvdV
  have hkpos : 0 < k := by
    by_contra hk0
    have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
    have : V = 0 := by simpa [hkz] using hkprod.symm
    exact (Nat.ne_of_gt (val_tripleBlocks_pos m)) this
  have hrev : 3^n ∣ reverse_nat (k * 3^n) := by
    rw [hkprod, reverse_nat_of_tripleBlocks]
    rw [hpow]
    exact (dvd_tripleBlocks_val m).2
  have hle : a (3^n) ≤ V := by
    simpa [hkprod] using a_le_of_witness (m:=3^n) (k:=k) (by positivity) hkpos hrev
  have hVlt : V < 10 ^ (10 * 3^m) := by
    dsimp [V]
    simpa [len_tripleBlocks] using Nat.ofDigits_lt_base_pow_length (b:=10)
      (l:=tripleBlocks m) (by norm_num) (mem_tripleBlocks_lt10 m)
  have hexp : 10 * 3^m < 3 ^ (n - 2) := by
    rw [hn_eq]
    have hm2 : m + 5 - 2 = m + 3 := by omega
    rw [hm2, pow_add]
    norm_num
    have hp : 0 < 3^m := by positivity
    nlinarith
  have hpowlt : 10 ^ (10 * 3^m) < 10 ^ (3 ^ (n - 2)) := by
    exact Nat.pow_lt_pow_right (by norm_num) hexp
  have hpospow : 0 < 10 ^ (10 * 3^m) := by positivity
  have hleSub : 10 ^ (10 * 3^m) ≤ 10 ^ (3 ^ (n - 2)) - 1 := by
    exact Nat.le_sub_one_of_lt hpowlt
  exact lt_of_le_of_lt hle (lt_of_lt_of_le hVlt hleSub)


end OEIS62567

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) :=
by
  intro hn
  constructor
  · intro heq
    by_cases h5 : 5 ≤ n
    · have hlt := OEIS62567.a_lt_rhs_of_five_le (n:=n) h5
      rw [heq] at hlt
      exact (lt_irrefl _ hlt).elim
    · omega
  · rintro (rfl | rfl | rfl)
    · norm_num [OEIS62567.a9]
    · norm_num [OEIS62567.a27]
    · norm_num [OEIS62567.a81]
