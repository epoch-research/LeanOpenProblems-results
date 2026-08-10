import FormalConjectures.Util.ProblemImports
open Nat
open Classical

/--
A272479: $a(n)$ is the smallest $k$ different from $n$ such that $(n, k)$ is a Harshad amicable pair.
Let $D(n)$ be the sum of digits of $n$.
$m$ and $k$ are Harshad amicable if they are distinct integers such that $D(m) \mid k$ and $D(k) \mid m$.
For any $n$ with no Harshad amicable partner, $a(n)=0$ (Conjecture: the sequence contains no zeros.)
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dsum (m : ℕ) : ℕ := (digits 10 m).sum

  let partners : Set ℕ := {k | k > 0 ∧ k ≠ n ∧ dsum n ∣ k ∧ dsum k ∣ n}

  -- The set of partners is bounded below by 1. If it is non-empty, `sInf`
  -- correctly returns the smallest element. If empty, we return 0 as per the OEIS comment.
  if h : partners.Nonempty then
    sInf partners
  else
    0

namespace A272479Aux

open List

abbrev D (n : ℕ) : ℕ := (Nat.digits 10 n).sum

lemma ofDigits_zero_of_all_zero : ∀ L : List ℕ, (∀ x ∈ L, x = 0) → Nat.ofDigits 10 L = 0
  | [], _ => by simp [Nat.ofDigits]
  | a :: t, h => by
      have ha : a = 0 := h a (by simp)
      have ht : ∀ x ∈ t, x = 0 := by
        intro x hx
        exact h x (by simp [hx])
      simp [Nat.ofDigits_cons, ha, ofDigits_zero_of_all_zero t ht]

lemma D_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < D n := by
  classical
  by_contra h
  have hD : D n = 0 := Nat.eq_zero_of_not_pos h
  have hall : ∀ x ∈ Nat.digits 10 n, x = 0 := (List.sum_eq_zero_iff).mp hD
  have hn0 : Nat.ofDigits 10 (Nat.digits 10 n) = 0 := ofDigits_zero_of_all_zero _ hall
  rw [Nat.ofDigits_digits] at hn0
  omega

lemma list_sum_le_nine_mul_length {L : List ℕ} (hL : ∀ x ∈ L, x < 10) :
    L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      have hx : x < 10 := hL x (by simp)
      have hxs : ∀ y ∈ xs, y < 10 := by
        intro y hy; exact hL y (by simp [hy])
      have hx9 : x ≤ 9 := by omega
      have ih' := ih hxs
      simp [List.sum_cons, List.length_cons]
      omega

lemma sum_le_nine_mul_length_of_digits (n : ℕ) : D n ≤ 9 * (Nat.digits 10 n).length := by
  exact list_sum_le_nine_mul_length (by
    intro x hx
    exact Nat.digits_lt_base (by norm_num) hx)

lemma comp_ofDigits_add (L : List ℕ) (hL : ∀ x ∈ L, x < 10) :
    Nat.ofDigits 10 (L.map (fun x => 9 - x)) + Nat.ofDigits 10 L + 1 = 10 ^ L.length := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons a t ih =>
      have ha : a < 10 := hL a (by simp)
      have ht : ∀ x ∈ t, x < 10 := by
        intro x hx; exact hL x (by simp [hx])
      have ih' := ih ht
      have hsum : (9 - a) + a = 9 := by omega
      simp [Nat.ofDigits_cons, List.map, List.length_cons]
      rw [pow_succ']
      nlinarith

lemma comp_sum_add (L : List ℕ) (hL : ∀ x ∈ L, x < 10) :
    (L.map (fun x => 9 - x)).sum + L.sum = 9 * L.length := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : a < 10 := hL a (by simp)
      have ht : ∀ x ∈ t, x < 10 := by
        intro x hx; exact hL x (by simp [hx])
      have ih' := ih ht
      have hsum : (9 - a) + a = 9 := by omega
      simp [List.map, List.sum_cons, List.length_cons]
      omega

lemma digitsAppend_ofDigits (L x : ℕ) (hx : x < 10 ^ L) :
    Nat.ofDigits 10 (Nat.digitsAppend 10 L x) = x := by
  rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

lemma digitsAppend_sum (L x : ℕ) (hx : x < 10 ^ L) :
    (Nat.digitsAppend 10 L x).sum = D x := by
  rw [Nat.digitsAppend, List.sum_append_nat, List.sum_replicate, nsmul_zero, add_zero]

lemma constructed_digit_sum {d L : ℕ} (hd : 0 < d) (hbound : d ≤ 10 ^ L) :
    D (d * (2 * 10 ^ L - 1)) = 9 * L + D (2 * d - 1) - D (d - 1) := by
  classical
  let low0 := Nat.digitsAppend 10 L (d - 1)
  let low := low0.map (fun x => 9 - x)
  let up := Nat.digits 10 (2 * d - 1)
  let W := low ++ up
  have hxlt : d - 1 < 10 ^ L := by omega
  have hlow0_len : low0.length = L := by
    simpa [low0] using Nat.length_digitsAppend (b := 10) (by norm_num) L hxlt
  have hlow0_mem : ∀ x ∈ low0, x < 10 := by
    intro x hx
    exact Nat.lt_of_mem_digitsAppend (b := 10) (by norm_num) L x (by simpa [low0] using hx)
  have hlow_mem : ∀ x ∈ low, x < 10 := by
    intro x hx
    simp [low] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hylt := hlow0_mem y hy
    omega
  have hup_mem : ∀ x ∈ up, x < 10 := by
    intro x hx
    exact Nat.digits_lt_base (by norm_num) (by simpa [up] using hx)
  have hW_mem : ∀ x ∈ W, x < 10 := by
    intro x hx
    simp [W] at hx
    rcases hx with hx | hx
    · exact hlow_mem x hx
    · exact hup_mem x hx
  have hW_sum_digits : D (Nat.ofDigits 10 W) = W.sum := by
    have hmem : W ∈ {L' : List ℕ | L'.length = W.length ∧ ∀ x ∈ L', x < 10} := by
      exact ⟨rfl, hW_mem⟩
    simpa [D] using Nat.sum_digits_ofDigits_eq_sum (b := 10) (by norm_num) (l := W.length) hmem
  have hlow0_of : Nat.ofDigits 10 low0 = d - 1 := by
    simpa [low0] using digitsAppend_ofDigits L (d - 1) hxlt
  have hcomp_add := comp_ofDigits_add low0 hlow0_mem
  have hlow_of : Nat.ofDigits 10 low = 10 ^ L - d := by
    change Nat.ofDigits 10 (low0.map (fun x => 9 - x)) = 10 ^ L - d
    have hadd : Nat.ofDigits 10 (low0.map (fun x => 9 - x)) + d = 10 ^ L := by
      have := hcomp_add
      simp [hlow0_len, hlow0_of] at this
      omega
    omega
  have hup_of : Nat.ofDigits 10 up = 2 * d - 1 := by
    simp [up, Nat.ofDigits_digits]
  have hW_of : Nat.ofDigits 10 W = d * (2 * 10 ^ L - 1) := by
    simp [W, low, up, Nat.ofDigits_append, hlow0_len, hlow_of, hup_of]
    have hp : 0 < 10 ^ L := pow_pos (by norm_num : (0:ℕ) < 10) L
    have hsub1 : 2 * 10 ^ L - 1 + 1 = 2 * 10 ^ L := by omega
    have hsub2 : 2 * d - 1 + 1 = 2 * d := by omega
    have hsubd : 10 ^ L - d + d = 10 ^ L := by omega
    nlinarith
  have hlow_sum_add := comp_sum_add low0 hlow0_mem
  have hlow_sum_add' : low.sum + D (d - 1) = 9 * L := by
    change (low0.map (fun x => 9 - x)).sum + D (d - 1) = 9 * L
    have hsum0 : low0.sum = D (d - 1) := by
      simpa [low0] using digitsAppend_sum L (d - 1) hxlt
    have := hlow_sum_add
    rw [hsum0, hlow0_len] at this
    exact this
  have hlow_sum : low.sum = 9 * L - D (d - 1) := by
    omega

  have hup_sum : up.sum = D (2 * d - 1) := by simp [up, D]
  have hW_sum : W.sum = 9 * L + D (2 * d - 1) - D (d - 1) := by
    simp [W, hlow_sum, hup_sum]
    omega
  rw [← hW_of, hW_sum_digits, hW_sum]

lemma D_rec (n : ℕ) : D n = n % 10 + D (n / 10) := by
  by_cases hn : n = 0
  · subst n
    simp [D]
  · have hxy : n % 10 ≠ 0 ∨ n / 10 ≠ 0 := by
      by_contra h
      push_neg at h
      have hrepr := Nat.mod_add_div n 10
      rw [h.1, h.2] at hrepr
      omega
    have hd := Nat.digits_add 10 (by norm_num) (n % 10) (n / 10)
      (Nat.mod_lt n (by norm_num)) hxy
    have hd2 : D (n % 10 + 10 * (n / 10)) = n % 10 + D (n / 10) := by
      simpa [D] using congrArg List.sum hd
    have hrepr := Nat.mod_add_div n 10
    rwa [hrepr] at hd2


lemma D_subadd (x y : ℕ) : D (x + y) ≤ D x + D y := by
  let P : ℕ → Prop := fun s => ∀ x y : ℕ, x + y = s → D (x + y) ≤ D x + D y
  have H : ∀ s, P s := by
    intro s
    refine Nat.strong_induction_on s ?_
    intro s IH x y hs
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    have hxpos : 0 < x := Nat.pos_of_ne_zero hx
    have hypos : 0 < y := Nat.pos_of_ne_zero hy
    let qx := x / 10
    let qy := y / 10
    let rx := x % 10
    let ry := y % 10
    let c := (rx + ry) / 10
    have hdivsum : (x + y) / 10 = qx + qy + c := by
      have h1 : x + y = (rx + ry) + 10 * (qx + qy) := by
        dsimp [rx, qx, ry, qy]
        omega
      rw [h1]
      rw [Nat.add_mul_div_left]
      · dsimp [c]
        omega
      · norm_num
    have hmodsum : (x + y) % 10 + 10 * c = rx + ry := by
      have h1 : x + y = (rx + ry) + 10 * (qx + qy) := by
        dsimp [rx, qx, ry, qy]
        omega
      have hmod : (x + y) % 10 = (rx + ry) % 10 := by
        rw [h1, Nat.add_mul_mod_self_left]
      have hc := Nat.mod_add_div (rx + ry) 10
      dsimp [c]
      rw [hmod]
      exact hc
    have hc_le : c ≤ 1 := by
      have hrx : rx < 10 := Nat.mod_lt x (by norm_num)
      have hry : ry < 10 := Nat.mod_lt y (by norm_num)
      dsimp [c, rx, ry]
      omega
    have hsmall1 : qx + qy < s := by
      have hqx : qx < x := Nat.div_lt_self hxpos (by norm_num)
      have hqy : qy < y := Nat.div_lt_self hypos (by norm_num)
      dsimp [qx, qy]
      omega
    have hsmall2 : qx + qy + c < s := by
      have hqx : qx < x := Nat.div_lt_self hxpos (by norm_num)
      have hqy : qy < y := Nat.div_lt_self hypos (by norm_num)
      dsimp [qx, qy]
      omega
    have ih_q : D (qx + qy) ≤ D qx + D qy := IH (qx + qy) hsmall1 qx qy rfl
    have ih_c : D ((qx + qy) + c) ≤ D (qx + qy) + D c :=
      IH (qx + qy + c) hsmall2 (qx + qy) c rfl
    have hDc : D c ≤ c := Nat.digit_sum_le 10 c
    rw [D_rec (x + y), D_rec x, D_rec y]
    rw [hdivsum]
    have hmain : (x + y) % 10 + c ≤ rx + ry := by
      have : (x + y) % 10 + 10 * c = rx + ry := hmodsum
      omega
    dsimp [qx, qy, rx, ry, c] at *
    omega
  exact H (x + y) x y rfl

lemma c_le_d {d : ℕ} (hd : 0 < d) : D (2 * d - 1) ≤ D (d - 1) + d := by
  have h : 2 * d - 1 = (d - 1) + d := by omega
  rw [h]
  calc
    D ((d - 1) + d) ≤ D (d - 1) + D d := D_subadd (d - 1) d
    _ ≤ D (d - 1) + d := by
      exact Nat.add_le_add_left (Nat.digit_sum_le 10 d) _

lemma nine_add_le_pow10 {s : ℕ} (hs : 1 ≤ s) : 9 + s ≤ 10 ^ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs0 : s = 0
      · subst s
        norm_num
      · have hs1 : 1 ≤ s := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs0)
        have ih' := ih hs1
        rw [pow_succ']
        nlinarith [ih', pow_pos (by norm_num : (0:ℕ) < 10) s]

lemma D_bound_by_gap (n : ℕ) (hn : 10 ≤ n) :
    ∃ S : ℕ, 9 * S = n - D n ∧ D n ≤ 10 ^ S := by
  let S : ℕ := ∑ i ∈ Finset.range (Nat.log 10 n).succ, n / 10 ^ i.succ
  refine ⟨S, ?_, ?_⟩
  · simpa [S, D] using (Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := 10) n)
  · have hterm : n / 10 ≤ S := by
      have hmem : 0 ∈ Finset.range (Nat.log 10 n).succ := by simp
      have hsingle := Finset.single_le_sum (fun i _ => Nat.zero_le (n / 10 ^ i.succ)) hmem
      simpa [S] using hsingle
    have hSpos : 1 ≤ S := by
      have : 1 ≤ n / 10 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 10)).mpr (by simpa using hn)
      omega
    have hDle : D n ≤ 9 + S := by
      rw [D_rec n]
      have hmod : n % 10 ≤ 9 := by
        have := Nat.mod_lt n (by norm_num : 0 < 10)
        omega
      have htail : D (n / 10) ≤ n / 10 := Nat.digit_sum_le 10 (n / 10)
      omega
    exact le_trans hDle (nine_add_le_pow10 hSpos)

lemma D_lt_self_of_ge_ten {n : ℕ} (hn : 10 ≤ n) : D n < n := by
  rw [D_rec n]
  have hmod : n % 10 ≤ 9 := by
    have := Nat.mod_lt n (by norm_num : 0 < 10)
    omega
  have htail : D (n / 10) ≤ n / 10 := Nat.digit_sum_le 10 (n / 10)
  have hrepr := Nat.mod_add_div n 10
  omega

end A272479Aux

open A272479Aux

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hnpos
  classical
  have hpartner : ({k : ℕ | k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n} : Set ℕ).Nonempty := by
    by_cases hnsmall : n < 10
    · interval_cases n
      all_goals norm_num at *
      · exact ⟨10, by norm_num⟩
      · exact ⟨20, by norm_num⟩
      · exact ⟨30, by norm_num⟩
      · exact ⟨40, by norm_num⟩
      · exact ⟨50, by norm_num⟩
      · exact ⟨60, by norm_num⟩
      · exact ⟨70, by norm_num⟩
      · exact ⟨80, by norm_num⟩
      · exact ⟨90, by norm_num⟩
    · have hn10 : 10 ≤ n := by omega
      let d := D n
      let A := D (d - 1)
      let B := D (2 * d - 1)
      have hdpos : 0 < d := by
        simpa [d, D] using D_pos_of_pos hnpos
      have hdle : d ≤ n := by
        simpa [d, D] using Nat.digit_sum_le 10 n
      have hBA : B ≤ n + A := by
        have hc : B ≤ A + d := by
          simpa [A, B] using c_le_d hdpos
        omega
      have hn_mod : n ≡ d [MOD 9] := by
        simpa [d, D] using Nat.modEq_nine_digits_sum n
      have hA_mod : A ≡ d - 1 [MOD 9] := by
        simpa [A, D] using (Nat.modEq_nine_digits_sum (d - 1)).symm
      have hB_mod : B ≡ 2 * d - 1 [MOD 9] := by
        simpa [B, D] using (Nat.modEq_nine_digits_sum (2 * d - 1)).symm
      have hsum_mod : n + A ≡ 2 * d - 1 [MOD 9] := by
        have h := Nat.ModEq.add hn_mod hA_mod
        have htarget : d + (d - 1) = 2 * d - 1 := by omega
        simpa [htarget] using h
      have hmod : B ≡ n + A [MOD 9] := hB_mod.trans hsum_mod.symm
      have hdiv : 9 ∣ n + A - B := (Nat.modEq_iff_dvd' hBA).mp hmod
      obtain ⟨L, hLsub⟩ := hdiv
      have hLeq : n + A = 9 * L + B := by omega
      obtain ⟨S, hS, hDpow⟩ := D_bound_by_gap n hn10
      have h9Lge : n - d ≤ 9 * L := by
        have hc : B ≤ A + d := by
          simpa [A, B] using c_le_d hdpos
        omega
      have hSleL : S ≤ L := by
        have hSd : 9 * S = n - d := by simpa [d] using hS
        omega
      have hbound : d ≤ 10 ^ L := by
        exact le_trans hDpow (Nat.pow_le_pow_right (by norm_num : 0 < 10) hSleL)
      let k := d * (2 * 10 ^ L - 1)
      have hDk : D k = n := by
        have hc := constructed_digit_sum hdpos hbound
        dsimp [k]
        rw [hc]
        omega
      refine ⟨k, ?_, ?_, ?_, ?_⟩
      · dsimp [k]
        have hp : 0 < 2 * 10 ^ L - 1 := by
          have : 0 < 10 ^ L := pow_pos (by norm_num : (0:ℕ) < 10) L
          omega
        exact Nat.mul_pos hdpos hp
      · intro hkn
        have hdlt : d < n := by
          simpa [d] using D_lt_self_of_ge_ten hn10
        have : n = d := by
          calc
            n = D k := hDk.symm
            _ = D n := by rw [hkn]
            _ = d := rfl
        omega
      · dsimp [k, d, D]
        exact ⟨2 * 10 ^ L - 1, rfl⟩
      · have : (Nat.digits 10 k).sum = n := by simpa [D] using hDk
        rw [this]
  unfold a
  dsimp
  split_ifs with h
  · intro hz
    have hs := Nat.sInf_mem h
    rw [hz] at hs
    exact (Nat.lt_irrefl 0) hs.1
  · exact False.elim (h hpartner)
