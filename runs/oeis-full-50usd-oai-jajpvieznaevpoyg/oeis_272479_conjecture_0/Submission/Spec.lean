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
  if _h : partners.Nonempty then
    sInf partners
  else
    0

namespace List
lemma sum_map_nine_sub_add_sum (L : List ℕ) (hL : ∀ x ∈ L, x < 10) :
    (L.map (fun x => 9 - x)).sum + L.sum = 9 * L.length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      have hxs : ∀ y ∈ xs, y < 10 := by intro y hy; exact hL y (by simp [hy])
      rw [List.map_cons, List.sum_cons, List.sum_cons, List.length_cons]
      have ih' := ih hxs
      have hx : x < 10 := hL x (by simp)
      omega
end List

namespace Nat
lemma ofDigits_map_nine_sub_add_ofDigits (L : List ℕ) (hL : ∀ x ∈ L, x < 10) :
    ofDigits 10 (L.map (fun x => 9 - x)) + ofDigits 10 L = 10 ^ L.length - 1 := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      have hx : x < 10 := hL x (by simp)
      have hxs : ∀ y ∈ xs, y < 10 := by intro y hy; exact hL y (by simp [hy])
      rw [List.map_cons, ofDigits_cons, ofDigits_cons, List.length_cons]
      have ih' := ih hxs
      rw [pow_succ']
      have hpow1 : (1:ℕ) ≤ 10 ^ xs.length := by exact Nat.succ_le_of_lt (pow_pos (by norm_num) _)
      have ih_add : Nat.ofDigits 10 (xs.map fun x => 9 - x) + Nat.ofDigits 10 xs + 1 = 10 ^ xs.length := by
        omega
      have hxadd : (9 - x) + x = 9 := by omega
      omega
end Nat

lemma digitSum_eq_mod_add_digitSum_div (n : ℕ) (hn : n ≠ 0) :
    (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
  have hlt : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hxy : n % 10 ≠ 0 ∨ n / 10 ≠ 0 := by
    by_contra h
    push_neg at h
    have : n = 0 := by rw [← Nat.mod_add_div n 10, h.1, h.2]
    exact hn this
  have hd := Nat.digits_add 10 (by norm_num) (n % 10) (n / 10) hlt hxy
  nth_rewrite 1 [← Nat.mod_add_div n 10]
  rw [hd]
  simp

lemma digit_sum_plus_digit_sum_digit_sum_le_self_of_ge20 {n : ℕ} (hn : 20 ≤ n) :
    let d := (Nat.digits 10 n).sum
    d + (Nat.digits 10 d).sum ≤ n := by
  intro d
  have hn0 : n ≠ 0 := by omega
  have hd_eq : d = n % 10 + (Nat.digits 10 (n / 10)).sum := digitSum_eq_mod_add_digitSum_div n hn0
  have hdsum_le : (Nat.digits 10 (n / 10)).sum ≤ n / 10 := Nat.digit_sum_le 10 (n / 10)
  have hd_le : d ≤ n % 10 + n / 10 := by omega
  have he_le : (Nat.digits 10 d).sum ≤ d := Nat.digit_sum_le 10 d
  have hq : 2 ≤ n / 10 := by omega
  have hr : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hn_decomp : n = n % 10 + 10 * (n / 10) := by rw [Nat.mod_add_div]
  calc
    d + (Nat.digits 10 d).sum ≤ 2 * d := by omega
    _ ≤ 2 * (n % 10 + n / 10) := by nlinarith
    _ ≤ n % 10 + 10 * (n / 10) := by nlinarith
    _ = n := by omega

lemma nine_mul_lt_pow10 {M : ℕ} (hM : 0 < M) : 9 * M < 10 ^ M := by
  induction M with
  | zero => omega
  | succ M ih =>
      cases M with
      | zero => norm_num
      | succ M =>
          have ih' : 9 * (M+1) < 10 ^ (M+1) := ih (by omega)
          rw [pow_succ]
          nlinarith [pow_pos (by norm_num : (0:ℕ) < 10) (M+1)]

lemma arith_construct {P d c : ℕ} (hd0 : 0 < d) (hdP : d ≤ P) (hc : c + (d - 1) = P - 1) :
    c + P * ((d - 1) + P * d) = d * (P * (P + 1) - 1) := by
  apply Nat.cast_injective (R := ℤ)
  have hcZ : (c:ℤ) + ((d:ℤ) - 1) = (P:ℤ) - 1 := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hc
    push_cast at this
    rw [Int.ofNat_sub (Nat.succ_le_of_lt hd0), Int.ofNat_sub (by omega : 1 ≤ P)] at this
    exact this
  have hR : (1:ℕ) ≤ P * (P + 1) := by nlinarith [Nat.succ_le_of_lt hd0, hdP]
  push_cast
  rw [Int.ofNat_sub (Nat.succ_le_of_lt hd0), Int.ofNat_sub hR]
  push_cast
  nlinarith

lemma exists_partner_large {n : ℕ} (hn : 20 ≤ n) :
    ∃ k : ℕ, k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n := by
  let d := (Nat.digits 10 n).sum
  let e := (Nat.digits 10 d).sum
  let M := (n - e) / 9
  let A := Nat.digitsAppend 10 M (d - 1)
  let B := A.map (fun x => 9 - x)
  let L := B ++ A ++ Nat.digits 10 d
  let q := Nat.ofDigits 10 L
  have hnpos : 0 < n := by omega
  have hnne : n ≠ 0 := by omega
  have hdpos : 0 < d := by
    have hne : Nat.digits 10 n ≠ [] := (Nat.digits_ne_nil_iff_ne_zero).mpr hnne
    have hlastne := Nat.getLast_digit_ne_zero 10 hnne
    have hmem := List.getLast_mem hne
    have hle := List.le_sum_of_mem (xs := Nat.digits 10 n) hmem
    omega
  have he_le_d : e ≤ d := Nat.digit_sum_le 10 d
  have hde_le_n : d + e ≤ n := digit_sum_plus_digit_sum_digit_sum_le_self_of_ge20 hn
  have he_le_n : e ≤ n := by omega
  have hnd : n ≡ d [MOD 9] := Nat.modEq_nine_digits_sum n
  have hde : d ≡ e [MOD 9] := Nat.modEq_nine_digits_sum d
  have hne_mod : e ≡ n [MOD 9] := (hnd.trans hde).symm
  have hdvd9 : 9 ∣ n - e := (Nat.modEq_iff_dvd' he_le_n).mp hne_mod
  have h9M : 9 * M = n - e := by
    dsimp [M]
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvd9
  have hd_le_9M : d ≤ 9 * M := by omega
  have hMpos : 0 < M := by omega
  have h9M_lt : 9 * M < 10 ^ M := nine_mul_lt_pow10 hMpos
  have hd_lt_pow : d < 10 ^ M := lt_of_le_of_lt hd_le_9M h9M_lt
  have hdm1_lt : d - 1 < 10 ^ M := by omega
  have hAlen : A.length = M := by
    dsimp [A]
    exact Nat.length_digitsAppend (by norm_num) M hdm1_lt
  have hAlt : ∀ x ∈ A, x < 10 := by
    intro x hx; dsimp [A] at hx; exact Nat.lt_of_mem_digitsAppend (by norm_num) M x hx
  have hBlen : B.length = M := by dsimp [B]; simp [hAlen]
  have hBlt : ∀ x ∈ B, x < 10 := by
    intro x hx
    dsimp [B] at hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hylt := hAlt y hy
    omega
  have hLlt : ∀ x ∈ L, x < 10 := by
    intro x hx
    dsimp [L] at hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact hBlt x hx
      · exact hAlt x hx
    · exact Nat.digits_lt_base (by norm_num) hx
  have hLsum : L.sum = n := by
    have hcomp := List.sum_map_nine_sub_add_sum A hAlt
    have hdigitd : (Nat.digits 10 d).sum = e := rfl
    dsimp [L, B]
    rw [List.sum_append_nat, List.sum_append_nat]
    omega
  have hqsum : (Nat.digits 10 q).sum = n := by
    have hLmem : L ∈ {L : List ℕ | L.length = L.length ∧ ∀ x ∈ L, x < 10} := by
      exact ⟨rfl, hLlt⟩
    dsimp [q]
    rw [Nat.sum_digits_ofDigits_eq_sum (by norm_num) hLmem, hLsum]
  have hAod : Nat.ofDigits 10 A = d - 1 := by
    dsimp [A, Nat.digitsAppend]
    rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  have hcompOD : Nat.ofDigits 10 B + Nat.ofDigits 10 A = 10 ^ M - 1 := by
    dsimp [B]
    rw [Nat.ofDigits_map_nine_sub_add_ofDigits A hAlt, hAlen]
  have hqeq : q = d * ((10 ^ M) * ((10 ^ M) + 1) - 1) := by
    dsimp [q, L]
    rw [Nat.ofDigits_append, Nat.ofDigits_append]
    rw [hBlen, hAod, Nat.ofDigits_digits]
    rw [List.length_append, hBlen, hAlen]
    rw [pow_add]
    have hmain := arith_construct hdpos (by omega : d ≤ 10 ^ M) (by simpa [hAod] using hcompOD)
    rw [← hmain]
    ring
  have hdvdq : d ∣ q := by
    rw [hqeq]
    exact dvd_mul_right d _
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    have : (Nat.digits 10 q).sum = 0 := by simp [hq0]
    omega
  refine ⟨10 ^ n * q, ?_, ?_, ?_, ?_⟩
  · positivity
  · have hpow : n < 10 ^ n := Nat.lt_pow_self (by norm_num)
    have hle : 10 ^ n ≤ 10 ^ n * q := by
      exact Nat.le_mul_of_pos_right (10 ^ n) hqpos
    omega
  · exact dvd_mul_of_dvd_right hdvdq (10 ^ n)
  · have hshift := Nat.digits_base_pow_mul (b := 10) (k := n) (m := q) (by norm_num) hqpos
    rw [hshift]
    simp [hqsum]


/-- Small positive integers have directly checkable partners. -/
lemma exists_partner_small {n : ℕ} (hnpos : n > 0) (hnot : ¬ 20 ≤ n) :
    ∃ k : ℕ, k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n := by
  have hnle : n ≤ 19 := by omega
  interval_cases n
  · exact ⟨10, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨10, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨12, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨20, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨10, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨12, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨70, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨40, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨18, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨1, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨10, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨3, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨76, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨10, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨12, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨35, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨296, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨9, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩
  · exact ⟨10, by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]⟩

lemma exists_partner (n : ℕ) (hnpos : n > 0) :
    ∃ k : ℕ, k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n := by
  by_cases hn20 : 20 ≤ n
  · exact exists_partner_large hn20
  · exact exists_partner_small hnpos hn20

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hnpos
  rcases exists_partner n hnpos with ⟨k, hkpos, hkne, hdvd, hkdvd⟩
  have hnon : ({k : ℕ | k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n} : Set ℕ).Nonempty := by
    exact ⟨k, hkpos, hkne, hdvd, hkdvd⟩
  unfold a
  dsimp only
  rw [dif_pos hnon]
  exact Nat.ne_of_gt (Nat.sInf_mem hnon).1
