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

namespace HarshadA272479

private def D (n : ℕ) : ℕ := (digits 10 n).sum

private lemma D_le_self (n : ℕ) : D n ≤ n := by
  simpa [D] using Nat.digit_sum_le 10 n

private lemma D_pos {n : ℕ} (hn : 0 < n) : 0 < D n := by
  unfold D
  have hnz : n ≠ 0 := by omega
  let hne : digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hnz
  let x := (digits 10 n).getLast hne
  have hxmem : x ∈ digits 10 n := List.getLast_mem _
  have hxne : x ≠ 0 := Nat.getLast_digit_ne_zero 10 hnz
  have hxle : x ≤ (digits 10 n).sum := List.single_le_sum (by intro y hy; exact Nat.zero_le y) x hxmem
  omega

private lemma digits_ten_mul (n : ℕ) : D (10 * n) = D n := by
  unfold D
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.digits_base_mul (by norm_num : 1 < 10) (Nat.pos_of_ne_zero hn)]
    simp

private lemma compl_ofDigits_aux (L : List ℕ) (hL : ∀ x ∈ L, x ≤ 9) :
    Nat.ofDigits 10 (L.map fun x => 9 - x) = 10 ^ L.length - 1 - Nat.ofDigits 10 L := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ 9 := hL x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ 9 := by intro y hy; exact hL y (by simp [hy])
      specialize ih hxs
      have hlt : Nat.ofDigits 10 xs < 10 ^ xs.length :=
        Nat.ofDigits_lt_base_pow_length (by norm_num : 1 < 10) (by
          intro y hy
          have := hxs y hy
          omega)
      simp [Nat.ofDigits_cons, ih, Nat.pow_succ]
      omega

private lemma sum_le_nine_len (L : List ℕ) (hL : ∀ x ∈ L, x ≤ 9) : L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ 9 := hL x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ 9 := by intro y hy; exact hL y (by simp [hy])
      specialize ih hxs
      simp
      omega

private lemma compl_sum_aux (L : List ℕ) (hL : ∀ x ∈ L, x ≤ 9) :
    (L.map fun x => 9 - x).sum = 9 * L.length - L.sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ 9 := hL x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ 9 := by intro y hy; exact hL y (by simp [hy])
      specialize ih hxs
      have hsum := sum_le_nine_len xs hxs
      simp [ih]
      omega

private lemma all_lt10_digitsAppend (m x : ℕ) : ∀ y ∈ Nat.digitsAppend 10 m x, y < 10 := by
  intro y hy
  exact Nat.lt_of_mem_digitsAppend (by norm_num : 1 < 10) m y hy

private lemma lower_block (d m : ℕ) (hd0 : 0 < d) (hdm : d ≤ 10 ^ m) :
    ∃ L : List ℕ, L.sum = 9 * m ∧ (∀ x ∈ L, x < 10) ∧ d ∣ Nat.ofDigits 10 L := by
  let A := Nat.digitsAppend 10 m (d - 1)
  let C := A.map fun x => 9 - x
  refine ⟨C ++ A, ?_, ?_, ?_⟩
  · have hlen : A.length = m := by
      apply Nat.length_digitsAppend (by norm_num : 1 < 10)
      have : d - 1 < 10 ^ m := Nat.sub_one_lt_of_le hd0 hdm
      simpa [A] using this
    have hle : ∀ x ∈ A, x ≤ 9 := by
      intro x hx
      have := all_lt10_digitsAppend m (d - 1) x hx
      omega
    have hAsum : A.sum ≤ 9 * m := by simpa [hlen] using sum_le_nine_len A hle
    simp [C, compl_sum_aux A hle, hlen]
    omega
  · intro x hx
    simp [C] at hx
    rcases hx with ⟨y, hy, rfl⟩ | hx
    · have hy9 : y ≤ 9 := by
        have := all_lt10_digitsAppend m (d - 1) y hy
        omega
      omega
    · exact all_lt10_digitsAppend m (d - 1) x hx
  · have hlen : A.length = m := by
      apply Nat.length_digitsAppend (by norm_num : 1 < 10)
      have : d - 1 < 10 ^ m := Nat.sub_one_lt_of_le hd0 hdm
      simpa [A] using this
    have hle : ∀ x ∈ A, x ≤ 9 := by
      intro x hx
      have := all_lt10_digitsAppend m (d - 1) x hx
      omega
    have hofA : Nat.ofDigits 10 A = d - 1 := by
      simp [A, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
    have hofC : Nat.ofDigits 10 C = 10 ^ m - d := by
      dsimp [C]
      rw [compl_ofDigits_aux A hle, hlen, hofA]
      omega
    have hClen : C.length = m := by simp [C, hlen]
    rw [Nat.ofDigits_append, hofC, hofA, hClen]
    use 10 ^ m - 1
    rw [Nat.mul_sub_left_distrib d (10 ^ m) 1, Nat.mul_one]
    rw [Nat.mul_comm (10 ^ m) (d - 1), Nat.mul_sub_right_distrib d 1 (10 ^ m), Nat.one_mul]
    have hdmul : 10 ^ m ≤ 10 ^ m * d := Nat.le_mul_of_pos_right (10 ^ m) hd0
    have hcomm : d * 10 ^ m = 10 ^ m * d := Nat.mul_comm d (10 ^ m)
    rw [hcomm]
    omega

private lemma D_mod_9 (n : ℕ) : n % 9 = D n % 9 := by
  have h := Nat.modEq_nine_digits_sum n
  exact h

private lemma D_iter_mod_9 (n : ℕ) : n % 9 = D (D n) % 9 := by
  rw [D_mod_9 n, D_mod_9 (D n)]

private lemma pow10_ge_add9 {q : ℕ} (hq : 0 < q) : q + 9 ≤ 10 ^ q := by
  induction q with
  | zero => omega
  | succ q ih =>
      cases q with
      | zero => norm_num
      | succ q =>
          have hpos : 0 < q.succ := by omega
          have := ih hpos
          calc
            q.succ.succ + 9 ≤ 10 * (q.succ + 9) := by nlinarith
            _ ≤ 10 * 10 ^ q.succ := by exact Nat.mul_le_mul_left 10 this
            _ = 10 ^ q.succ.succ := by simp [Nat.pow_succ, Nat.mul_comm]

private lemma digit_sum_bound (n : ℕ) (hn : 0 < n) :
    D n ≤ (n - D n) / 9 + 9 := by
  let t := n / 10
  let r := n % 10
  have hr : r < 10 := Nat.mod_lt n (by norm_num)
  have hn_ne : n ≠ 0 := by omega
  have hdig : digits 10 n = r :: digits 10 t := by
    rw [Nat.digits_eq_cons_digits_div (by norm_num : 1 < 10) hn_ne]
  have hn_eq : n = r + 10 * t := by
    have h := (Nat.div_add_mod n 10).symm
    dsimp [t, r]
    omega
  have hD : D n = r + D t := by simp [D, hdig]
  have hDt : D t ≤ t := D_le_self t
  have hge : 9 * t ≤ n - D n := by
    have hDnle : D n ≤ n := D_le_self n
    omega
  have hge' : t * 9 ≤ n - D n := by simpa [Nat.mul_comm] using hge
  have ht : t ≤ (n - D n) / 9 := Nat.le_div_iff_mul_le (by norm_num : 0 < 9) |>.2 hge'
  omega

private lemma q_bound (n : ℕ) (hn : 0 < n) (q : ℕ) (hq : q = (n - D (D n)) / 9) (hqpos : 0 < q) :
    D n ≤ 10 ^ q := by
  have hDle : D (D n) ≤ D n := D_le_self (D n)
  have hmono : n - D n ≤ n - D (D n) := Nat.sub_le_sub_left hDle n
  have hdiv : (n - D n) / 9 ≤ q := by
    rw [hq]
    exact Nat.div_le_div_right hmono
  have hb := digit_sum_bound n hn
  have : D n ≤ q + 9 := by omega
  exact le_trans this (pow10_ge_add9 hqpos)

private lemma nine_dvd_diff_DD (n : ℕ) : 9 ∣ n - D (D n) := by
  have hm : D (D n) ≡ n [MOD 9] := by
    exact (Nat.modEq_iff_dvd).2 (by
      have h : n % 9 = D (D n) % 9 := D_iter_mod_9 n
      omega)
  have hle : D (D n) ≤ n := le_trans (D_le_self (D n)) (D_le_self n)
  have hz : (9 : ℤ) ∣ (n : ℤ) - (D (D n) : ℤ) := Nat.ModEq.dvd hm
  exact_mod_cast hz

private lemma partner_exists (n : ℕ) (hn : 0 < n) :
    {k | 0 < k ∧ k ≠ n ∧ D n ∣ k ∧ D k ∣ n}.Nonempty := by
  let d := D n
  let e := D d
  let q := (n - e) / 9
  have hd0 : 0 < d := D_pos hn
  have he0 : 0 < e := D_pos hd0
  have he_le_n : e ≤ n := le_trans (D_le_self d) (D_le_self n)
  have h9 : 9 ∣ n - e := by simpa [d, e] using nine_dvd_diff_DD n
  have hn_eq : n = e + 9 * q := by
    have := Nat.div_mul_cancel h9
    omega
  by_cases hq0 : q = 0
  · refine ⟨10 * n, ?_⟩
    have hn_eq_e : n = e := by omega
    have hd_eq_n : d = n := by
      have hdle : d ≤ n := D_le_self n
      have hele : e ≤ d := D_le_self d
      omega
    constructor
    · positivity
    constructor
    · intro h
      have : 10 * n > n := by nlinarith
      exact (Nat.ne_of_gt this) h
    constructor
    · change d ∣ 10 * n
      rw [hd_eq_n]
      exact dvd_mul_left n 10
    · rw [digits_ten_mul, show D n = d by rfl, hd_eq_n]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hdq : d ≤ 10 ^ q := q_bound n hn q (by rfl) hqpos
    obtain ⟨L, hLsum, hLlt, hLdvd⟩ := lower_block d q hd0 hdq
    let G := List.replicate (n + 1) 0
    let H := digits 10 d
    let K := L ++ G ++ H
    let k := Nat.ofDigits 10 K
    refine ⟨k, ?_⟩
    have hHlt : ∀ x ∈ H, x < 10 := by
      intro x hx; exact Nat.digits_lt_base (by norm_num : 1 < 10) hx
    have hKlt : ∀ x ∈ K, x < 10 := by
      intro x hx
      simp [K, G, H] at hx
      rcases hx with hx | hx | hx
      · exact hLlt x hx
      · omega
      · exact hHlt x hx
    have hKsum : K.sum = n := by
      dsimp [K, G, H]
      simp only [List.sum_append_nat, List.sum_replicate, nsmul_eq_mul, mul_zero, add_zero]
      rw [hLsum]
      change 9 * q + D d = n
      rw [show D d = e by rfl, hn_eq]
      ring
    have hDk : D k = n := by
      unfold D k
      rw [Nat.sum_digits_ofDigits_eq_sum (by norm_num : 1 < 10) (l := K.length)]
      · exact hKsum
      · exact ⟨rfl, hKlt⟩
    constructor
    · have hsumpos : 0 < K.sum := by simpa [hKsum] using hn
      by_contra hkpos
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkpos
      have hzero : ∀ x ∈ K, x = 0 := Nat.digits_zero_of_eq_zero (by norm_num : (10:ℕ) ≠ 0) hk0
      have : K.sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        exact hzero x hx
      omega
    constructor
    · intro hkn
      have hd_eq_n : d = n := by
        have hdn : D n = n := by
          have htmp := hDk
          rw [hkn] at htmp
          exact htmp
        simpa [d] using hdn
      have he_eq_n : e = n := by
        calc
          e = D d := rfl
          _ = D n := by rw [hd_eq_n]
          _ = d := rfl
          _ = n := hd_eq_n
      omega
    constructor
    · have hval : k = Nat.ofDigits 10 (L ++ G) + 10 ^ (L ++ G).length * Nat.ofDigits 10 H := by
        simp [k, K, H, Nat.ofDigits_append]
      rw [hval]
      apply dvd_add
      · rw [Nat.ofDigits_append]
        simp [G]
        exact hLdvd
      · rw [Nat.ofDigits_digits]
        exact dvd_mul_of_dvd_right (dvd_refl d) _
    · rw [hDk]

end HarshadA272479

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  unfold a
  dsimp only
  rw [dif_pos]
  · have hm := Nat.sInf_mem (HarshadA272479.partner_exists n hn)
    exact Nat.ne_of_gt hm.1
  · simpa [HarshadA272479.D] using HarshadA272479.partner_exists n hn
