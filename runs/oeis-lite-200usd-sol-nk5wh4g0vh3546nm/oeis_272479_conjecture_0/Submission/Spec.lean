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
private def ds (n : ℕ) := (digits 10 n).sum

private lemma ds_le (n : ℕ) : ds n ≤ n := by
  exact Nat.digit_sum_le 10 n

private lemma ds_pos {n : ℕ} (hn : 0 < n) : 0 < ds n := by
  unfold ds
  have hne : digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hm := List.getLast_mem (l := digits 10 n) hne
  have hz : (digits 10 n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 10 (by omega)
  have hle : (digits 10 n).getLast hne ≤ (digits 10 n).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hm
  omega

private lemma ds_le_nine_add_div (n : ℕ) : ds n ≤ 9 + n / 10 := by
  by_cases hn : n = 0
  · simp [hn, ds]
  · rw [ds, Nat.digits_eq_cons_digits_div (by norm_num) hn, List.sum_cons]
    have hmod : n % 10 ≤ 9 := by omega
    have htail := Nat.digit_sum_le 10 (n / 10)
    omega

private lemma ds_modeq (n : ℕ) : n ≡ ds n [MOD 9] := by
  exact Nat.modEq_nine_digits_sum n

private lemma pow_bound {q : ℕ} (hq : 3 ≤ q) : 10 * (q + 1) < 10 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      calc
        10 * (q + 1 + 1) ≤ 10 * (10 * (q + 1)) := by nlinarith
        _ < 10 * 10 ^ q := (Nat.mul_lt_mul_left (by norm_num : 0 < 10)).mpr ih
        _ = 10 ^ (q + 1) := by ring

private lemma crucial_bound {n q : ℕ} (hn : 0 < n)
    (heq : n = ds (ds n) + 9 * q) (hq : 0 < q) : ds n < 10 ^ q := by
  let d := ds n
  let e := ds d
  have he_le_d : e ≤ d := ds_le d
  have hd_le : d ≤ 9 + n / 10 := ds_le_nine_add_div n
  have heq' : n = e + 9 * q := by simpa [d, e] using heq
  have hn_le : n ≤ 10 * (q + 1) := by
    have : n ≤ 9 + n / 10 + 9 * q := by omega
    omega
  rcases lt_trichotomy q 2 with hq2 | hq2 | hq2
  · have hq1 : q = 1 := by omega
    subst q
    norm_num only [Nat.reduceMul, Nat.reduceAdd] at hn_le heq'
    interval_cases n <;> norm_num [ds] at heq <;> norm_num [ds]
  · have hqeq : q = 2 := by omega
    subst q
    have hd_n : d ≤ n := by simpa [d] using ds_le n
    have : d < 100 := by omega
    simpa [d] using this
  · have h3 : 3 ≤ q := by omega
    have hd_n : d ≤ n := by simpa [d] using ds_le n
    have : d < 10 ^ q := lt_of_le_of_lt hd_n (lt_of_le_of_lt hn_le (pow_bound h3))
    simpa [d] using this

private lemma complement_sum (L : List ℕ) (hL : ∀ x ∈ L, x < 10) :
    L.sum + (L.map fun x => 9 - x).sum = 9 * L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
      simp only [List.sum_cons, List.map_cons, List.length_cons]
      have hx := hL x (by simp)
      have hi := ih (fun y hy => hL y (by simp [hy]))
      simp only [List.sum_cons] at *
      omega

private lemma complement_value (L : List ℕ) (hL : ∀ x ∈ L, x < 10) :
    Nat.ofDigits 10 L + Nat.ofDigits 10 (L.map fun x => 9 - x) =
      10 ^ L.length - 1 := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons x L ih =>
      have hx := hL x (by simp)
      have hi := ih (fun y hy => hL y (by simp [hy]))
      have hp : 0 < 10 ^ L.length := pow_pos (by norm_num) _
      have hxcomp : x + (9 - x) = 9 := by omega
      have hip : Nat.ofDigits 10 L + Nat.ofDigits 10 (L.map fun x => 9 - x) + 1 =
          10 ^ L.length := by omega
      simp only [List.map_cons, List.length_cons]
      rw [Nat.ofDigits_cons, Nat.ofDigits_cons, pow_succ]
      omega
private lemma ds_lt_self {n : ℕ} (hn : 10 ≤ n) : ds n < n := by
  have hn0 : n ≠ 0 := by omega
  rw [ds, Nat.digits_eq_cons_digits_div (by norm_num) hn0, List.sum_cons]
  have htail := Nat.digit_sum_le 10 (n / 10)
  have hq : 0 < n / 10 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 10)).2 hn
  have hdecomp := Nat.mod_add_div n 10
  omega

private lemma ds_ten_mul {m : ℕ} (hm : 0 < m) : ds (10 * m) = ds m := by
  unfold ds
  rw [Nat.digits_base_mul (by norm_num) hm]
  simp

private lemma exists_partner (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, k > 0 ∧ k ≠ n ∧ ds n ∣ k ∧ ds k ∣ n := by
  let d := ds n
  let e := ds d
  let q := (n - e) / 9
  have hdpos : 0 < d := by simpa [d] using ds_pos hn
  have he_le_d : e ≤ d := by simpa [e] using ds_le d
  have hd_le_n : d ≤ n := by simpa [d] using ds_le n
  have he_le_n : e ≤ n := he_le_d.trans hd_le_n
  have hmod : n ≡ e [MOD 9] := by
    exact (ds_modeq n).trans (by simpa [d, e] using ds_modeq d)
  have hdvdsub : 9 ∣ n - e := (Nat.modEq_iff_dvd' he_le_n).mp hmod.symm
  have heq : n = e + 9 * q := by
    have hcancel : 9 * ((n - e) / 9) = n - e := Nat.mul_div_cancel' hdvdsub
    dsimp [q]
    omega
  by_cases hq : q = 0
  · have hne : n = e := by omega
    have hdn : d = n := by omega
    have hnlt : n < 10 := by
      by_contra h
      have := ds_lt_self (n := n) (by omega)
      omega
    refine ⟨10 * n, by positivity, by omega, ?_, ?_⟩
    · simpa [d, hdn]
    · have := ds_ten_mul (m := n) hn
      have hds : ds n = n := by simpa [d] using hdn
      rw [this, hds]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hdbound : d < 10 ^ q := by
      simpa [d, e] using crucial_bound hn (by simpa [d, e] using heq) hqpos
    let A := Nat.digitsAppend 10 q (d - 1)
    let B := A.map fun x => 9 - x
    let L₀ := B ++ digits 10 (d - 1)
    let L := L₀ ++ digits 10 d
    let K := 0 :: L
    let k := Nat.ofDigits 10 K
    have hdm1 : d - 1 < 10 ^ q := lt_of_le_of_lt (Nat.sub_le d 1) hdbound
    have hAlen : A.length = q := by
      simpa [A] using Nat.length_digitsAppend (by norm_num : 1 < 10) q hdm1
    have hAdig : ∀ x ∈ A, x < 10 := by
      intro x hx
      exact Nat.lt_of_mem_digitsAppend (by norm_num) q x (by simpa [A] using hx)
    have hAval : Nat.ofDigits 10 A = d - 1 := by
      change Nat.ofDigits 10
        (digits 10 (d - 1) ++ List.replicate (q - (digits 10 (d - 1)).length) 0) = d - 1
      rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
    have hBsum : A.sum + B.sum = 9 * q := by
      simpa [B, hAlen] using complement_sum A hAdig
    have hBvaladd : Nat.ofDigits 10 A + Nat.ofDigits 10 B = 10 ^ q - 1 := by
      simpa [B, hAlen] using complement_value A hAdig
    have hBval : Nat.ofDigits 10 B = 10 ^ q - d := by
      have hdle : d ≤ 10 ^ q := Nat.le_of_lt hdbound
      omega
    have hBlen : B.length = q := by simp [B, hAlen]
    have hL0val : Nat.ofDigits 10 L₀ = d * (10 ^ q - 1) := by
      rw [show L₀ = B ++ digits 10 (d - 1) by rfl, Nat.ofDigits_append,
        hBval, hBlen, Nat.ofDigits_digits]
      have hdle : d ≤ 10 ^ q := Nat.le_of_lt hdbound
      have hpdeq : 10 ^ q - d + d = 10 ^ q := Nat.sub_add_cancel hdle
      have hd1eq : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
      nlinarith
    have hdvdL0 : d ∣ Nat.ofDigits 10 L₀ := by
      rw [hL0val]
      exact dvd_mul_right d _
    have hdvdL : d ∣ Nat.ofDigits 10 L := by
      rw [show L = L₀ ++ digits 10 d by rfl, Nat.ofDigits_append, Nat.ofDigits_digits]
      exact dvd_add hdvdL0 (dvd_mul_left d _)
    have hdvdk : d ∣ k := by
      rw [show k = Nat.ofDigits 10 (0 :: L) by rfl, Nat.ofDigits_cons]
      simpa [mul_comm] using dvd_mul_of_dvd_right hdvdL 10
    have hLsum : L.sum = n := by
      rw [show L = (B ++ digits 10 (d - 1)) ++ digits 10 d by rfl]
      simp only [List.sum_append_nat]
      have hAsum : A.sum = ds (d - 1) := by
        simp [A, Nat.digitsAppend, ds]
      have hdsd : (digits 10 d).sum = e := by rfl
      have hdsdm1 : (digits 10 (d - 1)).sum = A.sum := by
        simpa [ds] using hAsum.symm
      rw [hdsdm1, hdsd]
      omega
    have hKdig : ∀ x ∈ K, x < 10 := by
      intro x hx
      simp only [K, List.mem_cons] at hx
      rcases hx with rfl | hx
      · norm_num
      · simp only [L, L₀, List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · simp only [B, List.mem_map] at hx
          obtain ⟨a, ha, rfl⟩ := hx
          have := hAdig a ha
          omega
        · exact Nat.digits_lt_base (by norm_num) hx
        · exact Nat.digits_lt_base (by norm_num) hx
    have hdsk : ds k = n := by
      unfold ds
      rw [show k = Nat.ofDigits 10 K by rfl]
      rw [Nat.sum_digits_ofDigits_eq_sum (by norm_num : 1 < 10)
        (show K.length = K.length ∧ ∀ x ∈ K, x < 10 from ⟨rfl, hKdig⟩)]
      simp [K, hLsum]
    have hkpos : 0 < k := by
      have hle : ds k ≤ k := ds_le k
      rw [hdsk] at hle
      omega
    refine ⟨k, hkpos, ?_, by simpa [d] using hdvdk, ?_⟩
    · intro hkn
      have hself : ds n = n := by simpa [hkn] using hdsk
      have hnlt : n < 10 := by
        by_contra h
        exact (ds_lt_self (n := n) (by omega)).ne hself
      have hd : d = n := by simpa [d] using hself
      have he' : e = n := by simp [e, hd, hself]
      omega
    · rw [hdsk]
/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  unfold a
  dsimp only
  split_ifs with h
  · have hm := Nat.sInf_mem h
    exact Nat.ne_of_gt hm.1
  · exfalso
    apply h
    obtain ⟨k, hkpos, hkne, hdk, hkn⟩ := exists_partner n hn
    exact ⟨k, hkpos, hkne, by simpa [ds] using hdk, by simpa [ds] using hkn⟩
