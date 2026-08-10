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


lemma a_ne_zero_of_partner {n k : ℕ}
    (hkpos : k > 0) (hkne : k ≠ n)
    (hndvd : (digits 10 n).sum ∣ k) (hkdvd : (digits 10 k).sum ∣ n) : a n ≠ 0 := by
  unfold a
  dsimp only
  let partners : Set ℕ := {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n}
  have hne : partners.Nonempty := by
    refine ⟨k, ?_⟩
    exact ⟨hkpos, hkne, hndvd, hkdvd⟩
  rw [dif_pos hne]
  intro hz
  have hmem : sInf partners ∈ partners := Nat.sInf_mem hne
  rw [hz] at hmem
  exact (Nat.lt_irrefl 0) hmem.1

noncomputable def D (n : ℕ) : ℕ := (digits 10 n).sum

lemma D_rec {n : ℕ} (hn : 0 < n) : D n = n % 10 + D (n / 10) := by
  unfold D
  rw [Nat.digits_def' (by norm_num) hn]
  simp

lemma D_lt_self {n : ℕ} (hn : 10 ≤ n) : D n < n := by
  rw [D_rec (lt_of_lt_of_le (by norm_num) hn)]
  have hD : D (n / 10) ≤ n / 10 := by
    unfold D
    exact Nat.digit_sum_le 10 (n / 10)
  have hx : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hdecomp : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
  nlinarith

lemma D_add9_le_self {n : ℕ} (hn : 10 ≤ n) : D n + 9 ≤ n := by
  have hle : D n ≤ n := by unfold D; exact Nat.digit_sum_le 10 n
  have hlt : D n < n := D_lt_self hn
  have hmod : n ≡ D n [MOD 9] := by
    unfold D
    exact Nat.modEq_nine_digits_sum n
  rw [Nat.ModEq] at hmod
  omega

lemma ten_mul_D_le_self {n : ℕ} (hn : 100 ≤ n) : 10 * D n ≤ n := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rw [D_rec hnpos]
  let q := n / 10
  let r := n % 10
  have hq : 10 ≤ q := by
    dsimp [q]
    have hdecomp0 : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
    omega
  have hr : r < 10 := by dsimp [r]; exact Nat.mod_lt _ (by norm_num)
  have hqD : D q + 9 ≤ q := D_add9_le_self hq
  dsimp [q] at hqD
  have hdecomp : 10 * q + r = n := by
    dsimp [q, r]
    exact Nat.div_add_mod n 10
  omega

lemma ofDigits_compl_add (P : List ℕ) (hP : ∀ x ∈ P, x ≤ 9) :
    Nat.ofDigits 10 (P.map (fun x => 9 - x)) + Nat.ofDigits 10 P = 10 ^ P.length - 1 := by
  induction P with
  | nil => simp [Nat.ofDigits]
  | cons a tl ih =>
      have ha : a ≤ 9 := hP a (by simp)
      have htl : ∀ x ∈ tl, x ≤ 9 := by intro x hx; exact hP x (by simp [hx])
      have ih' := ih htl
      simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons]
      let C := Nat.ofDigits 10 (List.map (fun x => 9 - x) tl)
      let E := Nat.ofDigits 10 tl
      have hleft : 9 - a + 10 * C + (a + 10 * E) = 9 + 10 * (C + E) := by omega
      rw [hleft, ih']
      have hp : 1 ≤ 10 ^ tl.length := Nat.one_le_pow tl.length 10 (by norm_num)
      rw [Nat.pow_succ']
      omega

lemma sum_compl_add (P : List ℕ) (hP : ∀ x ∈ P, x ≤ 9) :
    (P.map (fun x => 9 - x)).sum + P.sum = 9 * P.length := by
  induction P with
  | nil => simp
  | cons a tl ih =>
      have ha : a ≤ 9 := hP a (by simp)
      have htl : ∀ x ∈ tl, x ≤ 9 := by intro x hx; exact hP x (by simp [hx])
      have ih' := ih htl
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

lemma D_pos {n : ℕ} (hn : 0 < n) : 0 < D n := by
  unfold D
  by_contra h
  have hsum : (digits 10 n).sum = 0 := by omega
  have hlast := Nat.getLast_digit_ne_zero 10 ((_root_.ne_of_gt hn))
  have hmem := List.getLast_mem (Nat.digits_ne_nil_iff_ne_zero.mpr ((_root_.ne_of_gt hn)) : digits 10 n ≠ [])
  have hall := (List.sum_eq_zero_iff.mp hsum) ((digits 10 n).getLast _) hmem
  exact hlast hall

lemma large_partner (n : ℕ) (hn : 100 ≤ n) :
    ∃ k, k > 0 ∧ k ≠ n ∧ D n ∣ k ∧ D k ∣ n := by
  let d := D n
  let dd := D d
  let T := (n - dd) / 9
  let base := digits 10 (d - 1)
  let P := base ++ List.replicate (T - base.length) 0
  let C := P.map (fun x => 9 - x)
  let block := C ++ P
  let L := block ++ ([0] ++ digits 10 d)
  let k := Nat.ofDigits 10 L
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hdpos : 0 < d := by dsimp [d]; exact D_pos hnpos
  have hdd_le_d : dd ≤ d := by dsimp [dd, D]; exact Nat.digit_sum_le 10 d
  have hd_le_n10 : 10 * d ≤ n := by dsimp [d]; exact ten_mul_D_le_self hn
  have hdd_le_n : dd ≤ n := by omega
  have hmod1 : n % 9 = d % 9 := by
    have h := Nat.modEq_nine_digits_sum n
    dsimp [d, D]
    rw [Nat.ModEq] at h
    exact h
  have hmod2 : d % 9 = dd % 9 := by
    have h := Nat.modEq_nine_digits_sum d
    dsimp [dd, D]
    rw [Nat.ModEq] at h
    exact h
  have hmod : n % 9 = dd % 9 := hmod1.trans hmod2
  have hT_eq : dd + 9 * T = n := by
    dsimp [T]
    have hzero : (n - dd) % 9 = 0 := by omega
    have hdecomp : 9 * ((n-dd)/9) + (n-dd)%9 = n-dd := Nat.div_add_mod (n-dd) 9
    omega
  have hd_le_T : d ≤ T := by
    have : 9 * d + dd ≤ n := by nlinarith
    omega
  have hTpow : T < 10 ^ T := Nat.lt_pow_self (by norm_num : 1 < 10)
  have hdm1_pow : d - 1 < 10 ^ T := by omega
  have hbase_len : base.length ≤ T := by
    dsimp [base]
    exact (Nat.digits_length_le_iff (by norm_num : 1 < 10) (d - 1)).2 hdm1_pow
  have hP_len : P.length = T := by
    dsimp [P]
    simp [hbase_len]
  have hP_sum : P.sum = D (d - 1) := by
    dsimp [P, base, D]
    simp
  have hP_val : Nat.ofDigits 10 P = d - 1 := by
    dsimp [P, base]
    rw [Nat.ofDigits_append]
    simp [Nat.ofDigits_digits]
  have hP_le : ∀ x ∈ P, x ≤ 9 := by
    intro x hx
    dsimp [P, base] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have hxlt : x < 10 := Nat.digits_lt_base (by norm_num : 1 < 10) hx
      omega
    · simp at hx
      omega
  have hCP_sum : C.sum + P.sum = 9 * T := by
    dsimp [C]
    rw [sum_compl_add P hP_le, hP_len]
  have hL_sum : L.sum = n := by
    change ((C ++ P) ++ ([0] ++ digits 10 d)).sum = n
    rw [List.sum_append]
    rw [List.sum_append]
    change C.sum + P.sum + (0 :: digits 10 d).sum = n
    rw [List.sum_cons]
    simp only [zero_add]
    rw [hCP_sum]
    have hdd_def : dd = (digits 10 d).sum := rfl
    omega
  have hC_len : C.length = T := by dsimp [C]; simp [hP_len]
  have hblock_dvd : d ∣ Nat.ofDigits 10 block := by
    have hcomp := ofDigits_compl_add P hP_le
    change Nat.ofDigits 10 C + Nat.ofDigits 10 P = 10 ^ P.length - 1 at hcomp
    rw [hP_len, hP_val] at hcomp
    have hAplus : Nat.ofDigits 10 C + d = 10 ^ T := by omega
    have hblock_add : Nat.ofDigits 10 block + d = 10 ^ T * d := by
      dsimp [block]
      rw [Nat.ofDigits_append, hC_len, hP_val]
      have hd1 : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
      calc
        Nat.ofDigits 10 C + 10 ^ T * (d - 1) + d
            = (Nat.ofDigits 10 C + d) + 10 ^ T * (d - 1) := by omega
        _ = 10 ^ T + 10 ^ T * (d - 1) := by rw [hAplus]
        _ = 10 ^ T * d := by
          rw [← hd1]
          have hpred : d - 1 + 1 - 1 = d - 1 := by omega
          rw [hpred]
          ring
    have hblock_eq : Nat.ofDigits 10 block = 10 ^ T * d - d := by omega
    rw [hblock_eq]
    exact Nat.dvd_sub (Nat.dvd_mul_left d (10 ^ T)) (dvd_refl d)
  have htail_dvd : d ∣ Nat.ofDigits 10 ([0] ++ digits 10 d) := by
    rw [Nat.ofDigits_append]
    simp [Nat.ofDigits_digits]
  have hk_dvd : d ∣ k := by
    dsimp [k, L]
    rw [Nat.ofDigits_append]
    apply Nat.dvd_add hblock_dvd
    exact dvd_mul_of_dvd_right htail_dvd (10 ^ block.length)
  have hL_lt : ∀ x ∈ L, x < 10 := by
    intro x hx
    change x ∈ (C ++ P) ++ ([0] ++ digits 10 d) at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.mem_append] at hx
      rcases hx with hcx | hpx
      · have : x ≤ 9 := by
          dsimp [C] at hcx
          rcases List.mem_map.mp hcx with ⟨y, hy, rfl⟩
          have hy9 := hP_le y hy
          omega
        omega
      · have hx9 := hP_le x hpx
        omega
    · rw [List.mem_append] at hx
      rcases hx with hx0 | hdx
      · simp at hx0
        omega
      · exact Nat.digits_lt_base (by norm_num : 1 < 10) hdx
  have hdigits_ne : digits 10 d ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (_root_.ne_of_gt hdpos)
  have hL_last : ∀ h : L ≠ [], L.getLast h ≠ 0 := by
    intro h
    change (block ++ ([0] ++ digits 10 d)).getLast h ≠ 0
    have htail_ne : [0] ++ digits 10 d ≠ [] := by simp
    rw [List.getLast_append_of_ne_nil h htail_ne]
    have htail_last : ([0] ++ digits 10 d).getLast htail_ne = (digits 10 d).getLast hdigits_ne := by
      rw [List.getLast_append_of_ne_nil htail_ne hdigits_ne]
    rw [htail_last]
    exact Nat.getLast_digit_ne_zero 10 (_root_.ne_of_gt hdpos)
  have hdigits_k : digits 10 k = L := by
    dsimp [k]
    exact Nat.digits_ofDigits 10 (by norm_num : 1 < 10) L hL_lt hL_last
  have hDk : D k = n := by
    unfold D
    rw [hdigits_k, hL_sum]
  have hkpos : k > 0 := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hz : D k = 0 := by
      rw [hk0]
      unfold D
      simp [Nat.digits_zero]
    omega
  have hkne : k ≠ n := by
    intro hkn
    have hDnn : D n = n := by simpa [hkn] using hDk
    have hd_eq_n : d = n := by simpa [d] using hDnn
    have : d < n := by nlinarith
    omega
  refine ⟨k, hkpos, hkne, ?_, ?_⟩
  · simpa [d] using hk_dvd
  · rw [hDk]


/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  by_cases hlarge : 100 ≤ n
  · rcases large_partner n hlarge with ⟨k, hkpos, hkne, hdn, hdk⟩
    exact a_ne_zero_of_partner hkpos hkne (by simpa [D] using hdn) (by simpa [D] using hdk)
  · have hnle : n ≤ 99 := by omega
    interval_cases n

    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=100) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=70) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=18) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=3) <;> norm_num
    · apply a_ne_zero_of_partner (k:=100) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1001) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=3) <;> norm_num
    · apply a_ne_zero_of_partner (k:=100) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=14) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=20999) <;> norm_num
    · apply a_ne_zero_of_partner (k:=3) <;> norm_num
    · apply a_ne_zero_of_partner (k:=100) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1001) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=11) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=100) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=99799) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=6059999) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=52) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1001) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=11) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1001) <;> norm_num
    · apply a_ne_zero_of_partner (k:=7998998) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9998989) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=319) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=98999797) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10010) <;> norm_num
    · apply a_ne_zero_of_partner (k:=30) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1001) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=11) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1001) <;> norm_num
    · apply a_ne_zero_of_partner (k:=70) <;> norm_num
    · apply a_ne_zero_of_partner (k:=30) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=80499989999) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=104) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10010) <;> norm_num
    · apply a_ne_zero_of_partner (k:=30) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9999999998) <;> norm_num
    · apply a_ne_zero_of_partner (k:=9) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10) <;> norm_num
    · apply a_ne_zero_of_partner (k:=11) <;> norm_num
    · apply a_ne_zero_of_partner (k:=12) <;> norm_num
    · apply a_ne_zero_of_partner (k:=1001) <;> norm_num
    · apply a_ne_zero_of_partner (k:=14) <;> norm_num
    · apply a_ne_zero_of_partner (k:=30) <;> norm_num
    · apply a_ne_zero_of_partner (k:=10000) <;> norm_num
    · apply a_ne_zero_of_partner (k:=100000001) <;> norm_num
    · apply a_ne_zero_of_partner (k:=18) <;> norm_num
