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


/-- Digit sum of `ofDigits 10 L` equals `L.sum` when all entries are digits (trailing zeros allowed). -/
lemma dsum_ofDigits_aux (L : List ℕ) (hL : ∀ x ∈ L, x < 10) :
    (Nat.digits 10 (Nat.ofDigits 10 L)).sum = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : a < 10 := hL a (by simp)
    have hL' : ∀ x ∈ L, x < 10 := fun x hx => hL x (by simp [hx])
    have ih' := ih hL'
    rw [Nat.ofDigits_cons, List.sum_cons]
    by_cases h : a ≠ 0 ∨ Nat.ofDigits 10 L ≠ 0
    · rw [Nat.digits_add 10 (by norm_num) a _ ha h, List.sum_cons, ih']
    · push_neg at h
      obtain ⟨rfl, h2⟩ := h
      rw [h2] at ih' ⊢
      simp at ih' ⊢
      exact ih'

lemma ofDigits_flatten_replicate_modEq (d t : ℕ) (ht : 10 ^ t ≡ 1 [MOD d]) (P : List ℕ)
    (hP : t ∣ P.length) (m : ℕ) :
    Nat.ofDigits 10 (List.replicate m P).flatten ≡ m * Nat.ofDigits 10 P [MOD d] := by
  induction m with
  | zero => simp; rfl
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append]
    obtain ⟨q, hq⟩ := hP
    have h1 : 10 ^ P.length ≡ 1 [MOD d] := by
      rw [hq, pow_mul]; simpa using ht.pow q
    calc Nat.ofDigits 10 P + 10 ^ P.length * Nat.ofDigits 10 (List.replicate m P).flatten
        ≡ Nat.ofDigits 10 P + 1 * (m * Nat.ofDigits 10 P) [MOD d] :=
          Nat.ModEq.add_left _ (Nat.ModEq.mul h1 ih)
      _ = (m + 1) * Nat.ofDigits 10 P := by ring

lemma flatten_replicate_length (P : List ℕ) (m : ℕ) :
    (List.replicate m P).flatten.length = m * P.length := by
  rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]

lemma flatten_replicate_sum (P : List ℕ) (m : ℕ) :
    (List.replicate m P).flatten.sum = m * P.sum := by
  rw [List.sum_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem harshad_partner_exists (n : ℕ) (hn : 0 < n) :
    ∃ k, 0 < k ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n := by
  set d := (digits 10 n).sum with hd
  have hdn : d ≤ n := Nat.digit_sum_le 10 n
  have hmod : n ≡ d [MOD 9] := Nat.modEq_nine_digits_sum n
  have hd0 : d ≠ 0 := by
    intro h
    have hall : ∀ x ∈ digits 10 n, x = 0 := List.sum_eq_zero_iff.mp h
    have : digits 10 n = List.replicate (digits 10 n).length 0 :=
      List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    have h2 := Nat.ofDigits_digits 10 n
    rw [this, Nat.ofDigits_replicate_zero] at h2
    omega
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  obtain ⟨a, m, hm2, hdm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 2 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hdm; exact hd0 hdm
  obtain ⟨b, d', hd5, hmd'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 5 (by norm_num)
  have hd2 : ¬ 2 ∣ d' := fun h => hm2 (hmd' ▸ Dvd.dvd.mul_left h _)
  have hcop : Nat.Coprime d' 10 := by
    have h2 : Nat.Coprime 2 d' := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hd2
    have h5 : Nat.Coprime 5 d' := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hd5
    exact (Nat.Coprime.mul_left h2 h5).symm
  have hd'0 : 0 < d' := Nat.pos_of_ne_zero (by rintro rfl; exact hd5 (dvd_zero 5))
  have hd'd : d' ≤ d := Nat.le_of_dvd hdpos (by rw [hdm, hmd']; exact Dvd.intro_left (2 ^ a * 5 ^ b) (by ring))
  set t := Nat.totient d' with ht
  have ht0 : 0 < t := Nat.totient_pos.mpr hd'0
  have ht1 : 10 ^ t ≡ 1 [MOD d'] := Nat.ModEq.pow_totient hcop.symm
  -- gcd(9, d') ∣ n
  have hgd : Nat.gcd 9 d' ∣ d := by
    rw [hdm, hmd']; exact (Nat.gcd_dvd_right 9 d').trans (Dvd.intro_left (2 ^ a * 5 ^ b) (by ring))
  have hgn : Nat.gcd 9 d' ∣ n := by
    have h1 := Nat.ModEq.of_dvd (Nat.gcd_dvd_left 9 d') hmod
    exact (Nat.modEq_zero_iff_dvd).mp (h1.trans ((Nat.modEq_zero_iff_dvd).mpr hgd))
  -- find j with d' ∣ n + 9 j
  obtain ⟨j, hjd', hj⟩ : ∃ j : ℕ, j < d' ∧ d' ∣ n + 9 * j := by
    obtain ⟨q, hq⟩ := hgn
    have hB := Nat.gcd_eq_gcd_ab 9 d'
    set A := Nat.gcdA 9 d' with hA
    set B := Nat.gcdB 9 d' with hBdef
    set X : ℤ := -(A * q) with hX
    have hd'z : (d' : ℤ) ≠ 0 := by exact_mod_cast hd'0.ne'
    have hJ0 : 0 ≤ X % (d' : ℤ) := Int.emod_nonneg _ hd'z
    have hJlt : X % (d' : ℤ) < d' := Int.emod_lt_of_pos _ (by exact_mod_cast hd'0)
    refine ⟨(X % (d' : ℤ)).toNat, ?_, ?_⟩
    · have : ((X % (d' : ℤ)).toNat : ℤ) < d' := by rw [Int.toNat_of_nonneg hJ0]; exact hJlt
      exact_mod_cast this
    · have hj : ((X % (d' : ℤ)).toNat : ℤ) = X - d' * (X / d') := by
        rw [Int.toNat_of_nonneg hJ0, Int.emod_def]
      have hn' : (n : ℤ) = (Nat.gcd 9 d' : ℤ) * q := by exact_mod_cast hq
      have : ((n + 9 * (X % (d' : ℤ)).toNat : ℕ) : ℤ) = d' * (B * q - 9 * (X / d')) := by
        push_cast
        rw [hj, hn', hB, hX]; ring
      exact Int.natCast_dvd_natCast.mp (this ▸ Dvd.intro _ rfl)
  have hjn : j ≤ n := by omega
  -- blocks
  set P1 : List ℕ := 1 :: List.replicate (t - 1) 0 with hP1
  set P10 : List ℕ := 0 :: 1 :: List.replicate (2 * t - 2) 0 with hP10
  have hP1len : P1.length = t := by simp [hP1]; omega
  have hP10len : P10.length = 2 * t := by simp [hP10]; omega
  have hP1val : Nat.ofDigits 10 P1 = 1 := by simp [hP1, Nat.ofDigits_cons]
  have hP10val : Nat.ofDigits 10 P10 = 10 := by simp [hP10, Nat.ofDigits_cons]
  have hP1sum : P1.sum = 1 := by simp [hP1]
  have hP10sum : P10.sum = 1 := by simp [hP10]
  set R : List ℕ := (List.replicate (n - j) P1).flatten ++ (List.replicate j P10).flatten with hR
  set L : List ℕ := List.replicate n 0 ++ R with hL
  set k := Nat.ofDigits 10 L with hk
  have hLlt : ∀ x ∈ L, x < 10 := by
    intro x hx
    simp only [hL, hR, hP1, hP10, List.mem_append, List.mem_flatten, List.mem_replicate] at hx
    rcases hx with ⟨-, rfl⟩ | ⟨l, ⟨-, rfl⟩, h⟩ | ⟨l, ⟨-, rfl⟩, h⟩
    · omega
    · simp only [List.mem_cons, List.mem_replicate] at h; omega
    · simp only [List.mem_cons, List.mem_replicate] at h; omega
  have hRsum : R.sum = n := by
    rw [hR, List.sum_append, flatten_replicate_sum, flatten_replicate_sum, hP1sum, hP10sum]
    omega
  have hksum : (digits 10 k).sum = n := by
    rw [hk, dsum_ofDigits_aux L hLlt, hL, List.sum_append, List.sum_replicate, hRsum]; simp
  have hkR : k = 10 ^ n * Nat.ofDigits 10 R := by
    rw [hk, hL, Nat.ofDigits_append, Nat.ofDigits_replicate_zero, List.length_replicate, zero_add]
  have hRmod : Nat.ofDigits 10 R ≡ 0 [MOD d'] := by
    rw [hR, Nat.ofDigits_append, flatten_replicate_length, hP1len]
    have h1 := ofDigits_flatten_replicate_modEq d' t ht1 P1 (by rw [hP1len]) (n - j)
    have h2 := ofDigits_flatten_replicate_modEq d' t ht1 P10 (by rw [hP10len]; exact Dvd.intro_left _ rfl) j
    have h3 : 10 ^ ((n - j) * t) ≡ 1 [MOD d'] := by
      rw [mul_comm, pow_mul]; simpa using ht1.pow (n - j)
    rw [hP1val] at h1
    rw [hP10val] at h2
    calc Nat.ofDigits 10 (List.replicate (n - j) P1).flatten
          + 10 ^ ((n - j) * t) * Nat.ofDigits 10 (List.replicate j P10).flatten
        ≡ (n - j) * 1 + 1 * (j * 10) [MOD d'] := Nat.ModEq.add h1 (Nat.ModEq.mul h3 h2)
      _ = n + 9 * j := by
          have : (n - j) * 1 + 1 * (j * 10) = n + 9 * j := by omega
          exact this
      _ ≡ 0 [MOD d'] := (Nat.modEq_zero_iff_dvd).mpr hj
  have hd'R : d' ∣ Nat.ofDigits 10 R := (Nat.modEq_zero_iff_dvd).mp hRmod
  have h2a : 2 ^ a ∣ 10 ^ n := by
    have ha : a ≤ n := by
      have h1 : a < 2 ^ a := Nat.lt_pow_self (by norm_num)
      have h2 : 2 ^ a ≤ d := Nat.le_of_dvd hdpos (Dvd.intro _ hdm.symm)
      omega
    exact (pow_dvd_pow 2 ha).trans (pow_dvd_pow_of_dvd (by norm_num) n)
  have h5b : 5 ^ b ∣ 10 ^ n := by
    have hb : b ≤ n := by
      have h1 : b < 5 ^ b := Nat.lt_pow_self (by norm_num)
      have h2 : 5 ^ b ≤ d := Nat.le_of_dvd hdpos (by rw [hdm, hmd']; exact Dvd.intro_left (2 ^ a * d') (by ring))
      omega
    exact (pow_dvd_pow 5 hb).trans (pow_dvd_pow_of_dvd (by norm_num) n)
  have h25 : 2 ^ a * 5 ^ b ∣ 10 ^ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num)) h2a h5b
  have hdk : d ∣ k := by
    rw [hkR, hdm, hmd', ← mul_assoc]
    exact Nat.mul_dvd_mul h25 hd'R
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hksum; simp at hksum; omega
    · exact h
  have hkn : k ≠ n := by
    have hR0 : 0 < Nat.ofDigits 10 R := by
      rcases Nat.eq_zero_or_pos (Nat.ofDigits 10 R) with h | h
      · rw [hkR, h, mul_zero] at hk0; exact absurd hk0 (lt_irrefl 0)
      · exact h
    have : 10 ^ n ≤ k := by rw [hkR]; exact Nat.le_mul_of_pos_right _ hR0
    have : n < 10 ^ n := Nat.lt_pow_self (by norm_num)
    omega
  exact ⟨k, hk0, hkn, hdk, hksum ▸ dvd_refl n⟩

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  obtain ⟨k, hk0, hkn, h1, h2⟩ := harshad_partner_exists n hn
  have hne : ({k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} : Set ℕ).Nonempty :=
    ⟨k, hk0, hkn, h1, h2⟩
  unfold a
  simp only []
  rw [dif_pos hne]
  exact (Nat.sInf_mem hne).1.ne'

theorem oeis_272479_conjecture_0.disproof : ¬ (type_of% @oeis_272479_conjecture_0) := sorry
