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

-- Lemma A: digit sum of ofDigits equals list sum when entries < 10
theorem digitSum_ofDigits (L : List ℕ) (hL : ∀ x ∈ L, x < 10) :
    (Nat.digits 10 (Nat.ofDigits 10 L)).sum = L.sum := by
  induction L with
  | nil => simp
  | cons a t IH =>
    have ha : a < 10 := hL a (by simp)
    have ht : ∀ x ∈ t, x < 10 := fun x hx => hL x (by simp [hx])
    rw [Nat.ofDigits_cons]
    by_cases h0 : a + 10 * Nat.ofDigits 10 t = 0
    · rw [h0]
      have ha0 : a = 0 := by omega
      have hX0 : Nat.ofDigits 10 t = 0 := by omega
      have hle : t.sum ≤ Nat.ofDigits 10 t := Nat.sum_le_ofDigits t (by norm_num)
      simp only [Nat.digits_zero, List.sum_nil, List.sum_cons]
      omega
    · have hxy : a ≠ 0 ∨ Nat.ofDigits 10 t ≠ 0 := by
        by_contra hc
        push_neg at hc
        obtain ⟨h1, h2⟩ := hc
        apply h0
        rw [h1, h2]
      have hsplit := Nat.digits_add 10 (by norm_num) a (Nat.ofDigits 10 t) ha hxy
      rw [hsplit, List.sum_cons, IH ht, List.sum_cons]

-- block residue lemma
theorem ofDigits_flatten_modEq (m W : ℕ) (hW : (10:ℕ)^W ≡ 1 [MOD m])
    (bs : List (List ℕ)) (hbs : ∀ b ∈ bs, b.length = W) :
    Nat.ofDigits 10 bs.flatten ≡ (bs.map (fun b => Nat.ofDigits 10 b)).sum [MOD m] := by
  induction bs with
  | nil =>
      simp only [List.flatten_nil, Nat.ofDigits_nil, List.map_nil, List.sum_nil]
      rfl
  | cons b rest IH =>
    have hb : b.length = W := hbs b (by simp)
    have hrest : ∀ x ∈ rest, x.length = W := fun x hx => hbs x (by simp [hx])
    rw [List.flatten_cons, Nat.ofDigits_append, hb, List.map_cons, List.sum_cons]
    have h1 : (10:ℕ)^W * Nat.ofDigits 10 rest.flatten ≡ Nat.ofDigits 10 rest.flatten [MOD m] := by
      calc (10:ℕ)^W * Nat.ofDigits 10 rest.flatten
          ≡ 1 * Nat.ofDigits 10 rest.flatten [MOD m] := hW.mul_right _
        _ = Nat.ofDigits 10 rest.flatten := by ring
    have h2 := IH hrest
    exact (Nat.ModEq.add_left _ h1).trans (Nat.ModEq.add_left _ h2)

-- coprime part existence
theorem exists_coprime_part (d : ℕ) (hd : 0 < d) :
    ∃ d' P : ℕ, 0 < d' ∧ Nat.Coprime 10 d' ∧ d' ∣ d ∧ d ∣ 10 ^ P * d' := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    by_cases h2 : 2 ∣ d
    · obtain ⟨c, rfl⟩ := h2
      have hc : 0 < c := by omega
      have hlt : c < 2 * c := by omega
      obtain ⟨d', P, hd'pos, hcop, hdvd, hdvd2⟩ := IH c hlt hc
      refine ⟨d', P + 1, hd'pos, hcop, hdvd.mul_left 2, ?_⟩
      calc 2 * c ∣ 2 * (10 ^ P * d') := Nat.mul_dvd_mul_left 2 hdvd2
        _ = (2 * 10 ^ P) * d' := by ring
        _ ∣ (10 * 10 ^ P) * d' := by
              apply Nat.mul_dvd_mul_right
              exact Nat.mul_dvd_mul_right (by norm_num) _
        _ = 10 ^ (P + 1) * d' := by ring
    · by_cases h5 : 5 ∣ d
      · obtain ⟨c, rfl⟩ := h5
        have hc : 0 < c := by omega
        have hlt : c < 5 * c := by omega
        obtain ⟨d', P, hd'pos, hcop, hdvd, hdvd2⟩ := IH c hlt hc
        refine ⟨d', P + 1, hd'pos, hcop, hdvd.mul_left 5, ?_⟩
        calc 5 * c ∣ 5 * (10 ^ P * d') := Nat.mul_dvd_mul_left 5 hdvd2
          _ = (5 * 10 ^ P) * d' := by ring
          _ ∣ (10 * 10 ^ P) * d' := by
                apply Nat.mul_dvd_mul_right
                exact Nat.mul_dvd_mul_right (by norm_num) _
          _ = 10 ^ (P + 1) * d' := by ring
      · refine ⟨d, 0, hd, ?_, dvd_refl _, by simp⟩
        have c2 : Nat.Coprime 2 d := (Nat.prime_two.coprime_iff_not_dvd).mpr h2
        have c5 : Nat.Coprime 5 d := ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr h5
        have : Nat.Coprime (2 * 5) d := Nat.Coprime.mul_left c2 c5
        simpa using this

-- linear congruence solver: 9 a ≡ 10 n  mod d'
theorem exists_a_solution (d' n : ℕ) (hd' : 0 < d') (hg : Nat.gcd 9 d' ∣ n) :
    ∃ a : ℕ, a < d' ∧ 9 * a ≡ 10 * n [MOD d'] := by
  obtain ⟨t, ht⟩ := hg
  have bez : ((Nat.gcd 9 d' : ℕ) : ℤ) = 9 * Nat.gcdA 9 d' + d' * Nat.gcdB 9 d' :=
    Nat.gcd_eq_gcd_ab 9 d'
  set A := Nat.gcdA 9 d' with hA
  set B := Nat.gcdB 9 d' with hB
  set a0 : ℤ := A * 10 * t with ha0
  set q : ℤ := a0 / d' with hq
  set a : ℕ := (a0 % d').toNat with hadef
  have hd'z : (0:ℤ) < d' := by exact_mod_cast hd'
  have hmod_nonneg : 0 ≤ a0 % (d':ℤ) := Int.emod_nonneg _ (by exact_mod_cast hd'.ne')
  have hmod_lt : a0 % (d':ℤ) < d' := Int.emod_lt_of_pos _ hd'z
  have hacast : (a : ℤ) = a0 % d' := Int.toNat_of_nonneg hmod_nonneg
  have haq : (a : ℤ) = a0 - d' * q := by rw [hacast, hq, Int.emod_def]
  have hn : (n : ℤ) = (Nat.gcd 9 d') * t := by rw [ht]; push_cast; ring
  refine ⟨a, ?_, ?_⟩
  · have : (a:ℤ) < (d':ℤ) := by rw [hacast]; exact hmod_lt
    exact_mod_cast this
  · rw [Nat.modEq_iff_dvd]
    push_cast
    refine ⟨10 * B * t + 9 * q, ?_⟩
    have key : (10 : ℤ) * n - 9 * a = d' * (10 * B * t + 9 * q) := by
      rw [haq, hn, ha0]
      linear_combination (10 * t) * bez
    linarith [key]

theorem exists_partner (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n := by
  set d := (Nat.digits 10 n).sum with hd
  -- d > 0
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso
      have hnz : n ≠ 0 := by omega
      have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hnz
      have hlast := Nat.getLast_digit_ne_zero 10 hnz
      have hmem : (Nat.digits 10 n).getLast hne ∈ Nat.digits 10 n := List.getLast_mem hne
      have hall : ∀ x ∈ Nat.digits 10 n, x = 0 := by
        have : (Nat.digits 10 n).sum = 0 := by rw [← hd]; omega
        exact (List.sum_eq_zero_iff).mp this
      exact hlast (hall _ hmem)
    · exact h
  -- d ≤ n
  have hdle : d ≤ n := by rw [hd]; exact Nat.digit_sum_le 10 n
  -- coprime decomposition
  obtain ⟨d', P, hd'pos, hcop, hdvd, hdvd2⟩ := exists_coprime_part d hdpos
  have hd'led : d' ≤ d := Nat.le_of_dvd hdpos hdvd
  have hd'len : d' ≤ n := le_trans hd'led hdle
  -- gcd 9 d' ∣ n
  have hg : Nat.gcd 9 d' ∣ n := by
    have h9 : n ≡ d [MOD 9] := Nat.modEq_nine_digits_sum n
    have hgd9 : Nat.gcd 9 d' ∣ 9 := Nat.gcd_dvd_left 9 d'
    have hgdd : Nat.gcd 9 d' ∣ d := (Nat.gcd_dvd_right 9 d').trans hdvd
    have hng : n ≡ d [MOD Nat.gcd 9 d'] := h9.of_dvd hgd9
    have hdg : d ≡ 0 [MOD Nat.gcd 9 d'] := (Nat.modEq_zero_iff_dvd).mpr hgdd
    exact (Nat.modEq_zero_iff_dvd).mp (hng.trans hdg)
  -- a
  obtain ⟨a, ha_lt, ha_cong⟩ := exists_a_solution d' n hd'pos hg
  have han : a ≤ n := le_trans (le_of_lt ha_lt) hd'len
  -- W
  set W := 2 * Nat.totient d' with hW_def
  have htotpos : 0 < Nat.totient d' := Nat.totient_pos.mpr hd'pos
  have hW2 : 2 ≤ W := by rw [hW_def]; omega
  have hW : (10:ℕ) ^ W ≡ 1 [MOD d'] := by
    have h2 := (Nat.ModEq.pow_totient hcop).pow 2
    simp only [one_pow] at h2
    rw [← pow_mul] at h2
    rwa [show W = Nat.totient d' * 2 from by rw [hW_def]; ring]
  -- blocks
  set blockA : List ℕ := 1 :: List.replicate (W - 1) 0 with hbA
  set blockB : List ℕ := 0 :: 1 :: List.replicate (W - 2) 0 with hbB
  have hlenA : blockA.length = W := by
    rw [hbA]; simp [List.length_replicate]; omega
  have hlenB : blockB.length = W := by
    rw [hbB]; simp [List.length_replicate]; omega
  have hofA : Nat.ofDigits 10 blockA = 1 := by
    rw [hbA, Nat.ofDigits_cons, Nat.ofDigits_replicate_zero]
  have hofB : Nat.ofDigits 10 blockB = 10 := by
    rw [hbB, Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_replicate_zero]
  have hsumA : blockA.sum = 1 := by
    rw [hbA]; simp
  have hsumB : blockB.sum = 1 := by
    rw [hbB]; simp
  have hltA : ∀ x ∈ blockA, x < 10 := by
    rw [hbA]; intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with h | h
    · omega
    · have := List.eq_of_mem_replicate h; omega
  have hltB : ∀ x ∈ blockB, x < 10 := by
    rw [hbB]; intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with h | h | h
    · omega
    · omega
    · have := List.eq_of_mem_replicate h; omega
  set BLOCKS : List (List ℕ) := List.replicate a blockA ++ List.replicate (n - a) blockB with hBL
  set L : List ℕ := BLOCKS.flatten with hL
  set V : ℕ := Nat.ofDigits 10 L with hV
  -- length condition for blocks
  have hbs : ∀ b ∈ BLOCKS, b.length = W := by
    rw [hBL]; intro b hb
    rcases List.mem_append.mp hb with h | h
    · rw [List.eq_of_mem_replicate h]; exact hlenA
    · rw [List.eq_of_mem_replicate h]; exact hlenB
  -- entries < 10
  have hL10 : ∀ x ∈ L, x < 10 := by
    rw [hL]; intro x hx
    rw [List.mem_flatten] at hx
    obtain ⟨b, hbB', hxb⟩ := hx
    rw [hBL] at hbB'
    rcases List.mem_append.mp hbB' with h | h
    · rw [List.eq_of_mem_replicate h] at hxb; exact hltA x hxb
    · rw [List.eq_of_mem_replicate h] at hxb; exact hltB x hxb
  -- L.sum = n
  have hLsum : L.sum = n := by
    rw [hL, List.sum_flatten, hBL, List.map_append, List.map_replicate, List.map_replicate,
        List.sum_append, List.sum_replicate, List.sum_replicate, hsumA, hsumB]
    simp only [smul_eq_mul, mul_one]
    omega
  -- V positive
  have hVpos : 0 < V := by
    rw [hV]
    have : L.sum ≤ Nat.ofDigits 10 L := Nat.sum_le_ofDigits L (by norm_num)
    omega
  -- digit sum of V = n
  have hdigV : (Nat.digits 10 V).sum = n := by
    rw [hV, digitSum_ofDigits L hL10, hLsum]
  -- d' ∣ V
  have hmapsum : (BLOCKS.map (fun b => Nat.ofDigits 10 b)).sum = a + 10 * (n - a) := by
    rw [hBL, List.map_append, List.map_replicate, List.map_replicate,
        List.sum_append, List.sum_replicate, List.sum_replicate, hofA, hofB]
    simp only [smul_eq_mul, mul_one]
    ring
  have hVcong : V ≡ a + 10 * (n - a) [MOD d'] := by
    rw [hV, hL]
    have := ofDigits_flatten_modEq d' W hW BLOCKS hbs
    rwa [hmapsum] at this
  have hdvdRS : d' ∣ (a + 10 * (n - a)) := by
    have heq : a + 10 * (n - a) = 10 * n - 9 * a := by omega
    rw [heq]
    have hle : 9 * a ≤ 10 * n := by omega
    exact (Nat.modEq_iff_dvd' hle).mp ha_cong
  have hd'V : d' ∣ V := by
    have hRS0 : (a + 10 * (n - a)) ≡ 0 [MOD d'] := (Nat.modEq_zero_iff_dvd).mpr hdvdRS
    exact (Nat.modEq_zero_iff_dvd).mp (hVcong.trans hRS0)
  -- final k
  set Q := P + n + 1 with hQ
  refine ⟨10 ^ Q * V, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (pow_pos (by norm_num) Q) hVpos
  · -- k ≠ n
    have hnlt : n < 10 ^ Q := by
      have h1 : n < 2 ^ n := Nat.lt_two_pow_self
      have h2 : (2:ℕ) ^ n ≤ 2 ^ Q := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : (2:ℕ) ^ Q ≤ 10 ^ Q := Nat.pow_le_pow_left (by norm_num) Q
      omega
    have hkge : 10 ^ Q ≤ 10 ^ Q * V := Nat.le_mul_of_pos_right _ hVpos
    omega
  · -- d ∣ k
    have h1 : d ∣ 10 ^ P * V :=
      hdvd2.trans (mul_dvd_mul_left (10 ^ P) hd'V)
    have hPV : 10 ^ P * V ∣ 10 ^ Q * V :=
      mul_dvd_mul_right (pow_dvd_pow 10 (by omega : P ≤ Q)) V
    exact h1.trans hPV
  · -- digit sum k ∣ n
    have hk : (Nat.digits 10 (10 ^ Q * V)).sum = n := by
      rw [Nat.digits_base_pow_mul (by norm_num) hVpos]
      simp [hdigV]
    rw [hk]

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  obtain ⟨k, hkpos, hkne, hdk, hkd⟩ := exists_partner n hn
  have hne : ({k | k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n} : Set ℕ).Nonempty :=
    ⟨k, hkpos, hkne, hdk, hkd⟩
  have heq : a n = sInf {k | k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n} := by
    rw [a]
    exact dif_pos hne
  rw [heq]
  intro hcontra
  have hmem := Nat.sInf_mem hne
  rw [hcontra] at hmem
  exact absurd hmem.1 (lt_irrefl 0)
