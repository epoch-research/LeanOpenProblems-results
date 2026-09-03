import Submission.Work

/-! Obstructions to substring-upward inductive invariants.
These are not a proof or disproof of Erdős 406. -/

namespace Erdos406Work

lemma fract_interval_arbitrarily_late {α a b : ℝ} (hα : Irrational α)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ a < Int.fract (n * α) ∧ Int.fract (n * α) < b := by
  let x : AddCircle (1 : ℝ) := α
  have hdZ : DenseRange (fun n : ℤ => n • x) := by
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa using hα
  have hdN : DenseRange (fun n : ℕ => n • x) := denseRange_zsmul_iff_nsmul.mp hdZ
  let H := Homeomorph.addRight (M • x)
  have hd : DenseRange (fun n : ℕ => n • x + M • x) :=
    H.surjective.denseRange.comp hdN H.continuous
  let U := ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ioo a b
  have ho : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hne : U.Nonempty := Set.Nonempty.image _ (Set.nonempty_Ioo.mpr hab)
  obtain ⟨n, y, hy, heq⟩ := hd.exists_mem_open ho hne
  have he : Int.fract ((n + M : ℕ) * α) = y := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (a := (0 : ℝ)) (p := (1 : ℝ))
      ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one ((n + M : ℕ) * α)⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩).mp
    rw [AddCircle.coe_fract]
    simp only [← nsmul_eq_mul, add_nsmul]
    exact heq.symm
  exact ⟨n + M, by omega, by rw [he]; exact hy⟩

/-- Scaling the reciprocal of a power of `4^s` by a power of three can give
any prescribed positive integer part. -/
lemma reciprocal_four_power_prefix (A s : ℕ) (hA : 0 < A) (hs : 0 < s) :
    ∃ t E : ℕ, 0 < t ∧ A * 4 ^ (s * t) < 3 ^ E ∧
      3 ^ E < (A + 1) * 4 ^ (s * t) := by
  let D := (Nat.digits 3 A).length
  let α : ℝ := (2 * s : ℕ) * (Real.log 2 / Real.log 3)
  let a : ℝ := ((D : ℝ) * Real.log 3 - Real.log (A + 1)) / Real.log 3
  let b : ℝ := ((D : ℝ) * Real.log 3 - Real.log A) / Real.log 3
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hi : Irrational α := irrational_log_two_div_log_three.natCast_mul (by omega)
  have hlowNat : A + 1 ≤ 3 ^ D := by
    exact Nat.succ_le_of_lt (Nat.lt_base_pow_length_digits (b := 3) (m := A) (by decide))
  have hhighNat : 3 ^ D ≤ 3 * A :=
    Nat.base_pow_length_digits_le 3 A (by decide) (ne_of_gt hA)
  have hlow : Real.log (A + 1) ≤ (D : ℝ) * Real.log 3 := by
    have hh : (A : ℝ) + 1 ≤ (3 : ℝ) ^ D := by exact_mod_cast hlowNat
    have hl := Real.log_le_log (by positivity : 0 < (A : ℝ) + 1) hh
    simpa only [Real.log_pow] using hl
  have hhigh : (D : ℝ) * Real.log 3 ≤ Real.log 3 + Real.log A := by
    have hh : (3 : ℝ) ^ D ≤ 3 * (A : ℝ) := by exact_mod_cast hhighNat
    have hl := Real.log_le_log (by positivity : 0 < (3 : ℝ) ^ D) hh
    simpa only [Real.log_pow, Real.log_mul (by positivity : (3 : ℝ) ≠ 0) (ne_of_gt hAr)] using hl
  have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg (sub_nonneg.mpr hlow) (le_of_lt h3)
  have hab : a < b := by
    dsimp [a, b]
    apply (div_lt_div_iff_of_pos_right h3).mpr
    have hh := Real.log_lt_log hAr (show (A : ℝ) < A + 1 by linarith)
    linarith
  have hb : b ≤ 1 := by
    dsimp [b]
    rw [div_le_iff₀ h3]
    linarith
  obtain ⟨t, ht, hta, htb⟩ := fract_interval_arbitrarily_late hi ha hab hb 1
  have htnonneg : 0 ≤ (t : ℝ) * α := by positivity
  let F := Nat.floor ((t : ℝ) * α)
  have hfract : Int.fract ((t : ℝ) * α) = t * α - F := by
    rw [Int.fract]
    have hh := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_floor_eq_floor htnonneg)
    simpa only [Int.cast_natCast] using congrArg (fun y : ℝ => t * α - y) hh.symm
  rw [hfract] at hta htb
  have hta' := mul_lt_mul_of_pos_right hta h3
  have htb' := mul_lt_mul_of_pos_right htb h3
  dsimp [a] at hta'
  dsimp [b] at htb'
  rw [div_mul_cancel₀ _ (ne_of_gt h3)] at hta' htb'
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog : Real.log ((4 : ℝ) ^ (s * t)) = (t * α) * Real.log 3 := by
    rw [Real.log_pow, hlog4]
    dsimp [α]
    push_cast
    field_simp
  have he : ((D + F : ℕ) : ℝ) * Real.log 3 = (D : ℝ) * Real.log 3 + (F : ℝ) * Real.log 3 := by
    push_cast
    ring
  have hloR : (A : ℝ) * (4 : ℝ) ^ (s * t) < (3 : ℝ) ^ (D + F) := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (ne_of_gt hAr) (by positivity), hlog, Real.log_pow, he]
    nlinarith
  have hhiR : (3 : ℝ) ^ (D + F) < ((A : ℝ) + 1) * (4 : ℝ) ^ (s * t) := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity : (A : ℝ) + 1 ≠ 0) (by positivity),
      hlog, Real.log_pow, he]
    nlinarith
  exact ⟨t, D + F, by omega, by exact_mod_cast hloR, by exact_mod_cast hhiR⟩

/-- Every positive prescribed leading ternary block occurs in arbitrarily large
multiples of `4^K` that become good after multiplication by a power of `4^s`.
The constructed numbers have a factor eleven, so are not counterexamples. -/
lemma arbitrary_prefix_can_disappear (A s K M : ℕ) (hA : 0 < A) (hs : 0 < s) :
    ∃ t n L : ℕ, 0 < t ∧ M < n ∧ 4 ^ K ∣ n ∧ n / 3 ^ L = A ∧
      Nat.digits 3 (4 ^ (s * t) * n) ⊆ [0, 1] ∧ 11 ∣ n := by
  obtain ⟨t, E, ht, hlo, hhi⟩ := reciprocal_four_power_prefix A s hA hs
  obtain ⟨c, hcE, hc, hc5, hdiv⟩ :=
    four_digit_divisibility_large (2 * (s * t + K)) (E + M + 3)
  rw [pow_mul] at hdiv
  change 4 ^ (s * t + K) ∣ 3 ^ c + 13 at hdiv
  obtain ⟨u, hu⟩ := hdiv
  let n := 4 ^ K * u
  have hn : 4 ^ (s * t) * n = 3 ^ c + 13 := by
    rw [hu, pow_add]
    dsimp [n]
    ring
  let L := c - E
  have hL : M + 3 ≤ L := by dsimp [L]; omega
  have hpow : 3 ^ c = 3 ^ E * 3 ^ L := by
    rw [← pow_add]
    congr 1
    dsimp [L]
    omega
  have hS : 13 < 3 ^ L := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 3 ≤ L)
    norm_num at hh
    omega
  have hQ : 0 < 4 ^ (s * t) := by positivity
  have hnlo : A * 3 ^ L ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := 4 ^ (s * t)) _ hQ
    calc
      4 ^ (s * t) * (A * 3 ^ L) = (A * 4 ^ (s * t)) * 3 ^ L := by ring
      _ ≤ 3 ^ E * 3 ^ L := Nat.mul_le_mul_right _ (le_of_lt hlo)
      _ ≤ 4 ^ (s * t) * n := by rw [hn, ← hpow]; omega
  have hnhi : n < (A + 1) * 3 ^ L := by
    apply Nat.lt_of_mul_lt_mul_left (a := 4 ^ (s * t))
    have hh := Nat.mul_le_mul_right (3 ^ L) (Nat.succ_le_of_lt hhi)
    calc
      4 ^ (s * t) * n = 3 ^ E * 3 ^ L + 13 := by rw [hn, hpow]
      _ < (3 ^ E + 1) * 3 ^ L := by nlinarith
      _ ≤ ((A + 1) * 4 ^ (s * t)) * 3 ^ L := hh
      _ = 4 ^ (s * t) * ((A + 1) * 3 ^ L) := by ring
  have hnM : M < n := by
    have hh : L < 3 ^ L := Nat.lt_pow_self (by decide)
    have hAn : 3 ^ L ≤ A * 3 ^ L := Nat.le_mul_of_pos_left _ hA
    omega
  refine ⟨t, n, L, ht, hnM, ⟨u, rfl⟩, Nat.div_eq_of_lt_le hnlo hnhi, ?_, ?_⟩
  · rw [hn, four_digit_formula (by omega : 3 ≤ c)]
    intro d hd
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_replicate] at hd ⊢
    aesop
  · have h11 : 11 ∣ 3 ^ c + 13 := by
      apply Nat.dvd_of_mod_eq_zero
      have he : c = 5 * (c / 5) + 2 := by omega
      rw [he, pow_add, pow_mul]
      norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
    rw [← hn] at h11
    rcases (by decide : Nat.Prime 11).dvd_mul.mp h11 with hbad | hgood
    · have hh := (by decide : Nat.Prime 11).dvd_of_dvd_pow hbad
      norm_num at hh
    · exact hgood

lemma digits_div_three (n : ℕ) : Nat.digits 3 (n / 3) = (Nat.digits 3 n).tail := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) (by omega : 0 < n)]
    rfl

lemma digits_div_three_pow (n L : ℕ) :
    Nat.digits 3 (n / 3 ^ L) = (Nat.digits 3 n).drop L := by
  induction L generalizing n with
  | zero => simp
  | succ L ih =>
    rw [pow_succ', ← Nat.div_div_eq_div_mul, ih, digits_div_three]
    rw [← List.drop_one, List.drop_drop]
    congr 1
    omega

/-- An arbitrary finite ternary word can disappear after multiplication by a
power of `4^s`, even with an arbitrarily strong fixed divisibility guard. -/
lemma arbitrary_block_can_disappear (w : List ℕ) (hw : ∀ d ∈ w, d < 3)
    (s K M : ℕ) (hs : 0 < s) :
    ∃ t n : ℕ, 0 < t ∧ M < n ∧ 4 ^ K ∣ n ∧ w <:+: Nat.digits 3 n ∧
      Nat.digits 3 (4 ^ (s * t) * n) ⊆ [0, 1] ∧ 11 ∣ n := by
  let A := Nat.ofDigits 3 (w ++ [1])
  have hA : 0 < A := by
    dsimp [A]
    rw [Nat.ofDigits_append]
    simp only [Nat.ofDigits_singleton, mul_one]
    positivity
  have hdA : Nat.digits 3 A = w ++ [1] := by
    apply Nat.digits_ofDigits 3 (by decide)
    · intro d hd
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with hd | rfl
      · exact hw d hd
      · decide
    · intro h
      simp
  obtain ⟨t, n, L, ht, hnM, hnK, hnA, hgood, h11⟩ :=
    arbitrary_prefix_can_disappear A s K M hA hs
  have hdrop : (Nat.digits 3 n).drop L = w ++ [1] := by
    have hh := congrArg (Nat.digits 3) hnA
    rwa [digits_div_three_pow, hdA] at hh
  refine ⟨t, n, ht, hnM, hnK, ?_, hgood, h11⟩
  refine ⟨(Nat.digits 3 n).take L, [1], ?_⟩
  rw [List.append_assoc, ← hdrop, List.take_append_drop]

/-- No nonempty substring-upward predicate on multiples of `4^K` can both be
preserved by multiplication by `4^s` and exclude every good positive integer.
This rules out this specific family of pattern certificates, not arbitrary
regular or finite-state invariants. -/
lemma no_substring_upward_invariant (P : ℕ → Prop) (s K : ℕ) (hs : 0 < s)
    (hup : ∀ n m : ℕ, 0 < n → 0 < m → 4 ^ K ∣ n → 4 ^ K ∣ m →
      Nat.digits 3 n <:+: Nat.digits 3 m → P n → P m)
    (hmul : ∀ n : ℕ, 0 < n → 4 ^ K ∣ n → P n → P (4 ^ s * n))
    (hsafe : ∀ n : ℕ, 0 < n → 4 ^ K ∣ n → Nat.digits 3 n ⊆ [0, 1] → ¬ P n) :
    ∀ n : ℕ, 0 < n → 4 ^ K ∣ n → ¬ P n := by
  intro n hn hnK hPn
  obtain ⟨t, m, ht, hm, hmK, hword, hgood, _⟩ :=
    arbitrary_block_can_disappear (Nat.digits 3 n)
      (fun d hd => Nat.digits_lt_base (by decide) hd) s K 0 hs
  have hPm : P m := hup n m hn hm hnK hmK hword hPn
  have hiter : ∀ j : ℕ, P (4 ^ (s * j) * m) := by
    intro j
    induction j with
    | zero => simpa using hPm
    | succ j ih =>
      have hd : 4 ^ K ∣ 4 ^ (s * j) * m := dvd_mul_of_dvd_right hmK _
      have hh := hmul (4 ^ (s * j) * m) (by positivity) hd ih
      simpa only [Nat.mul_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  exact hsafe _ (by positivity) (dvd_mul_of_dvd_right hmK _) hgood (hiter t)

lemma fract_affine_interval_arbitrarily_late {α a b : ℝ} (hα : Irrational α)
    (β : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ a < Int.fract (n * α + β) ∧ Int.fract (n * α + β) < b := by
  let x : AddCircle (1 : ℝ) := α
  have hdZ : DenseRange (fun n : ℤ => n • x) := by
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa using hα
  have hdN : DenseRange (fun n : ℕ => n • x) := denseRange_zsmul_iff_nsmul.mp hdZ
  let H := Homeomorph.addRight (M • x + (β : AddCircle (1 : ℝ)))
  have hd : DenseRange (fun n : ℕ => n • x + (M • x + (β : AddCircle (1 : ℝ)))) :=
    H.surjective.denseRange.comp hdN H.continuous
  let U := ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ioo a b
  have ho : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hne : U.Nonempty := Set.Nonempty.image _ (Set.nonempty_Ioo.mpr hab)
  obtain ⟨n, y, hy, heq⟩ := hd.exists_mem_open ho hne
  have he : Int.fract ((n + M : ℕ) * α + β) = y := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (a := (0 : ℝ)) (p := (1 : ℝ))
      ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one ((n + M : ℕ) * α + β)⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩).mp
    rw [AddCircle.coe_fract]
    simpa only [AddCircle.coe_add, ← nsmul_eq_mul, add_nsmul, add_assoc] using heq.symm
  exact ⟨n + M, by omega, by rw [he]; exact hy⟩

lemma leading_prefix_in_four_progression (A E s M : ℕ) (hA : 0 < A) (hs : 0 < s) :
    ∃ j L : ℕ, M ≤ j ∧ 4 ^ (E + s * j) / 3 ^ L = A := by
  let D := Nat.log 3 A
  let α : ℝ := (2 * s : ℕ) * (Real.log 2 / Real.log 3)
  let β : ℝ := (2 * E : ℕ) * (Real.log 2 / Real.log 3)
  let a : ℝ := (Real.log A - (D : ℝ) * Real.log 3) / Real.log 3
  let b : ℝ := (Real.log (A + 1) - (D : ℝ) * Real.log 3) / Real.log 3
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hi : Irrational α := irrational_log_two_div_log_three.natCast_mul (by omega)
  have hlowNat : 3 ^ D ≤ A := Nat.pow_log_le_self 3 (ne_of_gt hA)
  have hhighNat : A + 1 ≤ 3 ^ (D + 1) :=
    Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 3) A)
  have hlow : (D : ℝ) * Real.log 3 ≤ Real.log A := by
    have hh : (3 : ℝ) ^ D ≤ A := by exact_mod_cast hlowNat
    have hl := Real.log_le_log (by positivity : 0 < (3 : ℝ) ^ D) hh
    simpa only [Real.log_pow] using hl
  have hhigh : Real.log (A + 1) ≤ ((D : ℝ) + 1) * Real.log 3 := by
    have hh : (A : ℝ) + 1 ≤ (3 : ℝ) ^ (D + 1) := by exact_mod_cast hhighNat
    have hl := Real.log_le_log (by positivity : 0 < (A : ℝ) + 1) hh
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using hl
  have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg (sub_nonneg.mpr hlow) (le_of_lt h3)
  have hab : a < b := by
    dsimp [a, b]
    apply (div_lt_div_iff_of_pos_right h3).mpr
    have hh := Real.log_lt_log hAr (show (A : ℝ) < A + 1 by linarith)
    linarith
  have hb : b ≤ 1 := by
    dsimp [b]
    rw [div_le_iff₀ h3]
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((D : ℝ) / α)
  obtain ⟨j, hj, hja, hjb⟩ := fract_affine_interval_arbitrarily_late hi β ha hab hb (M + N)
  have hx : (D : ℝ) < (j : ℝ) * α + β := by
    have hNj : (N : ℝ) ≤ j := by exact_mod_cast (show N ≤ j by omega)
    have hN' := (div_lt_iff₀ hαpos).mp hN
    nlinarith
  have hx0 : 0 ≤ (j : ℝ) * α + β := by positivity
  let F := Nat.floor ((j : ℝ) * α + β)
  have hDF : D ≤ F := (Nat.le_floor_iff hx0).mpr (le_of_lt hx)
  have hfract : Int.fract ((j : ℝ) * α + β) = j * α + β - F := by
    rw [Int.fract]
    have hh := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_floor_eq_floor hx0)
    simpa only [Int.cast_natCast] using congrArg (fun y : ℝ => j * α + β - y) hh.symm
  rw [hfract] at hja hjb
  have hja' := mul_lt_mul_of_pos_right hja h3
  have hjb' := mul_lt_mul_of_pos_right hjb h3
  dsimp [a] at hja'
  dsimp [b] at hjb'
  rw [div_mul_cancel₀ _ (ne_of_gt h3)] at hja' hjb'
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog : Real.log ((4 : ℝ) ^ (E + s * j)) = (j * α + β) * Real.log 3 := by
    rw [Real.log_pow, hlog4]
    dsimp [α, β]
    push_cast
    field_simp
    ring
  have hFD : ((F - D : ℕ) : ℝ) + D = F := by
    exact_mod_cast Nat.sub_add_cancel hDF
  have hloR : (A : ℝ) * (3 : ℝ) ^ (F - D) < (4 : ℝ) ^ (E + s * j) := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (ne_of_gt hAr) (by positivity), hlog, Real.log_pow]
    nlinarith
  have hhiR : (4 : ℝ) ^ (E + s * j) < ((A : ℝ) + 1) * (3 : ℝ) ^ (F - D) := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity : (A : ℝ) + 1 ≠ 0) (by positivity), hlog, Real.log_pow]
    nlinarith
  have hloN : A * 3 ^ (F - D) ≤ 4 ^ (E + s * j) := by exact_mod_cast le_of_lt hloR
  have hhiN : 4 ^ (E + s * j) < (A + 1) * 3 ^ (F - D) := by exact_mod_cast hhiR
  exact ⟨j, F - D, by omega, Nat.div_eq_of_lt_le hloN hhiN⟩

lemma power_in_progression_contains_block (w : List ℕ) (hw : ∀ d ∈ w, d < 3)
    (E s M : ℕ) (hs : 0 < s) :
    ∃ j : ℕ, M ≤ j ∧ w <:+: Nat.digits 3 (4 ^ (E + s * j)) := by
  let A := Nat.ofDigits 3 (w ++ [1])
  have hA : 0 < A := by
    dsimp [A]
    rw [Nat.ofDigits_append]
    simp only [Nat.ofDigits_singleton, mul_one]
    positivity
  have hdA : Nat.digits 3 A = w ++ [1] := by
    apply Nat.digits_ofDigits 3 (by decide)
    · intro d hd
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with hd | rfl
      · exact hw d hd
      · decide
    · intro h
      simp
  obtain ⟨j, L, hj, hdiv⟩ := leading_prefix_in_four_progression A E s M hA hs
  have hdrop : (Nat.digits 3 (4 ^ (E + s * j))).drop L = w ++ [1] := by
    have hh := congrArg (Nat.digits 3) hdiv
    rwa [digits_div_three_pow, hdA] at hh
  refine ⟨j, hj, (Nat.digits 3 (4 ^ (E + s * j))).take L, [1], ?_⟩
  rw [List.append_assoc, ← hdrop, List.take_append_drop]

lemma infix_flatten_of_mem {w : List ℕ} {F : List (List ℕ)} (hw : w ∈ F) :
    w <:+: F.flatten := by
  obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp hw
  exact ⟨u.flatten, v.flatten, by simp [List.flatten_append, List.append_assoc]⟩

/-- An invariant whose eventual membership depends only on finitely many
substring-presence tests cannot prove an eventual missing-digit exclusion.
Boolean combinations of the tests are allowed; no monotonicity is assumed.
This does not rule out arbitrary regular languages or tests of counts/endpoints. -/
lemma finite_pattern_certificate_no_power_seed (P : ℕ → Prop)
    (F : List (List ℕ)) (hF : ∀ w ∈ F, ∀ d ∈ w, d < 3)
    (B K s E : ℕ) (hs : 0 < s) (hKE : K ≤ E) (hBE : B < 4 ^ E)
    (hsame : ∀ n m : ℕ, B < n → B < m → 4 ^ K ∣ n → 4 ^ K ∣ m →
      (∀ w ∈ F, (w <:+: Nat.digits 3 n ↔ w <:+: Nat.digits 3 m)) → P n → P m)
    (hmul : ∀ n : ℕ, B < n → 4 ^ K ∣ n → P n → P (4 ^ s * n))
    (hsafe : ∀ n : ℕ, B < n → 4 ^ K ∣ n → Nat.digits 3 n ⊆ [0, 1] → ¬ P n) :
    ¬ P (4 ^ E) := by
  intro hseed
  have hflat : ∀ d ∈ F.flatten, d < 3 := by
    intro d hd
    obtain ⟨w, hw, hdw⟩ := List.mem_flatten.mp hd
    exact hF w hw d hdw
  have hpowB (j : ℕ) : B < 4 ^ (E + s * j) :=
    hBE.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hpowK (j : ℕ) : 4 ^ K ∣ 4 ^ (E + s * j) := pow_dvd_pow 4 (by omega)
  have hiterPow : ∀ j : ℕ, P (4 ^ (E + s * j)) := by
    intro j
    induction j with
    | zero => simpa using hseed
    | succ j ih =>
      have hh := hmul _ (hpowB j) (hpowK j) ih
      simpa only [Nat.mul_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  obtain ⟨j, _, hwordPow⟩ := power_in_progression_contains_block F.flatten hflat E s 0 hs
  obtain ⟨t, m, ht, hmB, hmK, hwordM, hgood, _⟩ :=
    arbitrary_block_can_disappear F.flatten hflat s K B hs
  have hPm : P m := by
    apply hsame (4 ^ (E + s * j)) m (hpowB j) hmB (hpowK j) hmK _ (hiterPow j)
    intro w hw
    have hh := infix_flatten_of_mem hw
    exact ⟨fun _ => hh.trans hwordM, fun _ => hh.trans hwordPow⟩
  have hmpos : 0 < m := by omega
  have horbitB (i : ℕ) : B < 4 ^ (s * i) * m :=
    hmB.trans_le (Nat.le_mul_of_pos_left m (by positivity))
  have horbitK (i : ℕ) : 4 ^ K ∣ 4 ^ (s * i) * m := dvd_mul_of_dvd_right hmK _
  have hiterM : ∀ i : ℕ, P (4 ^ (s * i) * m) := by
    intro i
    induction i with
    | zero => simpa using hPm
    | succ i ih =>
      have hh := hmul _ (horbitB i) (horbitK i) ih
      simpa only [Nat.mul_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  exact hsafe _ (horbitB t) (horbitK t) hgood (hiterM t)

#print axioms arbitrary_block_can_disappear
#print axioms no_substring_upward_invariant
#print axioms finite_pattern_certificate_no_power_seed
end Erdos406Work
