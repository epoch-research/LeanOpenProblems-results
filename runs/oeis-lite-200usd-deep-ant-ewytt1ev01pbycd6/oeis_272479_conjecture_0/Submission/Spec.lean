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


/-- digit sum -/
def D (m : ℕ) : ℕ := (Nat.digits 10 m).sum

theorem dsum_lt (m : ℕ) (hm : 0 < m) (h10 : 10 ∣ m) : D m < m := by
  unfold D
  rw [Nat.digits_def' (by norm_num) hm]
  have hmod : m % 10 = 0 := by omega
  rw [List.sum_cons, hmod, Nat.zero_add]
  calc (Nat.digits 10 (m / 10)).sum ≤ m / 10 := Nat.digit_sum_le 10 (m/10)
    _ < m := Nat.div_lt_self hm (by norm_num)

-- flatten of replicate, value mod e
theorem flat_mod (e L : ℕ) (blk : List ℕ) (hlen : blk.length = L) (hL : (10:ℕ)^L ≡ 1 [MOD e])
    (m : ℕ) :
    Nat.ofDigits 10 ((List.replicate m blk).flatten) ≡ m * Nat.ofDigits 10 blk [MOD e] := by
  induction m with
  | zero => simp [Nat.ModEq.refl]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, hlen]
    calc Nat.ofDigits 10 blk + 10 ^ L * Nat.ofDigits 10 ((List.replicate k blk).flatten)
        ≡ Nat.ofDigits 10 blk + 1 * (k * Nat.ofDigits 10 blk) [MOD e] := by
          exact (Nat.ModEq.refl _).add (hL.mul ih)
      _ = (k+1) * Nat.ofDigits 10 blk := by ring

-- flatten of replicate, sum
theorem flat_sum (blk : List ℕ) (m : ℕ) :
    ((List.replicate m blk).flatten).sum = m * blk.sum := by
  induction m with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, List.sum_append, ih]; ring

-- flatten of replicate, length
theorem flat_len (blk : List ℕ) (m : ℕ) :
    ((List.replicate m blk).flatten).length = m * blk.length := by
  induction m with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; ring

-- flatten of replicate, membership
theorem flat_mem (blk : List ℕ) (m : ℕ) (x : ℕ) (hx : x ∈ (List.replicate m blk).flatten) :
    x ∈ blk := by
  rw [List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [List.eq_of_mem_replicate hl] at hxl
  exact hxl

-- solving the linear congruence  9*B ≡ -c  (mod e)
theorem congr_sol (e c : ℕ) (he : 0 < e) (h : Nat.gcd 9 e ∣ c) :
    ∃ B : ℕ, B < e ∧ e ∣ (c + 9 * B) := by
  obtain ⟨q, hq⟩ := h
  set u : ℤ := Nat.gcdA 9 e with hu
  set v : ℤ := Nat.gcdB 9 e with hv
  have hbez : (Nat.gcd 9 e : ℤ) = 9 * u + e * v := Nat.gcd_eq_gcd_ab 9 e
  set B0 : ℤ := -(u * q) with hB0
  -- key: c + 9*B0 = e * (v*q)
  have key : (c : ℤ) + 9 * B0 = (e : ℤ) * (v * q) := by
    have : (c : ℤ) = (Nat.gcd 9 e : ℤ) * q := by rw [hq]; push_cast; ring
    rw [this, hbez, hB0]; ring
  refine ⟨(B0 % e).toNat, ?_, ?_⟩
  · have h1 : 0 ≤ B0 % e := Int.emod_nonneg B0 (by exact_mod_cast he.ne')
    have h2 : B0 % e < e := Int.emod_lt_of_pos B0 (by exact_mod_cast he)
    omega
  · -- e ∣ c + 9 * (B0 % e).toNat
    have hcast : ((B0 % e).toNat : ℤ) = B0 % e :=
      Int.toNat_of_nonneg (Int.emod_nonneg B0 (by exact_mod_cast he.ne'))
    rw [← Int.natCast_dvd_natCast]
    push_cast
    rw [hcast]
    -- c + 9*(B0 % e) = e*(v*q) - 9*e*(B0/e)
    have hmod : B0 % e = B0 - e * (B0 / e) := by rw [Int.emod_def]
    rw [hmod]
    have : (c : ℤ) + 9 * (B0 - e * (B0 / e)) = (e : ℤ) * (v * q - 9 * (B0 / e)) := by
      have := key; ring_nf; ring_nf at this; linarith [this]
    rw [this]
    exact Dvd.intro _ rfl

-- factorization: split off the 2,5 part of d
theorem factor_props (d : ℕ) (hd : 0 < d) :
    ∃ g e : ℕ, 0 < e ∧ g * e = d ∧ g ∣ 10 ^ d ∧ Nat.Coprime 10 e ∧ e ∣ d := by
  set a := d.factorization 2 with ha
  set b := d.factorization 5 with hb
  set g := 2 ^ a * 5 ^ b with hg
  have h2d : 2 ^ a ∣ d := Nat.ordProj_dvd d 2
  have h5d : 5 ^ b ∣ d := Nat.ordProj_dvd d 5
  have hcop25 : Nat.Coprime (2 ^ a) (5 ^ b) := by
    have base : Nat.Coprime 2 5 := by norm_num
    exact Nat.Coprime.pow a b base
  have hgd : g ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop25 h2d h5d
  -- a ≤ d, b ≤ d
  have hale : a ≤ d := le_of_lt (Nat.factorization_lt 2 hd.ne')
  have hble : b ≤ d := le_of_lt (Nat.factorization_lt 5 hd.ne')
  have hg10 : g ∣ 10 ^ d := by
    have e1 : 2 ^ a ∣ 2 ^ d := pow_dvd_pow 2 hale
    have e2 : 5 ^ b ∣ 5 ^ d := pow_dvd_pow 5 hble
    have : (2 : ℕ) ^ d * 5 ^ d = 10 ^ d := by rw [← Nat.mul_pow]
    rw [hg, ← this]
    exact Nat.mul_dvd_mul e1 e2
  set e := d / g with he
  have hgpos : 0 < g := by positivity
  have hge : g * e = d := Nat.mul_div_cancel' hgd
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, Nat.mul_zero] at hge; omega
    · exact h
  have hed : e ∣ d := Dvd.intro_left g hge
  -- factorization of g
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have hp5 : Nat.Prime 5 := by norm_num
  have hgfact2 : g.factorization 2 = a := by
    rw [hg, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow hp2, Nat.Prime.factorization_pow hp5,
      Finsupp.single_apply, Finsupp.single_apply]
    norm_num
  have hgfact5 : g.factorization 5 = b := by
    rw [hg, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow hp2, Nat.Prime.factorization_pow hp5,
      Finsupp.single_apply, Finsupp.single_apply]
    norm_num
  have hefact2 : e.factorization 2 = 0 := by
    rw [he, Nat.factorization_div hgd]; simp [hgfact2, ha]
  have hefact5 : e.factorization 5 = 0 := by
    rw [he, Nat.factorization_div hgd]; simp [hgfact5, hb]
  have hne2 : ¬ (2 ∣ e) := by
    intro hc
    have := (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hepos.ne' hc)
    omega
  have hne5 : ¬ (5 ∣ e) := by
    intro hc
    have := (Nat.Prime.factorization_pos_of_dvd (by norm_num) hepos.ne' hc)
    omega
  have hcop : Nat.Coprime 10 e := by
    have c2 : Nat.Coprime 2 e := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hne2
    have c5 : Nat.Coprime 5 e := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hne5
    have : Nat.Coprime (2 * 5) e := Nat.Coprime.mul c2 c5
    simpa using this
  exact ⟨g, e, hepos, hge, hg10, hcop, hed⟩

-- the exponent L for the block construction
theorem exponent_ok (e : ℕ) (hcop : Nat.Coprime 10 e) :
    (10:ℕ) ^ (max 2 e.totient) ≡ 1 [MOD e] := by
  rcases eq_or_ne e 1 with rfl | he1
  · exact Nat.modEq_one
  · have he0 : e ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hcop
    have he2 : e ≠ 2 := by rintro rfl; simp [Nat.Coprime] at hcop
    have htot : 2 ≤ e.totient := by
      have h1 : e.totient ≠ 1 := by
        rw [Ne, Nat.totient_eq_one_iff]; push_neg; exact ⟨he1, he2⟩
      have h0 : 0 < e.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero he0)
      omega
    rw [max_eq_right htot]
    exact Nat.ModEq.pow_totient hcop

-- block construction: for L≥2 and 10^L ≡ 1 [MOD e], build digit list with
-- entries < 10, sum = A + B, value ≡ A + 10*B [MOD e].
theorem block_construction (e A B L : ℕ) (hL2 : 2 ≤ L) (hmodL : (10:ℕ)^L ≡ 1 [MOD e]) :
    ∃ Cd : List ℕ,
      (∀ x ∈ Cd, x < 10) ∧
      Cd.sum = A + B ∧
      Nat.ofDigits 10 Cd ≡ A + 10 * B [MOD e] := by
  set b1 : List ℕ := 1 :: List.replicate (L-1) 0 with hb1
  set b2 : List ℕ := 0 :: 1 :: List.replicate (L-2) 0 with hb2
  have hb1len : b1.length = L := by rw [hb1]; simp; omega
  have hb2len : b2.length = L := by rw [hb2]; simp; omega
  have hb1val : Nat.ofDigits 10 b1 = 1 := by rw [hb1, Nat.ofDigits_cons]; simp
  have hb2val : Nat.ofDigits 10 b2 = 10 := by rw [hb2, Nat.ofDigits_cons, Nat.ofDigits_cons]; simp
  have hb1sum : b1.sum = 1 := by rw [hb1]; simp
  have hb2sum : b2.sum = 1 := by rw [hb2]; simp
  have hb1mem : ∀ x ∈ b1, x < 10 := by
    rw [hb1]; intro x hx; rcases List.mem_cons.1 hx with h | h
    · omega
    · rw [List.eq_of_mem_replicate h]; omega
  have hb2mem : ∀ x ∈ b2, x < 10 := by
    rw [hb2]; intro x hx
    rcases List.mem_cons.1 hx with h | h
    · omega
    rcases List.mem_cons.1 h with h' | h'
    · omega
    · rw [List.eq_of_mem_replicate h']; omega
  refine ⟨(List.replicate A b1).flatten ++ (List.replicate B b2).flatten, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with h | h
    · exact hb1mem x (flat_mem b1 A x h)
    · exact hb2mem x (flat_mem b2 B x h)
  · rw [List.sum_append, flat_sum, flat_sum, hb1sum, hb2sum]; ring
  · rw [Nat.ofDigits_append, flat_len, hb1len]
    have h1 : Nat.ofDigits 10 ((List.replicate A b1).flatten) ≡ A * 1 [MOD e] := by
      have := flat_mod e L b1 hb1len hmodL A; rwa [hb1val] at this
    have h2 : Nat.ofDigits 10 ((List.replicate B b2).flatten) ≡ B * 10 [MOD e] := by
      have := flat_mod e L b2 hb2len hmodL B; rwa [hb2val] at this
    have h3 : (10:ℕ) ^ (A * L) ≡ 1 [MOD e] := by
      calc (10:ℕ) ^ (A * L) = (10 ^ L) ^ A := by rw [← pow_mul, Nat.mul_comm]
        _ ≡ 1 ^ A [MOD e] := hmodL.pow A
        _ = 1 := one_pow A
    calc Nat.ofDigits 10 ((List.replicate A b1).flatten)
          + 10 ^ (A * L) * Nat.ofDigits 10 ((List.replicate B b2).flatten)
        ≡ A * 1 + 1 * (B * 10) [MOD e] := h1.add (h3.mul h2)
      _ = A + 10 * B := by ring

-- D n > 0 for n > 0
theorem dsum_pos (n : ℕ) (hn : 0 < n) : 0 < D n := by
  apply Nat.pos_of_ne_zero
  intro hc
  unfold D at hc
  have : ∀ x ∈ Nat.digits 10 n, x = 0 := by
    have := List.sum_eq_zero_iff.mp hc
    intro x hx; exact this x hx
  have hz : Nat.ofDigits 10 (Nat.digits 10 n) = 0 := by
    have : Nat.digits 10 n = List.replicate (Nat.digits 10 n).length 0 :=
      List.eq_replicate_of_mem this
    rw [this]; simp
  rw [Nat.ofDigits_digits] at hz
  omega

-- MAIN witness existence
theorem witness_exists (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ k ≠ n ∧ D n ∣ k ∧ D k ∣ n := by
  set d := D n with hddef
  have hdpos : 0 < d := dsum_pos n hn
  have hdle : d ≤ n := Nat.digit_sum_le 10 n
  obtain ⟨g, e, hepos, hge, hg10, hcop, hed⟩ := factor_props d hdpos
  -- e ≤ n
  have hedn : e ≤ n := le_trans (Nat.le_of_dvd hdpos hed) hdle
  -- gcd 9 e ∣ n
  have hgcd9 : Nat.gcd 9 e ∣ n := by
    have h1 : Nat.gcd 9 e ∣ Nat.gcd 9 d :=
      Nat.dvd_gcd (Nat.gcd_dvd_left 9 e) (dvd_trans (Nat.gcd_dvd_right 9 e) hed)
    have hmod9 : d % 9 = n % 9 := by
      have := (Nat.modEq_nine_digits_sum n)  -- n ≡ (digits 10 n).sum [MOD 9]
      rw [hddef]; unfold D; exact this.symm
    have h2 : Nat.gcd 9 d = Nat.gcd 9 n := by
      rw [Nat.gcd_rec 9 d, Nat.gcd_rec 9 n, hmod9]
    have h3 : Nat.gcd 9 n ∣ n := Nat.gcd_dvd_right 9 n
    rw [h2] at h1
    exact dvd_trans h1 h3
  -- solve congruence
  obtain ⟨B, hBlt, hBdvd⟩ := congr_sol e n hepos hgcd9
  have hBn : B ≤ n := le_of_lt (lt_of_lt_of_le hBlt hedn)
  -- L
  set L := max 2 e.totient with hLdef
  have hL2 : 2 ≤ L := le_max_left 2 _
  have hmodL : (10:ℕ) ^ L ≡ 1 [MOD e] := exponent_ok e hcop
  -- block construction
  obtain ⟨Cd, hCdmem, hCdsum, hCdval⟩ := block_construction e (n - B) B L hL2 hmodL
  have hCdsum' : Cd.sum = n := by rw [hCdsum]; omega
  set C := Nat.ofDigits 10 Cd with hCdef
  -- e ∣ C
  have heC : e ∣ C := by
    have h1 : C ≡ (n - B) + 10 * B [MOD e] := hCdval
    have h2 : (n - B) + 10 * B = n + 9 * B := by omega
    rw [h2] at h1
    have h3 : e ∣ n + 9 * B := hBdvd
    -- C ≡ n + 9B ≡ 0
    have h4 : (n + 9 * B) ≡ 0 [MOD e] := (Nat.modEq_zero_iff_dvd).mpr h3
    have : C ≡ 0 [MOD e] := h1.trans h4
    exact (Nat.modEq_zero_iff_dvd).mp this
  -- D C = n
  have hDC : D C = n := by
    unfold D; rw [hCdef]
    rw [Nat.sum_digits_ofDigits_eq_sum (by norm_num) ⟨rfl, hCdmem⟩]
    exact hCdsum'
  -- full number
  set FL := List.replicate d 0 ++ Cd with hFLdef
  set k := Nat.ofDigits 10 FL with hkdef
  have hFLmem : ∀ x ∈ FL, x < 10 := by
    intro x hx
    rw [hFLdef, List.mem_append] at hx
    rcases hx with h | h
    · rw [List.eq_of_mem_replicate h]; omega
    · exact hCdmem x h
  have hkval : k = 10 ^ d * C := by
    rw [hkdef, hFLdef, Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
      List.length_replicate]
    ring
  -- D k = n
  have hDk : D k = n := by
    unfold D; rw [hkdef]
    rw [Nat.sum_digits_ofDigits_eq_sum (by norm_num) ⟨rfl, hFLmem⟩]
    rw [hFLdef, List.sum_append, List.sum_replicate]
    simp [hCdsum']
  -- d ∣ k
  have hdk : d ∣ k := by
    rw [hkval]
    have hmul : g * e ∣ 10 ^ d * C := Nat.mul_dvd_mul hg10 heC
    rwa [hge] at hmul
  -- k > 0
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso; rw [h] at hDk; unfold D at hDk; simp at hDk; omega
    · exact h
  -- k ≠ n
  have hkne : k ≠ n := by
    intro hkn
    have h10k : 10 ∣ k := by
      rw [hkval]
      exact Dvd.dvd.mul_right (dvd_pow_self 10 hdpos.ne') C
    have : D k < k := dsum_lt k hkpos h10k
    rw [hDk, hkn] at this
    omega
  refine ⟨k, hkpos, hkne, hdk, ?_⟩
  rw [hDk]

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  obtain ⟨k, hk0, hkn, hdnk, hdkn⟩ := witness_exists n hn
  unfold a
  have hne : ({k | k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n} : Set ℕ).Nonempty :=
    ⟨k, hk0, hkn, hdnk, hdkn⟩
  simp only []
  rw [dif_pos hne]
  intro hc
  have hmem := Nat.sInf_mem hne
  rw [hc] at hmem
  exact absurd hmem.1 (lt_irrefl 0)
