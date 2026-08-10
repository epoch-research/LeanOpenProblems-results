import FormalConjectures.Util.ProblemImports
open Nat
open Classical

set_option maxHeartbeats 1000000

/-- Linear congruence: if `gcd(9,d) ∣ n` and `d ≤ n`, there is `m ≤ n` with `d ∣ n + 9 m`. -/
lemma lemmaC (d n : ℕ) (hd : 0 < d) (hdn : d ≤ n) (hg : Nat.gcd 9 d ∣ n) :
    ∃ m, m ≤ n ∧ d ∣ (n + 9 * m) := by
  set g := Nat.gcd 9 d with hgdef
  obtain ⟨q, hq⟩ := hg          -- n = g * q
  -- Bezout
  have bez : (g : ℤ) = 9 * Nat.gcdA 9 d + d * Nat.gcdB 9 d := Nat.gcd_eq_gcd_ab 9 d
  set A := Nat.gcdA 9 d with hA
  set B := Nat.gcdB 9 d with hB
  have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
  have hdne : (d : ℤ) ≠ 0 := ne_of_gt hdpos
  set m0 : ℤ := (-(A * q)) % d with hm0
  have hm0nonneg : 0 ≤ m0 := Int.emod_nonneg _ hdne
  have hm0lt : m0 < d := Int.emod_lt_of_pos _ hdpos
  set m : ℕ := m0.toNat with hmdef
  have hmcast : (m : ℤ) = m0 := Int.toNat_of_nonneg hm0nonneg
  have hmltd : m < d := by
    have : (m : ℤ) < d := by rw [hmcast]; exact hm0lt
    exact_mod_cast this
  refine ⟨m, le_of_lt (lt_of_lt_of_le hmltd hdn), ?_⟩
  -- show d ∣ n + 9 m, prove over ℤ
  have key : (d : ℤ) ∣ ((n : ℤ) + 9 * (m : ℤ)) := by
    -- m ≡ -(A q) [ZMOD d]
    have hmmod : (m : ℤ) ≡ (-(A * q)) [ZMOD d] := by
      rw [hmcast, hm0]
      exact Int.mod_modEq _ _
    -- n = 9*(A q) + d*(B q)  from bezout * q
    have hnint : (n : ℤ) = 9 * (A * q) + d * (B * q) := by
      have hng : (n : ℤ) = g * q := by rw [hq]; push_cast; ring
      rw [hng, bez]; ring
    have h1 : ((n : ℤ) + 9 * (m : ℤ)) ≡ ((n : ℤ) + 9 * (-(A * q))) [ZMOD d] :=
      (Int.ModEq.refl (n : ℤ)).add (hmmod.mul_left 9)
    have h2 : (n : ℤ) + 9 * (-(A * q)) = d * (B * q) := by rw [hnint]; ring
    have h3 : ((n : ℤ) + 9 * (m : ℤ)) ≡ 0 [ZMOD d] := by
      rw [h2] at h1
      exact h1.trans (Int.modEq_zero_iff_dvd.mpr ⟨B * q, rfl⟩)
    exact Int.modEq_zero_iff_dvd.mp h3
  have : ((n + 9 * m : ℕ) : ℤ) = (n : ℤ) + 9 * (m : ℤ) := by push_cast; ring
  rw [← this] at key
  exact_mod_cast key

/-- Pigeonhole: powers of `10` in `ZMod d` are eventually periodic. -/
lemma pow_period (d : ℕ) (hd : 0 < d) :
    ∃ t L : ℕ, 0 < L ∧ (10 : ZMod d) ^ (t + L) = (10 : ZMod d) ^ t := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hcard : Fintype.card (ZMod d) < Fintype.card (Fin (d + 1)) := by
    rw [ZMod.card, Fintype.card_fin]; omega
  obtain ⟨a, b, hab, hval⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (d + 1) => (10 : ZMod d) ^ (i : ℕ)) hcard
  rcases lt_or_gt_of_ne (fun h => hab (Fin.ext h)) with hlt | hgt
  · exact ⟨a, b - a, by omega, by rw [show (a : ℕ) + (b - a) = b by omega]; exact hval.symm⟩
  · exact ⟨b, a - b, by omega, by rw [show (b : ℕ) + (a - b) = a by omega]; exact hval⟩

/-- Periodicity of powers of `10` from the period found by pigeonhole. -/
lemma pow_periodic {d : ℕ} {t L : ℕ}
    (hper : (10 : ZMod d) ^ (t + L) = (10 : ZMod d) ^ t) :
    ∀ i, (10 : ZMod d) ^ (t + i * L) = (10 : ZMod d) ^ t := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have : t + (i + 1) * L = (t + i * L) + L := by ring
    rw [this, pow_add, ih, ← pow_add, hper]

/-- Key lemma: for `d ≥ 1`, `d ≤ n`, `gcd(9,d) ∣ n`, there is a positive multiple of `d`
with digit sum exactly `n`. -/
lemma lemmaA (d n : ℕ) (hd : 0 < d) (hdn : d ≤ n) (hg : Nat.gcd 9 d ∣ n) :
    ∃ k, 0 < k ∧ d ∣ k ∧ (Nat.digits 10 k).sum = n := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨t, L, hLpos, hper⟩ := pow_period d hd
  obtain ⟨m, hmn, hdvd⟩ := lemmaC d n hd hdn hg
  -- positions
  set e : ℕ → ℕ := fun i => t + i * L + (if i < n - m then 0 else 1) with he
  have hind : ∀ i, (if i < n - m then (0:ℕ) else 1) ≤ (if i + 1 < n - m then 0 else 1) := by
    intro i
    by_cases h : i + 1 < n - m
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]; split <;> omega
  have eStrict : ∀ i, e i < e (i + 1) := by
    intro i
    have hmul : (i + 1) * L = i * L + L := by ring
    have h2 := hind i
    have h3 : 1 ≤ L := hLpos
    simp only [he]
    omega
  -- partial sums
  set P : ℕ → ℕ := fun j => ∑ i ∈ Finset.range j, 10 ^ (e i) with hP
  have hd1 : Nat.digits 10 1 = [1] := by
    rw [Nat.digits_def' (by norm_num) (by norm_num)]; simp
  -- digit sum induction
  have A : ∀ j, (Nat.digits 10 (P j)).sum = j ∧ (Nat.digits 10 (P j)).length ≤ e j := by
    intro j
    induction j with
    | zero =>
      refine ⟨by simp [hP], ?_⟩
      simp [hP]
    | succ j ih =>
      obtain ⟨ihs, ihl⟩ := ih
      set k := e j - (Nat.digits 10 (P j)).length with hk
      have hek : (Nat.digits 10 (P j)).length + k = e j := by omega
      have hPstep : P (j + 1) = P j + 10 ^ (e j) := by
        simp only [hP, Finset.sum_range_succ]
      have happ : Nat.digits 10 (P (j + 1))
          = Nat.digits 10 (P j) ++ List.replicate k 0 ++ Nat.digits 10 1 := by
        have hPs : P (j + 1) = P j + 10 ^ ((Nat.digits 10 (P j)).length + k) * 1 := by
          rw [hek, mul_one]; exact hPstep
        rw [hPs]
        exact (Nat.digits_append_zeroes_append_digits (by norm_num) (by norm_num)).symm
      refine ⟨?_, ?_⟩
      · rw [happ, List.sum_append, List.sum_append, ihs, hd1]
        simp [List.sum_replicate]
      · rw [happ, List.length_append, List.length_append, List.length_replicate, hd1]
        simp only [List.length_singleton]
        have := eStrict j
        omega
  -- final number
  refine ⟨P n, ?_, ?_, (A n).1⟩
  · -- 0 < P n
    have hn1 : 1 ≤ n := le_trans hd hdn
    rw [hP]
    apply Finset.sum_pos
    · intro i _; positivity
    · rw [Finset.nonempty_range_iff]; omega
  · -- d ∣ P n
    refine (ZMod.natCast_eq_zero_iff (P n) d).mp ?_
    have hcast : ((P n : ℕ) : ZMod d) = ∑ i ∈ Finset.range n, (10 : ZMod d) ^ (e i) := by
      simp only [hP, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
    rw [hcast, ← Finset.sum_range_add_sum_Ico _ (show n - m ≤ n by omega)]
    have e1 : ∀ i ∈ Finset.range (n - m), (10 : ZMod d) ^ (e i) = (10 : ZMod d) ^ t := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hei : e i = t + i * L := by simp only [he]; rw [if_pos hi, add_zero]
      rw [hei]; exact pow_periodic hper i
    have e2 : ∀ i ∈ Finset.Ico (n - m) n,
        (10 : ZMod d) ^ (e i) = (10 : ZMod d) ^ t * (10 : ZMod d) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hei : e i = t + i * L + 1 := by
        simp only [he]; rw [if_neg (by omega : ¬ i < n - m)]
      rw [hei, pow_succ, pow_periodic hper i]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
        Finset.sum_const, Finset.sum_const, Finset.card_range, Nat.card_Ico]
    have hcardm : n - (n - m) = m := by omega
    rw [hcardm, nsmul_eq_mul, nsmul_eq_mul]
    have hfact : (↑(n - m) : ZMod d) * (10 : ZMod d) ^ t
          + (↑m : ZMod d) * ((10 : ZMod d) ^ t * (10 : ZMod d))
        = (10 : ZMod d) ^ t * ((↑(n - m) : ZMod d) + (↑m : ZMod d) * (10 : ZMod d)) := by ring
    rw [hfact]
    have hsum0 : (↑(n - m) : ZMod d) + (↑m : ZMod d) * (10 : ZMod d) = (↑(n + 9 * m) : ZMod d) := by
      rw [Nat.cast_sub hmn]; push_cast; ring
    rw [hsum0, (ZMod.natCast_eq_zero_iff (n + 9 * m) d).mpr hdvd, mul_zero]

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

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  -- digit sum of n
  set d := (Nat.digits 10 n).sum with hddef
  have hd : 0 < d := by
    have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have hlast := Nat.getLast_digit_ne_zero 10 (show n ≠ 0 by omega)
    have hmem : (Nat.digits 10 n).getLast hne ∈ Nat.digits 10 n := List.getLast_mem hne
    have hpos : 0 < (Nat.digits 10 n).getLast hne := Nat.pos_of_ne_zero hlast
    exact lt_of_lt_of_le hpos (List.le_sum_of_mem hmem)
  have hdn : d ≤ n := Nat.digit_sum_le 10 n
  -- gcd(9,d) ∣ n
  have hmod : n ≡ d [MOD 9] := Nat.modEq_digits_sum 9 10 (by norm_num) n
  have hg : Nat.gcd 9 d ∣ n := by
    have h1 : n ≡ d [MOD Nat.gcd 9 d] := hmod.of_dvd (Nat.gcd_dvd_left 9 d)
    have h2 : d ≡ 0 [MOD Nat.gcd 9 d] := (Nat.modEq_zero_iff_dvd).mpr (Nat.gcd_dvd_right 9 d)
    exact (Nat.modEq_zero_iff_dvd).mp (h1.trans h2)
  -- get the multiple of d with digit sum n
  obtain ⟨k0, hk0pos, hk0dvd, hk0sum⟩ := lemmaA d n hd hdn hg
  -- partner
  set k := 10 ^ (n + 1) * k0 with hkdef
  have hkpos : 0 < k := by rw [hkdef]; positivity
  have hpow : n < 10 ^ (n + 1) := by
    calc n < n + 1 := by omega
      _ ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self.le
      _ ≤ 10 ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) _
  have hkgtn : n < k := by
    rw [hkdef]
    calc n < 10 ^ (n + 1) := hpow
      _ = 10 ^ (n + 1) * 1 := by ring
      _ ≤ 10 ^ (n + 1) * k0 := by apply Nat.mul_le_mul_left; omega
  have hkdvd : d ∣ k := by rw [hkdef]; exact Dvd.dvd.mul_left hk0dvd _
  have hksum : (Nat.digits 10 k).sum = n := by
    rw [hkdef, Nat.digits_base_pow_mul (by norm_num) hk0pos, List.sum_append,
      List.sum_replicate, hk0sum]
    simp
  -- membership in partners
  have hmem : k ∈ {k : ℕ | k > 0 ∧ k ≠ n ∧ d ∣ k ∧ (Nat.digits 10 k).sum ∣ n} :=
    ⟨hkpos, by omega, hkdvd, by simp [hksum]⟩
  have hne : ({k : ℕ | k > 0 ∧ k ≠ n ∧ d ∣ k ∧ (Nat.digits 10 k).sum ∣ n} : Set ℕ).Nonempty :=
    ⟨k, hmem⟩
  -- unfold a
  show (if _ : ({k : ℕ | k > 0 ∧ k ≠ n ∧ d ∣ k ∧ (Nat.digits 10 k).sum ∣ n} : Set ℕ).Nonempty
        then sInf {k : ℕ | k > 0 ∧ k ≠ n ∧ d ∣ k ∧ (Nat.digits 10 k).sum ∣ n} else 0) ≠ 0
  rw [dif_pos hne]
  have hsinf := Nat.sInf_mem hne
  have hpos : 0 < sInf {k : ℕ | k > 0 ∧ k ≠ n ∧ d ∣ k ∧ (Nat.digits 10 k).sum ∣ n} := hsinf.1
  omega
