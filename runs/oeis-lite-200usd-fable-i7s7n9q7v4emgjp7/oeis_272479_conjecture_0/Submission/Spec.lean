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

section Helpers

private lemma sum_pow_ten_lt (m : ℕ) : ∑ i ∈ Finset.range m, 10 ^ i < 10 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- Adding a power of ten above all digits of `y` adds `1` to the digit sum. -/
private lemma digitsum_pow_add : ∀ (p y : ℕ), y < 10 ^ p →
    (Nat.digits 10 (10 ^ p + y)).sum = 1 + (Nat.digits 10 y).sum := by
  intro p
  induction p with
  | zero =>
    intro y hy
    have hy0 : y = 0 := by simpa using hy
    subst hy0
    norm_num
  | succ p ih =>
    intro y hy
    have hpos : 0 < 10 ^ (p + 1) + y := by positivity
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hpos, List.sum_cons]
    have hmod : (10 ^ (p + 1) + y) % 10 = y % 10 := by
      rw [pow_succ, add_comm, Nat.add_mul_mod_self_right]
    have hdiv : (10 ^ (p + 1) + y) / 10 = 10 ^ p + y / 10 := by
      rw [pow_succ, add_comm, Nat.add_mul_div_right _ _ (by norm_num : (0:ℕ) < 10), add_comm]
    have hylt : y / 10 < 10 ^ p := by
      apply Nat.div_lt_of_lt_mul
      rw [← pow_succ']
      exact hy
    rw [hmod, hdiv, ih _ hylt]
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0; simp
    · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h0, List.sum_cons]
      ring

/-- The digit sum of a sum of distinct powers of ten is the number of powers. -/
private lemma digitsum_finset_sum (A : Finset ℕ) :
    (Nat.digits 10 (∑ x ∈ A, 10 ^ x)).sum = A.card := by
  induction A using Finset.induction_on_max with
  | h0 => simp
  | step a s hs ih =>
    have hnotmem : a ∉ s := fun h => lt_irrefl a (hs a h)
    have hlt : ∑ x ∈ s, 10 ^ x < 10 ^ a := by
      calc ∑ x ∈ s, 10 ^ x ≤ ∑ x ∈ Finset.range a, 10 ^ x := by
            apply Finset.sum_le_sum_of_subset
            intro x hx
            exact Finset.mem_range.mpr (hs x hx)
        _ < 10 ^ a := sum_pow_ten_lt a
    rw [Finset.sum_insert hnotmem, digitsum_pow_add _ _ hlt, ih,
      Finset.card_insert_of_notMem hnotmem]
    omega

private lemma digitsum_le (n : ℕ) : (Nat.digits 10 n).sum ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h, List.sum_cons]
      have h1 : n / 10 < n := Nat.div_lt_self h (by norm_num)
      have h2 := ih (n / 10) h1
      omega

private lemma digitsum_pos : ∀ n : ℕ, 0 < n → 0 < (Nat.digits 10 n).sum := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h, List.sum_cons]
    rcases Nat.eq_zero_or_pos (n % 10) with h0 | h0
    · have h2 : 0 < n / 10 := by omega
      have h3 := ih (n / 10) (Nat.div_lt_self h (by norm_num)) h2
      omega
    · omega

/-- Congruence of sums of naturals modulo `n`. -/
private lemma modeq_sum {n : ℕ} (s : Finset ℕ) (f g : ℕ → ℕ)
    (h : ∀ i ∈ s, f i ≡ g i [MOD n]) : (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [MOD n] := by
  unfold Nat.ModEq
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl h, ← Finset.sum_nat_mod]

/-- Powers of ten are eventually periodic modulo `d`. -/
private lemma exists_period (d : ℕ) (hd : 0 < d) :
    ∃ u Δ : ℕ, 0 < Δ ∧ ∀ e, u ≤ e → 10 ^ (e + Δ) ≡ 10 ^ e [MOD d] := by
  have hpigeon : ∃ x ∈ Finset.range (d + 1), ∃ y ∈ Finset.range (d + 1),
      x ≠ y ∧ 10 ^ x % d = 10 ^ y % d := by
    apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := Finset.range d)
    · simp
    · intro i _
      exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
  obtain ⟨x, -, y, -, hxy, heq⟩ := hpigeon
  -- wlog x < y
  have key : ∀ u v : ℕ, u < v → 10 ^ u % d = 10 ^ v % d →
      ∃ u' Δ : ℕ, 0 < Δ ∧ ∀ e, u' ≤ e → 10 ^ (e + Δ) ≡ 10 ^ e [MOD d] := by
    intro u v huv h
    refine ⟨u, v - u, by omega, fun e he => ?_⟩
    have h1 : e + (v - u) = (e - u) + v := by omega
    have h2 : e = (e - u) + u := by omega
    calc (10:ℕ) ^ (e + (v - u)) = 10 ^ (e - u) * 10 ^ v := by rw [h1, pow_add]
      _ ≡ 10 ^ (e - u) * 10 ^ u [MOD d] := Nat.ModEq.mul_left _ (Nat.ModEq.symm h)
      _ = 10 ^ e := by rw [← pow_add, ← h2]
  rcases Nat.lt_or_ge x y with hlt | hge
  · exact key x y hlt heq
  · have hlt : y < x := by omega
    exact key y x hlt heq.symm

private lemma period_pow {d u Δ : ℕ} (hper : ∀ e, u ≤ e → 10 ^ (e + Δ) ≡ 10 ^ e [MOD d]) :
    ∀ (k e : ℕ), u ≤ e → 10 ^ (e + Δ * k) ≡ 10 ^ e [MOD d] := by
  intro k
  induction k with
  | zero =>
    intro e _
    simp only [Nat.mul_zero, Nat.add_zero]
    exact Nat.ModEq.refl _
  | succ k ih =>
    intro e he
    have h1 : e + Δ * (k + 1) = (e + Δ * k) + Δ := by ring
    rw [h1]
    exact (hper (e + Δ * k) (by omega)).trans (ih e he)

/-- Main construction: for every `q` there is a finset `A` of positive exponents with
`|A| = d + 9q` such that `∑_{x ∈ A} 10^x` is a multiple of `d`. -/
private lemma exists_finset (d : ℕ) (hd : 0 < d) :
    ∀ q : ℕ, ∃ A : Finset ℕ, A.card = d + 9 * q ∧ (∀ x ∈ A, 1 ≤ x) ∧ d ∣ ∑ x ∈ A, 10 ^ x := by
  obtain ⟨u, Δ, hΔ, hper⟩ := exists_period d hd
  suffices h : ∀ q : ℕ, ∃ A : Finset ℕ, A.card = d + 9 * q ∧ (∀ x ∈ A, u + 1 ≤ x) ∧
      d ∣ ∑ x ∈ A, 10 ^ x by
    intro q
    obtain ⟨A, h1, h2, h3⟩ := h q
    exact ⟨A, h1, fun x hx => le_trans (by omega) (h2 x hx), h3⟩
  intro q
  induction q with
  | zero =>
    -- base: d exponents, all congruent to u+1 modulo the period
    have hinj : Set.InjOn (fun i => u + 1 + Δ * i) (Finset.range d) := by
      intro i _ j _ hij
      simp only at hij
      have h1 : Δ * i = Δ * j := by omega
      exact Nat.eq_of_mul_eq_mul_left hΔ h1
    refine ⟨(Finset.range d).image (fun i => u + 1 + Δ * i), ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      omega
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      omega
    · rw [Finset.sum_image hinj, ← Nat.modEq_zero_iff_dvd]
      have h1 : (∑ i ∈ Finset.range d, 10 ^ (u + 1 + Δ * i)) ≡
          (∑ i ∈ Finset.range d, 10 ^ (u + 1)) [MOD d] := by
        apply modeq_sum
        intro i _
        exact period_pow hper i (u + 1) (by omega)
      refine h1.trans ?_
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      exact Nat.modEq_zero_iff_dvd.mpr ⟨10 ^ (u + 1), rfl⟩
  | succ q ih =>
    obtain ⟨A, hcard, hmem, hdvd⟩ := ih
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    set m := A.max' hne with hm
    have hmA : m ∈ A := A.max'_mem hne
    have hmu : u + 1 ≤ m := hmem m hmA
    -- the 10 new exponents, all ≡ 10^(m-1) mod d, all above max A
    set B : Finset ℕ := (Finset.range 10).image (fun i => (m - 1) + Δ * (m + 1 + i)) with hB
    have hBinj : Set.InjOn (fun i => (m - 1) + Δ * (m + 1 + i)) (Finset.range 10) := by
      intro i _ j _ hij
      simp only at hij
      have h1 : Δ * (m + 1 + i) = Δ * (m + 1 + j) := by omega
      have h2 := Nat.eq_of_mul_eq_mul_left hΔ h1
      omega
    have hBcard : B.card = 10 := by
      rw [hB, Finset.card_image_of_injOn hBinj, Finset.card_range]
    have hBgt : ∀ b ∈ B, m < b := by
      intro b hb
      rw [hB, Finset.mem_image] at hb
      obtain ⟨i, _, rfl⟩ := hb
      have h1 : m + 1 + i ≤ Δ * (m + 1 + i) := Nat.le_mul_of_pos_left _ hΔ
      omega
    have hdisj : Disjoint (A.erase m) B := by
      rw [Finset.disjoint_left]
      intro x hx hxB
      have h1 : x ≤ m := A.le_max' x (Finset.mem_of_mem_erase hx)
      have h2 := hBgt x hxB
      omega
    refine ⟨(A.erase m) ∪ B, ?_, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hmA, hBcard]
      omega
    · intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hmem x (Finset.mem_of_mem_erase hx)
      · have h1 := hBgt x hx
        omega
    · rw [Finset.sum_union hdisj, ← Nat.modEq_zero_iff_dvd]
      -- ∑ B ≡ 10 * 10^(m-1) = 10^m
      have hSB : (∑ b ∈ B, 10 ^ b) ≡ 10 ^ m [MOD d] := by
        rw [hB, Finset.sum_image hBinj]
        have h1 : (∑ i ∈ Finset.range 10, 10 ^ ((m - 1) + Δ * (m + 1 + i))) ≡
            (∑ i ∈ Finset.range 10, 10 ^ (m - 1)) [MOD d] := by
          apply modeq_sum
          intro i _
          exact period_pow hper (m + 1 + i) (m - 1) (by omega)
        refine h1.trans ?_
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← pow_succ']
        have h2 : (m - 1).succ = m := by omega
        rw [h2]
      have hSA : (∑ x ∈ A.erase m, 10 ^ x) + 10 ^ m = ∑ x ∈ A, 10 ^ x :=
        Finset.sum_erase_add A _ hmA
      have h2 : (∑ x ∈ A.erase m, 10 ^ x) + (∑ b ∈ B, 10 ^ b) ≡
          (∑ x ∈ A.erase m, 10 ^ x) + 10 ^ m [MOD d] := Nat.ModEq.add_left _ hSB
      refine h2.trans ?_
      rw [hSA]
      exact Nat.modEq_zero_iff_dvd.mpr hdvd

/-- For every `n > 0` there is a Harshad amicable partner of `n`. -/
private lemma exists_partner (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n := by
  have hd1 : 0 < (Nat.digits 10 n).sum := digitsum_pos n hn
  have hdle : (Nat.digits 10 n).sum ≤ n := digitsum_le n
  have h9 : (Nat.digits 10 n).sum ≡ n [MOD 9] := (Nat.modEq_nine_digits_sum n).symm
  have h9' : 9 ∣ n - (Nat.digits 10 n).sum := (Nat.modEq_iff_dvd' hdle).mp h9
  obtain ⟨q, hq⟩ := h9'
  obtain ⟨A, hcard, hmem1, hdvd⟩ := exists_finset (Nat.digits 10 n).sum hd1 q
  have hcard' : A.card = n := by omega
  have h10 : 10 * n ≤ ∑ x ∈ A, 10 ^ x := by
    calc 10 * n = ∑ _x ∈ A, 10 := by
          rw [Finset.sum_const, hcard', smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ A, 10 ^ x := by
          apply Finset.sum_le_sum
          intro i hi
          calc (10:ℕ) = 10 ^ 1 := (pow_one 10).symm
            _ ≤ 10 ^ i := Nat.pow_le_pow_right (by norm_num) (hmem1 i hi)
  refine ⟨∑ x ∈ A, 10 ^ x, by omega, by omega, hdvd, ?_⟩
  rw [digitsum_finset_sum, hcard']

end Helpers

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  obtain ⟨k, hkpos, hkn, hdvd1, hdvd2⟩ := exists_partner n hn
  have hne : {k' : ℕ | k' > 0 ∧ k' ≠ n ∧ (Nat.digits 10 n).sum ∣ k' ∧
      (Nat.digits 10 k').sum ∣ n}.Nonempty := ⟨k, hkpos, hkn, hdvd1, hdvd2⟩
  unfold a
  simp only
  rw [dif_pos hne]
  have hmem := Nat.sInf_mem hne
  exact Nat.pos_iff_ne_zero.mp hmem.1
