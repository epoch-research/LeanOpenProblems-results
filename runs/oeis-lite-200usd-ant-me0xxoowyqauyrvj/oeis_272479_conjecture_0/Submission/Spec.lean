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

namespace OEIS272479

def block1 (W : ℕ) : List ℕ := 1 :: List.replicate (W-1) 0
def block10 (W : ℕ) : List ℕ := 0 :: 1 :: List.replicate (W-2) 0

lemma flatten_modEq (m W : ℕ) (hW : (10:ℕ)^W ≡ 1 [MOD m]) :
    ∀ (blocks : List (List ℕ)), (∀ b ∈ blocks, b.length = W) →
    Nat.ofDigits 10 blocks.flatten ≡ (blocks.map (Nat.ofDigits 10)).sum [MOD m] := by
  intro blocks
  induction blocks with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro hlen
    have hb : b.length = W := hlen b (by simp)
    have hbs : ∀ c ∈ bs, c.length = W := fun c hc => hlen c (by simp [hc])
    simp only [List.flatten_cons, List.map_cons, List.sum_cons]
    rw [Nat.ofDigits_append, hb]
    calc Nat.ofDigits 10 b + 10 ^ W * Nat.ofDigits 10 bs.flatten
        ≡ Nat.ofDigits 10 b + 1 * Nat.ofDigits 10 bs.flatten [MOD m] :=
          Nat.ModEq.add_left _ (Nat.ModEq.mul_right _ hW)
      _ = Nat.ofDigits 10 b + Nat.ofDigits 10 bs.flatten := by ring
      _ ≡ Nat.ofDigits 10 b + (bs.map (Nat.ofDigits 10)).sum [MOD m] := Nat.ModEq.add_left _ (ih hbs)

lemma coprime_factor : ∀ s : ℕ, 1 ≤ s →
    ∃ γ : ℕ, 1 ≤ γ ∧ ∃ s' : ℕ, 1 ≤ s' ∧ Nat.Coprime s' 10 ∧ s ∣ 10^γ * s' ∧
      Nat.gcd 9 s' = Nat.gcd 9 s ∧ s' ∣ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs
    by_cases h2 : 2 ∣ s
    · obtain ⟨t, rfl⟩ := h2
      have ht : 1 ≤ t := by omega
      obtain ⟨γ, hγ, s', hs', hcop, hdvd, hgcd, hdvds⟩ := ih t (by omega) ht
      refine ⟨γ + 1, by omega, s', hs', hcop, ?_, ?_, hdvds.trans ⟨2, by ring⟩⟩
      · have h1 : 2 * t ∣ 2 * (10^γ * s') := Nat.mul_dvd_mul_left 2 hdvd
        have h2 : 2 * (10^γ * s') ∣ 10 * (10^γ * s') := Nat.mul_dvd_mul_right (by norm_num) _
        have he : (10:ℕ) * (10^γ * s') = 10^(γ+1) * s' := by ring
        rw [he] at h2; exact dvd_trans h1 h2
      · rw [hgcd, Nat.gcd_comm 9 (2*t), Nat.gcd_comm 9 t]
        exact ((show Nat.Coprime 2 9 by decide).gcd_mul_left_cancel t).symm
    · by_cases h5 : 5 ∣ s
      · obtain ⟨t, rfl⟩ := h5
        have ht : 1 ≤ t := by omega
        obtain ⟨γ, hγ, s', hs', hcop, hdvd, hgcd, hdvds⟩ := ih t (by omega) ht
        refine ⟨γ + 1, by omega, s', hs', hcop, ?_, ?_, hdvds.trans ⟨5, by ring⟩⟩
        · have h1 : 5 * t ∣ 5 * (10^γ * s') := Nat.mul_dvd_mul_left 5 hdvd
          have h2 : 5 * (10^γ * s') ∣ 10 * (10^γ * s') := Nat.mul_dvd_mul_right (by norm_num) _
          have he : (10:ℕ) * (10^γ * s') = 10^(γ+1) * s' := by ring
          rw [he] at h2; exact dvd_trans h1 h2
        · rw [hgcd, Nat.gcd_comm 9 (5*t), Nat.gcd_comm 9 t]
          exact ((show Nat.Coprime 5 9 by decide).gcd_mul_left_cancel t).symm
      · refine ⟨1, le_refl 1, s, hs, ?_, ?_, rfl, dvd_rfl⟩
        · have c2 : Nat.Coprime s 2 :=
            Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
          have c5 : Nat.Coprime s 5 :=
            Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5)
          have he : (10:ℕ) = 2 * 5 := by norm_num
          rw [he]; exact Nat.Coprime.mul_right c2 c5
        · exact dvd_mul_left s (10^1)

lemma solve_bcount (s' D : ℕ) (hs' : 1 ≤ s') (hdvd : Nat.gcd 9 s' ∣ D) :
    ∃ bcount : ℕ, bcount < s' ∧ s' ∣ (D + 9 * bcount) := by
  set g := Nat.gcd 9 s' with hg
  obtain ⟨q, hq⟩ := hdvd
  have hbez : (g : ℤ) = 9 * Nat.gcdA 9 s' + s' * Nat.gcdB 9 s' := Nat.gcd_eq_gcd_ab 9 s'
  set a := Nat.gcdA 9 s'
  set b := Nat.gcdB 9 s'
  set x0 : ℤ := -a * (q : ℤ) with hx0
  have hs'0 : (s':ℤ) ≠ 0 := by exact_mod_cast (by omega : s' ≠ 0)
  have hs'pos : (0:ℤ) < s' := by exact_mod_cast hs'
  have key : (s' : ℤ) ∣ ((D:ℤ) + 9 * x0) := by
    have heq : (D : ℤ) + 9 * x0 = (s' : ℤ) * (b * q) := by
      have hD : (D : ℤ) = (g : ℤ) * (q : ℤ) := by rw [hq]; push_cast; ring
      rw [hx0, hD, hbez]; ring
    rw [heq]; exact Dvd.intro _ rfl
  refine ⟨(x0 % (s':ℤ)).toNat, ?_, ?_⟩
  · have h1 : 0 ≤ x0 % (s':ℤ) := Int.emod_nonneg x0 hs'0
    have h2 : x0 % (s':ℤ) < s' := Int.emod_lt_of_pos x0 hs'pos
    omega
  · have hmod : ((x0 % (s':ℤ)).toNat : ℤ) = x0 % (s':ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg x0 hs'0)
    have hint : (s' : ℤ) ∣ ((D : ℤ) + 9 * ((x0 % (s':ℤ)).toNat : ℤ)) := by
      rw [hmod]
      have hsplit : (D:ℤ) + 9 * (x0 % (s':ℤ))
          = ((D:ℤ) + 9 * x0) - (s':ℤ) * (9 * (x0 / s')) := by
        rw [Int.emod_def]; ring
      rw [hsplit]; exact dvd_sub key (Dvd.intro _ rfl)
    have hcast : (s' : ℤ) ∣ (((D + 9 * (x0 % (s':ℤ)).toNat : ℕ)) : ℤ) := by
      push_cast; convert hint using 1
    exact_mod_cast hcast

lemma core (s D : ℕ) (hs : 1 ≤ s) (hD : 1 ≤ D) (hsD : s ≤ D) (hg : Nat.gcd 9 s ∣ D) :
    ∃ X, 10 ∣ X ∧ s ∣ X ∧ (Nat.digits 10 X).sum = D := by
  obtain ⟨γ, hγ, s', hs', hcop, hdvd2, hgcd, hs'dvds⟩ := coprime_factor s hs
  have hs'D : s' ≤ D := le_trans (Nat.le_of_dvd (by omega) hs'dvds) hsD
  set W := 2 * Nat.totient s' with hWdef
  have htpos : 1 ≤ Nat.totient s' := Nat.totient_pos.mpr (by omega)
  have hW2 : 2 ≤ W := by omega
  have h10W : (10:ℕ)^W ≡ 1 [MOD s'] := by
    have hcop10 : Nat.Coprime 10 s' := hcop.symm
    have hpt := Nat.ModEq.pow_totient hcop10
    calc (10:ℕ)^W = (10^(Nat.totient s'))^2 := by rw [hWdef, mul_comm, pow_mul]
      _ ≡ 1^2 [MOD s'] := hpt.pow 2
      _ = 1 := by ring
  have hg' : Nat.gcd 9 s' ∣ D := hgcd ▸ hg
  obtain ⟨bcount, hbc, hbcdvd⟩ := solve_bcount s' D hs' hg'
  have hbcD : bcount ≤ D := le_of_lt (lt_of_lt_of_le hbc hs'D)
  have hlen1 : (block1 W).length = W := by simp [block1]; omega
  have hlen10 : (block10 W).length = W := by simp [block10]; omega
  have hofd1 : Nat.ofDigits 10 (block1 W) = 1 := by
    simp [block1, Nat.ofDigits_cons, Nat.ofDigits_replicate_zero]
  have hofd10 : Nat.ofDigits 10 (block10 W) = 10 := by
    simp [block10, Nat.ofDigits_cons, Nat.ofDigits_replicate_zero]
  have hsum1 : (block1 W).sum = 1 := by simp [block1]
  have hsum10 : (block10 W).sum = 1 := by simp [block10]
  have hmem1 : ∀ x ∈ block1 W, x < 10 := by intro x hx; simp [block1, List.mem_replicate] at hx; omega
  have hmem10 : ∀ x ∈ block10 W, x < 10 := by intro x hx; simp [block10, List.mem_replicate] at hx; omega
  set blocks : List (List ℕ) := List.replicate bcount (block10 W) ++ List.replicate (D - bcount) (block1 W) with hblocks
  have hblen : ∀ b ∈ blocks, b.length = W := by
    intro b hb
    rw [hblocks, List.mem_append] at hb
    rcases hb with hb | hb
    · rw [List.eq_of_mem_replicate hb]; exact hlen10
    · rw [List.eq_of_mem_replicate hb]; exact hlen1
  set Lcore : List ℕ := blocks.flatten with hLcore
  have hmapsum : (blocks.map (Nat.ofDigits 10)).sum = D + 9 * bcount := by
    rw [hblocks, List.map_append, List.sum_append, List.map_replicate, List.map_replicate,
        List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul, hofd10, hofd1]
    have hh : bcount * 10 + (D - bcount) * 1 = D + 9 * bcount := by omega
    linarith [hh]
  have hLcore_mod : Nat.ofDigits 10 Lcore ≡ D + 9 * bcount [MOD s'] := by
    rw [hLcore]
    calc Nat.ofDigits 10 blocks.flatten ≡ (blocks.map (Nat.ofDigits 10)).sum [MOD s'] :=
          flatten_modEq s' W h10W blocks hblen
      _ = D + 9 * bcount := hmapsum
  have hs'dvdLcore : s' ∣ Nat.ofDigits 10 Lcore := by
    have hz : Nat.ofDigits 10 Lcore ≡ 0 [MOD s'] := by
      calc Nat.ofDigits 10 Lcore ≡ D + 9 * bcount [MOD s'] := hLcore_mod
        _ ≡ 0 [MOD s'] := (Nat.modEq_zero_iff_dvd).mpr hbcdvd
    exact (Nat.modEq_zero_iff_dvd).mp hz
  set L : List ℕ := List.replicate γ 0 ++ Lcore with hL
  set X : ℕ := Nat.ofDigits 10 L with hX
  have hXval : X = 10^γ * Nat.ofDigits 10 Lcore := by
    rw [hX, hL, Nat.ofDigits_append, Nat.ofDigits_replicate_zero, List.length_replicate]; ring
  refine ⟨X, ?_, ?_, ?_⟩
  · rw [hXval]; exact Dvd.dvd.mul_right (dvd_pow_self 10 (by omega)) _
  · rw [hXval]
    exact dvd_trans hdvd2 (Nat.mul_dvd_mul_left _ hs'dvdLcore)
  · have hmemL : ∀ x ∈ L, x < 10 := by
      intro x hx
      rw [hL, List.mem_append] at hx
      rcases hx with hx | hx
      · rw [List.eq_of_mem_replicate hx]; norm_num
      · rw [hLcore, List.mem_flatten] at hx
        obtain ⟨l, hl, hxl⟩ := hx
        rw [hblocks, List.mem_append] at hl
        rcases hl with hl | hl
        · rw [List.eq_of_mem_replicate hl] at hxl; exact hmem10 x hxl
        · rw [List.eq_of_mem_replicate hl] at hxl; exact hmem1 x hxl
    rw [hX]
    rw [Nat.sum_digits_ofDigits_eq_sum (by norm_num : 1 < 10)
        (show L ∈ {L : List ℕ | L.length = L.length ∧ ∀ x ∈ L, x < 10} from ⟨rfl, hmemL⟩)]
    rw [hL, List.sum_append, List.sum_replicate, smul_eq_mul, mul_zero, zero_add, hLcore,
        List.sum_flatten, hblocks, List.map_append, List.sum_append, List.map_replicate,
        List.map_replicate, List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul,
        hsum10, hsum1]
    omega

lemma digitsum_lt (m : ℕ) (h10 : 10 ∣ m) (hm : 1 ≤ m) : (Nat.digits 10 m).sum < m := by
  obtain ⟨k, rfl⟩ := h10
  have hk : 1 ≤ k := by omega
  have hdig : Nat.digits 10 (10 * k) = 0 :: Nat.digits 10 k := by
    rw [Nat.digits_def' (by norm_num : 2 ≤ 10) (by omega)]
    congr 1
    · omega
    · congr 1; omega
  rw [hdig]; simp only [List.sum_cons, zero_add]
  calc (Nat.digits 10 k).sum ≤ k := Nat.digit_sum_le 10 k
    _ < 10 * k := by omega

lemma digitsum_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ (Nat.digits 10 n).sum := by
  rcases Nat.eq_zero_or_pos (Nat.digits 10 n).sum with h | h
  · exfalso
    rw [List.sum_eq_zero_iff] at h
    have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have hlast := Nat.getLast_digit_ne_zero 10 (m := n) (by omega)
    exact hlast (h _ (List.getLast_mem hne))
  · exact h

lemma gcd9_digitsum (n : ℕ) : Nat.gcd 9 (Nat.digits 10 n).sum = Nat.gcd 9 n := by
  have h : n ≡ (Nat.digits 10 n).sum [MOD 9] := Nat.modEq_nine_digits_sum n
  rw [Nat.gcd_rec 9 n, Nat.gcd_rec 9 (Nat.digits 10 n).sum]
  congr 1
  exact h.symm

end OEIS272479

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  have hn1 : 1 ≤ n := hn
  have hs1 : 1 ≤ (Nat.digits 10 n).sum := OEIS272479.digitsum_pos n hn1
  have hsn : (Nat.digits 10 n).sum ≤ n := Nat.digit_sum_le 10 n
  have hgdvd : Nat.gcd 9 (Nat.digits 10 n).sum ∣ n := by
    rw [OEIS272479.gcd9_digitsum]; exact Nat.gcd_dvd_right 9 n
  obtain ⟨X, h10X, hsX, hXsum⟩ := OEIS272479.core (Nat.digits 10 n).sum n hs1 hn1 hsn hgdvd
  have hX0 : 0 < X := by
    rcases Nat.eq_zero_or_pos X with h | h
    · rw [h] at hXsum; simp at hXsum; omega
    · exact h
  have hXn : X ≠ n := by
    intro hXeq
    rw [hXeq] at h10X hXsum
    have := OEIS272479.digitsum_lt n h10X hn1
    omega
  have hdvd2 : (Nat.digits 10 X).sum ∣ n := by rw [hXsum]
  have hmem : X ∈ {k | k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n} :=
    ⟨hX0, hXn, hsX, hdvd2⟩
  have hne : ({k | k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n} : Set ℕ).Nonempty :=
    ⟨X, hmem⟩
  unfold a
  simp only [hne, dif_pos]
  have hmemInf := Nat.sInf_mem hne
  have hpos : sInf {k | k > 0 ∧ k ≠ n ∧ (Nat.digits 10 n).sum ∣ k ∧ (Nat.digits 10 k).sum ∣ n} > 0 :=
    hmemInf.1
  omega
