import Submission.RothLocal
import Submission.PrimeSieve

/-!
# Squarefree integers in quarter-scale intervals

This file proves that, for all sufficiently large natural interval lengths `H`,
every interval `(x, x + H]` with `x ≤ H^4` contains a squarefree integer.
It combines the finite prime-square sieve with local rigidity in geometrically
increasing bands. All counting and all tail estimates use natural numbers.

This is a quarter-exponent partial result, not an all-positive-exponents bound.
-/

open Finset

namespace QuarterInterval

/-- The fixed cutoff multiplier used in the preliminary prime sieve. -/
def cutoff : ℕ := 2 ^ 33

/-- Bases in a closed interval whose square multiples hit `(x, x + H]`. -/
noncomputable def squareBases (x H L U : ℕ) : Finset ℕ := by
  classical
  exact (Icc L U).filter (fun d => ∃ m : ℕ, x < m * d ^ 2 ∧ m * d ^ 2 ≤ x + H)

/-- Partitioning a band into quotient fibers transfers the local two-base bound
into a bound for the whole band. -/
theorem card_squareBases_band_le (x H N B : ℕ)
    (hN : 0 < N) (hH : 64 * H ≤ N) (hB0 : 0 < B) (hB : B ≤ N)
    (hsmall : 16 * (x + H) * B ^ 3 < N ^ 4) :
    (squareBases x H N (16 * N)).card ≤ 2 * (15 * N / B + 1) := by
  classical
  have hmap : ∀ d ∈ squareBases x H N (16 * N),
      (d - N) / B ∈ range (15 * N / B + 1) := by
    intro d hd
    have hdI := mem_Icc.mp (mem_filter.mp hd).1
    have hsub : d - N ≤ 15 * N := by omega
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hsub))
  have hfiber : ∀ q ∈ range (15 * N / B + 1),
      ((squareBases x H N (16 * N)).filter (fun d => (d - N) / B = q)).card ≤ 2 := by
    intro q _
    have hNN : N ≤ N + q * B := Nat.le_add_right _ _
    apply le_trans (card_le_card (t := squareBases x H (N + q * B) (N + q * B + B)) ?_)
      (RothLocal.square_multiples_card_le_two x H (N + q * B) B
        (hN.trans_le hNN) (hH.trans hNN) (hB.trans hNN)
        (hsmall.trans_le (Nat.pow_le_pow_left hNN 4)))
    intro d hd
    obtain ⟨hd, hq⟩ := mem_filter.mp hd
    obtain ⟨hdI, hm⟩ := mem_filter.mp hd
    have hdN := (mem_Icc.mp hdI).1
    have hmod := Nat.mod_lt (d - N) hB0
    have heq := Nat.mod_add_div (d - N) B
    rw [hq, Nat.mul_comm B q] at heq
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hm⟩
  simpa only [card_range] using card_le_mul_card_image_of_maps_to hmap 2 hfiber

/-- Every base of a square multiple hitting a quarter-scale interval is at most
`2 * H^2`. -/
theorem square_base_le (x H d : ℕ) (hx : x ≤ H ^ 4)
    (hd : ∃ m : ℕ, x < m * d ^ 2 ∧ m * d ^ 2 ≤ x + H) : d ≤ 2 * H ^ 2 := by
  obtain ⟨m, hmlo, hmhi⟩ := hd
  have hm : 0 < m := by
    by_contra h
    have : m = 0 := by omega
    simp [this] at hmlo
  have hH4 : H ≤ H ^ 4 := Nat.le_self_pow (by decide) H
  have hdsq : d ^ 2 ≤ 2 * H ^ 4 :=
    (Nat.le_mul_of_pos_left (d ^ 2) hm).trans (hmhi.trans (by omega))
  apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
  calc
    d ^ 2 ≤ 2 * H ^ 4 := hdsq
    _ ≤ (2 * H ^ 2) ^ 2 := by nlinarith

private def bandStart (H j : ℕ) : ℕ := cutoff * H * 16 ^ j

private def blockWidth (j : ℕ) : ℕ := 2 ^ 42 * 32 ^ j

private lemma cutoff_pos : 0 < cutoff := by norm_num [cutoff]

private lemma blockWidth_pos (j : ℕ) : 0 < blockWidth j := by
  unfold blockWidth
  positivity

private lemma blockWidth_factor (j : ℕ) :
    blockWidth j = (cutoff * 16 ^ j) * (512 * 2 ^ j) := by
  unfold blockWidth
  rw [show (32 : ℕ) = 16 * 2 from rfl, mul_pow]
  norm_num [cutoff]
  ring

private lemma band_quotient (H j : ℕ) :
    15 * bandStart H j / blockWidth j = (15 * H / 512) / 2 ^ j := by
  rw [bandStart, blockWidth_factor]
  have heq : 15 * (cutoff * H * 16 ^ j) = (cutoff * 16 ^ j) * (15 * H) := by ring
  rw [heq, Nat.mul_div_mul_left _ _ (Nat.mul_pos cutoff_pos (by positivity))]
  exact (Nat.div_div_eq_div_mul (15 * H) 512 (2 ^ j)).symm

private lemma bandStart_pos (H j : ℕ) (hH : 0 < H) : 0 < bandStart H j := by
  unfold bandStart
  exact Nat.mul_pos (Nat.mul_pos cutoff_pos hH) (by positivity)

private lemma bandStart_large (H j : ℕ) : 64 * H ≤ bandStart H j := by
  calc
    64 * H ≤ cutoff * H := Nat.mul_le_mul_right H (by norm_num [cutoff])
    _ ≤ cutoff * H * 16 ^ j := Nat.le_mul_of_pos_right _ (by positivity)

private lemma blockWidth_le_bandStart (H j : ℕ) (hH : 0 < H)
    (hj : bandStart H j ≤ 2 * H ^ 2) : blockWidth j ≤ bandStart H j := by
  have hj' : cutoff * 16 ^ j ≤ 2 * H := by
    apply Nat.le_of_mul_le_mul_right (c := H) _ hH
    calc
      cutoff * 16 ^ j * H = bandStart H j := by unfold bandStart; ring
      _ ≤ 2 * H ^ 2 := hj
      _ = 2 * H * H := by ring
  have hp : 2 ^ j ≤ (16 : ℕ) ^ j := Nat.pow_le_pow_left (by decide) j
  have hscaled : 1024 * 2 ^ j ≤ 2 * H := by
    calc
      1024 * 2 ^ j ≤ cutoff * 16 ^ j :=
        Nat.mul_le_mul (by norm_num [cutoff]) hp
      _ ≤ 2 * H := hj'
  have hhalf : 512 * 2 ^ j ≤ H := by omega
  rw [blockWidth_factor]
  calc
    (cutoff * 16 ^ j) * (512 * 2 ^ j) ≤ (cutoff * 16 ^ j) * H :=
      Nat.mul_le_mul_left _ hhalf
    _ = bandStart H j := by unfold bandStart; ring

private lemma band_smallness (x H j : ℕ) (hH : 0 < H) (hx : x ≤ H ^ 4) :
    16 * (x + H) * blockWidth j ^ 3 < bandStart H j ^ 4 := by
  have htop : x + H ≤ 2 * H ^ 4 := by
    have := Nat.le_self_pow (by decide : 4 ≠ 0) H
    omega
  have hp : ((32 : ℕ) ^ j) ^ 3 ≤ ((16 : ℕ) ^ j) ^ 4 := by
    calc
      (32 ^ j) ^ 3 = (32 ^ 3) ^ j := by rw [← pow_mul, ← pow_mul, Nat.mul_comm j 3]
      _ ≤ (16 ^ 4) ^ j := Nat.pow_le_pow_left (by norm_num) j
      _ = (16 ^ j) ^ 4 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 4 j]
  have hc : 32 * ((2 : ℕ) ^ 42) ^ 3 < cutoff ^ 4 := by norm_num [cutoff]
  unfold blockWidth bandStart
  calc
    16 * (x + H) * (2 ^ 42 * 32 ^ j) ^ 3 ≤
        16 * (2 * H ^ 4) * (2 ^ 42 * 32 ^ j) ^ 3 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16 htop)
    _ = (32 * (2 ^ 42) ^ 3) * (H ^ 4 * (32 ^ j) ^ 3) := by ring
    _ ≤ (32 * (2 ^ 42) ^ 3) * (H ^ 4 * (16 ^ j) ^ 4) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp)
    _ < cutoff ^ 4 * (H ^ 4 * (16 ^ j) ^ 4) :=
      Nat.mul_lt_mul_of_pos_right hc (by positivity)
    _ = (cutoff * H * 16 ^ j) ^ 4 := by ring

private noncomputable def bandBases (x H j : ℕ) : Finset ℕ :=
  squareBases x H (bandStart H j) (16 * bandStart H j)

private lemma card_bandBases_le (x H j : ℕ) (hH : 0 < H) (hx : x ≤ H ^ 4) :
    (bandBases x H j).card ≤ 2 * ((15 * H / 512) / 2 ^ j + 1) := by
  classical
  by_cases hne : (bandBases x H j).Nonempty
  · obtain ⟨d, hd⟩ := hne
    obtain ⟨hdI, hm⟩ := mem_filter.mp hd
    have hj : bandStart H j ≤ 2 * H ^ 2 :=
      (mem_Icc.mp hdI).1.trans (square_base_le x H d hx hm)
    have hc := card_squareBases_band_le x H (bandStart H j) (blockWidth j)
      (bandStart_pos H j hH) (bandStart_large H j) (blockWidth_pos j)
      (blockWidth_le_bandStart H j hH hj) (band_smallness x H j hH hx)
    simpa only [bandBases, band_quotient] using hc
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty]
    exact Nat.zero_le _

private lemma geometric_cover (M d J : ℕ) (hlo : M ≤ d) (hhi : d < M * 16 ^ J) :
    ∃ j < J, M * 16 ^ j ≤ d ∧ d ≤ 16 * (M * 16 ^ j) := by
  induction J generalizing d with
  | zero =>
    simp only [pow_zero, mul_one] at hhi
    omega
  | succ J ih =>
    by_cases h : d < M * 16 ^ J
    · obtain ⟨j, hj, hdlo, hdhi⟩ := ih d hlo h
      exact ⟨j, by omega, hdlo, hdhi⟩
    · refine ⟨J, Nat.lt_succ_self J, Nat.le_of_not_gt h, ?_⟩
      have heq : M * 16 ^ (J + 1) = 16 * (M * 16 ^ J) := by rw [pow_succ]; ring
      rw [heq] at hhi
      exact hhi.le

private lemma pow_sixteen_large (J : ℕ) (hJ : 3 ≤ J) : 128 * (J + 1) ≤ 16 ^ J := by
  induction J, hJ using Nat.le_induction with
  | base => norm_num
  | succ J _ ih =>
    rw [pow_succ]
    omega

private lemma bandStart_terminal (H : ℕ) (hH : 192 ≤ H) :
    2 * H ^ 2 < bandStart H (H / 64) := by
  have hp := pow_sixteen_large (H / 64) (by omega)
  have hdiv := Nat.lt_mul_div_succ H (by decide : 0 < 64)
  have hpow : 2 * H < 16 ^ (H / 64) := by omega
  calc
    2 * H ^ 2 = H * (2 * H) := by ring
    _ < H * 16 ^ (H / 64) := Nat.mul_lt_mul_of_pos_left hpow (by omega)
    _ ≤ cutoff * (H * 16 ^ (H / 64)) := Nat.le_mul_of_pos_left _ cutoff_pos
    _ = bandStart H (H / 64) := by unfold bandStart; ring

/-- All relevant bases at or above the sieve cutoff. The endpoint is included;
this harmless overlap makes the geometric covering exact. -/
noncomputable def largeBases (x H : ℕ) : Finset ℕ :=
  squareBases x H (cutoff * H) (2 * H ^ 2)

/-- The integer geometric-series estimate for the number of large bases. -/
theorem card_largeBases_le (x H : ℕ) (hH : 192 ≤ H) (hx : x ≤ H ^ 4) :
    128 * (largeBases x H).card ≤ 19 * H := by
  classical
  have hsub : largeBases x H ⊆ (range (H / 64)).biUnion (bandBases x H) := by
    intro d hd
    obtain ⟨hdI, hm⟩ := mem_filter.mp hd
    obtain ⟨j, hj, hdlo, hdhi⟩ := geometric_cover (cutoff * H) d (H / 64)
      (mem_Icc.mp hdI).1 ((mem_Icc.mp hdI).2.trans_lt (bandStart_terminal H hH))
    exact mem_biUnion.mpr ⟨j, mem_range.mpr hj,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hdlo, hdhi⟩, hm⟩⟩
  have hcount : (largeBases x H).card ≤ 2 * (2 * (15 * H / 512) + H / 64) := by
    calc
      (largeBases x H).card ≤ ((range (H / 64)).biUnion (bandBases x H)).card :=
        card_le_card hsub
      _ ≤ ∑ j ∈ range (H / 64), (bandBases x H j).card := card_biUnion_le
      _ ≤ ∑ j ∈ range (H / 64), 2 * ((15 * H / 512) / 2 ^ j + 1) :=
        sum_le_sum (fun j _ => card_bandBases_le x H j (by omega) hx)
      _ = 2 * ((∑ j ∈ range (H / 64), (15 * H / 512) / 2 ^ j) + H / 64) := by
        rw [← mul_sum, sum_add_distrib]
        simp
      _ ≤ 2 * (2 * (15 * H / 512) + H / 64) := by
        have hg := Nat.geom_sum_le (b := 2) (by decide) (15 * H / 512) (H / 64)
        norm_num at hg
        omega
  have hq := Nat.mul_div_le (15 * H) 512
  have hj := Nat.mul_div_le H 64
  omega

/-- The union of square multiples attached to the large relevant bases. -/
noncomputable def largeSquareBad (x H : ℕ) : Finset ℕ := by
  classical
  exact (largeBases x H).biUnion
    (fun d => (Ioc x (x + H)).filter (fun n => d ^ 2 ∣ n))

/-- Each large base contributes at most one integer to the interval. -/
theorem card_largeSquareBad_le_card_bases (x H : ℕ) (hH : 0 < H) :
    (largeSquareBad x H).card ≤ (largeBases x H).card := by
  classical
  have hc := card_biUnion_le_card_mul (largeBases x H)
    (fun d => (Ioc x (x + H)).filter (fun n => d ^ 2 ∣ n)) 1 (by
      intro d hd
      have hdlo := (mem_Icc.mp (mem_filter.mp hd).1).1
      have hcut : 2 * H ≤ cutoff * H :=
        Nat.mul_le_mul_right H (by norm_num [cutoff])
      have hd2 : H < d ^ 2 :=
        (show H < d by omega).trans_le (Nat.le_self_pow (by decide) d)
      have hdcard := ElementarySquarefree.card_multiples_Ioc_le x H (d ^ 2)
      rw [Nat.div_eq_of_lt hd2] at hdcard
      exact hdcard)
  simpa only [largeSquareBad, mul_one] using hc

/-- Large square divisors remove at most `19 * H / 128` interval members. -/
theorem card_largeSquareBad_le (x H : ℕ) (hH : 192 ≤ H) (hx : x ≤ H ^ 4) :
    128 * (largeSquareBad x H).card ≤ 19 * H :=
  (Nat.mul_le_mul_left 128 (card_largeSquareBad_le_card_bases x H (by omega))).trans
    (card_largeBases_le x H hH hx)

/-- Every nonsquarefree interval member is removed by either the small-prime
sieve or the large-square tail. -/
theorem nonsquarefree_mem_union (x H n : ℕ) (hx : x ≤ H ^ 4)
    (hn : n ∈ Ioc x (x + H)) (hns : ¬ Squarefree n) :
    n ∈ PrimeSieve.primeSquareBad x H (cutoff * H) ∪ largeSquareBad x H := by
  classical
  rw [Nat.squarefree_iff_prime_squarefree] at hns
  push_neg at hns
  obtain ⟨p, hp, hpdvd⟩ := hns
  have hpsq : p ^ 2 ∣ n := by simpa only [pow_two] using hpdvd
  by_cases hpc : p ≤ cutoff * H
  · apply mem_union_left
    exact (PrimeSieve.mem_primeSquareBad x H (cutoff * H) n).mpr
      ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2, p, hp, hpc, hpsq⟩
  · obtain ⟨m, hnm⟩ := hpsq
    have hmn : m * p ^ 2 = n := by simpa only [mul_comm] using hnm.symm
    have hhit : ∃ m : ℕ, x < m * p ^ 2 ∧ m * p ^ 2 ≤ x + H :=
      ⟨m, by simpa only [hmn] using mem_Ioc.mp hn⟩
    have hpB : p ∈ largeBases x H :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, square_base_le x H p hx hhit⟩, hhit⟩
    apply mem_union_right
    exact mem_biUnion.mpr ⟨p, hpB, mem_filter.mpr ⟨hn, ⟨m, hnm⟩⟩⟩

open Classical in
/-- The two sieves together remove at most `123 * H / 128` members. -/
theorem card_nonsquarefree_le (x H : ℕ) (hH : 192 ≤ H) (hx : x ≤ H ^ 4)
    (hsieve : 16 * (PrimeSieve.primeSquareBad x H (cutoff * H)).card ≤ 13 * H) :
    128 * ((Ioc x (x + H)).filter (fun n => ¬ Squarefree n)).card ≤ 123 * H := by
  have hcard : ((Ioc x (x + H)).filter (fun n => ¬ Squarefree n)).card ≤
      (PrimeSieve.primeSquareBad x H (cutoff * H)).card + (largeSquareBad x H).card := by
    calc
      _ ≤ (PrimeSieve.primeSquareBad x H (cutoff * H) ∪ largeSquareBad x H).card := by
        apply card_le_card
        intro n hn
        exact nonsquarefree_mem_union x H n hx (mem_filter.mp hn).1 (mem_filter.mp hn).2
      _ ≤ _ := card_union_le _ _
  have htail := card_largeSquareBad_le x H hH hx
  omega

/-- The finite quarter-scale interval conclusion whenever the uniform sieve
estimate is available. -/
theorem exists_squarefree_of_sieve_bound (x H : ℕ) (hH : 192 ≤ H) (hx : x ≤ H ^ 4)
    (hsieve : 16 * (PrimeSieve.primeSquareBad x H (cutoff * H)).card ≤ 13 * H) :
    ∃ n : ℕ, x < n ∧ n ≤ x + H ∧ Squarefree n := by
  classical
  by_contra he
  have hall : (Ioc x (x + H)).filter (fun n => ¬ Squarefree n) = Ioc x (x + H) := by
    apply filter_eq_self.mpr
    intro n hn hsq
    exact he ⟨n, (mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2, hsq⟩
  have hc := card_nonsquarefree_le x H hH hx hsieve
  rw [hall, Nat.card_Ioc, Nat.add_sub_cancel_left] at hc
  omega

/-- Every sufficiently long interval `(x, x + H]` with `x ≤ H^4` contains a
squarefree natural number. The threshold is uniform in `x`.

This is only the quarter-exponent partial result. -/
theorem exists_squarefree_in_quarter_interval :
    ∃ H₀ : ℕ, ∀ H ≥ H₀, ∀ x : ℕ, x ≤ H ^ 4 →
      ∃ n : ℕ, x < n ∧ n ≤ x + H ∧ Squarefree n := by
  obtain ⟨H₀, hH₀⟩ := PrimeSieve.exists_uniform_threshold cutoff
  refine ⟨max 192 H₀, ?_⟩
  intro H hH x hx
  exact exists_squarefree_of_sieve_bound x H ((le_max_left 192 H₀).trans hH) hx
    (hH₀ H ((le_max_right 192 H₀).trans hH) x)

end QuarterInterval
