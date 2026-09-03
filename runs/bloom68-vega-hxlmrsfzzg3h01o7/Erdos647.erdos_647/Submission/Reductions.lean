import FormalConjecturesUtil

/-!
# Development reductions for Erdős problem 647

This file does not import or change `Submission/Spec.lean`.  It works with the
actual divisor-count condition `P`, and does not assume either the proposed
existence statement or its negation.

The main device is elementary: if `d ∣ m` and `d * d < m`, the divisors of `d`
and their complementary divisors in `m` are disjoint.  Thus
`2 * τ(d) ≤ τ(m)`.  This excludes residue classes of a putative solution.
All small exceptions below are checked using explicit finite sets of divisors,
not an external search or a native decision procedure.
-/

namespace Erdos647

open scoped ArithmeticFunction.sigma

/-- The pointwise form of the condition in Erdős problem 647. -/
def P (n : ℕ) : Prop := ∀ m < n, m + σ 0 m ≤ n + 2

/-- For positive `n`, `P n` is exactly the original finite natural-number
supremum bound (including the value at `m = 0`). -/
theorem p_iff_fin_iSup_bound {n : ℕ} (hn : 0 < n) :
    P n ↔ (⨆ m : Fin n, (m : ℕ) + σ 0 (m : ℕ)) ≤ n + 2 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  constructor
  · intro h
    exact ciSup_le fun m => h m m.isLt
  · intro h m hm
    exact (Finite.le_ciSup (fun i : Fin n => (i : ℕ) + σ 0 (i : ℕ)) ⟨m, hm⟩).trans h

/-- Each positive offset gives a small upper bound on the divisor count. -/
theorem P.offset_bound {n : ℕ} (h : P n) {j : ℕ}
    (hj : 0 < j) (hjn : j ≤ n) : σ 0 (n - j) ≤ j + 2 := by
  have hb := h (n - j) (by omega)
  omega

/-- Divisor counts are monotone under divisibility of a nonzero number. -/
theorem sigma_zero_le_of_dvd {d m : ℕ} (hm : m ≠ 0) (hd : d ∣ m) :
    σ 0 d ≤ σ 0 m := by
  simp only [ArithmeticFunction.sigma_zero_apply]
  exact Finset.card_le_card (Nat.divisors_subset_of_dvd hm hd)

/-- The divisors of `d` and their complements in `m` give twice as many
distinct divisors of `m` when `d * d < m`. -/
theorem two_mul_card_divisors_le {d m : ℕ} (hd : d ∣ m) (hm : d * d < m) :
    2 * d.divisors.card ≤ m.divisors.card := by
  have hm0 : m ≠ 0 := by omega
  have hs : d.divisors ⊆ m.divisors := Nat.divisors_subset_of_dvd hm0 hd
  have hi : Set.InjOn (fun x : ℕ => m / x) (↑d.divisors : Set ℕ) := by
    intro x hx y hy hxy
    exact (Nat.div_eq_iff_eq_of_dvd_dvd hm0
      ((Nat.dvd_of_mem_divisors hx).trans hd)
      ((Nat.dvd_of_mem_divisors hy).trans hd)).mp hxy
  have ht : d.divisors.image (fun x => m / x) ⊆ m.divisors := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd ((Nat.dvd_of_mem_divisors hy).trans hd), hm0⟩
  have hdis : Disjoint d.divisors (d.divisors.image (fun x => m / x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxi
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxi
    have hprod : x * y = m := by
      rw [← hxy]
      exact Nat.div_mul_cancel ((Nat.dvd_of_mem_divisors hy).trans hd)
    have hle := Nat.mul_le_mul (Nat.divisor_le hx) (Nat.divisor_le hy)
    omega
  have hc := Finset.card_le_card (Finset.union_subset hs ht)
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hi] at hc
  omega

/-- The same complementary-divisor estimate stated using `σ 0`. -/
theorem two_mul_sigma_zero_le {d m : ℕ} (hd : d ∣ m) (hm : d * d < m) :
    2 * σ 0 d ≤ σ 0 m := by
  simpa only [ArithmeticFunction.sigma_zero_apply] using two_mul_card_divisors_le hd hm

/-- A fixed divisor with sufficiently many divisors cannot divide `n - j`,
unless `n` lies below the explicit cutoff `d * d + j`. -/
theorem P.not_dvd_sub {n : ℕ} (h : P n) (j d : ℕ) (hj : 0 < j)
    (hc : j + 2 < 2 * d.divisors.card) (hn : d * d + j < n) :
    ¬ d ∣ n - j := by
  intro hd
  have hb := h.offset_bound hj (by omega)
  rw [ArithmeticFunction.sigma_zero_apply] at hb
  have hl := two_mul_card_divisors_le hd (by omega : d * d < n - j)
  omega

/-- A convenient residue-class version of `P.not_dvd_sub`. -/
theorem P.mod_ne_of_dvd {n : ℕ} (h : P n) (j p : ℕ) (hj : 0 < j)
    (hjn : j ∣ n) (hcop : j.Coprime p)
    (hc : j + 2 < 2 * (j * p).divisors.card)
    (hn : (j * p) * (j * p) + j < n) : n % p ≠ j % p := by
  intro heq
  apply h.not_dvd_sub j (j * p) hj hc hn
  apply hcop.mul_dvd_of_dvd_of_dvd
  · exact Nat.dvd_sub hjn (dvd_refl j)
  · exact (Nat.modEq_iff_dvd' (by omega : j ≤ n)).mp heq.symm

/-- A finite collection of offsets covering every nonzero residue modulo `p`
forces `p ∣ n`. The hypotheses on the offsets are finite, numerical certificates. -/
theorem P.dvd_of_residue_cover {n L p B : ℕ} (h : P n) (hL : L ∣ n)
    (hB : B < n) (hp : 0 < p) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 0 < j ∧ j ∣ L ∧ j.Coprime p ∧
      j + 2 < 2 * (j * p).divisors.card ∧ (j * p) * (j * p) + j ≤ B)
    (hcover : ∀ r ∈ Finset.Ico 1 p, ∃ j ∈ J, j % p = r) : p ∣ n := by
  by_contra hnot
  have hr : n % p ∈ Finset.Ico 1 p := by
    have hpos : n % p ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hnot
    exact Finset.mem_Ico.mpr ⟨by omega, Nat.mod_lt n hp⟩
  obtain ⟨j, hj, heq⟩ := hcover (n % p) hr
  obtain ⟨hj0, hjL, hcop, hcount, hsize⟩ := hJ j hj
  exact h.mod_ne_of_dvd j p hj0 (hjL.trans hL) hcop hcount
    (lt_of_le_of_lt hsize hB) heq.symm

/-- A short explicit divisor list is a certificate that `P n` fails.
Only finite membership, divisibility and cardinality need to be computed. -/
theorem not_P_of_divisor_certificate {n j : ℕ} {s : Finset ℕ}
    (hc : 0 < j ∧ j < n ∧ j + 2 < s.card ∧ ∀ d ∈ s, d ∣ n - j) : ¬ P n := by
  intro h
  have hb := h.offset_bound hc.1 hc.2.1.le
  rw [ArithmeticFunction.sigma_zero_apply] at hb
  have hs : s ⊆ (n - j).divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨hc.2.2.2 d hd, by omega⟩
  have hl := Finset.card_le_card hs
  omega

/-- A putative solution above 24 is even. -/
theorem P.dvd_two {n : ℕ} (h : P n) (hn : 24 < n) : 2 ∣ n := by
  have he := h.not_dvd_sub 1 2 (by decide) (by decide) (by omega)
  simp only [Nat.dvd_iff_mod_eq_zero] at he ⊢
  omega

/-- In fact a putative solution above 24 is divisible by four. -/
theorem P.dvd_four {n : ℕ} (h : P n) (hn : 24 < n) : 4 ∣ n := by
  have h2 := h.dvd_two hn
  have he := h.not_dvd_sub 2 4 (by decide) (by decide) (by omega)
  simp only [Nat.dvd_iff_mod_eq_zero] at h2 he ⊢
  omega

/- ## Divisibility by 24 -/

private theorem not_P_four_mul_small {k : ℕ} (hlo : 7 ≤ k) (hhi : k ≤ 17) :
    ¬ P (4 * k) := by
  interval_cases k
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 3, 9, 27}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 3, 5, 6}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 5, 7, 35}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 3, 13, 39}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 3, 6, 7}) (by decide)
  · exact not_P_of_divisor_certificate (j := 3) (s := {1, 3, 5, 9, 15, 45}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 3, 17, 51}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 5, 11, 55}) (by decide)
  · exact not_P_of_divisor_certificate (j := 4) (s := {1, 2, 4, 7, 8, 14, 28}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 3, 7, 9}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 3, 6, 11}) (by decide)

/-- The finitely many multiples of four between 24 and 68 all fail `P`. -/
theorem P.gt_68 {n : ℕ} (h : P n) (hn : 24 < n) : 68 < n := by
  by_contra hsmall
  obtain ⟨k, rfl⟩ := h.dvd_four hn
  exact not_P_four_mul_small (by omega) (by omega) h

/-- The offset four bound, with its small exceptions removed, forces `8 ∣ n`. -/
theorem P.dvd_eight {n : ℕ} (h : P n) (hn : 24 < n) : 8 ∣ n := by
  have h4 := h.dvd_four hn
  have hlarge := h.gt_68 hn
  have he := h.not_dvd_sub 4 8 (by decide) (by decide) (by omega)
  simp only [Nat.dvd_iff_mod_eq_zero] at h4 he ⊢
  omega

/-- The actual Erdős 647 condition necessarily implies `24 ∣ n` above 24. -/
theorem P.dvd_24 {n : ℕ} (h : P n) (hn : 24 < n) : 24 ∣ n := by
  have h8 := h.dvd_eight hn
  have hlarge := h.gt_68 hn
  have h3 : 3 ∣ n := h.dvd_of_residue_cover (L := 8) (B := 38) h8
    (by omega) (by decide) {1, 2} (by decide) (by decide)
  exact (by decide : Nat.Coprime 8 3).mul_dvd_of_dvd_of_dvd h8 h3

/- ## Divisibility by 360 -/

private theorem not_P_twentyfour_mul_small {k : ℕ} (hlo : 2 ≤ k) (hhi : k ≤ 16) :
    ¬ P (24 * k) := by
  interval_cases k
  · exact not_P_of_divisor_certificate (j := 3) (s := {1, 3, 5, 9, 15, 45}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 5, 7, 10}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 5, 19, 95}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 7, 17, 119}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 11, 13, 143}) (by decide)
  · exact not_P_of_divisor_certificate (j := 3) (s := {1, 3, 5, 11, 15, 33}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 5, 10, 19}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 5, 43, 215}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 7, 14, 17}) (by decide)
  · exact not_P_of_divisor_certificate (j := 3) (s := {1, 3, 9, 29, 87, 261}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 7, 41, 287}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 5, 10, 31}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 5, 67, 335}) (by decide)
  · exact not_P_of_divisor_certificate (j := 3) (s := {1, 3, 7, 17, 21, 51}) (by decide)
  · exact not_P_of_divisor_certificate (j := 4) (s := {1, 2, 4, 5, 10, 19, 20}) (by decide)

/-- Explicit divisor certificates eliminate the multiples of 24 up to 404. -/
theorem P.gt_404 {n : ℕ} (h : P n) (hn : 24 < n) : 404 < n := by
  by_contra hsmall
  obtain ⟨k, rfl⟩ := h.dvd_24 hn
  exact not_P_twentyfour_mul_small (by omega) (by omega) h

/-- Offsets three and six force one more factor of three. -/
theorem P.dvd_72 {n : ℕ} (h : P n) (hn : 24 < n) : 72 ∣ n := by
  have h24 := h.dvd_24 hn
  have hlarge := h.gt_404 hn
  have h9 := h.not_dvd_sub 3 9 (by decide) (by decide) (by omega)
  have h18 := h.not_dvd_sub 6 18 (by decide) (by decide) (by omega)
  have h3 : 3 ∣ n := (by decide : 3 ∣ 24).trans h24
  have h2 : 2 ∣ n := (by decide : 2 ∣ 24).trans h24
  have hm3 : n % 9 ≠ 3 := by
    intro hr
    apply h9
    exact (Nat.modEq_iff_dvd' (by omega : 3 ≤ n)).mp hr.symm
  have hm6 : n % 9 ≠ 6 := by
    intro hr
    apply h18
    exact (by decide : Nat.Coprime 2 9).mul_dvd_of_dvd_of_dvd
      (Nat.dvd_sub h2 (by decide : 2 ∣ 6))
      ((Nat.modEq_iff_dvd' (by omega : 6 ≤ n)).mp hr.symm)
  have hd9 : 9 ∣ n := by
    have hb := Nat.mod_lt n (by decide : 0 < 9)
    have hm := Nat.mod_mod_of_dvd n (by decide : 3 ∣ 9)
    rw [Nat.dvd_iff_mod_eq_zero] at h3 ⊢
    interval_cases hr : n % 9 <;> omega
  exact (by decide : Nat.Coprime 8 9).mul_dvd_of_dvd_of_dvd
    ((by decide : 8 ∣ 24).trans h24) hd9

/-- Offsets one through four cover all nonzero residues modulo five. -/
theorem P.dvd_360 {n : ℕ} (h : P n) (hn : 24 < n) : 360 ∣ n := by
  have h72 := h.dvd_72 hn
  have h5 : 5 ∣ n := h.dvd_of_residue_cover (L := 72) (B := 404) h72
    (h.gt_404 hn) (by decide) {1, 2, 3, 4} (by decide) (by decide)
  exact (by decide : Nat.Coprime 72 5).mul_dvd_of_dvd_of_dvd h72 h5

/- ## Divisibility by 2520 -/

private theorem not_P_360_mul_small {k : ℕ} (hlo : 1 ≤ k) (hhi : k ≤ 4) :
    ¬ P (360 * k) := by
  interval_cases k
  · exact not_P_of_divisor_certificate (j := 3) (s := {1, 3, 7, 17, 21, 51}) (by decide)
  · exact not_P_of_divisor_certificate (j := 5) (s := {1, 5, 11, 13, 55, 65, 143, 715}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 13, 83, 1079}) (by decide)
  · exact not_P_of_divisor_certificate (j := 5) (s := {1, 5, 7, 35, 41, 205, 287, 1435}) (by decide)

/-- The four positive multiples of 360 below 1771 all fail `P`. -/
theorem P.gt_1770 {n : ℕ} (h : P n) (hn : 24 < n) : 1770 < n := by
  by_contra hsmall
  obtain ⟨k, rfl⟩ := h.dvd_360 hn
  exact not_P_360_mul_small (by omega) (by omega) h

/-- Once `360 ∣ n`, offsets one through six cover the nonzero residues modulo seven. -/
theorem P.dvd_2520 {n : ℕ} (h : P n) (hn : 24 < n) : 2520 ∣ n := by
  have h360 := h.dvd_360 hn
  have h7 : 7 ∣ n := h.dvd_of_residue_cover (L := 360) (B := 1770) h360
    (h.gt_1770 hn) (by decide) {1, 2, 3, 4, 5, 6} (by decide) (by decide)
  exact (by decide : Nat.Coprime 360 7).mul_dvd_of_dvd_of_dvd h360 h7

/- ## The factors eleven and thirteen -/

private theorem not_P_2520_mul_small {k : ℕ} (hlo : 1 ≤ k) (hhi : k ≤ 15) :
    ¬ P (2520 * k) := by
  interval_cases k
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 11, 229, 2519}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 11, 22, 229}) (by decide)
  · exact not_P_of_divisor_certificate (j := 3) (s := {1, 3, 11, 33, 229, 687}) (by decide)
  · exact not_P_of_divisor_certificate (j := 4) (s := {1, 2, 4, 11, 22, 44, 229}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 43, 293, 12599}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 13, 1163, 15119}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 31, 569, 17639}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 19, 1061, 20159}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 17, 23, 29}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 113, 223, 25199}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 53, 523, 27719}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 11, 2749, 30239}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 17, 41, 47}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 31, 62, 569}) (by decide)
  · exact not_P_of_divisor_certificate (j := 3) (s := {1, 3, 43, 129, 293, 879}) (by decide)

/-- The small exceptions to the residue argument modulo eleven are impossible. -/
theorem P.gt_39222 {n : ℕ} (h : P n) (hn : 24 < n) : 39222 < n := by
  by_contra hsmall
  obtain ⟨k, rfl⟩ := h.dvd_2520 hn
  exact not_P_2520_mul_small (by omega) (by omega) h

/-- Offset eighteen supplies residue seven modulo eleven; the other residues
are covered by offsets one through ten, omitting seven. -/
theorem P.dvd_27720 {n : ℕ} (h : P n) (hn : 24 < n) : 27720 ∣ n := by
  have h2520 := h.dvd_2520 hn
  have h11 : 11 ∣ n := h.dvd_of_residue_cover (L := 2520) (B := 39222) h2520
    (h.gt_39222 hn) (by decide) {1, 2, 3, 4, 5, 6, 8, 9, 10, 18} (by decide) (by decide)
  exact (by decide : Nat.Coprime 2520 11).mul_dvd_of_dvd_of_dvd h2520 h11

private theorem not_P_27720_mul_small {k : ℕ} (hlo : 1 ≤ k) (hhi : k ≤ 3) :
    ¬ P (27720 * k) := by
  interval_cases k
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 53, 523, 27719}) (by decide)
  · exact not_P_of_divisor_certificate (j := 2) (s := {1, 2, 53, 106, 523}) (by decide)
  · exact not_P_of_divisor_certificate (j := 1) (s := {1, 137, 607, 83159}) (by decide)

/-- There are only three small multiples to exclude at the last residue step. -/
theorem P.gt_97368 {n : ℕ} (h : P n) (hn : 24 < n) : 97368 < n := by
  by_contra hsmall
  obtain ⟨k, rfl⟩ := h.dvd_27720 hn
  exact not_P_27720_mul_small (by omega) (by omega) h

/-- Main necessary divisibility reduction for the actual Erdős 647 condition.
Offsets twenty and twenty-four supply residues seven and eleven modulo thirteen. -/
theorem P.dvd_360360 {n : ℕ} (h : P n) (hn : 24 < n) : 360360 ∣ n := by
  have h27720 := h.dvd_27720 hn
  have h2520 : 2520 ∣ n := (by decide : 2520 ∣ 27720).trans h27720
  have h13 : 13 ∣ n := h.dvd_of_residue_cover (L := 2520) (B := 97368) h2520
    (h.gt_97368 hn) (by decide) {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 20, 24}
    (by decide) (by decide)
  exact (by decide : Nat.Coprime 27720 13).mul_dvd_of_dvd_of_dvd h27720 h13

/-- The main reduction stated directly for the finite `Nat` supremum in the specification. -/
theorem fin_iSup_bound_dvd_360360 {n : ℕ} (hn : 24 < n)
    (h : (⨆ m : Fin n, (m : ℕ) + σ 0 (m : ℕ)) ≤ n + 2) : 360360 ∣ n := by
  exact ((p_iff_fin_iSup_bound (by omega : 0 < n)).mpr h).dvd_360360 hn

/-- In particular, a putative solution greater than 24 is at least 360360. -/
theorem P.ge_360360 {n : ℕ} (h : P n) (hn : 24 < n) : 360360 ≤ n := by
  exact Nat.le_of_dvd (by omega) (h.dvd_360360 hn)

/-- The known boundary value really satisfies the pointwise inequalities. -/
theorem p_twentyfour : P 24 := by
  intro m hm
  interval_cases m <;> decide

/-- An exact reformulation of the remaining existence problem after the
necessary divisibility reduction. This is not an existence assertion. -/
theorem exists_iff_core_multiple :
    (∃ n > 24, (⨆ m : Fin n, (m : ℕ) + σ 0 (m : ℕ)) ≤ n + 2) ↔
      ∃ k > 0, P (360360 * k) := by
  constructor
  · rintro ⟨n, hn, hsup⟩
    have hp := (p_iff_fin_iSup_bound (by omega : 0 < n)).mpr hsup
    obtain ⟨k, rfl⟩ := hp.dvd_360360 hn
    exact ⟨k, by omega, hp⟩
  · rintro ⟨k, hk, hp⟩
    refine ⟨360360 * k, by omega, ?_⟩
    exact (p_iff_fin_iSup_bound (by omega : 0 < 360360 * k)).mp hp

end Erdos647

#print axioms Erdos647.p_iff_fin_iSup_bound
#print axioms Erdos647.two_mul_card_divisors_le
#print axioms Erdos647.P.dvd_of_residue_cover
#print axioms Erdos647.P.dvd_24
#print axioms Erdos647.P.dvd_2520
#print axioms Erdos647.P.dvd_360360
#print axioms Erdos647.fin_iSup_bound_dvd_360360
#print axioms Erdos647.P.ge_360360

#print axioms Erdos647.p_twentyfour
#print axioms Erdos647.exists_iff_core_multiple
