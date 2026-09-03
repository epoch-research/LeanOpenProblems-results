import Submission.Valuation

/-!
# Counting pairs in totient fibers through their LCM

These finite and conditional amplification results do not settle Erdős 821.
In particular, no adequate lower bound for large-overlap pairs is assumed
implicitly or asserted unconditionally.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma totient_lcm_mul_totient_gcd (a b : ℕ) :
    totient (Nat.lcm a b) * totient (Nat.gcd a b) = totient a * totient b := by
  let F : ArithmeticFunction ℕ := ⟨totient, Nat.totient_zero⟩
  have hF : F.IsMultiplicative := ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩
  exact hF.lcm_apply_mul_gcd_apply

lemma totient_lcm_of_equal_totient {a b n : ℕ} (hn : 0 < n)
    (ha : totient a = n) (hb : totient b = n) :
    totient (Nat.lcm a b) = n ^ 2 / totient (Nat.gcd a b) := by
  have ha0 : 0 < a := Nat.totient_pos.mp (ha ▸ hn)
  have he0 : 0 < totient (Nat.gcd a b) :=
    Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left b ha0)
  have h := totient_lcm_mul_totient_gcd a b
  rw [ha, hb, ← pow_two] at h
  exact Nat.eq_div_of_mul_eq_left he0.ne' h

lemma card_pairs_with_fixed_lcm_le (P : Finset (ℕ × ℕ)) (l : ℕ) (hl : l ≠ 0)
    (hP : ∀ ab ∈ P, Nat.lcm ab.1 ab.2 = l) :
    P.card ≤ l.divisors.card ^ 2 := by
  have hsub : P ⊆ l.divisors ×ˢ l.divisors := by
    intro ab hab
    have h := hP ab hab
    exact Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨h ▸ Nat.dvd_lcm_left ab.1 ab.2, hl⟩,
       Nat.mem_divisors.mpr ⟨h ▸ Nat.dvd_lcm_right ab.1 ab.2, hl⟩⟩
  simpa only [Finset.card_product, pow_two] using Finset.card_le_card hsub

lemma card_pair_family_le_lcm_image (P : Finset (ℕ × ℕ)) (D : ℕ)
    (hP : ∀ ab ∈ P, ab.1 ≠ 0 ∧ ab.2 ≠ 0)
    (hD : ∀ ab ∈ P, (Nat.lcm ab.1 ab.2).divisors.card ≤ D) :
    P.card ≤ D ^ 2 * (P.image (fun ab => Nat.lcm ab.1 ab.2)).card := by
  apply Finset.card_le_mul_card_image
  intro l hl
  obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hl
  have hl0 : Nat.lcm ab.1 ab.2 ≠ 0 := Nat.lcm_ne_zero (hP ab hab).1 (hP ab hab).2
  exact (card_pairs_with_fixed_lcm_le _ _ hl0
    (fun cd hcd => (Finset.mem_filter.mp hcd).2)).trans
      (Nat.pow_le_pow_left (hD ab hab) 2)

lemma card_pairs_with_fixed_gcd_totient_le (P : Finset (ℕ × ℕ)) (n e D : ℕ)
    (hn : 0 < n)
    (hP : ∀ ab ∈ P, totient ab.1 = n ∧ totient ab.2 = n ∧
      totient (Nat.gcd ab.1 ab.2) = e)
    (hD : ∀ ab ∈ P, (Nat.lcm ab.1 ab.2).divisors.card ≤ D) :
    P.card ≤ D ^ 2 * g (n ^ 2 / e) := by
  have hnonzero (ab : ℕ × ℕ) (hab : ab ∈ P) : ab.1 ≠ 0 ∧ ab.2 ≠ 0 :=
    ⟨(Nat.totient_pos.mp ((hP ab hab).1 ▸ hn)).ne',
     (Nat.totient_pos.mp ((hP ab hab).2.1 ▸ hn)).ne'⟩
  have hsub : (↑(P.image (fun ab => Nat.lcm ab.1 ab.2)) : Set ℕ) ⊆
      {m : ℕ | totient m = n ^ 2 / e} := by
    intro l hl
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hl
    change totient (Nat.lcm ab.1 ab.2) = n ^ 2 / e
    rw [totient_lcm_of_equal_totient hn (hP ab hab).1 (hP ab hab).2.1,
      (hP ab hab).2.2]
  have hcard := Set.ncard_le_ncard hsub (finite_totient_fiber _)
  have hcard' : (P.image (fun ab => Nat.lcm ab.1 ab.2)).card ≤ g (n ^ 2 / e) := by
    simpa only [Set.ncard_coe_finset, g] using hcard
  exact (card_pair_family_le_lcm_image P D hnonzero hD).trans
    (Nat.mul_le_mul_left _ hcard')

/-- Grouping by the totient of the GCD costs at most the divisor count of `n`.
LCM collisions cost at most the square of a uniform divisor-count bound. -/
lemma exists_lcm_fiber_of_pair_family (P : Finset (ℕ × ℕ)) (n D : ℕ)
    (hn : 0 < n) (hne : P.Nonempty)
    (hP : ∀ ab ∈ P, totient ab.1 = n ∧ totient ab.2 = n)
    (hD : ∀ ab ∈ P, (Nat.lcm ab.1 ab.2).divisors.card ≤ D) :
    ∃ e ∈ P.image (fun ab => totient (Nat.gcd ab.1 ab.2)),
      e ∈ n.divisors ∧ P.card ≤ n.divisors.card * D ^ 2 * g (n ^ 2 / e) := by
  let E := P.image (fun ab => totient (Nat.gcd ab.1 ab.2))
  have hE : E.Nonempty := hne.image _
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image E (fun e => g (n ^ 2 / e)) hE
  have hsub : E ⊆ n.divisors := by
    intro d hd
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨by
      rw [← (hP ab hab).1]
      exact Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left _ _), hn.ne'⟩
  refine ⟨e, he, hsub he, ?_⟩
  have hbound (d : ℕ) (hd : d ∈ E) :
      (P.filter (fun ab => totient (Nat.gcd ab.1 ab.2) = d)).card ≤
        D ^ 2 * g (n ^ 2 / e) := by
    apply (card_pairs_with_fixed_gcd_totient_le _ n d D hn ?_ ?_).trans
      (Nat.mul_le_mul_left _ (hmax d hd))
    · intro ab hab
      obtain ⟨habP, habd⟩ := Finset.mem_filter.mp hab
      exact ⟨(hP ab habP).1, (hP ab habP).2, habd⟩
    · intro ab hab
      exact hD ab (Finset.mem_filter.mp hab).1
  have hcount := Finset.card_le_mul_card_image P (D ^ 2 * g (n ^ 2 / e)) hbound
  calc
    P.card ≤ (D ^ 2 * g (n ^ 2 / e)) * E.card := hcount
    _ ≤ (D ^ 2 * g (n ^ 2 / e)) * n.divisors.card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
    _ = _ := by ring

lemma exists_small_lcm_fiber_of_pair_family (P : Finset (ℕ × ℕ)) (n D Y : ℕ)
    (hn : 0 < n) (hne : P.Nonempty) (hY : 0 < Y)
    (hP : ∀ ab ∈ P, totient ab.1 = n ∧ totient ab.2 = n ∧
      Y ≤ totient (Nat.gcd ab.1 ab.2))
    (hD : ∀ ab ∈ P, (Nat.lcm ab.1 ab.2).divisors.card ≤ D) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n ^ 2 / Y ∧
      P.card ≤ n.divisors.card * D ^ 2 * g m := by
  obtain ⟨e, he, hed, hcard⟩ := exists_lcm_fiber_of_pair_family P n D hn hne
    (fun ab hab => ⟨(hP ab hab).1, (hP ab hab).2.1⟩) hD
  obtain ⟨ab, hab, heq⟩ := Finset.mem_image.mp he
  have heY : Y ≤ e := heq ▸ (hP ab hab).2.2
  refine ⟨n ^ 2 / e, ?_, Nat.div_le_div_left heY hY, hcard⟩
  have hepos := Nat.pos_of_mem_divisors hed
  have hen : e ≤ n := Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hed)
  have hnn : n ≤ n ^ 2 := by have := hn; nlinarith
  exact Nat.div_pos (hen.trans hnn) hepos

lemma lcm_le_polynomial_of_equal_totient {a b n : ℕ} (hn : 0 < n)
    (ha : totient a = n) (hb : totient b = n) :
    Nat.lcm a b ≤ 576 * n ^ 4 := by
  have ha0 : 0 < a := Nat.totient_pos.mp (ha ▸ hn)
  have hb0 : 0 < b := Nat.totient_pos.mp (hb ▸ hn)
  have haB : a ≤ 24 * n ^ 2 := by
    simpa [ha] using input_pow_le_totient_pow a 1 (by decide)
  have hbB : b ≤ 24 * n ^ 2 := by
    simpa [hb] using input_pow_le_totient_pow b 1 (by decide)
  calc
    Nat.lcm a b ≤ a * b := Nat.lcm_le_mul ha0 hb0
    _ ≤ (24 * n ^ 2) * (24 * n ^ 2) := Nat.mul_le_mul haB hbB
    _ = _ := by ring

/-- The divisor bound is uniform over the whole polynomial-sized range of
possible LCMs, not just along an individual sequence of LCMs. -/
lemma eventually_uniform_lcm_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ l : ℕ, l ≤ 576 * n ^ 4 →
      (l.divisors.card : ℝ) ≤ (n : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (5 / ε)
  have hkR : (0 : ℝ) < k := (div_pos (by norm_num) hε).trans hk
  have hk0 : k ≠ 0 := by exact_mod_cast hkR.ne'
  have hkε : 5 < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  let C := (k.factorial * 2 ^ k) ^ (2 ^ k)
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (576 * C)] with n hn hC
  intro l hl
  by_cases hl0 : l = 0
  · simp [hl0, Real.rpow_nonneg]
  have hpow : l.divisors.card ^ k ≤ n ^ 5 := by
    calc
      l.divisors.card ^ k ≤ C * l := card_divisors_pow_le l k hl0
      _ ≤ C * (576 * n ^ 4) := Nat.mul_le_mul_left C hl
      _ = (576 * C) * n ^ 4 := by ring
      _ ≤ n * n ^ 4 := Nat.mul_le_mul_right _ hC
      _ = n ^ 5 := by ring
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hreal : (l.divisors.card : ℝ) ^ k ≤ ((n : ℝ) ^ ε) ^ k := by
    calc
      (l.divisors.card : ℝ) ^ k ≤ (n : ℝ) ^ (5 : ℕ) := by exact_mod_cast hpow
      _ = (n : ℝ) ^ (5 : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (n : ℝ) ^ (ε * (k : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith)
      _ = ((n : ℝ) ^ ε) ^ k := Real.rpow_mul_natCast (Nat.cast_nonneg n) _ _
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _) hk0).mp hreal

/-- A uniform, subpower-loss version of the finite LCM-pair reduction.
The existence of a sufficiently large family `P` remains a separate input. -/
lemma eventually_lcm_pair_amplification (η ζ : ℝ) (hζ : 0 < ζ) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Finset (ℕ × ℕ), P.Nonempty →
      (∀ ab ∈ P, totient ab.1 = n ∧ totient ab.2 = n ∧
        (n : ℝ) ^ η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ)) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (2 - η) ∧
        (P.card : ℝ) ≤ (n : ℝ) ^ ζ * (g m : ℝ) := by
  have he : 0 < ζ / 3 := div_pos hζ (by norm_num)
  filter_upwards [eventually_ge_atTop 1,
    eventually_card_divisors_le_rpow (ζ / 3) he,
    eventually_uniform_lcm_divisor_bound (ζ / 3) he] with n hn hnD hnL
  intro P hne hP
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨l, hl, hlmax⟩ := Finset.exists_max_image
    (P.image (fun ab => Nat.lcm ab.1 ab.2)) (fun l => l.divisors.card) (hne.image _)
  let D := l.divisors.card
  have hD (ab : ℕ × ℕ) (hab : ab ∈ P) : (Nat.lcm ab.1 ab.2).divisors.card ≤ D :=
    hlmax _ (Finset.mem_image_of_mem _ hab)
  have hDR : (D : ℝ) ≤ (n : ℝ) ^ (ζ / 3) := by
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hl
    exact hnL _ (lcm_le_polynomial_of_equal_totient hn0 (hP ab hab).1 (hP ab hab).2.1)
  obtain ⟨e, heP, hen, hcard⟩ := exists_lcm_fiber_of_pair_family P n D hn0 hne
    (fun ab hab => ⟨(hP ab hab).1, (hP ab hab).2.1⟩) hD
  have he0 : 0 < e := Nat.pos_of_mem_divisors hen
  have heR : (0 : ℝ) < e := by exact_mod_cast he0
  have hedvd : e ∣ n := Nat.dvd_of_mem_divisors hen
  have hesq : e ∣ n ^ 2 := hedvd.trans (by rw [pow_two]; exact Nat.dvd_mul_right _ _)
  have heη : (n : ℝ) ^ η ≤ e := by
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp heP
    exact (hP ab hab).2.2
  have hm0 : 0 < n ^ 2 / e := Nat.div_pos
    ((Nat.le_of_dvd hn0 hedvd).trans (by have := hn0; nlinarith)) he0
  refine ⟨n ^ 2 / e, hm0, ?_, ?_⟩
  · rw [Nat.cast_div hesq heR.ne', Nat.cast_pow, Real.rpow_sub hnR,
      Real.rpow_two]
    exact div_le_div_of_nonneg_left (sq_nonneg (n : ℝ)) (Real.rpow_pos_of_pos hnR _) heη
  · have hcoef : (n.divisors.card : ℝ) * (D : ℝ) ^ 2 ≤ (n : ℝ) ^ ζ := by
      calc
        (n.divisors.card : ℝ) * (D : ℝ) ^ 2 ≤
            (n : ℝ) ^ (ζ / 3) * ((n : ℝ) ^ (ζ / 3)) ^ 2 :=
          mul_le_mul hnD (pow_le_pow_left₀ (Nat.cast_nonneg D) hDR 2)
            (sq_nonneg _) (Real.rpow_nonneg hnR.le _)
        _ = (n : ℝ) ^ ζ := by
          rw [pow_two, ← Real.rpow_add hnR, ← Real.rpow_add hnR]
          congr 1
          ring
    calc
      (P.card : ℝ) ≤ (n.divisors.card : ℝ) * (D : ℝ) ^ 2 * (g (n ^ 2 / e) : ℝ) :=
        by exact_mod_cast hcard
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)

/-- Enough pairs with large GCD totient would give the indicated lower
multiplicity exponent. The pair supply is an explicit unproved hypothesis. -/
lemma infinite_g_gt_of_large_overlap_pairs (η ρ β : ℝ)
    (hη : η < 2) (hβ : 0 < β) (hρ : β * (2 - η) < ρ)
    (H : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ P : Finset (ℕ × ℕ),
      (n : ℝ) ^ ρ < (P.card : ℝ) ∧
      ∀ ab ∈ P, totient ab.1 = n ∧ totient ab.2 = n ∧
        (n : ℝ) ^ η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ)) :
    {m : ℕ | (g m : ℝ) > (m : ℝ) ^ β}.Infinite := by
  let ζ := (ρ - β * (2 - η)) / 2
  let s := ρ - ζ
  have hζ : 0 < ζ := half_pos (sub_pos.mpr hρ)
  have hprod : 0 < β * (2 - η) := mul_pos hβ (sub_pos.mpr hη)
  have hs : 0 < s := by dsimp [s, ζ]; linarith
  have hsβ : (2 - η) * β ≤ s := by dsimp [s, ζ]; nlinarith
  have hsζ : s + ζ = ρ := by dsimp [s]; ring
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ s) atTop atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  apply Set.infinite_of_forall_exists_gt
  intro N
  let C := (Finset.range (N + 1)).sup g
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((eventually_lcm_pair_amplification η ζ hζ).and
      ((hlim.eventually (eventually_gt_atTop (C : ℝ))).and (eventually_ge_atTop 1)))
  obtain ⟨n, hnA, P, hcard, hP⟩ := H A
  obtain ⟨hamp, hnC, hn1⟩ := hA n hnA.le
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hne : P.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (Real.rpow_pos_of_pos hnR ρ).trans hcard)
  obtain ⟨m, hm0, hmn, hcount⟩ := hamp P hne hP
  have hgz : (n : ℝ) ^ s < (g m : ℝ) := by
    have hmul : (n : ℝ) ^ s * (n : ℝ) ^ ζ < (n : ℝ) ^ ζ * (g m : ℝ) := by
      rw [← Real.rpow_add hnR, hsζ]
      exact hcard.trans_le hcount
    have hzpos := Real.rpow_pos_of_pos hnR ζ
    nlinarith
  refine ⟨m, ?_, ?_⟩
  · calc
      (m : ℝ) ^ β ≤ ((n : ℝ) ^ (2 - η)) ^ β :=
        Real.rpow_le_rpow (Nat.cast_nonneg m) hmn hβ.le
      _ = (n : ℝ) ^ ((2 - η) * β) := (Real.rpow_mul hnR.le _ _).symm
      _ ≤ (n : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hnR1 hsβ
      _ < (g m : ℝ) := hgz
  · by_contra h
    have hmN : m ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hgm : (g m : ℝ) ≤ C := by exact_mod_cast (Finset.le_sup (f := g) hmN)
    exact (not_lt_of_ge hgm) (hnC.trans hgz)

/-- The strict overlap-frequency threshold `ℓ < α*η` really would improve
an exponent `α`; no such overlap-frequency estimate is proved here. -/
lemma improved_exponent_of_large_overlap_pairs (α η ℓ : ℝ)
    (hα : 0 < α) (hη : η < 2) (hℓ : ℓ < α * η)
    (H : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ P : Finset (ℕ × ℕ),
      (n : ℝ) ^ (2 * α - ℓ) < (P.card : ℝ) ∧
      ∀ ab ∈ P, totient ab.1 = n ∧ totient ab.2 = n ∧
        (n : ℝ) ^ η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ)) :
    ∃ β : ℝ, α < β ∧ {m : ℕ | (g m : ℝ) > (m : ℝ) ^ β}.Infinite := by
  have hden : 0 < 2 - η := sub_pos.mpr hη
  let β := (α + (2 * α - ℓ) / (2 - η)) / 2
  have hgap : α < (2 * α - ℓ) / (2 - η) :=
    (lt_div_iff₀ hden).mpr (by nlinarith)
  have hαβ : α < β := by dsimp [β]; linarith
  refine ⟨β, hαβ, infinite_g_gt_of_large_overlap_pairs η (2 * α - ℓ) β hη
    (hα.trans hαβ) ?_ H⟩
  apply (lt_div_iff₀ hden).mp
  dsimp [β]
  linarith

#print axioms exists_small_lcm_fiber_of_pair_family
#print axioms eventually_uniform_lcm_divisor_bound
#print axioms eventually_lcm_pair_amplification
#print axioms infinite_g_gt_of_large_overlap_pairs
#print axioms improved_exponent_of_large_overlap_pairs

end Erdos821
