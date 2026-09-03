import Submission.PrimitiveTotientCollisions

/-!
# Excluding a finite set of input primes

A squarefree totient fiber can be split by its gcd with a prescribed positive
integer K. Dividing by that gcd leaves inputs coprime to K, at a loss bounded
by the number of divisors of K. This preserves attained multiplicity
exponents with arbitrarily small loss; it does not increase the exponent.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

/-- Squarefree preimages with none of the prime divisors of K. -/
noncomputable def gAvoiding (K n : ℕ) : ℕ :=
  {m : ℕ | Squarefree m ∧ Nat.Coprime m K ∧ Nat.totient m = n}.ncard

lemma finite_avoiding_totient_fiber (K n : ℕ) :
    {m : ℕ | Squarefree m ∧ Nat.Coprime m K ∧ Nat.totient m = n}.Finite :=
  (finite_squarefree_totient_fiber n).subset (fun _ hm => ⟨hm.1, hm.2.2⟩)

lemma gAvoiding_le_gSquarefree (K n : ℕ) : gAvoiding K n ≤ gSquarefree n :=
  Set.ncard_le_ncard (fun _ hm => ⟨hm.1, hm.2.2⟩) (finite_squarefree_totient_fiber n)

lemma card_le_gAvoiding (K n : ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, Squarefree m ∧ Nat.Coprime m K ∧ Nat.totient m = n) :
    S.card ≤ gAvoiding K n := by
  have hsub : (S : Set ℕ) ⊆
      {m : ℕ | Squarefree m ∧ Nat.Coprime m K ∧ Nat.totient m = n} := hS
  have h := Set.ncard_le_ncard hsub (finite_avoiding_totient_fiber K n)
  simpa only [Set.ncard_coe_finset, gAvoiding] using h

/-- A single gcd class injects into one prime-excluded fiber. -/
lemma card_gcd_class_le_gAvoiding (K n d : ℕ) (hK : 0 < K)
    (S : Finset ℕ)
    (hS : ∀ m ∈ S, Squarefree m ∧ Nat.totient m = n ∧ Nat.gcd m K = d) :
    S.card ≤ gAvoiding K (n / Nat.totient d) := by
  have hinj : Set.InjOn (fun m : ℕ => m / d) (S : Set ℕ) := by
    intro a ha b hb hab
    have hda : d ∣ a := (hS a ha).2.2 ▸ Nat.gcd_dvd_left a K
    have hdb : d ∣ b := (hS b hb).2.2 ▸ Nat.gcd_dvd_left b K
    calc
      a = d * (a / d) := (Nat.mul_div_cancel' hda).symm
      _ = d * (b / d) := congrArg (fun c : ℕ => d*c) hab
      _ = b := Nat.mul_div_cancel' hdb
  have himage : ∀ m ∈ S.image (fun m : ℕ => m/d),
      Squarefree m ∧ Nat.Coprime m K ∧ Nat.totient m = n / Nat.totient d := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨haSq, haφ, had⟩ := hS a ha
    have hda : d ∣ a := had ▸ Nat.gcd_dvd_left a K
    have hd : 0 < d := had ▸ Nat.gcd_pos_of_pos_right a hK
    have hcop : Nat.Coprime (a / d) K := by
      rw [← had]
      exact Nat.coprime_div_gcd_of_squarefree haSq hK.ne'
    have hφ : Nat.totient (a/d) = n / Nat.totient d := by
      apply Nat.eq_div_of_mul_eq_right (Nat.totient_pos.mpr hd).ne'
      exact (PrimitiveCollisions.totient_divisor_factor haSq hda).symm.trans haφ
    exact ⟨haSq.squarefree_of_dvd (Nat.div_dvd_of_dvd hda), hcop, hφ⟩
  have h := card_le_gAvoiding K (n / Nat.totient d) _ himage
  rwa [Finset.card_image_of_injOn hinj] at h

/-- Uniform finite bound, valid before any asymptotic parameter is chosen. -/
lemma gSquarefree_le_sum_gAvoiding (K n : ℕ) (hK : 0 < K) :
    gSquarefree n ≤ ∑ d ∈ K.divisors, gAvoiding K (n / Nat.totient d) := by
  let S := (finite_squarefree_totient_fiber n).toFinset
  have hS (m : ℕ) : m ∈ S ↔ Squarefree m ∧ Nat.totient m = n :=
    (finite_squarefree_totient_fiber n).mem_toFinset
  have hcard : S.card = gSquarefree n :=
    (Set.ncard_eq_toFinset_card _ (finite_squarefree_totient_fiber n)).symm
  have hmap : Set.MapsTo (fun m : ℕ => Nat.gcd m K) (S : Set ℕ)
      (K.divisors : Set ℕ) := by
    intro m _hm
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hK.ne'⟩
  rw [← hcard, Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_le_sum
  intro d _hd
  apply card_gcd_class_le_gAvoiding K n d hK
  intro m hm
  obtain ⟨hmS, hmd⟩ := Finset.mem_filter.mp hm
  exact ⟨((hS m).mp hmS).1, ((hS m).mp hmS).2, hmd⟩

lemma exists_reduced_gAvoiding (K n : ℕ) (hK : 0 < K) :
    ∃ m : ℕ, m ≤ n ∧ gSquarefree n ≤ K.divisors.card * gAvoiding K m := by
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image K.divisors
    (fun d : ℕ => gAvoiding K (n / Nat.totient d))
    ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hK.ne'⟩⟩
  refine ⟨n / Nat.totient d, Nat.div_le_self _ _, ?_⟩
  calc
    gSquarefree n ≤ ∑ e ∈ K.divisors, gAvoiding K (n / Nat.totient e) :=
      gSquarefree_le_sum_gAvoiding K n hK
    _ ≤ ∑ _e ∈ K.divisors, gAvoiding K (n / Nat.totient d) := Finset.sum_le_sum hmax
    _ = _ := by simp

/-- Prime exclusion also permits K to vary, provided its divisor-count loss
is bounded at the particular input scale. The output is at most n. -/
lemma exists_gAvoiding_gt_of_divisor_count (K n : ℕ) (hK : 0 < K) (hn : 0 < n)
    (α β : ℝ) (hcount : (K.divisors.card : ℝ) ≤ (n : ℝ)^β)
    (H : (n : ℝ)^(α+β) < (gSquarefree n : ℝ)) :
    ∃ m : ℕ, m ≤ n ∧ (n : ℝ)^α < (gAvoiding K m : ℝ) := by
  obtain ⟨m, hmn, hcard⟩ := exists_reduced_gAvoiding K n hK
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨m, hmn, ?_⟩
  have hprod : (n : ℝ)^β * (n : ℝ)^α < (n : ℝ)^β * (gAvoiding K m : ℝ) := by
    calc
      (n : ℝ)^β * (n : ℝ)^α = (n : ℝ)^(α+β) := by
        rw [← Real.rpow_add hnR]
        congr 1
        ring
      _ < (gSquarefree n : ℝ) := H
      _ ≤ (K.divisors.card : ℝ) * (gAvoiding K m : ℝ) := by exact_mod_cast hcard
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)
  exact (mul_lt_mul_iff_right₀ (Real.rpow_pos_of_pos hnR β)).mp hprod

/-- Every fixed finite prime exclusion preserves an attained exponent with
an arbitrary positive loss. This does not assert a uniform scale in K. -/
theorem infinite_gAvoiding_of_infinite_gSquarefree (K : ℕ) (hK : 0 < K)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (H : {n : ℕ | (n : ℝ)^(α+β) < (gSquarefree n : ℝ)}.Infinite) :
    {m : ℕ | 0 < m ∧ (m : ℝ)^α < (gAvoiding K m : ℝ)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  let C := (Finset.range (N+1)).sup gSquarefree
  have hlimα : Tendsto (fun n : ℕ => (n : ℝ)^α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hlimβ : Tendsto (fun n : ℕ => (n : ℝ)^β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((eventually_ge_atTop 1).and
      ((hlimβ.eventually (eventually_ge_atTop (K.divisors.card : ℝ))).and
        (hlimα.eventually (eventually_gt_atTop (C : ℝ)))))
  obtain ⟨n, hnH, hnM⟩ := H.exists_gt M
  obtain ⟨hn, hτ, hC⟩ := hM n hnM.le
  obtain ⟨m, hmn, hbig⟩ := exists_gAvoiding_gt_of_divisor_count K n hK (by omega)
    α β hτ hnH
  have hNm : N < m := by
    by_contra hm
    have hmN : m ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    have hbound : (gAvoiding K m : ℝ) ≤ C := by
      exact_mod_cast (gAvoiding_le_gSquarefree K m).trans (Finset.le_sup (f := gSquarefree) hmN)
    exact (not_lt_of_ge hbound) (hC.trans hbig)
  refine ⟨m, ⟨by omega, ?_⟩, hNm⟩
  exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmn) hα.le).trans_lt hbig

/-- Removing arbitrary prime powers and then excluding a fixed finite set
still costs only an arbitrarily small loss in an attained exponent. -/
theorem infinite_gAvoiding_of_infinite_g (K : ℕ) (hK : 0 < K)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (H : {n : ℕ | (n : ℝ)^(α+β) < (g n : ℝ)}.Infinite) :
    {m : ℕ | 0 < m ∧ (m : ℝ)^α < (gAvoiding K m : ℝ)}.Infinite := by
  have hexp : (α+β/2)+β/2 = α+β := by ring
  have Hsf := infinite_gSquarefree_gt_of_infinite_g_gt (α+β/2) (β/2)
    (by linarith) (by linarith) (by simpa only [hexp] using H)
  apply infinite_gAvoiding_of_infinite_gSquarefree K hK α (β/2) hα (by linarith)
  exact Hsf.mono (fun _ hn => hn.2)

/-- The full assertion is unchanged by excluding any fixed finite set of
input primes. The equivalence does not establish either side. -/
theorem erdos_821_iff_avoiding_inputs (K : ℕ) (hK : 0 < K) :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite) ↔
      ∀ ε > (0 : ℝ), {n : ℕ | (gAvoiding K n : ℝ) > (n : ℝ)^(1-ε)}.Infinite := by
  constructor
  · intro H ε hε
    let e := min ε (1/2)
    have he : 0 < e := lt_min hε (by norm_num)
    have heε : e ≤ ε := min_le_left _ _
    have hehalf : e ≤ 1/2 := min_le_right _ _
    have hexp : (1-e)+e/2 = 1-e/2 := by ring
    have Ha := infinite_gAvoiding_of_infinite_g K hK (1-e) (e/2)
      (by linarith) (by linarith)
      (by simpa only [hexp] using H (e/2) (by linarith))
    apply Ha.mono
    intro n hn
    exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.1 : (1 : ℝ) ≤ n)
      (by linarith : 1-ε ≤ 1-e)).trans_lt hn.2
  · intro H ε hε
    apply (H ε hε).mono
    intro n hn
    have hg : (gAvoiding K n : ℝ) ≤ g n := by
      exact_mod_cast (gAvoiding_le_gSquarefree K n).trans (gSquarefree_le_g n)
    exact hn.trans_le hg

end Erdos821
