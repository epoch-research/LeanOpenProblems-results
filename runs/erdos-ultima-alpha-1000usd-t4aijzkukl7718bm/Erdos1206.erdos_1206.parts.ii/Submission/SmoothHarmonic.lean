import FormalConjecturesUtil

/-!
A harmonic projection onto finite-prime dilation orbits. This is an auxiliary
bound, not a settlement of the positive-density cube-Sidon conjecture.
-/

namespace Erdos1206
open Finset
open scoped Classical

/-- Positive integers divisible by none of the primes in `P`. -/
def primeRough (P : Finset ℕ) (r : ℕ) : Prop :=
  0 < r ∧ ∀ p ∈ P, ¬ p ∣ r

lemma factored_rough_decomposition (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {n : ℕ} (hn : 0 < n) :
    ∃ r s : ℕ, primeRough P r ∧ s ∈ Nat.factoredNumbers P ∧ r * s = n := by
  let s := (n.primeFactorsList.filter (fun p => p ∈ P)).prod
  let r := (n.primeFactorsList.filter (fun p => p ∉ P)).prod
  have hs : s ∈ Nat.factoredNumbers P := Nat.prod_mem_factoredNumbers P n
  have hr0 : r ≠ 0 := List.prod_ne_zero (by
    intro hz
    have hz' := List.mem_of_mem_filter hz
    exact (Nat.pos_of_mem_primeFactorsList hz').ne' rfl)
  have hr : primeRough P r := by
    refine ⟨Nat.pos_of_ne_zero hr0, ?_⟩
    intro p hp hpr
    have hm := mem_list_primes_of_dvd_prod (hP p hp).prime
      (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hpr
    have hnot : p ∉ P := by simpa using List.of_mem_filter hm
    exact hnot hp
  refine ⟨r, s, hr, hs, ?_⟩
  have he := (List.filter_append_perm (fun p => decide (p ∈ P)) n.primeFactorsList).prod_eq
  simpa [s, r, List.prod_append, mul_comm] using he.trans (Nat.prod_primeFactorsList hn.ne')

lemma cube_sidon_dilation_preimage {A : Set ℕ}
    (hA : IsSidon ((fun n : ℕ => n ^ 3) '' A)) {r : ℕ} (hr : 0 < r) :
    IsSidon ((fun n : ℕ => n ^ 3) '' {n | r * n ∈ A}) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ he
  have he' : (r * a) ^ 3 + (r * b) ^ 3 = (r * c) ^ 3 + (r * d) ^ 3 := by
    simpa only [mul_pow, ← mul_add] using congrArg (fun x : ℕ => r ^ 3 * x) he
  have hh := hA _ ⟨r * a, ha, rfl⟩ _ ⟨r * c, hc, rfl⟩
    _ ⟨r * b, hb, rfl⟩ _ ⟨r * d, hd, rfl⟩ he'
  simp only [mul_pow] at hh
  have hp : 0 < r ^ 3 := pow_pos hr _
  rcases hh with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left hp h₁, Nat.eq_of_mul_eq_mul_left hp h₂⟩
  · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hp h₁, Nat.eq_of_mul_eq_mul_left hp h₂⟩

/-- A uniform reciprocal-weight bound on finite Sidon sets of `P`-smooth roots. -/
def SmoothCubeHarmonicBound (P : Finset ℕ) (B : ℝ) : Prop :=
  ∀ S : Finset ℕ, (∀ s ∈ S, s ∈ Nat.factoredNumbers P) →
    IsSidon ((fun n : ℕ => n ^ 3) '' (S : Set ℕ)) →
      ∑ s ∈ S, (1 : ℝ) / s ≤ B

/-- Project an arbitrary cube-Sidon root set onto its finite-prime dilation
orbits. No asymptotic bound on the constants `B` is asserted. -/
lemma cube_sidon_harmonic_projection {A : Set ℕ}
    (hA : IsSidon ((fun n : ℕ => n ^ 3) '' A))
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) {B : ℝ}
    (hB : SmoothCubeHarmonicBound P B) (N : ℕ) :
    (∑ n ∈ (Icc 1 N).filter (fun n => n ∈ A), (1 : ℝ) / n) ≤
      B * ∑ r ∈ (Icc 1 N).filter (primeRough P), (1 : ℝ) / r := by
  classical
  have hd (n : ℕ) : ∃ r s : ℕ, 0 < n →
      primeRough P r ∧ s ∈ Nat.factoredNumbers P ∧ r * s = n := by
    by_cases hn : 0 < n
    · obtain ⟨r, s, hh⟩ := factored_rough_decomposition P hP hn
      exact ⟨r, s, fun _ => hh⟩
    · exact ⟨1, 1, fun hh => (hn hh).elim⟩
  choose r s hrs using hd
  let U := (Icc 1 N).filter (fun n => n ∈ A)
  let R := (Icc 1 N).filter (primeRough P)
  let V (q : ℕ) := (Icc 1 N).filter (fun t => t ∈ Nat.factoredNumbers P ∧ q * t ∈ A)
  let F : ℕ → ℕ × ℕ := fun n => (r n, s n)
  let T := (R ×ˢ Icc 1 N).filter (fun x => x.2 ∈ Nat.factoredNumbers P ∧ x.1 * x.2 ∈ A)
  have hsub : U.image F ⊆ T := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    have hnI := mem_Icc.mp (mem_filter.mp hn).1
    have hh := hrs n hnI.1
    have hs0 := Nat.pos_of_ne_zero hh.2.1.1
    have hrN : r n ≤ N := (Nat.le_mul_of_pos_right _ hs0).trans (hh.2.2.le.trans hnI.2)
    have hsN : s n ≤ N := (Nat.le_mul_of_pos_left _ hh.1.1).trans (hh.2.2.le.trans hnI.2)
    have hmem : r n * s n ∈ A := by rw [hh.2.2]; exact (mem_filter.mp hn).2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hh.1.1, hrN⟩, hh.1⟩,
      mem_Icc.mpr ⟨hs0, hsN⟩⟩, hh.2.1, hmem⟩
  have hinj : Set.InjOn F (U : Set ℕ) := by
    intro n hn m hm he
    change n ∈ U at hn
    change m ∈ U at hm
    have hn0 := (mem_Icc.mp (mem_filter.mp hn).1).1
    have hm0 := (mem_Icc.mp (mem_filter.mp hm).1).1
    have hh := congrArg (fun x : ℕ × ℕ => x.1 * x.2) he
    change r n * s n = r m * s m at hh
    simpa only [(hrs n hn0).2.2, (hrs m hm0).2.2] using hh
  have hV (q : ℕ) (hq : q ∈ R) : (∑ t ∈ V q, (1 : ℝ) / t) ≤ B := by
    apply hB
    · intro t ht; exact (mem_filter.mp ht).2.1
    · apply Set.IsSidon.subset (cube_sidon_dilation_preimage hA (mem_filter.mp hq).2.1)
      rintro _ ⟨t, ht, rfl⟩
      change t ∈ V q at ht
      exact ⟨t, (mem_filter.mp ht).2.2, rfl⟩
  calc
    _ = ∑ x ∈ U.image F, (1 : ℝ) / (x.1 * x.2 : ℕ) := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro n hn
      dsimp [F]
      rw [(hrs n (mem_Icc.mp (mem_filter.mp hn).1).1).2.2]
    _ ≤ ∑ x ∈ T, (1 : ℝ) / (x.1 * x.2 : ℕ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ q ∈ R, ((1 : ℝ) / q) * ∑ t ∈ V q, (1 : ℝ) / t := by
      dsimp only [T, V]
      rw [sum_filter, sum_product]
      apply sum_congr rfl
      intro q hq
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro t ht
      split_ifs <;> simp [Nat.cast_mul, div_mul_eq_div_mul_one_div]
    _ ≤ ∑ q ∈ R, ((1 : ℝ) / q) * B :=
      sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hV q hq) (by positivity)
    _ = _ := by rw [← sum_mul, mul_comm]


/-- Summation by parts preserves prefix inequalities for reciprocal weights. -/
lemma harmonic_prefix_mono {f g : ℕ → ℝ}
    (h : ∀ n, (∑ i ∈ range n, f i) ≤ ∑ i ∈ range n, g i) (N : ℕ) :
    (∑ i ∈ range N, f i / (i + 1 : ℕ)) ≤
      ∑ i ∈ range N, g i / (i + 1 : ℕ) := by
  have hf := sum_range_by_parts (fun i : ℕ => (1 : ℝ) / (i + 1 : ℕ)) f N
  have hg := sum_range_by_parts (fun i : ℕ => (1 : ℝ) / (i + 1 : ℕ)) g N
  simp only [smul_eq_mul, one_div_mul_eq_div] at hf hg
  have htop := mul_le_mul_of_nonneg_left (h N)
    (show (0 : ℝ) ≤ 1 / (N - 1 + 1 : ℕ) by positivity)
  have htail :
      (∑ i ∈ range (N - 1), (1 / (i + 1 + 1 : ℕ) - (1 : ℝ) / (i + 1 : ℕ)) *
        ∑ j ∈ range (i + 1), g j) ≤
      ∑ i ∈ range (N - 1), (1 / (i + 1 + 1 : ℕ) - (1 : ℝ) / (i + 1 : ℕ)) *
        ∑ j ∈ range (i + 1), f j := by
    apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonpos_left (h (i + 1))
    apply sub_nonpos.mpr
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (show i + 1 ≤ i + 1 + 1 by omega))
  simp only [one_div_mul_eq_div] at htop
  linarith

lemma harmonic_of_prefix_upper {f : ℕ → ℝ} {a b : ℝ}
    (h : ∀ n, (∑ i ∈ range n, f i) ≤ a * n + b) (N : ℕ) :
    (∑ i ∈ range N, f i / (i + 1 : ℕ)) ≤
      a * (∑ i ∈ range N, (1 : ℝ) / (i + 1 : ℕ)) + b := by
  classical
  have hb : 0 ≤ b := by simpa using h 0
  let g : ℕ → ℝ := fun i => a + if i = 0 then b else 0
  have hg (n : ℕ) : (∑ i ∈ range n, g i) = a * n + if n = 0 then 0 else b := by
    cases n <;> simp [g, sum_add_distrib, mul_comm]
  have hh : ∀ n, (∑ i ∈ range n, f i) ≤ ∑ i ∈ range n, g i := by
    intro n
    cases n with
    | zero => simp
    | succ n => simpa [hg] using h (n + 1)
  have hw := harmonic_prefix_mono hh N
  have he : (∑ i ∈ range N, g i / (i + 1 : ℕ)) =
      a * (∑ i ∈ range N, (1 : ℝ) / (i + 1 : ℕ)) + if N = 0 then 0 else b := by
    dsimp [g]
    simp_rw [add_div]
    rw [sum_add_distrib, mul_sum]
    congr 1
    · apply sum_congr rfl; intros; ring
    · have hterm (i : ℕ) : (if i = 0 then b else 0) / (i + 1 : ℕ) =
          if i = 0 then b else 0 := by by_cases hi : i = 0 <;> simp [hi]
      simp_rw [hterm]
      cases N <;> simp
  rw [he] at hw
  split_ifs at hw with hN
  · linarith
  · exact hw

lemma shifted_range_sum_eq_Icc (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1)) = ∑ i ∈ Icc 1 N, f i := by
  have hh := sum_Ico_add' f 0 N 1
  have he : Ico (0 + 1) (N + 1) = Icc 1 N := by
    ext k
    simp only [mem_Ico, mem_Icc]
    omega
  rw [he] at hh
  simpa [Nat.Ico_zero_eq_range] using hh

lemma set_harmonic_of_prefix_upper {A : Set ℕ} {a b : ℝ}
    (h : ∀ n, (((Icc 1 n).filter (fun k => k ∈ A)).card : ℝ) ≤ a * n + b) (N : ℕ) :
    (∑ k ∈ (Icc 1 N).filter (fun k => k ∈ A), (1 : ℝ) / k) ≤
      a * (∑ i ∈ range N, (1 : ℝ) / (i + 1 : ℕ)) + b := by
  let f : ℕ → ℝ := fun i => if i + 1 ∈ A then 1 else 0
  have hp (n : ℕ) : (∑ i ∈ range n, f i) ≤ a * n + b := by
    change (∑ i ∈ range n, (fun k : ℕ => if k ∈ A then (1 : ℝ) else 0) (i + 1)) ≤ _
    rw [shifted_range_sum_eq_Icc (fun k : ℕ => if k ∈ A then (1 : ℝ) else 0), sum_boole]
    exact h n
  have hh := harmonic_of_prefix_upper hp N
  have he : (∑ i ∈ range N, f i / (i + 1 : ℕ)) =
      ∑ k ∈ (Icc 1 N).filter (fun k => k ∈ A), (1 : ℝ) / k := by
    rw [sum_filter]
    have ht (i : ℕ) : f i / (i + 1 : ℕ) =
        (fun k : ℕ => if k ∈ A then (1 : ℝ) / k else 0) (i + 1) := by
      dsimp [f]; split_ifs <;> simp
    simp_rw [ht]
    exact shifted_range_sum_eq_Icc (fun k : ℕ => if k ∈ A then (1 : ℝ) / k else 0) N
  rwa [he] at hh

lemma set_harmonic_of_prefix_lower {A : Set ℕ} {a b : ℝ}
    (h : ∀ n, a * n ≤ (((Icc 1 n).filter (fun k => k ∈ A)).card : ℝ) + b) (N : ℕ) :
    a * (∑ i ∈ range N, (1 : ℝ) / (i + 1 : ℕ)) ≤
      (∑ k ∈ (Icc 1 N).filter (fun k => k ∈ A), (1 : ℝ) / k) + b := by
  let f : ℕ → ℝ := fun i => if i + 1 ∈ A then 1 else 0
  have hp (n : ℕ) : (∑ i ∈ range n, -f i) ≤ (-a) * n + b := by
    rw [sum_neg_distrib]
    have he : (∑ i ∈ range n, f i) = (((Icc 1 n).filter (fun k => k ∈ A)).card : ℝ) := by
      change (∑ i ∈ range n, (fun k : ℕ => if k ∈ A then (1 : ℝ) else 0) (i + 1)) = _
      rw [shifted_range_sum_eq_Icc (fun k : ℕ => if k ∈ A then (1 : ℝ) else 0), sum_boole]
    rw [he]
    linarith [h n]
  have hh := harmonic_of_prefix_upper hp N
  have he : (∑ i ∈ range N, f i / (i + 1 : ℕ)) =
      ∑ k ∈ (Icc 1 N).filter (fun k => k ∈ A), (1 : ℝ) / k := by
    rw [sum_filter]
    have ht (i : ℕ) : f i / (i + 1 : ℕ) =
        (fun k : ℕ => if k ∈ A then (1 : ℝ) / k else 0) (i + 1) := by
      dsimp [f]; split_ifs <;> simp
    simp_rw [ht]
    exact shifted_range_sum_eq_Icc (fun k : ℕ => if k ∈ A then (1 : ℝ) / k else 0) N
  simp only [neg_div, sum_neg_distrib, he, neg_mul] at hh
  linarith

open Filter
open scoped Topology

lemma positive_prefix_of_lt_lowerDensity {A : Set ℕ} {a : ℝ}
    (ha : 0 < a) (hden : a < A.lowerDensity) :
    ∃ C : ℝ, ∀ N : ℕ,
      a * N ≤ (((Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) + C := by
  have hev : ∀ᶠ N : ℕ in atTop, a < A.partialDensity Set.univ N :=
    eventually_lt_of_lt_liminf hden (isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨a * M + 1, fun N => ?_⟩
  by_cases hNM : N < M
  · have hle : (N : ℝ) ≤ M := by exact_mod_cast hNM.le
    have hmul := mul_le_mul_of_nonneg_left hle ha.le
    have hz : (0 : ℝ) ≤ (((Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) := by positivity
    linarith
  · by_cases hN : N = 0
    · subst N; simp; positivity
    have hp := hM N (by omega)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio] at hp
    have he : A ∩ Set.Iio N = ((range N).filter (fun n => n ∈ A) : Set ℕ) := by
      ext n; simp [and_comm]
    rw [he, Set.ncard_coe_finset] at hp
    have hc : ((range N).filter (fun n => n ∈ A)).card ≤
        ((Icc 1 N).filter (fun n => n ∈ A)).card + 1 := by
      have hs : (range N).filter (fun n => n ∈ A) ⊆
          insert 0 ((Icc 1 N).filter (fun n => n ∈ A)) := by
        intro n hn
        by_cases hn0 : n = 0
        · simp [hn0]
        · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_Icc.mpr
            ⟨by omega, (mem_range.mp (mem_filter.mp hn).1).le⟩, (mem_filter.mp hn).2⟩)
      exact (card_le_card hs).trans (card_insert_le 0 _)
    have hcR : (((range N).filter (fun n => n ∈ A)).card : ℝ) ≤
        (((Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) + 1 := by exact_mod_cast hc
    have hm0 : (0 : ℝ) ≤ a * M := by positivity
    have hn0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hh := (lt_div_iff₀ hn0).mp hp
    linarith

/-- A harmonic upper bound bounds lower natural density as well. This proof
uses finite summation by parts, not an unproved logarithmic-density theorem. -/
lemma lowerDensity_le_of_harmonic_upper {A : Set ℕ} {d C : ℝ} (hd : 0 ≤ d)
    (h : ∀ N : ℕ,
      (∑ n ∈ (Icc 1 N).filter (fun n => n ∈ A), (1 : ℝ) / n) ≤
        d * (∑ i ∈ range N, (1 : ℝ) / (i + 1 : ℕ)) + C) :
    A.lowerDensity ≤ d := by
  by_contra! hden
  obtain ⟨a, hda, haA⟩ := exists_between hden
  have ha : 0 < a := hd.trans_lt hda
  obtain ⟨D, hD⟩ := positive_prefix_of_lt_lowerDensity ha haA
  have hl (N : ℕ) := set_harmonic_of_prefix_lower hD N
  have hs : Summable (fun i : ℕ => (1 : ℝ) / (i + 1 : ℕ)) := by
    apply summable_of_sum_range_le (c := (C + D) / (a - d)) (fun _ => by positivity)
    intro N
    apply (le_div_iff₀ (sub_pos.mpr hda)).mpr
    nlinarith [hl N, h N]
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).mp hs

/-- A normalized smooth-orbit bound is an upper bound for every cube-Sidon
root set's lower density. The required smooth bounds remain an open input. -/
lemma cube_sidon_lowerDensity_le_of_smooth_harmonic_bound {A : Set ℕ}
    (hA : IsSidon ((fun n : ℕ => n ^ 3) '' A))
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) {B ρ C : ℝ}
    (hB : SmoothCubeHarmonicBound P B) (hρ : 0 ≤ ρ)
    (hR : ∀ N : ℕ, (((Icc 1 N).filter (primeRough P)).card : ℝ) ≤ ρ * N + C) :
    A.lowerDensity ≤ B * ρ := by
  have hB0 : 0 ≤ B := by
    have hh := hB ∅ (by simp) (by simp [IsSidon])
    simpa using hh
  apply lowerDensity_le_of_harmonic_upper (mul_nonneg hB0 hρ) (C := B * C)
  intro N
  have hproj := cube_sidon_harmonic_projection hA P hP hB N
  have hr := set_harmonic_of_prefix_upper (A := {r | primeRough P r}) hR N
  have hm := mul_le_mul_of_nonneg_left hr hB0
  calc
    _ ≤ B * (ρ * (∑ i ∈ range N, (1 : ℝ) / (i + 1 : ℕ)) + C) := hproj.trans hm
    _ = _ := by ring

/-- A sufficient condition for a disproof. No family of bounds satisfying
this vanishing-normalization condition has been established. -/
lemma no_positive_density_cube_sidon_of_vanishing_smooth_bounds
    (h : ∀ ε : ℝ, 0 < ε → ∃ (P : Finset ℕ) (B ρ C : ℝ),
      (∀ p ∈ P, Nat.Prime p) ∧ SmoothCubeHarmonicBound P B ∧ 0 ≤ ρ ∧
      (∀ N : ℕ, (((Icc 1 N).filter (primeRough P)).card : ℝ) ≤ ρ * N + C) ∧
      B * ρ < ε) :
    ¬ (∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun n : ℕ => n ^ 3) '' A)) := by
  rintro ⟨A, _, hden, hA⟩
  obtain ⟨P, B, ρ, C, hP, hB, hρ, hR, hlt⟩ := h A.lowerDensity hden
  have hh := cube_sidon_lowerDensity_le_of_smooth_harmonic_bound hA P hP hB hρ hR
  linarith


/-- The elementary periodic upper bound for the rough part of the decomposition. -/
lemma primeRough_prefix_totient_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (N : ℕ) :
    (((Icc 1 N).filter (primeRough P)).card : ℝ) ≤
      ((P.prod id).totient : ℝ) / P.prod id * N + (P.prod id).totient := by
  let M := P.prod id
  have hM : 0 < M := prod_pos (fun p hp => (hP p hp).pos)
  have hc : ((Icc 1 N).filter (primeRough P)).card ≤
      ((Ico 1 (1 + N)).filter (Nat.Coprime M)).card := by
    apply card_le_card
    intro n hn
    have hnI := mem_Icc.mp (mem_filter.mp hn).1
    have hnR := (mem_filter.mp hn).2
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨hnI.1, by omega⟩, ?_⟩
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    exact (hP p hp).coprime_iff_not_dvd.mpr (hnR.2 p hp)
  have hb := Nat.Ico_filter_coprime_le (a := M) 1 N hM.ne'
  have hh : (((Icc 1 N).filter (primeRough P)).card : ℝ) ≤
      (M.totient : ℝ) * ((N / M : ℕ) + 1) := by exact_mod_cast hc.trans hb
  have ht : (M.totient : ℝ) * (N / M : ℕ) ≤ M.totient * ((N : ℝ) / M) :=
    mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
  change _ ≤ (M.totient : ℝ) / M * N + M.totient
  calc
    _ ≤ (M.totient : ℝ) * ((N : ℝ) / M) + M.totient := by nlinarith
    _ = _ := by ring

lemma cube_sidon_lowerDensity_le_totient_smooth_bound {A : Set ℕ}
    (hA : IsSidon ((fun n : ℕ => n ^ 3) '' A))
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) {B : ℝ}
    (hB : SmoothCubeHarmonicBound P B) :
    A.lowerDensity ≤ B * ((P.prod id).totient : ℝ) / P.prod id := by
  have hh := cube_sidon_lowerDensity_le_of_smooth_harmonic_bound hA P hP hB
    (show (0 : ℝ) ≤ (P.prod id).totient / P.prod id by positivity)
    (primeRough_prefix_totient_bound P hP)
  simpa only [mul_div_assoc] using hh

/-- The negative route is reduced to a vanishing normalized harmonic bound
on smooth cube-Sidon sets. This hypothesis is NOT proved in this file. -/
lemma no_positive_density_cube_sidon_of_normalized_smooth_bounds
    (h : ∀ ε : ℝ, 0 < ε → ∃ (P : Finset ℕ) (B : ℝ),
      (∀ p ∈ P, Nat.Prime p) ∧ SmoothCubeHarmonicBound P B ∧
      B * ((P.prod id).totient : ℝ) / P.prod id < ε) :
    ¬ (∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun n : ℕ => n ^ 3) '' A)) := by
  rintro ⟨A, _, hden, hA⟩
  obtain ⟨P, B, hP, hB, hlt⟩ := h A.lowerDensity hden
  have hh := cube_sidon_lowerDensity_le_totient_smooth_bound hA P hP hB
  linarith

#print axioms cube_sidon_lowerDensity_le_totient_smooth_bound
#print axioms no_positive_density_cube_sidon_of_normalized_smooth_bounds

#print axioms lowerDensity_le_of_harmonic_upper
#print axioms cube_sidon_lowerDensity_le_of_smooth_harmonic_bound
#print axioms no_positive_density_cube_sidon_of_vanishing_smooth_bounds


#print axioms factored_rough_decomposition
#print axioms cube_sidon_harmonic_projection

end Erdos1206
