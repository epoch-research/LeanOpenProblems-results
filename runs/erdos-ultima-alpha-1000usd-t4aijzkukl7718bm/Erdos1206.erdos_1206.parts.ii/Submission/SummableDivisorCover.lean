import FormalConjecturesUtil

/-! Sieve criteria only, not a settlement of the conjecture. A summable divisor
cover of all nontrivial cubic collisions has not been constructed. -/

namespace Erdos1206
open Filter Finset
open scoped Classical Topology

/-- Positive integers divisible by none of the forbidden divisors. -/
def divisorAvoider (B : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∀ p ∈ B, ¬ p ∣ n}

/-- Every nontrivial equality of two cube sums has a root divisible by an element of `B`. -/
def IsCubeDivisorCover (B : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < b → 0 < c → 0 < d →
    a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 → a ≠ c → a ≠ d →
    ∃ p ∈ B, p ∣ a ∨ p ∣ b ∨ p ∣ c ∨ p ∣ d

lemma divisorAvoider_cube_sidon {B : Set ℕ} (hB : IsCubeDivisorCover B) :
    IsSidon ((fun a : ℕ => a ^ 3) '' divisorAvoider B) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ heq
  by_cases hac : a = c
  · subst c
    exact Or.inl ⟨rfl, Nat.add_left_cancel heq⟩
  by_cases had : a = d
  · subst d
    exact Or.inr ⟨rfl, by omega⟩
  obtain ⟨p, hp, hpA | hpB | hpC | hpD⟩ :=
    hB a b c d ha.1 hb.1 hc.1 hd.1 heq hac had
  · exact (ha.2 p hp hpA).elim
  · exact (hb.2 p hp hpB).elim
  · exact (hc.2 p hp hpC).elim
  · exact (hd.2 p hp hpD).elim

private lemma divisorAvoider_count {B : Set ℕ} {s : ℝ}
    (hrec : ∀ N : ℕ, ∑ p ∈ (range (N + 1)).filter (· ∈ B), (1 : ℝ) / p ≤ s)
    (N : ℕ) :
    ((Set.Iio N \ divisorAvoider B).ncard : ℝ) ≤ 1 + N * s := by
  classical
  let T := (range (N + 1)).filter (· ∈ B)
  let S (p : ℕ) := (range (N + 1)).filter (fun n => n ≠ 0 ∧ p ∣ n)
  let U := T.biUnion S
  have hsub : Set.Iio N \ divisorAvoider B ⊆ ({0} : Set ℕ) ∪ (U : Set ℕ) := by
    intro n hn
    have hnN : n < N := hn.1
    by_cases hn0 : n = 0
    · exact Or.inl hn0
    · apply Or.inr
      have hnA := hn.2
      simp only [divisorAvoider, Set.mem_setOf_eq, not_and, not_forall, not_not] at hnA
      obtain ⟨p, hp, hpn⟩ := hnA (Nat.pos_of_ne_zero hn0)
      have hpN : p ≤ N := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn).trans hnN.le
      exact mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩,
        mem_filter.mpr ⟨mem_range.mpr (by omega), hn0, hpn⟩⟩
  have hc := Set.ncard_le_ncard hsub ((Set.finite_singleton 0).union U.finite_toSet)
  have hu := Set.ncard_union_le ({0} : Set ℕ) (U : Set ℕ)
  have hb : U.card ≤ ∑ p ∈ T, (S p).card := card_biUnion_le
  have heq (p : ℕ) : (S p).card = N / p := Nat.card_multiples' N p
  simp only [Set.ncard_singleton, Set.ncard_coe_finset] at hc hu
  have hn : (Set.Iio N \ divisorAvoider B).ncard ≤ 1 + ∑ p ∈ T, N / p := by
    simp_rw [heq] at hb
    omega
  have hn' : ((Set.Iio N \ divisorAvoider B).ncard : ℝ) ≤
      1 + ∑ p ∈ T, ((N / p : ℕ) : ℝ) := by exact_mod_cast hn
  have hsum : (∑ p ∈ T, ((N / p : ℕ) : ℝ)) ≤ (N : ℝ) * s := by
    calc
      _ ≤ ∑ p ∈ T, (N : ℝ) / p := sum_le_sum fun _ _ => Nat.cast_div_le
      _ = (N : ℝ) * (∑ p ∈ T, (1 : ℝ) / p) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p hp
        ring
      _ ≤ (N : ℝ) * s := mul_le_mul_of_nonneg_left (hrec N) (by positivity)
  linarith

lemma divisorAvoider_lowerDensity {B : Set ℕ} {s : ℝ}
    (hrec : ∀ N : ℕ, ∑ p ∈ (range (N + 1)).filter (· ∈ B), (1 : ℝ) / p ≤ s) :
    1 - s ≤ (divisorAvoider B).lowerDensity := by
  have hp (N : ℕ) : (1 - s) * N ≤
      (((divisorAvoider B) ∩ Set.Iio N).ncard : ℝ) + 1 := by
    have hcomp := divisorAvoider_count hrec N
    have hc : (Set.Iio N \ divisorAvoider B).ncard +
        ((divisorAvoider B) ∩ Set.Iio N).ncard = N := by
      simpa [Set.diff_inter, Nat.ncard_Iio] using
        Set.ncard_diff_add_ncard_of_subset
          (s := (divisorAvoider B) ∩ Set.Iio N) (t := Set.Iio N)
          Set.inter_subset_right
    have hc' : ((Set.Iio N \ divisorAvoider B).ncard : ℝ) +
        (((divisorAvoider B) ∩ Set.Iio N).ncard : ℝ) = N := by exact_mod_cast hc
    linarith
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  have heps : 0 < 1 - s - c := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / (1 - s - c))
  have hev : ∀ᶠ N : ℕ in atTop, c ≤ (divisorAvoider B).partialDensity Set.univ N := by
    apply eventually_atTop.mpr
    refine ⟨M + 1, fun N hN => ?_⟩
    have hN0 : 0 < N := by omega
    have hMN : (M : ℝ) < N := by exact_mod_cast (show M < N by omega)
    have hlarge := (div_lt_iff₀ heps).mp (hM.trans hMN)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (le_div_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN0)).mpr
    nlinarith [hp N]
  exact le_liminf_of_le
    (isCoboundedUnder_ge_of_le atTop (fun N => Set.partialDensity_le_one _ Set.univ N)) hev

/-- A reciprocal-small divisor cover would settle the original conjecture. -/
lemma reciprocal_divisor_cover_suffices {B : Set ℕ} {s : ℝ}
    (hcover : IsCubeDivisorCover B) (hs : s < 1)
    (hrec : ∀ N : ℕ, ∑ p ∈ (range (N + 1)).filter (· ∈ B), (1 : ℝ) / p ≤ s) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  have hd : 0 < (divisorAvoider B).lowerDensity :=
    (sub_pos.mpr hs).trans_le (divisorAvoider_lowerDensity hrec)
  refine ⟨divisorAvoider B, ?_, hd, divisorAvoider_cube_sidon hcover⟩
  by_contra hfin
  have hzero : (divisorAvoider B).lowerDensity = 0 :=
    (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
  simp [hzero] at hd


/-- Divisor closure restricted to positive divisors. -/
def PositiveDivisorClosed (A : Set ℕ) : Prop :=
  ∀ n ∈ A, ∀ m : ℕ, m ∣ n → 0 < m → m ∈ A

lemma divisorAvoider_divisorClosed (B : Set ℕ) : PositiveDivisorClosed (divisorAvoider B) := by
  intro n hn m hmn hm
  exact ⟨hm, fun p hp hpm => hn.2 p hp (hpm.trans hmn)⟩

private lemma prefix_bound_from_density {A : Set ℕ} (hA : 0 < A.lowerDensity) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ n : ℕ, δ * n ≤ ((A ∩ Set.Iio n).ncard : ℝ) + C := by
  let δ := A.lowerDensity / 2
  have hδ : 0 < δ := half_pos hA
  have hδA : δ < A.lowerDensity := half_lt_self hA
  have hev : ∀ᶠ n : ℕ in atTop, δ < A.partialDensity Set.univ n :=
    eventually_lt_of_lt_liminf hδA (isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨δ, hδ, δ * M, fun n => ?_⟩
  by_cases hn : n < M
  · have hle : (n : ℝ) ≤ M := by exact_mod_cast hn.le
    have hmul := mul_le_mul_of_nonneg_left hle hδ.le
    have hcard : (0 : ℝ) ≤ ((A ∩ Set.Iio n).ncard : ℝ) := by positivity
    linarith
  · by_cases hn0 : n = 0
    · subst n
      simpa using mul_nonneg hδ.le (Nat.cast_nonneg M)
    have hnp : 0 < n := Nat.pos_of_ne_zero hn0
    have hp := hM n (by omega)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio] at hp
    have hmul := (lt_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hnp)).mp hp
    have hC : (0 : ℝ) ≤ δ * M := by positivity
    linarith

private lemma positive_density_from_prefix {A : Set ℕ} {δ C : ℝ} (hδ : 0 < δ)
    (h : ∀ n : ℕ, δ * n ≤ ((A ∩ Set.Iio n).ncard : ℝ) + C) :
    0 < A.lowerDensity := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * C / δ)
  have hev : ∀ᶠ n : ℕ in atTop, δ / 2 ≤ A.partialDensity Set.univ n := by
    apply eventually_atTop.mpr
    refine ⟨M + 1, fun n hn => ?_⟩
    have hn0 : 0 < n := by omega
    have hMn : (M : ℝ) < n := by exact_mod_cast (show M < n by omega)
    have hC : 2 * C < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp (hM.trans hMn)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn0)).mpr
    nlinarith [h n]
  have hlim : δ / 2 ≤ A.lowerDensity :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n => Set.partialDensity_le_one A Set.univ n)) hev
  exact (half_pos hδ).trans_le hlim

private lemma strip_power_cover {A : Set ℕ} (hA : PositiveDivisorClosed A)
    {b : ℕ} (hb : 1 < b) (K : ℕ) {n : ℕ} (hn : n ∈ A) (hn0 : 0 < n) :
    b ^ K ∣ n ∨ ∃ j < K, ∃ m ∈ A, ¬ b ∣ m ∧ m ≤ n ∧ n = b ^ j * m := by
  induction K generalizing n with
  | zero => exact Or.inl (by simp)
  | succ K ih =>
    by_cases hbn : b ∣ n
    · obtain ⟨m, rfl⟩ := hbn
      have hm0 : 0 < m := by nlinarith
      have hm : m ∈ A := hA _ hn m (dvd_mul_left _ _) hm0
      rcases ih hm hm0 with h | ⟨j, hj, r, hr, hbr, hrm, heq⟩
      · apply Or.inl
        simpa [pow_succ, Nat.mul_comm] using Nat.mul_dvd_mul h (dvd_refl b)
      · apply Or.inr
        refine ⟨j + 1, by omega, r, hr, hbr, ?_, ?_⟩
        · exact hrm.trans (Nat.le_mul_of_pos_left m (by omega))
        · rw [heq, pow_succ]
          ring
    · exact Or.inr ⟨0, by omega, n, hn, hbn, le_refl _, by simp⟩

private lemma strip_power_count {A : Set ℕ} (hA : PositiveDivisorClosed A)
    (hpos : ∀ n ∈ A, 0 < n) {b : ℕ} (hb : 1 < b) (K N : ℕ) :
    (A ∩ Set.Iio N).ncard ≤
      K * ((A ∩ {n | ¬ b ∣ n}) ∩ Set.Iio N).ncard + N / b ^ K := by
  classical
  let G := A ∩ {n | ¬ b ∣ n}
  let F := (range N).filter (· ∈ G)
  let U := (range K).biUnion (fun j => F.image (fun m => b ^ j * m))
  let V := (range (N + 1)).filter (fun n => n ≠ 0 ∧ b ^ K ∣ n)
  have hF : (F : Set ℕ) = G ∩ Set.Iio N := by
    ext n
    simp only [F, mem_coe, mem_filter, mem_range, Set.mem_inter_iff, Set.mem_Iio]
    tauto
  have hsub : A ∩ Set.Iio N ⊆ ((U ∪ V : Finset ℕ) : Set ℕ) := by
    intro n hn
    have hnN : n < N := hn.2
    rcases strip_power_cover hA hb K hn.1 (hpos n hn.1) with h | ⟨j, hj, m, hm, hbm, hmn, heq⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), (hpos n hn.1).ne', h⟩
    · apply mem_union_left
      exact mem_biUnion.mpr ⟨j, mem_range.mpr hj, mem_image.mpr
        ⟨m, mem_filter.mpr ⟨mem_range.mpr (by omega), hm, hbm⟩, heq.symm⟩⟩
  have hc := Set.ncard_le_ncard hsub (U ∪ V).finite_toSet
  have hu := card_union_le U V
  have hbnd : U.card ≤ K * F.card := by
    calc
      U.card ≤ ∑ j ∈ range K, (F.image (fun m => b ^ j * m)).card := card_biUnion_le
      _ ≤ ∑ _j ∈ range K, F.card := sum_le_sum fun _ _ => card_image_le
      _ = K * F.card := by simp
  have hV : V.card = N / b ^ K := Nat.card_multiples' N (b ^ K)
  have hFcard : F.card = (G ∩ Set.Iio N).ncard := by
    rw [← hF, Set.ncard_coe_finset]
  simp only [Set.ncard_coe_finset] at hc
  rw [hFcard] at hbnd
  change (A ∩ Set.Iio N).ncard ≤ K * (G ∩ Set.Iio N).ncard + N / b ^ K
  omega

/-- For a divisor-closed set of positive lower density, deleting the multiples of
one integer other than `0` or `1` preserves positive lower density. -/
lemma remove_multiples_preserves_positive_density {A : Set ℕ}
    (hA : PositiveDivisorClosed A) (hpos : ∀ n ∈ A, 0 < n)
    (hden : 0 < A.lowerDensity) {b : ℕ} (hb : 1 < b) :
    0 < (A ∩ {n | ¬ b ∣ n}).lowerDensity := by
  obtain ⟨δ, hδ, C, hpre⟩ := prefix_bound_from_density hden
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / δ)
  have hK0 : 0 < K := by
    have : (0 : ℝ) < K := lt_trans (by positivity : (0 : ℝ) < 2 / δ) hK
    exact_mod_cast this
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hpowall : ∀ k : ℕ, k + 1 ≤ b ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      nlinarith
  have hpow := hpowall K
  have hq : (0 : ℝ) < (b ^ K : ℕ) := by positivity
  have hsmall : (1 : ℝ) / (b ^ K : ℕ) ≤ δ / 2 := by
    have hKδ := (div_lt_iff₀ hδ).mp hK
    have hpowr : (K : ℝ) + 1 ≤ (b ^ K : ℕ) := by exact_mod_cast hpow
    apply (div_le_iff₀ hq).mpr
    nlinarith
  apply positive_density_from_prefix (δ := (δ / 2) / K) (C := C / K) (by positivity)
  intro N
  have hc := strip_power_count hA hpos hb K N
  have hcr : ((A ∩ Set.Iio N).ncard : ℝ) ≤
      K * (((A ∩ {n | ¬ b ∣ n}) ∩ Set.Iio N).ncard : ℝ) +
      ((N / b ^ K : ℕ) : ℝ) := by exact_mod_cast hc
  have hdiv : ((N / b ^ K : ℕ) : ℝ) ≤ (N : ℝ) / (b ^ K : ℕ) := Nat.cast_div_le
  have hsmallN := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg N)
  have hh : (δ / 2) * N ≤
      K * (((A ∩ {n | ¬ b ∣ n}) ∩ Set.Iio N).ncard : ℝ) + C := by
    have hsmallN' : (N : ℝ) / (b ^ K : ℕ) ≤ (δ / 2) * N := by
      simpa only [mul_one_div, mul_comm] using hsmallN
    nlinarith [hpre N]
  convert div_le_div_of_nonneg_right hh hKr.le using 1 <;> field_simp


lemma remove_finite_divisors_preserves_positive_density {A : Set ℕ}
    (hA : PositiveDivisorClosed A) (hpos : ∀ n ∈ A, 0 < n)
    (hden : 0 < A.lowerDensity) (S : Finset ℕ) (hS : ∀ b ∈ S, 1 < b) :
    0 < (A ∩ {n | ∀ b ∈ S, ¬ b ∣ n}).lowerDensity := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty => intro hS; simpa using hden
  | @insert b S hbS ih =>
    intro hS
    let A' := A ∩ {n | ∀ p ∈ S, ¬ p ∣ n}
    have hd' : PositiveDivisorClosed A' := by
      intro n hn m hmn hm
      exact ⟨hA n hn.1 m hmn hm, fun p hp hpm => hn.2 p hp (hpm.trans hmn)⟩
    have hpos' : ∀ n ∈ A', 0 < n := fun n hn => hpos n hn.1
    have hden' : 0 < A'.lowerDensity := ih (fun p hp => hS p (mem_insert_of_mem hp))
    have hh := remove_multiples_preserves_positive_density hd' hpos' hden'
      (hS b (mem_insert_self _ _))
    have heq : A' ∩ {n | ¬ b ∣ n} = A ∩ {n | ∀ p ∈ insert b S, ¬ p ∣ n} := by
      ext n
      simp [A', and_left_comm, and_comm]
    rwa [heq] at hh

/-- Only a small reciprocal tail is needed; a finite initial part can be handled
by divisor closure. -/
lemma divisorAvoider_positive_density_of_small_tail {B : Set ℕ}
    (h1 : 1 ∉ B) (M : ℕ)
    (htail : ∀ N : ℕ, ∑ p ∈ (range (N + 1)).filter (fun p => p ∈ B ∧ M < p),
      (1 : ℝ) / p ≤ 1 / 2) :
    0 < (divisorAvoider B).lowerDensity := by
  classical
  let T : Set ℕ := {p | p ∈ B ∧ M < p}
  let S := (range (M + 1)).filter (fun p => p ∈ B ∧ 0 < p)
  have hT : 0 < (divisorAvoider T).lowerDensity :=
    (by norm_num : (0 : ℝ) < 1 - 1 / 2).trans_le (divisorAvoider_lowerDensity (B := T) (s := 1 / 2) (by
      intro N
      calc
        _ = ∑ p ∈ (range (N + 1)).filter (fun p => p ∈ B ∧ M < p), (1 : ℝ) / p := by
          apply sum_congr
          · ext p
            simp [T]
          · intro p hp
            rfl
        _ ≤ 1 / 2 := htail N))
  have hS : ∀ b ∈ S, 1 < b := by
    intro b hb
    have hh := (mem_filter.mp hb).2
    have hb1 : b ≠ 1 := fun heq => h1 (heq ▸ hh.1)
    omega
  have hd := remove_finite_divisors_preserves_positive_density
    (divisorAvoider_divisorClosed T) (fun _ hn => hn.1) hT S hS
  have heq : divisorAvoider T ∩ {n | ∀ b ∈ S, ¬ b ∣ n} = divisorAvoider B := by
    ext n
    constructor
    · rintro ⟨hnT, hnS⟩
      refine ⟨hnT.1, fun p hp hpn => ?_⟩
      by_cases hpM : p ≤ M
      · have hp0 := Nat.pos_of_dvd_of_pos hpn hnT.1
        exact hnS p (mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hp0⟩) hpn
      · exact hnT.2 p ⟨hp, by omega⟩ hpn
    · intro hn
      exact ⟨⟨hn.1, fun p hp => hn.2 p hp.1⟩,
        fun p hp => hn.2 p (mem_filter.mp hp).2.1⟩
  rwa [heq] at hd


lemma small_reciprocal_tail_of_summable {B : Set ℕ}
    (hB : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ) / n else 0)) :
    ∃ M : ℕ, ∀ N : ℕ,
      ∑ p ∈ (range (N + 1)).filter (fun p => p ∈ B ∧ M < p), (1 : ℝ) / p ≤ 1 / 2 := by
  classical
  let f : ℕ → ℝ := fun n => if n ∈ B then 1 / n else 0
  have hf : Summable f := hB
  have hf0 (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have ht : Tendsto (fun M : ℕ => ∑ p ∈ range M, f p) atTop (𝓝 (∑' p, f p)) :=
    hf.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ M : ℕ in atTop, (∑' p, f p) - 1 / 2 < ∑ p ∈ range M, f p :=
    ht.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨M, hM⟩ := hev.exists
  refine ⟨M, fun N => ?_⟩
  let S := (range (N + 1)).filter (fun p => p ∈ B ∧ M < p)
  have hdis : Disjoint (range M) S := by
    apply disjoint_left.mpr
    intro p hp hs
    have hpM := mem_range.mp hp
    have hMp := (mem_filter.mp hs).2.2
    omega
  have hs : (∑ p ∈ range M, f p) + (∑ p ∈ S, f p) ≤ ∑' p, f p := by
    rw [← sum_union hdis]
    exact hf.sum_le_tsum _ (fun p _ => hf0 p)
  have heq : (∑ p ∈ S, f p) = ∑ p ∈ S, (1 : ℝ) / p := by
    apply sum_congr rfl
    intro p hp
    simp only [f, if_pos (mem_filter.mp hp).2.1]
  change (∑ p ∈ S, (1 : ℝ) / p) ≤ 1 / 2
  rw [heq] at hs
  linarith

/-- A reciprocal-summable forbidden-divisor set omitting `1` leaves positive
lower density, even if its reciprocal sum exceeds `1`. -/
lemma divisorAvoider_positive_density_of_summable {B : Set ℕ} (h1 : 1 ∉ B)
    (hB : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ) / n else 0)) :
    0 < (divisorAvoider B).lowerDensity := by
  obtain ⟨M, hM⟩ := small_reciprocal_tail_of_summable hB
  exact divisorAvoider_positive_density_of_small_tail h1 M hM

/-- A summable divisor cover omitting `1` would settle the original conjecture.
The existence of such a cover is not established here. -/
lemma summable_divisor_cover_suffices {B : Set ℕ} (hcover : IsCubeDivisorCover B)
    (h1 : 1 ∉ B)
    (hB : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ) / n else 0)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  have hd := divisorAvoider_positive_density_of_summable h1 hB
  refine ⟨divisorAvoider B, ?_, hd, divisorAvoider_cube_sidon hcover⟩
  by_contra hfin
  have hzero : (divisorAvoider B).lowerDensity = 0 :=
    (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
  simp [hzero] at hd

end Erdos1206
