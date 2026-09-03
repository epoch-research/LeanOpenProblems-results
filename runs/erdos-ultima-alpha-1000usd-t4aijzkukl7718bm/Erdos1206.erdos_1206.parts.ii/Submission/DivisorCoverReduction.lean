import FormalConjecturesUtil

/-! A sufficient criterion, not a settlement of the conjecture. The construction
of a divisor cover satisfying the reciprocal bound remains unproved. -/

namespace Erdos1206
open Filter Finset
open scoped Classical

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

end Erdos1206
