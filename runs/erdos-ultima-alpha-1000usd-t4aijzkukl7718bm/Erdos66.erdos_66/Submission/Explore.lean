import FormalConjecturesUtil

/-!
# Partial reductions for Erdős Problem 66

These lemmas establish necessary conditions and invariance under finite additions.
They do not prove or disprove the conjecture in `Submission/Spec.lean`.
-/

namespace Erdos66Explore
open Filter AdditiveCombinatorics
open scoped Topology

lemma limit_nonneg {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    0 ≤ c := by
  apply ge_of_tendsto h
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))

lemma limit_pos {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    0 < c := lt_of_le_of_ne (limit_nonneg h) (Ne.symm hc)

lemma sumRep_eventually_zero_of_finite {A : Set ℕ} (hA : A.Finite) :
    ∀ᶠ n in atTop, sumRep A n = 0 := by
  classical
  obtain ⟨M, hM⟩ := hA.bddAbove
  filter_upwards [eventually_ge_atTop (2 * M + 1)] with n hn
  rw [sumRep_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp hm
  have he := Finset.mem_antidiagonal.mp hp
  have h₁ := hM hm.1
  have h₂ := hM hm.2
  omega

lemma finite_limit_zero {A : Set ℕ} (hA : A.Finite) :
    Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [sumRep_eventually_zero_of_finite hA] with n hn
  simp only [hn, Nat.cast_zero, zero_div]

lemma witness_infinite {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    A.Infinite := by
  intro hA
  exact hc (tendsto_nhds_unique h (finite_limit_zero hA))

lemma sumRep_tendsto_atTop {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (sumRep A) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hm := h.pos_mul_atTop (limit_pos hc h) hlog
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hn'))

lemma eventually_sum_of_two {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∀ᶠ n in atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n := by
  classical
  filter_upwards [(sumRep_tendsto_atTop hc h).eventually_ge_atTop 1] with n hn
  rw [sumRep_def] at hn
  obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp (show 0 < _ from hn)
  simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hab
  exact ⟨a, hab.2.1, b, hab.2.2, hab.1⟩

lemma sumRep_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    sumRep A n ≤ sumRep B n := by
  classical
  simp only [sumRep_def]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hAB hp.2.1, hAB hp.2.2⟩

lemma sumRep_insert_le (A : Set ℕ) (a n : ℕ) :
    sumRep (insert a A) n ≤ sumRep A n + 2 := by
  classical
  let S := (Finset.antidiagonal n).filter (fun p : ℕ × ℕ ↦ p.1 ∈ A ∧ p.2 ∈ A)
  have hs : (Finset.antidiagonal n).filter
      (fun p : ℕ × ℕ ↦ p.1 ∈ insert a A ∧ p.2 ∈ insert a A) ⊆
      S ∪ {(a, n - a), (n - a, a)} := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_insert_iff] at hp
    by_cases h₁ : p.1 ∈ A
    · by_cases h₂ : p.2 ∈ A
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_antidiagonal.mpr hp.1, h₁, h₂⟩)
      · have he₂ : p.2 = a := hp.2.2.resolve_right h₂
        have he₁ : p.1 = n - a := by omega
        apply Finset.mem_union_right
        simp [he₁, he₂, Prod.ext_iff]
    · have he₁ : p.1 = a := hp.2.1.resolve_right h₁
      have he₂ : p.2 = n - a := by omega
      apply Finset.mem_union_right
      simp [he₁, he₂, Prod.ext_iff]
  calc
    sumRep (insert a A) n ≤ (S ∪ {(a, n - a), (n - a, a)}).card := by
      rw [sumRep_def]
      apply Finset.card_le_card
      intro p hp
      apply hs
      simpa only [Finset.mem_filter] using hp
    _ ≤ S.card + ({(a, n - a), (n - a, a)} : Finset (ℕ × ℕ)).card :=
      Finset.card_union_le _ _
    _ ≤ S.card + 2 := Nat.add_le_add_left Finset.card_le_two _
    _ = sumRep A n + 2 := by rw [sumRep_def]

lemma limit_insert {A : Set ℕ} {c : ℝ} (a : ℕ)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ (sumRep (insert a A) n : ℝ) / Real.log n) atTop (𝓝 c) := by
  have hz : Tendsto (fun n : ℕ ↦ (2 : ℝ) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hu := h.add hz
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h hu
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hn))
    exact_mod_cast sumRep_mono (Set.subset_insert a A) n
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hn))
    exact_mod_cast sumRep_insert_le A a n

lemma limit_union_finite {A B : Set ℕ} {c : ℝ} (hB : B.Finite)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ (sumRep (A ∪ B) n : ℝ) / Real.log n) atTop (𝓝 c) := by
  induction B, hB using Set.Finite.induction_on with
  | empty => simpa only [Set.union_empty] using h
  | @insert a B ha hB ih =>
    simpa only [Set.union_insert] using limit_insert a ih

lemma progression_sumRep_lower {A : Set ℕ} (a d : ℕ) (hd : 0 < d)
    (hA : ∀ k : ℕ, a + d * k ∈ A) (n : ℕ) :
    n + 1 ≤ sumRep A (2 * a + d * n) := by
  classical
  let f : ℕ → ℕ × ℕ := fun k ↦ (a + d * k, a + d * (n - k))
  have hf : Function.Injective f := by
    intro i j hij
    have he : a + d * i = a + d * j := congrArg Prod.fst hij
    exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel he)
  have hs : (Finset.range (n + 1)).image f ⊆
      (Finset.antidiagonal (2 * a + d * n)).filter
        (fun p : ℕ × ℕ ↦ p.1 ∈ A ∧ p.2 ∈ A) := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    have hk' : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_antidiagonal.mpr ?_, hA k, hA (n - k)⟩
    change a + d * k + (a + d * (n - k)) = 2 * a + d * n
    rw [Nat.mul_sub_left_distrib]
    have hm : d * k ≤ d * n := Nat.mul_le_mul_left d hk'
    omega
  calc
    n + 1 = (Finset.range (n + 1)).card := (Finset.card_range _).symm
    _ = ((Finset.range (n + 1)).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ ≤ sumRep A (2 * a + d * n) := by
      rw [sumRep_def]
      apply Finset.card_le_card
      intro p hp
      exact hs hp

lemma representation_div_self_limit_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ (sumRep A n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hm := h.mul hlog
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hl : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hn').ne'
  field_simp

lemma no_infinite_progression_of_finite_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c))
    (a d : ℕ) (hd : 0 < d) : ¬ ∀ k : ℕ, a + d * k ∈ A := by
  intro hA
  have hmul (n : ℕ) : n ≤ d * n := by
    simpa only [one_mul] using Nat.mul_le_mul_right n (show 1 ≤ d from hd)
  have ht : Tendsto (fun n : ℕ ↦ 2 * a + d * n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ (hmul n).trans (Nat.le_add_left _ _)) tendsto_id
  let C := 2 * a + d + 1
  have hz := ((representation_div_self_limit_zero h).comp ht).const_mul (C : ℝ)
  simp only [mul_zero] at hz
  have hb : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ (C : ℝ) *
        ((sumRep A (2 * a + d * n) : ℝ) / ((2 * a + d * n : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < ((2 * a + d * n : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 2 * a + d * n by have := hmul n; omega)
    have hc : 2 * a + d * n ≤ C * (n + 1) := by dsimp [C]; nlinarith
    have hb := hc.trans (Nat.mul_le_mul_left C (progression_sumRep_lower a d hd hA n))
    rw [← mul_div_assoc, le_div_iff₀ hp, one_mul]
    exact_mod_cast hb
  have hf : (1 : ℝ) ≤ 0 := ge_of_tendsto hz hb
  norm_num at hf

lemma witness_not_eventually_periodic {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ¬ ∃ N d : ℕ, 0 < d ∧ ∀ n ≥ N, (n ∈ A ↔ n + d ∈ A) := by
  rintro ⟨N, d, hd, hper⟩
  obtain ⟨a, ha, hNa⟩ := (witness_infinite hc h).exists_gt N
  apply no_infinite_progression_of_finite_limit h a d hd
  intro k
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    have hNk : N ≤ a + d * k := by omega
    have hh := (hper (a + d * k) hNk).mp ih
    simpa only [Nat.mul_succ, ← Nat.add_assoc] using hh

end Erdos66Explore
