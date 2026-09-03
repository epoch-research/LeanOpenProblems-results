import FormalConjecturesUtil

/-!
A conditional route to Erdős 773: subpower-loss square-scale amplification is
actually equivalent to the desired bound. This file does not establish the
amplification hypothesis for the square-Sidon maximum.
-/
namespace Erdos773.SubpowerAmplification
open Filter Finset
open scoped Topology
set_option maxHeartbeats 1000000

/-- A monotone function with a slightly stronger lower bound at square indices
    inherits the desired exponent at every sufficiently large index. -/
lemma interpolate_square_lower (f : ℕ → ℝ) (hf : Monotone f)
    (β ρ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hρ : 0 < ρ)
    (h : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (2 * β + ρ) ≤ f (n ^ 2)) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ β ≤ f N := by
  have h4 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ (n : ℝ) ^ ρ :=
    (tendsto_atTop.mp ((tendsto_rpow_atTop hρ).comp
      tendsto_natCast_atTop_atTop)) 4
  obtain ⟨K, hK⟩ := eventually_atTop.mp (h.and (h4.and (eventually_ge_atTop 1)))
  refine eventually_atTop.mpr ⟨K ^ 2, fun N hN => ?_⟩
  let s := Nat.sqrt N
  have hKs : K ≤ s := Nat.le_sqrt'.mpr hN
  obtain ⟨hlo, hfour, hs⟩ := hK s hKs
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hupper : (N : ℝ) ≤ 4 * (s : ℝ) ^ 2 := by
    have hn := Nat.lt_succ_sqrt' N
    have hn' : (N : ℝ) < ((s : ℝ) + 1) ^ 2 := by exact_mod_cast hn
    nlinarith
  have h4β : (4 : ℝ) ^ β ≤ 4 := by
    calc
      _ ≤ (4 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
      _ = _ := Real.rpow_one _
  calc
    (N : ℝ) ^ β ≤ (4 * (s : ℝ) ^ 2) ^ β :=
      Real.rpow_le_rpow (by positivity) hupper hβ0
    _ = (4 : ℝ) ^ β * (s : ℝ) ^ (2 * β) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      rw [← Real.rpow_natCast_mul hs0.le 2 β]
      norm_num
    _ ≤ 4 * (s : ℝ) ^ (2 * β) :=
      mul_le_mul_of_nonneg_right h4β (Real.rpow_nonneg hs0.le _)
    _ ≤ (s : ℝ) ^ ρ * (s : ℝ) ^ (2 * β) :=
      mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hs0.le _)
    _ = (s : ℝ) ^ (2 * β + ρ) := by rw [Real.rpow_add hs0]; ring
    _ ≤ f (s ^ 2) := hlo
    _ ≤ f N := hf (Nat.sqrt_le' N)

def NearLinear (f : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - ε) ≤ f N

def SubpowerAmplifies (f : ℕ → ℝ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ (1 - δ) * f N ≤ f (N ^ 2)

lemma improve_gap (f : ℕ → ℝ) (hf : Monotone f)
    (hamp : SubpowerAmplifies f) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - ε) ≤ f N) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - (3 / 4) * ε) ≤ f N := by
  apply interpolate_square_lower f hf (1 - (3 / 4) * ε) (ε / 4)
    (by linarith) (by linarith) (by linarith)
  filter_upwards [h, hamp (ε / 4) (by linarith), eventually_ge_atTop 1] with N hlo hg hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    (N : ℝ) ^ (2 * (1 - (3 / 4) * ε) + ε / 4) =
        (N : ℝ) ^ (1 - ε / 4) * (N : ℝ) ^ (1 - ε) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ (1 - ε / 4) * f N :=
      mul_le_mul_of_nonneg_left hlo (Real.rpow_nonneg hN0.le _)
    _ ≤ f (N ^ 2) := hg

lemma nearLinear_of_subpowerAmplifies (f : ℕ → ℝ) (hf : Monotone f)
    (hone : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ f N)
    (hamp : SubpowerAmplifies f) : NearLinear f := by
  have hiter (k : ℕ) :
      ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - (3 / 4 : ℝ) ^ k) ≤ f N := by
    induction k with
    | zero => simpa using hone
    | succ k ih =>
      have hpos : (0 : ℝ) < (3 / 4 : ℝ) ^ k := by positivity
      have hone' : (3 / 4 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hh := improve_gap f hf hamp ((3 / 4 : ℝ) ^ k) hpos hone' ih
      simpa only [pow_succ', mul_comm (3 / 4 : ℝ)] using hh
  intro ε hε
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
  obtain ⟨k, hk⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  filter_upwards [hiter k, eventually_ge_atTop 1] with N hlo hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hlo

lemma subpowerAmplifies_of_nearLinear (f : ℕ → ℝ)
    (hupper : ∀ N : ℕ, f N ≤ N) (h : NearLinear f) :
    SubpowerAmplifies f := by
  intro δ hδ
  obtain ⟨K, hK⟩ := eventually_atTop.mp (h (δ / 2) (by linarith))
  filter_upwards [eventually_ge_atTop (max K 1)] with N hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hKN : K ≤ N := (le_max_left _ _).trans hN
  have hsq := hK (N ^ 2) (by nlinarith)
  calc
    (N : ℝ) ^ (1 - δ) * f N ≤ (N : ℝ) ^ (1 - δ) * N :=
      mul_le_mul_of_nonneg_left (hupper N) (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ (2 - δ) := by
      calc
        _ = (N : ℝ) ^ ((1 - δ) + 1) := by
          simpa using (Real.rpow_add hN0 (1 - δ) 1).symm
        _ = _ := by congr 1; ring
    _ = ((N ^ 2 : ℕ) : ℝ) ^ (1 - δ / 2) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul hN0.le 2 (1 - δ / 2)]
      congr 1
      norm_num
      ring
    _ ≤ f (N ^ 2) := hsq

lemma nearLinear_iff_subpowerAmplifies (f : ℕ → ℝ) (hf : Monotone f)
    (hone : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ f N)
    (hupper : ∀ N : ℕ, f N ≤ N) :
    NearLinear f ↔ SubpowerAmplifies f :=
  ⟨subpowerAmplifies_of_nearLinear f hupper,
    nearLinear_of_subpowerAmplifies f hf hone⟩

private lemma maxSidon_mono {A B : Finset ℕ} (h : A ⊆ B) :
    Finset.maxSidonSubsetCard A ≤ Finset.maxSidonSubsetCard B := by
  apply Finset.sup_mono
  intro S hS
  obtain ⟨hSA, hSidon⟩ := Finset.mem_filter.mp hS
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
    ((Finset.mem_powerset.mp hSA).trans h), hSidon⟩

private lemma maxSidon_le_card (A : Finset ℕ) :
    Finset.maxSidonSubsetCard A ≤ A.card := by
  apply Finset.sup_le
  intro S hS
  exact Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)

noncomputable def maxSquareSidon (N : ℕ) : ℝ :=
  Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2))

lemma maxSquareSidon_mono : Monotone maxSquareSidon := by
  intro N M hNM
  apply Nat.cast_le.mpr
  apply maxSidon_mono
  apply Finset.image_subset_image
  intro n hn
  obtain ⟨h1, hN⟩ := Finset.mem_Icc.mp hn
  exact Finset.mem_Icc.mpr ⟨h1, hN.trans hNM⟩

lemma maxSquareSidon_le (N : ℕ) : maxSquareSidon N ≤ N := by
  dsimp [maxSquareSidon]
  apply Nat.cast_le.mpr
  calc
    _ ≤ ((Icc 1 N).image (fun n : ℕ => n ^ 2)).card := maxSidon_le_card _
    _ ≤ (Icc 1 N).card := Finset.card_image_le
    _ = N := by simp

lemma one_le_maxSquareSidon (N : ℕ) (hN : 1 ≤ N) : 1 ≤ maxSquareSidon N := by
  have hsub : ({1} : Finset ℕ) ⊆ (Icc 1 N).image (fun n : ℕ => n ^ 2) := by
    intro x hx
    have hx' : x = 1 := by simpa using hx
    subst x
    exact mem_image.mpr ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩, by simp⟩
  have hSidon : IsSidon (({1} : Finset ℕ) : Set ℕ) := by
    intro a ha c hc b hb d hd he
    simp only [mem_coe, mem_singleton] at ha hc hb hd
    subst a; subst b; subst c; subst d
    simp
  have hmem : ({1} : Finset ℕ) ∈
      (((Icc 1 N).image (fun n : ℕ => n ^ 2)).powerset.filter
        (fun S : Finset ℕ => IsSidon (S : Set ℕ))) :=
    mem_filter.mpr ⟨mem_powerset.mpr hsub, hSidon⟩
  have hh := Finset.le_sup (f := Finset.card) hmem
  simp only [Finset.card_singleton] at hh
  dsimp [maxSquareSidon, Finset.maxSidonSubsetCard]
  exact_mod_cast hh

/-- An exact reformulation, not a proof of either side. The cardinality in
    both propositions is the actual maximum for the first N squares. -/
theorem square_sidon_iff_subpower_amplification :
    (∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ)) ↔
    (∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - δ) *
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ) ≤
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 (N ^ 2))) : ℝ)) := by
  change NearLinear maxSquareSidon ↔ SubpowerAmplifies maxSquareSidon
  apply nearLinear_iff_subpowerAmplifies _ maxSquareSidon_mono
    _ maxSquareSidon_le
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact one_le_maxSquareSidon N hN

#print axioms square_sidon_iff_subpower_amplification
#print axioms interpolate_square_lower
#print axioms nearLinear_iff_subpowerAmplifies
end Erdos773.SubpowerAmplification
