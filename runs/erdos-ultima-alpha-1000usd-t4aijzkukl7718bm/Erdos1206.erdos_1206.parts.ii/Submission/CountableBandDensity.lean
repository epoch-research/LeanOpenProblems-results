import Submission.Compactness

/-!
A uniform second-moment criterion for imposing countably many score bands on
an arbitrary positive-lower-density source. No Sidonness is asserted.
-/
namespace Erdos1206.CountableBandDensity
open Finset
open scoped Classical

/-- A summable family of UNIFORM second-moment bounds controls an infinite
union in every finite prefix. No exchange of asymptotic densities is used. -/
theorem bad_union_card_le (f : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    (hc : ∀ j, 0 ≤ c j) (hcs : Summable c)
    (hm : ∀ j N : ℕ, (∑ n ∈ Icc 1 N, (f j n)^2) ≤ (N:ℝ)*c j) (N : ℕ) :
    (((Icc 1 N).filter (fun n => ∃ j, 1 < |f j n|)).card:ℝ) ≤
      (N:ℝ)*∑' j, c j := by
  classical
  let B := (Icc 1 N).filter (fun n => ∃ j, 1 < |f j n|)
  have hex (n : ℕ) : ∃ j, n ∈ B → 1 < |f j n| := by
    by_cases hn : n ∈ B
    · obtain ⟨j,hj⟩ := (mem_filter.mp hn).2
      exact ⟨j,fun _ => hj⟩
    · exact ⟨0,fun hh => (hn hh).elim⟩
  choose idx hidx using hex
  let J := B.image idx
  have hfiber (j : ℕ) : ((B.filter (fun n => idx n=j)).card:ℝ) ≤ (N:ℝ)*c j := by
    let U := B.filter (fun n => idx n=j)
    have hsub : U ⊆ Icc 1 N := fun n hn => (mem_filter.mp (mem_filter.mp hn).1).1
    calc
      _ = ∑ _n ∈ U, (1:ℝ) := by simp [U]
      _ ≤ ∑ n ∈ U, (f j n)^2 := by
        apply sum_le_sum
        intro n hn
        have hh := hidx n (mem_filter.mp hn).1
        rw [(mem_filter.mp hn).2] at hh
        have hsq := (sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg (f j n))).mpr hh
        simpa using hsq.le
      _ ≤ ∑ n ∈ Icc 1 N, (f j n)^2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hm j N
  have he : (B.card:ℝ) = ∑ j ∈ J, ((B.filter (fun n => idx n=j)).card:ℝ) := by
    have hh := sum_fiberwise_of_maps_to
      (fun n hn => mem_image.mpr ⟨n,hn,rfl⟩ : ∀ n ∈ B, idx n ∈ J)
      (fun _ : ℕ => (1:ℝ))
    simpa using hh.symm
  change (B.card:ℝ) ≤ _
  calc
    _ = _ := he
    _ ≤ ∑ j ∈ J, (N:ℝ)*c j := sum_le_sum (fun j _ => hfiber j)
    _ = (N:ℝ)*∑ j ∈ J, c j := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hcs.sum_le_tsum J (fun j _ => hc j)) (by positivity)

/-- Score-band intersections preserve positive lower density when their
uniform second-moment costs sum to less than the source's prefix density. -/
theorem lowerDensity_pos_of_prefix (S : Set ℕ) (f : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    {δ C : ℝ} (hpos : ∀ n ∈ S, 0 < n)
    (hpre : ∀ N : ℕ, δ*(N:ℝ) ≤ ((S ∩ Set.Iio N).ncard:ℝ)+C)
    (hc : ∀ j, 0 ≤ c j) (hcs : Summable c)
    (hm : ∀ j N : ℕ, (∑ n ∈ Icc 1 N, (f j n)^2) ≤ (N:ℝ)*c j)
    (hcost : ∑' j, c j < δ) :
    0 < ({n | n ∈ S ∧ ∀ j, |f j n| ≤ 1} : Set ℕ).lowerDensity := by
  classical
  let A : Set ℕ := {n | n ∈ S ∧ ∀ j, |f j n| ≤ 1}
  apply positive_lowerDensity_of_prefix_bound (δ := δ-∑' j, c j) (C := C)
    (sub_pos.mpr hcost)
  intro N
  let U := (range N).filter (fun n => n ∈ S)
  let G := U.filter (fun n => ∀ j, |f j n| ≤ 1)
  let B := U.filter (fun n => ¬ ∀ j, |f j n| ≤ 1)
  have hcard : G.card+B.card=U.card := card_filter_add_card_filter_not (s := U) _
  have hBU : B ⊆ (Icc 1 N).filter (fun n => ∃ j, 1 < |f j n|) := by
    intro n hn
    obtain ⟨hn,hbad⟩ := mem_filter.mp hn
    obtain ⟨hnN,hnS⟩ := mem_filter.mp hn
    have hn0 := hpos n hnS
    have hbad' : ∃ j, 1 < |f j n| := by push_neg at hbad; exact hbad
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hn0,(mem_range.mp hnN).le⟩,hbad'⟩
  have hB' : (B.card:ℝ) ≤ (((Icc 1 N).filter (fun n => ∃ j, 1 < |f j n|)).card:ℝ) := by
    exact_mod_cast card_le_card hBU
  have hB : (B.card:ℝ) ≤ (N:ℝ)*∑' j, c j :=
    hB'.trans (bad_union_card_le f c hc hcs hm N)
  have hU : S ∩ Set.Iio N = (U : Set ℕ) := by
    ext n
    simp only [Set.mem_inter_iff,Set.mem_Iio,U,Finset.mem_coe,mem_filter,mem_range]
    tauto
  have hG : A ∩ Set.Iio N = (G : Set ℕ) := by
    ext n
    simp only [A,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_Iio,G,U,
      Finset.mem_coe,mem_filter,mem_range]
    tauto
  have hh := hpre N
  rw [hU,Set.ncard_coe_finset] at hh
  change (δ-∑' j, c j)*(N:ℝ) ≤ ((A ∩ Set.Iio N).ncard:ℝ)+C
  rw [hG,Set.ncard_coe_finset]
  have hcardR : (G.card:ℝ)+(B.card:ℝ)=(U.card:ℝ) := by exact_mod_cast hcard
  nlinarith

#print axioms bad_union_card_le
#print axioms lowerDensity_pos_of_prefix
end Erdos1206.CountableBandDensity
