import Submission.SmallDifferenceExtraction

/-! An explicit finite Balog–Szemerédi–Gowers theorem. The coarse constants are
chosen for transparent polynomial dependence rather than optimization. -/
namespace Erdos3BalogSzemerediGowers
open Finset Erdos3FiniteGraphPaths Erdos3SmallDifferenceExtraction
open scoped BigOperators Classical Pointwise Combinatorics.Additive
set_option maxHeartbeats 3500000

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def sumCount (A : Finset G) (s : G) : ℕ :=
  ((A ×ˢ A).filter (fun p ↦ p.1+p.2 = s)).card

lemma sumCount_le (A : Finset G) (s : G) : sumCount A s ≤ A.card := by
  apply card_le_card_of_injOn Prod.fst
  · intro p hp
    have hp' : p ∈ A ×ˢ A ∧ p.1+p.2 = s := by simpa only [mem_coe,mem_filter] using hp
    exact (mem_product.mp hp'.1).1
  · intro p hp q hq hpq
    have hp' : p.1+p.2 = s := by
      have hh : p ∈ A ×ˢ A ∧ p.1+p.2 = s := by simpa only [mem_coe,mem_filter] using hp
      exact hh.2
    have hq' : q.1+q.2 = s := by
      have hh : q ∈ A ×ˢ A ∧ q.1+q.2 = s := by simpa only [mem_coe,mem_filter] using hq
      exact hh.2
    apply Prod.ext hpq
    rw [hpq] at hp'
    exact add_left_cancel (hp'.trans hq'.symm)

lemma sum_sumCount (A : Finset G) : (∑ s ∈ A+A, sumCount A s) = A.card^2 := by
  have hh : Set.MapsTo (fun p : G × G ↦ p.1+p.2) (↑(A ×ˢ A) : Set (G × G)) (↑(A+A) : Set G) := by
    intro p hp
    obtain ⟨h1,h2⟩ := mem_product.mp hp
    exact add_mem_add h1 h2
  simpa only [sumCount,card_product,pow_two] using (card_eq_sum_card_fiberwise hh).symm

lemma sumCount_energy (A : Finset G) : (∑ s ∈ A+A, (sumCount A s)^2) = E[A] :=
  (addEnergy_eq_sum_sq' A A).symm

lemma mean_restricted_sums (A D : Finset G) :
    (𝔼 a : A, 𝔼 b : A, edge (fun x y : A ↦ (x : G)+(y : G) ∈ D) a b) =
      ((∑ s ∈ D, sumCount A s : ℕ) : ℝ)/(A.card : ℝ)^2 := by
  let w : G → ℝ := fun x ↦ if x ∈ D then 1 else 0
  have hedge (a b : A) : edge (fun x y : A ↦ (x : G)+(y : G) ∈ D) a b = w ((a : G)+(b : G)) := by
    by_cases h : (a : G)+(b : G) ∈ D <;> simp [edge,w,h]
  have hsum : (∑ a : A, ∑ b : A, w ((a : G)+(b : G))) = ∑ a ∈ A, ∑ b ∈ A, w (a+b) := by
    calc
      _ = ∑ a ∈ A, ∑ b : A, w (a+(b : G)) := sum_coe_sort A _
      _ = _ := sum_congr rfl (fun a _ ↦ sum_coe_sort A (fun b ↦ w (a+b)))
  simp_rw [hedge]
  simp only [Fintype.expect_eq_sum_div_card,Fintype.card_coe,← sum_div]
  rw [div_div,← pow_two,hsum]
  congr 1
  have he := sum_card_fiberwise_eq_card_filter (A ×ˢ A) D (fun p : G × G ↦ p.1+p.2)
  calc
    _ = ∑ p ∈ A ×ˢ A, w (p.1+p.2) := (sum_product _ _ _).symm
    _ = (((A ×ˢ A).filter (fun p ↦ p.1+p.2 ∈ D)).card : ℝ) := by
      dsimp [w]
      exact sum_boole _ _
    _ = _ := by exact_mod_cast he.symm

/-- Popular sums have a small range while accounting for a dense graph of pairs. -/
theorem popular_sums_of_energy (A : Finset G) (hA : A.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (hE : δ*(A.card : ℝ)^3 ≤ (E[A] : ℝ)) :
    ∃ D : Finset G, (δ/2)*(D.card : ℝ) ≤ A.card ∧
      δ/2 ≤ 𝔼 a : A, 𝔼 b : A, edge (fun x y : A ↦ (x : G)+(y : G) ∈ D) a b := by
  let N : ℝ := A.card
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hA.card_pos
  let c : G → ℝ := fun s ↦ sumCount A s
  let D := (A+A).filter (fun s ↦ δ*N/2 ≤ c s)
  have hc (s : G) : 0 ≤ c s ∧ c s ≤ N :=
    ⟨by dsimp [c]; positivity,by dsimp [c,N]; exact_mod_cast sumCount_le A s⟩
  have hsum : (∑ s ∈ A+A, c s) = N^2 := by
    dsimp [c,N]
    exact_mod_cast sum_sumCount A
  have henergy : (∑ s ∈ A+A, (c s)^2) = (E[A] : ℝ) := by
    dsimp [c]
    exact_mod_cast sumCount_energy A
  have hsub : D ⊆ A+A := filter_subset _ _
  have hsumD : (∑ s ∈ D, c s) ≤ N^2 := by
    rw [← hsum]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ ↦ (hc s).1)
  have hDsmall : (δ/2)*(D.card : ℝ) ≤ N := by
    have hh : (δ*N/2)*(D.card : ℝ) ≤ ∑ s ∈ D, c s := by
      calc
        _ = ∑ _s ∈ D, δ*N/2 := by simp [mul_comm]
        _ ≤ _ := sum_le_sum (fun s hs ↦ (mem_filter.mp hs).2)
    have hx : N*((δ/2)*(D.card : ℝ)) ≤ N*N := by nlinarith
    nlinarith
  have hEupper : (E[A] : ℝ) ≤ N*(∑ s ∈ D, c s)+(δ*N/2)*N^2 := by
    rw [← henergy]
    calc
      _ ≤ ∑ s ∈ A+A, (N*(if s ∈ D then c s else 0)+(δ*N/2)*c s) := by
        apply sum_le_sum
        intro s hs
        by_cases hd : s ∈ D
        · rw [if_pos hd]
          have hx := mul_le_mul_of_nonneg_right (hc s).2 (hc s).1
          have hy : 0 ≤ (δ*N/2)*c s := by positivity
          nlinarith
        · have hcs : c s < δ*N/2 := by
            have hh := mem_filter.not.mp hd
            exact lt_of_not_ge (fun h ↦ hh ⟨hs,h⟩)
          rw [if_neg hd,mul_zero,zero_add]
          nlinarith [mul_le_mul_of_nonneg_right hcs.le (hc s).1]
      _ = _ := by
        rw [sum_add_distrib,← mul_sum,← mul_sum,hsum]
        congr 1
        rw [← sum_filter]
        congr 2
        exact filter_mem_eq_inter.trans (inter_eq_right.mpr hsub)
  have hmass : δ/2*N^2 ≤ ∑ s ∈ D, c s := by
    change δ*N^3 ≤ (E[A] : ℝ) at hE
    have hh : N*(δ/2*N^2) ≤ N*(∑ s ∈ D, c s) := by nlinarith
    nlinarith
  refine ⟨D,hDsmall,?_⟩
  rw [mean_restricted_sums]
  apply (le_div_iff₀ (by dsimp [N] at hN; positivity : (0 : ℝ) < (A.card : ℝ)^2)).mpr
  simpa only [Nat.cast_sum,c,N] using hmass

/-- Quantitative Balog–Szemerédi–Gowers with explicit polynomial losses.
The ambient abelian group need not be finite. -/
theorem balog_szemeredi_gowers (A : Finset G) (hA : A.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (hE : δ*(A.card : ℝ)^3 ≤ (E[A] : ℝ)) :
    ∃ B ⊆ A, δ/8*(A.card : ℝ) ≤ B.card ∧
      δ^9*((B-B).card : ℝ) ≤ 2097152*(A.card : ℝ) := by
  obtain ⟨D,hD,havg⟩ := popular_sums_of_energy A hA hδ hE
  obtain ⟨B,hBA,hB,hDiff⟩ := restricted_sumset_small_difference A D hA (by positivity : 0 < δ/2) havg
  refine ⟨B,hBA,?_,?_⟩
  · simpa only [show δ/2/4 = δ/8 by ring] using hB
  · have hN : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hD4 := pow_le_pow_left₀ (by positivity : 0 ≤ δ/2*(D.card : ℝ)) hD 4
    have hD4' : δ^4*(D.card : ℝ)^4 ≤ 16*(A.card : ℝ)^4 := by nlinarith only [hD4]
    have hDiff' : δ^5*(A.card : ℝ)^3*((B-B).card : ℝ) ≤ 131072*(D.card : ℝ)^4 := by
      nlinarith only [hDiff]
    have hh := mul_le_mul_of_nonneg_left hDiff' (by positivity : 0 ≤ δ^4)
    have hh' : (A.card : ℝ)^3*(δ^9*((B-B).card : ℝ)) ≤
        (A.card : ℝ)^3*(2097152*(A.card : ℝ)) := by nlinarith only [hh,hD4']
    have hN3 : (0 : ℝ) < (A.card : ℝ)^3 := by positivity
    nlinarith only [hh',hN3]

#print axioms popular_sums_of_energy
#print axioms balog_szemeredi_gowers
end Erdos3BalogSzemerediGowers
