import FormalConjecturesUtil

/-! A quantitative dense-graph path lemma, used for a Balog–Szemerédi–Gowers
extraction. No inverse theorem or original-conjecture conclusion is asserted. -/
namespace Erdos3FiniteGraphPaths
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

noncomputable def edge (R : I → J → Prop) (i : I) (j : J) : ℝ := if R i j then 1 else 0
noncomputable def codegree (R : I → J → Prop) (i k : I) : ℝ := 𝔼 j, edge R i j*edge R k j
noncomputable def neighborMass (R : I → J → Prop) (j : J) : ℝ := 𝔼 i, edge R i j
noncomputable def badDegree (R : I → J → Prop) (θ : ℝ) (j : J) (i : I) : ℝ :=
  𝔼 k, edge R k j*(if codegree R i k < θ then 1 else 0)
noncomputable def badMass (R : I → J → Prop) (θ : ℝ) (j : J) : ℝ :=
  𝔼 i, edge R i j*badDegree R θ j i

lemma edge_nonneg (R : I → J → Prop) (i : I) (j : J) : 0 ≤ edge R i j := by
  unfold edge; split_ifs <;> norm_num
lemma edge_le_one (R : I → J → Prop) (i : I) (j : J) : edge R i j ≤ 1 := by
  unfold edge; split_ifs <;> norm_num
lemma codegree_nonneg (R : I → J → Prop) (i k : I) : 0 ≤ codegree R i k :=
  expect_nonneg (fun j _ ↦ mul_nonneg (edge_nonneg R i j) (edge_nonneg R k j))
lemma codegree_symm (R : I → J → Prop) (i k : I) : codegree R i k = codegree R k i := by
  unfold codegree
  simp only [mul_comm]
lemma badDegree_nonneg (R : I → J → Prop) (θ : ℝ) (j : J) (i : I) : 0 ≤ badDegree R θ j i := by
  apply expect_nonneg
  intro k _
  split_ifs
  · simpa only [mul_one] using edge_nonneg R k j
  · simp only [mul_zero,le_refl]
lemma badMass_nonneg (R : I → J → Prop) (θ : ℝ) (j : J) : 0 ≤ badMass R θ j :=
  expect_nonneg (fun i _ ↦ mul_nonneg (edge_nonneg R i j) (badDegree_nonneg R θ j i))

lemma mean_badMass_le (R : I → J → Prop) {θ : ℝ} (hθ : 0 ≤ θ) :
    (𝔼 j, badMass R θ j) ≤ θ := by
  have he : (𝔼 j, badMass R θ j) =
      𝔼 i, 𝔼 k, codegree R i k*(if codegree R i k < θ then 1 else 0) := by
    unfold badMass badDegree
    simp_rw [mul_expect]
    rw [expect_comm]
    apply expect_congr rfl
    intro i _
    rw [expect_comm]
    apply expect_congr rfl
    intro k _
    simp only [← mul_assoc,← expect_mul,codegree]
  rw [he]
  apply expect_le univ_nonempty
  intro i _
  apply expect_le univ_nonempty
  intro k _
  split_ifs with hh
  · simpa only [mul_one] using hh.le
  · simpa only [mul_zero] using hθ

lemma exists_good_neighborhood (R : I → J → Prop) {ε : ℝ} (hε : 0 < ε)
    (havg : ε ≤ 𝔼 i, 𝔼 j, edge R i j) :
    ∃ j, ε/2 ≤ neighborMass R j ∧
      badMass R (ε^2/32) j ≤ ε*neighborMass R j/16 := by
  let score : J → ℝ := fun j ↦ neighborMass R j-(16/ε)*badMass R (ε^2/32) j
  have hn : ε ≤ 𝔼 j, neighborMass R j := by
    unfold neighborMass
    rwa [expect_comm]
  have hb := mean_badMass_le R (by positivity : 0 ≤ ε^2/32)
  have hs : ε/2 ≤ 𝔼 j, score j := by
    dsimp [score]
    rw [expect_sub_distrib,← mul_expect]
    have hc := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 16/ε)
    have he : (16/ε)*(ε^2/32) = ε/2 := by field_simp <;> ring
    rw [he] at hc
    linarith
  obtain ⟨j,_,hj⟩ := exists_max_image univ score univ_nonempty
  have hj' : ε/2 ≤ score j := hs.trans (expect_le univ_nonempty hj)
  have hb0 := badMass_nonneg R (ε^2/32) j
  have hc0 : 0 ≤ (16/ε)*badMass R (ε^2/32) j := by positivity
  refine ⟨j,by dsimp [score] at hj'; linarith,?_⟩
  have hc : (16/ε)*badMass R (ε^2/32) j ≤ neighborMass R j := by
    dsimp [score] at hj'; linarith
  have hc' := (mul_le_mul_of_nonneg_left hc hε.le)
  have he : ε*((16/ε)*badMass R (ε^2/32) j) = 16*badMass R (ε^2/32) j := by
    field_simp <;> ring
  rw [he] at hc'
  linarith

lemma expect_indicator {K : Type*} [Fintype K] (S : Finset K) :
    (𝔼 k : K, if k ∈ S then (1 : ℝ) else 0) = (S.card : ℝ)/(Fintype.card K : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  simp only [← sum_filter]
  simp

/-- In a bipartite graph of density at least ε, there is a left-vertex set of
relative size at least ε/4 such that every pair has at least ε^5/4096 of all
possible alternating length-four paths between them. -/
theorem dense_graph_many_paths (R : I → J → Prop) {ε : ℝ} (hε : 0 < ε)
    (havg : ε ≤ 𝔼 i, 𝔼 j, edge R i j) :
    ∃ S : Finset I,
      ε/4 ≤ (S.card : ℝ)/(Fintype.card I : ℝ) ∧
      ∀ i ∈ S, ∀ k ∈ S,
        ε^5/4096 ≤ 𝔼 z : I, codegree R i z*codegree R k z := by
  obtain ⟨j,hn,hbad⟩ := exists_good_neighborhood R hε havg
  let n := neighborMass R j
  let θ : ℝ := ε^2/32
  have hn0 : 0 < n := by dsimp [n]; linarith
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  let S := univ.filter (fun i ↦ R i j ∧ badDegree R θ j i ≤ n/4)
  have hS (i : I) : i ∈ S ↔ R i j ∧ badDegree R θ j i ≤ n/4 := by
    simp only [S,mem_filter,mem_univ,true_and]
  have hsize : ε/4 ≤ (S.card : ℝ)/(Fintype.card I : ℝ) := by
    have hpt (i : I) : n*edge R i j ≤
        n*(if i ∈ S then 1 else 0)+4*(edge R i j*badDegree R θ j i) := by
      by_cases hij : R i j
      · by_cases hi : i ∈ S
        · simp only [edge,if_pos hij,if_pos hi,mul_one,one_mul]
          linarith [badDegree_nonneg R θ j i]
        · have hh : n/4 < badDegree R θ j i := by
            have := (not_and.mp ((hS i).not.mp hi)) hij
            linarith
          simp only [edge,if_pos hij,if_neg hi,mul_zero,one_mul,mul_one]
          linarith
      · have hi : i ∉ S := fun hi ↦ hij ((hS i).mp hi).1
        simp only [edge,if_neg hij,if_neg hi,mul_zero,zero_mul,add_zero,le_refl]
    have hh := expect_le_expect (fun i (_ : i ∈ univ) ↦ hpt i)
    rw [expect_add_distrib,← mul_expect,← mul_expect,← mul_expect,expect_indicator] at hh
    change n*n ≤ n*((S.card : ℝ)/(Fintype.card I : ℝ))+4*badMass R θ j at hh
    have hh' : n ≤ (S.card : ℝ)/(Fintype.card I : ℝ)+ε/4 := by
      have hx : n*n ≤ n*((S.card : ℝ)/(Fintype.card I : ℝ)+ε/4) := by
        change badMass R θ j ≤ ε*n/16 at hbad
        nlinarith
      nlinarith
    change ε/2 ≤ n at hn
    linarith
  refine ⟨S,hsize,?_⟩
  intro i hi k hk
  have hbi := ((hS i).mp hi).2
  have hbk := ((hS k).mp hk).2
  let M := univ.filter (fun z ↦ R z j ∧ θ ≤ codegree R i z ∧ θ ≤ codegree R k z)
  have hM (z : I) : z ∈ M ↔ R z j ∧ θ ≤ codegree R i z ∧ θ ≤ codegree R k z := by
    simp only [M,mem_filter,mem_univ,true_and]
  have hmiddle : n/2 ≤ 𝔼 z : I, if z ∈ M then (1 : ℝ) else 0 := by
    have hpt (z : I) : edge R z j ≤ (if z ∈ M then (1 : ℝ) else 0)+
        edge R z j*(if codegree R i z < θ then 1 else 0)+
        edge R z j*(if codegree R k z < θ then 1 else 0) := by
      by_cases hz : R z j
      · by_cases hi : codegree R i z < θ
        · simp only [edge,if_pos hz,if_pos hi,mul_one,one_mul]
          split_ifs <;> norm_num
        · by_cases hk : codegree R k z < θ
          · simp only [edge,if_pos hz,if_pos hk,one_mul]
            split_ifs <;> norm_num
          · have hm : z ∈ M := (hM z).mpr ⟨hz,le_of_not_gt hi,le_of_not_gt hk⟩
            simp only [edge,if_pos hz,if_pos hm,if_neg hi,if_neg hk,mul_zero,add_zero,le_refl]
      · have hm : z ∉ M := fun hh ↦ hz ((hM z).mp hh).1
        simp only [edge,if_neg hz,if_neg hm,zero_mul,add_zero,le_refl]
    have hh := expect_le_expect (fun z (_ : z ∈ univ) ↦ hpt z)
    rw [expect_add_distrib,expect_add_distrib] at hh
    change n ≤ (𝔼 z : I, if z ∈ M then (1 : ℝ) else 0)+badDegree R θ j i+badDegree R θ j k at hh
    linarith
  have hpt (z : I) : θ^2*(if z ∈ M then (1 : ℝ) else 0) ≤ codegree R i z*codegree R k z := by
    by_cases hz : z ∈ M
    · obtain ⟨_,hi,hk⟩ := (hM z).mp hz
      rw [if_pos hz,mul_one,pow_two]
      exact mul_le_mul hi hk hθ (codegree_nonneg R i z)
    · rw [if_neg hz,mul_zero]
      exact mul_nonneg (codegree_nonneg R i z) (codegree_nonneg R k z)
  have hh := expect_le_expect (fun z (_ : z ∈ univ) ↦ hpt z)
  rw [← mul_expect] at hh
  have hl : ε^5/4096 ≤ θ^2*(𝔼 z : I, if z ∈ M then (1 : ℝ) else 0) := by
    have hm : ε/4 ≤ 𝔼 z : I, if z ∈ M then (1 : ℝ) else 0 := by
      change ε/2 ≤ n at hn
      linarith
    have ht := mul_le_mul_of_nonneg_left hm (sq_nonneg θ)
    have he : θ^2*(ε/4) = ε^5/4096 := by dsimp [θ]; ring
    rwa [he] at ht
  exact hl.trans hh

noncomputable def paths (R : I → J → Prop) (i k : I) : Finset (I × J × J) :=
  univ.filter (fun p ↦ R i p.2.1 ∧ R p.1 p.2.1 ∧ R k p.2.2 ∧ R p.1 p.2.2)

lemma expect_pair {K L V : Type*} [Fintype K] [Fintype L]
    [AddCommMonoid V] [Module ℚ≥0 V] (f : K × L → V) :
    (𝔼 p, f p) = 𝔼 k, 𝔼 l, f (k,l) := expect_product _ _ _

lemma path_density_eq (R : I → J → Prop) (i k : I) :
    (𝔼 z : I, codegree R i z*codegree R k z) =
      ((paths R i k).card : ℝ)/((Fintype.card I : ℝ)*(Fintype.card J : ℝ)^2) := by
  have he (z : I) (b c : J) :
      edge R i b*edge R z b*(edge R k c*edge R z c) =
      if (z,b,c) ∈ paths R i k then (1 : ℝ) else 0 := by
    by_cases h1 : R i b <;> by_cases h2 : R z b <;>
      by_cases h3 : R k c <;> by_cases h4 : R z c <;>
      simp [edge,paths,h1,h2,h3,h4]
  unfold codegree
  simp_rw [Fintype.expect_mul_expect,he]
  have hp : (𝔼 p : I × J × J, if p ∈ paths R i k then (1 : ℝ) else 0) =
      𝔼 z : I, 𝔼 b : J, 𝔼 c : J, if (z,b,c) ∈ paths R i k then (1 : ℝ) else 0 := by
    rw [expect_pair]
    apply expect_congr rfl
    intro z _
    exact expect_pair _
  rw [← hp]
  simp [Fintype.expect_eq_sum_div_card,pow_two]

#print axioms dense_graph_many_paths
#print axioms path_density_eq
end Erdos3FiniteGraphPaths
