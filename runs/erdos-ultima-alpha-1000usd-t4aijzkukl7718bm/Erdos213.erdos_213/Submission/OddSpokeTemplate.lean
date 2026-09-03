import FormalConjecturesUtil

/-!
# Erdős Problem 213

*Reference:* [erdosproblems.com/213](https://www.erdosproblems.com/213)
-/

open EuclideanGeometry

namespace Erdos213

/--
The predicate (on $n$) that there exist $n$ points in $\mathbb{R}^2$,
no three on a line and no four on a circle,
such that all pairwise distances are integers.
-/
def Erdos213For (n : ℕ) : Prop := ∃ S : Set ℝ², S.Finite ∧ S.ncard = n ∧
    NonTrilinear S ∧
    (∀ Q : Set ℝ², Q ⊆ S ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q) ∧
    (S.Pairwise fun p₁ p₂ => dist p₁ p₂ ∈ Set.range Int.cast)

lemma Erdos213For.mono {m n : ℕ} (h : Erdos213For n) (hmn : m ≤ n) :
    Erdos213For m := by
  rcases h with ⟨S, hfin, hcard, htri, hcirc, hdist⟩
  obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_card_eq (hcard ▸ hmn)
  exact ⟨T, hfin.subset hTS, hTcard, htri.mono hTS,
    fun Q hQ => hcirc Q ⟨hQ.1.trans hTS, hQ.2⟩, hdist.mono hTS⟩

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a, b, c}) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨s, hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private lemma p4_dist_sq (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

/-- A finite set of rational real numbers admits a positive common denominator. -/
lemma finite_common_denominator {T : Set ℝ} (hT : T.Finite)
    (hQ : T ⊆ Set.range ((↑) : ℚ → ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ T, (D : ℝ) * x ∈ Set.range ((↑) : ℤ → ℝ) := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨1, by omega, by simp⟩
  | @insert x T hx hT ih =>
    obtain ⟨D, hD, hd⟩ := ih (fun y hy => hQ (Set.mem_insert_of_mem _ hy))
    obtain ⟨q, rfl⟩ := hQ (Set.mem_insert x T)
    refine ⟨q.den * D, Nat.mul_pos q.den_pos hD, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · refine ⟨(D : ℤ) * q.num, ?_⟩
      have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
      rw [Rat.cast_def]
      push_cast
      field_simp
    · obtain ⟨z, hz⟩ := hd y hy
      refine ⟨(q.den : ℤ) * z, ?_⟩
      push_cast
      rw [hz]
      ring

private lemma collinear_scale_image {T : Set ℝ²} (h : Collinear ℝ T) (c : ℝ) :
    Collinear ℝ ((fun x : ℝ² => c • x) '' T) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨o, v, h⟩ := h
  refine ⟨c • o, c • v, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, rfl⟩ := h x hx
  refine ⟨r, ?_⟩
  simp [smul_add, smul_smul, mul_comm]

private lemma cospherical_scale_image {T : Set ℝ²} (h : Cospherical T) (c : ℝ) :
    Cospherical ((fun x : ℝ² => c • x) '' T) := by
  obtain ⟨o, r, h⟩ := h
  refine ⟨c • o, ‖c‖ * r, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [dist_smul₀, h x hx]

lemma general_position_scale {T : Set ℝ²} (h : InGeneralPosition T) {c : ℝ}
    (hc : c ≠ 0) : InGeneralPosition ((fun x : ℝ² => c • x) '' T) := by
  have hi : Function.Injective (fun x : ℝ² => c⁻¹ • x) := by
    intro x y hxy
    simpa [hc] using congrArg (fun z : ℝ² => c • z) hxy
  constructor
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hxy hyz hxz hcol
    have hback := collinear_scale_image hcol c⁻¹
    simp only [Set.image_insert_eq, Set.image_singleton, inv_smul_smul₀ hc] at hback
    exact h.1 hx hy hz (fun he => hxy (he ▸ rfl))
      (fun he => hyz (he ▸ rfl)) (fun he => hxz (he ▸ rfl)) hback
  · intro Q hQ hcard hcos
    apply h.2 ((fun x : ℝ² => c⁻¹ • x) '' Q) ?_ ?_
      (cospherical_scale_image hcos c⁻¹)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hQ hx
      simpa [hc] using hy
    · rwa [Set.ncard_image_of_injective _ hi]

/-- For a fixed finite cardinality, rational and integer distances give equivalent
existence problems: a common dilation clears all denominators. -/
lemma erdos213For_iff_rational (n : ℕ) : Erdos213For n ↔
    ∃ S : Set ℝ², S.Finite ∧ S.ncard = n ∧ InGeneralPosition S ∧
      S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℚ → ℝ)) := by
  constructor
  · rintro ⟨S, hfin, hn, htri, hcircle, hdist⟩
    refine ⟨S, hfin, hn, ⟨htri, fun Q hQ h4 => hcircle Q ⟨hQ, h4⟩⟩, ?_⟩
    intro x hx y hy hxy
    obtain ⟨z, hz⟩ := hdist hx hy hxy
    exact ⟨(z : ℚ), by simpa using hz⟩
  · rintro ⟨S, hfin, hn, hgen, hdist⟩
    let T : Set ℝ := (fun p : ℝ² × ℝ² => dist p.1 p.2) '' (S ×ˢ S)
    have hTf : T.Finite := (hfin.prod hfin).image _
    have hTr : T ⊆ Set.range ((↑) : ℚ → ℝ) := by
      rintro _ ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩
      by_cases hxy : x = y
      · subst y
        exact ⟨0, by simp⟩
      · exact hdist hx hy hxy
    obtain ⟨D, hD, hmul⟩ := finite_common_denominator hTf hTr
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hD0 := ne_of_gt hDr
    have hinj : Function.Injective (fun x : ℝ² => (D : ℝ) • x) := by
      intro x y hxy
      simpa [hD0] using congrArg (fun z : ℝ² => (D : ℝ)⁻¹ • z) hxy
    have hg := general_position_scale hgen hD0
    refine ⟨(fun x : ℝ² => (D : ℝ) • x) '' S, hfin.image _, ?_, hg.1, ?_, ?_⟩
    · rwa [Set.ncard_image_of_injective _ hinj]
    · intro Q hQ
      exact hg.2 Q hQ.1 hQ.2
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ _
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hDr]
      exact hmul _ ⟨(x,y), ⟨hx,hy⟩, rfl⟩




namespace OddSpoke

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 10000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/- A bivariate conditional construction. No rational parameter satisfying
all its arithmetic hypotheses is asserted to exist. -/
def coordA (x s : ℚ) : Fin 8 → ℚ := ![0,-2*x*s - 2*s,0,2*x*s - 2*s,-s + 9,-4*s,-4*s,-3*s - 9]
def coordB (x s : ℚ) : Fin 8 → ℚ := ![0,4*x^2 + 4*x - s - 15,-12,-4*x^2 + 4*x + s + 3,2*x - 6,8*x - 12,8*x,6*x - 6]
def spoke (x s : ℚ) : Fin 7 → ℚ := ![s,-2*x + s + 1,2*x + s + 1,-6*x + s + 9,6*x + s + 9,-10*x + s + 25,10*x + s + 25]
def factor (x s : ℚ) : Fin 36 → ℚ := ![s,x + 1,6*x - s - 9,6*x - s + 15,s + 15,2*x + s + 5,x - 1,s - 9,s + 3,6*x - s + 3,2*x + s + 1,3*x - s,3*x + s,6*x + s + 9,6*x + s - 3,2*x - s - 1,2*x - s - 5,6*x + s - 15,x,2*x + s - 7,10*x - s - 5,6*x - s + 7,6*x + s + 5,s + 5,10*x - 3*s + 5,2*x - 3*s + 5,10*x + s + 5,10*x + 3*s - 5,2*x - s + 7,2*x + s - 3,2*x - s + 3,s - 3,6*x + s - 7,6*x - s - 5,s - 1,2*x + 3*s - 5]

def quadNorm (x s a b : ℚ) : ℚ := a^2+2*x*a*b+s*b^2

def triangle (x s : ℚ) (i j k : Fin 8) : ℚ :=
  (coordA x s j-coordA x s i)*(coordB x s k-coordB x s i) -
  (coordB x s j-coordB x s i)*(coordA x s k-coordA x s i)

def det3 {T : Type*} [CommRing T] (a b c d e f g h i : T) : T :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

def circle (x s : ℚ) (i j k l : Fin 8) : ℚ :=
  det3 (coordA x s j-coordA x s i) (coordB x s j-coordB x s i)
    (quadNorm x s (coordA x s j-coordA x s i) (coordB x s j-coordB x s i))
    (coordA x s k-coordA x s i) (coordB x s k-coordB x s i)
    (quadNorm x s (coordA x s k-coordA x s i) (coordB x s k-coordB x s i))
    (coordA x s l-coordA x s i) (coordB x s l-coordB x s i)
    (quadNorm x s (coordA x s l-coordA x s i) (coordB x s l-coordB x s i))

lemma norm_sorted_square (x s : ℚ) (hs : ∀ k, IsSquare (spoke x s k))
    (i j : Fin 8) (hij : i < j) :
    IsSquare (quadNorm x s (coordA x s j-coordA x s i) (coordB x s j-coordB x s i)) := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · change IsSquare (quadNorm x s (coordA x s 1-coordA x s 0) (coordB x s 1-coordB x s 0))
    have he : quadNorm x s (coordA x s 1-coordA x s 0) (coordB x s 1-coordB x s 0) = (1)^2 * (spoke x s 0) * (spoke x s 3) * (spoke x s 6) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 0)).mul (hs 3)).mul (hs 6)
  · change IsSquare (quadNorm x s (coordA x s 2-coordA x s 0) (coordB x s 2-coordB x s 0))
    have he : quadNorm x s (coordA x s 2-coordA x s 0) (coordB x s 2-coordB x s 0) = (12)^2 * (spoke x s 0) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((show IsSquare ((12 : ℚ)^2) from ⟨12, by ring⟩)).mul (hs 0)
  · change IsSquare (quadNorm x s (coordA x s 3-coordA x s 0) (coordB x s 3-coordB x s 0))
    have he : quadNorm x s (coordA x s 3-coordA x s 0) (coordB x s 3-coordB x s 0) = (1)^2 * (spoke x s 0) * (spoke x s 3) * (spoke x s 2) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 0)).mul (hs 3)).mul (hs 2)
  · change IsSquare (quadNorm x s (coordA x s 4-coordA x s 0) (coordB x s 4-coordB x s 0))
    have he : quadNorm x s (coordA x s 4-coordA x s 0) (coordB x s 4-coordB x s 0) = (1)^2 * (spoke x s 3)^2 := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (IsSquare.pow 2 (hs 3))
  · change IsSquare (quadNorm x s (coordA x s 5-coordA x s 0) (coordB x s 5-coordB x s 0))
    have he : quadNorm x s (coordA x s 5-coordA x s 0) (coordB x s 5-coordB x s 0) = (4)^2 * (spoke x s 0) * (spoke x s 3) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact (((show IsSquare ((4 : ℚ)^2) from ⟨4, by ring⟩)).mul (hs 0)).mul (hs 3)
  · change IsSquare (quadNorm x s (coordA x s 6-coordA x s 0) (coordB x s 6-coordB x s 0))
    have he : quadNorm x s (coordA x s 6-coordA x s 0) (coordB x s 6-coordB x s 0) = (4)^2 * (spoke x s 0)^2 := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((show IsSquare ((4 : ℚ)^2) from ⟨4, by ring⟩)).mul (IsSquare.pow 2 (hs 0))
  · change IsSquare (quadNorm x s (coordA x s 7-coordA x s 0) (coordB x s 7-coordB x s 0))
    have he : quadNorm x s (coordA x s 7-coordA x s 0) (coordB x s 7-coordB x s 0) = (3)^2 * (spoke x s 3) * (spoke x s 2) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact (((show IsSquare ((3 : ℚ)^2) from ⟨3, by ring⟩)).mul (hs 3)).mul (hs 2)
  · change IsSquare (quadNorm x s (coordA x s 2-coordA x s 1) (coordB x s 2-coordB x s 1))
    have he : quadNorm x s (coordA x s 2-coordA x s 1) (coordB x s 2-coordB x s 1) = (1)^2 * (spoke x s 0) * (spoke x s 1) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 0)).mul (hs 1)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 3-coordA x s 1) (coordB x s 3-coordB x s 1))
    have he : quadNorm x s (coordA x s 3-coordA x s 1) (coordB x s 3-coordB x s 1) = (2)^2 * (spoke x s 0) * (spoke x s 3) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((2 : ℚ)^2) from ⟨2, by ring⟩)).mul (hs 0)).mul (hs 3)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 4-coordA x s 1) (coordB x s 4-coordB x s 1))
    have he : quadNorm x s (coordA x s 4-coordA x s 1) (coordB x s 4-coordB x s 1) = (1)^2 * (spoke x s 3) * (spoke x s 2) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 3)).mul (hs 2)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 5-coordA x s 1) (coordB x s 5-coordB x s 1))
    have he : quadNorm x s (coordA x s 5-coordA x s 1) (coordB x s 5-coordB x s 1) = (1)^2 * (spoke x s 0) * (spoke x s 3) * (spoke x s 2) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 0)).mul (hs 3)).mul (hs 2)
  · change IsSquare (quadNorm x s (coordA x s 6-coordA x s 1) (coordB x s 6-coordB x s 1))
    have he : quadNorm x s (coordA x s 6-coordA x s 1) (coordB x s 6-coordB x s 1) = (1)^2 * (spoke x s 0) * (spoke x s 5) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 0)).mul (hs 5)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 7-coordA x s 1) (coordB x s 7-coordB x s 1))
    have he : quadNorm x s (coordA x s 7-coordA x s 1) (coordB x s 7-coordB x s 1) = (1)^2 * (spoke x s 3) * (spoke x s 1) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 3)).mul (hs 1)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 3-coordA x s 2) (coordB x s 3-coordB x s 2))
    have he : quadNorm x s (coordA x s 3-coordA x s 2) (coordB x s 3-coordB x s 2) = (1)^2 * (spoke x s 0) * (spoke x s 5) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 0)).mul (hs 5)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 4-coordA x s 2) (coordB x s 4-coordB x s 2))
    have he : quadNorm x s (coordA x s 4-coordA x s 2) (coordB x s 4-coordB x s 2) = (1)^2 * (spoke x s 4)^2 := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (IsSquare.pow 2 (hs 4))
  · change IsSquare (quadNorm x s (coordA x s 5-coordA x s 2) (coordB x s 5-coordB x s 2))
    have he : quadNorm x s (coordA x s 5-coordA x s 2) (coordB x s 5-coordB x s 2) = (4)^2 * (spoke x s 0)^2 := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((show IsSquare ((4 : ℚ)^2) from ⟨4, by ring⟩)).mul (IsSquare.pow 2 (hs 0))
  · change IsSquare (quadNorm x s (coordA x s 6-coordA x s 2) (coordB x s 6-coordB x s 2))
    have he : quadNorm x s (coordA x s 6-coordA x s 2) (coordB x s 6-coordB x s 2) = (4)^2 * (spoke x s 0) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact (((show IsSquare ((4 : ℚ)^2) from ⟨4, by ring⟩)).mul (hs 0)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 7-coordA x s 2) (coordB x s 7-coordB x s 2))
    have he : quadNorm x s (coordA x s 7-coordA x s 2) (coordB x s 7-coordB x s 2) = (3)^2 * (spoke x s 1) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact (((show IsSquare ((3 : ℚ)^2) from ⟨3, by ring⟩)).mul (hs 1)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 4-coordA x s 3) (coordB x s 4-coordB x s 3))
    have he : quadNorm x s (coordA x s 4-coordA x s 3) (coordB x s 4-coordB x s 3) = (1)^2 * (spoke x s 3) * (spoke x s 1) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 3)).mul (hs 1)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 5-coordA x s 3) (coordB x s 5-coordB x s 3))
    have he : quadNorm x s (coordA x s 5-coordA x s 3) (coordB x s 5-coordB x s 3) = (1)^2 * (spoke x s 0) * (spoke x s 3) * (spoke x s 6) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 0)).mul (hs 3)).mul (hs 6)
  · change IsSquare (quadNorm x s (coordA x s 6-coordA x s 3) (coordB x s 6-coordB x s 3))
    have he : quadNorm x s (coordA x s 6-coordA x s 3) (coordB x s 6-coordB x s 3) = (1)^2 * (spoke x s 0) * (spoke x s 1) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 0)).mul (hs 1)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 7-coordA x s 3) (coordB x s 7-coordB x s 3))
    have he : quadNorm x s (coordA x s 7-coordA x s 3) (coordB x s 7-coordB x s 3) = (1)^2 * (spoke x s 3) * (spoke x s 2) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (hs 3)).mul (hs 2)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 5-coordA x s 4) (coordB x s 5-coordB x s 4))
    have he : quadNorm x s (coordA x s 5-coordA x s 4) (coordB x s 5-coordB x s 4) = (3)^2 * (spoke x s 3) * (spoke x s 2) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact (((show IsSquare ((3 : ℚ)^2) from ⟨3, by ring⟩)).mul (hs 3)).mul (hs 2)
  · change IsSquare (quadNorm x s (coordA x s 6-coordA x s 4) (coordB x s 6-coordB x s 4))
    have he : quadNorm x s (coordA x s 6-coordA x s 4) (coordB x s 6-coordB x s 4) = (3)^2 * (spoke x s 1) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact (((show IsSquare ((3 : ℚ)^2) from ⟨3, by ring⟩)).mul (hs 1)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 7-coordA x s 4) (coordB x s 7-coordB x s 4))
    have he : quadNorm x s (coordA x s 7-coordA x s 4) (coordB x s 7-coordB x s 4) = (2)^2 * (spoke x s 3) * (spoke x s 4) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact (((show IsSquare ((2 : ℚ)^2) from ⟨2, by ring⟩)).mul (hs 3)).mul (hs 4)
  · change IsSquare (quadNorm x s (coordA x s 6-coordA x s 5) (coordB x s 6-coordB x s 5))
    have he : quadNorm x s (coordA x s 6-coordA x s 5) (coordB x s 6-coordB x s 5) = (12)^2 * (spoke x s 0) := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((show IsSquare ((12 : ℚ)^2) from ⟨12, by ring⟩)).mul (hs 0)
  · change IsSquare (quadNorm x s (coordA x s 7-coordA x s 5) (coordB x s 7-coordB x s 5))
    have he : quadNorm x s (coordA x s 7-coordA x s 5) (coordB x s 7-coordB x s 5) = (1)^2 * (spoke x s 3)^2 := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (IsSquare.pow 2 (hs 3))
  · change IsSquare (quadNorm x s (coordA x s 7-coordA x s 6) (coordB x s 7-coordB x s 6))
    have he : quadNorm x s (coordA x s 7-coordA x s 6) (coordB x s 7-coordB x s 6) = (1)^2 * (spoke x s 4)^2 := by
      dsimp [quadNorm,coordA,coordB,spoke]
      ring
    rw [he]
    exact ((show IsSquare ((1 : ℚ)^2) from ⟨1, by ring⟩)).mul (IsSquare.pow 2 (hs 4))

lemma triangle_sorted_ne (x s : ℚ) (hg : ∀ k, factor x s k ≠ 0)
    (i j k : Fin 8) (hij : i < j) (hjk : j < k) :
    triangle x s i j k ≠ 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  · change triangle x s 0 1 2 ≠ 0
    have he : triangle x s 0 1 2 = (24) * (factor x s 0) * (factor x s 1) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (hg 0)) (hg 1))
  · change triangle x s 0 1 3 ≠ 0
    have he : triangle x s 0 1 3 = (4) * (factor x s 0) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 0)) (hg 2))
  · change triangle x s 0 1 4 ≠ 0
    have he : triangle x s 0 1 4 = (-1) * (factor x s 3) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-1 : ℚ) ≠ 0) (hg 3)) (hg 2))
  · change triangle x s 0 1 5 ≠ 0
    have he : triangle x s 0 1 5 = (4) * (factor x s 0) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 0)) (hg 2))
  · change triangle x s 0 1 6 ≠ 0
    have he : triangle x s 0 1 6 = (-4) * (factor x s 0) * (factor x s 4) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-4 : ℚ) ≠ 0) (hg 0)) (hg 4))
  · change triangle x s 0 1 7 ≠ 0
    have he : triangle x s 0 1 7 = (3) * (factor x s 2) * (factor x s 5) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (3 : ℚ) ≠ 0) (hg 2)) (hg 5))
  · change triangle x s 0 2 3 ≠ 0
    have he : triangle x s 0 2 3 = (24) * (factor x s 0) * (factor x s 6) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (hg 0)) (hg 6))
  · change triangle x s 0 2 4 ≠ 0
    have he : triangle x s 0 2 4 = (-12) * (factor x s 7) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (hg 7))
  · change triangle x s 0 2 5 ≠ 0
    have he : triangle x s 0 2 5 = (-48) * (factor x s 0) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (-48 : ℚ) ≠ 0) (hg 0))
  · change triangle x s 0 2 6 ≠ 0
    have he : triangle x s 0 2 6 = (-48) * (factor x s 0) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (-48 : ℚ) ≠ 0) (hg 0))
  · change triangle x s 0 2 7 ≠ 0
    have he : triangle x s 0 2 7 = (-36) * (factor x s 8) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (hg 8))
  · change triangle x s 0 3 4 ≠ 0
    have he : triangle x s 0 3 4 = (1) * (factor x s 9) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (1 : ℚ) ≠ 0) (hg 9)) (hg 2))
  · change triangle x s 0 3 5 ≠ 0
    have he : triangle x s 0 3 5 = (-4) * (factor x s 0) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-4 : ℚ) ≠ 0) (hg 0)) (hg 2))
  · change triangle x s 0 3 6 ≠ 0
    have he : triangle x s 0 3 6 = (4) * (factor x s 0) * (factor x s 8) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 0)) (hg 8))
  · change triangle x s 0 3 7 ≠ 0
    have he : triangle x s 0 3 7 = (-3) * (factor x s 2) * (factor x s 10) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-3 : ℚ) ≠ 0) (hg 2)) (hg 10))
  · change triangle x s 0 4 5 ≠ 0
    have he : triangle x s 0 4 5 = (12) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 2))
  · change triangle x s 0 4 6 ≠ 0
    have he : triangle x s 0 4 6 = (24) * (factor x s 11) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (hg 11))
  · change triangle x s 0 4 7 ≠ 0
    have he : triangle x s 0 4 7 = (12) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 2))
  · change triangle x s 0 5 6 ≠ 0
    have he : triangle x s 0 5 6 = (-48) * (factor x s 0) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (-48 : ℚ) ≠ 0) (hg 0))
  · change triangle x s 0 5 7 ≠ 0
    have he : triangle x s 0 5 7 = (12) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 2))
  · change triangle x s 0 6 7 ≠ 0
    have he : triangle x s 0 6 7 = (24) * (factor x s 12) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (hg 12))
  · change triangle x s 1 2 3 ≠ 0
    have he : triangle x s 1 2 3 = (4) * (factor x s 0) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 0)) (hg 13))
  · change triangle x s 1 2 4 ≠ 0
    have he : triangle x s 1 2 4 = (1) * (factor x s 14) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (1 : ℚ) ≠ 0) (hg 14)) (hg 13))
  · change triangle x s 1 2 5 ≠ 0
    have he : triangle x s 1 2 5 = (4) * (factor x s 0) * (factor x s 8) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 0)) (hg 8))
  · change triangle x s 1 2 6 ≠ 0
    have he : triangle x s 1 2 6 = (4) * (factor x s 0) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 0)) (hg 13))
  · change triangle x s 1 2 7 ≠ 0
    have he : triangle x s 1 2 7 = (-3) * (factor x s 15) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-3 : ℚ) ≠ 0) (hg 15)) (hg 13))
  · change triangle x s 1 3 4 ≠ 0
    have he : triangle x s 1 3 4 = (2) * (factor x s 2) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (hg 2)) (hg 13))
  · change triangle x s 1 3 5 ≠ 0
    have he : triangle x s 1 3 5 = (-4) * (factor x s 0) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-4 : ℚ) ≠ 0) (hg 0)) (hg 2))
  · change triangle x s 1 3 6 ≠ 0
    have he : triangle x s 1 3 6 = (4) * (factor x s 0) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 0)) (hg 13))
  · change triangle x s 1 3 7 ≠ 0
    have he : triangle x s 1 3 7 = (-2) * (factor x s 2) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℚ) ≠ 0) (hg 2)) (hg 13))
  · change triangle x s 1 4 5 ≠ 0
    have he : triangle x s 1 4 5 = (-3) * (factor x s 2) * (factor x s 10) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-3 : ℚ) ≠ 0) (hg 2)) (hg 10))
  · change triangle x s 1 4 6 ≠ 0
    have he : triangle x s 1 4 6 = (-3) * (factor x s 16) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-3 : ℚ) ≠ 0) (hg 16)) (hg 13))
  · change triangle x s 1 4 7 ≠ 0
    have he : triangle x s 1 4 7 = (-2) * (factor x s 2) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℚ) ≠ 0) (hg 2)) (hg 13))
  · change triangle x s 1 5 6 ≠ 0
    have he : triangle x s 1 5 6 = (24) * (factor x s 0) * (factor x s 6) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (hg 0)) (hg 6))
  · change triangle x s 1 5 7 ≠ 0
    have he : triangle x s 1 5 7 = (-1) * (factor x s 9) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-1 : ℚ) ≠ 0) (hg 9)) (hg 2))
  · change triangle x s 1 6 7 ≠ 0
    have he : triangle x s 1 6 7 = (-1) * (factor x s 17) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-1 : ℚ) ≠ 0) (hg 17)) (hg 13))
  · change triangle x s 2 3 4 ≠ 0
    have he : triangle x s 2 3 4 = (1) * (factor x s 17) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (1 : ℚ) ≠ 0) (hg 17)) (hg 13))
  · change triangle x s 2 3 5 ≠ 0
    have he : triangle x s 2 3 5 = (4) * (factor x s 0) * (factor x s 4) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 0)) (hg 4))
  · change triangle x s 2 3 6 ≠ 0
    have he : triangle x s 2 3 6 = (4) * (factor x s 0) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 0)) (hg 13))
  · change triangle x s 2 3 7 ≠ 0
    have he : triangle x s 2 3 7 = (-3) * (factor x s 16) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-3 : ℚ) ≠ 0) (hg 16)) (hg 13))
  · change triangle x s 2 4 5 ≠ 0
    have he : triangle x s 2 4 5 = (24) * (factor x s 12) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (hg 12))
  · change triangle x s 2 4 6 ≠ 0
    have he : triangle x s 2 4 6 = (12) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 13))
  · change triangle x s 2 4 7 ≠ 0
    have he : triangle x s 2 4 7 = (12) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 13))
  · change triangle x s 2 5 6 ≠ 0
    have he : triangle x s 2 5 6 = (-48) * (factor x s 0) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (-48 : ℚ) ≠ 0) (hg 0))
  · change triangle x s 2 5 7 ≠ 0
    have he : triangle x s 2 5 7 = (24) * (factor x s 11) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (hg 11))
  · change triangle x s 2 6 7 ≠ 0
    have he : triangle x s 2 6 7 = (12) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 13))
  · change triangle x s 3 4 5 ≠ 0
    have he : triangle x s 3 4 5 = (3) * (factor x s 2) * (factor x s 5) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (3 : ℚ) ≠ 0) (hg 2)) (hg 5))
  · change triangle x s 3 4 6 ≠ 0
    have he : triangle x s 3 4 6 = (3) * (factor x s 15) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (3 : ℚ) ≠ 0) (hg 15)) (hg 13))
  · change triangle x s 3 4 7 ≠ 0
    have he : triangle x s 3 4 7 = (2) * (factor x s 2) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (hg 2)) (hg 13))
  · change triangle x s 3 5 6 ≠ 0
    have he : triangle x s 3 5 6 = (-24) * (factor x s 0) * (factor x s 1) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-24 : ℚ) ≠ 0) (hg 0)) (hg 1))
  · change triangle x s 3 5 7 ≠ 0
    have he : triangle x s 3 5 7 = (1) * (factor x s 3) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (1 : ℚ) ≠ 0) (hg 3)) (hg 2))
  · change triangle x s 3 6 7 ≠ 0
    have he : triangle x s 3 6 7 = (1) * (factor x s 14) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (1 : ℚ) ≠ 0) (hg 14)) (hg 13))
  · change triangle x s 4 5 6 ≠ 0
    have he : triangle x s 4 5 6 = (-36) * (factor x s 8) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (hg 8))
  · change triangle x s 4 5 7 ≠ 0
    have he : triangle x s 4 5 7 = (12) * (factor x s 2) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 2))
  · change triangle x s 4 6 7 ≠ 0
    have he : triangle x s 4 6 7 = (12) * (factor x s 13) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 13))
  · change triangle x s 5 6 7 ≠ 0
    have he : triangle x s 5 6 7 = (-12) * (factor x s 7) := by
      dsimp [triangle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (hg 7))

lemma circle_sorted_ne (x s : ℚ) (hg : ∀ k, factor x s k ≠ 0)
    (i j k l : Fin 8) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    circle x s i j k l ≠ 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> norm_num at hij <;> norm_num at hjk <;> norm_num at hkl
  · change circle x s 0 1 2 3 ≠ 0
    have he : circle x s 0 1 2 3 = (-48) * (factor x s 2) * (factor x s 18) * (factor x s 13) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-48 : ℚ) ≠ 0) (hg 2)) (hg 18)) (hg 13)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 0 1 2 4 ≠ 0
    have he : circle x s 0 1 2 4 = (12) * (factor x s 0) * (factor x s 2) * (factor x s 19) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 19)) (hg 13))
  · change circle x s 0 1 2 5 ≠ 0
    have he : circle x s 0 1 2 5 = (48) * (factor x s 2) * (factor x s 5) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (48 : ℚ) ≠ 0) (hg 2)) (hg 5)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 0 1 2 6 ≠ 0
    have he : circle x s 0 1 2 6 = (48) * (factor x s 20) * (factor x s 13) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (48 : ℚ) ≠ 0) (hg 20)) (hg 13)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 0 1 2 7 ≠ 0
    have he : circle x s 0 1 2 7 = (-36) * (factor x s 0) * (factor x s 2) * (factor x s 15) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 15)) (hg 13))
  · change circle x s 0 1 3 4 ≠ 0
    have he : circle x s 0 1 3 4 = (-2) * (factor x s 0) * (factor x s 21) * (factor x s 13) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℚ) ≠ 0) (hg 0)) (hg 21)) (hg 13)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 1 3 5 ≠ 0
    have he : circle x s 0 1 3 5 = (8) * (factor x s 22) * (factor x s 0)^2 * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℚ) ≠ 0) (hg 22)) (pow_ne_zero 2 (hg 0))) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 1 3 6 ≠ 0
    have he : circle x s 0 1 3 6 = (-8) * (factor x s 23) * (factor x s 2) * (factor x s 13) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-8 : ℚ) ≠ 0) (hg 23)) (hg 2)) (hg 13)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 0 1 3 7 ≠ 0
    have he : circle x s 0 1 3 7 = (6) * (factor x s 0) * (factor x s 10) * (factor x s 13) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (hg 0)) (hg 10)) (hg 13)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 1 4 5 ≠ 0
    have he : circle x s 0 1 4 5 = (-24) * (factor x s 0) * (factor x s 10) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-24 : ℚ) ≠ 0) (hg 0)) (hg 10)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 1 4 6 ≠ 0
    have he : circle x s 0 1 4 6 = (-12) * (factor x s 0) * (factor x s 24) * (factor x s 2) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (hg 0)) (hg 24)) (hg 2)) (hg 13))
  · change circle x s 0 1 4 7 ≠ 0
    have he : circle x s 0 1 4 7 = (6) * (factor x s 25) * (factor x s 13) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (hg 25)) (hg 13)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 1 5 6 ≠ 0
    have he : circle x s 0 1 5 6 = (48) * (factor x s 2) * (factor x s 26) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (48 : ℚ) ≠ 0) (hg 2)) (hg 26)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 0 1 5 7 ≠ 0
    have he : circle x s 0 1 5 7 = (-96) * (factor x s 0) * (factor x s 1) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-96 : ℚ) ≠ 0) (hg 0)) (hg 1)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 1 6 7 ≠ 0
    have he : circle x s 0 1 6 7 = (-12) * (factor x s 0) * (factor x s 2) * (factor x s 13) * (factor x s 27) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 13)) (hg 27))
  · change circle x s 0 2 3 4 ≠ 0
    have he : circle x s 0 2 3 4 = (12) * (factor x s 0) * (factor x s 2) * (factor x s 28) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 28)) (hg 13))
  · change circle x s 0 2 3 5 ≠ 0
    have he : circle x s 0 2 3 5 = (-48) * (factor x s 2) * (factor x s 26) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-48 : ℚ) ≠ 0) (hg 2)) (hg 26)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 0 2 3 6 ≠ 0
    have he : circle x s 0 2 3 6 = (-48) * (factor x s 16) * (factor x s 13) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-48 : ℚ) ≠ 0) (hg 16)) (hg 13)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 0 2 3 7 ≠ 0
    have he : circle x s 0 2 3 7 = (-36) * (factor x s 0) * (factor x s 2) * (factor x s 10) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 10)) (hg 13))
  · change circle x s 0 2 4 5 ≠ 0
    have he : circle x s 0 2 4 5 = (144) * (factor x s 0) * (factor x s 2) * (factor x s 29) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (144 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 29))
  · change circle x s 0 2 4 6 ≠ 0
    have he : circle x s 0 2 4 6 = (144) * (factor x s 0) * (factor x s 30) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (144 : ℚ) ≠ 0) (hg 0)) (hg 30)) (hg 13))
  · change circle x s 0 2 4 7 ≠ 0
    have he : circle x s 0 2 4 7 = (72) * (factor x s 31) * (factor x s 2) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (hg 31)) (hg 2)) (hg 13))
  · change circle x s 0 2 5 6 ≠ 0
    have he : circle x s 0 2 5 6 = (-4608) * (factor x s 18) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-4608 : ℚ) ≠ 0) (hg 18)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 0 2 5 7 ≠ 0
    have he : circle x s 0 2 5 7 = (144) * (factor x s 0) * (factor x s 9) * (factor x s 2) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (144 : ℚ) ≠ 0) (hg 0)) (hg 9)) (hg 2))
  · change circle x s 0 2 6 7 ≠ 0
    have he : circle x s 0 2 6 7 = (144) * (factor x s 0) * (factor x s 14) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (144 : ℚ) ≠ 0) (hg 0)) (hg 14)) (hg 13))
  · change circle x s 0 3 4 5 ≠ 0
    have he : circle x s 0 3 4 5 = (-96) * (factor x s 0) * (factor x s 1) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-96 : ℚ) ≠ 0) (hg 0)) (hg 1)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 3 4 6 ≠ 0
    have he : circle x s 0 3 4 6 = (-12) * (factor x s 0) * (factor x s 2) * (factor x s 15) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 15)) (hg 13))
  · change circle x s 0 3 4 7 ≠ 0
    have he : circle x s 0 3 4 7 = (-6) * (factor x s 10) * (factor x s 13) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (hg 10)) (hg 13)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 3 5 6 ≠ 0
    have he : circle x s 0 3 5 6 = (48) * (factor x s 2) * (factor x s 5) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (48 : ℚ) ≠ 0) (hg 2)) (hg 5)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 0 3 5 7 ≠ 0
    have he : circle x s 0 3 5 7 = (-24) * (factor x s 0) * (factor x s 10) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-24 : ℚ) ≠ 0) (hg 0)) (hg 10)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 3 6 7 ≠ 0
    have he : circle x s 0 3 6 7 = (-12) * (factor x s 0) * (factor x s 2) * (factor x s 10) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 10)) (hg 13))
  · change circle x s 0 4 5 6 ≠ 0
    have he : circle x s 0 4 5 6 = (144) * (factor x s 0) * (factor x s 9) * (factor x s 2) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (144 : ℚ) ≠ 0) (hg 0)) (hg 9)) (hg 2))
  · change circle x s 0 4 5 7 ≠ 0
    have he : circle x s 0 4 5 7 = (-72) * (factor x s 30) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (hg 30)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 0 4 6 7 ≠ 0
    have he : circle x s 0 4 6 7 = (-144) * (factor x s 2) * (factor x s 18) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-144 : ℚ) ≠ 0) (hg 2)) (hg 18)) (hg 13))
  · change circle x s 0 5 6 7 ≠ 0
    have he : circle x s 0 5 6 7 = (-144) * (factor x s 0) * (factor x s 2) * (factor x s 29) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-144 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 29))
  · change circle x s 1 2 3 4 ≠ 0
    have he : circle x s 1 2 3 4 = (2) * (factor x s 0) * (factor x s 2) * (factor x s 32) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 32)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 2 3 5 ≠ 0
    have he : circle x s 1 2 3 5 = (8) * (factor x s 23) * (factor x s 2) * (factor x s 13) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℚ) ≠ 0) (hg 23)) (hg 2)) (hg 13)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 1 2 3 6 ≠ 0
    have he : circle x s 1 2 3 6 = (8) * (factor x s 33) * (factor x s 0)^2 * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℚ) ≠ 0) (hg 33)) (pow_ne_zero 2 (hg 0))) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 2 3 7 ≠ 0
    have he : circle x s 1 2 3 7 = (-6) * (factor x s 0) * (factor x s 2) * (factor x s 15) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 15)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 2 4 5 ≠ 0
    have he : circle x s 1 2 4 5 = (12) * (factor x s 0) * (factor x s 2) * (factor x s 10) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 10)) (hg 13))
  · change circle x s 1 2 4 6 ≠ 0
    have he : circle x s 1 2 4 6 = (96) * (factor x s 0) * (factor x s 6) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (96 : ℚ) ≠ 0) (hg 0)) (hg 6)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 2 4 7 ≠ 0
    have he : circle x s 1 2 4 7 = (-6) * (factor x s 2) * (factor x s 15) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (hg 2)) (hg 15)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 2 5 6 ≠ 0
    have he : circle x s 1 2 5 6 = (-48) * (factor x s 16) * (factor x s 13) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-48 : ℚ) ≠ 0) (hg 16)) (hg 13)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 1 2 5 7 ≠ 0
    have he : circle x s 1 2 5 7 = (12) * (factor x s 0) * (factor x s 2) * (factor x s 15) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 15)) (hg 13))
  · change circle x s 1 2 6 7 ≠ 0
    have he : circle x s 1 2 6 7 = (24) * (factor x s 0) * (factor x s 15) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (hg 0)) (hg 15)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 3 4 5 ≠ 0
    have he : circle x s 1 3 4 5 = (6) * (factor x s 0) * (factor x s 10) * (factor x s 13) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (hg 0)) (hg 10)) (hg 13)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 1 3 4 6 ≠ 0
    have he : circle x s 1 3 4 6 = (6) * (factor x s 0) * (factor x s 2) * (factor x s 15) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 15)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 3 4 7 ≠ 0
    have he : circle x s 1 3 4 7 = (4) * (factor x s 34) * (factor x s 2)^2 * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (hg 34)) (pow_ne_zero 2 (hg 2))) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 3 5 6 ≠ 0
    have he : circle x s 1 3 5 6 = (-48) * (factor x s 2) * (factor x s 18) * (factor x s 13) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-48 : ℚ) ≠ 0) (hg 2)) (hg 18)) (hg 13)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 1 3 5 7 ≠ 0
    have he : circle x s 1 3 5 7 = (2) * (factor x s 0) * (factor x s 21) * (factor x s 13) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (hg 0)) (hg 21)) (hg 13)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 1 3 6 7 ≠ 0
    have he : circle x s 1 3 6 7 = (2) * (factor x s 0) * (factor x s 2) * (factor x s 32) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 32)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 4 5 6 ≠ 0
    have he : circle x s 1 4 5 6 = (-36) * (factor x s 0) * (factor x s 2) * (factor x s 10) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 10)) (hg 13))
  · change circle x s 1 4 5 7 ≠ 0
    have he : circle x s 1 4 5 7 = (6) * (factor x s 10) * (factor x s 13) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (hg 10)) (hg 13)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 1 4 6 7 ≠ 0
    have he : circle x s 1 4 6 7 = (6) * (factor x s 2) * (factor x s 35) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (hg 2)) (hg 35)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 1 5 6 7 ≠ 0
    have he : circle x s 1 5 6 7 = (12) * (factor x s 0) * (factor x s 2) * (factor x s 28) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 28)) (hg 13))
  · change circle x s 2 3 4 5 ≠ 0
    have he : circle x s 2 3 4 5 = (-12) * (factor x s 0) * (factor x s 2) * (factor x s 13) * (factor x s 27) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 13)) (hg 27))
  · change circle x s 2 3 4 6 ≠ 0
    have he : circle x s 2 3 4 6 = (-24) * (factor x s 0) * (factor x s 15) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-24 : ℚ) ≠ 0) (hg 0)) (hg 15)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 2 3 4 7 ≠ 0
    have he : circle x s 2 3 4 7 = (-6) * (factor x s 2) * (factor x s 35) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (hg 2)) (hg 35)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 2 3 5 6 ≠ 0
    have he : circle x s 2 3 5 6 = (48) * (factor x s 20) * (factor x s 13) * (factor x s 0)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (48 : ℚ) ≠ 0) (hg 20)) (hg 13)) (pow_ne_zero 2 (hg 0)))
  · change circle x s 2 3 5 7 ≠ 0
    have he : circle x s 2 3 5 7 = (-12) * (factor x s 0) * (factor x s 24) * (factor x s 2) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (hg 0)) (hg 24)) (hg 2)) (hg 13))
  · change circle x s 2 3 6 7 ≠ 0
    have he : circle x s 2 3 6 7 = (-96) * (factor x s 0) * (factor x s 6) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-96 : ℚ) ≠ 0) (hg 0)) (hg 6)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 2 4 5 6 ≠ 0
    have he : circle x s 2 4 5 6 = (144) * (factor x s 0) * (factor x s 14) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (144 : ℚ) ≠ 0) (hg 0)) (hg 14)) (hg 13))
  · change circle x s 2 4 5 7 ≠ 0
    have he : circle x s 2 4 5 7 = (-144) * (factor x s 2) * (factor x s 18) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-144 : ℚ) ≠ 0) (hg 2)) (hg 18)) (hg 13))
  · change circle x s 2 4 6 7 ≠ 0
    have he : circle x s 2 4 6 7 = (-72) * (factor x s 29) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (hg 29)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 2 5 6 7 ≠ 0
    have he : circle x s 2 5 6 7 = (-144) * (factor x s 0) * (factor x s 30) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-144 : ℚ) ≠ 0) (hg 0)) (hg 30)) (hg 13))
  · change circle x s 3 4 5 6 ≠ 0
    have he : circle x s 3 4 5 6 = (36) * (factor x s 0) * (factor x s 2) * (factor x s 15) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 15)) (hg 13))
  · change circle x s 3 4 5 7 ≠ 0
    have he : circle x s 3 4 5 7 = (-6) * (factor x s 25) * (factor x s 13) * (factor x s 2)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (hg 25)) (hg 13)) (pow_ne_zero 2 (hg 2)))
  · change circle x s 3 4 6 7 ≠ 0
    have he : circle x s 3 4 6 7 = (-6) * (factor x s 2) * (factor x s 15) * (factor x s 13)^2 := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (hg 2)) (hg 15)) (pow_ne_zero 2 (hg 13)))
  · change circle x s 3 5 6 7 ≠ 0
    have he : circle x s 3 5 6 7 = (-12) * (factor x s 0) * (factor x s 2) * (factor x s 19) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (hg 0)) (hg 2)) (hg 19)) (hg 13))
  · change circle x s 4 5 6 7 ≠ 0
    have he : circle x s 4 5 6 7 = (-72) * (factor x s 31) * (factor x s 2) * (factor x s 13) := by
      dsimp [circle,det3,quadNorm,coordA,coordB,factor]
      ring
    rw [he]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (hg 31)) (hg 2)) (hg 13))



open EuclideanGeometry

noncomputable def height (x s : ℚ) : ℝ := Real.sqrt ((s : ℝ)-(x : ℝ)^2)

noncomputable def realPoint (x s : ℚ) (i : Fin 8) : ℝ² :=
  !₂[(coordA x s i : ℝ)+(coordB x s i : ℝ)*(x : ℝ),
    (coordB x s i : ℝ)*height x s]

lemma height_pos {x s : ℚ} (hd : x^2 < s) : 0 < height x s := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast sub_pos.mpr hd

lemma height_sq {x s : ℚ} (hd : x^2 < s) :
    height x s ^ 2 = (s : ℝ)-(x : ℝ)^2 := by
  apply Real.sq_sqrt
  exact_mod_cast sub_nonneg.mpr hd.le

lemma realPoint_dist_sq {x s : ℚ} (hd : x^2 < s) (i j : Fin 8) :
    dist (realPoint x s i) (realPoint x s j)^2 =
      (quadNorm x s (coordA x s j-coordA x s i) (coordB x s j-coordB x s i) : ℝ) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two,Real.dist_eq,sq_abs]
  dsimp [realPoint,quadNorm]
  push_cast
  linear_combination ((coordB x s j : ℝ)-(coordB x s i : ℝ))^2 * height_sq hd

lemma sorted_not_collinear {x s : ℚ} (hg : ∀ k, factor x s k ≠ 0)
    (hd : x^2 < s) (i j k : Fin 8) (hij : i < j) (hjk : j < k) :
    ¬Collinear ℝ {realPoint x s i,realPoint x s j,realPoint x s k} := by
  intro hc
  have hh := collinear_det_zero hc
  have he : (triangle x s i j k : ℝ)*height x s = 0 := by
    convert hh using 1
    dsimp [triangle,realPoint]
    push_cast
    ring
  have hn : (triangle x s i j k : ℝ) ≠ 0 := by
    exact_mod_cast triangle_sorted_ne x s hg i j k hij hjk
  exact mul_ne_zero hn (ne_of_gt (height_pos hd)) he

private lemma cospherical_real_det {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2) = 0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,Real.dist_eq,sq_abs] at ha hb hc hd ⊢
  unfold det3
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1)) * (hb-ha) +
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1)) * (hc-ha) +
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1)) * (hd-ha)

lemma sorted_not_cospherical {x s : ℚ} (hg : ∀ k, factor x s k ≠ 0)
    (hd : x^2 < s) (i j k l : Fin 8)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    ¬Cospherical {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
  intro hc
  have hh := cospherical_real_det hc
  simp only [realPoint_dist_sq hd] at hh
  have he : (circle x s i j k l : ℝ)*height x s = 0 := by
    convert hh using 1
    dsimp [circle,det3,realPoint]
    push_cast
    ring
  have hn : (circle x s i j k l : ℝ) ≠ 0 := by
    exact_mod_cast circle_sorted_ne x s hg i j k l hij hjk hkl
  exact mul_ne_zero hn (ne_of_gt (height_pos hd)) he

lemma not_collinear {x s : ℚ} (hg : ∀ k, factor x s k ≠ 0)
    (hd : x^2 < s) (i j k : Fin 8)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ¬Collinear ℝ {realPoint x s i,realPoint x s j,realPoint x s k} := by
  have horder : ∀ i j k : Fin 8, i ≠ j → i ≠ k → j ≠ k →
    (i < j ∧ j < k) ∨
    (i < k ∧ k < j) ∨
    (j < i ∧ i < k) ∨
    (j < k ∧ k < i) ∨
    (k < i ∧ i < j) ∨
    (k < j ∧ j < i) := by decide
  have ho := horder i j k hij hik hjk
  rcases ho with ⟨ha,hb⟩ |
    ⟨ha,hb⟩ |
    ⟨ha,hb⟩ |
    ⟨ha,hb⟩ |
    ⟨ha,hb⟩ |
    ⟨ha,hb⟩
  · have hset : ({realPoint x s i,realPoint x s j,realPoint x s k} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hg hd i j k ha hb
  · have hset : ({realPoint x s i,realPoint x s k,realPoint x s j} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hg hd i k j ha hb
  · have hset : ({realPoint x s j,realPoint x s i,realPoint x s k} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hg hd j i k ha hb
  · have hset : ({realPoint x s j,realPoint x s k,realPoint x s i} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hg hd j k i ha hb
  · have hset : ({realPoint x s k,realPoint x s i,realPoint x s j} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hg hd k i j ha hb
  · have hset : ({realPoint x s k,realPoint x s j,realPoint x s i} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hg hd k j i ha hb

lemma not_cospherical {x s : ℚ} (hg : ∀ k, factor x s k ≠ 0)
    (hd : x^2 < s) (i j k l : Fin 8)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : ¬Cospherical {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
  have horder : ∀ i j k l : Fin 8, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    (i < j ∧ j < k ∧ k < l) ∨
    (i < j ∧ j < l ∧ l < k) ∨
    (i < k ∧ k < j ∧ j < l) ∨
    (i < k ∧ k < l ∧ l < j) ∨
    (i < l ∧ l < j ∧ j < k) ∨
    (i < l ∧ l < k ∧ k < j) ∨
    (j < i ∧ i < k ∧ k < l) ∨
    (j < i ∧ i < l ∧ l < k) ∨
    (j < k ∧ k < i ∧ i < l) ∨
    (j < k ∧ k < l ∧ l < i) ∨
    (j < l ∧ l < i ∧ i < k) ∨
    (j < l ∧ l < k ∧ k < i) ∨
    (k < i ∧ i < j ∧ j < l) ∨
    (k < i ∧ i < l ∧ l < j) ∨
    (k < j ∧ j < i ∧ i < l) ∨
    (k < j ∧ j < l ∧ l < i) ∨
    (k < l ∧ l < i ∧ i < j) ∨
    (k < l ∧ l < j ∧ j < i) ∨
    (l < i ∧ i < j ∧ j < k) ∨
    (l < i ∧ i < k ∧ k < j) ∨
    (l < j ∧ j < i ∧ i < k) ∨
    (l < j ∧ j < k ∧ k < i) ∨
    (l < k ∧ k < i ∧ i < j) ∨
    (l < k ∧ k < j ∧ j < i) := by decide
  have ho := horder i j k l hij hik hil hjk hjl hkl
  rcases ho with ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩
  · have hset : ({realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd i j k l ha hb hc
  · have hset : ({realPoint x s i,realPoint x s j,realPoint x s l,realPoint x s k} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd i j l k ha hb hc
  · have hset : ({realPoint x s i,realPoint x s k,realPoint x s j,realPoint x s l} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd i k j l ha hb hc
  · have hset : ({realPoint x s i,realPoint x s k,realPoint x s l,realPoint x s j} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd i k l j ha hb hc
  · have hset : ({realPoint x s i,realPoint x s l,realPoint x s j,realPoint x s k} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd i l j k ha hb hc
  · have hset : ({realPoint x s i,realPoint x s l,realPoint x s k,realPoint x s j} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd i l k j ha hb hc
  · have hset : ({realPoint x s j,realPoint x s i,realPoint x s k,realPoint x s l} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd j i k l ha hb hc
  · have hset : ({realPoint x s j,realPoint x s i,realPoint x s l,realPoint x s k} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd j i l k ha hb hc
  · have hset : ({realPoint x s j,realPoint x s k,realPoint x s i,realPoint x s l} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd j k i l ha hb hc
  · have hset : ({realPoint x s j,realPoint x s k,realPoint x s l,realPoint x s i} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd j k l i ha hb hc
  · have hset : ({realPoint x s j,realPoint x s l,realPoint x s i,realPoint x s k} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd j l i k ha hb hc
  · have hset : ({realPoint x s j,realPoint x s l,realPoint x s k,realPoint x s i} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd j l k i ha hb hc
  · have hset : ({realPoint x s k,realPoint x s i,realPoint x s j,realPoint x s l} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd k i j l ha hb hc
  · have hset : ({realPoint x s k,realPoint x s i,realPoint x s l,realPoint x s j} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd k i l j ha hb hc
  · have hset : ({realPoint x s k,realPoint x s j,realPoint x s i,realPoint x s l} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd k j i l ha hb hc
  · have hset : ({realPoint x s k,realPoint x s j,realPoint x s l,realPoint x s i} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd k j l i ha hb hc
  · have hset : ({realPoint x s k,realPoint x s l,realPoint x s i,realPoint x s j} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd k l i j ha hb hc
  · have hset : ({realPoint x s k,realPoint x s l,realPoint x s j,realPoint x s i} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd k l j i ha hb hc
  · have hset : ({realPoint x s l,realPoint x s i,realPoint x s j,realPoint x s k} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd l i j k ha hb hc
  · have hset : ({realPoint x s l,realPoint x s i,realPoint x s k,realPoint x s j} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd l i k j ha hb hc
  · have hset : ({realPoint x s l,realPoint x s j,realPoint x s i,realPoint x s k} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd l j i k ha hb hc
  · have hset : ({realPoint x s l,realPoint x s j,realPoint x s k,realPoint x s i} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd l j k i ha hb hc
  · have hset : ({realPoint x s l,realPoint x s k,realPoint x s i,realPoint x s j} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd l k i j ha hb hc
  · have hset : ({realPoint x s l,realPoint x s k,realPoint x s j,realPoint x s i} : Set ℝ²) = {realPoint x s i,realPoint x s j,realPoint x s k,realPoint x s l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hg hd l k j i ha hb hc

lemma realPoint_injective {x s : ℚ} (hg : ∀ k, factor x s k ≠ 0)
    (hd : x^2 < s) : Function.Injective (realPoint x s) := by
  intro i j he
  by_contra hij
  have hex : ∀ i j : Fin 8, ∃ k : Fin 8, i ≠ k ∧ j ≠ k := by decide
  obtain ⟨k,hik,hjk⟩ := hex i j
  have hc := not_collinear hg hd i j k hij hik hjk
  apply hc
  rw [he]
  simpa using (collinear_pair ℝ (realPoint x s j) (realPoint x s k))

lemma realPoint_general_position {x s : ℚ} (hg : ∀ k, factor x s k ≠ 0)
    (hd : x^2 < s) : InGeneralPosition (Set.range (realPoint x s)) := by
  constructor
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact not_collinear hg hd i j k (fun he => hij (he ▸ rfl))
      (fun he => hik (he ▸ rfl)) (fun he => hjk (he ▸ rfl))
  · intro Q hQ hcard hcos
    obtain ⟨a,b,c,e,hab,hac,hae,hbc,hbe,hce,hset⟩ := Set.ncard_eq_four.mp hcard
    subst Q
    obtain ⟨i,rfl⟩ := hQ (by simp : a ∈ ({a,b,c,e} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ (by simp : b ∈ ({realPoint x s i,b,c,e} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ (by simp : c ∈ ({realPoint x s i,realPoint x s j,c,e} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ (by simp : e ∈ ({realPoint x s i,realPoint x s j,realPoint x s k,e} : Set ℝ²))
    exact not_cospherical hg hd i j k l
      (fun he => hab (he ▸ rfl)) (fun he => hac (he ▸ rfl))
      (fun he => hae (he ▸ rfl)) (fun he => hbc (he ▸ rfl))
      (fun he => hbe (he ▸ rfl)) (fun he => hce (he ▸ rfl)) hcos



lemma rational_distances {x s : ℚ} (hd : x^2 < s)
    (hs : ∀ k, IsSquare (spoke x s k)) (i j : Fin 8) :
    ∃ q : ℚ, (q : ℝ) = dist (realPoint x s i) (realPoint x s j) := by
  have sorted : ∀ i j : Fin 8, i < j →
      ∃ q : ℚ, (q : ℝ) = dist (realPoint x s i) (realPoint x s j) := by
    intro i j hij
    obtain ⟨q,hq⟩ := norm_sorted_square x s hs i j hij
    have hq' : quadNorm x s (coordA x s j-coordA x s i)
        (coordB x s j-coordB x s i) = q^2 := by simpa [pow_two] using hq
    have hh := realPoint_dist_sq hd i j
    rw [hq'] at hh
    push_cast at hh
    refine ⟨|q|, ?_⟩
    push_cast
    nlinarith [sq_abs (q : ℝ), abs_nonneg (q : ℝ),
      dist_nonneg (x := realPoint x s i) (y := realPoint x s j)]
  rcases lt_trichotomy i j with h | rfl | h
  · exact sorted i j h
  · exact ⟨0, by simp⟩
  · obtain ⟨q,hq⟩ := sorted j i h
    exact ⟨q, by simpa [dist_comm] using hq⟩

/-- A complete arithmetic sufficient condition for an eight-point set.
The hypotheses are not asserted to be jointly satisfiable over the rationals. -/
lemma erdos213For_eight_of_odd_spokes (x s : ℚ) (hd : x^2 < s)
    (hs : ∀ k, IsSquare (spoke x s k))
    (hg : ∀ k, factor x s k ≠ 0) : Erdos213For 8 := by
  apply (erdos213For_iff_rational 8).mpr
  refine ⟨Set.range (realPoint x s), Set.finite_range _, ?_,
    realPoint_general_position hg hd, ?_⟩
  · rw [Set.ncard_range_of_injective (realPoint_injective hg hd)]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    exact rational_distances hd hs i j

#print axioms norm_sorted_square
#print axioms triangle_sorted_ne
#print axioms circle_sorted_ne
#print axioms realPoint_general_position
#print axioms erdos213For_eight_of_odd_spokes

end OddSpoke
end Erdos213
