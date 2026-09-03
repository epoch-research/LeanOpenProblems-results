import Submission.FiniteBohr

/-! Relative cardinality bounds for finite Bohr sets, obtained from a coordinate grid.
These are auxiliary results, not a proof of the original conjecture. -/
namespace Erdos3BohrCovering
open Finset Erdos3FiniteBohr
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma bohr_mono (D : Finset (AddChar G ℂ)) {r s : ℝ} (h : r ≤ s) : bohr D r ⊆ bohr D s := by
  intro x hx
  exact mem_bohr.mpr (fun χ hχ ↦ (mem_bohr.mp hx χ hχ).trans h)

private noncomputable def gridCoord (q : ℕ) (r : ℝ) (hr : |r| ≤ 1) : Fin (2*q+1) :=
  ⟨⌊(q : ℝ)*(r+1)⌋₊, by
    have hn : 0 ≤ (q : ℝ)*(r+1) := mul_nonneg (Nat.cast_nonneg _) (by linarith [(abs_le.mp hr).1])
    apply (Nat.floor_lt hn).mpr
    push_cast
    nlinarith [(abs_le.mp hr).2, (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]⟩

private lemma gridCoord_close {q : ℕ} (hq : 0 < q) {r s : ℝ} (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (h : gridCoord q r hr = gridCoord q s hs) : |r-s| ≤ 1/(q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : 0 ≤ (q : ℝ)*(r+1) := mul_nonneg hqR.le (by linarith [(abs_le.mp hr).1])
  have hnS : 0 ≤ (q : ℝ)*(s+1) := mul_nonneg hqR.le (by linarith [(abs_le.mp hs).1])
  have he : ⌊(q : ℝ)*(r+1)⌋₊ = ⌊(q : ℝ)*(s+1)⌋₊ := congrArg Fin.val h
  have hr0 := Nat.floor_le hnR
  have hs0 := Nat.floor_le hnS
  have hr1 := Nat.lt_floor_add_one ((q : ℝ)*(r+1))
  have hs1 := Nat.lt_floor_add_one ((q : ℝ)*(s+1))
  rw [he] at hr0 hr1
  have hd : |(q : ℝ)*(r-s)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos hqR] at hd
  apply (le_div_iff₀ hqR).mpr
  nlinarith

/-- If all character values on A stay within radius R of fixed centers, a largest grid fiber
injects, after translation, into a Bohr set at radius 2R/q. -/
theorem card_le_grid_mul_bohr (D : Finset (AddChar G ℂ)) (A : Finset G) (hA : A.Nonempty)
    (c : AddChar G ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ x ∈ A, ∀ χ ∈ D, ‖χ x-c χ‖ ≤ R) {q : ℕ} (hq : 0 < q) :
    A.card ≤ (2*q+1)^(2*D.card)*(bohr D (2*R/(q : ℝ))).card := by
  letI : Nonempty A := hA.to_subtype
  let z : A → D → ℂ := fun x χ ↦ ((χ : AddChar G ℂ) x-c χ)/(R : ℂ)
  have hz (x : A) (χ : D) : ‖z x χ‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact (div_le_one hR).mpr (hbound x x.property χ χ.property)
  let Y := D → Fin (2*q+1) × Fin (2*q+1)
  let label : A → Y := fun x χ ↦
    (gridCoord q (z x χ).re ((Complex.abs_re_le_norm _).trans (hz x χ)),
     gridCoord q (z x χ).im ((Complex.abs_im_le_norm _).trans (hz x χ)))
  obtain ⟨y,_,hy⟩ := exists_max_image (univ : Finset Y)
    (fun y ↦ (univ.filter (fun x : A ↦ label x = y)).card) univ_nonempty
  let F := univ.filter (fun x : A ↦ label x = y)
  have hcount : A.card ≤ Fintype.card Y*F.card := by
    calc
      _ = ∑ y : Y, (univ.filter (fun x : A ↦ label x = y)).card := by
        simpa only [card_univ, Fintype.card_coe] using
          card_eq_sum_card_fiberwise (f := label) (s := univ) (t := univ) (fun _ _ ↦ mem_univ _)
      _ ≤ ∑ _y : Y, F.card := sum_le_sum (fun y hy' ↦ hy y hy')
      _ = _ := by simp
  have hF : F.Nonempty := by
    apply card_pos.mp
    by_contra h
    have hz : F.card = 0 := by omega
    rw [hz, mul_zero] at hcount
    have := hA.card_pos
    omega
  obtain ⟨x₀,hx₀⟩ := hF
  have hsub : F.image (fun (x : A) ↦ (x : G)-(x₀ : G)) ⊆ bohr D (2*R/(q : ℝ)) := by
    intro w hw
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hw
    apply mem_bohr.mpr
    intro χ hχ
    let χ' : D := ⟨χ,hχ⟩
    have he : label x = label x₀ := (mem_filter.mp hx).2.trans (mem_filter.mp hx₀).2.symm
    have hre := congrArg (fun v : Y ↦ (v χ').1) he
    have him := congrArg (fun v : Y ↦ (v χ').2) he
    have hr := gridCoord_close hq ((Complex.abs_re_le_norm _).trans (hz x χ'))
      ((Complex.abs_re_le_norm _).trans (hz x₀ χ')) hre
    have hi := gridCoord_close hq ((Complex.abs_im_le_norm _).trans (hz x χ'))
      ((Complex.abs_im_le_norm _).trans (hz x₀ χ')) him
    have hdist : ‖z x χ'-z x₀ χ'‖ ≤ 2/(q : ℝ) := by
      calc
        _ ≤ |(z x χ'-z x₀ χ').re|+|(z x χ'-z x₀ χ').im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 1/(q : ℝ)+1/(q : ℝ) := by simpa only [Complex.sub_re, Complex.sub_im] using add_le_add hr hi
        _ = _ := by ring
    have heq : z x χ'-z x₀ χ' = (χ x-χ x₀)/(R : ℂ) := by dsimp [z, χ']; ring
    rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hdist
    rw [norm_char_sub_one]
    have h := (div_le_iff₀ hR).mp hdist
    convert h using 1 <;> ring
  have hcF : F.card ≤ (bohr D (2*R/(q : ℝ))).card := by
    calc
      _ = (F.image (fun (x : A) ↦ (x : G)-(x₀ : G))).card :=
        (card_image_of_injective _ (fun a b hab ↦ Subtype.ext (sub_left_injective hab))).symm
      _ ≤ _ := card_le_card hsub
  have hY : Fintype.card Y = (2*q+1)^(2*D.card) := by
    simp only [Y, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      ← sq, ← pow_mul]
  rw [hY] at hcount
  exact hcount.trans (Nat.mul_le_mul_left _ hcF)

lemma card_scale_le (D : Finset (AddChar G ℂ)) {R : ℝ} (hR : 0 < R) {q : ℕ} (hq : 0 < q) :
    (bohr D R).card ≤ (2*q+1)^(2*D.card)*(bohr D (2*R/(q : ℝ))).card :=
  card_le_grid_mul_bohr D (bohr D R) ⟨0,bohr_zero D hR.le⟩ (fun _ ↦ 1) hR
    (fun _ hx χ hχ ↦ mem_bohr.mp hx χ hχ) hq

/-- The doubling cost of a finite Bohr set is exponential only in its rank. -/
theorem card_double_le (D : Finset (AddChar G ℂ)) {R : ℝ} (hR : 0 < R) :
    (bohr D (2*R)).card ≤ 81^D.card*(bohr D R).card := by
  have h := card_scale_le D (mul_pos (by norm_num : (0 : ℝ) < 2) hR) (q := 4) (by norm_num)
  have he : 2*(2*R)/(4 : ℝ) = R := by ring
  simpa only [Nat.cast_ofNat, he, show 2*4+1 = 9 by decide, pow_mul, show (9 : ℕ)^2 = 81 by decide] using h

#print axioms card_le_grid_mul_bohr
#print axioms card_double_le
end Erdos3BohrCovering
