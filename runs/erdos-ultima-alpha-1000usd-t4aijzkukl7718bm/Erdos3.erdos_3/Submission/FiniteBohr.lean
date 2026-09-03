import Submission.ChangSpectrum

/-! Elementary Bohr sets: span control and quantitative cardinality by grid pigeonholing.
These are auxiliary finite-group results only. -/
namespace Erdos3FiniteBohr
open Finset
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def bohr (D : Finset (AddChar G ℂ)) (ρ : ℝ) : Finset G :=
  univ.filter (fun x ↦ ∀ χ ∈ D, ‖χ x-1‖ ≤ ρ)

lemma mem_bohr {D : Finset (AddChar G ℂ)} {ρ : ℝ} {x : G} :
    x ∈ bohr D ρ ↔ ∀ χ ∈ D, ‖χ x-1‖ ≤ ρ := by simp [bohr]

lemma norm_mul_sub_one_le {z w : ℂ} (hz : ‖z‖ = 1) :
    ‖z*w-1‖ ≤ ‖z-1‖+‖w-1‖ := by
  calc
    _ = ‖(z-1)+z*(w-1)‖ := by congr 1; ring
    _ ≤ ‖z-1‖+‖z*(w-1)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, hz, one_mul]

lemma norm_prod_sub_one_le {I : Type*} (s : Finset I) (f : I → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ = 1) : ‖(∏ i ∈ s, f i)-1‖ ≤ ∑ i ∈ s, ‖f i-1‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    exact (norm_mul_sub_one_le (hf i (mem_insert_self _ _))).trans
      (add_le_add le_rfl (ih (fun j hj ↦ hf j (mem_insert_of_mem hj))))

lemma char_neg_sub_one_norm (χ : AddChar G ℂ) (x : G) : ‖χ (-x)-1‖ = ‖χ x-1‖ := by
  rw [χ.map_neg_eq_inv, AddChar.inv_apply_eq_conj]
  simpa only [map_sub, map_one] using Complex.norm_conj (χ x-1)

lemma norm_char_sub_one (χ : AddChar G ℂ) (x y : G) :
    ‖χ (x-y)-1‖ = ‖χ x-χ y‖ := by
  rw [χ.map_sub_eq_div, div_sub_one (norm_ne_zero_iff.mp (by rw [χ.norm_apply]; norm_num)), norm_div, χ.norm_apply, div_one]

lemma bohr_zero (D : Finset (AddChar G ℂ)) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ∈ bohr D ρ := by
  apply mem_bohr.mpr
  intro χ _
  simpa using hρ

lemma bohr_add {D : Finset (AddChar G ℂ)} {ρ σ : ℝ} {x y : G}
    (hx : x ∈ bohr D ρ) (hy : y ∈ bohr D σ) : x+y ∈ bohr D (ρ+σ) := by
  apply mem_bohr.mpr
  intro χ hχ
  rw [χ.map_add_eq_mul]
  exact (norm_mul_sub_one_le (χ.norm_apply x)).trans
    (add_le_add (mem_bohr.mp hx χ hχ) (mem_bohr.mp hy χ hχ))

lemma bohr_neg {D : Finset (AddChar G ℂ)} {ρ : ℝ} {x : G}
    (hx : x ∈ bohr D ρ) : -x ∈ bohr D ρ := by
  apply mem_bohr.mpr
  intro χ hχ
  rw [char_neg_sub_one_norm]
  exact mem_bohr.mp hx χ hχ

lemma span_control (D : Finset (AddChar G ℂ)) {χ : AddChar G ℂ} (hχ : χ ∈ D.mulSpan)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {x : G} (hx : x ∈ bohr D ρ) : ‖χ x-1‖ ≤ D.card*ρ := by
  obtain ⟨e,he,rfl⟩ := mem_mulSpan.mp hχ
  rw [AddChar.prod_apply]
  calc
    _ ≤ ∑ ψ ∈ D, ‖(ψ^e ψ) x-1‖ :=
      norm_prod_sub_one_le D (fun ψ ↦ (ψ^e ψ) x) (fun ψ _ ↦ (ψ^e ψ).norm_apply x)
    _ ≤ ∑ _ψ ∈ D, ρ := by
      apply sum_le_sum
      intro ψ hψ
      rcases he ψ with h | h | h
      · simp only [h, zpow_neg_one, AddChar.inv_apply, char_neg_sub_one_norm]
        exact mem_bohr.mp hx ψ hψ
      · simpa only [h, zpow_zero, AddChar.one_apply, sub_self, norm_zero] using hρ
      · simpa only [h, zpow_one] using mem_bohr.mp hx ψ hψ
    _ = _ := by simp

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

/-- Grid pigeonholing gives a lower bound for a finite Bohr set without any regularity hypothesis. -/
theorem card_bohr_lower (D : Finset (AddChar G ℂ)) {q : ℕ} (hq : 0 < q) :
    Fintype.card G ≤ (2*q+1)^(2*D.card) * (bohr D (2/(q : ℝ))).card := by
  let Y := D → Fin (2*q+1) × Fin (2*q+1)
  let label : G → Y := fun x χ ↦
    (gridCoord q ((χ : AddChar G ℂ) x).re (by simpa using Complex.abs_re_le_norm ((χ : AddChar G ℂ) x)),
     gridCoord q ((χ : AddChar G ℂ) x).im (by simpa using Complex.abs_im_le_norm ((χ : AddChar G ℂ) x)))
  obtain ⟨y,_,hy⟩ := exists_max_image (univ : Finset Y)
    (fun y ↦ (univ.filter (fun x ↦ label x = y)).card) univ_nonempty
  let F := univ.filter (fun x ↦ label x = y)
  have hcount : Fintype.card G ≤ Fintype.card Y * F.card := by
    calc
      _ = ∑ y : Y, (univ.filter (fun x ↦ label x = y)).card :=
        card_eq_sum_card_fiberwise (f := label) (t := univ) (fun _ _ ↦ mem_univ _)
      _ ≤ ∑ _y : Y, F.card := sum_le_sum (fun y hy' ↦ hy y hy')
      _ = _ := by simp
  have hF : F.Nonempty := by
    apply card_pos.mp
    by_contra h
    have hz : F.card = 0 := by omega
    rw [hz, mul_zero] at hcount
    have := Fintype.card_pos (α := G)
    omega
  obtain ⟨x₀,hx₀⟩ := hF
  have hsub : F.image (fun x ↦ x-x₀) ⊆ bohr D (2/(q : ℝ)) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    apply mem_bohr.mpr
    intro χ hχ
    have he : label x = label x₀ := (mem_filter.mp hx).2.trans (mem_filter.mp hx₀).2.symm
    have hre := congrArg (fun v : Y ↦ (v ⟨χ,hχ⟩).1) he
    have him := congrArg (fun v : Y ↦ (v ⟨χ,hχ⟩).2) he
    have hr := gridCoord_close hq (by simpa using Complex.abs_re_le_norm (χ x))
      (by simpa using Complex.abs_re_le_norm (χ x₀)) hre
    have hi := gridCoord_close hq (by simpa using Complex.abs_im_le_norm (χ x))
      (by simpa using Complex.abs_im_le_norm (χ x₀)) him
    rw [norm_char_sub_one]
    calc
      _ ≤ |(χ x-χ x₀).re|+|(χ x-χ x₀).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1/(q : ℝ)+1/(q : ℝ) := by simpa only [Complex.sub_re, Complex.sub_im] using add_le_add hr hi
      _ = _ := by ring
  have hcF : F.card ≤ (bohr D (2/(q : ℝ))).card := by
    calc
      _ = (F.image (fun x ↦ x-x₀)).card := (card_image_of_injective _ (sub_left_injective)).symm
      _ ≤ _ := card_le_card hsub
  have hY : Fintype.card Y = (2*q+1)^(2*D.card) := by
    simp only [Y, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      ← sq, ← pow_mul]
  rw [hY] at hcount
  exact hcount.trans (Nat.mul_le_mul_left _ hcF)

#print axioms span_control
#print axioms card_bohr_lower
end Erdos3FiniteBohr
