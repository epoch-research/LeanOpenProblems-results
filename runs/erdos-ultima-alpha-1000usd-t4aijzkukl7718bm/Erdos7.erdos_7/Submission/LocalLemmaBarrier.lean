import FormalConjecturesUtil

/-!
A limitation of the plain product-form local-lemma criterion. Four disjoint
odd residue classes already fail that criterion despite having an explicit
uncovered integer. This is NOT a covering system or a disproof of Erdős 7.
-/

namespace Erdos7LocalLemmaBarrier

lemma polynomial_pos (t : ℝ) (ht : 0 ≤ t) :
    0 < t^4 + 120*t^3 + 3510*t^2 - 29889*t + 59049 := by
  have h4 : 0 ≤ t^4 := pow_nonneg ht _
  have hs : 0 ≤ 1684800*(t-3)^2*(t+6) := by positivity
  have hq := sq_nonneg (7020*t-26649)
  have hid : 14040*(t^4 + 120*t^3 + 3510*t^2 - 29889*t + 59049) =
      14040*t^4 + 1684800*(t-3)^2*(t+6) + (7020*t-26649)^2 + 27899559 := by ring
  nlinarith only [h4, hs, hq, hid]

lemma product_gt_self (t : ℝ) (ht : 0 ≤ t) :
    t < (1+t/3)*(1+t/9)*(1+t/27)*(1+t/81) := by
  have h := polynomial_pos t ht
  nlinarith only [h]

/-- The odds-parameter form of the ordinary asymmetric local lemma cannot
certify a clique with event probabilities 1/3, 1/9, 1/27, 1/81. -/
theorem no_four_odds (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ¬ ((1+a)*(1+b)*(1+c)*(1+d)/3 ≤ a ∧
       (1+a)*(1+b)*(1+c)*(1+d)/9 ≤ b ∧
       (1+a)*(1+b)*(1+c)*(1+d)/27 ≤ c ∧
       (1+a)*(1+b)*(1+c)*(1+d)/81 ≤ d) := by
  rintro ⟨h₁, h₂, h₃, h₄⟩
  let t := (1+a)*(1+b)*(1+c)*(1+d)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hle : (1+t/3)*(1+t/9)*(1+t/27)*(1+t/81) ≤ t := by
    change (1+t/3)*(1+t/9)*(1+t/27)*(1+t/81) ≤ (1+a)*(1+b)*(1+c)*(1+d)
    have ht₁ : t/3 ≤ a := h₁
    have ht₂ : t/9 ≤ b := h₂
    have ht₃ : t/27 ≤ c := h₃
    have ht₄ : t/81 ≤ d := h₄
    gcongr
  exact (not_lt_of_ge hle) (product_gt_self t ht)

/-- Conversion from the usual product-form criterion to odds parameters. -/
lemma odds_product_form {I : Type*} [Fintype I] [DecidableEq I]
    (x p : I → ℝ) (hx : ∀ i, x i < 1)
    (h : ∀ i, p i ≤ x i * ∏ j ∈ Finset.univ.erase i, (1-x j)) (i : I) :
    p i * (∏ j, (1+x j/(1-x j))) ≤ x i/(1-x i) := by
  let D := ∏ j, (1-x j)
  have hD : 0 < D := Finset.prod_pos (fun j _ => sub_pos.mpr (hx j))
  have ht : (∏ j, (1+x j/(1-x j))) = D⁻¹ := by
    calc
      _ = ∏ j, (1-x j)⁻¹ := by
        apply Finset.prod_congr rfl
        intro j _
        field_simp [(sub_pos.mpr (hx j)).ne']
        ring
      _ = D⁻¹ := Finset.prod_inv_distrib _
  have hle : p i ≤ (x i/(1-x i))*D := by
    calc
      p i ≤ x i * ∏ j ∈ Finset.univ.erase i, (1-x j) := h i
      _ = (x i/(1-x i))*D := by
        dsimp [D]
        rw [← Finset.mul_prod_erase Finset.univ (fun j => 1-x j) (Finset.mem_univ i)]
        field_simp [(sub_pos.mpr (hx i)).ne']
  rw [ht]
  simpa only [div_eq_mul_inv] using (div_le_iff₀ hD).mpr hle

/-- Concrete odd, distinct, nontrivial moduli for the limitation example. -/
def modulus : Fin 4 → ℕ := ![3, 9, 27, 81]
def residue : Fin 4 → ℤ := ![0, 2, 8, 26]

lemma modulus_injective : Function.Injective modulus := by decide +kernel
lemma odd_nontrivial : ∀ i, Odd (modulus i) ∧ 1 < modulus i := by decide +kernel
lemma private_points : ∀ i j, (modulus j : ℤ) ∣ residue i - residue j ↔ i = j := by
  decide +kernel
lemma stem_uncovered : ∀ i, ¬ (modulus i : ℤ) ∣ -1 - residue i := by decide +kernel

lemma comparable_incompatible : ∀ i j : Fin 4, i < j →
    (modulus i : ℤ) ∣ modulus j ∧ ¬ (modulus i : ℤ) ∣ residue j-residue i := by
  decide +kernel

lemma disjoint_of_lt (i j : Fin 4) (hij : i < j) (z : ℤ) :
    ¬ ((modulus i : ℤ) ∣ z-residue i ∧ (modulus j : ℤ) ∣ z-residue j) := by
  rintro ⟨hi, hj⟩
  obtain ⟨hd, hn⟩ := comparable_incompatible i j hij
  apply hn
  convert dvd_sub hi (hd.trans hj) using 1; ring

theorem pairwise_disjoint : Pairwise (fun i j : Fin 4 => ∀ z : ℤ,
    ¬ ((modulus i : ℤ) ∣ z-residue i ∧ (modulus j : ℤ) ∣ z-residue j)) := by
  intro i j hij z h
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact disjoint_of_lt i j hlt z h
  · exact disjoint_of_lt j i hgt z h.symm

/-- The usual product-form local-lemma condition for the complete
incompatibility graph of these four classes has no parameters. -/
theorem no_product_criterion : ¬ ∃ x : Fin 4 → ℝ,
    (∀ i, 0 ≤ x i ∧ x i < 1) ∧
    ∀ i, 1/(modulus i : ℝ) ≤ x i * ∏ j ∈ Finset.univ.erase i, (1-x j) := by
  rintro ⟨x, hx, hp⟩
  let u : Fin 4 → ℝ := fun i => x i/(1-x i)
  have hu : ∀ i, 0 ≤ u i := fun i => div_nonneg (hx i).1 (sub_pos.mpr (hx i).2).le
  let t := (1+u 0)*(1+u 1)*(1+u 2)*(1+u 3)
  have ht : (∏ j, (1+x j/(1-x j))) = t := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    dsimp [t, u]
    ring
  have hconv (i : Fin 4) : (1/(modulus i : ℝ))*t ≤ u i := by
    have h := odds_product_form x (fun i => 1/(modulus i : ℝ)) (fun i => (hx i).2) hp i
    rwa [ht] at h
  apply no_four_odds (u 0) (u 1) (u 2) (u 3) (hu 0) (hu 1) (hu 2) (hu 3)
  have h₀ := hconv 0
  have h₁ := hconv 1
  have h₂ := hconv 2
  have h₃ := hconv 3
  change (1/(3 : ℝ))*t ≤ u 0 at h₀
  change (1/(9 : ℝ))*t ≤ u 1 at h₁
  change (1/(27 : ℝ))*t ≤ u 2 at h₂
  change (1/(81 : ℝ))*t ≤ u 3 at h₃
  change t/3 ≤ u 0 ∧ t/9 ≤ u 1 ∧ t/27 ≤ u 2 ∧ t/81 ≤ u 3
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A positive control: the clique-corrected algebraic bound DOES handle
this example. No failure of that sharper bound is claimed. -/
noncomputable def cliqueWeight : Fin 4 → ℝ := ![27/41, 9/41, 3/41, 1/41]

lemma cliqueWeight_nonneg : ∀ i, 0 ≤ cliqueWeight i := by
  intro i
  fin_cases i <;> norm_num [cliqueWeight]

lemma clique_corrected_identity (i : Fin 4) :
    (1/(modulus i : ℝ)) * (1+∑ j, cliqueWeight j) = cliqueWeight i := by
  fin_cases i <;> norm_num [modulus, cliqueWeight, Fin.sum_univ_succ]

theorem not_cover : ¬ ∀ z : ℤ, ∃ i, (modulus i : ℤ) ∣ z-residue i := by
  intro h
  obtain ⟨i, hi⟩ := h (-1)
  exact stem_uncovered i hi

#print axioms no_four_odds
#print axioms odds_product_form
#print axioms pairwise_disjoint
#print axioms no_product_criterion
#print axioms clique_corrected_identity
#print axioms modulus_injective
#print axioms odd_nontrivial
#print axioms private_points
#print axioms not_cover

end Erdos7LocalLemmaBarrier
