import Submission.RisingMonicForms

/-! Root cells for the rising-factorial row polynomials. This auxiliary
result does not settle the irrationality conjecture in Spec.lean. -/

namespace RisingHalfIntegerRoots

open Finset Polynomial

noncomputable def halfProd (n : ℕ) : ℝ :=
  ∏ i ∈ range n, ((i : ℝ)+1/2)

lemma halfProd_pos (n : ℕ) : 0 < halfProd n := by
  apply prod_pos
  intro i _
  positivity

lemma halfProd_succ (n : ℕ) : halfProd (n+1) = halfProd n*((n : ℝ)+1/2) := by
  exact prod_range_succ _ _

lemma halfProd_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : halfProd a ≤ halfProd b := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hb : (1 : ℝ) ≤ b := by exact_mod_cast ha.trans hab
    rw [halfProd_succ]
    nlinarith [halfProd_pos b]

private lemma pair_small (a b : ℕ) (ha : a ≤ 2) (hab : 5 ≤ a+b) :
    1 < halfProd a*halfProd b := by
  interval_cases a
  · have hb := halfProd_mono (a := 5) (b := b) (by omega) (by omega)
    norm_num [halfProd, prod_range_succ] at hb ⊢
    linarith
  · have hb := halfProd_mono (a := 4) (b := b) (by omega) (by omega)
    norm_num [halfProd, prod_range_succ] at hb ⊢
    linarith
  · have hb := halfProd_mono (a := 3) (b := b) (by omega) (by omega)
    norm_num [halfProd, prod_range_succ] at hb ⊢
    linarith

lemma halfProd_pair_gt_one (a b : ℕ) (hab : 5 ≤ a+b) :
    1 < halfProd a*halfProd b := by
  by_cases ha : a ≤ 2
  · exact pair_small a b ha hab
  by_cases hb : b ≤ 2
  · simpa only [mul_comm] using pair_small b a hb (by omega)
  have ha' := halfProd_mono (a := 3) (b := a) (by omega) (by omega)
  have hb' := halfProd_mono (a := 3) (b := b) (by omega) (by omega)
  norm_num [halfProd, prod_range_succ] at ha' hb'
  change (15/8 : ℝ) ≤ halfProd a at ha'
  change (15/8 : ℝ) ≤ halfProd b at hb'
  nlinarith [halfProd_pos a, halfProd_pos b]

noncomputable def rising (k : ℕ) (x : ℝ) : ℝ :=
  ∏ i ∈ range k, (x+((i+1 : ℕ) : ℝ))

lemma rising_continuous (k : ℕ) : Continuous (rising k) := by
  unfold rising
  fun_prop

private lemma negative_half_prod (a : ℕ) :
    (∏ i ∈ range a, ((i : ℝ)-(a : ℝ)+1/2)) = (-1 : ℝ)^a*halfProd a := by
  induction a with
  | zero => simp [halfProd]
  | succ a ih =>
    rw [prod_range_succ']
    have he : (∏ i ∈ range a, (((i+1 : ℕ) : ℝ)-((a+1 : ℕ) : ℝ)+1/2)) =
        ∏ i ∈ range a, ((i : ℝ)-(a : ℝ)+1/2) := by
      apply prod_congr rfl
      intro i _
      push_cast
      ring
    rw [he, ih, halfProd_succ, pow_succ]
    push_cast
    ring

lemma rising_at_half (a b : ℕ) :
    rising (a+b) (-(a : ℝ)-1/2) = (-1 : ℝ)^a*halfProd a*halfProd b := by
  rw [rising, prod_range_add]
  have hleft : (∏ i ∈ range a, (-(a : ℝ)-1/2+((i+1 : ℕ) : ℝ))) =
      (-1 : ℝ)^a*halfProd a := by
    convert negative_half_prod a using 1
    apply prod_congr rfl
    intro i _
    push_cast
    ring
  have hright : (∏ i ∈ range b, (-(a : ℝ)-1/2+((a+i+1 : ℕ) : ℝ))) =
      halfProd b := by
    unfold halfProd
    apply prod_congr rfl
    intro i _
    push_cast
    ring
  rw [hleft, hright]

lemma rising_at_even_half_gt_one (a b : ℕ) (ha : Even a) (hab : 5 ≤ a+b) :
    1 < rising (a+b) (-(a : ℝ)-1/2) := by
  rw [rising_at_half, ha.neg_one_pow, one_mul]
  exact halfProd_pair_gt_one a b hab

lemma rising_at_negative_integer (k m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) :
    rising k (-(m : ℝ)) = 0 := by
  unfold rising
  apply prod_eq_zero (mem_range.mpr (show m-1 < k by omega))
  rw [show m-1+1=m by omega]
  ring

lemma rising_eq_pochhammer (k : ℕ) (x : ℝ) :
    rising k x = (ascPochhammer ℝ k).eval (x+1) := by
  induction k with
  | zero => simp [rising]
  | succ k ih =>
    rw [rising, prod_range_succ]
    change rising k x * _ = _
    rw [ih, ascPochhammer_succ_eval]
    congr 1
    push_cast
    ring

lemma row_eval (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    (RisingMonicForms.rowPolynomial (k-1)).eval₂ (Int.castRingHom ℝ) x =
      rising k x-1 := by
  rw [RisingMonicForms.rowPolynomial]
  simp only [eval₂_sub, eval₂_comp, eval₂_add, eval₂_X, eval₂_one,
    map_one, ← ascPochhammer_eval₂, show k-1+1=k by omega]
  rw [rising_eq_pochhammer]

/-- Each row of degree at least five has a root strictly inside each
negative-integer half-cell. The cells are disjoint. -/
theorem root_in_cell (k m : ℕ) (hk : 5 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k) :
    ∃ x : ℝ, -(m : ℝ)-1/2 < x ∧ x < -(m : ℝ)+1/2 ∧
      (RisingMonicForms.rowPolynomial (k-1)).eval₂ (Int.castRingHom ℝ) x = 0 := by
  have hz := rising_at_negative_integer k m hm hmk
  rcases Nat.even_or_odd m with he | ho
  · have hp : 1 < rising k (-(m : ℝ)-1/2) := by
      simpa only [Nat.add_sub_of_le hmk] using
        rising_at_even_half_gt_one m (k-m) he (by omega)
    obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc'
      (show -(m : ℝ)-1/2 ≤ -(m : ℝ) by linarith)
      (rising_continuous k).continuousOn
      (show (1 : ℝ) ∈ Set.Icc (rising k (-(m : ℝ)))
        (rising k (-(m : ℝ)-1/2)) from ⟨by rw [hz]; norm_num, hp.le⟩)
    have hxl : -(m : ℝ)-1/2 < x := by
      rcases hx.1.eq_or_lt with heq | hlt
      · rw [← heq] at hxe
        linarith
      · exact hlt
    refine ⟨x, hxl, by linarith [hx.2], ?_⟩
    rw [row_eval k (by omega), hxe, sub_self]
  · have he : Even (m-1) := by
      rw [Nat.even_iff]
      have ho' := Nat.odd_iff.mp ho
      omega
    have hp : 1 < rising k (-(m : ℝ)+1/2) := by
      have h := rising_at_even_half_gt_one (m-1) (k-(m-1)) he (by omega)
      rw [Nat.add_sub_of_le (by omega : m-1 ≤ k),
        Nat.cast_sub hm, Nat.cast_one] at h
      convert h using 1
      congr 1
      ring
    obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc
      (show -(m : ℝ) ≤ -(m : ℝ)+1/2 by linarith)
      (rising_continuous k).continuousOn
      (show (1 : ℝ) ∈ Set.Icc (rising k (-(m : ℝ)))
        (rising k (-(m : ℝ)+1/2)) from ⟨by rw [hz]; norm_num, hp.le⟩)
    have hxr : x < -(m : ℝ)+1/2 := by
      rcases hx.2.eq_or_lt with heq | hlt
      · rw [heq] at hxe
        linarith
      · exact hlt
    refine ⟨x, by linarith [hx.1], hxr, ?_⟩
    rw [row_eval k (by omega), hxe, sub_self]

/-- The roots in the cells exhaust the roots, with no repetitions. Thus the
row polynomial splits over the reals into simple roots. -/
theorem root_enumeration (k : ℕ) (hk : 5 ≤ k) :
    ∃ r : Fin k → ℝ, Function.Injective r ∧
      (∀ i, -((i.val+1 : ℕ) : ℝ)-1/2 < r i ∧
        r i < -((i.val+1 : ℕ) : ℝ)+1/2) ∧
      ((RisingMonicForms.rowPolynomial (k-1)).map (Int.castRingHom ℝ)).roots =
        (univ.image r).val := by
  classical
  have hex (i : Fin k) := root_in_cell k (i.val+1) hk (by omega) (by omega)
  choose r hr using hex
  have hinj : Function.Injective r := by
    intro i j heq
    apply Fin.ext
    have hi := hr i
    have hj := hr j
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (i.val : ℝ)+1 ≤ j.val := by
        exact_mod_cast (show i.val+1 ≤ j.val by omega)
      norm_num only [Nat.cast_add, Nat.cast_one] at hi hj
      rw [heq] at hi
      linarith [hi.1, hj.2.1]
    · have hle : (j.val : ℝ)+1 ≤ i.val := by
        exact_mod_cast (show j.val+1 ≤ i.val by omega)
      norm_num only [Nat.cast_add, Nat.cast_one] at hi hj
      rw [heq] at hi
      linarith [hj.1, hi.2.1]
  refine ⟨r, hinj, fun i => ⟨(hr i).1, (hr i).2.1⟩, ?_⟩
  apply roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    simpa only [eval_map] using (hr i).2.2
  · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
    have hd := natDegree_map_le (p := RisingMonicForms.rowPolynomial (k-1))
      (f := Int.castRingHom ℝ)
    rw [RisingMonicForms.rowPolynomial_natDegree] at hd
    omega
  · exact ((RisingMonicForms.rowPolynomial_monic (k-1)).map (Int.castRingHom ℝ)).ne_zero

end RisingHalfIntegerRoots

#print axioms RisingHalfIntegerRoots.halfProd_pair_gt_one
#print axioms RisingHalfIntegerRoots.root_in_cell
#print axioms RisingHalfIntegerRoots.root_enumeration
