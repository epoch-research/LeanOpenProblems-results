import Submission.LambertRelativeCombinationBound

/-! Finite phase-mass estimates for Lambert row combinations.
These estimates do not assert integrality of the output boundaries. -/

namespace LambertCyclicMass

open Finset LambertDifferenceOperators LambertRawBounds LambertTailRows
  FactorialGeometricProductBound LambertCyclicRowLowerBound
  LambertCyclicCombinationLowerBound LambertLongBoundedCombinations
  LambertRelativeCombinationBound

noncomputable section

section FiniteMass
variable {ι : Type*} [Fintype ι]

def mass (f : ι → ℝ) : ℝ := ∑ i, |f i|

lemma mass_nonneg (f : ι → ℝ) : 0 ≤ mass f := Finset.sum_nonneg (by intros; positivity)

lemma abs_le_mass (f : ι → ℝ) (i : ι) : |f i| ≤ mass f := by
  change |f i| ≤ ∑ j, |f j|
  exact Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)

lemma norm_le_mass (f : ι → ℝ) : ‖f‖ ≤ mass f := by
  apply (pi_norm_le_iff_of_nonneg (mass_nonneg f)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using abs_le_mass f i

lemma mass_comp (f : ι → ℝ) (e : Equiv.Perm ι) : mass (f ∘ e) = mass f :=
  Equiv.sum_comp e (fun i => |f i|)

lemma mass_sub_le (f g : ι → ℝ) : mass (fun i => f i-g i) ≤ mass f+mass g := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (by intro i _; exact abs_sub _ _)

lemma shift_mass_lower (f : ι → ℝ) (e : Equiv.Perm ι) (t : ℝ) (ht : 0 ≤ t) :
    (1-t)*mass f ≤ mass (fun i => t*f (e i)-f i) := by
  have he : (∑ i, |f (e i)|) = mass f := Equiv.sum_comp e (fun i => |f i|)
  have hp (i : ι) : |f i| ≤ |t*f (e i)-f i|+t*|f (e i)| := by
    have h := abs_sub (t*f (e i)) (t*f (e i)-f i)
    rw [show t*f (e i)-(t*f (e i)-f i)=f i by ring,
      abs_mul, abs_of_nonneg ht] at h
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, he] at hs
  change mass f ≤ mass (fun i => t*f (e i)-f i)+t*mass f at hs
  nlinarith
end FiniteMass

variable (d : ℕ) [NeZero d]

def group (s : Finset ℕ) (f : ℕ → ℝ) (h : ZMod d) : ℝ :=
  ∑ j ∈ s, if (j : ZMod d)=h then f j else 0

lemma sum_group (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ h : ZMod d, group d s f h) = ∑ j ∈ s, f j := by
  classical
  unfold group
  rw [Finset.sum_comm]
  simp

lemma mass_group_le (s : Finset ℕ) (f : ℕ → ℝ) :
    mass (group d s f) ≤ ∑ j ∈ s, |f j| := by
  classical
  calc
    _ ≤ ∑ h : ZMod d, group d s (fun j => |f j|) h := by
      apply Finset.sum_le_sum
      intro h _
      apply (abs_sum_le_sum_abs _ _).trans_eq
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ = _ := sum_group d s _

lemma initial_group_value (N : ℕ) (hN : N ≤ d) (f : ℕ → ℝ) (h : ZMod d) :
    group d (Finset.range N) f h = if h.val<N then f h.val else 0 := by
  classical
  have he (j : ℕ) (hj : j ∈ Finset.range N) : (j : ZMod d)=h ↔ j=h.val := by
    have hjd : j<d := by have := Finset.mem_range.mp hj; omega
    constructor
    · intro hh
      have hv := congrArg ZMod.val hh
      simpa only [ZMod.val_natCast_of_lt hjd] using hv
    · intro hh
      rw [hh, ZMod.natCast_zmod_val]
  unfold group
  calc
    _ = ∑ j ∈ Finset.range N, if j=h.val then f j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [he j hj]
    _ = _ := by simp

lemma initial_group_mass (N : ℕ) (hN : N ≤ d) (f : ℕ → ℝ) :
    mass (group d (Finset.range N) f) = ∑ j ∈ Finset.range N, |f j| := by
  calc
    _ = ∑ h : ZMod d, group d (Finset.range N) (fun j => |f j|) h := by
      apply Finset.sum_congr rfl
      intro h _
      rw [initial_group_value d N hN f, initial_group_value d N hN (fun j => |f j|)]
      split_ifs <;> simp
    _ = _ := sum_group d _ _

/-- The total weighted coefficient mass is at most three times its cyclic
aggregate mass. The constant is independent of d, Q, and support length. -/
theorem weighted_mass_le_three (M Q : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hw0 : w 0 ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ)) :
    (∑ j ∈ Finset.range (M+1), |(w j : ℝ)|/rate d^j) ≤
      3*mass (aggregate d M w) := by
  classical
  have hp := rate_pos d
  let f : ℕ → ℝ := fun j => (w j : ℝ)/rate d^j
  have hf (j : ℕ) : |f j| = |(w j : ℝ)|/rate d^j := by
    dsimp only [f]
    rw [abs_div, abs_of_pos (pow_pos hp _)]
  let a := group d (Finset.range (min d (M+1))) f
  let b := group d (Finset.Ico d (M+1)) f
  have he : Finset.Ico (min d (M+1)) (M+1)=Finset.Ico d (M+1) := by
    ext j
    simp only [Finset.mem_Ico]
    omega
  have hsplit : aggregate d M w = fun h => a h+b h := by
    funext h
    change (∑ j ∈ Finset.range (M+1), if (j : ZMod d)=h then f j else 0) = _
    rw [← Finset.sum_range_add_sum_Ico (f := fun j => if (j : ZMod d)=h then f j else 0)
      (min_le_right d (M+1)), he]
    rfl
  have hmass := mass_group_le d (Finset.Ico d (M+1)) f
  simp only [hf] at hmass
  have hlate := late_mass_bound d M Q w hd hQ hw
  have ha : mass a ≤ mass (aggregate d M w)+mass b := by
    have hh := mass_sub_le (aggregate d M w) b
    have hfun : (fun h => aggregate d M w h-b h)=a := by
      funext h
      rw [hsplit]
      simp
    rwa [hfun] at hh
  have haeq : mass a = ∑ j ∈ Finset.range (min d (M+1)), |(w j : ℝ)|/rate d^j := by
    simpa only [a, hf] using initial_group_mass d (min d (M+1)) (min_le_left _ _) f
  have hnorm : (1/2 : ℝ) ≤ mass (aggregate d M w) :=
    (aggregate_zero_lower d M Q w hd hQ hw0 hw).trans (norm_le_mass _)
  rw [← Finset.sum_range_add_sum_Ico (f := fun j => |(w j : ℝ)|/rate d^j)
    (min_le_right d (M+1)), he, ← haeq]
  change mass (group d (Ico d (M+1)) f) ≤ _ at hmass
  change mass b ≤ _ at hmass
  linarith

lemma cyclicApply_mass_lower (ks : List ℕ)
    (hks : ∀ k ∈ ks, (k.factorial : ℝ)/rate d^k ≤ 1) (f : ZMod d → ℝ) :
    (ks.map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod * mass f ≤
      mass (cyclicApply d ks f) := by
  have hrate := rate_pos d
  induction ks generalizing f with
  | nil => simp [cyclicApply]
  | cons k ks ih =>
    have hp : 0 ≤ (ks.map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      linarith [hks j (by simp [hj])]
    have hb := shift_mass_lower f (Equiv.addRight (k : ZMod d))
      ((k.factorial : ℝ)/rate d^k) (by positivity)
    have hi := ih (fun j hj => hks j (by simp [hj])) (cyclicShift d k f)
    change _ ≤ mass (cyclicApply d ks (cyclicShift d k f))
    simp only [List.map_cons, List.prod_cons]
    calc
      _ = (ks.map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod *
          ((1-(k.factorial : ℝ)/rate d^k)*mass f) := by ring
      _ ≤ (ks.map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod *
          mass (cyclicShift d k f) := mul_le_mul_of_nonneg_left hb hp
      _ ≤ _ := hi

lemma convolution_mass_lower (hd : 2 ≤ d) (c : ZMod d → ℝ) :
    mass c/(rate d+1) ≤ mass (convolve d c (rowModel d)) := by
  have hp := rate_pos d
  have he : (∑ h : ZMod d, |c (-h-1)|) = mass c := by
    simpa [mass, sub_eq_add_neg] using
      Equiv.sum_comp ((Equiv.neg (ZMod d)).trans (Equiv.addRight (-1))) (fun h => |c h|)
  have hs : (∑ h : ZMod d, |convolve d c (rowModel d) (h+1)|) =
      mass (convolve d c (rowModel d)) :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod d)) (fun h => |convolve d c (rowModel d) h|)
  have hb (h : ZMod d) : |c (-h-1)| ≤
      rate d*|convolve d c (rowModel d) h|+|convolve d c (rowModel d) (h+1)| := by
    rw [← convolve_jump d hd c h]
    exact (abs_sub _ _).trans_eq (by rw [abs_mul, abs_of_pos hp])
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hb h)
  rw [he, Finset.sum_add_distrib, ← Finset.mul_sum, hs] at hh
  change mass c ≤ rate d*mass (convolve d c (rowModel d)) +
    mass (convolve d c (rowModel d)) at hh
  exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)

/-- Full-phase first-row mass, before clearing any rational boundary. -/
theorem first_row_mass_lower (K : ℕ) (hd : 12 ≤ d) (hKd : K+1 < d)
    (c : ZMod d → ℝ) :
    Real.exp (-48)*mass c/(rate d+1) ≤
      mass (cyclicApply d (List.range' 2 K) (convolve d c (rowModel d))) := by
  have hrate := rate_pos d
  have hprod := lower_product_uniform K d hd hKd
  have hcn := convolution_mass_lower d (by omega) c
  have ho := cyclicApply_mass_lower d (List.range' 2 K) (by
    intro k hk
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp hk
    exact (normalized_factorial_le_three_quarters d k hd (by omega) (by omega)).trans
      (by norm_num)) (convolve d c (rowModel d))
  calc
    _ = Real.exp (-48)*(mass c/(rate d+1)) := by ring
    _ ≤ ((List.range' 2 K).map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod *
        mass (convolve d c (rowModel d)) :=
      mul_le_mul hprod hcn (div_nonneg (mass_nonneg c) (by positivity))
        ((Real.exp_pos _).le.trans hprod)
    _ ≤ _ := ho

end
end LambertCyclicMass

#print axioms LambertCyclicMass.weighted_mass_le_three
#print axioms LambertCyclicMass.first_row_mass_lower
