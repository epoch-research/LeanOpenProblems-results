import Submission.FiniteRetentionKernel

/-! Two-tier branch/density retention, a local lemma only.
This file does not settle the odd covering-system conjecture. -/
namespace Erdos7TwoTierRetentionKernel
open scoped BigOperators
open Erdos7FiniteRetentionKernel
set_option maxHeartbeats 1500000

/-- Packing into full branches and at most one partial branch gives a valid
lower bound for every finite family of good-branch fractions. The integer b
can be chosen to be the floor of their total, but that choice is not needed
for validity of the inequality. -/
theorem sum_min_lower {A : Type*} [Fintype A]
    (g : A → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (L H : ℝ) (hL : 0 ≤ L) (hLH : L ≤ H) (b : ℕ) :
    (b : ℝ)*L + min L (H*((∑ x, g x)-b)) ≤
      ∑ x, min L (H*g x) := by
  classical
  let s : Finset A := Finset.univ.filter (fun x => L ≤ H*g x)
  let t : Finset A := Finset.univ.filter (fun x => ¬ L ≤ H*g x)
  let R : ℝ := ∑ x ∈ t, g x
  have hH : 0 ≤ H := hL.trans hLH
  have hR : 0 ≤ R := Finset.sum_nonneg (fun x _ => hg0 x)
  have hsplit (f : A → ℝ) : (∑ x, f x) = (∑ x ∈ s, f x)+(∑ x ∈ t, f x) := by
    symm
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hsum : (∑ x, min L (H*g x)) = (s.card : ℝ)*L+H*R := by
    rw [hsplit]
    have hs : (∑ x ∈ s, min L (H*g x)) = (s.card : ℝ)*L := by
      calc
        _ = ∑ _x ∈ s, L := Finset.sum_congr rfl (fun x hx =>
          min_eq_left ((Finset.mem_filter.mp hx).2))
        _ = _ := by simp
    have ht : (∑ x ∈ t, min L (H*g x)) = H*R := by
      calc
        _ = ∑ x ∈ t, H*g x := Finset.sum_congr rfl (fun x hx =>
          min_eq_right (le_of_not_ge ((Finset.mem_filter.mp hx).2)))
        _ = _ := by rw [← Finset.mul_sum]
    rw [hs,ht]
  have htotal : (∑ x, g x) ≤ (s.card : ℝ)+R := by
    rw [hsplit]
    have hh : (∑ x ∈ s, g x) ≤ (s.card : ℝ) := by
      calc
        _ ≤ ∑ _x ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hg1 x)
        _ = _ := by simp
    exact add_le_add hh (le_refl R)
  rw [hsum]
  by_cases hsb : s.card ≤ b
  · have hsb' : (s.card : ℝ) ≤ b := by exact_mod_cast hsb
    have hm := mul_nonneg (sub_nonneg.mpr hsb') (sub_nonneg.mpr hLH)
    have ht := mul_le_mul_of_nonneg_left htotal hH
    have hmin := min_le_right L (H*((∑ x, g x)-b))
    nlinarith
  · have hbs : b+1 ≤ s.card := by omega
    have hbs' : (b : ℝ)+1 ≤ s.card := by exact_mod_cast hbs
    have hm := mul_le_mul_of_nonneg_right hbs' hL
    have hr := mul_nonneg hH hR
    have hmin := min_le_left L (H*((∑ x, g x)-b))
    nlinarith

/-- Full branches, one fractional branch, and empty branches attain the bound.
Together with `sum_min_lower`, this proves sharpness for any total b+r with
0≤r≤1, whenever there are enough branches. -/
theorem packed_profile_attains (b n : ℕ) (r L H : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hLH : L ≤ H) :
    ∃ g : Fin b ⊕ (Unit ⊕ Fin n) → ℝ,
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      (∑ x, g x) = (b : ℝ)+r ∧
      (∑ x, min L (H*g x)) = (b : ℝ)*L+min L (H*r) := by
  let g : Fin b ⊕ (Unit ⊕ Fin n) → ℝ :=
    Sum.elim (fun _ => 1) (Sum.elim (fun _ => r) (fun _ => 0))
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x
    rcases x with x | x
    · norm_num [g]
    · rcases x with x | x
      · exact ⟨hr0,hr1⟩
      · norm_num [g]
  · simp [g, Fintype.sum_sum_type]
  · simp [g, Fintype.sum_sum_type, min_eq_left hLH, min_eq_right hL]


/-- The sharp lower branch-capacity function as a function of total good volume. -/
noncomputable def packed (L H t : ℝ) : ℝ :=
  (⌊t⌋₊ : ℝ)*L+min L (H*(t-⌊t⌋₊))

theorem packed_nonneg (L H t : ℝ) (hL : 0 ≤ L) (hH : 0 ≤ H) (ht : 0 ≤ t) :
    0 ≤ packed L H t := by
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hL)
    (le_min hL (mul_nonneg hH (sub_nonneg.mpr (Nat.floor_le ht))))

theorem packed_monotoneOn (L H : ℝ) (hL : 0 ≤ L) (hLH : L ≤ H) :
    MonotoneOn (packed L H) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hH : 0 ≤ H := hL.trans hLH
  have hfloor := Nat.floor_mono hxy
  by_cases he : ⌊x⌋₊=⌊y⌋₊
  · dsimp only [packed]
    rw [he]
    exact add_le_add le_rfl (min_le_min le_rfl
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy _) hH))
  · have hstrict : ⌊x⌋₊+1 ≤ ⌊y⌋₊ := by omega
    have hstrict' : (⌊x⌋₊ : ℝ)+1 ≤ ⌊y⌋₊ := by exact_mod_cast hstrict
    have hmul := mul_le_mul_of_nonneg_right hstrict' hL
    have hminx := min_le_left L (H*(x-⌊x⌋₊))
    have hminy : 0 ≤ min L (H*(y-⌊y⌋₊)) :=
      le_min hL (mul_nonneg hH (sub_nonneg.mpr (Nat.floor_le hy)))
    dsimp only [packed]
    nlinarith

noncomputable def retained (p L H α : ℝ) : ℝ :=
  max 0 (min 1 (packed L H (p*(1-α))/p))

theorem retained_antitoneOn (p L H : ℝ) (hp : 0 < p)
    (hL : 0 ≤ L) (hLH : L ≤ H) :
    AntitoneOn (retained p L H) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have hta : 0 ≤ p*(1-a) := mul_nonneg hp.le (sub_nonneg.mpr ha.2)
  have htb : 0 ≤ p*(1-b) := mul_nonneg hp.le (sub_nonneg.mpr hb.2)
  have ht : p*(1-b) ≤ p*(1-a) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hab _) hp.le
  exact max_le_max le_rfl (min_le_min le_rfl (div_le_div_of_nonneg_right
    (packed_monotoneOn L H hL hLH htb hta ht) hp.le))

/-- At an integral current count, the two-tier availability lies between the
old low-cap availability and that of the equal cap with the same first moment.
This statement alone is not an LP optimality or noncoverage theorem. -/
theorem integral_availability_bounds (p k L H : ℝ) (hp : 1 < p)
    (hk0 : 0 ≤ k) (hk1 : k ≤ p-1) (hL : 0 ≤ L) (hLH : L ≤ H) :
    L*(1-k/(p-1)) ≤
        ((p-k-1)*L+min L (H*(1-k/(p-1))))/p ∧
    ((p-k-1)*L+min L (H*(1-k/(p-1))))/p ≤
        (((p-1)*L+H)/p)*(1-k/(p-1)) := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < p-1 := by linarith
  have hu0 : 0 ≤ 1-k/(p-1) := sub_nonneg.mpr ((div_le_one hq).mpr hk1)
  have hu1 : 1-k/(p-1) ≤ 1 := by
    have := div_nonneg hk0 hq.le
    linarith
  have he : p-k-1 = (p-1)*(1-k/(p-1)) := by field_simp; ring
  constructor
  · apply (le_div_iff₀ hp0).mpr
    have hmin : L*(1-k/(p-1)) ≤ min L (H*(1-k/(p-1))) := by
      apply le_min
      · nlinarith
      · exact mul_le_mul_of_nonneg_right hLH hu0
    rw [he]
    nlinarith
  · rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hp0).mpr
    rw [he]
    have hmin := min_le_right L (H*(1-k/(p-1)))
    nlinarith

/-- A genuine finite kernel, with uniform first-digit branch law and arbitrary
common within-branch probability law. The total mass may be thinned to any
nonnegative target below the packed lower bound. -/
theorem exists_two_tier_kernel {A B : Type*} [Fintype A] [Fintype B]
    (hA : 0 < Fintype.card A) (ρ : B → ℝ)
    (hρ : ∀ y, 0 ≤ ρ y) (hρmass : (∑ y, ρ y)=1)
    (bad : A → B → Prop) [∀ x y, Decidable (bad x y)]
    (L H h : ℝ) (hL : 0 ≤ L) (hLH : L ≤ H) (hh : 0 ≤ h) (b : ℕ)
    (hbound : h ≤ ((b : ℝ)*L +
      min L (H*((∑ x, (1-∑ y, if bad x y then ρ y else 0))-b))) / Fintype.card A) :
    ∃ ν : A → B → ℝ,
      (∀ x y, 0 ≤ ν x y) ∧
      (∀ x y, ν x y ≤ H*ρ y/Fintype.card A) ∧
      (∀ x, (∑ y, ν x y) ≤ L/Fintype.card A) ∧
      (∀ x y, bad x y → ν x y=0) ∧
      (∑ x, ∑ y, ν x y)=h := by
  classical
  let g (x : A) : ℝ := 1-∑ y, if bad x y then ρ y else 0
  have hg0 (x : A) : 0 ≤ g x := by
    apply sub_nonneg.mpr
    rw [← hρmass]
    apply Finset.sum_le_sum
    intro y _
    split_ifs
    · exact le_rfl
    · exact hρ y
  have hg1 (x : A) : g x ≤ 1 := by
    have hr : 0 ≤ ∑ y, if bad x y then ρ y else 0 := by
      apply Finset.sum_nonneg
      intro y _
      split_ifs
      · exact hρ y
      · exact le_rfl
    dsimp only [g]
    linarith
  have hH : 0 ≤ H := hL.trans hLH
  have ht0 (x : A) : 0 ≤ min L (H*g x) := le_min hL (mul_nonneg hH (hg0 x))
  obtain ⟨v,hv,hvcap,hvzero,hvmass⟩ := exists_retention_kernel
    (fun _ : A => (1 : ℝ)) (fun _ => by norm_num) ρ hρ hρmass bad
    (fun x => min L (H*g x)) H hH ht0 (fun x => min_le_right _ _)
  let w (z : A × B) : ℝ := v z.1 z.2/Fintype.card A
  have hp : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have hw (z : A × B) : 0 ≤ w z := div_nonneg (hv z.1 z.2) hp.le
  have hm : (∑ z, w z) = (∑ x, min L (H*g x))/Fintype.card A := by
    rw [Fintype.sum_prod_type]
    simp only [w, ← Finset.sum_div, hvmass, one_mul]
  have hav : h ≤ ∑ z, w z := by
    rw [hm]
    exact hbound.trans (div_le_div_of_nonneg_right (sum_min_lower g hg0 hg1 L H hL hLH b) hp.le)
  obtain ⟨ν,hν,hνmass⟩ := exists_thinning (fun _ : Unit => w) (fun _ => h)
    (fun _ => hw) (fun _ => hh) (fun _ => hav)
  refine ⟨fun x y => ν () (x,y), (fun x y => (hν () (x,y)).1), ?_, ?_, ?_, ?_⟩
  · intro x y
    apply (hν () (x,y)).2.trans
    apply div_le_div_of_nonneg_right _ hp.le
    simpa only [mul_one] using hvcap x y
  · intro x
    calc
      _ ≤ ∑ y, w (x,y) := Finset.sum_le_sum (fun y _ => (hν () (x,y)).2)
      _ = min L (H*g x)/Fintype.card A := by simp only [w, ← Finset.sum_div, hvmass, one_mul]
      _ ≤ _ := div_le_div_of_nonneg_right (min_le_left _ _) hp.le
  · intro x y hb
    apply le_antisymm _ (hν () (x,y)).1
    simpa only [w,hvzero x y hb,zero_div] using (hν () (x,y)).2
  · simpa only [Fintype.sum_prod_type] using hνmass ()

#print axioms sum_min_lower
#print axioms packed_profile_attains
#print axioms packed_monotoneOn
#print axioms retained_antitoneOn
#print axioms integral_availability_bounds
#print axioms exists_two_tier_kernel
end Erdos7TwoTierRetentionKernel
