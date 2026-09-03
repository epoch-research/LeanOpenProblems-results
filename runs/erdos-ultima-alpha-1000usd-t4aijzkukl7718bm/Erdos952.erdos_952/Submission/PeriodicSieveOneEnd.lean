import Submission.PeriodicSieveEndsLogic

/-! Finite-box detours in the unique infinite component of a periodic sieve. -/
namespace Erdos952Investigation.PeriodicSieveEnds
open FiniteSieveReduction PeriodicSieveComponents SieveInfiniteUniqueness PeriodicSievePlanarity
set_option maxHeartbeats 0

lemma coarse_horizontal {C : ℤ} {N : ℕ} (H : SimpleGraph GaussianInt)
    (R B : ℤ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hH : ∀ {a b}, (sieveGraph C N).Adj a b → Outside R a → Outside R b → H.Adj a b)
    {z : GaussianInt} (px : (sieveGraph C N).Walk z (z+shift N 1 0))
    (hpx : walkRadius px ≤ B) (l : ℤ) (hl : R+B < |l|) (i j : ℤ) :
    H.Reachable (z+shift N i l) (z+shift N j l) := by
  apply reachable_int_line (fun k => z+shift N k l) _ i j
  intro k
  have hh := translate_walk_avoiding H R B hR hB hH px hpx k l (Or.inr hl)
  simpa only [add_assoc,shift_x_succ] using hh

lemma coarse_vertical {C : ℤ} {N : ℕ} (H : SimpleGraph GaussianInt)
    (R B : ℤ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hH : ∀ {a b}, (sieveGraph C N).Adj a b → Outside R a → Outside R b → H.Adj a b)
    {z : GaussianInt} (py : (sieveGraph C N).Walk z (z+shift N 0 1))
    (hpy : walkRadius py ≤ B) (k : ℤ) (hk : R+B < |k|) (i j : ℤ) :
    H.Reachable (z+shift N k i) (z+shift N k j) := by
  apply reachable_int_line (fun l => z+shift N k l) _ i j
  intro l
  have hh := translate_walk_avoiding H R B hR hB hH py hpy k l (Or.inl hk)
  simpa only [add_assoc,shift_y_succ] using hh

lemma coarse_grid_detour {C : ℤ} {N : ℕ} (H : SimpleGraph GaussianInt)
    (R B : ℤ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hH : ∀ {a b}, (sieveGraph C N).Adj a b → Outside R a → Outside R b → H.Adj a b)
    {z : GaussianInt} (px : (sieveGraph C N).Walk z (z+shift N 1 0))
    (py : (sieveGraph C N).Walk z (z+shift N 0 1))
    (hpx : walkRadius px ≤ B) (hpy : walkRadius py ≤ B)
    (k l : ℤ) (hlarge : R+B < |k| ∨ R+B < |l|) :
    H.Reachable (z+shift N k l) (z+shift N (R+B+1) (R+B+1)) := by
  have hT : R+B < |R+B+1| := by rw [abs_of_nonneg (by omega : 0 ≤ R+B+1)]; omega
  rcases hlarge with hk | hl
  · exact (coarse_vertical H R B hR hB hH py hpy k hk l (R+B+1)).trans
      (coarse_horizontal H R B hR hB hH px hpx (R+B+1) hT k (R+B+1))
  · exact (coarse_horizontal H R B hR hB hH px hpx l hl k (R+B+1)).trans
      (coarse_vertical H R B hR hB hH py hpy (R+B+1) hT l (R+B+1))

lemma reachable_representative {C : ℤ} {N : ℕ} {z v : GaussianInt}
    (hz : {w | (sieveGraph C N).Reachable z w}.Infinite)
    (hv : (sieveGraph C N).Reachable z v) :
    (sieveGraph C N).Reachable z (representative N (residue N v)) := by
  let w := representative N (residue N v)
  have hd : IsPeriod N (w-v) :=
    period_of_same_residue (residue_representative N (residue N v)).symm
  have hbase := infinite_component_reaches_all_periods hz (w-v) hd
  have ht := reachable_add_period hv hd
  have he : v+(w-v) = w := by abel
  rw [he] at ht
  exact hbase.trans ht

lemma far_indices (N : ℕ) (R B : ℤ) {v w : GaussianInt} {k l : ℤ}
    (hw : |w.re| ≤ B ∧ |w.im| ≤ B) (he : v = w+shift N k l)
    (hv : Outside (B+(N.factorial : ℤ)*(R+B)) v) : R+B < |k| ∨ R+B < |l| := by
  by_contra! hs
  have hM : (0 : ℤ) ≤ N.factorial := Int.natCast_nonneg _
  have hkr := mul_le_mul_of_nonneg_left hs.1 hM
  have hlr := mul_le_mul_of_nonneg_left hs.2 hM
  have hr := abs_add_le w.re ((N.factorial : ℤ)*k)
  have hi := abs_add_le w.im ((N.factorial : ℤ)*l)
  rw [abs_mul,abs_of_nonneg hM] at hr hi
  rw [he] at hv
  rcases hv with hv | hv <;> dsimp [shift] at hv <;> linarith

/-- After a finite region is removed or modified, all sufficiently distant
vertices of the infinite sieve component still connect to one common vertex. -/
theorem far_component_detours {C : ℤ} {N : ℕ} {z : GaussianInt}
    (hz : {w | (sieveGraph C N).Reachable z w}.Infinite)
    (H : SimpleGraph GaussianInt) (R : ℤ) (hR : 0 ≤ R)
    (hH : ∀ {a b}, (sieveGraph C N).Adj a b → Outside R a → Outside R b → H.Adj a b) :
    ∃ F : ℤ, 0 ≤ F ∧ ∃ a : GaussianInt, ∀ v : GaussianInt,
      (sieveGraph C N).Reachable z v → Outside F v → H.Reachable a v := by
  classical
  letI : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩
  let Cell := {r : ZMod N.factorial × ZMod N.factorial //
    (sieveGraph C N).Reachable z (representative N r)}
  letI : Fintype Cell := Fintype.ofFinite Cell
  let pr (r : Cell) : (sieveGraph C N).Walk z (representative N r.val) := Classical.choice r.property
  obtain ⟨px⟩ := infinite_component_reaches_all_periods hz (shift N 1 0) (shift_period N 1 0)
  obtain ⟨py⟩ := infinite_component_reaches_all_periods hz (shift N 0 1) (shift_period N 0 1)
  let S : ℤ := ∑ r : Cell, walkRadius (pr r)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => walkRadius_nonneg _)
  let B : ℤ := walkRadius px+walkRadius py+S
  have hpx0 := walkRadius_nonneg px
  have hpy0 := walkRadius_nonneg py
  have hB : 0 ≤ B := by dsimp [B]; omega
  have hpx : walkRadius px ≤ B := by dsimp [B]; omega
  have hpy : walkRadius py ≤ B := by dsimp [B]; omega
  have hpr (r : Cell) : walkRadius (pr r) ≤ B := by
    have hh : walkRadius (pr r) ≤ S := Finset.single_le_sum
      (fun _ _ => walkRadius_nonneg _) (Finset.mem_univ r)
    dsimp [B]
    omega
  refine ⟨B+(N.factorial : ℤ)*(R+B),by positivity,z+shift N (R+B+1) (R+B+1),?_⟩
  intro v hv hvfar
  let r : Cell := ⟨residue N v,reachable_representative hz hv⟩
  let w := representative N r.val
  have hd : IsPeriod N (v-w) :=
    period_of_same_residue (residue_representative N (residue N v))
  obtain ⟨k,hk⟩ := hd.1
  obtain ⟨l,hl⟩ := hd.2
  have he : v = w+shift N k l := by
    apply Zsqrtd.ext <;> dsimp [shift] <;> simp only [Zsqrtd.re_sub,Zsqrtd.im_sub] at hk hl <;> omega
  have hw : |w.re| ≤ B ∧ |w.im| ≤ B :=
    ⟨(coordinates_le_walkRadius (pr r) (pr r).end_mem_support).1.trans (hpr r),
      (coordinates_le_walkRadius (pr r) (pr r).end_mem_support).2.trans (hpr r)⟩
  have hlarge := far_indices N R B hw he hvfar
  have hp := translate_walk_avoiding H R B hR hB hH (pr r) (hpr r) k l hlarge
  have hgrid := coarse_grid_detour H R B hR hB hH px py hpx hpy k l hlarge
  rw [he]
  exact hgrid.symm.trans hp

lemma outside_compl_finite (F : ℤ) (hF : 0 ≤ F) : {v : GaussianInt | ¬ Outside F v}.Finite := by
  apply (norm_sublevel_finite (2*F^2)).subset
  intro v hv
  have hh : |v.re| ≤ F ∧ |v.im| ≤ F := by simpa only [Outside,not_or,not_lt] using hv
  have hr : v.re^2 ≤ F^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hF] using hh.1)
  have hi : v.im^2 ≤ F^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hF] using hh.2)
  change v.norm ≤ 2*F^2
  rw [gaussian_norm_sq]
  linarith

/-- Deleting a finite region cannot destroy the infinite sieve component. -/
theorem infinite_component_survives_finite_change {C : ℤ} {N : ℕ} {z : GaussianInt}
    (hz : {w | (sieveGraph C N).Reachable z w}.Infinite)
    (H : SimpleGraph GaussianInt) (R : ℤ) (hR : 0 ≤ R)
    (hH : ∀ {a b}, (sieveGraph C N).Adj a b → Outside R a → Outside R b → H.Adj a b) :
    ∃ a : GaussianInt, {v | H.Reachable a v}.Infinite := by
  obtain ⟨F,hF,a,ha⟩ := far_component_detours hz H R hR hH
  refine ⟨a,(hz.diff (outside_compl_finite F hF)).mono ?_⟩
  intro v hv
  exact ha v hv.1 (by simpa using hv.2)

#print axioms far_component_detours
#print axioms infinite_component_survives_finite_change
end Erdos952Investigation.PeriodicSieveEnds
