import Submission.SignedInverseRectangles
import Submission.MonotoneRegionRectangles

/-! Uniform comparison of the positive and negative modular-inverse curves
inside antitone subgraphs. This retains the prime-field normalization. -/
namespace Erdos371.Kloosterman
open Finset Filter
open scoped Topology

section Prime
variable (p : ℕ) [Fact p.Prime]

noncomputable def orientedInverse (s : Bool) (x : (ZMod p)ˣ) : ZMod p :=
  if s then -(x : ZMod p)⁻¹ else (x : ZMod p)⁻¹

noncomputable def orientedRegionCount (s : Bool) (h : ℕ → ℕ) : ℕ :=
  MonotoneRectangles.regionCount (fun x : (ZMod p)ˣ => (x : ZMod p).val)
    (fun x => (orientedInverse p s x).val) h

lemma oriented_rectCount_eq (s : Bool) (L M : ℕ) :
    MonotoneRectangles.rectCount (fun x : (ZMod p)ˣ => (x : ZMod p).val)
      (fun x => (orientedInverse p s x).val) L M=signedRectangleCount p s L M := by
  rw [signedRectangleCount_eq_filter]
  rfl

/-- Explicit two-parameter bound: H,K describe the staircase; T describes
Fourier smoothing. The cutoff h may depend arbitrarily on p. -/
theorem oriented_region_difference_bound (h : ℕ → ℕ) (hh : Antitone h) (hzero : h 0≤p)
    (H K T : ℕ) (hH : 0<H) (hcover : p≤K*H) (hT : 2≤T) :
    |(orientedRegionCount p true h : ℝ)/p-(orientedRegionCount p false h : ℝ)/p|≤
      (H : ℝ)/p+4*K*(4/(T : ℝ)+5/(p : ℝ)+Real.sqrt (Real.sqrt (3/(p : ℝ)))*(T : ℝ)) := by
  apply MonotoneRectangles.monotone_region_comparison
    (fun x : (ZMod p)ˣ => (x : ZMod p).val)
    (fun x => (orientedInverse p true x).val)
    (fun x : (ZMod p)ˣ => (x : ZMod p).val)
    (fun x => (orientedInverse p false x).val) h hh p H K
    (Fact.out : p.Prime).pos hH hcover
    (fun x => ZMod.val_lt _) (fun x => ZMod.val_lt _) hzero
  · intro U V hU hV
    rw [oriented_rectCount_eq]
    exact signed_rectangle_ratio_uniform p true U V T hU hV hT
  · intro U V hU hV
    rw [oriented_rectCount_eq]
    exact signed_rectangle_ratio_uniform p false U V T hU hV hT
end Prime

lemma integer_grid_width_ratio (p K : ℕ) (hp : 0<p) (hK : 0<K) :
    ((p/K+1 : ℕ) : ℝ)/p≤1/(K : ℝ)+1/(p : ℝ) := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp
  have hf : ((p/K+1 : ℕ) : ℝ)≤(p : ℝ)/K+1 := by
    push_cast
    exact add_le_add (Nat.cast_div_le (α := ℝ) (m := p) (n := K)) le_rfl
  have h := div_le_div_of_nonneg_right hf hp0.le
  convert h using 1
  field_simp

/-- Uniform o(p) signed cancellation in every moving antitone subgraph. -/
theorem oriented_region_difference_tendsto (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hp : Tendsto p atTop atTop) (h : ℕ → ℕ → ℕ)
    (hh : ∀ n, Antitone (h n)) (hzero : ∀ n, h n 0≤p n) :
    Tendsto (fun n => |(orientedRegionCount (p n) true (h n) : ℝ)/(p n)-
      (orientedRegionCount (p n) false (h n) : ℝ)/(p n)|) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun n => hε.trans_le (abs_nonneg _)
  · intro ε hε
    obtain ⟨K,hK⟩ := exists_nat_gt (max (2 : ℝ) (4/ε))
    have hK2 : 2≤K := by exact_mod_cast (le_max_left _ _).trans hK.le
    have hK0 : (0 : ℝ)<K := by exact_mod_cast (show 0<K by omega)
    have hKe : 1/(K : ℝ)<ε/4 := by
      have hk := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hK)
      apply (div_lt_iff₀ hK0).mpr
      nlinarith
    obtain ⟨T,hT⟩ := exists_nat_gt (max (2 : ℝ) (64*(K : ℝ)/ε))
    have hT2 : 2≤T := by exact_mod_cast (le_max_left _ _).trans hT.le
    have hT0 : (0 : ℝ)<T := by exact_mod_cast (show 0<T by omega)
    have hTe : 16*(K : ℝ)/T<ε/4 := by
      have ht := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hT)
      apply (div_lt_iff₀ hT0).mpr
      nlinarith
    let A : ℝ := 1/(K : ℝ)+16*(K : ℝ)/T
    have hA : A<ε := by dsimp [A]; linarith
    have hroot := ((((tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp hp).sqrt).sqrt).mul_const (T : ℝ)
    have ht := ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hp).add
      ((((tendsto_const_div_atTop_nhds_zero_nat (5 : ℝ)).comp hp).add hroot).const_mul (4*(K : ℝ)))
    simp only [Real.sqrt_zero,zero_mul,add_zero,mul_zero] at ht
    filter_upwards [ht.eventually_lt_const (show 0<ε-A by linarith)] with n hn
    dsimp only [Function.comp_apply] at hn
    let H : ℕ := p n/K+1
    have hH : 0<H := Nat.succ_pos _
    have hcover : p n≤K*H := by
      have hm := Nat.mod_lt (p n) (show 0<K by omega)
      have he := Nat.div_add_mod (p n) K
      dsimp [H]
      nlinarith
    have hb := oriented_region_difference_bound (p n) (h n) (hh n) (hzero n) H K T hH hcover hT2
    have hw := integer_grid_width_ratio (p n) K (Fact.out : (p n).Prime).pos (by omega)
    change (H : ℝ)/(p n)≤_ at hw
    calc
      _ ≤ A+(1/(p n : ℝ)+4*(K : ℝ)*(5/(p n : ℝ)+Real.sqrt (Real.sqrt (3/(p n : ℝ)))*(T : ℝ))) := by
        apply (hb.trans (add_le_add hw le_rfl)).trans_eq
        dsimp [A]
        ring
      _ < ε := by linarith

/-- An integer hyperbola is an antitone subgraph on the positive coordinates.
At y=0 the cutoff is defined to be p so that antitonicity remains global. -/
def hyperbolaCutoff (p N y : ℕ) : ℕ := if y=0 then p else min p ((N-1)/y+1)

lemma hyperbolaCutoff_antitone (p N : ℕ) : Antitone (hyperbolaCutoff p N) := by
  intro a b hab
  by_cases ha : a=0
  · subst a
    simp only [hyperbolaCutoff,if_true]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hb : b≠0 := by omega
  simp only [hyperbolaCutoff,if_neg ha,if_neg hb]
  apply min_le_min_left
  exact Nat.add_le_add_right (Nat.div_le_div_left hab (by omega)) 1

lemma below_hyperbolaCutoff_iff (p N a b : ℕ) (ha : 0<a) (hap : a<p) (hb : 0<b) :
    a<hyperbolaCutoff p N b ↔ a*b<N := by
  rw [hyperbolaCutoff,if_neg (by omega : b≠0),lt_min_iff,and_iff_right hap]
  by_cases hN : N=0
  · subst N
    simp only [Nat.zero_sub,Nat.zero_div,zero_add]
    have hm : 0<a*b := Nat.mul_pos ha hb
    omega
  · have he := Nat.le_div_iff_mul_le hb (x := a) (y := N-1)
    omega

section Hyperbola
variable (p : ℕ) [Fact p.Prime]

lemma orientedInverse_ne_zero (s : Bool) (x : (ZMod p)ˣ) : orientedInverse p s x≠0 := by
  cases s
  · exact inv_ne_zero (Units.ne_zero x)
  · exact neg_ne_zero.mpr (inv_ne_zero (Units.ne_zero x))

noncomputable def inverseHyperbolaCount (s : Bool) (N : ℕ) : ℕ :=
  (univ.filter fun x : (ZMod p)ˣ =>
    (x : ZMod p).val*(orientedInverse p s x).val<N).card

lemma inverseHyperbolaCount_eq_region (s : Bool) (N : ℕ) :
    inverseHyperbolaCount p s N=orientedRegionCount p s (hyperbolaCutoff p N) := by
  unfold inverseHyperbolaCount orientedRegionCount MonotoneRectangles.regionCount
  congr 1
  ext x
  have hx : 0<(x : ZMod p).val := by
    have hn := (ZMod.val_eq_zero (x : ZMod p)).not.mpr (Units.ne_zero x)
    omega
  have hy : 0<(orientedInverse p s x).val := by
    have hn := (ZMod.val_eq_zero (orientedInverse p s x)).not.mpr (orientedInverse_ne_zero p s x)
    omega
  simp only [mem_filter,mem_univ,true_and,below_hyperbolaCutoff_iff p N _ _ hx (ZMod.val_lt _) hy]
end Hyperbola

/-- Signed modular-inverse hyperbola counts cancel uniformly in the moving
integer cutoff N. This counts marked factor pairs, not unweighted indices. -/
theorem inverse_hyperbola_difference_tendsto (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hp : Tendsto p atTop atTop) (N : ℕ → ℕ) :
    Tendsto (fun n => |(inverseHyperbolaCount (p n) true (N n) : ℝ)/(p n)-
      (inverseHyperbolaCount (p n) false (N n) : ℝ)/(p n)|) atTop (nhds 0) := by
  simp_rw [inverseHyperbolaCount_eq_region]
  exact oriented_region_difference_tendsto p hp (fun n => hyperbolaCutoff (p n) (N n))
    (fun n => hyperbolaCutoff_antitone _ _) (fun n => by simp [hyperbolaCutoff])

#print axioms oriented_region_difference_bound
#print axioms oriented_region_difference_tendsto
#print axioms inverse_hyperbola_difference_tendsto
end Erdos371.Kloosterman
