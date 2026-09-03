import Submission.TripleConicFamily
import Submission.OddCycleColoring

/-! Full-prefix superlinear counts of six-root three-pair cube-difference
configurations. Each gives a three-edge odd cycle. This rules out a linear
count bound on these configurations, but does not rule out a reusable divisor
cover, a proper coloring, or a positive-density cube-Sidon set. -/

namespace Erdos1206.TripleConicGrowth
open Finset Filter TripleConicFamily
open scoped Classical
set_option maxHeartbeats 1000000

/-- The pairs (0,1), (2,4), (3,5) have the same positive cube difference. -/
def IsTriple (x : Fin 6 → ℕ) : Prop :=
  StrictMono x ∧ 0 < x 0 ∧
    x 0 ^ 3 + x 4 ^ 3 = x 1 ^ 3 + x 2 ^ 3 ∧
    x 0 ^ 3 + x 5 ^ 3 = x 1 ^ 3 + x 3 ^ 3 ∧
    x 2 ^ 3 + x 5 ^ 3 = x 3 ^ 3 + x 4 ^ 3

lemma isTriple_point (x : Index) : IsTriple (point x) :=
  ⟨roots_strictMono (u_pos x) (V x), roots_pos (u_pos x) (V x) 0,
    identities (U x) (V x)⟩

lemma IsTriple.dilate {x : Fin 6 → ℕ} (hx : IsTriple x) {q : ℕ} (hq : 0 < q) :
    IsTriple (fun i => q*x i) := by
  refine ⟨fun i j hij => Nat.mul_lt_mul_of_pos_left (hx.1 hij) hq,
    Nat.mul_pos hq hx.2.1, ?_, ?_, ?_⟩
  · simpa only [mul_pow, ← mul_add] using congrArg (fun n : ℕ => q^3*n) hx.2.2.1
  · simpa only [mul_pow, ← mul_add] using congrArg (fun n : ℕ => q^3*n) hx.2.2.2.1
  · simpa only [mul_pow, ← mul_add] using congrArg (fun n : ℕ => q^3*n) hx.2.2.2.2

/-- These six roots support an odd even-incidence collection of three cubic
edges. This is an obstruction to odd-parity coloring, not proper coloring. -/
theorem IsTriple.not_noOddCycle {x : Fin 6 → ℕ} (hx : IsTriple x) :
    ¬ OddCycleColoring.NoOddCycle
      (fun e : OddCycleColoring.CubicEdges (Set.range x) => (e : Finset ℕ)) := by
  intro h
  obtain ⟨c,hc⟩ := OddCycleColoring.exists_odd_coloring _ h
  have hm (i : Fin 6) : x i ∈ Set.range x := Set.mem_range_self _
  have h₂ : 0 < x 2 := hx.2.1.trans (hx.1 (by decide : (0 : Fin 6) < 2))
  have he₁ : {x 0,x 1,x 2,x 4} ∈ OddCycleColoring.CubicEdges (Set.range x) :=
    ⟨x 0,hm 0,x 1,hm 1,x 2,hm 2,x 4,hm 4,hx.2.1,
      hx.1 (by decide),hx.1 (by decide),hx.1 (by decide),hx.2.2.1,rfl⟩
  have he₂ : {x 0,x 1,x 3,x 5} ∈ OddCycleColoring.CubicEdges (Set.range x) :=
    ⟨x 0,hm 0,x 1,hm 1,x 3,hm 3,x 5,hm 5,hx.2.1,
      hx.1 (by decide),hx.1 (by decide),hx.1 (by decide),hx.2.2.2.1,rfl⟩
  have he₃ : {x 2,x 3,x 4,x 5} ∈ OddCycleColoring.CubicEdges (Set.range x) :=
    ⟨x 2,hm 2,x 3,hm 3,x 4,hm 4,x 5,hm 5,h₂,
      hx.1 (by decide),hx.1 (by decide),hx.1 (by decide),hx.2.2.2.2,rfl⟩
  have h₁ : c (x 0) + (c (x 1) + (c (x 2) + c (x 4))) = 1 := by
    simpa [hx.1.injective.eq_iff] using hc ⟨_,he₁⟩
  have h₂ : c (x 0) + (c (x 1) + (c (x 3) + c (x 5))) = 1 := by
    simpa [hx.1.injective.eq_iff] using hc ⟨_,he₂⟩
  have h₃ : c (x 2) + (c (x 3) + (c (x 4) + c (x 5))) = 1 := by
    simpa [hx.1.injective.eq_iff] using hc ⟨_,he₃⟩
  have hz (z : ZMod 2) : z+z=0 := by
    simpa [ZMod.neg_eq_self_mod_two] using neg_add_cancel z
  have hzero : c (x 0) + (c (x 1) + (c (x 2) + c (x 4))) +
      (c (x 0) + (c (x 1) + (c (x 3) + c (x 5)))) +
      (c (x 2) + (c (x 3) + (c (x 4) + c (x 5)))) = 0 := by
    calc
      _ = (c (x 0)+c (x 0)) + (c (x 1)+c (x 1)) +
        (c (x 2)+c (x 2)) + (c (x 3)+c (x 3)) +
        (c (x 4)+c (x 4)) + (c (x 5)+c (x 5)) := by ring
      _ = 0 := by simp only [hz]
  rw [h₁,h₂,h₃] at hzero
  norm_num at hzero
  exact (by decide : (3 : ZMod 2) ≠ 0) hzero

noncomputable def triplesUpTo (N : ℕ) : Finset (Fin 6 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 6 => range (N+1))).filter IsTriple

lemma dilate_mem_triplesUpTo (x : Index) {q N : ℕ}
    (hq : 0 < q) (hN : q*height x ≤ N) :
    (fun i => q*point x i) ∈ triplesUpTo N := by
  apply mem_filter.mpr
  refine ⟨?_,(isTriple_point x).dilate hq⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply mem_range.mpr
  have hb := Nat.mul_le_mul_left q (roots_le_height (u_pos x) (V x) i)
  exact Nat.lt_succ_of_le (hb.trans hN)

lemma finite_dilate_count (T : Finset Index) (N : ℕ) :
    ∑ x ∈ T, N/height x ≤ (triplesUpTo N).card := by
  let S := T.sigma (fun x => Icc 1 (N/height x))
  let f : ((x : Index) × ℕ) → (Fin 6 → ℕ) := fun z i => z.2*point z.1 i
  have hf : Set.InjOn f (S : Set ((x : Index) × ℕ)) := by
    intro x hx y hy hxy
    have hq : 0 < x.2 := (mem_Icc.mp (mem_sigma.mp hx).2).1
    obtain ⟨he,hr⟩ := point_dilate_injective hq hxy
    cases x with | mk e q =>
      cases y with | mk e' q' =>
        dsimp only at he hr
        subst e' q'
        rfl
  have hsub : S.image f ⊆ triplesUpTo N := by
    intro x hx
    obtain ⟨⟨e,q⟩,hz,rfl⟩ := mem_image.mp hx
    have hq := mem_Icc.mp (mem_sigma.mp hz).2
    apply dilate_mem_triplesUpTo e hq.1
    exact (Nat.mul_le_mul_right _ hq.2).trans (Nat.div_mul_le_self N _)
  have hh := card_le_card hsub
  rw [card_image_of_injOn hf] at hh
  simpa [S,card_sigma] using hh

lemma finite_reciprocal_bound (T : Finset Index) (N : ℕ) :
    (N : ℝ)*(∑ x ∈ T, (1 : ℝ)/height x) ≤
      ((triplesUpTo N).card : ℝ)+T.card := by
  have hterm (x : Index) :
      (N : ℝ)/height x ≤ ((N/height x : ℕ) : ℝ)+1 := by
    have hx : (0 : ℝ) < height x := by exact_mod_cast height_pos x
    apply (div_le_iff₀ hx).mpr
    have hh := Nat.lt_mul_div_succ N (height_pos x)
    have hh' : (N : ℝ) < height x*(((N/height x : ℕ) : ℝ)+1) := by exact_mod_cast hh
    nlinarith
  have hc : (∑ x ∈ T, ((N/height x : ℕ) : ℝ)) ≤
      ((triplesUpTo N).card : ℝ) := by exact_mod_cast finite_dilate_count T N
  calc
    _ = ∑ x ∈ T, (N : ℝ)/height x := by simp [mul_sum,div_eq_mul_inv]
    _ ≤ ∑ x ∈ T, (((N/height x : ℕ) : ℝ)+1) := sum_le_sum fun x _ => hterm x
    _ = (∑ x ∈ T, ((N/height x : ℕ) : ℝ))+T.card := by simp [sum_add_distrib]
    _ ≤ _ := by linarith

/-- Even these six-root three-pair configurations have superlinear counts at
all sufficiently large cutoffs. This is not an independence bound. -/
theorem triple_count_superlinear (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M, C*N < ((triplesUpTo N).card : ℝ) := by
  have hT : ∃ T : Finset Index, C+1 < ∑ x ∈ T, (1 : ℝ)/height x := by
    by_contra! h
    exact reciprocal_heights_not_summable (summable_of_sum_le (fun _ => by positivity) h)
  obtain ⟨T,hT⟩ := hT
  refine ⟨T.card+1,fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hTN : (T.card : ℝ) ≤ N := by exact_mod_cast (show T.card ≤ N by omega)
  have hm := mul_lt_mul_of_pos_left hT hNpos
  have hb := finite_reciprocal_bound T N
  nlinarith

#print axioms IsTriple.not_noOddCycle
#print axioms triple_count_superlinear
end Erdos1206.TripleConicGrowth
