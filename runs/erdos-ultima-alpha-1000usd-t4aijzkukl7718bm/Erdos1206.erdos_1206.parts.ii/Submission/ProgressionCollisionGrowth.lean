import Submission.ProgressionCollisionMass
import Submission.DensityOneCollisionGrowth

/-!
Every residue-class tail has superlinear cubic collision counts. This rules out
periodic sources for the linear-collision extraction criterion, but does not
bound independence densities or settle the original conjecture.
-/
namespace Erdos1206.ProgressionCollisionGrowth
open Finset Filter CubeCollisionGrowth ProgressionCollisionMass
open PrimitiveCollisionMass (Collision)
open scoped Classical Topology

lemma exists_multiplier (Q r a : ℕ) (hQ : 0 < Q) (ha : Nat.Coprime a Q) :
    ∃ s : ℕ, 0 < s ∧ s ≤ Q ∧ Nat.ModEq Q (s*a) r := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  let z : ZMod Q := (r : ZMod Q)*(a : ZMod Q)⁻¹
  have hza : z*(a : ZMod Q)=r := by
    dsimp [z]
    rw [mul_assoc,ZMod.inv_mul_of_unit _ ((ZMod.isUnit_iff_coprime a Q).mpr ha),mul_one]
  let s : ℕ := if z.val=0 then Q else z.val
  have hscast : (s : ZMod Q)=z := by
    by_cases hz : z.val=0
    · have hz' : z=0 := by
        have hh := ZMod.natCast_zmod_val z
        rw [hz,Nat.cast_zero] at hh
        exact hh.symm
      simp [s,hz']
    · simpa only [s,if_neg hz] using ZMod.natCast_zmod_val z
  refine ⟨s,?_,?_,?_⟩
  · dsimp [s]
    split_ifs with hz
    · exact hQ
    · omega
  · dsimp [s]
    split_ifs
    · rfl
    · exact (ZMod.val_lt z).le
  · apply (ZMod.natCast_eq_natCast_iff (s*a) r Q).mp
    simpa only [Nat.cast_mul,hscast] using hza

noncomputable def multiplier {Q : ℕ} (hQ : 0 < Q) (r : ℕ) (e : Family Q) : ℕ :=
  (exists_multiplier Q r e.val.val.1 hQ e.property.1).choose

lemma multiplier_spec {Q : ℕ} (hQ : 0 < Q) (r : ℕ) (e : Family Q) :
    0 < multiplier hQ r e ∧ multiplier hQ r e ≤ Q ∧
      Nat.ModEq Q (multiplier hQ r e*e.val.val.1) r :=
  (exists_multiplier Q r e.val.val.1 hQ e.property.1).choose_spec

def residueTail (Q r L : ℕ) : Set ℕ := {n | L ≤ n ∧ Nat.ModEq Q n r}

/-- One admissible multiplier in every block of Q, after an optional initial
cutoff, embeds disjoint dilations of the chosen primitive patterns. -/
lemma finite_dilate_count (Q r L : ℕ) (hQ : 0 < Q) (F : Finset (Family Q)) (N : ℕ) :
    ∑ e ∈ F, (N/(Q*e.val.val.2.2.2)-L) ≤
      (sourceCollisionsUpTo (residueTail Q r L) N).card := by
  let T := F.sigma (fun e => range (N/(Q*e.val.val.2.2.2)-L))
  let q : Family Q → ℕ → ℕ := fun e t => multiplier hQ r e+Q*(t+L)
  let f : ((e : Family Q) × ℕ) → Quad := fun z => dilate (q z.1 z.2) z.1.val.val
  have hqpos (e : Family Q) (t : ℕ) : 0 < q e t := by
    have := (multiplier_spec hQ r e).1
    dsimp [q]
    omega
  have hf : Set.InjOn f (T : Set ((e : Family Q) × ℕ)) := by
    intro x hx y hy he
    obtain ⟨hee,hqq⟩ := primitive_dilate_injective (hqpos x.1 x.2) he
    have hee' : x.1=y.1 := Subtype.ext hee
    have htt : x.2=y.2 := by
      dsimp [q] at hqq
      rw [hee'] at hqq
      have hh := Nat.eq_of_mul_eq_mul_left hQ (Nat.add_left_cancel hqq)
      omega
    cases x with
    | mk e t =>
      cases y with
      | mk e' t' =>
        dsimp only at hee' htt
        subst e' t'
        rfl
  have hsub : T.image f ⊆ sourceCollisionsUpTo (residueTail Q r L) N := by
    intro x hx
    obtain ⟨⟨e,t⟩,hz,rfl⟩ := mem_image.mp hx
    have ht := mem_range.mp (mem_sigma.mp hz).2
    change t < N/(Q*e.val.val.2.2.2)-L at ht
    have hqsmall : q e t ≤ Q*(t+L+1) := by
      have := (multiplier_spec hQ r e).2.1
      dsimp [q]
      nlinarith
    have hN : q e t*e.val.val.2.2.2 ≤ N := by
      calc
        _ ≤ (Q*(t+L+1))*e.val.val.2.2.2 := Nat.mul_le_mul_right _ hqsmall
        _ = (t+L+1)*(Q*e.val.val.2.2.2) := by ring
        _ ≤ (N/(Q*e.val.val.2.2.2))*(Q*e.val.val.2.2.2) :=
          Nat.mul_le_mul_right _ (by omega)
        _ ≤ N := Nat.div_mul_le_self N _
    have hLq : L ≤ q e t := by
      have hQ1 : 1 ≤ Q := hQ
      have hh := Nat.mul_le_mul_right (t+L) hQ1
      dsimp [q]
      omega
    have hqm : Nat.ModEq Q (q e t) (multiplier hQ r e) := by
      simp [q,Nat.ModEq,Nat.add_mod]
    have ha := (hqm.mul_right e.val.val.1).trans (multiplier_spec hQ r e).2.2
    have hb : Nat.ModEq Q (q e t*e.val.val.2.1) r :=
      (e.property.2.1.mul_left (q e t)).symm.trans ha
    have hc : Nat.ModEq Q (q e t*e.val.val.2.2.1) r :=
      (e.property.2.2.1.mul_left (q e t)).symm.trans ha
    have hd : Nat.ModEq Q (q e t*e.val.val.2.2.2) r :=
      (e.property.2.2.2.mul_left (q e t)).symm.trans ha
    have he := e.val.property
    have hbound (v : ℕ) (hv : 0 < v) : L ≤ q e t*v :=
      hLq.trans (Nat.le_mul_of_pos_right _ hv)
    apply mem_filter.mpr
    refine ⟨dilate_mem_collisionsUpTo e.val (hqpos e t) hN,?_⟩
    exact ⟨⟨hbound _ he.1,ha⟩,⟨hbound _ (he.1.trans he.2.1),hb⟩,
      ⟨hbound _ (he.1.trans (he.2.1.trans he.2.2.1)),hc⟩,
      ⟨hbound _ (primitive_height_pos e.val),hd⟩⟩
  have hh := card_le_card hsub
  rw [card_image_of_injOn hf] at hh
  simpa [T,card_sigma] using hh

lemma finite_reciprocal_count_bound (Q r L : ℕ) (hQ : 0 < Q)
    (F : Finset (Family Q)) (N : ℕ) :
    (N : ℝ)*(∑ e ∈ F, (1 : ℝ)/e.val.val.2.2.2) ≤
      Q*(sourceCollisionsUpTo (residueTail Q r L) N).card + Q*F.card*(L+1) := by
  have hterm (e : Family Q) :
      (N : ℝ)/e.val.val.2.2.2 ≤ Q*((N/(Q*e.val.val.2.2.2)-L : ℕ) : ℝ)+Q*(L+1) := by
    have hd : (0 : ℝ) < e.val.val.2.2.2 := by exact_mod_cast primitive_height_pos e.val
    have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hn := Nat.lt_mul_div_succ N (Nat.mul_pos hQ (primitive_height_pos e.val))
    have hn' : (N : ℝ) < (Q*e.val.val.2.2.2)*(((N/(Q*e.val.val.2.2.2) : ℕ) : ℝ)+1) := by
      exact_mod_cast hn
    have hsub : ((N/(Q*e.val.val.2.2.2) : ℕ) : ℝ) ≤
        ((N/(Q*e.val.val.2.2.2)-L : ℕ) : ℝ)+L := by
      exact_mod_cast (show N/(Q*e.val.val.2.2.2) ≤ (N/(Q*e.val.val.2.2.2)-L)+L by omega)
    apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hsub (mul_pos hq hd).le
    nlinarith
  have hs := sum_le_sum (fun e (_ : e ∈ F) => hterm e)
  have hc : (∑ e ∈ F, ((N/(Q*e.val.val.2.2.2)-L : ℕ) : ℝ)) ≤
      (sourceCollisionsUpTo (residueTail Q r L) N).card := by
    exact_mod_cast finite_dilate_count Q r L hQ F N
  have hc' := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ Q by positivity)
  have heq : (∑ e ∈ F, (N : ℝ)/e.val.val.2.2.2) =
      (N : ℝ)*(∑ e ∈ F, (1 : ℝ)/e.val.val.2.2.2) := by simp [mul_sum,div_eq_mul_inv]
  rw [heq] at hs
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] at hs
  nlinarith

/-- Every residue-class tail, including non-unit classes, has superlinear
collision counts at all sufficiently large cutoffs. -/
theorem residueTail_superlinear (Q r L : ℕ) (hQ : 0 < Q) (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M,
      C*N < ((sourceCollisionsUpTo (residueTail Q r L) N).card : ℝ) := by
  obtain ⟨F,hF⟩ := exists_large_reciprocal_sum Q hQ (Q*(C+1))
  refine ⟨F.card*(L+1)+1,fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hFN : (F.card : ℝ)*(L+1) ≤ N := by
    exact_mod_cast (show F.card*(L+1) ≤ N by omega)
  have hh := mul_lt_mul_of_pos_left hF hN0
  have hb := finite_reciprocal_count_bound Q r L hQ F N
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlarge : (Q : ℝ)*(C*N) < Q*(sourceCollisionsUpTo (residueTail Q r L) N).card := by
    nlinarith [mul_le_mul_of_nonneg_left hFN hq.le]
  exact (mul_lt_mul_iff_right₀ hq).mp hlarge

lemma source_count_mono {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    (sourceCollisionsUpTo S N).card ≤ (sourceCollisionsUpTo T N).card := by
  apply card_le_card
  intro x hx
  obtain ⟨hx,h₀,h₁,h₂,h₃⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hx,hST h₀,hST h₁,hST h₂,hST h₃⟩

/-- No source containing a residue-class tail meets the uniform linear
hypergraph-count hypothesis. -/
theorem not_linear_source_of_residueTail {S : Set ℕ} {Q r L : ℕ}
    (hQ : 0 < Q) (hS : residueTail Q r L ⊆ S) :
    ¬ ∃ C : ℕ, ∀ N, (CubicHypergraph.edges N S).card ≤ C*N := by
  rintro ⟨C,hC⟩
  obtain ⟨M,hM⟩ := residueTail_superlinear Q r L hQ (2*C)
  let N := M+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hg := hM N (by dsimp [N]; omega)
  have hb : ((sourceCollisionsUpTo (residueTail Q r L) N).card : ℝ) ≤ C*(N+1) := by
    exact_mod_cast ((source_count_mono hS N).trans
      (DensityOneCollisionGrowth.source_count_le_hypergraph S N)).trans (hC (N+1))
  have hNN : (N : ℝ)+1 ≤ 2*N := by exact_mod_cast (show N+1 ≤ 2*N by omega)
  nlinarith [mul_le_mul_of_nonneg_left hNN (show (0 : ℝ) ≤ C by positivity)]

#print axioms exists_multiplier
#print axioms finite_reciprocal_count_bound
#print axioms residueTail_superlinear
#print axioms not_linear_source_of_residueTail
end Erdos1206.ProgressionCollisionGrowth
