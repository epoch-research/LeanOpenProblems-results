import Submission.ProgressionCollisionGrowth

/-!
Superlinear collision counts persist after deleting a density-zero set from
any residue class. This is an obstruction to periodic or almost-periodic
linear-count sources, not to arbitrary positive-density Sidon sets.
-/
namespace Erdos1206.ProgressionCollisionDeletion
open Finset Filter CubeCollisionGrowth ProgressionCollisionMass ProgressionCollisionGrowth
open DensityOneCollisionGrowth
open scoped Classical Topology

noncomputable def admissible {Q : ℕ} (r : ℕ) (e : Family Q) (N : ℕ) : Finset ℕ :=
  (Icc 1 (N/e.val.val.2.2.2)).filter (fun q => Nat.ModEq Q (q*e.val.val.1) r)

lemma admissible_lower_bound {Q : ℕ} (hQ : 0 < Q) (r : ℕ) (e : Family Q) (N : ℕ) :
    N/(Q*e.val.val.2.2.2) ≤ (admissible r e N).card := by
  let s := multiplier hQ r e
  let f : ℕ → ℕ := fun t => s+Q*t
  have hf : Function.Injective f := by
    intro t u he
    exact Nat.eq_of_mul_eq_mul_left hQ (Nat.add_left_cancel he)
  have hsub : (range (N/(Q*e.val.val.2.2.2))).image f ⊆ admissible r e N := by
    intro q hq
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hq
    have hspec := multiplier_spec hQ r e
    have hpos : 0 < f t := by dsimp [f,s]; omega
    have hbound : f t*e.val.val.2.2.2 ≤ N := by
      have hq : f t ≤ Q*(t+1) := by dsimp [f,s]; nlinarith [hspec.2.1]
      calc
        _ ≤ Q*(t+1)*e.val.val.2.2.2 := Nat.mul_le_mul_right _ hq
        _ = (t+1)*(Q*e.val.val.2.2.2) := by ring
        _ ≤ (N/(Q*e.val.val.2.2.2))*(Q*e.val.val.2.2.2) :=
          Nat.mul_le_mul_right _ (by have := mem_range.mp ht; omega)
        _ ≤ N := Nat.div_mul_le_self N _
    have hmod : Nat.ModEq Q (f t) s := by simp [f,Nat.ModEq,Nat.add_mod]
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hpos,?_⟩,(hmod.mul_right _).trans hspec.2.2⟩
    exact (Nat.le_div_iff_mul_le (primitive_height_pos e.val)).mpr hbound
  have hh := card_le_card hsub
  simpa [card_image_of_injective _ hf] using hh

lemma admissible_roots {Q r N q : ℕ} {e : Family Q} (hq : q ∈ admissible r e N) :
    q*e.val.val.1 ∈ residueTail Q r 0 ∧ q*e.val.val.2.1 ∈ residueTail Q r 0 ∧
    q*e.val.val.2.2.1 ∈ residueTail Q r 0 ∧ q*e.val.val.2.2.2 ∈ residueTail Q r 0 := by
  have ha := (mem_filter.mp hq).2
  exact ⟨⟨Nat.zero_le _,ha⟩,
    ⟨Nat.zero_le _,(e.property.2.1.mul_left q).symm.trans ha⟩,
    ⟨Nat.zero_le _,(e.property.2.2.1.mul_left q).symm.trans ha⟩,
    ⟨Nat.zero_le _,(e.property.2.2.2.mul_left q).symm.trans ha⟩⟩

/-- Fill outside the residue class, so only omissions within it are charged. -/
def filled (Q r : ℕ) (S : Set ℕ) : Set ℕ := S ∪ (residueTail Q r 0)ᶜ

noncomputable def good {Q : ℕ} (r : ℕ) (S : Set ℕ) (e : Family Q) (N : ℕ) : Finset ℕ :=
  admissible r e N ∩ goodMultipliers (filled Q r S) e.val N

lemma good_lower_bound {Q : ℕ} (hQ : 0 < Q) (r : ℕ) (S : Set ℕ)
    (e : Family Q) (N : ℕ) :
    N/(Q*e.val.val.2.2.2) ≤ (good r S e N).card+4*(missing (filled Q r S) N).card := by
  let U := Icc 1 (N/e.val.val.2.2.2)
  let G := goodMultipliers (filled Q r S) e.val N
  have hG : G ⊆ U := filter_subset _ _
  have hA : admissible r e N ⊆ U := filter_subset _ _
  have hdiff : (admissible r e N \ G).card ≤ (U \ G).card :=
    card_le_card (sdiff_subset_sdiff hA (Subset.refl _))
  have heG := card_sdiff_add_card_eq_card hG
  have heA := card_inter_add_card_sdiff (admissible r e N) G
  have hfull := goodMultipliers_card (filled Q r S) e.val N
  have hU : U.card=N/e.val.val.2.2.2 := by simp [U]
  have hadm := admissible_lower_bound hQ r e N
  change N/(Q*e.val.val.2.2.2) ≤ (admissible r e N ∩ G).card+
    4*(missing (filled Q r S) N).card
  change N/e.val.val.2.2.2 ≤ G.card+4*(missing (filled Q r S) N).card at hfull
  omega

lemma finite_good_count {Q : ℕ} (r : ℕ) (S : Set ℕ) (F : Finset (Family Q)) (N : ℕ) :
    ∑ e ∈ F, (good r S e N).card ≤ (sourceCollisionsUpTo S N).card := by
  let T := F.sigma (fun e => good r S e N)
  let f : ((e : Family Q) × ℕ) → Quad := fun z => dilate z.2 z.1.val.val
  have hf : Set.InjOn f (T : Set ((e : Family Q) × ℕ)) := by
    intro x hx y hy he
    have hqx : 0 < x.2 := (mem_Icc.mp (mem_filter.mp
      (mem_inter.mp (mem_sigma.mp hx).2).1).1).1
    obtain ⟨hee,hqq⟩ := primitive_dilate_injective hqx he
    have hee' : x.1=y.1 := Subtype.ext hee
    cases x with
    | mk e q =>
      cases y with
      | mk e' q' =>
        dsimp only at hee' hqq
        subst e' q'
        rfl
  have hsub : T.image f ⊆ sourceCollisionsUpTo S N := by
    intro x hx
    obtain ⟨⟨e,q⟩,hz,rfl⟩ := mem_image.mp hx
    have hq := mem_inter.mp (mem_sigma.mp hz).2
    have hqa : q ∈ admissible r e N := hq.1
    have hqc := mem_filter.mp hq.2
    have hres := admissible_roots hqa
    have hS (n : ℕ) (hn : n ∈ residueTail Q r 0) (hf : n ∈ filled Q r S) : n ∈ S :=
      hf.elim id (fun hc => False.elim (hc hn))
    apply mem_filter.mpr
    refine ⟨dilate_mem_collisionsUpTo e.val (mem_Icc.mp hqc.1).1 ?_,?_,?_,?_,?_⟩
    · exact (Nat.mul_le_mul_right _ (mem_Icc.mp hqc.1).2).trans (Nat.div_mul_le_self N _)
    · exact hS _ hres.1 hqc.2.1
    · exact hS _ hres.2.1 hqc.2.2.1
    · exact hS _ hres.2.2.1 hqc.2.2.2.1
    · exact hS _ hres.2.2.2 hqc.2.2.2.2
  have hh := card_le_card hsub
  rw [card_image_of_injOn hf] at hh
  simpa only [T,card_sigma] using hh

/-- A relative finite-pattern deletion inequality. Only missing roots in the
prescribed residue class occur in its error term. -/
theorem finite_deletion_bound {Q : ℕ} (hQ : 0 < Q) (r : ℕ) (S : Set ℕ)
    (F : Finset (Family Q)) (N : ℕ) :
    (N : ℝ)*(∑ e ∈ F, (1 : ℝ)/e.val.val.2.2.2) ≤
      Q*(sourceCollisionsUpTo S N).card+Q*F.card+
        4*Q*F.card*(missing (filled Q r S) N).card := by
  have hterm (e : Family Q) :
      (N : ℝ)/e.val.val.2.2.2 ≤ Q*(good r S e N).card+Q+
        4*Q*(missing (filled Q r S) N).card := by
    have hd : (0 : ℝ) < e.val.val.2.2.2 := by exact_mod_cast primitive_height_pos e.val
    have hn := Nat.lt_mul_div_succ N (Nat.mul_pos hQ (primitive_height_pos e.val))
    have hn' : (N : ℝ) < (Q*e.val.val.2.2.2)*(((N/(Q*e.val.val.2.2.2) : ℕ) : ℝ)+1) := by
      exact_mod_cast hn
    have hg : ((N/(Q*e.val.val.2.2.2) : ℕ) : ℝ) ≤
        (good r S e N).card+4*(missing (filled Q r S) N).card := by
      exact_mod_cast good_lower_bound hQ r S e N
    apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hg (show (0 : ℝ) ≤ Q*e.val.val.2.2.2 by positivity)
    nlinarith
  have hs := sum_le_sum (fun e (_ : e ∈ F) => hterm e)
  have hc : (∑ e ∈ F, ((good r S e N).card : ℝ)) ≤
      (sourceCollisionsUpTo S N).card := by exact_mod_cast finite_good_count r S F N
  have hh := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ Q by positivity)
  have heq : (∑ e ∈ F, (N : ℝ)/e.val.val.2.2.2) =
      (N : ℝ)*(∑ e ∈ F, (1 : ℝ)/e.val.val.2.2.2) := by simp [mul_sum,div_eq_mul_inv]
  rw [heq] at hs
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] at hs
  nlinarith

lemma high_filled_density_forces_large_count {Q : ℕ} (hQ : 0 < Q) (r : ℕ) (C : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℕ, 0 < M ∧
      ∀ (S : Set ℕ) (N : ℕ), M ≤ N →
        1-ε < (filled Q r S).partialDensity Set.univ (N+1) →
        C*N < ((sourceCollisionsUpTo S N).card : ℝ) := by
  obtain ⟨F,hF⟩ := exists_large_reciprocal_sum Q hQ (Q*(C+2))
  let ε : ℝ := 1/(16*((F.card : ℝ)+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heq : 16*((F.card : ℝ)+1)*ε=1 := by dsimp [ε]; field_simp
  refine ⟨ε,hε,F.card+1,by omega,?_⟩
  intro S N hN hden
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hFN : (F.card : ℝ) ≤ N := by exact_mod_cast (show F.card ≤ N by omega)
  have hN1 : (N : ℝ)+1 ≤ 2*N := by exact_mod_cast (show N+1 ≤ 2*N by omega)
  have hmiss := missing_card_le_of_partialDensity hden
  have hmiss' : ((missing (filled Q r S) N).card : ℝ) ≤ 2*ε*N := by nlinarith
  have hweight : 4*(F.card : ℝ)*ε ≤ 1/4 := by
    nlinarith [show (0 : ℝ) ≤ F.card from Nat.cast_nonneg _]
  have hweighted := mul_le_mul_of_nonneg_left hmiss'
    (show 0 ≤ 4*(F.card : ℝ) by positivity)
  have hweightN := mul_le_mul_of_nonneg_right hweight hN0.le
  have hbad : 4*(F.card : ℝ)*(missing (filled Q r S) N).card ≤ N/2 := by nlinarith
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hbadQ := mul_le_mul_of_nonneg_left hbad hQ0.le
  have hFNQ := mul_le_mul_of_nonneg_left hFN hQ0.le
  have hlarge := mul_lt_mul_of_pos_left hF hN0
  have hbound := finite_deletion_bound hQ r S F N
  have hh : (Q : ℝ)*(C*N) < Q*(sourceCollisionsUpTo S N).card := by nlinarith
  exact (mul_lt_mul_iff_right₀ hQ0).mp hh

theorem filled_density_one_superlinear {Q r : ℕ} {S : Set ℕ} (hQ : 0 < Q)
    (hS : (filled Q r S).lowerDensity=1) (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M, C*N < ((sourceCollisionsUpTo S N).card : ℝ) := by
  obtain ⟨ε,hε,M,hM,hcount⟩ := high_filled_density_forces_large_count hQ r C
  have hev : ∀ᶠ n : ℕ in atTop, 1-ε < (filled Q r S).partialDensity Set.univ n :=
    eventually_lt_of_lt_liminf
      (show 1-ε < (filled Q r S).lowerDensity by rw [hS]; linarith)
      (isBoundedUnder_of ⟨0,fun _ => by positivity⟩)
  obtain ⟨L,hL⟩ := eventually_atTop.mp hev
  exact ⟨max M L,fun N hN => hcount S N (by omega) (hL (N+1) (by omega))⟩

lemma filled_lowerDensity_one {Q r : ℕ} {S : Set ℕ}
    (hS : (residueTail Q r 0 \ S).HasDensity 0) : (filled Q r S).lowerDensity=1 := by
  have he : (filled Q r S)ᶜ=residueTail Q r 0 \ S := by
    ext n
    simp [filled,and_comm]
  have hf : ∀ᶠ n : ℕ in atTop,
      1-(residueTail Q r 0 \ S).partialDensity Set.univ n =
        (filled Q r S).partialDensity Set.univ n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hh := partialDensity_compl_add (S := filled Q r S) (show 0 < n by omega)
    rw [he] at hh
    linarith
  have ht : Tendsto (fun n : ℕ => 1-(residueTail Q r 0 \ S).partialDensity Set.univ n)
      atTop (𝓝 1) := by simpa using hS.const_sub (1 : ℝ)
  exact (ht.congr' hf).liminf_eq

/-- Deleting a density-zero set from a residue class still leaves
superlinear cubic collision counts in every sufficiently large prefix. -/
theorem zero_density_deletion_superlinear {Q r : ℕ} {S : Set ℕ} (hQ : 0 < Q)
    (hS : (residueTail Q r 0 \ S).HasDensity 0) (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M, C*N < ((sourceCollisionsUpTo S N).card : ℝ) :=
  filled_density_one_superlinear hQ (filled_lowerDensity_one hS) C

theorem zero_density_deletion_not_linear_source {Q r : ℕ} {S : Set ℕ} (hQ : 0 < Q)
    (hS : (residueTail Q r 0 \ S).HasDensity 0) :
    ¬ ∃ C : ℕ, ∀ N, (CubicHypergraph.edges N S).card ≤ C*N := by
  rintro ⟨C,hC⟩
  obtain ⟨M,hM⟩ := zero_density_deletion_superlinear hQ hS (2*C)
  let N := M+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hg := hM N (by dsimp [N]; omega)
  have hb : ((sourceCollisionsUpTo S N).card : ℝ) ≤ C*(N+1) := by
    exact_mod_cast (source_count_le_hypergraph S N).trans (hC (N+1))
  have hNN : (N : ℝ)+1 ≤ 2*N := by exact_mod_cast (show N+1 ≤ 2*N by omega)
  nlinarith [mul_le_mul_of_nonneg_left hNN (show (0 : ℝ) ≤ C by positivity)]

#print axioms high_filled_density_forces_large_count
#print axioms filled_density_one_superlinear
#print axioms zero_density_deletion_superlinear
#print axioms zero_density_deletion_not_linear_source
#print axioms admissible_lower_bound
#print axioms finite_deletion_bound
end Erdos1206.ProgressionCollisionDeletion
