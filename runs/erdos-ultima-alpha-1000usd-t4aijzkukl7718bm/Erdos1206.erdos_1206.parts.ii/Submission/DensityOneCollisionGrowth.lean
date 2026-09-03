import Submission.SourceCollisionGrowth
import Submission.AlmostColoringReduction
import Submission.CubicHypergraph

/-!
Deleting a set of natural density zero cannot give a source with uniformly
linear cubic collision counts. This is a limitation on one sufficient
criterion, not a disproof of the positive-density Sidon conjecture.
-/
namespace Erdos1206.DensityOneCollisionGrowth
open Finset Filter CubeCollisionGrowth PrimitiveCollisionMass
open scoped Classical Topology

noncomputable def missing (S : Set ℕ) (N : ℕ) : Finset ℕ :=
  (range (N+1)).filter (fun n => n ∉ S)

private lemma bad_multipliers_card {S : Set ℕ} {N D r : ℕ}
    (hr : 0 < r) (hrD : r ≤ D) :
    ((Icc 1 (N/D)).filter (fun q => q*r ∉ S)).card ≤ (missing S N).card := by
  apply card_le_card_of_injOn (fun q => q*r)
  · intro q hq
    change q ∈ (Icc 1 (N/D)).filter (fun q => q*r ∉ S) at hq
    obtain ⟨hq,hbad⟩ := mem_filter.mp hq
    have hbound : q*r ≤ N := (Nat.mul_le_mul (mem_Icc.mp hq).2 hrD).trans
      (Nat.div_mul_le_self N D)
    change q*r ∈ missing S N
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),hbad⟩
  · intro q _ q' _ he
    exact Nat.eq_of_mul_eq_mul_right hr he

noncomputable def goodMultipliers (S : Set ℕ) (e : Collision) (N : ℕ) : Finset ℕ :=
  (Icc 1 (N/e.val.2.2.2)).filter (fun q =>
    q*e.val.1 ∈ S ∧ q*e.val.2.1 ∈ S ∧ q*e.val.2.2.1 ∈ S ∧ q*e.val.2.2.2 ∈ S)

lemma goodMultipliers_card (S : Set ℕ) (e : Collision) (N : ℕ) :
    N/e.val.2.2.2 ≤ (goodMultipliers S e N).card + 4*(missing S N).card := by
  let U := Icc 1 (N/e.val.2.2.2)
  let B₀ := U.filter (fun q => q*e.val.1 ∉ S)
  let B₁ := U.filter (fun q => q*e.val.2.1 ∉ S)
  let B₂ := U.filter (fun q => q*e.val.2.2.1 ∉ S)
  let B₃ := U.filter (fun q => q*e.val.2.2.2 ∉ S)
  have hcover : U ⊆ goodMultipliers S e N ∪ (B₀ ∪ (B₁ ∪ (B₂ ∪ B₃))) := by
    intro q hq
    by_cases h₀ : q*e.val.1 ∈ S
    · by_cases h₁ : q*e.val.2.1 ∈ S
      · by_cases h₂ : q*e.val.2.2.1 ∈ S
        · by_cases h₃ : q*e.val.2.2.2 ∈ S
          · exact mem_union_left _ (mem_filter.mpr ⟨hq,h₀,h₁,h₂,h₃⟩)
          · simp only [mem_union]
            exact Or.inr (Or.inr (Or.inr (Or.inr (mem_filter.mpr ⟨hq,h₃⟩))))
        · simp only [mem_union]
          exact Or.inr (Or.inr (Or.inr (Or.inl (mem_filter.mpr ⟨hq,h₂⟩))))
      · simp only [mem_union]
        exact Or.inr (Or.inr (Or.inl (mem_filter.mpr ⟨hq,h₁⟩)))
    · simp only [mem_union]
      exact Or.inr (Or.inl (mem_filter.mpr ⟨hq,h₀⟩))
  have he := e.property
  have hb₀ : B₀.card ≤ (missing S N).card := bad_multipliers_card he.1
    (he.2.1.trans (he.2.2.1.trans he.2.2.2.1)).le
  have hb₁ : B₁.card ≤ (missing S N).card := bad_multipliers_card (he.1.trans he.2.1)
    (he.2.2.1.trans he.2.2.2.1).le
  have hb₂ : B₂.card ≤ (missing S N).card := bad_multipliers_card
    (he.1.trans (he.2.1.trans he.2.2.1)) he.2.2.2.1.le
  have hb₃ : B₃.card ≤ (missing S N).card := bad_multipliers_card (primitive_height_pos e) le_rfl
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  have h₀ := card_union_le B₀ (B₁ ∪ (B₂ ∪ B₃))
  have h₁ := card_union_le B₁ (B₂ ∪ B₃)
  have h₂ := card_union_le B₂ B₃
  have hU : U.card = N/e.val.2.2.2 := by simp [U]
  omega

lemma finite_good_dilate_count (S : Set ℕ) (F : Finset Collision) (N : ℕ) :
    ∑ e ∈ F, (goodMultipliers S e N).card ≤ (sourceCollisionsUpTo S N).card := by
  let T := F.sigma (fun e => goodMultipliers S e N)
  let f : ((e : Collision) × ℕ) → Quad := fun z => dilate z.2 z.1.val
  have hf : Set.InjOn f (T : Set ((e : Collision) × ℕ)) := by
    intro x hx y hy hxy
    have hqx : 0 < x.2 := (mem_Icc.mp (mem_filter.mp (mem_sigma.mp hx).2).1).1
    obtain ⟨he,hq⟩ := primitive_dilate_injective hqx hxy
    cases x with
    | mk e q =>
      cases y with
      | mk e' q' =>
        dsimp only at he hq
        subst e' q'
        rfl
  have hsub : T.image f ⊆ sourceCollisionsUpTo S N := by
    intro x hx
    obtain ⟨⟨e,q⟩,hz,rfl⟩ := mem_image.mp hx
    have hq := mem_filter.mp (mem_sigma.mp hz).2
    apply mem_filter.mpr
    constructor
    · apply dilate_mem_collisionsUpTo e (mem_Icc.mp hq.1).1
      exact (Nat.mul_le_mul_right _ (mem_Icc.mp hq.1).2).trans (Nat.div_mul_le_self N _)
    · exact hq.2
  have hh := card_le_card hsub
  rw [card_image_of_injOn hf] at hh
  simpa only [T,card_sigma] using hh

/-- A finite collection of primitive patterns has a deletion bound linear
in the number of omitted roots, uniformly in the prefix length. -/
theorem finite_reciprocal_deletion_bound (S : Set ℕ) (F : Finset Collision) (N : ℕ) :
    (N : ℝ)*(∑ e ∈ F, (1 : ℝ)/e.val.2.2.2) ≤
      (sourceCollisionsUpTo S N).card + F.card + 4*F.card*(missing S N).card := by
  have hterm (e : Collision) :
      (N : ℝ)/e.val.2.2.2 ≤ (goodMultipliers S e N).card + 1 + 4*(missing S N).card := by
    have hp : (0 : ℝ) < e.val.2.2.2 := by exact_mod_cast primitive_height_pos e
    have hfloor : (N : ℝ)/e.val.2.2.2 ≤ ((N/e.val.2.2.2 : ℕ) : ℝ)+1 := by
      apply (div_le_iff₀ hp).mpr
      have hh := Nat.lt_mul_div_succ N (primitive_height_pos e)
      have hh' : (N : ℝ) < e.val.2.2.2 * (((N/e.val.2.2.2 : ℕ) : ℝ)+1) := by
        exact_mod_cast hh
      nlinarith
    have hg : ((N/e.val.2.2.2 : ℕ) : ℝ) ≤
        (goodMultipliers S e N).card + 4*(missing S N).card := by
      exact_mod_cast goodMultipliers_card S e N
    linarith
  have hc : (∑ e ∈ F, ((goodMultipliers S e N).card : ℝ)) ≤
      (sourceCollisionsUpTo S N).card := by exact_mod_cast finite_good_dilate_count S F N
  have hs := sum_le_sum (fun e (_ : e ∈ F) => hterm e)
  have heq : (∑ e ∈ F, (N : ℝ)/e.val.2.2.2) =
      (N : ℝ)*(∑ e ∈ F, (1 : ℝ)/e.val.2.2.2) := by simp [mul_sum,div_eq_mul_inv]
  rw [heq] at hs
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at hs
  nlinarith

lemma missing_card_le_of_partialDensity {S : Set ℕ} {N : ℕ} {ε : ℝ}
    (h : 1-ε < S.partialDensity Set.univ (N+1)) :
    ((missing S N).card : ℝ) ≤ ε*((N : ℝ)+1) := by
  have hcomp := partialDensity_compl_add (S := S) (Nat.succ_pos N)
  have he : Sᶜ ∩ Set.Iio (N+1) = (missing S N : Set ℕ) := by
    ext n
    simp [missing,and_comm]
  have hpd : Sᶜ.partialDensity Set.univ (N+1) =
      ((missing S N).card : ℝ)/((N : ℝ)+1) := by
    simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,he,
      Set.ncard_coe_finset,Nat.ncard_Iio,Nat.cast_add,Nat.cast_one]
  have hh : ((missing S N).card : ℝ)/((N : ℝ)+1) < ε := by
    rw [hpd] at hcomp
    linarith
  exact ((div_lt_iff₀ (by positivity : 0 < (N : ℝ)+1)).mp hh).le

/-- For each requested collision-count coefficient, some fixed density
threshold below one forces a larger count at every sufficiently long prefix. -/
theorem high_density_forces_large_count (C : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℕ, 0 < M ∧
      ∀ (S : Set ℕ) (N : ℕ), M ≤ N →
        1-ε < S.partialDensity Set.univ (N+1) →
        C*N < ((sourceCollisionsUpTo S N).card : ℝ) := by
  obtain ⟨F,hF⟩ := exists_large_primitive_reciprocal_sum (C+2)
  let ε : ℝ := 1/(16*((F.card : ℝ)+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heq : 16*((F.card : ℝ)+1)*ε=1 := by
    dsimp [ε]
    field_simp
  refine ⟨ε,hε,F.card+1,by omega,?_⟩
  intro S N hN hden
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hFN : (F.card : ℝ) ≤ N := by exact_mod_cast (show F.card ≤ N by omega)
  have hN1 : (N : ℝ)+1 ≤ 2*N := by exact_mod_cast (show N+1 ≤ 2*N by omega)
  have hmiss := missing_card_le_of_partialDensity hden
  have hmiss' : ((missing S N).card : ℝ) ≤ 2*ε*N := by nlinarith
  have hweight : 4*(F.card : ℝ)*ε ≤ 1/4 := by nlinarith [show (0 : ℝ) ≤ F.card from Nat.cast_nonneg _]
  have hweighted := mul_le_mul_of_nonneg_left hmiss'
    (show 0 ≤ 4*(F.card : ℝ) by positivity)
  have hweightN := mul_le_mul_of_nonneg_right hweight hN0.le
  have hlarge := mul_lt_mul_of_pos_left hF hN0
  have hbound := finite_reciprocal_deletion_bound S F N
  nlinarith

/-- Natural density one leaves a superlinear number of cubic collisions,
not merely a large count along a subsequence. -/
theorem lowerDensity_one_superlinear {S : Set ℕ} (hS : S.lowerDensity=1) (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M, C*N < ((sourceCollisionsUpTo S N).card : ℝ) := by
  obtain ⟨ε,hε,M,hM,hcount⟩ := high_density_forces_large_count C
  have hev : ∀ᶠ n : ℕ in atTop, 1-ε < S.partialDensity Set.univ n := by
    exact eventually_lt_of_lt_liminf (show 1-ε < S.lowerDensity by rw [hS]; linarith)
      (isBoundedUnder_of ⟨0,fun _ => by positivity⟩)
  obtain ⟨L,hL⟩ := eventually_atTop.mp hev
  refine ⟨max M L,fun N hN => hcount S N (by omega) (hL (N+1) (by omega))⟩

theorem lowerDensity_one_count_div_tendsto_atTop {S : Set ℕ}
    (hS : S.lowerDensity=1) :
    Tendsto (fun N : ℕ => ((sourceCollisionsUpTo S N).card : ℝ)/N) atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  obtain ⟨M,hM⟩ := lowerDensity_one_superlinear hS C
  filter_upwards [eventually_ge_atTop (M+1)] with N hN
  apply (le_div_iff₀ (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega))).mpr
  exact (hM N (by omega)).le

/-- Even upper density one precludes an eventual uniform linear bound. -/
theorem upperDensity_one_unbounded {S : Set ℕ} (hS : S.upperDensity=1)
    (C : ℝ) (L : ℕ) :
    ∃ N : ℕ, L ≤ N ∧ C*N < ((sourceCollisionsUpTo S N).card : ℝ) := by
  obtain ⟨ε,hε,M,hM,hcount⟩ := high_density_forces_large_count C
  have hfreq : ∃ᶠ n : ℕ in atTop, 1-ε < S.partialDensity Set.univ n := by
    apply frequently_lt_of_lt_limsup
      (isCoboundedUnder_le_of_le atTop (fun n =>
        (show (0 : ℝ) ≤ S.partialDensity Set.univ n by positivity)))
    change 1-ε < S.upperDensity
    rw [hS]
    linarith
  obtain ⟨n,hn,hlarge⟩ := (hfreq.and_eventually (eventually_ge_atTop (max M L+1))).exists
  refine ⟨n-1,by omega,hcount S (n-1) (by omega) ?_⟩
  simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hn

private lemma ordered_quad_injective {x y : Quad}
    (hx : x.1 < x.2.1 ∧ x.2.1 < x.2.2.1 ∧ x.2.2.1 < x.2.2.2)
    (hy : y.1 < y.2.1 ∧ y.2.1 < y.2.2.1 ∧ y.2.2.1 < y.2.2.2)
    (he : ({x.1,x.2.1,x.2.2.1,x.2.2.2} : Finset ℕ)=
      {y.1,y.2.1,y.2.2.1,y.2.2.2}) : x=y := by
  have hs (z : Quad) (hz : z.1 < z.2.1 ∧ z.2.1 < z.2.2.1 ∧ z.2.2.1 < z.2.2.2) :
      List.Pairwise (· < ·) [z.1,z.2.1,z.2.2.1,z.2.2.2] := by
    simp [List.pairwise_cons]
    omega
  have hl := (hs x hx).eq_of_mem_iff (hs y hy) (fun n => by
    have hh := congrArg (fun f : Finset ℕ => n ∈ f) he
    simpa only [mem_insert,mem_singleton,List.mem_cons,List.not_mem_nil,or_false]
      using Iff.of_eq hh)
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨a',b',c',d'⟩
  simpa using hl

/-- The ordered-tuple count embeds in the collision hypergraph used by the
linear-source extraction theorem. -/
lemma source_count_le_hypergraph (S : Set ℕ) (N : ℕ) :
    (sourceCollisionsUpTo S N).card ≤ (CubicHypergraph.edges (N+1) S).card := by
  let f : Quad → Finset ℕ := fun x => {x.1,x.2.1,x.2.2.1,x.2.2.2}
  apply card_le_card_of_injOn f
  · intro x hx
    change x ∈ sourceCollisionsUpTo S N at hx
    obtain ⟨hx,hS⟩ := mem_filter.mp hx
    obtain ⟨hxN,hx⟩ := mem_filter.mp hx
    have hN : x.1 < N+1 ∧ x.2.1 < N+1 ∧ x.2.2.1 < N+1 ∧ x.2.2.2 < N+1 := by
      simpa only [mem_product,mem_range] using hxN
    change f x ∈ CubicHypergraph.edges (N+1) S
    apply CubicHypergraph.mem_edges.mpr
    refine ⟨?_,?_,x.1,x.2.1,x.2.2.1,x.2.2.2,rfl,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2⟩
    · intro n hn
      simp only [f,mem_insert,mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> exact mem_range.mpr (by omega)
    · intro n hn
      change n ∈ f x at hn
      simp only [f,mem_insert,mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> tauto
  · intro x hx y hy he
    change x ∈ sourceCollisionsUpTo S N at hx
    change y ∈ sourceCollisionsUpTo S N at hy
    have hx' := (mem_filter.mp (mem_filter.mp hx).1).2
    have hy' := (mem_filter.mp (mem_filter.mp hy).1).2
    exact ordered_quad_injective ⟨hx'.2.1,hx'.2.2.1,hx'.2.2.2.1⟩
      ⟨hy'.2.1,hy'.2.2.1,hy'.2.2.2.1⟩ he

/-- Removing any set of density zero cannot satisfy the linear-source
hypothesis used to extract positive-density cube-Sidon sets. -/
theorem upperDensity_one_not_linear_source {S : Set ℕ} (hS : S.upperDensity=1) :
    ¬ ∃ C : ℕ, ∀ N, (CubicHypergraph.edges N S).card ≤ C*N := by
  rintro ⟨C,hC⟩
  obtain ⟨N,hN,hcount⟩ := upperDensity_one_unbounded hS (2*C) 1
  have hb : ((sourceCollisionsUpTo S N).card : ℝ) ≤ C*(N+1) := by
    exact_mod_cast (source_count_le_hypergraph S N).trans (hC (N+1))
  have hN' : (N : ℝ)+1 ≤ 2*N := by exact_mod_cast (show N+1 ≤ 2*N by omega)
  have hh := mul_le_mul_of_nonneg_left hN' (show (0 : ℝ) ≤ C by positivity)
  nlinarith

#print axioms source_count_le_hypergraph
#print axioms upperDensity_one_not_linear_source
#print axioms finite_reciprocal_deletion_bound
#print axioms high_density_forces_large_count
#print axioms lowerDensity_one_superlinear
#print axioms lowerDensity_one_count_div_tendsto_atTop
#print axioms upperDensity_one_unbounded
end Erdos1206.DensityOneCollisionGrowth
