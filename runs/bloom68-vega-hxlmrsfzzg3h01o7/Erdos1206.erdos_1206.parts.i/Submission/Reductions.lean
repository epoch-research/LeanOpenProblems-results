import FormalConjecturesUtil

/-!
# Exact reductions for Sidon subsets of the cubes

This file does not import `Submission.Spec`. It proves the finite combinatorial
reductions and conditional density statements, not the density hypothesis itself.
The roots are natural numbers, so cubing is injective.
-/

namespace Erdos1206

/-- The Sidon property expressed in terms of the roots of the cubes. -/
def CubeSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Cubing is injective on the natural numbers. -/
theorem cube_injective : Function.Injective (fun n : ℕ => n ^ 3) :=
  Nat.pow_left_injective (by decide)

@[simp]
theorem cube_eq_cube_iff {a b : ℕ} : a ^ 3 = b ^ 3 ↔ a = b :=
  cube_injective.eq_iff

/-- The root formulation is exactly the Sidon property of the image of cubing. -/
theorem cubeSidon_iff_isSidon_image (A : Finset ℕ) :
    CubeSidon A ↔ IsSidon (↑(A.image (fun n => n ^ 3)) : Set ℕ) := by
  constructor
  · intro h x hx y hy z hz w hw heq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
    rcases h a ha b hb c hc d hd heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · intro h a ha b hb c hc d hd heq
    have h' := h (a ^ 3) (Finset.mem_image_of_mem (fun n : ℕ => n ^ 3) ha)
      (c ^ 3) (Finset.mem_image_of_mem (fun n : ℕ => n ^ 3) hc)
      (b ^ 3) (Finset.mem_image_of_mem (fun n : ℕ => n ^ 3) hb)
      (d ^ 3) (Finset.mem_image_of_mem (fun n : ℕ => n ^ 3) hd) heq
    simpa only [cube_eq_cube_iff] using h'

/-- Passing from roots to their cubes does not change the cardinality. -/
@[simp]
theorem card_image_cubes (A : Finset ℕ) :
    (A.image (fun n => n ^ 3)).card = A.card :=
  Finset.card_image_of_injective A cube_injective

/-- Exact finite-scale reduction of the target to a cardinality bound on cube-Sidon roots. -/
theorem exists_sidon_subset_cubes_iff (N : ℕ) (r : ℝ) :
    (∃ S : Finset ℕ, S ⊆ (Finset.Icc 1 N).image (fun n => n ^ 3) ∧
      IsSidon (S : Set ℕ) ∧ r ≤ (S.card : ℝ)) ↔
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ CubeSidon A ∧ r ≤ (A.card : ℝ)) := by
  constructor
  · rintro ⟨S, hSI, hS, hcard⟩
    obtain ⟨A, hAI, rfl⟩ := Finset.subset_image_iff.mp hSI
    refine ⟨A, hAI, (cubeSidon_iff_isSidon_image A).mpr hS, ?_⟩
    simpa only [card_image_cubes] using hcard
  · rintro ⟨A, hAI, hA, hcard⟩
    refine ⟨A.image (fun n => n ^ 3), Finset.image_subset_image hAI,
      (cubeSidon_iff_isSidon_image A).mp hA, ?_⟩
    simpa only [card_image_cubes] using hcard

@[simp]
theorem cubeSidon_empty : CubeSidon ∅ := by
  simp [CubeSidon]

/-- The root Sidon property passes to subsets. -/
theorem CubeSidon.subset {A B : Finset ℕ} (hB : CubeSidon B) (hAB : A ⊆ B) :
    CubeSidon A := by
  intro a ha b hb c hc d hd heq
  exact hB a (hAB ha) b (hAB hb) c (hAB hc) d (hAB hd) heq

/-- The two possible obstructions to inserting a new root into a cube-Sidon set. -/
theorem cubeSidon_insert_iff {A : Finset ℕ} {n : ℕ}
    (hA : CubeSidon A) (hn : n ∉ A) :
    CubeSidon (insert n A) ↔
      ∀ a ∈ A, ∀ b ∈ A,
        n ^ 3 + n ^ 3 ≠ a ^ 3 + b ^ 3 ∧
          ∀ c ∈ A, n ^ 3 + a ^ 3 ≠ b ^ 3 + c ^ 3 := by
  have hn' : n ^ 3 ∉ (↑(A.image (fun m => m ^ 3)) : Set ℕ) := by
    intro h
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp h
    exact hn (cube_injective heq ▸ ha)
  rw [cubeSidon_iff_isSidon_image, Finset.image_insert, Finset.coe_insert,
    ← Set.union_singleton, Set.IsSidon.insert ((cubeSidon_iff_isSidon_image A).mp hA)]
  simp only [hn', false_or, Finset.mem_coe, Finset.forall_mem_image]

/-- Insertion fails exactly when one of the two displayed equations has old roots. -/
theorem not_cubeSidon_insert_iff {A : Finset ℕ} {n : ℕ}
    (hA : CubeSidon A) (hn : n ∉ A) :
    ¬ CubeSidon (insert n A) ↔
      (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3) ∨
      (∃ a ∈ A, ∃ b ∈ A, n ^ 3 + n ^ 3 = a ^ 3 + b ^ 3) := by
  classical
  constructor
  · intro hnot
    by_contra h
    apply hnot
    apply (cubeSidon_insert_iff hA hn).mpr
    intro a ha b hb
    exact ⟨fun heq => h (Or.inr ⟨a, ha, b, hb, heq⟩),
      fun c hc heq => h (Or.inl ⟨a, ha, b, hb, c, hc, heq⟩)⟩
  · intro h hs
    have hg := (cubeSidon_insert_iff hA hn).mp hs
    rcases h with ⟨a, ha, b, hb, c, hc, heq⟩ | ⟨a, ha, b, hb, heq⟩
    · exact (hg a ha b hb).2 c hc heq
    · exact (hg a ha b hb).1 heq

/-- `F_N(A)`: the roots outside `A` in `[1,N]` forbidden by an insertion equation. -/
def forbiddenRoots (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  ((Finset.Icc 1 N) \ A).filter fun n =>
    (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3) ∨
    (∃ a ∈ A, ∃ b ∈ A, n ^ 3 + n ^ 3 = a ^ 3 + b ^ 3)

@[simp]
theorem mem_forbiddenRoots {N n : ℕ} {A : Finset ℕ} :
    n ∈ forbiddenRoots N A ↔ n ∈ Finset.Icc 1 N ∧ n ∉ A ∧
      ((∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3) ∨
       (∃ a ∈ A, ∃ b ∈ A, n ^ 3 + n ^ 3 = a ^ 3 + b ^ 3)) := by
  simp only [forbiddenRoots, Finset.mem_filter, Finset.mem_sdiff, and_assoc]

/-- The equation-based definition of forbidden roots is exactly insertion failure. -/
theorem mem_forbiddenRoots_iff_not_cubeSidon_insert {N n : ℕ} {A : Finset ℕ}
    (hA : CubeSidon A) :
    n ∈ forbiddenRoots N A ↔
      n ∈ Finset.Icc 1 N ∧ n ∉ A ∧ ¬ CubeSidon (insert n A) := by
  rw [mem_forbiddenRoots]
  refine and_congr_right fun _ => and_congr_right fun hn => ?_
  exact (not_cubeSidon_insert_iff hA hn).symm

theorem forbiddenRoots_subset (N : ℕ) (A : Finset ℕ) :
    forbiddenRoots N A ⊆ Finset.Icc 1 N := by
  intro n hn
  exact (mem_forbiddenRoots.mp hn).1

theorem disjoint_forbiddenRoots (N : ℕ) (A : Finset ℕ) :
    Disjoint A (forbiddenRoots N A) := by
  apply Finset.disjoint_left.mpr
  intro n hn hF
  exact (mem_forbiddenRoots.mp hF).2.1 hn

/-- Inclusion-maximality among cube-Sidon subsets of `[1,N]`. -/
def MaximalCubeSidon (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ CubeSidon A ∧
    ∀ B : Finset ℕ, A ⊆ B → B ⊆ Finset.Icc 1 N → CubeSidon B → B = A

/-- A maximum-cardinality choice gives an inclusion-maximal cube-Sidon set. -/
theorem exists_maximalCubeSidon (N : ℕ) :
    ∃ A : Finset ℕ, MaximalCubeSidon N A := by
  classical
  let candidates := (Finset.Icc 1 N).powerset.filter CubeSidon
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨A, hAmem, hmax⟩ := candidates.exists_max_image Finset.card hnonempty
  obtain ⟨hAin, hAsidon⟩ := Finset.mem_filter.mp hAmem
  refine ⟨A, Finset.mem_powerset.mp hAin, hAsidon, ?_⟩
  intro B hAB hBI hBS
  apply (Finset.eq_of_subset_of_card_le hAB ?_).symm
  exact hmax B (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBI, hBS⟩)

/-- No missing root in the ambient interval can be inserted into a maximal set. -/
theorem MaximalCubeSidon.not_insert {N n : ℕ} {A : Finset ℕ}
    (hA : MaximalCubeSidon N A) (hn : n ∈ Finset.Icc 1 N) (hnA : n ∉ A) :
    ¬ CubeSidon (insert n A) := by
  intro hs
  have heq := hA.2.2 (insert n A) (Finset.subset_insert n A)
    (Finset.insert_subset hn hA.1) hs
  exact hnA (heq ▸ Finset.mem_insert_self n A)

/-- For a maximal cube-Sidon set, the forbidden roots are precisely its complement. -/
theorem MaximalCubeSidon.forbiddenRoots_eq_sdiff {N : ℕ} {A : Finset ℕ}
    (hA : MaximalCubeSidon N A) :
    forbiddenRoots N A = Finset.Icc 1 N \ A := by
  ext n
  rw [mem_forbiddenRoots_iff_not_cubeSidon_insert hA.2.1, Finset.mem_sdiff]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hA.not_insert h.1 h.2⟩⟩

/-- The interval is partitioned into selected roots and forbidden roots. -/
theorem MaximalCubeSidon.union_forbiddenRoots {N : ℕ} {A : Finset ℕ}
    (hA : MaximalCubeSidon N A) :
    A ∪ forbiddenRoots N A = Finset.Icc 1 N := by
  rw [hA.forbiddenRoots_eq_sdiff]
  exact Finset.union_sdiff_of_subset hA.1

/-- Exact cardinality identity, including the empty interval at `N = 0`. -/
theorem MaximalCubeSidon.card_add_card_forbiddenRoots {N : ℕ} {A : Finset ℕ}
    (hA : MaximalCubeSidon N A) :
    N = A.card + (forbiddenRoots N A).card := by
  calc
    N = (Finset.Icc 1 N).card := by simp
    _ = (A ∪ forbiddenRoots N A).card := congrArg Finset.card hA.union_forbiddenRoots.symm
    _ = A.card + (forbiddenRoots N A).card :=
      Finset.card_union_of_disjoint (disjoint_forbiddenRoots N A)

/-- The proposed forbidden-root estimate, at a single value of `N`.
No assertion that this bound holds is made here. -/
def DensityProjectionBound (δ : ℝ) (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → CubeSidon A →
    (A.card : ℝ) ≤ δ * (N : ℝ) →
      ((forbiddenRoots N A).card : ℝ) < (1 - δ) * (N : ℝ)

/-- The partition identity rules out a small maximal set under the proposed bound. -/
theorem MaximalCubeSidon.card_gt_of_densityProjectionBound {N : ℕ} {A : Finset ℕ}
    {δ : ℝ} (hA : MaximalCubeSidon N A) (hprojection : DensityProjectionBound δ N) :
    δ * (N : ℝ) < (A.card : ℝ) := by
  by_contra h
  have hsmall : (A.card : ℝ) ≤ δ * (N : ℝ) := le_of_not_gt h
  have hF := hprojection A hA.1 hA.2.1 hsmall
  have hcard : (N : ℝ) = (A.card : ℝ) + ((forbiddenRoots N A).card : ℝ) := by
    exact_mod_cast hA.card_add_card_forbiddenRoots
  nlinarith

/-- A single-scale forbidden-root bound produces a large set of roots. -/
theorem exists_large_cubeSidon_of_densityProjectionBound {δ : ℝ} {N : ℕ}
    (hprojection : DensityProjectionBound δ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ CubeSidon A ∧
      δ * (N : ℝ) < (A.card : ℝ) := by
  obtain ⟨A, hA⟩ := exists_maximalCubeSidon N
  exact ⟨A, hA.1, hA.2.1, hA.card_gt_of_densityProjectionBound hprojection⟩

/-- Projection to cubes preserves the lower bound and gives a Sidon subset of the target. -/
theorem exists_large_sidon_of_densityProjectionBound {δ : ℝ} {N : ℕ}
    (hprojection : DensityProjectionBound δ N) :
    ∃ S : Finset ℕ, S ⊆ (Finset.Icc 1 N).image (fun n => n ^ 3) ∧
      IsSidon (S : Set ℕ) ∧ δ * (N : ℝ) < (S.card : ℝ) := by
  obtain ⟨A, hAI, hAS, hcard⟩ :=
    exists_large_cubeSidon_of_densityProjectionBound hprojection
  refine ⟨A.image (fun n => n ^ 3), Finset.image_subset_image hAI,
    (cubeSidon_iff_isSidon_image A).mp hAS, ?_⟩
  simpa only [card_image_cubes] using hcard

/-- An eventual density-projection bound suffices for the original positive-density
conclusion, with `c = δ`. No upper bound on the positive constant is needed for this implication. -/
theorem erdos_1206_of_eventual_density_projection (δ : ℝ) (hδ : 0 < δ)
    (hprojection : ∀ᶠ N in Filter.atTop, DensityProjectionBound δ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in Filter.atTop, ∃ S : Finset ℕ,
      S ⊆ (Finset.Icc 1 N).image (fun n => n ^ 3) ∧
      IsSidon (S : Set ℕ) ∧ c * (N : ℝ) ≤ (S.card : ℝ) := by
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hprojection] with N hN
  obtain ⟨S, hSI, hSidon, hcard⟩ := exists_large_sidon_of_densityProjectionBound hN
  exact ⟨S, hSI, hSidon, hcard.le⟩

/-- The useful all-positive-`N` version of the proposed criterion. The bound is still
an unproved hypothesis, and the conclusion is exactly the original existential statement. -/
theorem erdos_1206_of_positive_density_projection
    (hprojection : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ N : ℕ, 1 ≤ N → DensityProjectionBound δ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in Filter.atTop, ∃ S : Finset ℕ,
      S ⊆ (Finset.Icc 1 N).image (fun n => n ^ 3) ∧
      IsSidon (S : Set ℕ) ∧ c * (N : ℝ) ≤ (S.card : ℝ) := by
  obtain ⟨δ, hδ, _hhalf, hbound⟩ := hprojection
  apply erdos_1206_of_eventual_density_projection δ hδ
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
  exact hbound N hN

/-- The literal all-natural-`N` criterion in the question implies the original conclusion.
Its hypothesis is stronger than necessary: at `N = 0` the strict bound cannot hold.
Use `erdos_1206_of_positive_density_projection` or the eventual version to avoid that issue.
This implication uses the maximal-set reduction, not the inconsistency at zero. -/
theorem erdos_1206_of_density_projection
    (hprojection : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ N : ℕ, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → CubeSidon A →
        (A.card : ℝ) ≤ δ * (N : ℝ) →
          ((forbiddenRoots N A).card : ℝ) < (1 - δ) * (N : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in Filter.atTop, ∃ S : Finset ℕ,
      S ⊆ (Finset.Icc 1 N).image (fun n => n ^ 3) ∧
      IsSidon (S : Set ℕ) ∧ c * (N : ℝ) ≤ (S.card : ℝ) := by
  obtain ⟨δ, hδ, hhalf, hbound⟩ := hprojection
  exact erdos_1206_of_positive_density_projection
    ⟨δ, hδ, hhalf, fun N _ => hbound N⟩

/-- The strict single-scale bound cannot hold at zero, for any `δ`.
This is only a boundary-case observation and is not used to prove the density implications. -/
theorem not_densityProjectionBound_zero (δ : ℝ) : ¬ DensityProjectionBound δ 0 := by
  intro h
  have hzero := h ∅ (by simp) cubeSidon_empty (by simp)
  simp [forbiddenRoots] at hzero

end Erdos1206
