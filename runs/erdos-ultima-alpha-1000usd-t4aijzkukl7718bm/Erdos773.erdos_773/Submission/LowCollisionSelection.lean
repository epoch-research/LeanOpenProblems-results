import Submission.WeakSidonExtraction

/-!
A collision-count reduction for Erdős 773. Only four-distinct-entry supports
need to be counted: weak Sidon extraction handles the three-entry supports
at constant cost. The low-collision hypothesis below is NOT established.
-/
namespace Erdos773.LowCollisionSelection
open Finset Filter WeakSidonExtraction
set_option maxHeartbeats 1000000

/-- Four-distinct-entry, nontrivial equal-pair-sum supports in a finite set
of values. Each support is counted once, not once per ordered presentation. -/
noncomputable def fourSupports (A : Finset ℕ) : Finset (Finset A) :=
  (sidonObstructions A).filter (fun e => e.card = 4)

private lemma weak_of_avoids {A : Finset ℕ} {B : Finset A}
    (hB : ∀ e ∈ fourSupports A, ¬ e ⊆ B) :
    WeakSidon ((B.image Subtype.val : Finset ℕ) : Set ℕ) := by
  classical
  intro a ha b hb c hc d hd he
  by_contra hn
  have hab : a ≠ b := by tauto
  have hac : a ≠ c := by intro h; apply hn; omega
  have had : a ≠ d := by intro h; apply hn; omega
  have hbc : b ≠ c := by intro h; apply hn; omega
  have hbd : b ≠ d := by intro h; apply hn; omega
  have hcd : c ≠ d := by tauto
  obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
  obtain ⟨c', hc', rfl⟩ := mem_image.mp hc
  obtain ⟨d', hd', rfl⟩ := mem_image.mp hd
  have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
  have hac' : a' ≠ c' := fun h => hac (congrArg Subtype.val h)
  have had' : a' ≠ d' := fun h => had (congrArg Subtype.val h)
  have hbc' : b' ≠ c' := fun h => hbc (congrArg Subtype.val h)
  have hbd' : b' ≠ d' := fun h => hbd (congrArg Subtype.val h)
  have hcd' : c' ≠ d' := fun h => hcd (congrArg Subtype.val h)
  apply hB {a', c', b', d'}
  · apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _, a', c', b', d', rfl, he, ?_⟩, ?_⟩
    · intro h
      rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact hac' h
      · exact had' h
    · simp [hab', hac', had', hbc'.symm, hbd', hcd']
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption

/-- Alteration followed by constant-fraction weak-Sidon extraction.
There is no assumption of progression-freeness and no Behrend loss. -/
theorem finite_selection (A : Finset ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ C ⊆ A, IsSidon (C : Set ℕ) ∧
      (p * A.card - p ^ 4 * (fourSupports A).card) / 4 ≤ C.card := by
  classical
  have hn : ∀ e ∈ fourSupports A, e.Nonempty := by
    intro e he
    exact card_pos.mp (by rw [(mem_filter.mp he).2]; norm_num)
  obtain ⟨B, hB, hc⟩ := alteration_bound (fourSupports A) hn p hp hp1
  have hcost : (∑ e ∈ fourSupports A, p ^ e.card) = p ^ 4 * (fourSupports A).card := by
    calc
      _ = ∑ _e ∈ fourSupports A, p ^ 4 := by
        apply sum_congr rfl
        intro e he
        rw [(mem_filter.mp he).2]
      _ = _ := by simp [mul_comm]
  rw [hcost] at hc
  simp only [Fintype.card_coe] at hc
  obtain ⟨C, hC, hsidon, hcard⟩ := extract (B.image Subtype.val) (weak_of_avoids hB)
  have hBA : B.image Subtype.val ⊆ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    exact b.property
  have hBi : (B.image Subtype.val).card = B.card :=
    card_image_of_injective _ Subtype.val_injective
  rw [hBi] at hcard
  refine ⟨C, hC.trans hBA, hsidon, ?_⟩
  linarith

/-- The finite bound can be applied to any subset of a specified ambient set. -/
theorem finite_max_bound {A S : Finset ℕ} (hA : A ⊆ S)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (p * A.card - p ^ 4 * (fourSupports A).card) / 4 ≤
      (maxSidonSubsetCard S : ℝ) := by
  obtain ⟨C, hC, hs, hc⟩ := finite_selection A p hp hp1
  have hm : C.card ≤ maxSidonSubsetCard S :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr (hC.trans hA), hs⟩)
  exact hc.trans (by exact_mod_cast hm)

/-- Effective exponent accounting: the collision count beta and size alpha
produce exponent (4 alpha - beta)/3 when beta >= alpha. In particular, the
unrestricted square collision exponent two gives only exponent two thirds. -/
theorem power_count_bound {A S : Finset ℕ} (hA : A ⊆ S)
    (X α β : ℝ) (hX : 1 ≤ X) (hαβ : α ≤ β)
    (hsize : X ^ α ≤ A.card) (hcount : ((fourSupports A).card : ℝ) ≤ X ^ β) :
    (7 / 64 : ℝ) * X ^ ((4 * α - β) / 3) ≤ (maxSidonSubsetCard S : ℝ) := by
  have hX0 : 0 < X := by linarith
  let p : ℝ := (1 / 2) * X ^ ((α - β) / 3)
  let R : ℝ := X ^ ((4 * α - β) / 3)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    have hh := Real.rpow_le_one_of_one_le_of_nonpos hX
      (show (α - β) / 3 ≤ 0 by linarith)
    dsimp [p]
    linarith
  have hlead : R / 2 ≤ p * A.card := by
    calc
      _ = p * X ^ α := by
        dsimp [p, R]
        rw [mul_assoc, ← Real.rpow_add hX0]
        have he : (α - β) / 3 + α = (4 * α - β) / 3 := by ring
        rw [he]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsize hp
  have hcost : p ^ 4 * (fourSupports A).card ≤ R / 16 := by
    calc
      _ ≤ p ^ 4 * X ^ β := mul_le_mul_of_nonneg_left hcount (pow_nonneg hp _)
      _ = _ := by
        dsimp [p, R]
        rw [mul_pow, mul_assoc, ← Real.rpow_mul_natCast hX0.le,
          ← Real.rpow_add hX0]
        have he : (α - β) / 3 * (4 : ℕ) + β = (4 * α - β) / 3 := by push_cast; ring
        rw [he]
        norm_num
        ring
  have hh := finite_max_bound hA p hp hp1
  change (7 / 64 : ℝ) * R ≤ _
  linarith

/-- A converse finite estimate: a set much larger than its ambient maximum
Sidon cardinality must contain many four-entry supports, not just one. -/
theorem supersaturation {A S : Finset ℕ} (hA : A ⊆ S)
    (hM : 0 < (maxSidonSubsetCard S : ℝ))
    (hlarge : 8 * (maxSidonSubsetCard S : ℝ) ≤ A.card) :
    (A.card : ℝ) ^ 4 ≤ 1024 * (maxSidonSubsetCard S : ℝ) ^ 3 *
      (fourSupports A).card := by
  let M : ℝ := maxSidonSubsetCard S
  let m : ℝ := A.card
  let E : ℝ := (fourSupports A).card
  have hm : 0 < m := by dsimp [m]; linarith
  let p : ℝ := 8 * M / m
  have hp : 0 ≤ p := by dsimp [p, M, m]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one hm).mpr
    exact hlarge
  have hh := finite_max_bound hA p hp hp1
  have hpm : p * m = 8 * M := by dsimp [p]; field_simp
  change (p * m - p ^ 4 * E) / 4 ≤ M at hh
  have hcost : 4 * M ≤ p ^ 4 * E := by linarith only [hh, hpm]
  have hmul := mul_le_mul_of_nonneg_right hcost (pow_nonneg hm.le 4)
  have hcancel : p ^ 4 * E * m ^ 4 = (8 * M) ^ 4 * E := by
    calc
      _ = (p * m) ^ 4 * E := by ring
      _ = _ := by rw [hpm]
  rw [hcancel] at hmul
  change m ^ 4 ≤ 1024 * M ^ 3 * E
  have hh' : (4 * M) * m ^ 4 ≤ (4 * M) * (1024 * M ^ 3 * E) := by
    nlinarith only [hmul]
  exact (mul_le_mul_iff_right₀ (show 0 < 4 * M by dsimp [M]; positivity)).mp hh'

/-- A Sidon set has no four-entry collision supports. -/
theorem fourSupports_eq_empty {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    fourSupports A = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨_, a, b, c, d, _, heq, hnt⟩ := mem_filter.mp (mem_filter.mp he).1
  apply hnt
  simpa only [Subtype.ext_iff] using
    hA a.val a.property b.val b.property c.val c.property d.val d.property heq

/-- The quantitative missing hypothesis, expressed on square values.
It does not require the chosen set itself to be Sidon or AP-free. -/
def LowCollision : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∃ A ⊆ (Icc 1 N).image (fun n : ℕ => n ^ 2),
      (N : ℝ) ^ (1 - δ) ≤ A.card ∧
      ((fourSupports A).card : ℝ) ≤ (N : ℝ) ^ (1 + δ)

/-- Four-support saving to exponent one suffices for the original conjecture. -/
theorem near_linear_of_lowCollision (h : LowCollision) :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) := by
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ht (r : ℝ) (hr : 0 < r) :
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-r)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) (ht δ hδ)
  have hslack := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 8)
    (ht (2 * δ) (by positivity))
  filter_upwards [h δ hδ, hsmall, hslack, eventually_ge_atTop 1] with N hN hsmall hslack hN1
  obtain ⟨A, hA, hAc, hEc⟩ := hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  let p : ℝ := (N : ℝ) ^ (-δ)
  let S : ℝ := (N : ℝ) ^ (1 - 2 * δ)
  have hp : 0 ≤ p := Real.rpow_nonneg hNpos.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  have hS : 0 ≤ S := Real.rpow_nonneg hNpos.le _
  have hb := finite_max_bound hA p hp hp1
  have hlead : S ≤ p * A.card := by
    calc
      _ = p * (N : ℝ) ^ (1 - δ) := by
        dsimp [S, p]
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAc hp
  have hcost : p ^ 4 * (fourSupports A).card ≤ S * (N : ℝ) ^ (-δ) := by
    calc
      _ ≤ p ^ 4 * (N : ℝ) ^ (1 + δ) :=
        mul_le_mul_of_nonneg_left hEc (pow_nonneg hp _)
      _ = _ := by
        dsimp [p, S]
        rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_add hNpos,
          ← Real.rpow_add hNpos]
        congr 1
        ring
  have htarget : (N : ℝ) ^ (1 - ε) = S * (N : ℝ) ^ (-(2 * δ)) := by
    dsimp [S, δ]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have he := mul_le_mul_of_nonneg_left hsmall hS
  have hs := mul_le_mul_of_nonneg_left hslack hS
  rw [htarget]
  nlinarith only [hb, hlead, hcost, he, hs]

/-- The low-collision formulation is equivalent to the original assertion,
not a proof of it. The reverse implication takes a maximum Sidon subset. -/
theorem lowCollision_iff_near_linear : LowCollision ↔
    (∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ)) := by
  classical
  refine ⟨near_linear_of_lowCollision, ?_⟩
  intro h δ hδ
  filter_upwards [h δ hδ] with N hN
  let S := (Icc 1 N).image (fun n : ℕ => n ^ 2)
  have hne : (S.powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))).Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨by simp, ?_⟩⟩
    intro a ha
    simp at ha
  obtain ⟨A, hA, he⟩ := exists_mem_eq_sup _ hne Finset.card
  obtain ⟨hAS, hsidon⟩ := mem_filter.mp hA
  refine ⟨A, mem_powerset.mp hAS, ?_, ?_⟩
  · change (N : ℝ) ^ (1 - δ) ≤ (maxSidonSubsetCard S : ℝ) at hN
    simpa only [maxSidonSubsetCard, he] using hN
  · rw [fourSupports_eq_empty hsidon]
    simp only [card_empty, Nat.cast_zero]
    positivity

#print axioms finite_selection
#print axioms finite_max_bound
#print axioms power_count_bound
#print axioms supersaturation
#print axioms fourSupports_eq_empty
#print axioms near_linear_of_lowCollision
#print axioms lowCollision_iff_near_linear
end Erdos773.LowCollisionSelection
