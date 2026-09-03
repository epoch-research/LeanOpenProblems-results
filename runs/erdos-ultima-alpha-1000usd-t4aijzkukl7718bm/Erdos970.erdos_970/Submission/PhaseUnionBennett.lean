import Submission.PopulationLowCountBennett

/-! Exact core-tail decomposition of low-count probabilities and an averaged
conditional Bennett bound. The nonlinear average remains explicit. -/
namespace Erdos970.GapAverages
open Finset Real Erdos970.Resampling

/-- Join two residue vectors; on an intersection the first vector takes priority. -/
def joinPhase (P R : Finset ℕ) (r : Phase P) (s : Phase R) : Phase (P ∪ R) :=
  fun p => if hp : p.val ∈ P then r ⟨p.val, hp⟩
    else s ⟨p.val, (mem_union.mp p.property).resolve_left hp⟩

lemma joinPhase_left (P R : Finset ℕ) (r : Phase P) (s : Phase R) (p : P) :
    joinPhase P R r s ⟨p.val, mem_union_left _ p.property⟩ = r p := by
  simp [joinPhase, p.property]

lemma joinPhase_right (P R : Finset ℕ) (hdis : Disjoint P R)
    (r : Phase P) (s : Phase R) (p : R) :
    joinPhase P R r s ⟨p.val, mem_union_right _ p.property⟩ = s p := by
  have hp : p.val ∉ P := fun hp => (disjoint_left.mp hdis) hp p.property
  simp [joinPhase, hp]

/-- Independent phase spaces for disjoint prime sets form the full phase space. -/
def unionPhaseEquiv (P R : Finset ℕ) (hdis : Disjoint P R) :
    (Phase P × Phase R) ≃ Phase (P ∪ R) where
  toFun v := joinPhase P R v.1 v.2
  invFun r := (fun p => r ⟨p.val, mem_union_left _ p.property⟩,
    fun p => r ⟨p.val, mem_union_right _ p.property⟩)
  left_inv v := by
    rcases v with ⟨r, s⟩
    apply Prod.ext
    · funext p
      exact joinPhase_left P R r s p
    · funext p
      exact joinPhase_right P R hdis r s p
  right_inv r := by
    funext p
    dsimp only [joinPhase]
    split_ifs <;> rfl

lemma phaseMean_union (P R : Finset ℕ) (hdis : Disjoint P R)
    (f : Phase (P ∪ R) → ℝ) :
    phaseMean (P ∪ R) f = phaseMean P (fun r => phaseMean R (fun s => f (joinPhase P R r s))) := by
  have hs : (∑ v : Phase P × Phase R, f (joinPhase P R v.1 v.2)) =
      ∑ r : Phase (P ∪ R), f r := by
    apply Fintype.sum_equiv (unionPhaseEquiv P R hdis)
    intro v
    rfl
  have hd : (∏ p : ↥(P ∪ R), (p.val : ℝ)) =
      (∏ p : P, (p.val : ℝ)) * ∏ p : R, (p.val : ℝ) := by
    rw [prod_coe_sort (P ∪ R) (fun p : ℕ => (p : ℝ)), prod_union hdis,
      prod_coe_sort P (fun p : ℕ => (p : ℝ)), prod_coe_sort R (fun p : ℕ => (p : ℝ))]
  unfold phaseMean
  rw [hd, ← hs, Fintype.sum_prod_type, ← sum_div]
  ring

lemma populationSurvivors_union (S P R : Finset ℕ) (hdis : Disjoint P R)
    (r : Phase P) (s : Phase R) :
    populationSurvivors S (P ∪ R) (joinPhase P R r s) =
      populationSurvivors (populationSurvivors S P r) R s := by
  ext x
  simp only [populationSurvivors, mem_filter]
  constructor
  · rintro ⟨hx, ha⟩
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · intro p hp
      have hh := ha ⟨p.val, mem_union_left _ p.property⟩
      rw [joinPhase_left] at hh
      exact hh hp
    · intro p hp
      have hh := ha ⟨p.val, mem_union_right _ p.property⟩
      rw [joinPhase_right P R hdis] at hh
      exact hh hp
  · rintro ⟨⟨hx, hP⟩, hR⟩
    refine ⟨hx, ?_⟩
    intro p hp
    rcases mem_union.mp p.property with hpP | hpR
    · have he : joinPhase P R r s p = r ⟨p.val, hpP⟩ := by simp [joinPhase, hpP]
      rw [he] at hp
      exact hP ⟨p.val, hpP⟩ hp
    · have he : joinPhase P R r s p = s ⟨p.val, hpR⟩ := by
        exact joinPhase_right P R hdis r s ⟨p.val, hpR⟩
      rw [he] at hp
      exact hR ⟨p.val, hpR⟩ hp

lemma lowCountFraction_union (P R : Finset ℕ) (hdis : Disjoint P R) (m : ℕ) (b : ℝ) :
    lowCountFraction (P ∪ R) m b =
      phaseMean P (fun r => populationLowCountFraction (populationSurvivors (range m) P r) R b) := by
  unfold lowCountFraction
  rw [phaseMean_union P R hdis]
  have he (r : Phase P) (s : Phase R) : intervalCount (P ∪ R) m (joinPhase P R r s) =
      ((populationSurvivors (populationSurvivors (range m) P r) R s).card : ℝ) := by
    rw [← populationSurvivors_union _ _ _ hdis, populationSurvivors_card]
    rfl
  simp_rw [he]
  rfl

lemma populationLowCountFraction_le_one (S P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (b : ℝ) :
    populationLowCountFraction S P b ≤ 1 := by
  have hh := phaseMean_mono P (f := fun r => if ((populationSurvivors S P r).card : ℝ) ≤ b then 1 else 0)
    (g := fun _ => 1) (fun r => by dsimp only; split_ifs <;> norm_num)
  rwa [phaseMean_const P hP] at hh

/-- The rigorous averaged bound: the exponential is INSIDE the core average.
Parameters and caps may depend on the old phase. The minimum with one keeps
bad old phases from contributing a spurious exponentially large upper bound. -/
theorem lowCountFraction_union_bennett (P R : Finset ℕ) (hdis : Disjoint P R)
    (hR : ∀ p ∈ R, p.Prime) (m : ℕ) (b : ℝ)
    (t : Phase P → ℝ) (ht : ∀ r, 0 ≤ t r) (B : Phase P → R → ℝ)
    (hupper : ∀ (r : Phase P) (p : R) (a : Fin p.val),
      centeredHits (populationSurvivors (range m) P r) p.val a ≤ B r p) :
    lowCountFraction (P ∪ R) m b ≤ phaseMean P (fun r =>
      let S := populationSurvivors (range m) P r
      min 1 (exp (-t r * ((S.card : ℝ) * (1 - ∑ p : R, 1 / (p.val : ℝ)) - b) +
        ∑ p : R, bennettFactor (t r) (B r p) * classVariance S p.val))) := by
  rw [lowCountFraction_union P R hdis]
  apply phaseMean_mono
  intro r
  apply le_min
  · exact populationLowCountFraction_le_one _ R hR b
  · exact populationLowCountFraction_bennett _ R hR b (t r) (ht r) (B r) (hupper r)

/-- A finite sufficient criterion combining conditional Bennett averaging
with the low-count cylinder lower bound. The retained set Q need not equal
the analysis core P. Its nonlinear average hypothesis is not asserted here. -/
theorem survivor_of_averaged_bennett_cylinder (P R Q : Finset ℕ)
    (hdis : Disjoint P R) (hQ : Q ⊆ P ∪ R)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime)
    (m : ℕ) (b : ℝ) (t : Phase P → ℝ) (ht : ∀ r, 0 ≤ t r)
    (B : Phase P → R → ℝ)
    (hupper : ∀ (r : Phase P) (p : R) (a : Fin p.val),
      centeredHits (populationSurvivors (range m) P r) p.val a ≤ B r p)
    (hbudget : deletionBudget (P ∪ R) Q m ≤ b)
    (havg : phaseMean P (fun r =>
      let S := populationSurvivors (range m) P r
      min 1 (exp (-t r * ((S.card : ℝ) * (1 - ∑ p : R, 1 / (p.val : ℝ)) - b) +
        ∑ p : R, bennettFactor (t r) (B r p) * classVariance S p.val))) <
      ∏ p ∈ Q, (p : ℝ)⁻¹) (a : ℕ → ℕ) :
    ∃ x < m, ∀ p ∈ P ∪ R, ¬x ≡ a p [MOD p] := by
  classical
  have hPR (p : ℕ) (hp : p ∈ P ∪ R) : p.Prime := by
    rcases mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hR p hp
  by_contra hbad
  push_neg at hbad
  let r : Phase (P ∪ R) := fun p => ⟨a p.val % p.val,
    Nat.mod_lt _ (hPR p.val p.property).pos⟩
  have hr : intervalCount (P ∪ R) m r = 0 := by
    apply count_zero_of_cover
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hbad x hx
    exact ⟨⟨p, hp⟩, hxp⟩
  have hl := reciprocal_le_lowCountFraction (P ∪ R) Q hQ hPR m b hbudget r hr
  have hu := lowCountFraction_union_bennett P R hdis hR m b t ht B hupper
  exact havg.not_ge (hl.trans hu)

#print axioms survivor_of_averaged_bennett_cylinder
#print axioms phaseMean_union
#print axioms lowCountFraction_union
#print axioms lowCountFraction_union_bennett
end Erdos970.GapAverages
