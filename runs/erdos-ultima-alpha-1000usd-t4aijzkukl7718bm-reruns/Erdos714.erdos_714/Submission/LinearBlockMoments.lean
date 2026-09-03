import Submission.LinearBlockCounts

/-! First and second moments of complementary graph-of-linear-map blocks. -/
noncomputable section
open Finset Classical Module
set_option maxHeartbeats 2000000
namespace Erdos714LinearBlocks
variable {F V C : Type*} [Field F] [Fintype F]
  [AddCommGroup V] [Module F V] [Fintype V] [FiniteDimensional F V] [Fintype C]

local instance : Fintype (End (F := F) (V := V)) := endFintype
local instance : Fintype (Module.Dual F V) := dualFintype

/-- Distinct indexed points never lie on the same scalar ray. -/
def RayInjective {U : Type*} [SMul F U] (R : C → U) : Prop :=
  ∀ (c d : C) (a : F), R c = a • R d → c = d

lemma ray_independent {U : Type*} [AddCommGroup U] [Module F U]
    (R : C → U) (hR : RayInjective (F := F) R) (c d : C) (hcd : c ≠ d)
    (hd : R d ≠ 0) (s t : F) (h : s • R c+t • R d = 0) : s = 0 ∧ t = 0 := by
  by_cases hs : s = 0
  · subst s
    have ht : t • R d = 0 := by simpa using h
    exact ⟨rfl, (smul_eq_zero.mp ht).resolve_right hd⟩
  · exfalso
    apply hcd
    apply hR c d (s⁻¹*(-t))
    calc
      R c = s⁻¹ • (s • R c) := by simp [smul_smul, hs]
      _ = s⁻¹ • ((-t) • R d) := by congr 1; simpa only [neg_smul] using eq_neg_of_add_eq_zero_left h
      _ = _ := by rw [smul_smul]

def rows (R : C → V × V) (f : End (F := F) (V := V)) : Finset C :=
  univ.filter (fun c => f (R c).1 = (R c).2)

def columns (R : C → Module.Dual F V × Module.Dual F V)
    (f : End (F := F) (V := V)) : Finset C :=
  univ.filter (fun c => (R c).1.comp f = (R c).2)

lemma row_point_coverage (hd : finrank F V = 3) (R : C → V × V)
    (hR : ∀ c, (R c).1 ≠ 0) (c : C) :
    (univ.filter (fun f => c ∈ rows (F := F) R f)).card = Fintype.card F^6 := by
  simpa only [rows, mem_filter, mem_univ, true_and] using point_count hd (R c).1 (R c).2 (hR c)

lemma row_pair_coverage (hd : finrank F V = 3) (R : C → V × V)
    (hR : RayInjective (F := F) R) (hn : ∀ c, (R c).1 ≠ 0) (c d : C) (hcd : c ≠ d) :
    (univ.filter (fun f => c ∈ rows (F := F) R f ∧ d ∈ rows (F := F) R f)).card ≤ Fintype.card F^3 := by
  by_cases hex : ∃ f : End (F := F) (V := V), f (R c).1 = (R c).2 ∧ f (R d).1 = (R d).2
  · obtain ⟨f, hc, he⟩ := hex
    have hi (s t : F) (h : s • (R c).1+t • (R d).1 = 0) : s = 0 ∧ t = 0 := by
      apply ray_independent R hR c d hcd (fun hz => hn d (congrArg Prod.fst hz)) s t
      apply Prod.ext h
      have hf := congrArg f h
      simpa only [map_add, map_smul, map_zero, hc, he] using hf
    have h := two_point_count hd (R c).1 (R d).1 (R c).2 (R d).2 hi
    simpa only [rows, mem_filter, mem_univ, true_and] using h.le
  · have he : (univ.filter (fun f => c ∈ rows (F := F) R f ∧ d ∈ rows (F := F) R f)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro f hf
      simp only [mem_filter, mem_univ, true_and, rows] at hf
      exact hex ⟨f, hf⟩
    rw [he, card_empty]
    omega

lemma column_point_coverage (hd : finrank F V = 3)
    (R : C → Module.Dual F V × Module.Dual F V) (hn : ∀ c, (R c).1 ≠ 0) (c : C) :
    (univ.filter (fun f => c ∈ columns R f)).card = Fintype.card F^6 := by
  simpa only [columns, mem_filter, mem_univ, true_and] using dual_point_count hd _ _ (hn c)

lemma column_pair_coverage (hd : finrank F V = 3)
    (R : C → Module.Dual F V × Module.Dual F V) (hR : RayInjective (F := F) R)
    (hn : ∀ c, (R c).1 ≠ 0) (c d : C) (hcd : c ≠ d) :
    (univ.filter (fun f => c ∈ columns R f ∧ d ∈ columns R f)).card ≤ Fintype.card F^3 := by
  by_cases hex : ∃ f : End (F := F) (V := V), (R c).1.comp f = (R c).2 ∧ (R d).1.comp f = (R d).2
  · obtain ⟨f, hc, he⟩ := hex
    have hi (s t : F) (h : s • (R c).1+t • (R d).1 = 0) : s = 0 ∧ t = 0 := by
      apply ray_independent R hR c d hcd (fun hz => hn d (congrArg Prod.fst hz)) s t
      apply Prod.ext h
      have hf := congrArg f.dualMap h
      rw [map_add, map_smul, map_smul, map_zero] at hf
      change s • ((R c).1.comp f)+t • ((R d).1.comp f) = 0 at hf
      simpa only [hc, he] using hf
    have h := dual_two_point_count hd (R c).1 (R d).1 (R c).2 (R d).2 hi
    simpa only [columns, mem_filter, mem_univ, true_and] using h.le
  · have he : (univ.filter (fun f => c ∈ columns R f ∧ d ∈ columns R f)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro f hf
      simp only [mem_filter, mem_univ, true_and, columns] at hf
      exact hex ⟨f, hf⟩
    rw [he, card_empty]
    omega

/-- Exact dimension, and therefore exact number of linear-map blocks. -/
lemma block_count (hd : finrank F V = 3) :
    Fintype.card (End (F := F) (V := V)) = Fintype.card F^9 := by
  rw [Module.card_eq_pow_finrank (K := F)]
  simp [Module.finrank_linearMap, hd]

lemma row_moments (hd : finrank F V = 3) (R : C → V × V)
    (hR : RayInjective (F := F) R) (hn : ∀ c, (R c).1 ≠ 0) :
    (∑ f, (rows (F := F) R f).card) ≤ Fintype.card F^6*Fintype.card C ∧
    (∑ f, (rows (F := F) R f).card^2) ≤ Fintype.card F^6*Fintype.card C+
      Fintype.card F^3*Fintype.card C^2 := by
  exact ⟨Erdos714BlockMoment.first_moment _ _ (fun c => (row_point_coverage hd R hn c).le),
    Erdos714BlockMoment.second_moment _ _ _ (fun c => (row_point_coverage hd R hn c).le)
      (row_pair_coverage hd R hR hn)⟩

lemma column_moments (hd : finrank F V = 3)
    (R : C → Module.Dual F V × Module.Dual F V) (hR : RayInjective (F := F) R)
    (hn : ∀ c, (R c).1 ≠ 0) :
    (∑ f, (columns R f).card) ≤ Fintype.card F^6*Fintype.card C ∧
    (∑ f, (columns R f).card^2) ≤ Fintype.card F^6*Fintype.card C+
      Fintype.card F^3*Fintype.card C^2 := by
  exact ⟨Erdos714BlockMoment.first_moment _ _ (fun c => (column_point_coverage hd R hn c).le),
    Erdos714BlockMoment.second_moment _ _ _ (fun c => (column_point_coverage hd R hn c).le)
      (column_pair_coverage hd R hR hn)⟩

#print axioms row_pair_coverage
#print axioms column_pair_coverage
#print axioms row_moments
#print axioms column_moments
#print axioms block_count
end Erdos714LinearBlocks
