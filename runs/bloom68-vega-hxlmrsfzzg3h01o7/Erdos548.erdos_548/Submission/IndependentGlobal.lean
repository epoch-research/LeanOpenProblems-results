import FormalConjecturesUtil

/-!
# Kernel-checked core of an independent global Erdős–Sós attempt

This file does not import `Submission.Spec`, does not use its declarations, and
DOES NOT prove Erdős–Sós. The full mathematical report is
`independent_global_attempt.md`.

Proved here: a finite weighted collision-cover bound; its injective-map interface;
a two-vertex degree bound and the single-exceptional-target-vertex reduction;
and arithmetic for an obstruction to the proposed first-moment bridge.

The locally injective sampling/projection identities and the infinite obstruction
family are proved on paper in the report, not asserted as formal theorems here.
-/

open SimpleGraph
open scoped BigOperators Classical

namespace Erdos548.IndependentGlobal

section FiniteWeights

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

/-- A finite weighted union bound, allowing the total mass to be less than one. -/
theorem weighted_cover_bound (w : Ω → ℚ) (good : Ω → Prop)
    (bad : I → Ω → Prop) (hw : ∀ ω, 0 ≤ w ω)
    (hcover : ∀ ω, ¬ good ω → ∃ i, bad i ω) :
    (∑ ω, w ω) ≤ (∑ ω, if good ω then w ω else 0) +
      ∑ i, ∑ ω, if bad i ω then w ω else 0 := by
  classical
  have hterm (ω : Ω) (i : I) : 0 ≤ (if bad i ω then w ω else 0) := by
    split_ifs <;> simp_all
  have hpoint (ω : Ω) : w ω ≤
      (if good ω then w ω else 0) + ∑ i, if bad i ω then w ω else 0 := by
    by_cases hg : good ω
    · have hs : 0 ≤ ∑ i, if bad i ω then w ω else 0 :=
        Finset.sum_nonneg (fun i _ => hterm ω i)
      simpa [hg] using (le_add_of_nonneg_right (a := w ω) hs)
    · obtain ⟨i, hi⟩ := hcover ω hg
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun j => if bad j ω then w ω else 0)
        (fun j _ => hterm ω j) (Finset.mem_univ i)
      simpa [hg, hi] using hs
  calc
    (∑ ω, w ω) ≤ ∑ ω,
        ((if good ω then w ω else 0) + ∑ i, if bad i ω then w ω else 0) :=
      Finset.sum_le_sum (fun ω _ => hpoint ω)
    _ = (∑ ω, if good ω then w ω else 0) +
        ∑ i, ∑ ω, if bad i ω then w ω else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]

/-- Replacing each actual collision mass by a proved upper bound is safe. -/
theorem weighted_good_lower_bound (w : Ω → ℚ) (good : Ω → Prop)
    (bad : I → Ω → Prop) (b : I → ℚ) (hw : ∀ ω, 0 ≤ w ω)
    (hcover : ∀ ω, ¬ good ω → ∃ i, bad i ω)
    (hbudget : ∀ i, (∑ ω, if bad i ω then w ω else 0) ≤ b i) :
    (∑ ω, w ω) - (∑ i, b i) ≤ ∑ ω, if good ω then w ω else 0 := by
  classical
  have hc := weighted_cover_bound w good bad hw hcover
  have hb : (∑ i, ∑ ω, if bad i ω then w ω else 0) ≤ ∑ i, b i :=
    Finset.sum_le_sum (fun i _ => hbudget i)
  linarith

/-- A strict mass-versus-collision budget supplies a positive-weight good state. -/
theorem exists_good_of_budget_lt (w : Ω → ℚ) (good : Ω → Prop)
    (bad : I → Ω → Prop) (b : I → ℚ) (hw : ∀ ω, 0 ≤ w ω)
    (hcover : ∀ ω, ¬ good ω → ∃ i, bad i ω)
    (hbudget : ∀ i, (∑ ω, if bad i ω then w ω else 0) ≤ b i)
    (hstrict : (∑ i, b i) < ∑ ω, w ω) :
    ∃ ω, good ω ∧ 0 < w ω := by
  classical
  have hl := weighted_good_lower_bound w good bad b hw hcover hbudget
  by_contra! h
  have hz : (∑ ω, if good ω then w ω else 0) ≤ 0 := by
    apply Finset.sum_nonpos
    intro ω _
    by_cases hg : good ω
    · simpa [hg] using h ω hg
    · simp [hg]
  linarith

end FiniteWeights

/-- Exactly one orientation for each unordered pair of distinct target labels. -/
abbrev IncreasingPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Noninjectivity has an increasing-pair witness; no factor of two is introduced. -/
theorem exists_increasing_collision {n : ℕ} {V : Type*} (f : Fin n → V)
    (h : ¬ Function.Injective f) :
    ∃ p : IncreasingPair n, f p.1.1 = f p.1.2 := by
  classical
  by_contra hn
  apply h
  intro x y hxy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hn ⟨⟨(x, y), hlt⟩, hxy⟩
  · exact hn ⟨⟨(y, x), hgt⟩, hxy.symm⟩

/-- A graph-independent interface for the return-walk collision argument. -/
theorem exists_injective_of_pair_budget {Ω V : Type*} [Fintype Ω] {n : ℕ}
    (f : Ω → Fin n → V) (w : Ω → ℚ) (b : IncreasingPair n → ℚ)
    (hw : ∀ ω, 0 ≤ w ω)
    (hbudget : ∀ p : IncreasingPair n,
      (∑ ω, if f ω p.1.1 = f ω p.1.2 then w ω else 0) ≤ b p)
    (hstrict : (∑ p, b p) < ∑ ω, w ω) :
    ∃ ω, Function.Injective (f ω) ∧ 0 < w ω := by
  classical
  exact exists_good_of_budget_lt w (fun ω => Function.Injective (f ω))
    (fun p ω => f ω p.1.1 = f ω p.1.2) b hw
    (fun ω h => exists_increasing_collision (f ω) h) hbudget hstrict

/-- The budget interface gives ordinary containment, not induced containment. -/
theorem isContained_of_hom_pair_budget {Ω V : Type*} [Fintype Ω] {n : ℕ}
    (T : SimpleGraph (Fin n)) (G : SimpleGraph V) (f : Ω → T →g G)
    (w : Ω → ℚ) (b : IncreasingPair n → ℚ) (hw : ∀ ω, 0 ≤ w ω)
    (hbudget : ∀ p : IncreasingPair n,
      (∑ ω, if f ω p.1.1 = f ω p.1.2 then w ω else 0) ≤ b p)
    (hstrict : (∑ p, b p) < ∑ ω, w ω) : T.IsContained G := by
  obtain ⟨ω, hinj, _⟩ := exists_injective_of_pair_budget (fun ω => f ω) w b hw hbudget hstrict
  exact ⟨{ toHom := f ω, injective' := hinj }⟩

section DegreeBound

variable {A : Type*} [Fintype A] (T : SimpleGraph A) [DecidableRel T.Adj]

/-- Two distinct vertices share at most one incident edge. No tree hypothesis is needed. -/
theorem degree_add_degree_le_edges_add_one {u v : A} (hne : u ≠ v) :
    T.degree u + T.degree v ≤ T.edgeFinset.card + 1 := by
  classical
  have hu : T.incidenceFinset u ∪ T.incidenceFinset v ⊆ T.edgeFinset :=
    Finset.union_subset (T.incidenceFinset_subset u) (T.incidenceFinset_subset v)
  have hi : T.incidenceFinset u ∩ T.incidenceFinset v ⊆ {s(u, v)} := by
    intro e he
    rcases Finset.mem_inter.mp he with ⟨heu, hev⟩
    apply Finset.mem_singleton.mpr
    apply Set.mem_singleton_iff.mp
    apply T.incidenceSet_inter_incidenceSet_subset hne
    exact ⟨by simpa using heu, by simpa using hev⟩
  have huc := Finset.card_le_card hu
  have hic : (T.incidenceFinset u ∩ T.incidenceFinset v).card ≤ 1 := by
    simpa using Finset.card_le_card hi
  have hid := Finset.card_union_add_card_inter (T.incidenceFinset u) (T.incidenceFinset v)
  rw [T.card_incidenceFinset_eq_degree, T.card_incidenceFinset_eq_degree] at hid
  omega

/-- Only a maximum-degree target vertex can require more than ceil(k/2) neighbors. -/
theorem other_tree_degree_le_half {k : ℕ} (hT : T.IsTree)
    (hcard : Fintype.card A = k + 1) (a : A)
    (hmax : ∀ x, T.degree x ≤ T.degree a) :
    ∀ x, x ≠ a → T.degree x ≤ (k + 1) / 2 := by
  intro x hxa
  have he : T.edgeFinset.card = k := by
    have := hT.card_edgeFinset
    omega
  have hb := degree_add_degree_le_edges_add_one T hxa
  rw [he] at hb
  have hm := hmax x
  omega

end DegreeBound

/-- Exact arithmetic for the infinite-family pair-collision obstruction. -/
theorem pair_collision_lower_bound_gt_one (d : ℕ) (hd : 5 ≤ d) :
    (1 : ℚ) < ((d : ℚ) - 2) ^ 2 / (2 * ((d : ℚ) - 1)) := by
  have hq : (5 : ℚ) ≤ d := by exact_mod_cast hd
  have hden : 0 < 2 * ((d : ℚ) - 1) := by linarith
  apply (lt_div_iff₀ hden).mpr
  have hp : 0 ≤ ((d : ℚ) - 5) * ((d : ℚ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

#print axioms weighted_cover_bound
#print axioms weighted_good_lower_bound
#print axioms exists_good_of_budget_lt
#print axioms exists_increasing_collision
#print axioms exists_injective_of_pair_budget
#print axioms isContained_of_hom_pair_budget
#print axioms degree_add_degree_le_edges_add_one
#print axioms other_tree_degree_le_half
#print axioms pair_collision_lower_bound_gt_one

end Erdos548.IndependentGlobal
