import Submission.GraphCoreIrreducible

/-! Quantitative reduction to branch-cut-irreducible minimal cores.
The bound on the irreducible cores remains an explicit, unproved hypothesis. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.IrreducibleBound
open GraphCoreIrreducible GraphTwoCut GraphBranchCount GraphIsoCore Critical EvenCore Rigidity
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma branches_le_card (G : SimpleGraph V) : branches G ≤ Fintype.card V := by
  unfold branches
  calc
    _ ≤ ∑ _v : V, 1 := Finset.sum_le_sum (fun v _ => by split_ifs <;> omega)
    _ = _ := by simp

lemma cut_of_not_irreducible (G : SimpleGraph V) (hi : ¬ BranchCutIrreducible G) :
    ∃ S : Set V, (crossPairs G S).card = 2 ∧
      (∃ x : S, 2 < G.degree x.val) ∧ (∃ x : (Sᶜ : Set V), 2 < G.degree x.val) := by
  unfold BranchCutIrreducible at hi
  push_neg at hi
  exact hi

lemma closures_branch_sum (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d)) :
    branches (closure (G.induce S) a b) + branches (closure (G.induce Sᶜ) c d) = branches G := by
  exact (branches_join _ _ hsep).symm.trans (branches_iso (partitionIso G S a b c d hcut))

lemma closure_sizes (S : Set V) :
    Fintype.card (S ⊕ Bool) + Fintype.card ((Sᶜ : Set V) ⊕ Bool) = Fintype.card V + 4 := by
  have h := Fintype.card_congr (Equiv.Set.sumCompl S)
  simp only [Fintype.card_sum,Fintype.card_bool] at h ⊢
  omega

lemma closures_branches_pos (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d))
    (hL : ∃ x : S, 2 < G.degree x.val) (hR : ∃ x : (Sᶜ : Set V), 2 < G.degree x.val) :
    0 < branches (closure (G.induce S) a b) ∧ 0 < branches (closure (G.induce Sᶜ) c d) := by
  constructor
  · rw [partition_branches_left G S a b c d hsep hcut]
    obtain ⟨x,hx⟩ := hL
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x,Finset.mem_univ _,by simp [hx]⟩
  · rw [partition_branches_right G S a b c d hsep hcut]
    obtain ⟨x,hx⟩ := hR
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x,Finset.mem_univ _,by simp [hx]⟩

/-- The subtraction makes this potential additive across a nontrivial two-cut. -/
noncomputable def potential (G : SimpleGraph V) : ℕ := Fintype.card V + 4 * branches G - 4

lemma potential_add (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d))
    (hL : 0 < branches (closure (G.induce S) a b))
    (hR : 0 < branches (closure (G.induce Sᶜ) c d)) :
    potential (closure (G.induce S) a b) + potential (closure (G.induce Sᶜ) c d) = potential G := by
  have hb := closures_branch_sum G S a b c d hsep hcut
  have hs := closure_sizes S
  unfold potential
  omega

lemma minimal_potential_bound (C : ℕ)
    (hcore : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      (∀ x, Even (R.degree x)) → EvenMinimal R → BranchCutIrreducible R →
        number R ≤ C * Fintype.card W) :
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      (∀ x, Even (R.degree x)) → EvenMinimal R → 0 < branches R →
        number R ≤ C * potential R + 1 := by
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      branches R = n → (∀ x, Even (R.degree x)) → EvenMinimal R → 0 < branches R →
        number R ≤ C * potential R + 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ R hn he hm hbpos
      by_cases hi : BranchCutIrreducible R
      · have hb := hcore R he hm hi
        have hpot : Fintype.card W ≤ potential R := by unfold potential; omega
        exact hb.trans ((Nat.mul_le_mul_left C hpot).trans (Nat.le_add_right _ _))
      · obtain ⟨S,hc,hL,hR⟩ := cut_of_not_irreducible R hi
        obtain ⟨a,b,c,d,hsep,hcut⟩ := exists_cut_endpoints R S hc
        obtain ⟨heL,heR⟩ := partition_closures_even R S a b c d hsep hcut he
        obtain ⟨hmL,hmR⟩ := (minimal_two_edge_cut_iff R S a b c d hsep hcut he).mp hm
        obtain ⟨hbL,hbR⟩ := closures_branches_pos R S a b c d hsep hcut hL hR
        have hsum := closures_branch_sum R S a b c d hsep hcut
        have hltL : branches (closure (R.induce S) a b) < n := by omega
        have hltR : branches (closure (R.induce Sᶜ) c d) < n := by omega
        have hnumL := ih _ hltL (closure (R.induce S) a b) rfl heL hmL hbL
        have hnumR := ih _ hltR (closure (R.induce Sᶜ) c d) rfl heR hmR hbR
        have hnR := number_two_edge_cut R S a b c d hsep hcut he
        have hp := potential_add R S a b c d hsep hcut hbL hbR
        have hmul : C * potential (closure (R.induce S) a b) +
            C * potential (closure (R.induce Sᶜ) c d) = C * potential R := by rw [← Nat.mul_add,hp]
        omega
  intro W _ _ R he hm hb
  exact main _ R rfl he hm hb

lemma minimal_linear_bound (C : ℕ) (hC : 1 ≤ C)
    (hcore : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      (∀ x, Even (R.degree x)) → EvenMinimal R → BranchCutIrreducible R →
        number R ≤ C * Fintype.card W)
    (G : SimpleGraph V) (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) :
    number G ≤ (5 * C) * Fintype.card V := by
  by_cases hi : BranchCutIrreducible G
  · have hb := hcore G he hm hi
    have hc : C ≤ 5 * C := by omega
    exact hb.trans (Nat.mul_le_mul_right _ hc)
  · obtain ⟨S,hc,hL,hR⟩ := cut_of_not_irreducible G hi
    obtain ⟨a,b,c,d,hsep,hcut⟩ := exists_cut_endpoints G S hc
    obtain ⟨hbL,hbR⟩ := closures_branches_pos G S a b c d hsep hcut hL hR
    have hsum := closures_branch_sum G S a b c d hsep hcut
    have hbpos : 0 < branches G := by omega
    have hp := minimal_potential_bound C hcore G he hm hbpos
    have hbcard := branches_le_card G
    have hpot : potential G + 1 ≤ 5 * Fintype.card V := by unfold potential; omega
    calc
      number G ≤ C * potential G + 1 := hp
      _ ≤ C * potential G + C := Nat.add_le_add_left hC _
      _ = C * (potential G + 1) := by ring
      _ ≤ C * (5 * Fintype.card V) := Nat.mul_le_mul_left C hpot
      _ = (5 * C) * Fintype.card V := by ring

lemma even_linear_bound (C : ℕ) (hC : 1 ≤ C)
    (hcore : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      (∀ x, Even (R.degree x)) → EvenMinimal R → BranchCutIrreducible R →
        number R ≤ C * Fintype.card W)
    (G : SimpleGraph V) (he : ∀ x, Even (G.degree x)) :
    number G ≤ (5 * C) * Fintype.card V := by
  obtain ⟨R,_,hR,hn,hm,_⟩ := exists_even_minimal_core G he
  have hR' : ∀ x, Even (R.degree x) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hR
  rw [← hn]
  exact minimal_linear_bound C hC hcore R hR' hm

lemma asymptotic_of_irreducible_core_bound (C : ℕ) (hC : 1 ≤ C)
    (hcore : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      (∀ x, Even (R.degree x)) → EvenMinimal R → BranchCutIrreducible R →
        number R ≤ C * Fintype.card W) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_even_cycle_uniform.mpr
  refine ⟨5 * C,?_⟩
  intro W _ _ R hR
  obtain ⟨D,hD,hdec,hcard⟩ := minimum_cycles hR
  refine ⟨D,hD,hdec,?_⟩
  have hn := even_linear_bound C hC hcore R hR
  have hc : D.card ≤ (5 * C) * Fintype.card W := by omega
  exact_mod_cast hc

#print axioms potential_add
#print axioms minimal_potential_bound
#print axioms even_linear_bound
#print axioms asymptotic_of_irreducible_core_bound
end Erdos184Work.IrreducibleBound
