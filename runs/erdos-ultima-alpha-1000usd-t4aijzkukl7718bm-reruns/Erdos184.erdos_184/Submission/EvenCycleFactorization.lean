import Submission.BalancedOrientation
import Submission.CycleFactors
import Submission.TerminalPermutationFactors

/-! Petersen factorization in a form that permits isolated vertices and
vertices of smaller even degree: an even graph of maximum degree at most
`2*r` is a disjoint union of `r` graphs consisting of vertex-disjoint cycles. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.EvenCycleFactorization
open BalancedOrientation
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

noncomputable def padded (A : V → V → ℕ) (r : ℕ) (x y : V) : ℕ :=
  A x y + if x = y then r - ∑ z, A x z else 0

lemma padded_sums {G : SimpleGraph V} {A : V → V → ℕ} (hA : IsBalanced G A)
    (r : ℕ) (hd : ∀ x, G.degree x ≤ 2*r) :
    (∀ x, (∑ y, padded A r x y) = r) ∧ (∀ y, (∑ x, padded A r x y) = r) := by
  have hl (x : V) : (∑ y, A x y) ≤ r := by
    have h₁ := row_twice_degree hA x
    have h₂ := hd x
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h₁ h₂
    omega
  constructor
  · intro x
    simp only [padded, Finset.sum_add_distrib]
    have hh : (∑ y : V, if x = y then r - ∑ z, A x z else 0) = r - ∑ z, A x z := by
      simp
    rw [hh]
    exact Nat.add_sub_of_le (hl x)
  · intro y
    simp only [padded, Finset.sum_add_distrib]
    have hh : (∑ x : V, if x = y then r - ∑ z, A x z else 0) = r - ∑ z, A y z := by simp
    rw [hh, ← hA.2]
    exact Nat.add_sub_of_le (hl y)

/-- Discard the loops from the undirected graph of a permutation. -/
def permutationGraph (σ : Equiv.Perm V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (σ x = y ∨ σ y = x)
  symm := by intro x y h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro x h; exact h.1 rfl

omit [Fintype V] in
lemma permutationGraph_isCycles (σ : Equiv.Perm V)
    (htwo : ∀ x, σ (σ x) = x → σ x = x) : (permutationGraph σ).IsCycles := by
  intro x hn
  have hf : σ x ≠ x := by
    intro hfix
    obtain ⟨y,hxy⟩ := hn
    rcases hxy.2 with hh | hh
    · exact hxy.1 (hfix.symm.trans hh)
    · exact hxy.1 (σ.injective (hfix.trans hh.symm))
  have hi : σ.symm x ≠ x := by
    intro hh
    apply hf
    calc σ x = σ (σ.symm x) := congrArg σ hh.symm
         _ = x := σ.apply_symm_apply x
  have hne : σ x ≠ σ.symm x := by
    intro hh
    have h₂ : σ (σ x) = x := (congrArg σ hh).trans (σ.apply_symm_apply x)
    exact hf (htwo x h₂)
  have hN : (permutationGraph σ).neighborSet x = {σ x,σ.symm x} := by
    ext y
    change (x ≠ y ∧ (σ x = y ∨ σ y = x)) ↔ y ∈ ({σ x,σ.symm x} : Set V)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_,h | h⟩
      · exact Or.inl h.symm
      · exact Or.inr ((σ.eq_symm_apply).mpr h)
    · rintro (rfl | rfl)
      · exact ⟨hf.symm,Or.inl rfl⟩
      · exact ⟨hi.symm,Or.inr (σ.apply_symm_apply x)⟩
  rw [hN, Set.ncard_pair hne]

lemma arc_lower {A : V → V → ℕ} {r : ℕ} {p : Fin r → Equiv.Perm V}
    (hp : ∀ x y, padded A r x y = ∑ c, if p c x = y then 1 else 0)
    (c : Fin r) {x y : V} (hne : x ≠ y) (hxy : p c x = y) : 1 ≤ A x y := by
  have hh := TerminalPermutationFactors.supported_of_factorization (padded A r) r p hp c x
  rw [hxy] at hh
  simpa only [padded, if_neg hne, Nat.add_zero] using hh

lemma factor_no_two_cycles {G : SimpleGraph V} {A : V → V → ℕ} (hA : IsBalanced G A)
    {r : ℕ} {p : Fin r → Equiv.Perm V}
    (hp : ∀ x y, padded A r x y = ∑ c, if p c x = y then 1 else 0) (c : Fin r) :
    ∀ x, p c (p c x) = x → p c x = x := by
  intro x hx
  by_contra hn
  have h₁ := arc_lower hp c (Ne.symm hn) rfl
  have h₂ := arc_lower hp c hn hx
  have h₃ := hA.1 x (p c x)
  split_ifs at h₃ <;> omega

lemma factor_indicator {G : SimpleGraph V} {A : V → V → ℕ} (hA : IsBalanced G A)
    {r : ℕ} {p : Fin r → Equiv.Perm V}
    (hp : ∀ x y, padded A r x y = ∑ c, if p c x = y then 1 else 0) (x y : V) :
    (∑ c, if (permutationGraph (p c)).Adj x y then (1 : ℕ) else 0) =
      if G.Adj x y then 1 else 0 := by
  by_cases hxy : x = y
  · subst y
    simp
  have hpoint (c : Fin r) :
      (if (permutationGraph (p c)).Adj x y then (1 : ℕ) else 0) =
        (if p c x = y then 1 else 0) + (if p c y = x then 1 else 0) := by
    have hnot : ¬(p c x = y ∧ p c y = x) := by
      rintro ⟨h₁,h₂⟩
      have hh := factor_no_two_cycles hA hp c x (by rw [h₁,h₂])
      exact hxy (hh.symm.trans h₁)
    simp only [permutationGraph]
    by_cases h₁ : p c x = y <;> by_cases h₂ : p c y = x <;> simp_all
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← hp, ← hp]
  simpa only [padded, if_neg hxy, if_neg (Ne.symm hxy), Nat.add_zero] using hA.1 x y

/-- A bounded-degree even graph has a cycle-factorization with exact edge
coverage. Each factor may have arbitrarily many connected components. -/
lemma exists_factorization (G : SimpleGraph V) (r : ℕ)
    (he : ∀ x, Even (G.degree x)) (hd : ∀ x, G.degree x ≤ 2*r) :
    ∃ F : Fin r → SimpleGraph V, (∀ c, (F c).IsCycles) ∧
      ∀ x y, (∑ c, if (F c).Adj x y then (1 : ℕ) else 0) = if G.Adj x y then 1 else 0 := by
  obtain ⟨A,hA⟩ := exists_balanced G he
  obtain ⟨hrow,hcol⟩ := padded_sums hA r hd
  obtain ⟨p,hp⟩ := IntegerMatrixFactorization.exists_permutation_factorization (padded A r) r hrow hcol
  exact ⟨fun c => permutationGraph (p c),
    fun c => permutationGraph_isCycles (p c) (factor_no_two_cycles hA hp c),
    factor_indicator hA hp⟩

lemma exists_two_factors (G : SimpleGraph V)
    (he : ∀ x, Even (G.degree x)) (hd : ∀ x, G.degree x ≤ 4) :
    ∃ A B : SimpleGraph V, A.IsCycles ∧ B.IsCycles ∧
      Disjoint A.edgeSet B.edgeSet ∧ A.edgeSet ∪ B.edgeSet = G.edgeSet := by
  obtain ⟨F,hF,hcov⟩ := exists_factorization G 2 he (by simpa using hd)
  refine ⟨F 0,F 1,hF 0,hF 1,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro e he₀ he₁
    induction e using Sym2.ind with
    | h x y =>
      have hh := hcov x y
      simp only [Fin.sum_univ_two, if_pos (show (F 0).Adj x y from he₀),
        if_pos (show (F 1).Adj x y from he₁)] at hh
      split_ifs at hh <;> omega
  · ext e
    induction e using Sym2.ind with
    | h x y =>
      have hh := hcov x y
      simp only [Fin.sum_univ_two] at hh
      change ((F 0).Adj x y ∨ (F 1).Adj x y) ↔ G.Adj x y
      by_cases h₀ : (F 0).Adj x y <;> by_cases h₁ : (F 1).Adj x y <;>
        by_cases hg : G.Adj x y <;> simp_all

open FractionalEnvelope CycleNumberSubmodularity

lemma rooted_degree_four (G : SimpleGraph V)
    (he : ∀ x, Even (G.degree x)) (hd : ∀ x, G.degree x ≤ 4)
    (e : Sym2 V) (heG : e ∈ G.edgeSet) :
    (cycleNumber G : ℝ) ≤ envelope (G.deleteEdges {e}) + RootedEnvelopeProfiles.through G e := by
  obtain ⟨A,B,hA,hB,hdis,hcov⟩ := exists_two_factors G he hd
  exact CycleFactors.rooted_of_two_factors hcov hdis hA hB heG

lemma number_le_twice_envelope_degree_four (G : SimpleGraph V)
    (he : ∀ x, Even (G.degree x)) (hd : ∀ x, G.degree x ≤ 4) :
    (cycleNumber G : ℝ) ≤ 2 * envelope G := by
  by_cases hb : G = ⊥
  · subst G
    simp only [CountCritical.number_bot, Nat.cast_zero, envelope_bot, mul_zero, le_refl]
  obtain ⟨x,y,hxy⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hb
  have hh := rooted_degree_four G he hd s(x,y) hxy
  have h₀ := envelope_mono (G.deleteEdges_le {s(x,y)})
  have h₁ := RootedEnvelopeProfiles.through_le_envelope G s(x,y)
  linarith

/-- This comparison is hereditary, so it also bounds the integral envelope
of an arbitrary (not necessarily even) graph of maximum degree at most four. -/
lemma envelope_le_twice_fractional_degree_four (G : SimpleGraph V)
    (hd : ∀ x, G.degree x ≤ 4) :
    (CycleEnvelope.envelope G : ℝ) ≤ 2 * envelope G := by
  obtain ⟨H,hHG,heH,hval⟩ := CycleEnvelope.attained G
  have hdH : ∀ x, H.degree x ≤ 4 := by
    intro x
    have h₁ := SimpleGraph.degree_le_of_le (v := x) hHG
    have h₂ := hd x
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h₁ h₂ ⊢
    omega
  have hh := number_le_twice_envelope_degree_four H heH hdH
  rw [hval] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (envelope_mono hHG) (by norm_num))

end Erdos184.EvenCycleFactorization
