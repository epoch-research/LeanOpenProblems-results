import FormalConjecturesUtil
import Submission.CompactCloneAverageAudit

/-! A diagnostic against transferring an upper power bound through a single
identification. This is not a counterexample to the rationality conjecture. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713C8Fold
open Erdos713Cloning Erdos713Rate

noncomputable def identifiedIso {A W : Type*} {F : SimpleGraph A} {G : SimpleGraph W}
    (e : F ≃g G) (a b : A) (hna : ¬ F.Adj a b) (hnb : ¬ G.Adj (e a) (e b)) :
    identified F a b hna ≃g identified G (e a) (e b) hnb where
  toEquiv :=
    { toFun := fun z => ⟨e z.val,fun he => z.prop (e.injective he)⟩
      invFun := fun z => ⟨e.symm z.val,fun he => z.prop (by simpa using congrArg e he)⟩
      left_inv := fun z => Subtype.ext (e.symm_apply_apply z.val)
      right_inv := fun z => Subtype.ext (e.apply_symm_apply z.val) }
  map_rel_iff' := by
    intro z w
    change (G.Adj (e z.val) (e w.val) ∨
        (e z.val = e b ∧ G.Adj (e a) (e w.val)) ∨
        (e w.val = e b ∧ G.Adj (e a) (e z.val))) ↔ _
    simp only [e.map_rel_iff,e.injective.eq_iff,identified]

lemma triangle_not_bipartite {W : Type*} {G : SimpleGraph W} {a b c : W}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : ¬ G.IsBipartite := by
  rintro ⟨χ⟩
  have h₁ := χ.valid hab
  have h₂ := χ.valid hbc
  have h₃ := χ.valid hca
  omega

lemma fold_two_contains_C6 (hn : ¬ (cycleGraph 8).Adj 0 2) :
    Erdos713C6.C6 ⊑ identified (cycleGraph 8) 0 2 hn := by
  let f : Fin 6 → {w : Fin 8 // w ≠ 0} := fun i => ⟨⟨i.val+2,by omega⟩,by
    intro he
    have hh := congrArg Fin.val he
    change i.val+2 = 0 at hh
    omega⟩
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro i j
    simp only [Erdos713C6.C6,cycleGraph_adj,f,identified]
    fin_cases i <;> fin_cases j <;> decide
  · intro i j hij
    have hh := congrArg (fun w : {w : Fin 8 // w ≠ 0} => w.val.val) hij
    change i.val+2 = j.val+2 at hh
    exact Fin.ext (by omega)

lemma fold_six_contains_C6 (hn : ¬ (cycleGraph 8).Adj 0 6) :
    Erdos713C6.C6 ⊑ identified (cycleGraph 8) 0 6 hn := by
  let f : Fin 6 → {w : Fin 8 // w ≠ 0} := fun i => ⟨⟨i.val+1,by omega⟩,by
    intro he
    have hh := congrArg Fin.val he
    change i.val+1 = 0 at hh
    omega⟩
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro i j
    simp only [Erdos713C6.C6,cycleGraph_adj,f,identified]
    fin_cases i <;> fin_cases j <;> decide
  · intro i j hij
    have hh := congrArg (fun w : {w : Fin 8 // w ≠ 0} => w.val.val) hij
    change i.val+1 = j.val+1 at hh
    exact Fin.ext (by omega)

lemma fold_four_contains_K22 (hn : ¬ (cycleGraph 8).Adj 0 4) :
    Erdos713C4.K22 ⊑ identified (cycleGraph 8) 0 4 hn := by
  classical
  by_contra hfree
  apply Erdos713C4.no_rectangle hfree
    (u := ⟨1,by decide⟩) (v := ⟨3,by decide⟩) (a := ⟨2,by decide⟩) (b := ⟨4,by decide⟩)
  all_goals first | decide | (simp only [identified,cycleGraph_adj] <;> decide)

lemma fold_three_not_bipartite (hn : ¬ (cycleGraph 8).Adj 0 3) :
    ¬ (identified (cycleGraph 8) 0 3 hn).IsBipartite := by
  apply triangle_not_bipartite (a := ⟨1,by decide⟩) (b := ⟨2,by decide⟩) (c := ⟨3,by decide⟩)
  all_goals first | decide | (simp only [identified,cycleGraph_adj] <;> decide)

lemma fold_five_not_bipartite (hn : ¬ (cycleGraph 8).Adj 0 5) :
    ¬ (identified (cycleGraph 8) 0 5 hn).IsBipartite := by
  apply triangle_not_bipartite (a := ⟨5,by decide⟩) (b := ⟨6,by decide⟩) (c := ⟨7,by decide⟩)
  all_goals first | decide | (simp only [identified,cycleGraph_adj] <;> decide)

lemma normalized_contains (b : Fin 8) (hb : (0 : Fin 8) ≠ b)
    (hn : ¬ (cycleGraph 8).Adj 0 b) (hB : (identified (cycleGraph 8) 0 b hn).IsBipartite) :
    Erdos713C6.C6 ⊑ identified (cycleGraph 8) 0 b hn ∨
      Erdos713C4.K22 ⊑ identified (cycleGraph 8) 0 b hn := by
  fin_cases b
  · exact (hb rfl).elim
  · exact (hn (by decide)).elim
  · exact Or.inl (fold_two_contains_C6 hn)
  · exact (fold_three_not_bipartite hn hB).elim
  · exact Or.inr (fold_four_contains_K22 hn)
  · exact (fold_five_not_bipartite hn hB).elim
  · exact Or.inl (fold_six_contains_C6 hn)
  · exact (hn (by decide)).elim

lemma contains_of_first_zero (a b : Fin 8) (ha : a = 0) (hab : a ≠ b)
    (hn : ¬ (cycleGraph 8).Adj a b) (hB : (identified (cycleGraph 8) a b hn).IsBipartite) :
    Erdos713C6.C6 ⊑ identified (cycleGraph 8) a b hn ∨
      Erdos713C4.K22 ⊑ identified (cycleGraph 8) a b hn := by
  subst a
  exact normalized_contains b hab hn hB

lemma contains_shorter (a b : Fin 8) (hab : a ≠ b) (hn : ¬ (cycleGraph 8).Adj a b)
    (hB : (identified (cycleGraph 8) a b hn).IsBipartite) :
    Erdos713C6.C6 ⊑ identified (cycleGraph 8) a b hn ∨
      Erdos713C4.K22 ⊑ identified (cycleGraph 8) a b hn := by
  let e : cycleGraph 8 ≃g cycleGraph 8 :=
    ⟨Equiv.addRight (-a),by intro u v; exact circulantGraph_adj_translate⟩
  have hea : e a = 0 := by change a+(-a) = 0; simp
  have hne : e a ≠ e b := e.injective.ne hab
  have hn' : ¬ (cycleGraph 8).Adj (e a) (e b) := fun h => hn (e.map_rel_iff.mp h)
  let E := identifiedIso e a b hn hn'
  have hB' : (identified (cycleGraph 8) (e a) (e b) hn').IsBipartite :=
    hB.of_hom E.symm.toHom
  have hshort := contains_of_first_zero (e a) (e b) hea hne hn' hB'
  exact hshort.imp (fun h => h.trans ⟨E.symm.toCopy⟩) (fun h => h.trans ⟨E.symm.toCopy⟩)

lemma quotient_lower {a b : Fin 8} (hab : a ≠ b) (hn : ¬ (cycleGraph 8).Adj a b)
    (hB : (identified (cycleGraph 8) a b hn).IsBipartite) {r : ℝ}
    (hU : (fun n : ℕ => (extremalNumber n (identified (cycleGraph 8) a b hn) : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ)^r)) : (4 : ℝ)/3 ≤ r := by
  rcases contains_shorter a b hab hn hB with hSix | hFour
  · apply Erdos713C6.lower_exponent_of_prime_bound hU
    intro p hp
    exact (Erdos713C6.extremal_lower_prime p hp).trans hSix.extremalNumber_le
  · have hh : (3 : ℝ)/2 ≤ r := by
      apply Erdos713C4.lower_exponent_of_prime_bound hU
      intro p hp
      exact (Erdos713C4.extremal_lower_prime p hp).trans hFour.extremalNumber_le
    linarith

lemma not_upper_five_quarters {a b : Fin 8} (hab : a ≠ b)
    (hn : ¬ (cycleGraph 8).Adj a b) (hB : (identified (cycleGraph 8) a b hn).IsBipartite) :
    ¬ (fun n : ℕ => (extremalNumber n (identified (cycleGraph 8) a b hn) : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ)^((5 : ℝ)/4)) := by
  intro hu
  have hh := quotient_lower hab hn hB hu
  norm_num at hh

/-- Conditional on a C8 asymptotic, every bipartite single-identification
quotient has a strictly HIGHER ordinary lower threshold. No existence of
such an exact asymptotic for C8 is assumed outside this implication. -/
lemma no_transfer_at_asymptotic {α c : ℝ} (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) {a b : Fin 8} (hab : a ≠ b)
    (hn : ¬ (cycleGraph 8).Adj a b) (hB : (identified (cycleGraph 8) a b hn).IsBipartite) :
    ¬ HasRate (identified (cycleGraph 8) a b hn) α := by
  intro hRate
  have hα : α ≤ (5 : ℝ)/4 :=
    Erdos713EvenCycle.exponent_upper_of_containment (by decide : 2 ≤ 4) (.refl _) hc h
  have hlo := quotient_lower hab hn hB hRate.upper
  linarith

lemma fold_two_bipartite (hn : ¬ (cycleGraph 8).Adj 0 2) :
    (identified (cycleGraph 8) 0 2 hn).IsBipartite := by
  refine ⟨Coloring.mk (fun z => (⟨z.val.val % 2,Nat.mod_lt _ (by decide)⟩ : Fin 2)) ?_⟩
  intro u v
  simp only [identified,cycleGraph_adj]
  fin_cases u <;> fin_cases v <;> decide

set_option maxHeartbeats 800000 in
/-- A checked negation of an AUXILIARY transfer principle. It is not the
negation of the original rational-exponent conjecture. -/
lemma no_universal_upper_transfer :
    ¬ ∀ (q : ℕ) (H : SimpleGraph (Fin q)) (a b : Fin q)
      (hab : a ≠ b) (hn : ¬ H.Adj a b) (r : ℝ),
      H.IsBipartite → (identified H a b hn).IsBipartite →
      ((fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r)) →
      ((fun n : ℕ => (extremalNumber n (identified H a b hn) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^r)) := by
  intro h
  have hn : ¬ (cycleGraph 8).Adj 0 2 := by decide
  have hB : (cycleGraph 8).IsBipartite := by
    refine ⟨Coloring.mk (fun z => (⟨z.val % 2,Nat.mod_lt _ (by decide)⟩ : Fin 2)) ?_⟩
    intro u v
    simp only [cycleGraph_adj]
    fin_cases u <;> fin_cases v <;> decide
  have hU : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((5 : ℝ)/4)) :=
    by simpa using (Erdos713EvenCycle.upper (by decide : 2 ≤ 4))
  exact not_upper_five_quarters (by decide : (0 : Fin 8) ≠ 2) hn (fold_two_bipartite hn)
    (h 8 (cycleGraph 8) 0 2 (by decide) hn (5/4) hB (fold_two_bipartite hn) hU)

#print axioms identifiedIso
#print axioms contains_shorter
#print axioms quotient_lower
#print axioms no_transfer_at_asymptotic
#print axioms no_universal_upper_transfer
end Erdos713C8Fold
