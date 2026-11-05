import Mathlib
import Submission.Basic

open SimpleGraph

namespace E74

universe u

variable {V : Type u}

/-- the capped graph on `Option V`: interior `I`, cap vertex `none` adjacent to `N`. -/
def capGraph (Q : SimpleGraph V) (I N : Set V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | some u, some v => u ∈ I ∧ v ∈ I ∧ Q.Adj u v
    | none, some v => v ∈ N
    | some u, none => u ∈ N
    | none, none => False
  symm := by
    intro a b h
    cases a <;> cases b <;> simp_all [Q.adj_comm]
  loopless := by
    intro a h
    cases a <;> simp_all

@[simp] lemma capGraph_adj_some_some (Q : SimpleGraph V) (I N : Set V) (u v : V) :
    (capGraph Q I N).Adj (some u) (some v) ↔ u ∈ I ∧ v ∈ I ∧ Q.Adj u v := Iff.rfl

@[simp] lemma capGraph_adj_none_some (Q : SimpleGraph V) (I N : Set V) (v : V) :
    (capGraph Q I N).Adj none (some v) ↔ v ∈ N := Iff.rfl

@[simp] lemma capGraph_adj_some_none (Q : SimpleGraph V) (I N : Set V) (v : V) :
    (capGraph Q I N).Adj (some v) none ↔ v ∈ N := Iff.rfl

@[simp] lemma capGraph_adj_none_none (Q : SimpleGraph V) (I N : Set V) :
    ¬ (capGraph Q I N).Adj none none := fun h => h

/-- multi-source distance -/
noncomputable def delta (T : SimpleGraph V) (C : Finset V) (v : V) : ℕ∞ :=
  C.inf (fun c => T.edist c v)

lemma delta_le {T : SimpleGraph V} {C : Finset V} {c v : V} (hc : c ∈ C) :
    delta T C v ≤ T.edist c v := Finset.inf_le hc

lemma delta_attained {T : SimpleGraph V} {C : Finset V} {u : V} (h : delta T C u ≠ ⊤) :
    ∃ c ∈ C, T.edist c u = delta T C u := by
  rcases C.eq_empty_or_nonempty with hC | hC
  · subst hC
    simp [delta] at h
  · obtain ⟨c, hc, heq⟩ := Finset.exists_mem_eq_inf C hC (fun c => T.edist c u)
    exact ⟨c, hc, heq.symm⟩

lemma delta_step {T : SimpleGraph V} {C : Finset V} {u v : V} (h : T.Adj u v) :
    delta T C v ≤ delta T C u + 1 := by
  by_cases hu : delta T C u = ⊤
  · rw [hu]; simp
  · obtain ⟨c, hc, heq⟩ := delta_attained hu
    calc delta T C v ≤ T.edist c v := delta_le hc
      _ ≤ T.edist c u + T.edist u v := T.edist_triangle
      _ = delta T C u + 1 := by rw [heq, edist_eq_one_iff_adj.2 h]

end E74
