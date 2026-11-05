import Mathlib

open SimpleGraph

namespace E74

universe u

variable {V : Type u}

/-- 3-colourability. -/
def Col3 (Q : SimpleGraph V) : Prop := ∃ g : V → Fin 3, ∀ u v, Q.Adj u v → g u ≠ g v

/-- the set of edges of `Q` inside `S` that are monochromatic under `c`. -/
def mono (Q : SimpleGraph V) (S : Finset V) (c : V → Bool) : Set (Sym2 V) :=
  {e | ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∈ S ∧ Q.Adj u v ∧ c u = c v}

lemma mono_finite [Finite V] (Q : SimpleGraph V) (S : Finset V) (c : V → Bool) :
    (mono Q S c).Finite :=
  Set.toFinite _

/-- the "profile condition" for the function `T`. -/
def Prof (T : ℕ → ℕ) (Q : SimpleGraph V) : Prop :=
  ∀ (S : Finset V) (k : ℕ), (∀ c : V → Bool, k ≤ (mono Q S c).ncard) → T k ≤ S.card

lemma walk_parity {H : SimpleGraph V} (c : V → Bool) {u v : V} (w : H.Walk u v)
    (hc : ∀ e ∈ w.edges, ∀ a b, e = s(a, b) → c a ≠ c b) :
    (c u = c v ↔ Even w.length) := by
  induction w with
  | nil => simp
  | cons h p ih =>
    rename_i a b d
    have h1 : c a ≠ c b := hc _ (by simp) a b rfl
    have h2 := ih (fun e he => hc e (by simp [he]))
    rw [Walk.length_cons, Nat.even_add_one, ← h2]
    revert h1
    generalize c a = x
    generalize c b = y
    generalize c d = z
    revert x y z
    decide

lemma exists_mono_edge {H : SimpleGraph V} (c : V → Bool) {u : V} (w : H.Walk u u)
    (hodd : Odd w.length) : ∃ e ∈ w.edges, ∃ a b, e = s(a, b) ∧ c a = c b := by
  by_contra hcon
  push_neg at hcon
  have h := (walk_parity c w (fun e he a b hab => hcon e he a b hab)).1 rfl
  exact (Nat.not_even_iff_odd.2 hodd) h

/-- there is an odd closed walk of length `≤ L`. -/
def OddShort (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ (u : V) (w : G.Walk u u), Odd w.length ∧ w.length ≤ L

/-- size bound in the tree lemma -/
def sz (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (L + 1) + L * sz L k

theorem tree_lemma [Finite V] (L : ℕ) : ∀ (k : ℕ) (H : SimpleGraph V),
    (∀ F : Finset (Sym2 V), F.card < k → OddShort (H.deleteEdges (F : Set (Sym2 V))) L) →
    ∃ S : Finset V, S.card ≤ sz L k ∧ ∀ c : V → Bool, k ≤ (mono H S c).ncard := by
  classical
  intro k
  induction k with
  | zero => intro H _; exact ⟨∅, by simp [sz], fun c => Nat.zero_le _⟩
  | succ k ih =>
    intro H hH
    obtain ⟨u, w, hodd, hlen⟩ := hH ∅ (by simp)
    have hyp : ∀ e : Sym2 V, ∀ F : Finset (Sym2 V), F.card < k →
        OddShort ((H.deleteEdges {e}).deleteEdges (F : Set (Sym2 V))) L := by
      intro e F hF
      have h := hH (insert e F) (by
        have := Finset.card_insert_le e F
        omega)
      have heq : H.deleteEdges (↑(insert e F) : Set (Sym2 V)) =
          (H.deleteEdges {e}).deleteEdges (F : Set (Sym2 V)) := by
        rw [deleteEdges_deleteEdges, Finset.coe_insert, Set.insert_eq]
      rw [heq] at h
      exact h
    have hex : ∀ e : Sym2 V, e ∈ w.edges.toFinset → ∃ S : Finset V, S.card ≤ sz L k ∧
        ∀ c : V → Bool, k ≤ (mono (H.deleteEdges {e}) S c).ncard :=
      fun e _ => ih (H.deleteEdges {e}) (hyp e)
    choose! Sf hSf using hex
    refine ⟨w.support.toFinset ∪ w.edges.toFinset.biUnion Sf, ?_, ?_⟩
    · have h1 : w.support.toFinset.card ≤ L + 1 := by
        have := List.toFinset_card_le w.support
        rw [Walk.length_support] at this
        omega
      have h2 : (w.edges.toFinset.biUnion Sf).card ≤ L * sz L k := by
        have h3 : w.edges.toFinset.card ≤ L := by
          have := List.toFinset_card_le w.edges
          rw [Walk.length_edges] at this
          omega
        calc (w.edges.toFinset.biUnion Sf).card ≤ w.edges.toFinset.card * sz L k :=
              Finset.card_biUnion_le_card_mul _ _ _ (fun e he => (hSf e he).1)
          _ ≤ L * sz L k := Nat.mul_le_mul_right _ h3
      calc (w.support.toFinset ∪ w.edges.toFinset.biUnion Sf).card
          ≤ w.support.toFinset.card + (w.edges.toFinset.biUnion Sf).card :=
            Finset.card_union_le _ _
        _ ≤ sz L (k + 1) := by
            simp only [sz]
            omega
    · intro c
      obtain ⟨e, he, a, b, rfl, hab⟩ := exists_mono_edge c w hodd
      have ha : a ∈ w.support := w.fst_mem_support_of_mem_edges he
      have hb : b ∈ w.support := w.snd_mem_support_of_mem_edges he
      have hadj : H.Adj a b := by
        have := w.edges_subset_edgeSet he
        rw [mem_edgeSet] at this
        exact ((deleteEdges_adj).1 this).1
      have hmem : s(a, b) ∈ mono H (w.support.toFinset ∪ w.edges.toFinset.biUnion Sf) c :=
        ⟨a, b, rfl, by simp [ha], by simp [hb], hadj, hab⟩
      have heE : s(a, b) ∈ w.edges.toFinset := by simpa using he
      have hsub : mono (H.deleteEdges {s(a, b)}) (Sf s(a, b)) c ⊆
          mono H (w.support.toFinset ∪ w.edges.toFinset.biUnion Sf) c \ {s(a, b)} := by
        rintro e ⟨x, y, rfl, hx, hy, hxy, hcxy⟩
        rw [deleteEdges_adj] at hxy
        refine ⟨⟨x, y, rfl, ?_, ?_, hxy.1, hcxy⟩, ?_⟩
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, heE, hx⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, heE, hy⟩)
        · simpa using hxy.2
      have h1 := (hSf s(a, b) heE).2 c
      have h2 : (mono H (w.support.toFinset ∪ w.edges.toFinset.biUnion Sf) c \ {s(a, b)}).ncard =
          (mono H (w.support.toFinset ∪ w.edges.toFinset.biUnion Sf) c).ncard - 1 :=
        Set.ncard_diff_singleton_of_mem hmem
      have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h4 : 0 < (mono H (w.support.toFinset ∪ w.edges.toFinset.biUnion Sf) c).ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hmem⟩
      omega

end E74
