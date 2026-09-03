import Submission.LinearFamilyGap

/-! An efficient decomposition for the graphs used in LinearFamilyGap.
This is a special family, not a proof of Erdos 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.LinearFamilyGap.Efficient

variable {q : ℕ} [NeZero q]

/-- The shifts around the six parts sum to one. Each individual shift is
also a bijective function of the cycle parameter. -/
def shift (t : ZMod q) : Fin 6 → ZMod q := ![t,t,t,-t,-t,1-t]

def next (t : ZMod q) (v : Fin 6 × ZMod q) : Fin 6 × ZMod q :=
  (v.1+1, v.2 + shift t v.1)

def prev (t : ZMod q) (v : Fin 6 × ZMod q) : Fin 6 × ZMod q :=
  (v.1-1, v.2 - shift t (v.1-1))

lemma next_prev (t : ZMod q) (v : Fin 6 × ZMod q) : next t (prev t v) = v := by
  simp [next,prev]

lemma prev_next (t : ZMod q) (v : Fin 6 × ZMod q) : prev t (next t v) = v := by
  simp [next,prev]

lemma next_ne (t : ZMod q) (v : Fin 6 × ZMod q) : next t v ≠ v := by
  intro h
  have hh := congrArg Prod.fst h
  rcases v with ⟨i,x⟩
  fin_cases i <;> simp [next] at hh

lemma next_ne_prev (t : ZMod q) (v : Fin 6 × ZMod q) : next t v ≠ prev t v := by
  intro h
  have hh := congrArg Prod.fst h
  rcases v with ⟨i,x⟩
  fin_cases i <;> simp [next,prev,Fin.ext_iff] at hh

/-- One spanning cycle in the blowup graph. -/
def F (t : ZMod q) : SimpleGraph (Fin 6 × ZMod q) where
  Adj u v := next t u = v ∨ next t v = u
  symm := by intro u v h; exact h.symm
  loopless := by intro v h; exact h.elim (next_ne t v) (next_ne t v)

lemma F_le (t : ZMod q) : F t ≤ G (ZMod q) := by
  have hn (v : Fin 6 × ZMod q) : (G (ZMod q)).Adj v (next t v) := by
    rcases v with ⟨i,x⟩
    change (cycleGraph 6).Adj i (i+1)
    fin_cases i <;> decide
  intro u v h
  rcases h with h | h
  · exact h ▸ hn u
  · exact h ▸ (hn v).symm

lemma neighbors (t : ZMod q) (v : Fin 6 × ZMod q) :
    (F t).neighborSet v = {next t v, prev t v} := by
  ext w
  change (next t v = w ∨ next t w = v) ↔ w = next t v ∨ w = prev t v
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [← prev_next t w, h])
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (next_prev t v)

lemma F_regular (t : ZMod q) : (F t).IsRegularOfDegree 2 := by
  intro v
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  rw [neighbors]
  simp [next_ne_prev]

def chain (t x : ZMod q) : (F t).Walk (0,x) (0,x+1) :=
  .cons (by
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring : (F t).Adj (0,x) (1,x+t)) <|
  .cons (by
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring : (F t).Adj (1,x+t) (2,x+2*t)) <|
  .cons (by
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring : (F t).Adj (2,x+2*t) (3,x+3*t)) <|
  .cons (by
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring : (F t).Adj (3,x+3*t) (4,x+2*t)) <|
  .cons (by
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring : (F t).Adj (4,x+2*t) (5,x+t)) <|
  .cons (by
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring : (F t).Adj (5,x+t) (0,x+1)) .nil

def offset (t : ZMod q) : Fin 6 → ZMod q := ![0,t,2*t,3*t,2*t,t]

lemma reachable_part (t x : ZMod q) (i : Fin 6) :
    (F t).Reachable (0,x) (i,x + offset t i) := by
  have hm : (i,x + offset t i) ∈ (chain t x).support := by
    fin_cases i <;> simp [chain,offset]
  exact ((chain t x).takeUntil _ hm).reachable

lemma reachable_zero (t x : ZMod q) : (F t).Reachable (0,0) (0,x) := by
  have hn (n : ℕ) : (F t).Reachable (0,0) (0,(n : ZMod q)) := by
    induction n with
    | zero => simpa only [Nat.cast_zero] using
        (SimpleGraph.Reachable.rfl : (F t).Reachable (0,0) (0,0))
    | succ n ih =>
      simpa only [Nat.cast_add,Nat.cast_one] using ih.trans (chain t (n : ZMod q)).reachable
  simpa only [ZMod.natCast_zmod_val] using hn x.val

lemma F_connected (t : ZMod q) : (F t).Connected := by
  have hr (v : Fin 6 × ZMod q) : (F t).Reachable (0,0) v := by
    have hh := (reachable_zero t (v.2 - offset t v.1)).trans
      (reachable_part t (v.2 - offset t v.1) v.1)
    simpa only [sub_add_cancel,Prod.mk.eta] using hh
  exact {preconnected := fun u v => (hr u).symm.trans (hr v)}

lemma shift_injective (i : Fin 6) : Function.Injective (fun t : ZMod q => shift t i) := by
  intro t s h
  fin_cases i <;> simpa [shift] using h

lemma next_parameter {t s : ZMod q} (u : Fin 6 × ZMod q)
    (h : next t u = next s u) : t = s := by
  apply shift_injective u.1
  exact add_left_cancel (congrArg Prod.snd h)

lemma no_two_steps {t s : ZMod q} {u v : Fin 6 × ZMod q}
    (h : next t u = v) (h' : next s v = u) : False := by
  have h1 : u.1 + 1 = v.1 := congrArg Prod.fst h
  have h2 : v.1 + 1 = u.1 := congrArg Prod.fst h'
  have hh : (u.1 + 1) + 1 = u.1 := by rw [h1,h2]
  rcases u with ⟨i,x⟩
  fin_cases i <;> simp at hh

lemma edge_parameter {t s : ZMod q} {u v : Fin 6 × ZMod q}
    (h : (F t).Adj u v) (h' : (F s).Adj u v) : t = s := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact next_parameter u (h.trans h'.symm)
  · exact (no_two_steps h h').elim
  · exact (no_two_steps h h').elim
  · exact next_parameter v (h.trans h'.symm)

lemma edge_covered (u v : Fin 6 × ZMod q) (h : (G (ZMod q)).Adj u v) :
    ∃ t : ZMod q, (F t).Adj u v := by
  rcases u with ⟨i,x⟩
  rcases v with ⟨j,y⟩
  change (cycleGraph 6).Adj i j at h
  rw [base_adj] at h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · refine ⟨y-x,?_⟩
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨x-y,?_⟩
    apply Or.inr
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨y-x,?_⟩
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨x-y,?_⟩
    apply Or.inr
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨y-x,?_⟩
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨x-y,?_⟩
    apply Or.inr
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨x-y,?_⟩
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨y-x,?_⟩
    apply Or.inr
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨x-y,?_⟩
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨y-x,?_⟩
    apply Or.inr
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨x+1-y,?_⟩
    apply Or.inl
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring
  · refine ⟨y+1-x,?_⟩
    apply Or.inr
    apply Prod.ext
    · rfl
    · dsimp [next,shift] <;> ring

def P (t : ZMod q) : (G (ZMod q)).Subgraph := SimpleGraph.toSubgraph (F t) (F_le t)

lemma P_cycles (t : ZMod q) : (P t).coe.Connected ∧ (P t).coe.IsRegularOfDegree 2 := by
  constructor
  · apply (Subgraph.spanningCoeEquivCoeOfSpanning (P t)
      (SimpleGraph.toSubgraph.isSpanning (F t) (F_le t))).connected_iff.mp
    exact F_connected t
  · intro v
    rw [Subgraph.coe_degree, ← Subgraph.degree_spanningCoe]
    exact F_regular t v.val

lemma P_injective : Function.Injective (P (q := q)) := by
  intro t s h
  have ht : (P t).Adj (0,0) (next t (0,0)) := Or.inl rfl
  have hs : (P s).Adj (0,0) (next t (0,0)) := h ▸ ht
  exact edge_parameter ht hs

noncomputable def E : Finset (G (ZMod q)).Subgraph := Finset.univ.image P

lemma mem_E (H : (G (ZMod q)).Subgraph) : H ∈ E ↔ ∃ t, H = P t := by
  simp [E,eq_comm]

lemma E_card : (E (q := q)).card = q := by
  rw [E,Finset.card_image_of_injective _ P_injective]
  simp only [Finset.card_univ,ZMod.card]

lemma E_cycles : ∀ H ∈ E (q := q), H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  intro H hH
  obtain ⟨t,rfl⟩ := (mem_E H).mp hH
  exact P_cycles t

lemma E_decomposition : IsDecomposition (G (ZMod q)) E := by
  constructor
  · intro H hH J hJ hne
    obtain ⟨t,rfl⟩ := (mem_E H).mp hH
    obtain ⟨s,rfl⟩ := (mem_E J).mp hJ
    change Disjoint (P t).edgeSet (P s).edgeSet
    rw [Set.disjoint_left]
    intro e he hf
    induction e using Sym2.ind with
    | h u v =>
      have ht : (F t).Adj u v := Subgraph.mem_edgeSet.mp he
      have hs : (F s).Adj u v := Subgraph.mem_edgeSet.mp hf
      exact hne (congrArg P (edge_parameter ht hs))
  · ext e
    induction e using Sym2.ind with
    | h u v =>
      simp only [Set.mem_iUnion,exists_prop]
      constructor
      · rintro ⟨H,_,he⟩
        exact H.edgeSet_subset he
      · intro he
        obtain ⟨t,ht⟩ := edge_covered u v he
        exact ⟨P t,(mem_E _).mpr ⟨t,rfl⟩,Subgraph.mem_edgeSet.mpr ht⟩

/-- The very same graph has q spanning cycle pieces, so the q^2-piece
Latin-square decomposition is not a superlinear lower bound. -/
theorem efficient_decomposition :
    ∃ E : Finset (G (ZMod q)).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (G (ZMod q)) E ∧ E.card = q :=
  ⟨E,E_cycles,E_decomposition,E_card⟩

lemma q_le_decomposition_card (D : Finset (G (ZMod q)).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (G (ZMod q)) D) : q ≤ D.card := by
  have hcount := cycle_decomposition_vertex_count (G (ZMod q)) D hc hd (0,0)
  have hdegree : (G (ZMod q)).degree (0,0) = 2*q := by
    have h := graph_regular (ZMod q) (0,0)
    rw [ZMod.card] at h
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h
  rw [hdegree] at hcount
  have hfilter := Finset.card_filter_le (s := D) (p := fun H => (0,0) ∈ H.verts)
  omega

/-- The minimum pure cycle count of this graph is exactly q. -/
theorem E_minimum (D : Finset (G (ZMod q)).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (G (ZMod q)) D) : (E (q := q)).card ≤ D.card := by
  rw [E_card]
  exact q_le_decomposition_card D hc hd

/-- For q>1, the displayed q^2-piece decomposition is strictly larger
than this q-piece decomposition. -/
theorem strict_improvement (hq : 1 < q) :
    (E (q := q)).card < (LinearFamilyGap.D (ZMod q)).card := by
  rw [E_card,D_card,ZMod.card]
  nlinarith

end Erdos184.LinearFamilyGap.Efficient
