import FormalConjecturesUtil

/-!
The Mycielski graph of a five-cycle is triangle-free, but every ordering of
its vertices has an increasing three-edge path whose endpoints are adjacent.
A short parity proof uses ten four-cycles. This is an auxiliary obstruction
to a proposed representation route, not a solution of Erdos 595.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open SimpleGraph Set
namespace Erdos595MycielskiFiveOrder

abbrev Vertex := Option (Fin 5 × Bool)
def old (i : Fin 5) : Vertex := some (i,false)
def copy (i : Fin 5) : Vertex := some (i,true)
def ringAdj (i j : Fin 5) : Prop := j = i + 1 ∨ i = j + 1
instance : DecidableRel ringAdj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private lemma ring_irrefl (i : Fin 5) : ¬ringAdj i i := by
  fin_cases i <;> decide
private lemma ring_triangle : ∀ i j k : Fin 5,
    ringAdj i j → ringAdj i k → ringAdj j k → False := by decide +kernel

def graph : SimpleGraph Vertex where
  Adj
    | none, none => False
    | none, some p => p.2 = true
    | some p, none => p.2 = true
    | some p, some q => ringAdj p.1 q.1 ∧ (p.2 = false ∨ q.2 = false)
  symm := by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    intro a h
    cases a with
    | none => exact h
    | some a => exact ring_irrefl a.1 h.1

instance : DecidableRel graph.Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [graph] <;> infer_instance

private lemma no_triangle : ∀ a b c, graph.Adj a b → graph.Adj a c →
    graph.Adj b c → False := by decide +kernel

lemma triangleFree : graph.CliqueFree 3 := by
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact no_triangle a b c hab hac hbc

lemma old_edge (i : Fin 5) : graph.Adj (old i) (old (i+1)) :=
  ⟨Or.inl rfl,Or.inl rfl⟩
lemma left_edge (i : Fin 5) : graph.Adj (old i) (copy (i+1)) :=
  ⟨Or.inl rfl,Or.inl rfl⟩
lemma right_edge (i : Fin 5) : graph.Adj (copy i) (old (i+1)) :=
  ⟨Or.inl rfl,Or.inr rfl⟩
lemma apex_edge (i : Fin 5) : graph.Adj none (copy i) := rfl

/-- An antisymmetric sign on each edge cannot balance all four-cycles. -/
theorem no_balanced_signs (s : Vertex → Vertex → ℤ)
    (hv : ∀ a b, graph.Adj a b → s a b = 1 ∨ s a b = -1)
    (hs : ∀ a b, graph.Adj a b → s b a = -s a b)
    (hb : ∀ a b c d, graph.Adj a b → graph.Adj b c →
      graph.Adj c d → graph.Adj d a → s a b + s b c + s c d + s d a = 0) : False := by
  let a (i : Fin 5) := s (old i) (old (i+1))
  let b (i : Fin 5) := s (old i) (copy (i+1))
  let c (i : Fin 5) := s (copy i) (old (i+1))
  let d (i : Fin 5) := s none (copy i)
  have h₁ (i : Fin 5) : a i + a (i+1) - c (i+1) - b i = 0 := by
    have h := hb (old i) (old (i+1)) (old ((i+1)+1)) (copy (i+1))
      (old_edge i) (old_edge (i+1)) (right_edge (i+1)).symm (left_edge i).symm
    rw [hs _ _ (right_edge (i+1)),hs _ _ (left_edge i)] at h
    exact h
  have h₂ (i : Fin 5) : c i + b (i+1) - d ((i+1)+1) + d i = 0 := by
    have h := hb (copy i) (old (i+1)) (copy ((i+1)+1)) none
      (right_edge i) (left_edge (i+1)) (apex_edge ((i+1)+1)).symm (apex_edge i)
    rw [hs _ _ (apex_edge ((i+1)+1))] at h
    exact h
  have e0 := h₁ 0
  have e1 := h₁ 1
  have e2 := h₁ 2
  have e3 := h₁ 3
  have e4 := h₁ 4
  have f0 := h₂ 0
  have f1 := h₂ 1
  have f2 := h₂ 2
  have f3 := h₂ 3
  have f4 := h₂ 4
  have v0 := hv _ _ (old_edge 0)
  have v1 := hv _ _ (old_edge 1)
  have v2 := hv _ _ (old_edge 2)
  have v3 := hv _ _ (old_edge 3)
  have v4 := hv _ _ (old_edge 4)
  change a 0 = 1 ∨ a 0 = -1 at v0
  change a 1 = 1 ∨ a 1 = -1 at v1
  change a 2 = 1 ∨ a 2 = -1 at v2
  change a 3 = 1 ∨ a 3 = -1 at v3
  change a 4 = 1 ∨ a 4 = -1 at v4
  change a 0 + a 1 - c 1 - b 0 = 0 at e0
  change a 1 + a 2 - c 2 - b 1 = 0 at e1
  change a 2 + a 3 - c 3 - b 2 = 0 at e2
  change a 3 + a 4 - c 4 - b 3 = 0 at e3
  change a 4 + a 0 - c 0 - b 4 = 0 at e4
  change c 0 + b 1 - d 2 + d 0 = 0 at f0
  change c 1 + b 2 - d 3 + d 1 = 0 at f1
  change c 2 + b 3 - d 4 + d 2 = 0 at f2
  change c 3 + b 4 - d 0 + d 3 = 0 at f3
  change c 4 + b 0 - d 1 + d 4 = 0 at f4
  have hsum : 2 * (a 0 + a 1 + a 2 + a 3 + a 4) = 0 := by
    linear_combination e0 + e1 + e2 + e3 + e4 + f0 + f1 + f2 + f3 + f4
  clear hv hs hb h₁ h₂ e0 e1 e2 e3 e4 f0 f1 f2 f3 f4
  rcases v0 with v0 | v0 <;> rcases v1 with v1 | v1 <;>
    rcases v2 with v2 | v2 <;> rcases v3 with v3 | v3 <;> rcases v4 with v4 | v4 <;>
    rw [v0,v1,v2,v3,v4] at hsum <;> norm_num at hsum

variable {A K : Type*} [LinearOrder K]

noncomputable def sign (t : A → K) (a b : A) : ℤ := if t a < t b then 1 else -1

lemma sign_values (t : A → K) (a b : A) : sign t a b = 1 ∨ sign t a b = -1 := by
  classical
  by_cases h : t a < t b <;> simp [sign,h]

lemma sign_reverse (t : A → K) {a b : A} (h : t a ≠ t b) :
    sign t b a = -sign t a b := by
  classical
  rcases lt_or_gt_of_ne h with h | h <;> simp [sign,h,not_lt_of_ge h.le]

/-- This uses only a strict separation on edges, not injectivity on vertices. -/
lemma square_balance (G : SimpleGraph A) (t : A → K)
    (he : ∀ a b, G.Adj a b → t a ≠ t b)
    (hn : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      ¬(t a < t b ∧ t b < t c ∧ t c < t d))
    (a b c d : A) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) :
    sign t a b + sign t b c + sign t c d + sign t d a = 0 := by
  classical
  have eab := he a b hab
  have ebc := he b c hbc
  have ecd := he c d hcd
  have eda := he d a hda
  have h0 := hn a b c d hab hbc hcd hda
  have h1 := hn b c d a hbc hcd hda hab
  have h2 := hn c d a b hcd hda hab hbc
  have h3 := hn d a b c hda hab hbc hcd
  have k0 := hn d c b a hcd.symm hbc.symm hab.symm hda.symm
  have k1 := hn a d c b hda.symm hcd.symm hbc.symm hab.symm
  have k2 := hn b a d c hab.symm hda.symm hcd.symm hbc.symm
  have k3 := hn c b a d hbc.symm hab.symm hda.symm hcd.symm
  by_cases hAB : t a < t b <;> by_cases hBC : t b < t c <;>
    by_cases hCD : t c < t d <;> by_cases hDA : t d < t a
  · exact (h0 ⟨hAB,hBC,hCD⟩).elim
  · exact (h0 ⟨hAB,hBC,hCD⟩).elim
  · exact (h3 ⟨hDA,hAB,hBC⟩).elim
  · norm_num [sign,hAB,hBC,hCD,hDA]
  · exact (h2 ⟨hCD,hDA,hAB⟩).elim
  · norm_num [sign,hAB,hBC,hCD,hDA]
  · norm_num [sign,hAB,hBC,hCD,hDA]
  · have rBC : t c < t b := lt_of_le_of_ne (le_of_not_gt hBC) ebc.symm
    have rCD : t d < t c := lt_of_le_of_ne (le_of_not_gt hCD) ecd.symm
    have rDA : t a < t d := lt_of_le_of_ne (le_of_not_gt hDA) eda.symm
    exact (k1 ⟨rDA,rCD,rBC⟩).elim
  · exact (h1 ⟨hBC,hCD,hDA⟩).elim
  · norm_num [sign,hAB,hBC,hCD,hDA]
  · norm_num [sign,hAB,hBC,hCD,hDA]
  · have rCD : t d < t c := lt_of_le_of_ne (le_of_not_gt hCD) ecd.symm
    have rDA : t a < t d := lt_of_le_of_ne (le_of_not_gt hDA) eda.symm
    have rAB : t b < t a := lt_of_le_of_ne (le_of_not_gt hAB) eab.symm
    exact (k2 ⟨rAB,rDA,rCD⟩).elim
  · norm_num [sign,hAB,hBC,hCD,hDA]
  · have rDA : t a < t d := lt_of_le_of_ne (le_of_not_gt hDA) eda.symm
    have rAB : t b < t a := lt_of_le_of_ne (le_of_not_gt hAB) eab.symm
    have rBC : t c < t b := lt_of_le_of_ne (le_of_not_gt hBC) ebc.symm
    exact (k3 ⟨rBC,rAB,rDA⟩).elim
  · have rAB : t b < t a := lt_of_le_of_ne (le_of_not_gt hAB) eab.symm
    have rBC : t c < t b := lt_of_le_of_ne (le_of_not_gt hBC) ebc.symm
    have rCD : t d < t c := lt_of_le_of_ne (le_of_not_gt hCD) ecd.symm
    exact (k0 ⟨rCD,rBC,rAB⟩).elim
  · have rAB : t b < t a := lt_of_le_of_ne (le_of_not_gt hAB) eab.symm
    have rBC : t c < t b := lt_of_le_of_ne (le_of_not_gt hBC) ebc.symm
    have rCD : t d < t c := lt_of_le_of_ne (le_of_not_gt hCD) ecd.symm
    exact (k0 ⟨rCD,rBC,rAB⟩).elim

/-- In particular this triangle-free graph has no ordering avoiding all
increasing three-edge shortcuts. -/
theorem increasing_shortcut (t : Vertex → K)
    (he : ∀ a b, graph.Adj a b → t a ≠ t b) :
    ∃ a b c d, graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a ∧
      t a < t b ∧ t b < t c ∧ t c < t d := by
  classical
  by_contra h
  apply no_balanced_signs (sign t) (fun a b _ => sign_values t a b)
    (fun a b hab => sign_reverse t (he a b hab))
  apply square_balance graph t he
  intro a b c d hab hbc hcd hda ht
  exact h ⟨a,b,c,d,hab,hbc,hcd,hda,ht⟩

#print axioms triangleFree
#print axioms no_balanced_signs
#print axioms increasing_shortcut
end Erdos595MycielskiFiveOrder
