import Mathlib
import Submission.Basic
import Submission.Cap1

open SimpleGraph

namespace E74

universe u

variable {V : Type u}

/-- the graph `T = Q - F` -/
abbrev Tg (Q : SimpleGraph V) (F : Finset (Sym2 V)) : SimpleGraph V :=
  Q.deleteEdges (F : Set (Sym2 V))

lemma Tg_adj {Q : SimpleGraph V} {F : Finset (Sym2 V)} {u v : V} :
    (Tg Q F).Adj u v ↔ Q.Adj u v ∧ s(u, v) ∉ F := by
  simp [Tg]

lemma adj_of_Q {Q : SimpleGraph V} {F : Finset (Sym2 V)} {u v : V} (h : Q.Adj u v) :
    (Tg Q F).Adj u v ∨ s(u, v) ∈ F := by
  by_cases hF : s(u, v) ∈ F
  · exact Or.inr hF
  · exact Or.inl (Tg_adj.2 ⟨h, hF⟩)

/-- hypotheses of the capping construction -/
structure CapData (Q : SimpleGraph V) (F : Finset (Sym2 V)) (P : V → Bool) (C : Finset V)
    (R : ℕ) : Prop where
  hR : 1 ≤ R
  hsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
    ((4 * R + 1 : ℕ) : ℕ∞) < (Tg Q F).edist c c'
  hodd : ∀ (u : V) (w : (Tg Q F).Walk u u), Odd w.length → 4 * R + 1 < w.length
  hW : ∀ v : V, ((∃ e ∈ F, v ∈ e) ∨ ∃ u, Q.Adj v u ∧ P v = P u) →
    ∃ c ∈ C, (Tg Q F).edist c v ≤ (R : ℕ∞)

section cap

variable {Q : SimpleGraph V} {F : Finset (Sym2 V)} {P : V → Bool} {C : Finset V} {R : ℕ}

/-- interior -/
def Iset (Q : SimpleGraph V) (F : Finset (Sym2 V)) (C : Finset V) (R : ℕ) : Set V :=
  {v | delta (Tg Q F) C v < ((2 * R : ℕ) : ℕ∞)}

/-- sphere -/
def Sset (Q : SimpleGraph V) (F : Finset (Sym2 V)) (C : Finset V) (R : ℕ) : Set V :=
  {v | delta (Tg Q F) C v = ((2 * R : ℕ) : ℕ∞)}

/-- inner boundary -/
def Nset (Q : SimpleGraph V) (F : Finset (Sym2 V)) (C : Finset V) (R : ℕ) : Set V :=
  {u | delta (Tg Q F) C u < ((2 * R : ℕ) : ℕ∞) ∧
    ∃ v, (Tg Q F).Adj u v ∧ delta (Tg Q F) C v = ((2 * R : ℕ) : ℕ∞)}

lemma delta_layer (hd : CapData Q F P C R) {u v : V} (huv : (Tg Q F).Adj u v)
    (hu : delta (Tg Q F) C u ≤ ((2 * R : ℕ) : ℕ∞)) :
    delta (Tg Q F) C u ≠ delta (Tg Q F) C v := by
  intro heq
  have hne : delta (Tg Q F) C u ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hu
  obtain ⟨c, hc, hcu⟩ := delta_attained hne
  have hne' : delta (Tg Q F) C v ≠ ⊤ := heq ▸ hne
  obtain ⟨c', hc', hcv⟩ := delta_attained hne'
  obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.1 hne
  have hiR : i ≤ 2 * R := by
    have : (i : ℕ∞) ≤ ((2 * R : ℕ) : ℕ∞) := hi ▸ hu
    exact_mod_cast this
  have hcu' : (Tg Q F).edist c u = (i : ℕ∞) := by rw [hcu, hi]
  have hcv' : (Tg Q F).edist c' v = (i : ℕ∞) := by rw [hcv, ← heq, hi]
  by_cases hcc : c = c'
  · subst hcc
    obtain ⟨p, hp⟩ := (Tg Q F).exists_walk_of_edist_eq_coe hcu'
    obtain ⟨q, hq⟩ := (Tg Q F).exists_walk_of_edist_eq_coe hcv'
    let w : (Tg Q F).Walk c c := p.append (Walk.cons huv q.reverse)
    have hlen : w.length = 2 * i + 1 := by
      simp only [w, Walk.length_append, Walk.length_cons, Walk.length_reverse, hp, hq]
      omega
    have := hd.hodd c w (by rw [hlen]; exact ⟨i, rfl⟩)
    omega
  · have h1 := hd.hsep c hc c' hc' hcc
    have h2 : (Tg Q F).edist c c' ≤ ((2 * i + 1 : ℕ) : ℕ∞) := by
      calc (Tg Q F).edist c c' ≤ (Tg Q F).edist c u + (Tg Q F).edist u c' := (Tg Q F).edist_triangle
        _ ≤ (Tg Q F).edist c u + ((Tg Q F).edist u v + (Tg Q F).edist v c') := by
            gcongr
            exact (Tg Q F).edist_triangle
        _ = ((2 * i + 1 : ℕ) : ℕ∞) := by
            rw [hcu', edist_eq_one_iff_adj.2 huv, edist_comm (G := Tg Q F) (u := v) (v := c'), hcv']
            push_cast
            ring
    have h3 : ((2 * i + 1 : ℕ) : ℕ∞) ≤ ((4 * R + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast (by omega : 2 * i + 1 ≤ 4 * R + 1)
    exact absurd (lt_of_lt_of_le h1 (h2.trans h3)) (lt_irrefl _)


lemma mem_I_of_W (hd : CapData Q F P C R) {v : V}
    (hv : (∃ e ∈ F, v ∈ e) ∨ ∃ u, Q.Adj v u ∧ P v = P u) : v ∈ Iset Q F C R := by
  obtain ⟨c, hc, hcv⟩ := hd.hW v hv
  show delta (Tg Q F) C v < _
  calc delta (Tg Q F) C v ≤ (R : ℕ∞) := le_trans (delta_le hc) hcv
    _ < ((2 * R : ℕ) : ℕ∞) := by
      have := hd.hR
      exact_mod_cast (by omega : R < 2 * R)

lemma F_edge_in_I (hd : CapData Q F P C R) {u v : V} (h : s(u, v) ∈ F) :
    u ∈ Iset Q F C R ∧ v ∈ Iset Q F C R :=
  ⟨mem_I_of_W hd (Or.inl ⟨_, h, Sym2.mem_mk_left u v⟩),
   mem_I_of_W hd (Or.inl ⟨_, h, Sym2.mem_mk_right u v⟩)⟩

lemma mono_edge_in_I (hd : CapData Q F P C R) {u v : V} (h : Q.Adj u v) (hP : P u = P v) :
    u ∈ Iset Q F C R ∧ v ∈ Iset Q F C R :=
  ⟨mem_I_of_W hd (Or.inr ⟨v, h, hP⟩), mem_I_of_W hd (Or.inr ⟨u, h.symm, hP.symm⟩)⟩

lemma step_I_or_S {u v : V} (huv : (Tg Q F).Adj u v) (hu : u ∈ Iset Q F C R) :
    v ∈ Iset Q F C R ∨ v ∈ Sset Q F C R := by
  have h1 := delta_step (C := C) huv
  have h2 : delta (Tg Q F) C u + 1 ≤ ((2 * R : ℕ) : ℕ∞) := Order.add_one_le_of_lt hu
  rcases lt_or_eq_of_le (h1.trans h2) with h | h
  · exact Or.inl h
  · exact Or.inr h

lemma not_I_and_S {v : V} (h1 : v ∈ Iset Q F C R) (h2 : v ∈ Sset Q F C R) : False := by
  have h1' : delta (Tg Q F) C v < ((2 * R : ℕ) : ℕ∞) := h1
  have h2' : delta (Tg Q F) C v = ((2 * R : ℕ) : ℕ∞) := h2
  exact absurd h2' (ne_of_lt h1')

lemma S_S_nonadj (hd : CapData Q F P C R) {u v : V} (huv : (Tg Q F).Adj u v)
    (hu : u ∈ Sset Q F C R) (hv : v ∈ Sset Q F C R) : False := by
  have hu' : delta (Tg Q F) C u = ((2 * R : ℕ) : ℕ∞) := hu
  have hv' : delta (Tg Q F) C v = ((2 * R : ℕ) : ℕ∞) := hv
  exact delta_layer hd huv (le_of_eq hu') (hu'.trans hv'.symm)

theorem claim1 (hd : CapData Q F P C R) :
    Col3 (capGraph Q (Iset Q F C R) (Nset Q F C R)) → Col3 Q := by
  classical
  rintro ⟨g, hg⟩
  let σ : Equiv.Perm (Fin 3) := Equiv.swap (g none) 2
  let g' : Option V → Fin 3 := fun a => σ (g a)
  have hg' : ∀ a b, (capGraph Q (Iset Q F C R) (Nset Q F C R)).Adj a b → g' a ≠ g' b :=
    fun a b h => σ.injective.ne (hg a b h)
  have hgnone : g' none = 2 := by simp [g', σ]
  let col : V → Fin 3 := fun v =>
    if v ∈ Iset Q F C R then g' (some v)
    else if v ∈ Sset Q F C R then 2
    else if P v then 1 else 0
  have colI : ∀ v, v ∈ Iset Q F C R → col v = g' (some v) := fun v hv => by simp [col, hv]
  have colS : ∀ v, v ∉ Iset Q F C R → v ∈ Sset Q F C R → col v = 2 := fun v hv hs => by
    simp [col, hv, hs]
  have colO : ∀ v, v ∉ Iset Q F C R → v ∉ Sset Q F C R → col v = if P v then 1 else 0 :=
    fun v hv hs => by simp [col, hv, hs]
  -- key case: u ∈ I, v ∉ I
  have key1 : ∀ u v, Q.Adj u v → u ∈ Iset Q F C R → v ∉ Iset Q F C R → col u ≠ col v := by
    intro u v huv hu hv
    rcases adj_of_Q (F := F) huv with hT | hFe
    · have hvS : v ∈ Sset Q F C R := by
        rcases step_I_or_S hT hu with h | h
        · exact absurd h hv
        · exact h
      have huN : u ∈ Nset Q F C R := ⟨hu, v, hT, hvS⟩
      have := hg' (some u) none huN
      rw [colI u hu, colS v hv hvS, ← hgnone]
      exact this
    · exact absurd (F_edge_in_I hd hFe).2 hv
  refine ⟨col, ?_⟩
  intro u v huv
  by_cases hu : u ∈ Iset Q F C R
  · by_cases hv : v ∈ Iset Q F C R
    · rw [colI u hu, colI v hv]
      exact hg' (some u) (some v) ⟨hu, hv, huv⟩
    · exact key1 u v huv hu hv
  · by_cases hv : v ∈ Iset Q F C R
    · exact (key1 v u huv.symm hv hu).symm
    · rcases adj_of_Q (F := F) huv with hT | hFe
      · by_cases hus : u ∈ Sset Q F C R
        · by_cases hvs : v ∈ Sset Q F C R
          · exact (S_S_nonadj hd hT hus hvs).elim
          · rw [colS u hu hus, colO v hv hvs]
            cases P v <;> decide
        · by_cases hvs : v ∈ Sset Q F C R
          · rw [colO u hu hus, colS v hv hvs]
            cases P u <;> decide
          · rw [colO u hu hus, colO v hv hvs]
            intro heq
            have hPuv : P u = P v := by
              cases hPu : P u <;> cases hPv : P v <;> simp_all
            exact hu (mono_edge_in_I hd huv hPuv).1
      · exact absurd (F_edge_in_I hd hFe).1 hu

end cap

end E74
