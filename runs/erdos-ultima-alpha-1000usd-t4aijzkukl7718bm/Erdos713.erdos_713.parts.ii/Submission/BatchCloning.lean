import FormalConjecturesUtil
import Submission.QuantitativeRobustCopies

/-! Partial clones may interact. Every obstruction has a reduced witness
in which each used clone is paired with its old root. -/
open SimpleGraph Finset
namespace Erdos713BatchCloning

variable {V W : Type*}

def graph (G : SimpleGraph V) (P : V → V → Prop) : SimpleGraph (V ⊕ V) where
  Adj
    | .inl u,.inl v => G.Adj u v
    | .inr u,.inl v => P u v
    | .inl u,.inr v => P v u
    | .inr _,.inr _ => False
  symm := by rintro (u|u) (v|v) h <;> first | exact h | exact h.symm
  loopless := by rintro (u|u) h; exact G.loopless u h; exact h

open scoped Classical in
noncomputable def retract (v : V) : V ⊕ V → V ⊕ V
  | .inl w => .inl w
  | .inr w => if w = v then .inl w else .inr w

noncomputable def retractHom (G : SimpleGraph V) (P : V → V → Prop)
    (hP : ∀ u v, P u v → G.Adj u v) (v : V) : graph G P →g graph G P := by
  classical
  refine ⟨retract v,?_⟩
  rintro (a|a) (b|b) h
  · exact h
  · change (graph G P).Adj (.inl a) (if b=v then .inl b else .inr b)
    split_ifs
    · exact (hP _ _ h).symm
    · exact h
  · change (graph G P).Adj (if a=v then .inl a else .inr a) (.inl b)
    split_ifs
    · exact hP _ _ h
    · exact h
  · exact h.elim

lemma retract_injective_off_old (v : V) :
    Set.InjOn (retract v) {z : V ⊕ V | z ≠ .inl v} := by
  classical
  rintro (a|a) ha (b|b) hb h
  all_goals
    dsimp only [retract] at h
    first | exact h | (split_ifs at h <;> simp_all)

lemma retract_new {v : V} {z : V ⊕ V} {w : V}
    (h : retract v z = .inr w) : z = .inr w := by
  classical
  rcases z with z|z
  · simp [retract] at h
  · dsimp only [retract] at h
    split_ifs at h <;> simp_all

/-- The ambient graph contains all clones, but only clones indexed by S
may occur in the copy. This is equivalent to a copy in the selected batch. -/
def Allowed {H : SimpleGraph W} {G : SimpleGraph V} {P : V → V → Prop}
    (S : Finset V) (f : H.Copy (graph G P)) : Prop :=
  ∀ w v, f w = .inr v → v ∈ S

def ContainsWithNew (H : SimpleGraph W) (G : SimpleGraph V) (P : V → V → Prop)
    (S : Finset V) : Prop := ∃ f : H.Copy (graph G P), Allowed S f

open scoped Classical in
noncomputable def newDomain [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {P : V → V → Prop} (f : H.Copy (graph G P)) : Finset W :=
  univ.filter (fun w => ∃ v, f w = .inr v)

open scoped Classical in
noncomputable def roots [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {P : V → V → Prop} (f : H.Copy (graph G P)) : Finset V :=
  univ.filter (fun v => ∃ w, f w = .inr v)

lemma mem_newDomain [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {P : V → V → Prop} (f : H.Copy (graph G P)) (w : W) :
    w ∈ newDomain f ↔ ∃ v, f w = .inr v := by
  classical
  simp only [newDomain,mem_filter,mem_univ,true_and]

lemma mem_roots [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {P : V → V → Prop} (f : H.Copy (graph G P)) (v : V) :
    v ∈ roots f ↔ ∃ w, f w = .inr v := by
  classical
  simp only [roots,mem_filter,mem_univ,true_and]

lemma paired_copy [Fintype V] [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (P : V → V → Prop) (hP : ∀ u v, P u v → G.Adj u v) (S : Finset V)
    (h : ContainsWithNew H G P S) :
    ∃ f : H.Copy (graph G P), Allowed S f ∧
      ∀ v, (∃ w, f w = .inr v) → ∃ w, f w = .inl v := by
  classical
  let F : Finset (H.Copy (graph G P)) := univ.filter (Allowed S)
  have hF : F.Nonempty := by obtain ⟨f,hf⟩ := h; exact ⟨f,by simpa [F] using hf⟩
  obtain ⟨f,hf,hmin⟩ := F.exists_min_image (fun f => (newDomain f).card) hF
  have ha : Allowed S f := by simpa [F] using hf
  refine ⟨f,ha,?_⟩
  intro v hv
  by_contra hmissing
  have hnot (w : W) : f w ≠ .inl v := fun hw => hmissing ⟨w,hw⟩
  let g : H.Copy (graph G P) := ⟨(retractHom G P hP v).comp f.toHom,by
    intro a b hab
    exact f.injective (retract_injective_off_old v (hnot a) (hnot b) hab)⟩
  have hg : Allowed S g := by
    intro w z hwz
    exact ha w z (retract_new hwz)
  have hgF : g ∈ F := by simpa [F] using hg
  have hsub : newDomain g ⊆ newDomain f := by
    intro w hw
    obtain ⟨z,hz⟩ := (mem_newDomain g w).mp hw
    exact (mem_newDomain f w).mpr ⟨z,retract_new hz⟩
  obtain ⟨w,hw⟩ := hv
  have hwf : w ∈ newDomain f := (mem_newDomain f w).mpr ⟨v,hw⟩
  have hwg : w ∉ newDomain g := by
    intro hmem
    obtain ⟨z,hz⟩ := (mem_newDomain g w).mp hmem
    change retract v (f w) = .inr z at hz
    simp [hw,retract] at hz
  have hlt : (newDomain g).card < (newDomain f).card :=
    card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun he => hwg (he.symm ▸ hwf)⟩)
  exact (not_lt_of_ge (hmin g hgF)) hlt

lemma paired_card [Fintype V] [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {P : V → V → Prop} (f : H.Copy (graph G P))
    (hp : ∀ v, (∃ w, f w = .inr v) → ∃ w, f w = .inl v) :
    2*(roots f).card ≤ Fintype.card W := by
  classical
  have hn (v : roots f) : ∃ w, f w = .inr v.val := (mem_roots f v.val).mp v.property
  have ho (v : roots f) : ∃ w, f w = .inl v.val := hp v.val (hn v)
  choose a ha using ho
  choose b hb using hn
  let e : (roots f) ⊕ (roots f) ↪ W := ⟨Sum.elim a b,by
    rintro (x|x) (y|y) h
    all_goals
      have h' := congrArg f h
      simp only [Sum.elim_inl,Sum.elim_inr,ha,hb] at h'
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h'))
    · cases h'
    · cases h'
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h'))⟩
  have he := Fintype.card_le_of_embedding e
  simpa only [Fintype.card_sum,Fintype.card_coe,two_mul] using he

/-- All batch obstructions have a witness using at most half as many
clones as the forbidden graph has vertices. -/
theorem contains_iff_small_batch [Fintype V] [Fintype W] (H : SimpleGraph W)
    (G : SimpleGraph V) (P : V → V → Prop) (hP : ∀ u v, P u v → G.Adj u v)
    (S : Finset V) :
    ContainsWithNew H G P S ↔ ∃ T : Finset V, T ⊆ S ∧
      2*T.card ≤ Fintype.card W ∧ ContainsWithNew H G P T := by
  constructor
  · intro h
    obtain ⟨f,hf,hp⟩ := paired_copy H G P hP S h
    refine ⟨roots f,?_,paired_card f hp,f,?_⟩
    · intro v hv
      obtain ⟨w,hw⟩ := (mem_roots f v).mp hv
      exact hf w v hw
    · intro w v hw
      exact (mem_roots f v).mpr ⟨w,hw⟩
  · rintro ⟨T,hTS,_,f,hf⟩
    exact ⟨f,fun w v hw => hTS (hf w v hw)⟩

lemma card_le_of_contains [Fintype V] [Fintype W] {H : SimpleGraph W}
    {G : SimpleGraph V} {P : V → V → Prop} {S : Finset V}
    (h : ContainsWithNew H G P S) : Fintype.card W ≤ Fintype.card V+S.card := by
  classical
  obtain ⟨f,hf⟩ := h
  let lift (w : W) : V ⊕ S := match he : f w with
    | .inl v => .inl v
    | .inr v => .inr ⟨v,hf w v he⟩
  have hlift (w : W) : Sum.map id Subtype.val (lift w) = f w := by
    dsimp only [lift]
    split <;> simp_all
  have hinj : Function.Injective lift := by
    intro u v huv
    apply f.injective
    simpa only [hlift] using congrArg (Sum.map id Subtype.val) huv
  have hh := Fintype.card_le_of_injective lift hinj
  simpa only [Fintype.card_sum,Fintype.card_coe] using hh

/-- Even two individually safe full clones can interact. This is an
auxiliary counterexample, not a disproof of the rationality conjecture. -/
theorem single_safe_not_joint :
    ∃ (G : SimpleGraph (Fin 2 ⊕ Fin 4)) (S : Finset (Fin 2 ⊕ Fin 4)),
      S.card = 2 ∧
      (∀ v ∈ S, ¬ ContainsWithNew (completeBipartiteGraph (Fin 4) (Fin 4)) G G.Adj {v}) ∧
      ContainsWithNew (completeBipartiteGraph (Fin 4) (Fin 4)) G G.Adj S := by
  classical
  let G := completeBipartiteGraph (Fin 2) (Fin 4)
  let H := completeBipartiteGraph (Fin 4) (Fin 4)
  let S : Finset (Fin 2 ⊕ Fin 4) := {.inl 0,.inl 1}
  have hsingle (v : Fin 2 ⊕ Fin 4) : ¬ ContainsWithNew H G G.Adj {v} := by
    intro h
    have hh := card_le_of_contains h
    norm_num at hh
  let L : Fin 4 → (Fin 2 ⊕ Fin 4) ⊕ (Fin 2 ⊕ Fin 4) :=
    ![.inl (.inl 0),.inr (.inl 0),.inl (.inl 1),.inr (.inl 1)]
  have hL : Function.Injective L := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [L]
  have hadj (i j : Fin 4) : (graph G G.Adj).Adj (L i) (.inl (.inr j)) := by
    fin_cases i <;> simp [L,graph,G,completeBipartiteGraph]
  let f : H.Copy (graph G G.Adj) := ⟨⟨Sum.elim L (fun j => .inl (.inr j)),by
    rintro (i|j) (i'|j') h
    · simp [H,completeBipartiteGraph] at h
    · exact hadj i j'
    · exact (hadj i' j).symm
    · simp [H,completeBipartiteGraph] at h⟩,by
      rintro (i|j) (i'|j') h
      · exact congrArg Sum.inl (hL h)
      · change L i = .inl (.inr j') at h
        fin_cases i <;> simp [L] at h
      · change .inl (.inr j) = L i' at h
        fin_cases i' <;> simp [L] at h
      · exact congrArg Sum.inr (Sum.inr.inj (Sum.inl.inj h))⟩
  refine ⟨G,S,by simp [S],fun v _ => hsingle v,f,?_⟩
  rintro (i|j) v h
  · change L i = .inr v at h
    fin_cases i <;> simp_all [L,S]
  · change (Sum.inl (.inr j) : (Fin 2 ⊕ Fin 4) ⊕ (Fin 2 ⊕ Fin 4)) = .inr v at h
    cases h

#print axioms card_le_of_contains
#print axioms single_safe_not_joint
#print axioms paired_copy
#print axioms paired_card
#print axioms contains_iff_small_batch
end Erdos713BatchCloning
