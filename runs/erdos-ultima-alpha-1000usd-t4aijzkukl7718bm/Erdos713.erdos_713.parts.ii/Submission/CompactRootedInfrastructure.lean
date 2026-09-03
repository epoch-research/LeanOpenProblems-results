import FormalConjecturesUtil
import Submission.CompactPruningAudit

/-! Compact packing and bounded-blocker sampling infrastructure for rooted
gluing. Only the required portions of the earlier verified development are
included; this file does not import the admitted conjecture. -/
open Filter SimpleGraph Asymptotics Finset

namespace Erdos713Fan
structure Packing {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) (x : W) (v : V) (t : ℕ) where
  copies : Fin t → H.Copy G
  root : ∀ i, copies i x = v
  disjoint : ∀ i j, i ≠ j → ∀ a b, a ≠ x → b ≠ x → copies i a ≠ copies j b

def Packing.empty {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) (x : W) (v : V) :
    Packing H G x v 0 where
  copies := Fin.elim0
  root i := Fin.elim0 i
  disjoint i := Fin.elim0 i

noncomputable def Packing.blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) : Finset V := by
  classical
  exact univ.biUnion (fun i => (univ.filter (fun a => a ≠ x)).image (p.copies i))

lemma Packing.mem_blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) {z : V} :
    z ∈ p.blocker ↔ ∃ i a, a ≠ x ∧ p.copies i a = z := by
  classical
  simp [blocker]

lemma Packing.root_not_mem_blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) : v ∉ p.blocker := by
  rintro hv
  obtain ⟨i, a, ha, hav⟩ := p.mem_blocker.mp hv
  exact ha ((p.copies i).injective (hav.trans (p.root i).symm))

lemma Packing.card_blocker_le {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) : p.blocker.card ≤ t * Fintype.card W := by
  classical
  calc
    p.blocker.card ≤ ∑ i : Fin t, ((univ.filter (fun a => a ≠ x)).image (p.copies i)).card :=
      card_biUnion_le
    _ ≤ ∑ _ : Fin t, Fintype.card W := sum_le_sum fun _ _ =>
      (card_image_le).trans ((card_filter_le _ _).trans_eq (card_univ))
    _ = _ := by simp

noncomputable def Packing.cons {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) (f : H.Copy G) (hf : f x = v)
    (havoid : ∀ a, a ≠ x → f a ∉ p.blocker) : Packing H G x v (t + 1) where
  copies := Fin.cases f p.copies
  root i := by induction i using Fin.cases <;> simp [hf, p.root]
  disjoint i j hij a b ha hb := by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        intro hab
        exact havoid a ha (p.mem_blocker.mpr ⟨j, b, hb, hab.symm⟩)
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        intro hab
        exact havoid b hb (p.mem_blocker.mpr ⟨i, a, ha, hab⟩)
      | succ j =>
        simp only [Fin.cases_succ]
        exact p.disjoint i j (fun h => hij (congrArg Fin.succ h)) a b ha hb

theorem packing_or_blocker {W V : Type*} [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (x : W) (v : V) (t : ℕ) : Nonempty (Packing H G x v t) ∨
    ∃ B : Finset V, v ∉ B ∧ B.card ≤ t * Fintype.card W ∧
      ∀ f : H.Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B := by
  classical
  induction t with
  | zero => exact Or.inl ⟨Packing.empty H G x v⟩
  | succ t ih =>
    rcases ih with hp | ⟨B, hv, hc, hB⟩
    · obtain ⟨p⟩ := hp
      change Packing H G x v t at p
      by_cases h : ∃ f : H.Copy G, f x = v ∧ ∀ a, a ≠ x → f a ∉ p.blocker
      · obtain ⟨f, hf, havoid⟩ := h
        exact Or.inl ⟨p.cons f hf havoid⟩
      · right
        refine ⟨p.blocker, p.root_not_mem_blocker, p.card_blocker_le.trans ?_, ?_⟩
        · exact Nat.mul_le_mul_right _ (Nat.le_succ _)
        · intro f hf
          have hh : ¬∀ a, a ≠ x → f a ∉ p.blocker := fun hh => h ⟨f, hf, hh⟩
          push_neg at hh
          exact hh
    · exact Or.inr ⟨B, hv, hc.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)), hB⟩


end Erdos713Fan

namespace Erdos713Blocking
open Finset

theorem card_fixed_pattern {V K : Type*} [Fintype V] [Fintype K] (S : Set V) (p : V → K) :
    Nat.card {f : V → K // ∀ v ∈ S, f v = p v} =
      Nat.card K ^ (Nat.card V - Nat.card S) := by
  classical
  let e : {f : V → K // ∀ v ∈ S, f v = p v} ≃ (↥(Sᶜ) → K) :=
    { toFun := fun f i => f.val i.val
      invFun := fun f => ⟨fun i => if h : i ∈ S then p i else f ⟨i, h⟩, by
        intro i hi
        simp only [dif_pos hi]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simpa only [dif_pos hi] using (f.prop i hi).symm
        · simp only [dif_neg hi]
      right_inv := by
        intro f
        funext i
        simp only [dif_neg i.prop] }
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_compl_set]

def selected {V : Type*} (B : V → Finset V) (σ : V → Bool) (v : V) : Prop :=
  σ v = true ∧ ∀ w ∈ B v, σ w = false

def keep {V : Type*} (G : SimpleGraph V) (B : V → Finset V) (σ : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ selected B σ u ∧ selected B σ v
  symm _ _ huv := ⟨huv.1.symm, huv.2.2, huv.2.1⟩
  loopless u huv := G.loopless u huv.1

theorem keep_le {V : Type*} (G : SimpleGraph V) (B : V → Finset V) (σ : V → Bool) : keep G B σ ≤ G :=
  fun _ _ huv => huv.1

open scoped Classical in
set_option maxHeartbeats 1000000 in
theorem pair_survival {V : Type*} [Fintype V] (B : V → Finset V) (k : ℕ)
    (hk : ∀ v, (B v).card ≤ k) {u v : V}
    (huu : u ∉ B u) (hvv : v ∉ B v) (huv : v ∉ B u) (hvu : u ∉ B v) :
    Fintype.card (V → Bool) ≤ 2 ^ (2 * k + 2) *
      Nat.card {σ : V → Bool // selected B σ u ∧ selected B σ v} := by
  classical
  let T : Finset V := insert u (insert v (B u ∪ B v))
  let p : V → Bool := fun z => if z = u ∨ z = v then true else false
  have hT : T.card ≤ 2 * k + 2 := by
    have hh := card_insert_le u (insert v (B u ∪ B v))
    have hi := card_insert_le v (B u ∪ B v)
    have hj := card_union_le (B u) (B v)
    dsimp only [T]
    have hku := hk u
    have hkv := hk v
    omega
  have hTn : T.card ≤ Fintype.card V := card_le_univ _
  have hp : ∀ σ : V → Bool, (∀ z ∈ T, σ z = p z) → selected B σ u ∧ selected B σ v := by
    intro σ hσ
    have hu : σ u = true := by simpa only [p, if_pos (Or.inl rfl)] using hσ u (by simp [T])
    have hv : σ v = true := by simpa only [p, if_pos (Or.inr rfl)] using hσ v (by simp [T])
    refine ⟨⟨hu, ?_⟩, ⟨hv, ?_⟩⟩
    · intro z hz
      have hzu : z ≠ u := fun he => huu (he ▸ hz)
      have hzv : z ≠ v := fun he => huv (he ▸ hz)
      simpa only [p, hzu, hzv, or_self, if_false] using hσ z (by simp [T, hz])
    · intro z hz
      have hzu : z ≠ u := fun he => hvu (he ▸ hz)
      have hzv : z ≠ v := fun he => hvv (he ▸ hz)
      simpa only [p, hzu, hzv, or_self, if_false] using hσ z (by simp [T, hz])
  have hcard : 2 ^ (Fintype.card V - T.card) ≤
      Nat.card {σ : V → Bool // selected B σ u ∧ selected B σ v} := by
    let e : {σ : V → Bool // ∀ z ∈ T, σ z = p z} ↪
        {σ : V → Bool // selected B σ u ∧ selected B σ v} :=
      ⟨fun σ => ⟨σ.val, hp σ.val σ.prop⟩, by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun σ : {σ : V → Bool // selected B σ u ∧ selected B σ v} => σ.val) h⟩
    have hh := Fintype.card_le_of_embedding e
    simp only [Fintype.card_eq_nat_card] at hh
    have hf : Nat.card {σ : V → Bool // ∀ z ∈ T, σ z = p z} =
        2 ^ (Fintype.card V - T.card) := by
      have hfixed := card_fixed_pattern (T : Set V) p
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at hfixed
      simpa only [mem_coe, Nat.card_eq_fintype_card, Fintype.card_bool] using hfixed
    exact hf ▸ hh
  calc
    Fintype.card (V → Bool) = 2 ^ Fintype.card V := by simp
    _ = 2 ^ T.card * 2 ^ (Fintype.card V - T.card) := by
      rw [← pow_add, Nat.add_sub_of_le hTn]
    _ ≤ 2 ^ (2 * k + 2) * Nat.card {σ : V → Bool // selected B σ u ∧ selected B σ v} :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hT) hcard

open scoped Classical in
set_option maxHeartbeats 2000000 in
theorem edges_le_of_keep_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (B : V → Finset V) (k M : ℕ) (hb : ∀ v, v ∉ B v) (hk : ∀ v, (B v).card ≤ k)
    (hM : ∀ σ : V → Bool, (keep G B σ).edgeFinset.card ≤ M) :
    G.edgeFinset.card ≤ 2 ^ (2 * k + 2) * M + k * Fintype.card V := by
  classical
  let D : Finset (Sym2 V) := univ.biUnion (fun u => (B u).image (fun v => s(u,v)))
  let E : Finset (Sym2 V) := G.edgeFinset \ D
  let C := 2 ^ (2 * k + 2)
  let A := Fintype.card (V → Bool)
  let rel : (V → Bool) → Sym2 V → Prop := fun σ e => e ∈ (keep G B σ).edgeFinset
  have hD : D.card ≤ k * Fintype.card V := by
    calc
      D.card ≤ ∑ u, ((B u).image (fun v => s(u,v))).card := card_biUnion_le
      _ ≤ ∑ u : V, k := sum_le_sum fun u _ => card_image_le.trans (hk u)
      _ = _ := by simp [Nat.mul_comm]
  have hBelow : ∀ e ∈ E, A ≤ C * ((univ : Finset (V → Bool)).bipartiteBelow rel e).card := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hgood : s(u,v) ∈ G.edgeFinset ∧ s(u,v) ∉ D := mem_sdiff.mp he
      have hadj : G.Adj u v := by simpa using hgood.1
      have huv : v ∉ B u := by
        intro hh
        apply hgood.2
        exact mem_biUnion.mpr ⟨u, mem_univ _, mem_image.mpr ⟨v, hh, rfl⟩⟩
      have hvu : u ∉ B v := by
        intro hh
        apply hgood.2
        exact mem_biUnion.mpr ⟨v, mem_univ _, mem_image.mpr ⟨u, hh, by simp⟩⟩
      have hrel (σ : V → Bool) : rel σ s(u,v) ↔ selected B σ u ∧ selected B σ v := by
        change (s(u,v) ∈ (keep G B σ).edgeFinset) ↔ _
        simp only [mem_edgeFinset, mem_edgeSet, keep, hadj, true_and]
      have hh := pair_survival B k hk (hb u) (hb v) huv hvu
      simpa only [A, C, Nat.card_eq_fintype_card, Fintype.card_subtype, bipartiteBelow, hrel] using hh
  have hAbove (σ : V → Bool) : (E.bipartiteAbove rel σ).card ≤ M := by
    apply (card_le_card (show E.bipartiteAbove rel σ ⊆ (keep G B σ).edgeFinset from ?_)).trans (hM σ)
    intro e he
    exact (mem_filter.mp he).2
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := (univ : Finset (V → Bool))) (t := E)
  have hCount : E.card * A ≤ C * (A * M) := by
    calc
      E.card * A = ∑ _e ∈ E, A := by simp
      _ ≤ ∑ e ∈ E, C * ((univ : Finset (V → Bool)).bipartiteBelow rel e).card :=
        sum_le_sum hBelow
      _ = C * ∑ σ : V → Bool, (E.bipartiteAbove rel σ).card := by
        rw [← mul_sum, ← hsum]
      _ ≤ C * ∑ _σ : V → Bool, M := Nat.mul_le_mul_left C (sum_le_sum fun σ _ => hAbove σ)
      _ = C * (A * M) := by simp [A]
  have hA : 0 < A := Fintype.card_pos
  have hE : E.card ≤ C * M := Nat.le_of_mul_le_mul_left
    (show A * E.card ≤ A * (C * M) by nlinarith only [hCount]) hA
  exact (card_le_card_sdiff_add_card (s := G.edgeFinset) (t := D)).trans (Nat.add_le_add hE hD)


end Erdos713Blocking

namespace Erdos713Gluing
open Finset Erdos713Fan Erdos713Rate Erdos713Blocking
universe u v

abbrev Vertex {W T : Type*} (_x : W) (y : T) := W ⊕ {b : T // b ≠ y}

def wedge {W T : Type*} (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T) :
    SimpleGraph (Vertex x y) where
  Adj
    | Sum.inl a, Sum.inl b => H.Adj a b
    | Sum.inl a, Sum.inr b => a = x ∧ J.Adj y b.val
    | Sum.inr a, Sum.inl b => b = x ∧ J.Adj a.val y
    | Sum.inr a, Sum.inr b => J.Adj a.val b.val
  symm := by
    rintro (a | a) (b | b) hab
    · exact hab.symm
    · exact ⟨hab.1, hab.2.symm⟩
    · exact ⟨hab.1, hab.2.symm⟩
    · exact hab.symm
  loopless := by
    rintro (a | a) haa
    · exact H.loopless a haa
    · exact J.loopless a.val haa

def leftCopy {W T : Type*} (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T) :
    H.Copy (wedge H x J y) := ⟨⟨Sum.inl, fun hab => hab⟩, Sum.inl_injective⟩

noncomputable def rightCopy {W T : Type*} (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T) :
    J.Copy (wedge H x J y) := by
  classical
  let f : T → Vertex x y := fun b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro a b hab
    by_cases ha : a = y <;> by_cases hb : b = y
    · subst a; subst b; exact (J.loopless _ hab).elim
    · subst a; simpa [f, wedge, hb] using hab
    · subst b; simpa [f, wedge, ha] using hab
    · simpa [f, wedge, ha, hb] using hab
  · intro a b hab
    change f a = f b at hab
    by_cases ha : a = y <;> by_cases hb : b = y
    · exact ha.trans hb.symm
    · simp [f, ha, hb] at hab
    · simp [f, ha, hb] at hab
    · simpa [f, ha, hb] using hab

noncomputable def commonRootCopy {W T V : Type*} {H : SimpleGraph W} {J : SimpleGraph T}
    {G : SimpleGraph V} {x : W} {y : T} (f : H.Copy G) (g : J.Copy G)
    (hroot : f x = g y) (hdis : ∀ a b, b ≠ y → f a ≠ g b) : (wedge H x J y).Copy G := by
  let F : Vertex x y → V := Sum.elim f (fun b => g b.val)
  refine ⟨⟨F, ?_⟩, ?_⟩
  · rintro (a | a) (b | b) hab
    · exact f.toHom.map_adj hab
    · change G.Adj (f a) (g b.val)
      obtain ⟨rfl, hab⟩ := hab
      rw [hroot]
      exact g.toHom.map_adj hab
    · change G.Adj (g a.val) (f b)
      obtain ⟨rfl, hab⟩ := hab
      rw [hroot]
      exact g.toHom.map_adj hab
    · exact g.toHom.map_adj hab
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (f.injective hab)
    · exact (hdis a b.val b.prop hab).elim
    · exact (hdis b a.val a.prop hab.symm).elim
    · exact congrArg Sum.inr (Subtype.ext (g.injective hab))

theorem exists_disjoint_petal {W T V : Type*} [Fintype T] {H : SimpleGraph W} {J : SimpleGraph T}
    {G : SimpleGraph V} {x : W} {z : V}
    (p : Packing H G x z (Fintype.card T + 1)) (g : J.Copy G) :
    ∃ i, ∀ a, a ≠ x → ∀ b, p.copies i a ≠ g b := by
  classical
  by_contra hh
  push_neg at hh
  choose a ha b hab using hh
  have hinj : Function.Injective b := by
    intro i j hij
    by_contra hne
    exact p.disjoint i j hne (a i) (a j) (ha i) (ha j)
      ((hab i).trans ((congrArg g hij).trans (hab j).symm))
  have hc := Fintype.card_le_of_injective b hinj
  simp only [Fintype.card_fin] at hc
  omega

theorem contained_of_packing {W T V : Type*} [Fintype T] {H : SimpleGraph W} {J : SimpleGraph T}
    {G : SimpleGraph V} {x : W} {y : T} {z : V}
    (p : Packing H G x z (Fintype.card T + 1)) (g : J.Copy G) (hg : g y = z) :
    wedge H x J y ⊑ G := by
  classical
  obtain ⟨i, hi⟩ := exists_disjoint_petal p g
  refine ⟨commonRootCopy (p.copies i) g ((p.root i).trans hg.symm) ?_⟩
  intro a b hb
  by_cases ha : a = x
  · subst a
    intro hab
    have hh : g y = g b := hg.trans ((p.root i).symm.trans hab)
    exact hb (g.injective hh).symm
  · exact hi a ha b

theorem blockers_or_no_right {W T V : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T) (G : SimpleGraph V)
    (hfree : (wedge H x J y).Free G) : ∀ v, ∃ B : Finset V,
    v ∉ B ∧ B.card ≤ (Fintype.card T + 1) * Fintype.card W ∧
      ((∀ f : H.Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B) ∨
       (∀ g : J.Copy G, g y = v → False)) := by
  intro v
  rcases packing_or_blocker H G x v (Fintype.card T + 1) with hp | ⟨B, hv, hc, hB⟩
  · obtain ⟨p⟩ := hp
    refine ⟨∅, by simp, by simp, Or.inr ?_⟩
    intro g hg
    exact hfree (contained_of_packing p g hg)
  · exact ⟨B, hv, hc, Or.inl hB⟩

def rest {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm _ _ huv := ⟨huv.1.symm, huv.2.2, huv.2.1⟩
  loopless u huv := G.loopless u huv.1

lemma rest_le {V : Type*} (G : SimpleGraph V) (S : Set V) : rest G S ≤ G := fun _ _ h => h.1

end Erdos713Gluing

namespace Erdos713SwitchGluing
open Erdos713Gluing
def inside {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless u h := G.loopless u h.1

def cross {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S))
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless u h := G.loopless u h.1

lemma inside_le {V : Type*} (G : SimpleGraph V) (S : Set V) : inside G S ≤ G := fun _ _ h => h.1

lemma cross_le {V : Type*} (G : SimpleGraph V) (S : Set V) : cross G S ≤ G := fun _ _ h => h.1

open scoped Classical in
lemma edge_split {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    G.edgeFinset.card ≤ (inside G S).edgeFinset.card + (cross G S).edgeFinset.card +
      (rest G S).edgeFinset.card := by
  classical
  apply (card_le_card (show G.edgeFinset ⊆
      (inside G S).edgeFinset ∪ (cross G S).edgeFinset ∪ (rest G S).edgeFinset from ?_)).trans
    ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := by simpa using he
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
      simp [inside, cross, rest, huv, hu, hv]


end Erdos713SwitchGluing
