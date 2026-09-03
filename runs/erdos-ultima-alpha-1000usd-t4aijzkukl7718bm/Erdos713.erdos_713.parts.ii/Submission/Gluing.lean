import FormalConjecturesUtil
import Submission.Latest

/-! Gluing graphs at a distinguished vertex, and a packing criterion for copies. -/

open Filter SimpleGraph Asymptotics

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

def touch {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∈ S ∨ v ∈ S)
  symm _ _ huv := ⟨huv.1.symm, huv.2.symm⟩
  loopless u huv := G.loopless u huv.1

def rest {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm _ _ huv := ⟨huv.1.symm, huv.2.2, huv.2.1⟩
  loopless u huv := G.loopless u huv.1

theorem touch_le {V : Type*} (G : SimpleGraph V) (S : Set V) : touch G S ≤ G := fun _ _ h => h.1

theorem rest_le {V : Type*} (G : SimpleGraph V) (S : Set V) : rest G S ≤ G := fun _ _ h => h.1

open scoped Classical in
theorem edge_split {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    G.edgeFinset.card ≤ (touch G S).edgeFinset.card + (rest G S).edgeFinset.card := by
  classical
  apply (card_le_card (show G.edgeFinset ⊆ (touch G S).edgeFinset ∪ (rest G S).edgeFinset from ?_)).trans
    (card_union_le _ _)
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := by simpa using he
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
      simp [touch, rest, huv, hu, hv]

theorem no_isolates_of_root_movable {W : Type*} (H : SimpleGraph W) (x : W)
    (hMove : ∀ a, ∃ e : H ≃g H, e x = a) (hx : ∃ b, H.Adj x b) : ∀ a, ∃ b, H.Adj a b := by
  intro a
  obtain ⟨b, hxb⟩ := hx
  obtain ⟨e, he⟩ := hMove a
  refine ⟨e b, ?_⟩
  have hh : H.Adj (e x) (e b) := e.toCopy.toHom.map_adj hxb
  simpa only [he] using hh

open scoped Classical in
set_option maxHeartbeats 2000000 in
theorem free_edge_bound {W T V : Type*} [Fintype W] [Fintype T] [Fintype V]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T) (G : SimpleGraph V)
    (hMove : ∀ a, ∃ e : H ≃g H, e x = a) (hx : ∃ b, H.Adj x b)
    (hfree : (wedge H x J y).Free G) :
    G.edgeFinset.card ≤ 2 ^ (2 * ((Fintype.card T + 1) * Fintype.card W) + 2) *
      (extremalNumber (Fintype.card V) H + extremalNumber (Fintype.card V) J +
        Fintype.card T * Fintype.card V) +
      ((Fintype.card T + 1) * Fintype.card W) * Fintype.card V := by
  classical
  choose B hb hk hB using blockers_or_no_right H x J y G hfree
  let S : Set V := {v | ∀ f : H.Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B v}
  have hNoJ (v : V) (hv : v ∉ S) (g : J.Copy G) (hg : g y = v) : False := by
    rcases hB v with hleft | hright
    · exact hv hleft
    · exact hright g hg
  have hNoIso := no_isolates_of_root_movable H x hMove hx
  apply edges_le_of_keep_bound G B ((Fintype.card T + 1) * Fintype.card W) _ hb hk
  intro σ
  let K := keep G B σ
  have hsel (f : H.Copy K) (a : W) : selected B σ (f a) := by
    obtain ⟨b, hab⟩ := hNoIso a
    exact (f.toHom.map_adj hab).2.1
  have hRoots (f : H.Copy K) (a : W) : f a ∉ S := by
    intro hfa
    obtain ⟨e, he⟩ := hMove a
    let g : H.Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp (f.comp e.toCopy)
    have hroot : g x = f a := by change f (e x) = f a; rw [he]
    obtain ⟨b, _, hmem⟩ := hfa g hroot
    change f (e b) ∈ B (f a) at hmem
    exact Bool.noConfusion ((hsel f (e b)).1.symm.trans ((hsel f a).2 (f (e b)) hmem))
  have hTouch : H.Free (touch K S) := by
    rintro ⟨f⟩
    let g : H.Copy K := (Copy.ofLE _ _ (touch_le K S)).comp f
    obtain ⟨b, hxb⟩ := hx
    have hm := f.toHom.map_adj hxb
    rcases hm.2 with hxS | hbS
    · exact hRoots g x hxS
    · exact hRoots g b hbS
  have hRest : J.Free ((rest K S).induce Sᶜ) := by
    rintro ⟨f⟩
    let g : J.Copy G := (Copy.ofLE _ _ ((rest_le K S).trans (keep_le G B σ))).comp
      ((Copy.induce _ _).comp f)
    exact hNoJ (f y).val (f y).prop g rfl
  have hSupp : (rest K S).support ⊆ Sᶜ := by
    rintro v ⟨w, hvw⟩
    exact hvw.2.1
  have hA := card_edgeFinset_le_extremalNumber hTouch
  have hB := Erdos713Support.edges_le_of_free_induce J (rest K S) Sᶜ hSupp hRest
  have hSplit := edge_split K S
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hA hB hSplit ⊢
  dsimp only [K] at hA hB hSplit
  omega

open scoped Classical in
theorem extremal_bound {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hMove : ∀ a, ∃ e : H ≃g H, e x = a) (hx : ∃ b, H.Adj x b) (n : ℕ) :
    extremalNumber n (wedge H x J y) ≤ 2 ^ (2 * ((Fintype.card T + 1) * Fintype.card W) + 2) *
      (extremalNumber n H + extremalNumber n J + Fintype.card T * n) +
      ((Fintype.card T + 1) * Fintype.card W) * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using free_edge_bound H x J y G hMove hx hfree

theorem wedge_upper {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hMove : ∀ a, ∃ e : H ≃g H, e x = a) (hx : ∃ b, H.Adj x b)
    {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hJ : (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ b)) :
    (fun n : ℕ => (extremalNumber n (wedge H x J y) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (max a b)) := by
  let k := (Fintype.card T + 1) * Fintype.card W
  let C : ℕ := 2 ^ (2 * k + 2)
  have hH' := hH.trans (rpow_mono_bigO (le_max_left a b))
  have hJ' := hJ.trans (rpow_mono_bigO (le_max_right a b))
  have hL := cast_linear_bigO (ha.trans (le_max_left a b)) (Fintype.card T)
  have hA := ((hH'.add hJ').add hL).const_mul_left (C : ℝ)
  have hB := cast_linear_bigO (ha.trans (le_max_left a b)) k
  apply IsBigO.trans _ (hA.add hB)
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast extremal_bound H x J y hMove hx n

theorem wedge_rate {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hMove : ∀ a, ∃ e : H ≃g H, e x = a) (hx : ∃ b, H.Adj x b)
    {a b : ℝ} (hH : HasRate H a) (hJ : HasRate J b) : HasRate (wedge H x J y) (max a b) := by
  refine ⟨hH.one_le.trans (le_max_left a b),
    wedge_upper H x J y hMove hx hH.one_le hJ.one_le hH.upper hJ.upper, ?_⟩
  intro c hc hC
  apply max_le
  · exact hH.lower c hc ((extremal_mono_bigO ⟨leftCopy H x J y⟩).trans hC)
  · exact hJ.lower c hc ((extremal_mono_bigO ⟨rightCopy H x J y⟩).trans hC)

theorem rate_wedge_or {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hMove : ∀ a, ∃ e : H ≃g H, e x = a) (hx : ∃ b, H.Adj x b)
    {r : ℝ} (h : HasRate (wedge H x J y) r) : HasRate H r ∨ HasRate J r := by
  classical
  have huH := (extremal_mono_bigO ⟨leftCopy H x J y⟩).trans h.upper
  have huJ := (extremal_mono_bigO ⟨rightCopy H x J y⟩).trans h.upper
  by_cases hH : HasRate H r
  · exact Or.inl hH
  right
  refine ⟨h.one_le, huJ, ?_⟩
  intro b hb hB
  by_contra hbr
  have hg : ¬∀ a : ℝ, 1 ≤ a →
      ((fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ a)) → r ≤ a := fun hh => hH ⟨h.one_le, huH, hh⟩
  push_neg at hg
  obtain ⟨a, ha, hA, har⟩ := hg
  have hh := h.lower (max a b) (ha.trans (le_max_left _ _))
    (wedge_upper H x J y hMove hx ha hb hA hB)
  exact (not_lt.mpr hh) (max_lt har (lt_of_not_ge hbr))

theorem cycle_root_move (n : ℕ) (x a : Fin n) :
    ∃ e : cycleGraph n ≃g cycleGraph n, e x = a := by
  cases n with
  | zero => exact x.elim0
  | succ n =>
    let e : cycleGraph (n + 1) ≃g cycleGraph (n + 1) :=
      ⟨Equiv.addRight (a - x), by intro u v; exact circulantGraph_adj_translate⟩
    refine ⟨e, ?_⟩
    change x + (a - x) = a
    abel

theorem cycle_root_edge (n : ℕ) (x : Fin (n + 2)) : ∃ b, (cycleGraph (n + 2)).Adj x b := by
  refine ⟨x + 1, ?_⟩
  rw [cycleGraph_adj]
  exact Or.inr (by simp)

noncomputable def balancedPerm {A : Type*} (σ τ : A ≃ A) :
    completeBipartiteGraph A A ≃g completeBipartiteGraph A A :=
  ⟨Equiv.sumCongr σ τ, by rintro (u | u) (v | v) <;> rfl⟩

def balancedSwap (A : Type*) : completeBipartiteGraph A A ≃g completeBipartiteGraph A A :=
  ⟨Equiv.sumComm A A, by rintro (u | u) (v | v) <;> simp [completeBipartiteGraph]⟩

theorem balanced_root_move {A : Type*} (x a : A ⊕ A) :
    ∃ e : completeBipartiteGraph A A ≃g completeBipartiteGraph A A, e x = a := by
  classical
  cases x with
  | inl x =>
    cases a with
    | inl a => exact ⟨balancedPerm (Equiv.swap x a) (Equiv.refl A), by simp [balancedPerm]⟩
    | inr a => exact ⟨(balancedPerm (Equiv.swap x a) (Equiv.refl A)).trans (balancedSwap A), by
        simp [balancedPerm, balancedSwap]⟩
  | inr x =>
    cases a with
    | inl a => exact ⟨(balancedPerm (Equiv.refl A) (Equiv.swap x a)).trans (balancedSwap A), by
        simp [balancedPerm, balancedSwap]⟩
    | inr a => exact ⟨balancedPerm (Equiv.refl A) (Equiv.swap x a), by simp [balancedPerm]⟩

theorem balanced_root_edge {A : Type*} (x : A ⊕ A) :
    ∃ b, (completeBipartiteGraph A A).Adj x b := by
  refine ⟨x.swap, ?_⟩
  cases x <;> simp [completeBipartiteGraph]

open scoped Classical in
theorem minimal_wedge_card {U W T : Type u} [Fintype U] [Fintype W] [Fintype T]
    (H : SimpleGraph U) {r : ℝ} (h : HasRate H r)
    (hMin : ∀ (A : Type u) [Fintype A] (F : SimpleGraph A), F ⊑ H → HasRate F r →
      Fintype.card U ≤ Fintype.card A)
    (J : SimpleGraph W) (x : W) (K : SimpleGraph T) (y : T)
    (hMove : ∀ a, ∃ e : J ≃g J, e x = a) (hx : ∃ b, J.Adj x b)
    (e : H ≃g wedge J x K y) : Fintype.card W ≤ 1 ∨ Fintype.card T ≤ 1 := by
  classical
  have hEq := Nat.card_congr e.toEquiv
  simp only [Nat.card_eq_fintype_card, Vertex, Fintype.card_sum] at hEq
  have hSub : Fintype.card {b : T // b ≠ y} = Fintype.card T - 1 := by
    simpa only [Fintype.card_eq_nat_card] using Set.card_ne_eq y
  simp only [Fintype.card_eq_nat_card] at hEq hSub
  rw [hSub] at hEq
  letI : Nonempty T := ⟨y⟩
  have hTpos : 0 < Fintype.card T := Fintype.card_pos
  rcases rate_wedge_or J x K y hMove hx (iso_rate e.symm h) with hJ | hK
  · have hJH : J ⊑ H := (show J ⊑ wedge J x K y from ⟨leftCopy J x K y⟩).trans ⟨e.symm.toCopy⟩
    have hc := hMin W J hJH hJ
    simp only [Fintype.card_eq_nat_card] at hc hTpos ⊢
    omega
  · have hKH : K ⊑ H := (show K ⊑ wedge J x K y from ⟨rightCopy J x K y⟩).trans ⟨e.symm.toCopy⟩
    have hc := hMin T K hKH hK
    simp only [Fintype.card_eq_nat_card] at hc hTpos ⊢
    omega

#print axioms minimal_wedge_card
#print axioms cycle_root_move
#print axioms balanced_root_move
#print axioms wedge_rate
#print axioms rate_wedge_or
#print axioms contained_of_packing
#print axioms free_edge_bound

end Erdos713Gluing
