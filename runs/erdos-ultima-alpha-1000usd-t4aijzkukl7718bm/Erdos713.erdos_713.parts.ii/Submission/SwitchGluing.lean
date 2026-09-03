import FormalConjecturesUtil
import Submission.UpToTheta3

/-! A gluing bound when automorphisms can switch the root's bipartition class. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713SwitchGluing
open Erdos713Gluing Erdos713Blocking Erdos713Rate Finset

/-- In every two-coloring, some automorphism changes the color of the root. -/
def RootSwitching {W : Type*} (H : SimpleGraph W) (x : W) : Prop :=
  ∀ c : H.Coloring Bool, ∃ e : H ≃g H, c (e x) ≠ c x

lemma rootSwitching_of_root_movable {W : Type*} (H : SimpleGraph W) (x : W)
    (hMove : ∀ a, ∃ e : H ≃g H, e x = a) (hx : ∃ b, H.Adj x b) :
    RootSwitching H x := by
  intro c
  obtain ⟨b, hxb⟩ := hx
  obtain ⟨e, he⟩ := hMove b
  exact ⟨e, by simpa only [he] using (c.valid hxb).symm⟩

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

noncomputable def crossColoring {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (cross G S).Coloring Bool := by
  classical
  refine Coloring.mk (fun v => decide (v ∈ S)) ?_
  intro u v h
  rcases h.2 with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;> simp [hu,hv]

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

open scoped Classical in
set_option maxHeartbeats 2000000 in
lemma free_edge_bound {W T V : Type*} [Fintype W] [Fintype T] [Fintype V]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T) (G : SimpleGraph V)
    (hSwitch : RootSwitching H x) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hfree : (wedge H x J y).Free G) :
    G.edgeFinset.card ≤ 2 ^ (2 * ((Fintype.card T + 1) * Fintype.card W) + 2) *
      (2 * extremalNumber (Fintype.card V) H + extremalNumber (Fintype.card V) J +
        Fintype.card T * Fintype.card V) +
      ((Fintype.card T + 1) * Fintype.card W) * Fintype.card V := by
  classical
  choose B hb hk hB using blockers_or_no_right H x J y G hfree
  let S : Set V := {v | ∀ f : H.Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B v}
  have hNoJ (v : V) (hv : v ∉ S) (g : J.Copy G) (hg : g y = v) : False := by
    rcases hB v with hleft | hright
    · exact hv hleft
    · exact hright g hg
  apply edges_le_of_keep_bound G B ((Fintype.card T + 1) * Fintype.card W) _ hb hk
  intro σ
  let K := keep G B σ
  have hsel (f : H.Copy K) (a : W) : selected B σ (f a) := by
    obtain ⟨b, hab⟩ := hNoIso a
    exact (f.toHom.map_adj hab).2.1
  have hRoot (f : H.Copy K) : f x ∉ S := by
    intro hfx
    let g : H.Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp f
    obtain ⟨b, _, hmem⟩ := hfx g rfl
    exact Bool.noConfusion ((hsel f b).1.symm.trans ((hsel f x).2 (f b) hmem))
  have hInside : H.Free (inside K S) := by
    rintro ⟨f⟩
    let g : H.Copy K := (Copy.ofLE _ _ (inside_le K S)).comp f
    obtain ⟨b, hxb⟩ := hNoIso x
    exact hRoot g (f.toHom.map_adj hxb).2.1
  have hCross : H.Free (cross K S) := by
    rintro ⟨f⟩
    let g : H.Copy K := (Copy.ofLE _ _ (cross_le K S)).comp f
    let c : H.Coloring Bool := (crossColoring K S).comp f.toHom
    obtain ⟨e, he⟩ := hSwitch c
    have h0 : f x ∉ S := hRoot g
    have h1 : f (e x) ∉ S := hRoot (g.comp e.toCopy)
    apply he
    simp [c, crossColoring, Coloring.mk, h0, h1]
  have hRest : J.Free ((rest K S).induce Sᶜ) := by
    rintro ⟨f⟩
    let g : J.Copy G := (Copy.ofLE _ _ ((rest_le K S).trans (keep_le G B σ))).comp
      ((Copy.induce _ _).comp f)
    exact hNoJ (f y).val (f y).prop g rfl
  have hSupp : (rest K S).support ⊆ Sᶜ := by
    rintro v ⟨w, hvw⟩
    exact hvw.2.1
  have hA := card_edgeFinset_le_extremalNumber hInside
  have hC := card_edgeFinset_le_extremalNumber hCross
  have hR := Erdos713Support.edges_le_of_free_induce J (rest K S) Sᶜ hSupp hRest
  have hSplit := edge_split K S
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hA hC hR hSplit ⊢
  dsimp only [K] at hA hC hR hSplit
  omega

open scoped Classical in
lemma extremal_bound {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hSwitch : RootSwitching H x) (hNoIso : ∀ a, ∃ b, H.Adj a b) (n : ℕ) :
    extremalNumber n (wedge H x J y) ≤ 2 ^ (2 * ((Fintype.card T + 1) * Fintype.card W) + 2) *
      (2 * extremalNumber n H + extremalNumber n J + Fintype.card T * n) +
      ((Fintype.card T + 1) * Fintype.card W) * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using free_edge_bound H x J y G hSwitch hNoIso hfree

lemma wedge_upper {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hSwitch : RootSwitching H x) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hJ : (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ b)) :
    (fun n : ℕ => (extremalNumber n (wedge H x J y) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (max a b)) := by
  let k := (Fintype.card T + 1) * Fintype.card W
  let C : ℕ := 2 ^ (2 * k + 2)
  have hH' := (hH.trans (rpow_mono_bigO (le_max_left a b))).const_mul_left (2 : ℝ)
  have hJ' := hJ.trans (rpow_mono_bigO (le_max_right a b))
  have hL := cast_linear_bigO (ha.trans (le_max_left a b)) (Fintype.card T)
  have hA := ((hH'.add hJ').add hL).const_mul_left (C : ℝ)
  have hB := cast_linear_bigO (ha.trans (le_max_left a b)) k
  apply IsBigO.trans _ (hA.add hB)
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast extremal_bound H x J y hSwitch hNoIso n

lemma wedge_rate {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hSwitch : RootSwitching H x) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    {a b : ℝ} (hH : HasRate H a) (hJ : HasRate J b) : HasRate (wedge H x J y) (max a b) := by
  refine ⟨hH.one_le.trans (le_max_left a b),
    wedge_upper H x J y hSwitch hNoIso hH.one_le hJ.one_le hH.upper hJ.upper, ?_⟩
  intro c hc hC
  apply max_le
  · exact hH.lower c hc ((extremal_mono_bigO ⟨leftCopy H x J y⟩).trans hC)
  · exact hJ.lower c hc ((extremal_mono_bigO ⟨rightCopy H x J y⟩).trans hC)


lemma bool_ne_of_three_steps {a b c d : Bool} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) :
    d ≠ a := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

def thetaSwap (t : ℕ) : Erdos713Theta3.theta t ≃g Erdos713Theta3.theta t :=
  ⟨Equiv.sumComm _ _, by
    rintro (a | a) (b | b) <;> cases a <;> cases b <;>
      simp [Erdos713Theta3.theta, Erdos713Theta3.Rel, Erdos713C6.bipGraph, eq_comm]⟩

lemma theta_rootSwitching {t : ℕ} (ht : 1 ≤ t) (x : Erdos713Theta3.Vertex t) :
    RootSwitching (Erdos713Theta3.theta t) x := by
  intro c
  refine ⟨thetaSwap t, ?_⟩
  let i : Fin t := ⟨0, by omega⟩
  have h0 : c (Sum.inl none) ≠ c (Sum.inr (some i)) :=
    c.valid (show (Erdos713Theta3.theta t).Adj _ _ from trivial)
  have h1 : c (Sum.inr (some i)) ≠ c (Sum.inl (some i)) :=
    c.valid (show (Erdos713Theta3.theta t).Adj _ _ from rfl)
  have h2 : c (Sum.inl (some i)) ≠ c (Sum.inr none) :=
    c.valid (show (Erdos713Theta3.theta t).Adj _ _ from trivial)
  have hEnds := bool_ne_of_three_steps h0 h1 h2
  cases x with
  | inl x =>
    cases x with
    | none => exact hEnds
    | some j => exact (c.valid (show (Erdos713Theta3.theta t).Adj (Sum.inl (some j))
        (Sum.inr (some j)) from rfl)).symm
  | inr x =>
    cases x with
    | none => exact hEnds.symm
    | some j => exact c.valid (show (Erdos713Theta3.theta t).Adj (Sum.inl (some j))
        (Sum.inr (some j)) from rfl)

lemma theta_no_isolates {t : ℕ} (ht : 1 ≤ t) (x : Erdos713Theta3.Vertex t) :
    ∃ y, (Erdos713Theta3.theta t).Adj x y := by
  let i : Fin t := ⟨0, by omega⟩
  cases x with
  | inl x =>
    cases x with
    | none => exact ⟨Sum.inr (some i), trivial⟩
    | some j => exact ⟨Sum.inr (some j), rfl⟩
  | inr x =>
    cases x with
    | none => exact ⟨Sum.inl (some i), trivial⟩
    | some j => exact ⟨Sum.inl (some j), rfl⟩

lemma theta_wedge_rate {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W)
    {t : ℕ} (ht : 2 ≤ t) (y : Erdos713Theta3.Vertex t) {r : ℝ} (hH : HasRate H r) :
    HasRate (wedge (Erdos713Theta3.theta t) y H x) (max ((4 : ℝ) / 3) r) :=
  wedge_rate _ y H x (theta_rootSwitching (by omega) y) (theta_no_isolates (by omega))
    (Erdos713Theta3.rate ht) hH

end Erdos713SwitchGluing

namespace Erdos713SwitchTight
open Erdos713Tight Erdos713Gluing Erdos713SwitchGluing Erdos713Rate
universe u

lemma wedge_littleO {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hSwitch : RootSwitching H x) (hNoIso : ∀ a, ∃ b, H.Adj a b) {r : ℝ} (hr : 1 < r)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r))
    (hJ : (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    (fun n : ℕ => (extremalNumber n (wedge H x J y) : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
  let k := (Fintype.card T + 1) * Fintype.card W
  let C := 2 ^ (2 * k + 2)
  have hs : (fun n : ℕ => ((2 * extremalNumber n H + extremalNumber n J : ℕ) : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using (hH.const_mul_left (2 : ℝ)).add hJ
  apply bounded_littleO C (C * Fintype.card T + k) ?_ hr hs
  intro n
  convert Erdos713SwitchGluing.extremal_bound H x J y hSwitch hNoIso n using 1; dsimp [C, k]; ring

lemma wedge_or {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hSwitch : RootSwitching H x) (hNoIso : ∀ a, ∃ b, H.Adj a b) {r : ℝ} (hr : 1 < r)
    (h : HasTightRate (wedge H x J y) r) : HasTightRate H r ∨ HasTightRate J r := by
  classical
  by_cases hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)
  · right
    apply of_upper_notLittleO h.one_le
      ((extremal_mono_bigO ⟨rightCopy H x J y⟩).trans h.upper)
    intro hJ
    exact h.notLittleO (wedge_littleO H x J y hSwitch hNoIso hr hH hJ)
  · exact Or.inl (of_upper_notLittleO h.one_le
      ((extremal_mono_bigO ⟨leftCopy H x J y⟩).trans h.upper) hH)

open scoped Classical in
lemma minimal_wedge_card {U W T : Type u} [Fintype U] [Fintype W] [Fintype T]
    (H : SimpleGraph U) {r : ℝ} (hr : 1 < r) (h : HasTightRate H r)
    (hMin : ∀ (A : Type u) [Fintype A] (F : SimpleGraph A), F ⊑ H → HasTightRate F r →
      Fintype.card U ≤ Fintype.card A)
    (J : SimpleGraph W) (x : W) (K : SimpleGraph T) (y : T)
    (hSwitch : RootSwitching J x) (hNoIso : ∀ a, ∃ b, J.Adj a b)
    (e : H ≃g wedge J x K y) : Fintype.card W ≤ 1 ∨ Fintype.card T ≤ 1 := by
  classical
  have hEq := Nat.card_congr e.toEquiv
  simp only [Nat.card_eq_fintype_card, Erdos713Gluing.Vertex, Fintype.card_sum] at hEq
  have hSub : Fintype.card {b : T // b ≠ y} = Fintype.card T - 1 := by
    simpa only [Fintype.card_eq_nat_card] using Set.card_ne_eq y
  simp only [Fintype.card_eq_nat_card] at hEq hSub
  rw [hSub] at hEq
  letI : Nonempty T := ⟨y⟩
  have hTpos : 0 < Fintype.card T := Fintype.card_pos
  rcases wedge_or J x K y hSwitch hNoIso hr (iso e.symm h) with hJ | hK
  · have hJH : J ⊑ H := (show J ⊑ wedge J x K y from ⟨leftCopy J x K y⟩).trans ⟨e.symm.toCopy⟩
    have hc := hMin W J hJH hJ
    simp only [Fintype.card_eq_nat_card] at hc hTpos ⊢
    omega
  · have hKH : K ⊑ H := (show K ⊑ wedge J x K y from ⟨rightCopy J x K y⟩).trans ⟨e.symm.toCopy⟩
    have hc := hMin T K hKH hK
    simp only [Fintype.card_eq_nat_card] at hc hTpos ⊢
    omega

end Erdos713SwitchTight

#print axioms Erdos713SwitchGluing.wedge_rate
#print axioms Erdos713SwitchGluing.theta_wedge_rate
#print axioms Erdos713SwitchTight.minimal_wedge_card
