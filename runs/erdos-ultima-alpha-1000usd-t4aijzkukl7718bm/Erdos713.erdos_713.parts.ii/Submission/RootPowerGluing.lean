import FormalConjecturesUtil
import Submission.RootPowerBounds

/-! One-vertex gluing from a proved one-shore rooted upper bound. The bound
is a hypothesis here, not an assertion about all forbidden graphs. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713RootPower
open Erdos713Rate Erdos713Gluing Erdos713Blocking Erdos713SwitchGluing

open scoped Classical in
lemma free_edge_bound {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
    (a C : ℝ) (hC : 0 ≤ C) (n : ℕ) (G : SimpleGraph (Fin n))
    (hfree : (wedge H x J y).Free G)
    (hcross : ∀ K : SimpleGraph (Fin n), ∀ S : Set (Fin n),
      K.IsBipartiteWith S Sᶜ → (∀ f : H.Copy K, f x ∉ S) →
        (Nat.card K.edgeSet : ℝ) ≤ C*(n : ℝ)^a) :
    (G.edgeFinset.card : ℝ) ≤
      (2^(2*((Fintype.card T+1)*Fintype.card W)+2) : ℕ) *
        ((extremalNumber n H : ℝ)+C*(n : ℝ)^a+(extremalNumber n J : ℝ)) +
      (((Fintype.card T+1)*Fintype.card W)*n : ℕ) := by
  classical
  choose B hb hk hB using blockers_or_no_right H x J y G hfree
  let S : Set (Fin n) := {v | ∀ f : H.Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B v}
  have hNoJ (v : Fin n) (hv : v ∉ S) (g : J.Copy G) (hg : g y = v) : False := by
    rcases hB v with hleft | hright
    · exact hv hleft
    · exact hright g hg
  suffices hh : (G.edgeFinset.card : ℝ) ≤
      (2^(2*((Fintype.card T+1)*Fintype.card W)+2) : ℕ) *
        ((extremalNumber n H : ℝ)+C*(n : ℝ)^a+(extremalNumber n J : ℝ)) +
      (((Fintype.card T+1)*Fintype.card W)*Fintype.card (Fin n) : ℕ) by
    simpa only [Fintype.card_fin] using hh
  apply Erdos713KstGluing.real_edges_le_of_keep_bound G B
    ((Fintype.card T+1)*Fintype.card W) _ hb hk (by positivity)
  intro σ
  let K := keep G B σ
  have hsel (f : H.Copy K) (a : W) : selected B σ (f a) := by
    obtain ⟨b,hab⟩ := hNoIso a
    exact (f.toHom.map_adj hab).2.1
  have hRoot (f : H.Copy K) : f x ∉ S := by
    intro hfx
    let g : H.Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp f
    obtain ⟨b,_,hmem⟩ := hfx g rfl
    exact Bool.noConfusion ((hsel f b).1.symm.trans ((hsel f x).2 (f b) hmem))
  have hInside : H.Free (inside K S) := by
    rintro ⟨f⟩
    obtain ⟨b,hxb⟩ := hNoIso x
    exact hRoot ((Copy.ofLE _ _ (inside_le K S)).comp f) (f.toHom.map_adj hxb).2.1
  have hCross : ((cross K S).edgeFinset.card : ℝ) ≤ C*(n : ℝ)^a := by
    have hh := hcross (cross K S) S (Erdos713KstGluing.cross_isBipartiteWith K S)
      (fun f => hRoot ((Copy.ofLE _ _ (cross_le K S)).comp f))
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hh
  have hRest : J.Free (rest K S) := by
    rintro ⟨f⟩
    obtain ⟨z,hyz⟩ := hy
    exact hNoJ (f y) (f.toHom.map_adj hyz).2.1
      ((Copy.ofLE _ _ ((rest_le K S).trans (keep_le G B σ))).comp f) rfl
  have hA : ((inside K S).edgeFinset.card : ℝ) ≤ extremalNumber (Fintype.card (Fin n)) H := by
    exact_mod_cast card_edgeFinset_le_extremalNumber hInside
  have hR : ((rest K S).edgeFinset.card : ℝ) ≤ extremalNumber (Fintype.card (Fin n)) J := by
    exact_mod_cast card_edgeFinset_le_extremalNumber hRest
  have hSplit : (K.edgeFinset.card : ℝ) ≤ (inside K S).edgeFinset.card +
      (cross K S).edgeFinset.card + (rest K S).edgeFinset.card := by
    exact_mod_cast Erdos713SwitchGluing.edge_split K S
  simp only [Fintype.card_fin] at hA hR
  exact hSplit.trans (by linarith)

lemma wedge_upper {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z) {a b : ℝ}
    (hb : 1 ≤ b) (hRoot : RootPowerBound H x a)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^a))
    (hJ : (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^b)) :
    (fun n : ℕ => (extremalNumber n (wedge H x J y) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^(max a b)) := by
  classical
  obtain ⟨D,hD,hroot⟩ := hRoot
  let k := (Fintype.card T+1)*Fintype.card W
  let C : ℕ := 2^(2*k+2)
  have hH' := hH.trans (rpow_mono_bigO (le_max_left a b))
  have hD' := (rpow_mono_bigO (le_max_left a b)).const_mul_left D
  have hJ' := hJ.trans (rpow_mono_bigO (le_max_right a b))
  have hA := ((hH'.add hD').add hJ').const_mul_left (C : ℝ)
  have hL := cast_linear_bigO (hb.trans (le_max_right a b)) k
  apply IsBigO.trans _ (hA.add hL)
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast,Real.norm_of_nonneg (by positivity),one_mul]
  rw [← Fintype.card_fin n,extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ hG
  simpa only [C,k,edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin] using
    free_edge_bound H x hNoIso J y hy a D hD n G hG (hroot n)

lemma wedge_rate {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z) {a b : ℝ}
    (hH : HasRate H a) (hJ : HasRate J b) (hRoot : RootPowerBound H x a) :
    HasRate (wedge H x J y) (max a b) := by
  refine ⟨hJ.one_le.trans (le_max_right _ _),
    wedge_upper H x hNoIso J y hy hJ.one_le hRoot hH.upper hJ.upper,?_⟩
  intro r hr h
  exact max_le (hH.lower r hr ((extremal_mono_bigO ⟨leftCopy _ _ _ _⟩).trans h))
    (hJ.lower r hr ((extremal_mono_bigO ⟨rightCopy _ _ _ _⟩).trans h))

lemma small_core_wedge_rate {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (S : Set W) (hB : H.IsBipartiteWith S Sᶜ)
    (hS : Nat.card S ≤ 3) (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v))
    (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
    {b : ℚ} (hJ : HasRate J (b : ℝ)) :
    ∃ r : ℚ, HasRate (wedge H x J y) (r : ℝ) := by
  classical
  letI : Nonempty W := ⟨x⟩
  obtain ⟨a,hH,hroot⟩ := small_core H S hB hS hd
  have hNoIso : ∀ v, ∃ w, H.Adj v w := by
    intro v
    apply (H.degree_pos_iff_exists_adj v).mp
    have hh : 2 ≤ H.degree v := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hd v
    omega
  refine ⟨max a b,?_⟩
  simpa only [Rat.cast_max] using wedge_rate H x hNoIso J y hy hH hJ (hroot x)

lemma exceptional_columns_wedge_rate {A B W T : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Fintype W] [Fintype T]
    (R : A → B → Prop) (E : Set B) (hE : Nat.card E ≤ 2)
    (hR : ∀ b ∉ E, Nat.card {a // R a b} ≤ 2)
    (H : SimpleGraph W) (x : W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ Erdos713C6.bipGraph R)
    (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
    {b : ℝ} (hJ : HasRate J b) : HasRate (wedge H x J y) (max ((3 : ℝ)/2) b) :=
  wedge_rate H x hNoIso J y hy (two_exception_columns_rate R E hE hR hlo hhi) hJ
    (exceptional_columns R E hE hR hhi x)


#print axioms wedge_rate

lemma edge_wedge_rate {T : Type*} [Fintype T] (J : SimpleGraph T) (y : T)
    (hy : ∃ z, J.Adj y z) (x : Fin 1 ⊕ Fin 1) {b : ℝ} (hJ : HasRate J b) :
    HasRate (wedge (Erdos713KST.Kst 1 1) x J y) b := by
  have hH : HasRate (Erdos713KST.Kst 1 1) 1 := by
    refine ⟨le_rfl,?_,fun r hr _ => hr⟩
    simpa using upper_of_power_bound (by decide : 1 ≠ 0)
      (fun n => Erdos713KST.extremal_pow_le 1 1 n (by decide))
  simpa only [Nat.sub_self,Nat.zero_add,Nat.cast_one,div_one,max_eq_right hJ.one_le] using
    Erdos713KstGluing.wedge_rate J y hy (s := 1) (t := 1) (by decide) (by decide) x
      (by simpa using hH) hJ

#print axioms small_core_wedge_rate
end Erdos713RootPower
