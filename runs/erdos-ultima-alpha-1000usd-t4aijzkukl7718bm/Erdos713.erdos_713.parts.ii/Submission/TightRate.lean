import FormalConjecturesUtil
import Submission.Latest
import Submission.SharpUnion
import Submission.Gluing

/-! A growth rate with a nonvanishing normalized limsup. This retains more
of a pure-power asymptotic than an upper power threshold alone. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713Tight
open Erdos713Rate
universe u

structure HasTightRate {W : Type*} (H : SimpleGraph W) (r : ℝ) : Prop extends HasRate H r where
  notLittleO : ¬ (fun n : ℕ => (extremalNumber n H : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)

theorem of_upper_notLittleO {W : Type*} {H : SimpleGraph W} {r : ℝ} (hr : 1 ≤ r)
    (hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r))
    (hn : ¬ (fun n : ℕ => (extremalNumber n H : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    HasTightRate H r := by
  refine ⟨⟨hr, hu, ?_⟩, hn⟩
  intro a _ ha
  by_contra hh
  exact hn (ha.trans_isLittleO (Erdos713Leaf.rpow_isLittleO_nat (lt_of_not_ge hh)))

theorem not_rpow_littleO_self (r : ℝ) :
    ¬ (fun n : ℕ => (n : ℝ) ^ r) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r) := by
  intro h
  have he := h.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨n, hn, hnpos⟩ := (he.and (eventually_gt_atTop (0 : ℕ))).exists
  have hp : 0 < (n : ℝ) ^ r := Real.rpow_pos_of_pos (by exact_mod_cast hnpos) r
  rw [Real.norm_of_nonneg hp.le] at hn
  nlinarith

theorem of_asymptotic {W : Type*} {H : SimpleGraph W} {r c : ℝ} (hr : 1 ≤ r) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ r)) : HasTightRate H r := by
  refine ⟨rate_of_asymptotic hr hc h, ?_⟩
  intro ho
  exact not_rpow_littleO_self r (((isBigO_const_mul_left_iff hc).mp h.isBigO_symm).trans_isLittleO ho)

theorem iso {W T : Type*} {G : SimpleGraph W} {H : SimpleGraph T} (e : G ≃g H)
    {r : ℝ} (h : HasTightRate H r) : HasTightRate G r := by
  refine ⟨iso_rate e h.toHasRate, ?_⟩
  intro ho
  exact h.notLittleO ((extremal_mono_bigO ⟨e.symm.toCopy⟩).trans_isLittleO ho)

theorem linear_littleO {r : ℝ} (hr : 1 < r) (C : ℕ) :
    (fun n : ℕ => ((C * n : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r) := by
  simpa only [Nat.cast_mul, Real.rpow_one] using
    (Erdos713Leaf.rpow_isLittleO_nat hr).const_mul_left (C : ℝ)

theorem sum_littleO {A B : Type*} [Fintype A] [Fintype B]
    (G : SimpleGraph A) (H : SimpleGraph B) {r : ℝ} (hr : 1 < r)
    (hG : (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r))
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    (fun n : ℕ => (extremalNumber n (G ⊕g H) : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r) := by
  apply IsBigO.trans_isLittleO _ ((hG.add hH).add (linear_littleO hr (Fintype.card A + Fintype.card B)))
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  have hh := Erdos713SharpUnion.extremal_sum_max_bound G H n
  have hm : max (extremalNumber n G) (extremalNumber n H) ≤
      extremalNumber n G + extremalNumber n H := max_le (by omega) (by omega)
  exact_mod_cast hh.trans (Nat.add_le_add_right hm _)

theorem sum_or {A B : Type*} [Fintype A] [Fintype B]
    (G : SimpleGraph A) (H : SimpleGraph B) {r : ℝ} (hr : 1 < r)
    (h : HasTightRate (G ⊕g H) r) : HasTightRate G r ∨ HasTightRate H r := by
  classical
  by_cases hG : (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)
  · right
    apply of_upper_notLittleO h.one_le ((extremal_mono_bigO ⟨Embedding.sumInr.toCopy⟩).trans h.upper)
    intro hH
    exact h.notLittleO (sum_littleO G H hr hG hH)
  · exact Or.inl (of_upper_notLittleO h.one_le
      ((extremal_mono_bigO ⟨Embedding.sumInl.toCopy⟩).trans h.upper) hG)

open scoped Classical in
theorem leaf_converse {W : Type*} [Fintype W] (G : SimpleGraph W)
    {x y : W} (hx : G.degree x = 1) (hxy : G.Adj x y) {r : ℝ} (hr : 1 < r)
    (h : HasTightRate G r) : HasTightRate (G.induce {x}ᶜ) r := by
  refine ⟨leaf_rate_converse G hx hxy h.toHasRate, ?_⟩
  intro ho
  apply h.notLittleO
  apply IsBigO.trans_isLittleO _ (ho.add (linear_littleO hr (Fintype.card W)))
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast Erdos713Leaf.extremal_leaf_upper G hx hxy n

open scoped Classical in
theorem isolated_converse {W : Type*} [Fintype W] (G : SimpleGraph W)
    {x : W} (hx : G.degree x = 0) {r : ℝ} (h : HasTightRate G r) : HasTightRate (G.induce {x}ᶜ) r := by
  refine ⟨isolated_rate_converse G hx h.toHasRate, ?_⟩
  intro ho
  apply h.notLittleO
  apply ho.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (Fintype.card W)] with n hn
  rw [Erdos713Leaf.extremal_isolated_eq G hx hn]

open scoped Classical in
theorem exists_minimal_connected_core {W : Type u} [Fintype W] (G : SimpleGraph W)
    {r : ℝ} (hr : 1 < r) (h : HasTightRate G r) :
    ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U), H ⊑ G ∧ H.Connected ∧
      (∀ v, 2 ≤ Nat.card (H.neighborSet v)) ∧ HasTightRate H r ∧ Fintype.card U ≤ Fintype.card W ∧
      (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasTightRate J r →
        Fintype.card U ≤ Fintype.card T) := by
  classical
  let P : ℕ → Prop := fun n => ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U),
    H ⊑ G ∧ HasTightRate H r ∧ Fintype.card U = n
  have hP : ∃ n, P n := ⟨Fintype.card W, W, inferInstance, G, .refl _, h, rfl⟩
  obtain ⟨U, instU, H, hHG, hHR, hcard⟩ := Nat.find_spec hP
  have hMin (T : Type u) [Fintype T] (J : SimpleGraph T) (hJG : J ⊑ G) (hJR : HasTightRate J r) :
      Fintype.card U ≤ Fintype.card T := by
    rw [hcard]
    exact Nat.find_min' hP ⟨T, inferInstance, J, hJG, hJR, rfl⟩
  have hSmaller (S : Set U) (hS : Nat.card S < Fintype.card U)
      (hR : HasTightRate (H.induce S) r) : False := by
    have hh := hMin S (H.induce S) ((show H.induce S ⊑ H from ⟨Copy.induce H S⟩).trans hHG) hR
    simp only [Fintype.card_eq_nat_card] at hh hS
    omega
  have hDegree : ∀ v, 2 ≤ Nat.card (H.neighborSet v) := by
    intro x
    by_contra hx
    have hx' : H.degree x < 2 := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, not_le] using hx
    apply hSmaller {x}ᶜ (by
      simpa only [Fintype.card_eq_nat_card] using
        Fintype.card_subtype_lt (p := fun v => v ∈ ({x}ᶜ : Set U)) (x := x) (by simp))
    have hx01 : H.degree x = 0 ∨ H.degree x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · exact isolated_converse H hx0 hHR
    · obtain ⟨y, hxy, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hx1
      exact leaf_converse H hx1 hxy hr hHR
  letI : Nonempty U := nonempty_of_superlinear_rate hr hHR.toHasRate
  have hConnected : H.Connected := by
    by_contra hC
    let w : U := Classical.arbitrary U
    have hw : ∃ v, ¬H.Reachable w v := by
      by_contra hhh
      push_neg at hhh
      exact hC ((H.connected_iff_exists_forall_reachable).mpr ⟨w, hhh⟩)
    obtain ⟨v, hv⟩ := hw
    let S : Set U := (H.connectedComponentMk w).supp
    have hwS : w ∈ S := rfl
    have hvS : v ∉ S := by
      intro hh
      exact hv (ConnectedComponent.exact hh.symm)
    have hs : Nat.card S < Fintype.card U := by
      simpa only [Fintype.card_eq_nat_card] using Fintype.card_subtype_lt hvS
    have hsc : Nat.card ↥(Sᶜ) < Fintype.card U := by
      simpa only [Fintype.card_eq_nat_card] using
        Fintype.card_subtype_lt (x := w) (by simpa only [Set.mem_compl_iff, not_not] using hwS)
    have hSplit := iso (Erdos713Components.splitIso H S (fun u v huv =>
      ConnectedComponent.mem_supp_congr_adj (H.connectedComponentMk w) huv)) hHR
    rcases sum_or (H.induce S) (H.induce Sᶜ) hr hSplit with hRS | hRSc
    · exact hSmaller S hs hRS
    · exact hSmaller Sᶜ hsc hRSc
  refine ⟨U, instU, H, hHG, hConnected, hDegree, hHR, hMin W G (.refl _) h, ?_⟩
  intro T _ J hJH hJR
  exact hMin T J (hJH.trans hHG) hJR

theorem exists_positive_lower_constant {W : Type*} {H : SimpleGraph W} {r : ℝ}
    (h : HasTightRate H r) : ∃ d : ℝ, 0 < d ∧ ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ d * (n : ℝ) ^ r < (extremalNumber n H : ℝ) := by
  classical
  by_contra hn
  push_neg at hn
  apply h.notLittleO
  apply IsLittleO.of_bound
  intro d hd
  obtain ⟨N, hN⟩ := hn d hd
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact hN n hn

theorem bounded_littleO {f g : ℕ → ℕ} (C D : ℕ)
    (hbound : ∀ n, f n ≤ C * g n + D * n) {r : ℝ} (hr : 1 < r)
    (hg : (fun n : ℕ => (g n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    (fun n : ℕ => (f n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r) := by
  apply IsBigO.trans_isLittleO _ ((hg.const_mul_left (C : ℝ)).add (linear_littleO hr D))
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast hbound n

theorem fan_littleO {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W) (t : ℕ)
    {r : ℝ} (hr : 1 < r)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    (fun n : ℕ => (extremalNumber n (Erdos713Fan.fan H x t) : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
  let k := t * Fintype.card W
  let C := 2 ^ (2 * k + 2)
  apply bounded_littleO C (C * Fintype.card W + k) ?_ hr hH
  intro n
  convert Erdos713Fan.extremal_bound_general H x t n using 1; dsimp [C, k]; ring

theorem fan_sandwich_converse {W T : Type*} [Fintype W]
    (J : SimpleGraph W) (x : W) (t : ℕ) {H : SimpleGraph T}
    (hlo : J ⊑ H) (hhi : H ⊑ Erdos713Fan.fan J x t) {r : ℝ} (hr : 1 < r)
    (h : HasTightRate H r) : HasTightRate J r := by
  refine ⟨Erdos713Fan.rate_of_sandwich_converse J x t hlo hhi h.toHasRate, ?_⟩
  intro ho
  exact h.notLittleO ((extremal_mono_bigO hhi).trans_isLittleO (fan_littleO J x t hr ho))

theorem wedge_littleO {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hMove : ∀ a, ∃ e : H ≃g H, e x = a) (hx : ∃ b, H.Adj x b) {r : ℝ} (hr : 1 < r)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r))
    (hJ : (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    (fun n : ℕ => (extremalNumber n (Erdos713Gluing.wedge H x J y) : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
  let k := (Fintype.card T + 1) * Fintype.card W
  let C := 2 ^ (2 * k + 2)
  have hs : (fun n : ℕ => ((extremalNumber n H + extremalNumber n J : ℕ) : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by simpa only [Nat.cast_add] using hH.add hJ
  apply bounded_littleO C (C * Fintype.card T + k) ?_ hr hs
  intro n
  convert Erdos713Gluing.extremal_bound H x J y hMove hx n using 1; dsimp [C, k]; ring

theorem wedge_or {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
    (hMove : ∀ a, ∃ e : H ≃g H, e x = a) (hx : ∃ b, H.Adj x b) {r : ℝ} (hr : 1 < r)
    (h : HasTightRate (Erdos713Gluing.wedge H x J y) r) : HasTightRate H r ∨ HasTightRate J r := by
  classical
  by_cases hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r)
  · right
    apply of_upper_notLittleO h.one_le
      ((extremal_mono_bigO ⟨Erdos713Gluing.rightCopy H x J y⟩).trans h.upper)
    intro hJ
    exact h.notLittleO (wedge_littleO H x J y hMove hx hr hH hJ)
  · exact Or.inl (of_upper_notLittleO h.one_le
      ((extremal_mono_bigO ⟨Erdos713Gluing.leftCopy H x J y⟩).trans h.upper) hH)

theorem minimal_fan_sandwich_card {U W : Type u} [Fintype U] [Fintype W]
    (H : SimpleGraph U) {r : ℝ} (hr : 1 < r) (h : HasTightRate H r)
    (hMin : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasTightRate J r →
      Fintype.card U ≤ Fintype.card T)
    (J : SimpleGraph W) (x : W) (t : ℕ) (hlo : J ⊑ H) (hhi : H ⊑ Erdos713Fan.fan J x t) :
    Fintype.card U ≤ Fintype.card W := hMin W J hlo (fan_sandwich_converse J x t hlo hhi hr h)

open scoped Classical in
theorem minimal_wedge_card {U W T : Type u} [Fintype U] [Fintype W] [Fintype T]
    (H : SimpleGraph U) {r : ℝ} (hr : 1 < r) (h : HasTightRate H r)
    (hMin : ∀ (A : Type u) [Fintype A] (F : SimpleGraph A), F ⊑ H → HasTightRate F r →
      Fintype.card U ≤ Fintype.card A)
    (J : SimpleGraph W) (x : W) (K : SimpleGraph T) (y : T)
    (hMove : ∀ a, ∃ e : J ≃g J, e x = a) (hx : ∃ b, J.Adj x b)
    (e : H ≃g Erdos713Gluing.wedge J x K y) : Fintype.card W ≤ 1 ∨ Fintype.card T ≤ 1 := by
  classical
  have hEq := Nat.card_congr e.toEquiv
  simp only [Nat.card_eq_fintype_card, Erdos713Gluing.Vertex, Fintype.card_sum] at hEq
  have hSub : Fintype.card {b : T // b ≠ y} = Fintype.card T - 1 := by
    simpa only [Fintype.card_eq_nat_card] using Set.card_ne_eq y
  simp only [Fintype.card_eq_nat_card] at hEq hSub
  rw [hSub] at hEq
  letI : Nonempty T := ⟨y⟩
  have hTpos : 0 < Fintype.card T := Fintype.card_pos
  rcases wedge_or J x K y hMove hx hr (iso e.symm h) with hJ | hK
  · have hJH : J ⊑ H := (show J ⊑ Erdos713Gluing.wedge J x K y from ⟨Erdos713Gluing.leftCopy J x K y⟩).trans ⟨e.symm.toCopy⟩
    have hc := hMin W J hJH hJ
    simp only [Fintype.card_eq_nat_card] at hc hTpos ⊢
    omega
  · have hKH : K ⊑ H := (show K ⊑ Erdos713Gluing.wedge J x K y from ⟨Erdos713Gluing.rightCopy J x K y⟩).trans ⟨e.symm.toCopy⟩
    have hc := hMin T K hKH hK
    simp only [Fintype.card_eq_nat_card] at hc hTpos ⊢
    omega

#print axioms minimal_wedge_card
#print axioms fan_sandwich_converse
#print axioms wedge_or
#print axioms exists_positive_lower_constant
#print axioms exists_minimal_connected_core
#print axioms of_asymptotic
#print axioms sum_or
#print axioms leaf_converse
#print axioms isolated_converse

end Erdos713Tight
