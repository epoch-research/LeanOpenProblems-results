import FormalConjecturesUtil

/-! The forest case of the extremal-exponent question. -/

open SimpleGraph Filter Asymptotics

namespace Erdos713Forest

open scoped Classical in
 theorem tree_copy_of_degree_bound {V W : Type*} [Fintype V] [Nonempty V]
    [Fintype W] (G : SimpleGraph V) [DecidableRel G.Adj] (T : SimpleGraph W) (hT : T.IsTree)
    (hdeg : ∀ v, Fintype.card W ≤ G.degree v) : Nonempty (Copy T G) := by
  classical
  revert hdeg
  revert T
  refine Fintype.induction_subsingleton_or_nontrivial
    (P := fun W _ => ∀ T : SimpleGraph W, T.IsTree →
      (∀ v, Fintype.card W ≤ G.degree v) → Nonempty (Copy T G)) W ?_ ?_
  · intro W _ _ T _ _
    let v : V := Classical.choice inferInstance
    refine ⟨⟨⟨fun _ => v, ?_⟩, Function.injective_of_subsingleton _⟩⟩
    intro x y hxy
    exact (hxy.ne (Subsingleton.elim _ _)).elim
  · intro W _ _ ih T hT hdeg
    obtain ⟨x, hx⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨y, hxy, hy⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
    have hsmall : Fintype.card ↥({x}ᶜ : Set W) < Fintype.card W :=
      Fintype.card_subtype_lt (x := x) (by simp)
    have hT' : (T.induce {x}ᶜ).IsTree :=
      ⟨hT.isConnected.induce_compl_singleton_of_degree_eq_one hx, hT.IsAcyclic.induce _⟩
    obtain ⟨f⟩ := ih ↥({x}ᶜ : Set W) hsmall (T.induce {x}ᶜ) hT'
      (fun v => hsmall.le.trans (hdeg v))
    let y' : ↥({x}ᶜ : Set W) := ⟨y, by simpa using hxy.ne.symm⟩
    let S : Finset V := Finset.univ.image f
    have hS : S.card < (G.neighborFinset (f y')).card := by
      calc
        S.card ≤ Fintype.card ↥({x}ᶜ : Set W) := by
          simpa only [Finset.card_univ] using (Finset.card_image_le (s := Finset.univ) (f := f))
        _ < Fintype.card W := hsmall
        _ ≤ (G.neighborFinset (f y')).card := hdeg _
    obtain ⟨z, hz, hzS⟩ := Finset.exists_mem_notMem_of_card_lt_card hS
    have hzadj : G.Adj (f y') z := by simpa using hz
    have hzf : ∀ w, z ≠ f w := by
      intro w heq
      apply hzS
      exact heq ▸ Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
    let g : W → V := fun w => if h : w = x then z else f ⟨w, by simpa using h⟩
    have hg : ∀ w (hw : w ≠ x), g w = f ⟨w, by simpa using hw⟩ := by
      intro w hw
      simp [g, hw]
    have hgx : g x = z := by simp [g]
    refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
    · intro u v huv
      by_cases hu : u = x
      · subst u
        have hv : v = y := hy v huv
        subst v
        simpa [hgx, hg y hxy.ne.symm, y'] using hzadj.symm
      · by_cases hv : v = x
        · subst v
          have hu' : u = y := hy u huv.symm
          subst u
          simpa [hgx, hg y hxy.ne.symm, y'] using hzadj
        · rw [hg u hu, hg v hv]
          exact f.toHom.map_rel' huv
    · intro u v huv
      change g u = g v at huv
      by_cases hu : u = x
      · by_cases hv : v = x
        · exact hu.trans hv.symm
        · rw [hu, hgx, hg v hv] at huv
          exact (hzf _ huv).elim
      · by_cases hv : v = x
        · rw [hv, hgx, hg u hu] at huv
          exact (hzf _ huv.symm).elim
        · rw [hg u hu, hg v hv] at huv
          exact congrArg Subtype.val (f.injective huv)

open scoped Classical in
 theorem free_tree_edge_bound {W V : Type*} [Fintype W] [Fintype V]
    (T : SimpleGraph W) (hT : T.IsTree) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : T.Free G) :
    G.edgeFinset.card ≤ Fintype.card W * Fintype.card V := by
  classical
  revert G
  refine Fintype.induction_subsingleton_or_nontrivial
    (P := fun V _ => ∀ G : SimpleGraph V, ∀ _ : DecidableRel G.Adj, T.Free G →
      G.edgeFinset.card ≤ Fintype.card W * Fintype.card V) V ?_ ?_
  · intro V _ _ G _ _
    have hG : G = ⊥ := Subsingleton.elim _ _
    rw [edgeFinset_eq_empty.mpr hG]
    exact Nat.zero_le _
  · intro V _ _ ih G _ hfree
    by_cases hdeg : ∀ v, Fintype.card W ≤ G.degree v
    · exact (hfree (tree_copy_of_degree_bound G T hT hdeg)).elim
    · push_neg at hdeg
      obtain ⟨v, hv⟩ := hdeg
      have hsmall : Fintype.card ↥({v}ᶜ : Set V) < Fintype.card V :=
        Fintype.card_subtype_lt (x := v) (by simp)
      have hfree' : T.Free (G.induce {v}ᶜ) :=
        fun h => hfree (h.trans ⟨Copy.induce G {v}ᶜ⟩)
      have hbound := ih ↥({v}ᶜ : Set V) hsmall (G.induce {v}ᶜ) inferInstance hfree'
      rw [card_edgeFinset_induce_compl_singleton,
        card_edgeFinset_deleteIncidenceSet, Fintype.card_compl_set] at hbound
      simp only [Fintype.card_unique] at hbound
      calc
        G.edgeFinset.card = (G.edgeFinset.card - G.degree v) + G.degree v :=
          (Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)).symm
        _ ≤ Fintype.card W * (Fintype.card V - 1) + Fintype.card W :=
          Nat.add_le_add hbound hv.le
        _ = Fintype.card W * Fintype.card V := by
          rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel Fintype.card_pos]

open scoped Classical in
 theorem extremal_tree_bound {W : Type*} [Fintype W] (T : SimpleGraph W)
    (hT : T.IsTree) (n : ℕ) : extremalNumber n T ≤ Fintype.card W * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  exact free_tree_edge_bound T hT G hfree

open scoped Classical in
 theorem extremal_forest_bound {W : Type*} [Fintype W] [Nonempty W]
    (F : SimpleGraph W) (hF : F.IsAcyclic) (n : ℕ) :
    extremalNumber n F ≤ Fintype.card W * n := by
  classical
  obtain ⟨T, hFT, hT⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
    (G := (⊤ : SimpleGraph W)) le_top hF
  have ht : T.IsTree := connected_top.maximal_le_isAcyclic_iff_isTree le_top |>.mp hT
  calc
    extremalNumber n F ≤ extremalNumber n T :=
      (show F ⊑ T from ⟨Copy.ofLE F T hFT⟩).extremalNumber_le
    _ ≤ Fintype.card W * n := extremal_tree_bound T ht n

theorem exponent_le_of_isBigO {a b : ℝ}
    (h : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ b)) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  obtain ⟨C, _, hC⟩ := h.exists_pos
  have hdiv : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (a - b) ≤ C := by
    filter_upwards [hC.bound, eventually_gt_atTop (0 : ℕ)] with n hn hnp
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hnp
    rw [Real.rpow_sub hnpos, div_le_iff₀ (Real.rpow_pos_of_pos hnpos b)]
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)] using hn
  have htop : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hba)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hn'⟩ := (hdiv.and (htop.eventually_gt_atTop C)).exists
  exact (not_lt_of_ge hn) hn'

theorem forest_exponent_eq_one {W : Type*} [Fintype W] [Nonempty W]
    (F : SimpleGraph W) (hF : F.IsAcyclic) {a c : ℝ} (ha : 1 ≤ a) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n F : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = 1 := by
  have hb : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    apply IsBigO.of_bound (Fintype.card W : ℝ)
    filter_upwards with n
    simp only [Real.norm_natCast, Real.rpow_one]
    exact_mod_cast extremal_forest_bound F hF n
  have hp : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) :=
    (isBigO_const_mul_left_iff hc.ne').mp (h.isBigO_symm.trans hb)
  exact le_antisymm (exponent_le_of_isBigO hp) ha

open scoped Classical in
 theorem rational_exponent_of_acyclic (q : ℕ) (G : SimpleGraph (Fin q))
    (hG : G.IsAcyclic) (he : 2 ≤ G.edgeFinset.card)
    (a c : ℝ) (ha : a ∈ Set.Ico 1 2) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  have hq : 0 < q := by
    have hbound := G.card_edgeFinset_le_card_choose_two
    simp only [Fintype.card_fin] at hbound
    by_contra hq
    have hq' : q = 0 := Nat.eq_zero_of_not_pos hq
    simp only [hq', Nat.choose_zero_succ] at hbound
    omega
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  have ha1 := forest_exponent_eq_one G hG ha.1 hc h
  exact ⟨1, by simpa using ha1.symm⟩

end Erdos713Forest

namespace Erdos713C6

open Finset

abbrev C6 := cycleGraph 6

def bipGraph {P L : Type*} (R : P → L → Prop) : SimpleGraph (P ⊕ L) where
  Adj u v := match u, v with
    | Sum.inl x, Sum.inr y => R x y
    | Sum.inr y, Sum.inl x => R x y
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp
  loopless := by intro v; cases v <;> simp

theorem right_of_adj_left {P L : Type*} {R : P → L → Prop} {x : P} {v : P ⊕ L}
    (h : (bipGraph R).Adj (Sum.inl x) v) : ∃ y, v = Sum.inr y ∧ R x y := by
  cases v with
  | inl y => exact h.elim
  | inr y => exact ⟨y, rfl, h⟩

theorem left_of_adj_right {P L : Type*} {R : P → L → Prop} {y : L} {v : P ⊕ L}
    (h : (bipGraph R).Adj (Sum.inr y) v) : ∃ x, v = Sum.inl x ∧ R x y := by
  cases v with
  | inl x => exact ⟨x, rfl, h⟩
  | inr x => exact h.elim

theorem injective_triple_of_map {U V : Type*} (f : Fin 6 → V) (hf : Function.Injective f)
    (g : U → V) (x : Fin 3 → U) (k : Fin 3 → Fin 6) (hk : Function.Injective k)
    (he : ∀ i, f (k i) = g (x i)) : Function.Injective x := by
  intro i j hij
  apply hk
  apply hf
  rw [he i, he j, hij]

theorem free_of_no_hexagon {P L : Type*} (R : P → L → Prop)
    (h : ∀ (a : Fin 3 → P) (b : Fin 3 → L), Function.Injective a → Function.Injective b →
      (∀ i, R (a i) (b i)) → (∀ i, R (a (i + 1)) (b i)) → False) :
    C6.Free (bipGraph R) := by
  rintro ⟨f⟩
  have h01 := f.toHom.map_rel' (show C6.Adj 0 1 by decide)
  have h12 := f.toHom.map_rel' (show C6.Adj 1 2 by decide)
  have h23 := f.toHom.map_rel' (show C6.Adj 2 3 by decide)
  have h34 := f.toHom.map_rel' (show C6.Adj 3 4 by decide)
  have h45 := f.toHom.map_rel' (show C6.Adj 4 5 by decide)
  have h50 := f.toHom.map_rel' (show C6.Adj 5 0 by decide)
  change (bipGraph R).Adj (f 0) (f 1) at h01
  change (bipGraph R).Adj (f 1) (f 2) at h12
  change (bipGraph R).Adj (f 2) (f 3) at h23
  change (bipGraph R).Adj (f 3) (f 4) at h34
  change (bipGraph R).Adj (f 4) (f 5) at h45
  change (bipGraph R).Adj (f 5) (f 0) at h50
  cases e0 : f 0 with
  | inl x₀ =>
    rw [e0] at h01
    obtain ⟨y₀, e1, h00⟩ := right_of_adj_left h01
    rw [e1] at h12
    obtain ⟨x₁, e2, h10⟩ := left_of_adj_right h12
    rw [e2] at h23
    obtain ⟨y₁, e3, h11⟩ := right_of_adj_left h23
    rw [e3] at h34
    obtain ⟨x₂, e4, h21⟩ := left_of_adj_right h34
    rw [e4] at h45
    obtain ⟨y₂, e5, h22⟩ := right_of_adj_left h45
    have h02 : R x₀ y₂ := by simpa only [e5, e0] using h50
    apply h ![x₀, x₁, x₂] ![y₀, y₁, y₂]
    · apply injective_triple_of_map f f.injective Sum.inl _ ![0, 2, 4] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_triple_of_map f f.injective Sum.inr _ ![1, 3, 5] (by decide)
      intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
  | inr y₀ =>
    rw [e0] at h01
    obtain ⟨x₀, e1, h00⟩ := left_of_adj_right h01
    rw [e1] at h12
    obtain ⟨y₁, e2, h01'⟩ := right_of_adj_left h12
    rw [e2] at h23
    obtain ⟨x₁, e3, h11⟩ := left_of_adj_right h23
    rw [e3] at h34
    obtain ⟨y₂, e4, h12'⟩ := right_of_adj_left h34
    rw [e4] at h45
    obtain ⟨x₂, e5, h22⟩ := left_of_adj_right h45
    have h20 : R x₂ y₀ := by simpa only [e5, e0] using h50
    apply h ![x₀, x₁, x₂] ![y₁, y₂, y₀]
    · apply injective_triple_of_map f f.injective Sum.inl _ ![1, 3, 5] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_triple_of_map f f.injective Sum.inr _ ![2, 4, 0] (by decide)
      intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption

abbrev Triple (F : Type*) := F × F × F

def WengerRel {F : Type*} [Field F] (p l : Triple F) : Prop :=
  p.2.1 = l.1 * p.1 + l.2.1 ∧ p.2.2 = l.1 ^ 2 * p.1 + l.2.2

abbrev wengerGraph (F : Type*) [Field F] := bipGraph (WengerRel (F := F))

theorem point_eq_of_x_eq {F : Type*} [Field F] {p q l : Triple F}
    (hp : WengerRel p l) (hq : WengerRel q l) (h : p.1 = q.1) : p = q := by
  apply Prod.ext h
  apply Prod.ext <;> dsimp
  · rw [hp.1, hq.1, h]
  · rw [hp.2, hq.2, h]

theorem line_eq_of_slope_eq {F : Type*} [Field F] {p l m : Triple F}
    (hl : WengerRel p l) (hm : WengerRel p m) (h : l.1 = m.1) : l = m := by
  apply Prod.ext h
  apply Prod.ext <;> dsimp
  · linear_combination hm.1 - hl.1 - p.1 * h
  · have ht := hl.2
    rw [h] at ht
    exact add_left_cancel (ht.symm.trans hm.2)

theorem wenger_no_hexagon {F : Type*} [Field F] (p l : Fin 3 → Triple F)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, WengerRel (p i) (l i)) (hB : ∀ i, WengerRel (p (i + 1)) (l i)) : False := by
  have h01 : (l 0).1 ≠ (l 1).1 := by
    intro h
    exact (show (0 : Fin 3) ≠ 1 by decide)
      (hl (line_eq_of_slope_eq (hB 0) (hA 1) h))
  have h02 : (l 0).1 ≠ (l 2).1 := by
    intro h
    exact (show (0 : Fin 3) ≠ 2 by decide)
      (hl (line_eq_of_slope_eq (hA 0) (hB 2) h))
  have hx01 : (p 0).1 ≠ (p 1).1 := by
    intro h
    exact (show (0 : Fin 3) ≠ 1 by decide)
      (hp (point_eq_of_x_eq (hA 0) (hB 0) h))
  have hb0 : WengerRel (p 1) (l 0) := hB 0
  have hb1 : WengerRel (p 2) (l 1) := hB 1
  have hb2 : WengerRel (p 0) (l 2) := hB 2
  have hy : (l 0).1 * ((p 0).1 - (p 1).1) +
      (l 1).1 * ((p 1).1 - (p 2).1) + (l 2).1 * ((p 2).1 - (p 0).1) = 0 := by
    linear_combination -(hA 0).1 + hb0.1 - (hA 1).1 + hb1.1 -
      (hA 2).1 + hb2.1
  have hz : (l 0).1 ^ 2 * ((p 0).1 - (p 1).1) +
      (l 1).1 ^ 2 * ((p 1).1 - (p 2).1) + (l 2).1 ^ 2 * ((p 2).1 - (p 0).1) = 0 := by
    linear_combination -(hA 0).2 + hb0.2 - (hA 1).2 + hb1.2 -
      (hA 2).2 + hb2.2
  have hprod : ((l 0).1 - (l 1).1) * ((l 0).1 - (l 2).1) *
      ((p 0).1 - (p 1).1) = 0 := by
    linear_combination hz - ((l 1).1 + (l 2).1) * hy
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h01) (sub_ne_zero.mpr h02))
    (sub_ne_zero.mpr hx01) hprod

theorem wengerGraph_free (F : Type*) [Field F] : C6.Free (wengerGraph F) :=
  free_of_no_hexagon WengerRel wenger_no_hexagon

def leftNeighbors {F : Type*} [Field F] (p : Triple F) :
    F ↪ (wengerGraph F).neighborSet (Sum.inl p) where
  toFun a := ⟨Sum.inr (a, p.2.1 - a * p.1, p.2.2 - a ^ 2 * p.1), by
    change WengerRel p _
    constructor <;> dsimp <;> ring⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Triple F => x.1)
      (fun x : Triple F => x.1) v.val) h

def rightNeighbors {F : Type*} [Field F] (l : Triple F) :
    F ↪ (wengerGraph F).neighborSet (Sum.inr l) where
  toFun x := ⟨Sum.inl (x, l.1 * x + l.2.1, l.1 ^ 2 * x + l.2.2), by
    change WengerRel _ l
    exact ⟨rfl, rfl⟩⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Triple F => x.1)
      (fun x : Triple F => x.1) v.val) h

open scoped Classical in
theorem wengerGraph_degree_lower (F : Type*) [Field F] [Fintype F]
    (v : Triple F ⊕ Triple F) : Fintype.card F ≤ (wengerGraph F).degree v := by
  classical
  rw [← card_neighborSet_eq_degree]
  cases v with
  | inl p => exact Fintype.card_le_of_embedding (leftNeighbors p)
  | inr l => exact Fintype.card_le_of_embedding (rightNeighbors l)

open scoped Classical in
theorem wengerGraph_edge_lower (F : Type*) [Field F] [Fintype F] :
    Fintype.card F ^ 4 ≤ (wengerGraph F).edgeFinset.card := by
  classical
  have hh : ∑ v : Triple F ⊕ Triple F, Fintype.card F ≤
      ∑ v : Triple F ⊕ Triple F, (wengerGraph F).degree v :=
    sum_le_sum fun v _ => wengerGraph_degree_lower F v
  rw [sum_degrees_eq_twice_card_edges] at hh
  simp only [sum_const, card_univ, Fintype.card_sum, Triple, Fintype.card_prod,
    Nat.nsmul_eq_mul] at hh
  nlinarith

theorem extremal_lower_prime (p : ℕ) (hp : p.Prime) :
    p ^ 4 ≤ extremalNumber (2 * p ^ 3) C6 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have he := wengerGraph_edge_lower (ZMod p)
  have hExt := card_edgeFinset_le_extremalNumber (wengerGraph_free (ZMod p))
  have hc : Fintype.card (Triple (ZMod p) ⊕ Triple (ZMod p)) = 2 * p ^ 3 := by
    simp only [Triple, Fintype.card_sum, Fintype.card_prod, ZMod.card]
    ring
  rw [hc] at hExt
  rw [ZMod.card] at he
  exact he.trans hExt

theorem lower_exponent_of_prime_bound {f : ℕ → ℕ} {a : ℝ}
    (hO : (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hlow : ∀ p : ℕ, p.Prime → p ^ 4 ≤ f (2 * p ^ 3)) : (4 : ℝ) / 3 ≤ a := by
  by_contra ha
  have ha' : a < (4 : ℝ) / 3 := lt_of_not_ge ha
  obtain ⟨C, _, hC⟩ := hO.exists_pos
  have ht : Tendsto (fun p : ℕ => 2 * p ^ 3) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro p
    have hp := Nat.le_self_pow (by decide : 3 ≠ 0) p
    change p ≤ 2 * p ^ 3
    omega
  have hratio : ∀ᶠ p : ℕ in atTop,
      p.Prime → (p : ℝ) ^ (4 - 3 * a) ≤ C * (2 : ℝ) ^ a := by
    filter_upwards [ht.eventually hC.bound, eventually_gt_atTop (0 : ℕ)] with p hp hpos
    intro hprime
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpos
    have hl : (p : ℝ) ^ 4 ≤ (f (2 * p ^ 3) : ℝ) := by exact_mod_cast hlow p hprime
    have hu : (f (2 * p ^ 3) : ℝ) ≤ C * (2 * (p : ℝ) ^ 3) ^ a := by
      rw [Real.norm_natCast, Real.norm_of_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg (2 * p ^ 3)) a)] at hp
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hp
    have he := hl.trans hu
    have hp3 : ((p : ℝ) ^ 3) ^ a = (p : ℝ) ^ (3 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      norm_num
    rw [Real.mul_rpow (by norm_num) (pow_nonneg hp0.le 3), hp3] at he
    rw [Real.rpow_sub hp0, div_le_iff₀ (Real.rpow_pos_of_pos hp0 (3 * a))]
    have hp4 : (p : ℝ) ^ (4 : ℝ) = (p : ℝ) ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (p : ℝ) 4
    rw [hp4]
    simpa only [mul_assoc] using he
  have htop : Tendsto (fun p : ℕ => (p : ℝ) ^ (4 - 3 * a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 4 - 3 * a)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hratio.and (htop.eventually_gt_atTop (C * (2 : ℝ) ^ a)))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  exact (not_lt_of_ge ((hN p hpN).1 hp)) ((hN p hpN).2)

theorem exponent_lower_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : C6 ⊑ H) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : (4 : ℝ) / 3 ≤ a := by
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc).mp h.isBigO
  apply lower_exponent_of_prime_bound hO
  intro p hp
  exact (extremal_lower_prime p hp).trans hH.extremalNumber_le

end Erdos713C6

namespace Erdos713C6

open Finset

theorem pathGraph_six_tree : (pathGraph 6).IsTree := by
  letI : DecidableRel (pathGraph 6).Adj := fun u v =>
    decidable_of_iff (u.val + 1 = v.val ∨ v.val + 1 = u.val) pathGraph_adj.symm
  apply isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected 5, ?_⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem injective_pair {U : Type*} {x y : U} (hxy : x ≠ y) :
    Function.Injective ![x, y] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem free_path_of_no_alternating_path {P L : Type*} (R : P → L → Prop)
    (h : ∀ (a : Fin 3 → P) (b : Fin 2 → L), Function.Injective a → Function.Injective b →
      R (a 0) (b 0) → R (a 1) (b 0) → R (a 1) (b 1) → R (a 2) (b 1) → False) :
    (pathGraph 6).Free (bipGraph R) := by
  rintro ⟨f⟩
  have h01 := f.toHom.map_rel' (show (pathGraph 6).Adj 0 1 by simp [pathGraph_adj])
  have h12 := f.toHom.map_rel' (show (pathGraph 6).Adj 1 2 by simp [pathGraph_adj])
  have h23 := f.toHom.map_rel' (show (pathGraph 6).Adj 2 3 by simp [pathGraph_adj])
  have h34 := f.toHom.map_rel' (show (pathGraph 6).Adj 3 4 by simp [pathGraph_adj])
  have h45 := f.toHom.map_rel' (show (pathGraph 6).Adj 4 5 by simp [pathGraph_adj])
  change (bipGraph R).Adj (f 0) (f 1) at h01
  change (bipGraph R).Adj (f 1) (f 2) at h12
  change (bipGraph R).Adj (f 2) (f 3) at h23
  change (bipGraph R).Adj (f 3) (f 4) at h34
  change (bipGraph R).Adj (f 4) (f 5) at h45
  cases e0 : f 0 with
  | inl x₀ =>
    rw [e0] at h01
    obtain ⟨y₀, e1, h00⟩ := right_of_adj_left h01
    rw [e1] at h12
    obtain ⟨x₁, e2, h10⟩ := left_of_adj_right h12
    rw [e2] at h23
    obtain ⟨y₁, e3, h11⟩ := right_of_adj_left h23
    rw [e3] at h34
    obtain ⟨x₂, e4, h21⟩ := left_of_adj_right h34
    apply h ![x₀, x₁, x₂] ![y₀, y₁] ?_ ?_ h00 h10 h11 h21
    · apply injective_triple_of_map f f.injective Sum.inl _ ![0, 2, 4] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_pair
      intro hy
      have he : f 1 = f 3 := e1.trans ((congrArg Sum.inr hy).trans e3.symm)
      exact (show (1 : Fin 6) ≠ 3 by decide) (f.injective he)
  | inr y₀ =>
    rw [e0] at h01
    obtain ⟨x₀, e1, _⟩ := left_of_adj_right h01
    rw [e1] at h12
    obtain ⟨y₁, e2, h01'⟩ := right_of_adj_left h12
    rw [e2] at h23
    obtain ⟨x₁, e3, h11⟩ := left_of_adj_right h23
    rw [e3] at h34
    obtain ⟨y₂, e4, h12'⟩ := right_of_adj_left h34
    rw [e4] at h45
    obtain ⟨x₂, e5, h22⟩ := left_of_adj_right h45
    apply h ![x₀, x₁, x₂] ![y₁, y₂] ?_ ?_ h01' h11 h12' h22
    · apply injective_triple_of_map f f.injective Sum.inl _ ![1, 3, 5] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_pair
      intro hy
      have he : f 2 = f 4 := e2.trans ((congrArg Sum.inr hy).trans e4.symm)
      exact (show (2 : Fin 6) ≠ 4 by decide) (f.injective he)

open scoped Classical in
theorem edge_bound_no_alternating_path {P L : Type*} [Fintype P] [Fintype L]
    (R : P → L → Prop)
    (h : ∀ (a : Fin 3 → P) (b : Fin 2 → L), Function.Injective a → Function.Injective b →
      R (a 0) (b 0) → R (a 1) (b 0) → R (a 1) (b 1) → R (a 2) (b 1) → False) :
    (bipGraph R).edgeFinset.card ≤ 6 * (Fintype.card P + Fintype.card L) := by
  have hh := Erdos713Forest.free_tree_edge_bound (pathGraph 6) pathGraph_six_tree
    (bipGraph R) (free_path_of_no_alternating_path R h)
  simpa only [Fintype.card_fin, Fintype.card_sum] using hh

end Erdos713C6

#print axioms Erdos713C6.edge_bound_no_alternating_path
namespace Erdos713C6

open Finset

theorem contained_of_hexagon {V : Type*} (G : SimpleGraph V) (a b : Fin 3 → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (hA : ∀ i, G.Adj (a i) (b i)) (hB : ∀ i, G.Adj (a (i + 1)) (b i)) : C6 ⊑ G := by
  let g : Fin 6 → V := ![a 0, b 0, a 1, b 1, a 2, b 2]
  have h00 := hA 0
  have h11 := hA 1
  have h22 := hA 2
  have h10 : G.Adj (a 1) (b 0) := hB 0
  have h21 : G.Adj (a 2) (b 1) := hB 1
  have h02 : G.Adj (a 0) (b 2) := hB 2
  have hba (i j) : b i ≠ a j := (hab j i).symm
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · have hStep (i : Fin 6) : G.Adj (g i) (g (i + 1)) := by
      fin_cases i <;> dsimp [g]
      all_goals first | assumption | exact h00.symm | exact h11.symm | exact h22.symm |
        exact h10.symm | exact h21.symm | exact h02.symm
    intro u v huv
    rcases cycleGraph_adj.mp huv with he | he
    · rw [sub_eq_iff_eq_add'.mp he]
      exact (hStep v).symm
    · rw [sub_eq_iff_eq_add'.mp he]
      exact hStep u
  · intro u v huv
    change g u = g v at huv
    fin_cases u <;> fin_cases v <;> simp_all [g, ha.eq_iff, hb.eq_iff]

theorem free_path_of_no_alternating_path_sets {V : Type*} (G : SimpleGraph V)
    {A B : Set V} (hBip : G.IsBipartiteWith A B)
    (h : ∀ (a : Fin 3 → V) (b : Fin 2 → V), Function.Injective a → Function.Injective b →
      (∀ i, a i ∈ A) → (∀ j, b j ∈ B) →
      G.Adj (a 0) (b 0) → G.Adj (a 1) (b 0) → G.Adj (a 1) (b 1) → G.Adj (a 2) (b 1) → False) :
    (pathGraph 6).Free G := by
  rintro ⟨f⟩
  have h01 := f.toHom.map_rel' (show (pathGraph 6).Adj 0 1 by simp [pathGraph_adj])
  have h12 := f.toHom.map_rel' (show (pathGraph 6).Adj 1 2 by simp [pathGraph_adj])
  have h23 := f.toHom.map_rel' (show (pathGraph 6).Adj 2 3 by simp [pathGraph_adj])
  have h34 := f.toHom.map_rel' (show (pathGraph 6).Adj 3 4 by simp [pathGraph_adj])
  have h45 := f.toHom.map_rel' (show (pathGraph 6).Adj 4 5 by simp [pathGraph_adj])
  rcases hBip.mem_of_adj h01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have h2 := hBip.symm.mem_of_mem_adj h1 h12
    have h3 := hBip.mem_of_mem_adj h2 h23
    have h4 := hBip.symm.mem_of_mem_adj h3 h34
    apply h (f ∘ ![0, 2, 4]) (f ∘ ![1, 3])
      (f.injective.comp (by decide)) (f.injective.comp (by decide))
      (by intro i; fin_cases i <;> assumption) (by intro i; fin_cases i <;> assumption)
      h01 h12.symm h23 h34.symm
  · have h2 := hBip.mem_of_mem_adj h1 h12
    have h3 := hBip.symm.mem_of_mem_adj h2 h23
    have h4 := hBip.mem_of_mem_adj h3 h34
    have h5 := hBip.symm.mem_of_mem_adj h4 h45
    apply h (f ∘ ![1, 3, 5]) (f ∘ ![2, 4])
      (f.injective.comp (by decide)) (f.injective.comp (by decide))
      (by intro i; fin_cases i <;> assumption) (by intro i; fin_cases i <;> assumption)
      h12 h23.symm h34 h45.symm

open scoped Classical in
theorem edge_bound_no_alternating_path_sets {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {A B : Finset V} (hBip : G.IsBipartiteWith A B)
    (h : ∀ (a : Fin 3 → V) (b : Fin 2 → V), Function.Injective a → Function.Injective b →
      (∀ i, a i ∈ A) → (∀ j, b j ∈ B) →
      G.Adj (a 0) (b 0) → G.Adj (a 1) (b 0) → G.Adj (a 1) (b 1) → G.Adj (a 2) (b 1) → False) :
    G.edgeFinset.card ≤ 6 * (A.card + B.card) := by
  classical
  have hfree := free_path_of_no_alternating_path_sets G hBip h
  have hs : G.support ⊆ (↑(A ∪ B) : Set V) := by
    simpa only [coe_union] using isBipartiteWith_support_subset hBip
  have hiFree : (pathGraph 6).Free (G.induce (↑(A ∪ B) : Set V)) := by
    intro hc
    exact hfree (hc.trans ⟨Copy.induce G _⟩)
  have hh := Erdos713Forest.free_tree_edge_bound (pathGraph 6) pathGraph_six_tree
    (G.induce (↑(A ∪ B) : Set V)) hiFree
  have hEq : Nat.card (G.induce (↑(A ∪ B) : Set V)).edgeSet = Nat.card G.edgeSet := by
    simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using
      card_edgeFinset_induce_of_support_subset hs
  have hc : Nat.card ↥(↑(A ∪ B) : Set V) = A.card + B.card := by
    simp only [Nat.card_coe_set_eq, Set.ncard_coe_finset,
      card_union_of_disjoint (disjoint_coe.mp hBip.disjoint)]
  have hh' : Nat.card (G.induce (↑(A ∪ B) : Set V)).edgeSet ≤ 6 * (A.card + B.card) := by
    simpa only [edgeFinset_card, Fintype.card_fin, Fintype.card_eq_nat_card, Nat.card_fin, hc] using hh
  rw [hEq] at hh'
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using hh'

end Erdos713C6
namespace Erdos713C6

open Finset

theorem injective_triple {U : Type*} {x y z : U} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective ![x, y, z] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

open scoped Classical in
theorem degree_cube_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : C6.Free G) (d : ℕ)
    (hd : ∀ u v, G.Adj u v → d ≤ G.degree u) {v w : V} (hvw : G.Adj v w) :
    d ^ 3 ≤ 24 ^ 3 * Fintype.card V := by
  classical
  obtain ⟨χ⟩ := hBip
  let A := G.neighborFinset v
  let B := (A.biUnion (fun a => G.neighborFinset a)).erase v
  let C := (B.biUnion (fun b => G.neighborFinset b)) \ A
  have hA (a : V) : a ∈ A ↔ G.Adj v a := mem_neighborFinset G v a
  have hB (b : V) : b ∈ B ↔ b ≠ v ∧ ∃ a ∈ A, G.Adj a b := by
    simp [B, mem_biUnion]
  have hC (c : V) : c ∈ C ↔ (∃ b ∈ B, G.Adj b c) ∧ c ∉ A := by
    simp [C, mem_biUnion]
  have hcolA {a : V} (ha : a ∈ A) : χ a ≠ χ v := (χ.valid ((hA a).mp ha)).symm
  have hcolB {b : V} (hb : b ∈ B) : χ b = χ v := by
    obtain ⟨_, a, ha, hab⟩ := (hB b).mp hb
    have hh := χ.valid hab
    have hh' := hcolA ha
    omega
  have hcolC {c : V} (hc : c ∈ C) : χ c ≠ χ v := by
    obtain ⟨⟨b, hb, hbc⟩, _⟩ := (hC c).mp hc
    have hh := (χ.valid hbc).symm
    rwa [hcolB hb] at hh
  have hcross {x y : V} (hx : χ x = χ v) (hy : χ y ≠ χ v) : x ≠ y := by
    intro he
    exact hy (he ▸ hx)
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact hcolA hx (hcolB hx')
  have hBC : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact hcolC hx' (hcolB hx)
  have hAC : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact ((hC x).mp hx').2 hx
  have hBnot {b : V} (hb : b ∈ B) : b ≠ v := ((hB b).mp hb).1
  have hCA {c a : V} (hc : c ∈ C) (ha : a ∈ A) : c ≠ a := by
    intro he
    exact ((hC c).mp hc).2 (he ▸ ha)
  have hNoAB (a : Fin 3 → V) (b : Fin 2 → V)
      (ha : Function.Injective a) (hb : Function.Injective b)
      (haA : ∀ i, a i ∈ A) (hbB : ∀ j, b j ∈ B)
      (h00 : G.Adj (a 0) (b 0)) (h10 : G.Adj (a 1) (b 0))
      (h11 : G.Adj (a 1) (b 1)) (h21 : G.Adj (a 2) (b 1)) : False := by
    apply hfree
    apply contained_of_hexagon G a ![b 0, b 1, v] ha
      (injective_triple (hb.ne (by decide)) (hBnot (hbB 0)) (hBnot (hbB 1)))
    · intro i j
      fin_cases j
      · exact (hcross (hcolB (hbB 0)) (hcolA (haA i))).symm
      · exact (hcross (hcolB (hbB 1)) (hcolA (haA i))).symm
      · exact (hcross rfl (hcolA (haA i))).symm
    · intro i; fin_cases i
      · exact h00
      · exact h11
      · exact ((hA _).mp (haA 2)).symm
    · intro i; fin_cases i
      · exact h10
      · exact h21
      · exact ((hA _).mp (haA 0)).symm
  have parent_eq {b₁ b₂ c a₁ a₂ : V}
      (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hc : c ∈ C) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
      (hne : b₁ ≠ b₂) (he₁ : G.Adj a₁ b₁) (he₂ : G.Adj a₂ b₂)
      (hf₁ : G.Adj b₁ c) (hf₂ : G.Adj b₂ c) : a₁ = a₂ := by
    by_contra hneA
    apply hfree
    apply contained_of_hexagon G ![v, b₁, b₂] ![a₁, c, a₂]
      (injective_triple (hBnot hb₁).symm (hBnot hb₂).symm hne)
      (injective_triple (hCA hc ha₁).symm hneA (hCA hc ha₂))
    · intro i j
      apply hcross
      · fin_cases i
        · rfl
        · exact hcolB hb₁
        · exact hcolB hb₂
      · fin_cases j
        · exact hcolA ha₁
        · exact hcolC hc
        · exact hcolA ha₂
    · intro i; fin_cases i
      · exact (hA _).mp ha₁
      · exact hf₁
      · exact he₂.symm
    · intro i; fin_cases i
      · exact he₁.symm
      · exact hf₂
      · exact (hA _).mp ha₂
  have hNoBC (b : Fin 3 → V) (c : Fin 2 → V)
      (hb : Function.Injective b) (hc : Function.Injective c)
      (hbB : ∀ i, b i ∈ B) (hcC : ∀ j, c j ∈ C)
      (h00 : G.Adj (b 0) (c 0)) (h10 : G.Adj (b 1) (c 0))
      (h11 : G.Adj (b 1) (c 1)) (h21 : G.Adj (b 2) (c 1)) : False := by
    obtain ⟨a₀, ha₀, he₀⟩ := ((hB _).mp (hbB 0)).2
    obtain ⟨a₁, ha₁, he₁⟩ := ((hB _).mp (hbB 1)).2
    obtain ⟨a₂, ha₂, he₂⟩ := ((hB _).mp (hbB 2)).2
    have h01 := parent_eq (hbB 0) (hbB 1) (hcC 0) ha₀ ha₁
      (hb.ne (by decide)) he₀ he₁ h00 h10
    have h12 := parent_eq (hbB 1) (hbB 2) (hcC 1) ha₁ ha₂
      (hb.ne (by decide)) he₁ he₂ h11 h21
    have hb0a : G.Adj (b 0) a₁ := by simpa only [h01] using he₀.symm
    have hb2a : G.Adj (b 2) a₁ := by simpa only [← h12] using he₂.symm
    apply hfree
    apply contained_of_hexagon G b ![c 0, c 1, a₁] hb
      (injective_triple (hc.ne (by decide)) (hCA (hcC 0) ha₁) (hCA (hcC 1) ha₁))
    · intro i j
      apply hcross (hcolB (hbB i))
      fin_cases j
      · exact hcolC (hcC 0)
      · exact hcolC (hcC 1)
      · exact hcolA ha₁
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
  let AB := G.between (↑A) (↑B)
  let BC := G.between (↑B) (↑C)
  have hABip : AB.IsBipartiteWith A B := between_isBipartiteWith (disjoint_coe.mpr hAB)
  have hBCip : BC.IsBipartiteWith B C := between_isBipartiteWith (disjoint_coe.mpr hBC)
  have heAB : AB.edgeFinset.card ≤ 6 * (A.card + B.card) := by
    apply edge_bound_no_alternating_path_sets AB hABip
    intro a b ha hb haA hbB h00 h10 h11 h21
    exact hNoAB a b ha hb haA hbB h00.1 h10.1 h11.1 h21.1
  have heBC : BC.edgeFinset.card ≤ 6 * (B.card + C.card) := by
    apply edge_bound_no_alternating_path_sets BC hBCip
    intro b c hb hc hbB hcC h00 h10 h11 h21
    exact hNoBC b c hb hc hbB hcC h00.1 h10.1 h11.1 h21.1
  have hADeg (a : V) (ha : a ∈ A) : d ≤ AB.degree a + 1 := by
    have hsub : G.neighborFinset a ⊆ insert v (AB.neighborFinset a) := by
      intro b hb
      by_cases hbv : b = v
      · simp [hbv]
      · apply mem_insert_of_mem
        rw [mem_neighborFinset]
        exact ⟨(mem_neighborFinset _ _ _).mp hb, Or.inl ⟨ha, (hB b).mpr ⟨hbv, a, ha,
          (mem_neighborFinset _ _ _).mp hb⟩⟩⟩
    have hh := (card_le_card hsub).trans (card_insert_le v (AB.neighborFinset a))
    simp only [card_neighborFinset_eq_degree] at hh
    exact (hd a v ((hA a).mp ha).symm).trans hh
  have hBDeg (b : V) (hb : b ∈ B) : d ≤ AB.degree b + BC.degree b := by
    have hsub : G.neighborFinset b ⊆ AB.neighborFinset b ∪ BC.neighborFinset b := by
      intro c hc
      by_cases hcA : c ∈ A
      · apply mem_union_left
        rw [mem_neighborFinset]
        exact ⟨(mem_neighborFinset _ _ _).mp hc, Or.inr ⟨hb, hcA⟩⟩
      · apply mem_union_right
        rw [mem_neighborFinset]
        exact ⟨(mem_neighborFinset _ _ _).mp hc, Or.inl ⟨hb,
          (hC c).mpr ⟨⟨b, hb, (mem_neighborFinset _ _ _).mp hc⟩, hcA⟩⟩⟩
    have hh := (card_le_card hsub).trans (card_union_le _ _)
    simp only [card_neighborFinset_eq_degree] at hh
    obtain ⟨a, ha, hab⟩ := ((hB b).mp hb).2
    exact (hd b a hab.symm).trans hh
  have hsA : d * A.card ≤ AB.edgeFinset.card + A.card := by
    have hh := sum_le_sum (s := A) (fun a ha => hADeg a ha)
    rw [sum_add_distrib, isBipartiteWith_sum_degrees_eq_card_edges hABip] at hh
    simpa only [sum_const, Nat.nsmul_eq_mul, mul_one, one_mul, mul_comm] using hh
  have hsB : d * B.card ≤ AB.edgeFinset.card + BC.edgeFinset.card := by
    have hh := sum_le_sum (s := B) (fun b hb => hBDeg b hb)
    rw [sum_add_distrib, isBipartiteWith_sum_degrees_eq_card_edges hABip.symm,
      isBipartiteWith_sum_degrees_eq_card_edges hBCip] at hh
    simpa only [sum_const, Nat.nsmul_eq_mul, mul_comm] using hh
  have hdA : d ≤ A.card := hd v w hvw
  have hACn : A.card + C.card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint hAC]
    exact card_le_univ _
  have hnp : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  by_cases hd24 : d ≤ 24
  · exact (Nat.pow_le_pow_left hd24 3).trans
      (Nat.le_mul_of_pos_right _ hnp)
  · have hd14 : 14 ≤ d := by omega
    have hd24' : 24 ≤ d := by omega
    have h1 : d * A.card ≤ 12 * B.card := by
      have hh := Nat.mul_le_mul_right A.card hd14
      nlinarith
    have h2 : d * B.card ≤ 12 * Fintype.card V := by
      have hh := Nat.mul_le_mul_right B.card hd24'
      nlinarith
    have hd2 : d ^ 2 ≤ 12 * B.card := by
      have hh := Nat.mul_le_mul_left d hdA
      nlinarith
    have hh := Nat.mul_le_mul_left d hd2
    have h3 : d ^ 3 ≤ 144 * Fintype.card V := by nlinarith
    nlinarith

end Erdos713C6
namespace Erdos713Leaf

open Finset

theorem exists_pruned {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) :
    ∃ K : SimpleGraph V, K ≤ G ∧
      (∀ v, Nat.card (K.neighborSet v) = 0 ∨ d ≤ Nat.card (K.neighborSet v)) ∧
      Nat.card G.edgeSet ≤ Nat.card K.edgeSet + d * Fintype.card V := by
  classical
  let S : Finset (SimpleGraph V) := {K | K ≤ G}
  let weight : SimpleGraph V → ℤ := fun K =>
    (Nat.card K.edgeSet : ℤ) - (d : ℤ) * Nat.card K.support
  obtain ⟨K, hKS, hmax⟩ := exists_max_image S weight
    (show S.Nonempty from ⟨G, by simp [S]⟩)
  have hKG : K ≤ G := by simpa [S] using hKS
  refine ⟨K, hKG, ?_, ?_⟩
  · intro v
    by_cases hd : d ≤ Nat.card (K.neighborSet v)
    · exact Or.inr hd
    left
    by_contra hz
    have hpos : 0 < K.degree v := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using Nat.pos_of_ne_zero hz
    have hlt : K.degree v < d := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using Nat.lt_of_not_ge hd
    have hv : v ∈ K.support := (K.degree_pos_iff_mem_support v).mp hpos
    have hDel : K.deleteIncidenceSet v ∈ S := by
      simpa [S] using (K.deleteIncidenceSet_le v).trans hKG
    have hm := hmax (K.deleteIncidenceSet v) hDel
    dsimp only [weight] at hm
    have he : Nat.card (K.deleteIncidenceSet v).edgeSet + K.degree v = Nat.card K.edgeSet := by
      simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card,
        card_edgeFinset_deleteIncidenceSet] using
        Nat.sub_add_cancel (K.degree_le_card_edgeFinset v)
    have hs : Nat.card (K.deleteIncidenceSet v).support + 1 ≤ Nat.card K.support := by
      have hb := K.card_support_deleteIncidenceSet hv
      have hp : 0 < Fintype.card K.support := Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
      have hh : Fintype.card (K.deleteIncidenceSet v).support + 1 ≤ Fintype.card K.support := by omega
      simpa only [Nat.card_eq_fintype_card] using hh
    have hei : (Nat.card (K.deleteIncidenceSet v).edgeSet : ℤ) + K.degree v =
        (Nat.card K.edgeSet : ℤ) := by exact_mod_cast he
    have hsi : (Nat.card (K.deleteIncidenceSet v).support : ℤ) + 1 ≤
        (Nat.card K.support : ℤ) := by exact_mod_cast hs
    have hlti : (K.degree v : ℤ) < (d : ℤ) := by exact_mod_cast hlt
    have hmul := mul_le_mul_of_nonneg_left hsi (Int.natCast_nonneg d)
    nlinarith
  · have hm := hmax G (by simp [S])
    dsimp only [weight] at hm
    have hs : Nat.card G.support ≤ Fintype.card V := by
      simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le (· ∈ G.support)
    have hsi : (Nat.card G.support : ℤ) ≤ (Fintype.card V : ℤ) := by exact_mod_cast hs
    have hmul := mul_le_mul_of_nonneg_left hsi (Int.natCast_nonneg d)
    have hprod : 0 ≤ (d : ℤ) * Nat.card K.support := by positivity
    have hb : (Nat.card G.edgeSet : ℤ) ≤
        (Nat.card K.edgeSet : ℤ) + (d : ℤ) * Fintype.card V := by nlinarith
    exact_mod_cast hb


end Erdos713Leaf

namespace Erdos713C6

open Finset

open scoped Classical in
theorem bipartite_edge_cube_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hBip : G.IsBipartite) (hfree : C6.Free G) :
    G.edgeFinset.card ^ 3 ≤ (64 * (24 ^ 3 + 1)) * Fintype.card V ^ 4 := by
  classical
  let e := G.edgeFinset.card
  let n := Fintype.card V
  by_cases he : e = 0
  · change e ^ 3 ≤ _
    simp [he]
  have hGne : G ≠ ⊥ := by
    intro hG
    apply he
    exact congrArg Finset.card (edgeFinset_eq_empty.mpr hG)
  obtain ⟨u, v, huv⟩ := ne_bot_iff_exists_adj.mp hGne
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨u⟩
  let d := e / (2 * n)
  have hdiv : d * (2 * n) ≤ e := Nat.div_mul_le_self e (2 * n)
  obtain ⟨K, hKG, hd, hbound⟩ := Erdos713Leaf.exists_pruned G d
  have hKne : K ≠ ⊥ := by
    intro hK
    have hB : e ≤ d * n := by
      simpa only [hK, edgeSet_bot, Nat.card_eq_fintype_card, Fintype.card_ofIsEmpty,
        zero_add, ← edgeFinset_card] using hbound
    nlinarith only [hB, hdiv, Nat.pos_of_ne_zero he]
  obtain ⟨x, y, hxy⟩ := ne_bot_iff_exists_adj.mp hKne
  have hKBip : K.IsBipartite := Colorable.of_hom (Copy.ofLE K G hKG).toHom hBip
  have hKfree : C6.Free K := fun hc => hfree (hc.mono_right hKG)
  have hd' (x y : V) (hxy : K.Adj x y) : d ≤ K.degree x := by
    rcases hd x with hz | hb
    · have hpos : 0 < K.degree x := hxy.degree_pos_left
      rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] at hz
      omega
    · simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hb
  have hd3 : d ^ 3 ≤ 24 ^ 3 * n := degree_cube_le K hKBip hKfree d hd' hxy
  have heUpper : e ≤ 2 * n * (d + 1) :=
    (Nat.lt_mul_div_succ e (by omega : 0 < 2 * n)).le
  have hdAdd : (d + 1) ^ 3 ≤ 8 * (d ^ 3 + 1) := by
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hle : d + 1 ≤ 2 * d := by omega
      have hh := Nat.pow_le_pow_left hle 3
      nlinarith only [hh]
  have he3 : e ^ 3 ≤ 8 * n ^ 3 * (d + 1) ^ 3 := by
    have hh := Nat.pow_le_pow_left heUpper 3
    nlinarith only [hh]
  have hm1 := Nat.mul_le_mul_left (8 * n ^ 3) hdAdd
  have hm2 := Nat.mul_le_mul_left (64 * n ^ 3) (Nat.add_le_add_right hd3 1)
  have hm3 := Nat.mul_le_mul_left (64 * n ^ 3)
    (show 24 ^ 3 * n + 1 ≤ (24 ^ 3 + 1) * n by omega)
  change e ^ 3 ≤ (64 * (24 ^ 3 + 1)) * n ^ 4
  nlinarith only [he3, hm1, hm2, hm3]

end Erdos713C6

#print axioms Erdos713C6.bipartite_edge_cube_le

namespace Erdos713Cut

open Finset

variable {V : Type*}

def cut (G : SimpleGraph V) (χ : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ χ u ≠ χ v
  symm := fun u v h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun v h => h.1.ne rfl

theorem cut_le (G : SimpleGraph V) (χ : V → Bool) : cut G χ ≤ G := fun _ _ h => h.1

theorem cut_bipartite (G : SimpleGraph V) (χ : V → Bool) : (cut G χ).IsBipartite := by
  let C : (cut G χ).Coloring Bool := ⟨χ, fun h => h.2⟩
  simpa using C.colorable

open scoped Classical in
theorem twice_card_colorings [Fintype V] {u v : V} (huv : u ≠ v) :
    2 * (univ.filter (fun χ : V → Bool => χ u ≠ χ v)).card = Fintype.card (V → Bool) := by
  classical
  let p : (V → Bool) → Prop := fun χ => χ u ≠ χ v
  let flip : (V → Bool) → (V → Bool) := fun χ => Function.update χ u (!(χ u))
  have hinv : Function.Involutive flip := by
    intro χ
    funext w
    by_cases hw : w = u
    · subst w
      simp [flip]
    · simp [flip, hw]
  have hcard : (univ.filter p).card = (univ.filter (fun χ => ¬p χ)).card := by
    apply card_bijective flip hinv.bijective
    intro χ
    cases h₁ : χ u <;> cases h₂ : χ v <;>
      simp [p, flip, huv, huv.symm, h₁, h₂]
  have hh := card_filter_add_card_filter_not (s := (univ : Finset (V → Bool))) p
  rw [← hcard] at hh
  simpa only [card_univ, two_mul] using hh

open scoped Classical in
theorem exists_bipartite_half [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ K : SimpleGraph V, K ≤ G ∧ K.IsBipartite ∧ G.edgeFinset.card ≤ 2 * K.edgeFinset.card := by
  classical
  let r : (V → Bool) → G.Dart → Prop := fun χ d => χ d.fst ≠ χ d.snd
  have hAbove (χ : V → Bool) :
      ((univ : Finset G.Dart).bipartiteAbove r χ).card = 2 * (cut G χ).edgeFinset.card := by
    let e : ↥((univ : Finset G.Dart).bipartiteAbove r χ) ≃ (cut G χ).Dart :=
      { toFun := fun d => ⟨d.val.toProd, ⟨d.val.adj, ((mem_bipartiteAbove r).mp d.prop).2⟩⟩
        invFun := fun d => ⟨⟨d.toProd, d.adj.1⟩,
          (mem_bipartiteAbove r).mpr ⟨mem_univ _, d.adj.2⟩⟩
        left_inv := by intro d; rfl
        right_inv := by intro d; rfl }
    rw [← Fintype.card_coe, Fintype.card_congr e, dart_card_eq_twice_card_edges]
  have hBelow (d : G.Dart) :
      2 * ((univ : Finset (V → Bool)).bipartiteBelow r d).card = Fintype.card (V → Bool) :=
    twice_card_colorings d.adj.ne
  obtain ⟨χ₀, _, hmax⟩ := exists_max_image (univ : Finset (V → Bool))
    (fun χ => (cut G χ).edgeFinset.card) ⟨fun _ => false, mem_univ _⟩
  refine ⟨cut G χ₀, cut_le G χ₀, cut_bipartite G χ₀, ?_⟩
  let N := Fintype.card (V → Bool)
  let M := (cut G χ₀).edgeFinset.card
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := r)
    (s := (univ : Finset (V → Bool))) (t := (univ : Finset G.Dart))
  simp_rw [hAbove] at hsum
  have hDouble : 4 * (∑ χ : V → Bool, (cut G χ).edgeFinset.card) =
      (2 * G.edgeFinset.card) * N := by
    calc
      4 * (∑ χ : V → Bool, (cut G χ).edgeFinset.card) =
          2 * (∑ χ : V → Bool, 2 * (cut G χ).edgeFinset.card) := by
        rw [← mul_sum]
        ring
      _ = 2 * (∑ d : G.Dart, ((univ : Finset (V → Bool)).bipartiteBelow r d).card) :=
        congrArg (2 * ·) hsum
      _ = ∑ d : G.Dart, 2 * ((univ : Finset (V → Bool)).bipartiteBelow r d).card := by rw [mul_sum]
      _ = ∑ _ : G.Dart, N := sum_congr rfl fun d _ => hBelow d
      _ = (2 * G.edgeFinset.card) * N := by
        simp only [sum_const, card_univ, Nat.nsmul_eq_mul, dart_card_eq_twice_card_edges]
  have hSumle : (∑ χ : V → Bool, (cut G χ).edgeFinset.card) ≤ N * M := by
    calc
      (∑ χ : V → Bool, (cut G χ).edgeFinset.card) ≤ ∑ _ : V → Bool, M :=
        sum_le_sum fun χ hχ => hmax χ hχ
      _ = N * M := by simp only [sum_const, card_univ, Nat.nsmul_eq_mul, N]
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  have hMul : N * G.edgeFinset.card ≤ N * (2 * M) := by
    nlinarith only [hDouble, hSumle]
  exact (mul_le_mul_iff_right₀ hN).mp (by simpa only [mul_comm] using hMul)

end Erdos713Cut

namespace Erdos713C6

open Finset

open scoped Classical in
theorem edge_cube_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hfree : C6.Free G) :
    G.edgeFinset.card ^ 3 ≤ (512 * (24 ^ 3 + 1)) * Fintype.card V ^ 4 := by
  classical
  obtain ⟨K, hKG, hKBip, hhalf⟩ := Erdos713Cut.exists_bipartite_half G
  have hKfree : C6.Free K := fun hc => hfree (hc.mono_right hKG)
  have hb := bipartite_edge_cube_le K hKBip hKfree
  have hp := Nat.pow_le_pow_left hhalf 3
  nlinarith only [hb, hp]

theorem extremal_cube_le (n : ℕ) :
    (extremalNumber n C6) ^ 3 ≤ (512 * (24 ^ 3 + 1)) * n ^ 4 := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | C6.Free G}
  change (S.sup (fun G => G.edgeFinset.card)) ^ 3 ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨G, hG, he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
    rw [he]
    have hfree : C6.Free G := by simpa [S] using hG
    simpa only [Fintype.card_fin] using edge_cube_le G hfree
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp

theorem exponent_upper_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : H ⊑ C6) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ (4 : ℝ) / 3 := by
  have hO : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ)) :=
    (isBigO_const_mul_left_iff hc).mp h.isBigO_symm
  have hP : (fun n : ℕ => (n : ℝ) ^ (a * (3 : ℝ))) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ) ^ (3 : ℕ)) := by
    have he (n : ℕ) : ((n : ℝ) ^ a) ^ (3 : ℕ) = (n : ℝ) ^ (a * (3 : ℝ)) := by
      have hh := Real.rpow_mul_natCast (Nat.cast_nonneg (α := ℝ) n) a 3
      norm_num only [Nat.cast_ofNat] at hh
      exact hh.symm
    simpa only [he] using hO.pow 3
  have hB : (fun n : ℕ => (extremalNumber n H : ℝ) ^ (3 : ℕ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (4 : ℝ)) := by
    apply IsBigO.of_bound ((512 * (24 ^ 3 + 1) : ℕ) : ℝ)
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    have hn4 : (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (n : ℝ) 4
    rw [hn4, Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    exact_mod_cast (Nat.pow_le_pow_left (hH.extremalNumber_le (n := n)) 3).trans
      (extremal_cube_le n)
  have hExp := Erdos713Forest.exponent_le_of_isBigO (hP.trans hB)
  linarith

theorem exponent_eq_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : C6 ⊑ H) (hhi : H ⊑ C6) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (4 : ℝ) / 3 :=
  le_antisymm (exponent_upper_of_containment hhi hc h) (exponent_lower_of_containment hlo hc h)

theorem rational_exponent_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : C6 ⊑ H) (hhi : H ⊑ C6) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨4 / 3, ?_⟩
  simpa using (exponent_eq_of_containment hlo hhi hc h).symm

theorem rational_exponent {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n C6 : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) :=
  rational_exponent_of_containment (.refl _) (.refl _) hc h

end Erdos713C6

#print axioms Erdos713C6.rational_exponent
