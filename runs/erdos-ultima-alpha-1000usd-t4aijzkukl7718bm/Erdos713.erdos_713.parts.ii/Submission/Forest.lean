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

#print axioms Erdos713Forest.rational_exponent_of_acyclic
