import FormalConjecturesUtil

/-! Leaf-removal reductions for extremal graph exponents. -/

open SimpleGraph Filter Asymptotics Finset

namespace Erdos713Leaf

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

open scoped Classical in
theorem extend_leaf {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : SimpleGraph W) [DecidableRel T.Adj]
    {x y : W} (hx : T.degree x = 1) (hxy : T.Adj x y)
    (f : Copy (T.induce {x}ᶜ) G)
    (hdeg : Fintype.card W ≤ G.degree (f ⟨y, by simpa using hxy.ne.symm⟩)) : T ⊑ G := by
  classical
  obtain ⟨y₀, hy₀, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
  have hy : ∀ w, T.Adj x w → w = y :=
    fun w hw => (huniq w hw).trans (huniq y hxy).symm
  have hsmall : Fintype.card ↥({x}ᶜ : Set W) < Fintype.card W :=
    Fintype.card_subtype_lt (x := x) (by simp)
  let y' : ↥({x}ᶜ : Set W) := ⟨y, by simpa using hxy.ne.symm⟩
  let S : Finset V := Finset.univ.image f
  have hS : S.card < (G.neighborFinset (f y')).card := by
    calc
      S.card ≤ Fintype.card ↥({x}ᶜ : Set W) := by
        simpa only [Finset.card_univ] using (Finset.card_image_le (s := Finset.univ) (f := f))
      _ < Fintype.card W := hsmall
      _ ≤ (G.neighborFinset (f y')).card := hdeg
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

theorem exists_neighbor_not_range {V U : Type*} [Fintype V] [Fintype U]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : U → V) (u : V)
    (hcard : Fintype.card U < G.degree u) :
    ∃ w, G.Adj u w ∧ ∀ a, w ≠ f a := by
  classical
  have hc : (univ.image f).card < (G.neighborFinset u).card := by
    calc
      (univ.image f).card ≤ Fintype.card U := by
        simpa only [card_univ] using card_image_le (s := univ) (f := f)
      _ < (G.neighborFinset u).card := hcard
  obtain ⟨w, hw, hwf⟩ := exists_mem_notMem_of_card_lt_card hc
  refine ⟨w, by simpa using hw, ?_⟩
  intro a ha
  exact hwf (ha ▸ mem_image.mpr ⟨a, mem_univ _, rfl⟩)

noncomputable def move_isolated {U V : Type*} {A : SimpleGraph U} {B : SimpleGraph V}
    (f : Copy A B) (y : U) (hy : ∀ v, ¬A.Adj y v) (w : V) (hw : ∀ a, w ≠ f a) :
    Copy A B := by
  classical
  refine ⟨⟨Function.update (⇑f) y w, ?_⟩, ?_⟩
  · intro u v huv
    have hu : u ≠ y := fun he => hy v (he ▸ huv)
    have hv : v ≠ y := fun he => hy u (he ▸ huv.symm)
    simpa only [Function.update_of_ne hu, Function.update_of_ne hv] using f.toHom.map_rel' huv
  · intro u v huv
    change Function.update (⇑f) y w u = Function.update (⇑f) y w v at huv
    by_cases hu : u = y
    · by_cases hv : v = y
      · exact hu.trans hv.symm
      · rw [hu, Function.update_self, Function.update_of_ne hv] at huv
        exact (hw v huv).elim
    · by_cases hv : v = y
      · rw [hv, Function.update_self, Function.update_of_ne hu] at huv
        exact (hw u huv.symm).elim
      · apply f.injective
        simpa [hu, hv] using huv

@[simp]
theorem move_isolated_self {U V : Type*} {A : SimpleGraph U} {B : SimpleGraph V}
    (f : Copy A B) (y : U) (hy : ∀ v, ¬A.Adj y v) (w : V) (hw : ∀ a, w ≠ f a) :
    move_isolated f y hy w hw y = w := by
  classical
  simp [move_isolated]

open scoped Classical in
theorem free_leaf_edge_bound {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : SimpleGraph W) [DecidableRel T.Adj]
    {x y : W} (hx : T.degree x = 1) (hxy : T.Adj x y) (hfree : T.Free G) :
    G.edgeFinset.card ≤ extremalNumber (Fintype.card V) (T.induce {x}ᶜ) +
      Fintype.card W * Fintype.card V := by
  classical
  obtain ⟨K, hKG, hdeg, hbound⟩ := exists_pruned G (Fintype.card W)
  by_cases hK : K = ⊥
  · have he : Nat.card K.edgeSet = 0 := by simp [hK]
    rw [he, zero_add] at hbound
    have hb := hbound.trans (Nat.le_add_left (Fintype.card W * Fintype.card V)
      (extremalNumber (Fintype.card V) (T.induce {x}ᶜ)))
    simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card] using hb
  have hdpos (u v : V) (huv : K.Adj u v) : Fintype.card W ≤ K.degree u := by
    have hp : 0 < K.degree u := (K.degree_pos_iff_exists_adj _).mpr ⟨_, huv⟩
    rcases hdeg u with hh | hh
    · rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] at hh
      omega
    · simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hh
  have hKfree : (T.induce {x}ᶜ).Free K := by
    rintro ⟨f⟩
    let y' : ↥({x}ᶜ : Set W) := ⟨y, by simpa using hxy.ne.symm⟩
    by_cases hz : ∃ z, z ≠ x ∧ T.Adj y z
    · obtain ⟨z, hzx, hyz⟩ := hz
      let z' : ↥({x}ᶜ : Set W) := ⟨z, by simpa using hzx⟩
      have hAdj : K.Adj (f y') (f z') := f.toHom.map_rel' hyz
      exact hfree ((extend_leaf K T hx hxy f (hdpos _ _ hAdj)).mono_right hKG)
    · have hyiso : ∀ v, ¬(T.induce {x}ᶜ).Adj y' v := by
        intro v hv
        apply hz
        exact ⟨v.val, v.prop, hv⟩
      obtain ⟨u, v, huv⟩ := ne_bot_iff_exists_adj.mp hK
      have hsmall : Fintype.card ↥({x}ᶜ : Set W) < Fintype.card W :=
        Fintype.card_subtype_lt (x := x) (by simp)
      obtain ⟨w, huw, hw⟩ := exists_neighbor_not_range K f u
        (hsmall.trans_le (hdpos _ _ huv))
      let f' := move_isolated f y' hyiso w hw
      have he : f' y' = w := move_isolated_self f y' hyiso w hw
      have hdc : Fintype.card W ≤ Nat.card (K.neighborSet (f' y')) := by
        rw [he, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
        exact hdpos _ _ huw.symm
      have hd : Fintype.card W ≤ K.degree (f' y') := by
        simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hdc
      exact hfree ((extend_leaf K T hx hxy f' hd).mono_right hKG)
  have hKbound : Nat.card K.edgeSet ≤ extremalNumber (Fintype.card V) (T.induce {x}ᶜ) := by
    simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card] using
      card_edgeFinset_le_extremalNumber hKfree
  have hb := hbound.trans (Nat.add_le_add_right hKbound (Fintype.card W * Fintype.card V))
  simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card] using hb

open scoped Classical in
theorem extremal_leaf_upper {W : Type*} [Fintype W]
    (T : SimpleGraph W) [DecidableRel T.Adj]
    {x y : W} (hx : T.degree x = 1) (hxy : T.Adj x y) (n : ℕ) :
    extremalNumber n T ≤ extremalNumber n (T.induce {x}ᶜ) + Fintype.card W * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  exact free_leaf_edge_bound G T hx hxy hfree

theorem rpow_isLittleO_nat {a b : ℝ} (hab : a < b) :
    (fun n : ℕ => (n : ℝ) ^ a) =o[atTop] (fun n : ℕ => (n : ℝ) ^ b) := by
  apply (isLittleO_iff_tendsto' ?_).mpr
  · have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    simp only [Function.comp_apply, neg_sub, Real.rpow_sub hn']
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    intro hz
    exact ((Real.rpow_pos_of_pos hn' b).ne' hz).elim

open scoped Classical in
theorem leaf_asymptotic {W : Type*} [Fintype W]
    (T : SimpleGraph W) [DecidableRel T.Adj]
    {x y : W} (hx : T.degree x = 1) (hxy : T.Adj x y)
    {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n T : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    IsEquivalent atTop (fun n : ℕ => (extremalNumber n (T.induce {x}ᶜ) : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a) := by
  have hLo (n : ℕ) : extremalNumber n (T.induce {x}ᶜ) ≤ extremalNumber n T :=
    (show (T.induce {x}ᶜ) ⊑ T from ⟨Copy.induce T _⟩).extremalNumber_le
  have hδnonneg (n : ℕ) :
      0 ≤ (extremalNumber n T : ℝ) - (extremalNumber n (T.induce {x}ᶜ) : ℝ) := by
    apply sub_nonneg.mpr
    exact_mod_cast hLo n
  have hδbound (n : ℕ) :
      (extremalNumber n T : ℝ) - (extremalNumber n (T.induce {x}ᶜ) : ℝ) ≤
        (Fintype.card W : ℝ) * (n : ℝ) := by
    have hu : (extremalNumber n T : ℝ) ≤ (extremalNumber n (T.induce {x}ᶜ) : ℝ) +
        (Fintype.card W : ℝ) * (n : ℝ) := by
      exact_mod_cast extremal_leaf_upper T hx hxy n
    linarith
  have hlin : (fun n : ℕ => (extremalNumber n T : ℝ) -
      (extremalNumber n (T.induce {x}ᶜ) : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
    apply IsBigO.of_bound (Fintype.card W : ℝ)
    filter_upwards with n
    rw [Real.norm_of_nonneg (hδnonneg n), Real.norm_natCast]
    exact hδbound n
  have ho : (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ a) := by
    simpa only [Real.rpow_one] using rpow_isLittleO_nat ha
  have hδ := hlin.trans_isLittleO (ho.const_mul_right hc)
  apply (h.sub_isLittleO hδ).congr_left
  filter_upwards with n
  simp only [Pi.sub_apply]
  ring

/-! Removing an isolated forbidden vertex changes no sufficiently large extremal number. -/

open scoped Classical in
theorem extend_isolated {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (T : SimpleGraph W) [DecidableRel T.Adj]
    {x : W} (hx : T.degree x = 0) (f : Copy (T.induce {x}ᶜ) G)
    (hcard : Fintype.card W ≤ Fintype.card V) : T ⊑ G := by
  classical
  have hsmall : Fintype.card ↥({x}ᶜ : Set W) < Fintype.card W :=
    Fintype.card_subtype_lt (x := x) (by simp)
  have hS : (Finset.univ.image f).card < (Finset.univ : Finset V).card := by
    calc
      (Finset.univ.image f).card ≤ Fintype.card ↥({x}ᶜ : Set W) := by
        simpa only [Finset.card_univ] using
          (Finset.card_image_le (s := Finset.univ) (f := f))
      _ < Fintype.card W := hsmall
      _ ≤ (Finset.univ : Finset V).card := hcard
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hS
  have hzf : ∀ w, z ≠ f w := by
    intro w heq
    exact hz (heq ▸ Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩)
  let g : W → V := fun w => if h : w = x then z else f ⟨w, by simpa using h⟩
  have hg : ∀ w (hw : w ≠ x), g w = f ⟨w, by simpa using hw⟩ := by
    intro w hw
    simp [g, hw]
  have hgx : g x = z := by simp [g]
  have hiso : ∀ w, ¬ T.Adj x w := by
    intro w hw
    have hd := hw.degree_pos_left
    omega
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro u v huv
    have hu : u ≠ x := fun he => hiso v (he ▸ huv)
    have hv : v ≠ x := fun he => hiso u (he ▸ huv.symm)
    rw [hg u hu, hg v hv]
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
theorem extremal_isolated_eq {W : Type*} [Fintype W]
    (T : SimpleGraph W) [DecidableRel T.Adj]
    {x : W} (hx : T.degree x = 0) {n : ℕ} (hn : Fintype.card W ≤ n) :
    extremalNumber n T = extremalNumber n (T.induce {x}ᶜ) := by
  apply le_antisymm
  · rw [← Fintype.card_fin n, extremalNumber_le_iff]
    intro G _ hfree
    apply card_edgeFinset_le_extremalNumber
    rintro ⟨f⟩
    exact hfree (extend_isolated G T hx f (by simpa using hn))
  · exact (show (T.induce {x}ᶜ) ⊑ T from ⟨Copy.induce T _⟩).extremalNumber_le

open scoped Classical in
theorem isolated_asymptotic {W : Type*} [Fintype W]
    (T : SimpleGraph W) [DecidableRel T.Adj]
    {x : W} (hx : T.degree x = 0) {a c : ℝ}
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n T : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    IsEquivalent atTop (fun n : ℕ => (extremalNumber n (T.induce {x}ᶜ) : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a) := by
  apply h.congr_left
  filter_upwards [eventually_ge_atTop (Fintype.card W)] with n hn
  rw [extremal_isolated_eq T hx hn]

end Erdos713Leaf

#print axioms Erdos713Leaf.leaf_asymptotic

#print axioms Erdos713Leaf.isolated_asymptotic
