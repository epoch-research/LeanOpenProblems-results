import Submission.LamMap

/-!
# The chain argument: nested hitting sets for short odd closed walks give a `3`-coloring
-/

open SimpleGraph

namespace Erdos74Aux

variable {V : Type*}

/-- The fast-growing sequence of odd-girth thresholds. -/
def ell : ℕ → ℕ
  | 0 => 3
  | j + 1 => 2 ^ (j + 2) * ell j

lemma ell_zero : ell 0 = 3 := rfl

lemma ell_succ (j : ℕ) : ell (j + 1) = 2 ^ (j + 2) * ell j := rfl

lemma ell_pos (j : ℕ) : 0 < ell j := by
  induction j with
  | zero => simp [ell]
  | succ j ih => rw [ell_succ]; positivity

lemma le_ell (j : ℕ) : j ≤ ell j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ell_succ]
    have : 2 ≤ 2 ^ (j + 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := ell_pos j
    nlinarith

lemma ell_mono : Monotone ell := by
  apply monotone_nat_of_le_succ
  intro j
  rw [ell_succ]
  have : 1 ≤ 2 ^ (j + 2) := Nat.one_le_two_pow
  nlinarith [ell_pos j]

/-- `F` hits every odd closed walk of `G` of length at most `L`. -/
def HitsShortOdd (G : SimpleGraph V) (F : Set (Sym2 V)) (L : ℕ) : Prop :=
  ∀ (v : V) (w : G.Walk v v), Odd w.length → w.length ≤ L → ∃ e ∈ w.edges, e ∈ F

/-- If `U ⊇ F` and `F` hits all short odd closed walks, then `G - U` has no short odd
closed walk. -/
lemma noShort_of_hits {G : SimpleGraph V} {F U : Set (Sym2 V)} {L : ℕ} (hFU : F ⊆ U)
    (hF : HitsShortOdd G F L) (v : V) (w : (G.deleteEdges U).Walk v v) (hodd : Odd w.length) :
    L < w.length := by
  by_contra hle
  push_neg at hle
  have hle' : (w.mapLe (G.deleteEdges_le U)).length ≤ L := by simpa using hle
  have hodd' : Odd (w.mapLe (G.deleteEdges_le U)).length := by simpa using hodd
  obtain ⟨e, he, heF⟩ := hF v _ hodd' hle'
  rw [Walk.edges_mapLe_eq_edges] at he
  have := w.edges_subset_edgeSet he
  rw [edgeSet_deleteEdges] at this
  exact this.2 (hFU heF)

/-- The key parity consequence: a shortest even path between the endpoints of an edge
of `K` gives an odd closed walk. -/
lemma odd_bound {K H' : SimpleGraph V} {L : ℕ}
    (hK : ∀ (v : V) (w : K.Walk v v), Odd w.length → L < w.length) (hle : H' ≤ K) {x y : V}
    (hxy : K.Adj x y) (hr : H'.Reachable x y) (hev : Even (H'.dist x y)) :
    L < H'.dist x y + 1 := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  let c : K.Walk y y := Walk.cons hxy.symm (p.mapLe hle)
  have hc : c.length = H'.dist x y + 1 := by simp [c, hp]
  have := hK y c (by rw [hc]; exact hev.add_one)
  omega

theorem chain_colorable {W : Type*} [Fintype W] (G : SimpleGraph W)
    (E : ℕ → Finset (Sym2 W)) (hcard : ∀ j, (E j).card ≤ j)
    (hhit : ∀ j, HitsShortOdd G (E j : Set (Sym2 W)) (ell (j + 1))) : G.Colorable 3 := by
  classical
  let U : ℕ → Finset (Sym2 W) := fun j => (Finset.range (j + 1)).biUnion E
  have hEU : ∀ j, E j ⊆ U j := fun j =>
    Finset.subset_biUnion_of_mem E (Finset.self_mem_range_succ j)
  have hUsucc : ∀ j, U (j + 1) = U j ∪ E (j + 1) := by
    intro j; simp only [U]; rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
  let K : ℕ → SimpleGraph W := fun j => G.deleteEdges (U j : Set (Sym2 W))
  have hK : ∀ j, ∀ (v : W) (w : (K j).Walk v v), Odd w.length → ell (j + 1) < w.length :=
    fun j => noShort_of_hits (by exact_mod_cast hEU j) (hhit j)
  set T := Fintype.card W with hT
  -- base
  have base : ∃ θ : W → ℝ, IsLamMap (K T) θ (1 / ell T) := by
    let B : Finset (Sym2 W) := Finset.univ.filter (fun e => e ∈ (K T).edgeSet)
    have hyp : ∀ H' : SimpleGraph W, H' ≤ K T → ∀ x y, (K T).Adj x y → H'.Reachable x y →
        Even (H'.dist x y) → 1 ≤ (0 : ℝ) * ((H'.dist x y : ℝ) + 1) := by
      intro H' hH' x y hxy hr hev
      exfalso
      have h1 := odd_bound (hK T) hH' hxy hr hev
      obtain ⟨p, hpath, hp⟩ := hr.exists_path_of_dist
      have h2 := hpath.length_lt
      have h3 := le_ell (T + 1)
      omega
    obtain ⟨θ, hθ⟩ := block (K := K T) (H := ⊥) bot_le (le_refl (0:ℝ)) hyp B
      (by simp [B]) (le_refl 0) (isLamMap_bot (fun _ => 0) 0)
    refine ⟨θ, ?_⟩
    have hle : K T ≤ ⊥ ⊔ fromEdgeSet (B : Set (Sym2 W)) := by
      intro u v huv
      rw [sup_adj, fromEdgeSet_adj]
      right
      exact ⟨by simp [B, huv], (K T).ne_of_adj huv⟩
    refine (hθ.anti hle).mono ?_
    simp only [mul_zero, add_zero]
    have := ell_pos T
    positivity
  -- step
  have step : ∀ j, (∃ θ : W → ℝ, IsLamMap (K (j + 1)) θ (1 / ell (j + 1))) →
      ∃ θ : W → ℝ, IsLamMap (K j) θ (1 / ell j) := by
    intro j ⟨θ, hθ⟩
    let B : Finset (Sym2 W) := (E (j + 1)).filter (fun e => e ∈ (K j).edgeSet)
    have hHK : K (j + 1) ≤ K j := by
      intro u v huv
      simp only [K, deleteEdges_adj] at huv ⊢
      refine ⟨huv.1, fun h => huv.2 ?_⟩
      rw [hUsucc]; exact Finset.mem_union_left _ h
    have hLpos : (0 : ℝ) < ell (j + 1) := by exact_mod_cast ell_pos _
    have hδ : (0:ℝ) ≤ 1 / ell (j + 1) := by positivity
    have hyp : ∀ H' : SimpleGraph W, H' ≤ K j → ∀ x y, (K j).Adj x y → H'.Reachable x y →
        Even (H'.dist x y) → 1 ≤ (1 / (ell (j + 1) : ℝ)) * ((H'.dist x y : ℝ) + 1) := by
      intro H' hH' x y hxy hr hev
      have h1 := odd_bound (hK j) hH' hxy hr hev
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hLpos, one_mul]
      exact_mod_cast h1.le
    obtain ⟨θ', hθ'⟩ := block hHK hδ hyp B (fun e he => (Finset.mem_filter.mp he).2) hδ hθ
    refine ⟨θ', ?_⟩
    have hle : K j ≤ K (j + 1) ⊔ fromEdgeSet (B : Set (Sym2 W)) := by
      intro u v huv
      rw [sup_adj, fromEdgeSet_adj]
      by_cases he : s(u, v) ∈ E (j + 1)
      · right; exact ⟨by simp [B, he, huv], (K j).ne_of_adj huv⟩
      · left
        simp only [K, deleteEdges_adj] at huv ⊢
        refine ⟨huv.1, ?_⟩
        rw [hUsucc]
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or]
        exact ⟨huv.2, he⟩
    refine (hθ'.anti hle).mono ?_
    have hb : B.card ≤ j + 1 := (Finset.card_filter_le _ _).trans (hcard _)
    have h2b : (2:ℝ) ^ B.card ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) hb
    have hL : (ell (j + 1) : ℝ) = 2 ^ (j + 2) * ell j := by rw [ell_succ]; push_cast; ring
    have hl0 : (0 : ℝ) < ell j := by exact_mod_cast ell_pos _
    calc (2:ℝ) ^ B.card * (1 / ell (j + 1)) + (2 ^ B.card - 1) * (1 / ell (j + 1))
        ≤ 2 ^ (j + 1) * (1 / ell (j + 1)) + 2 ^ (j + 1) * (1 / ell (j + 1)) := by
          gcongr; linarith
      _ = 2 ^ (j + 2) / ell (j + 1) := by ring
      _ = 1 / ell j := by rw [hL]; field_simp
  -- downward induction
  have all : ∀ i, i ≤ T → ∃ θ : W → ℝ, IsLamMap (K (T - i)) θ (1 / ell (T - i)) := by
    intro i
    induction i with
    | zero => intro _; simpa using base
    | succ i ih =>
      intro hi
      have h := ih (by omega)
      have e : T - i = (T - (i + 1)) + 1 := by omega
      rw [e] at h
      exact step _ h
  obtain ⟨θ, hθ⟩ := all T le_rfl
  rw [Nat.sub_self] at hθ
  have hE0 : E 0 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hcard 0))
  have hU0 : U 0 = ∅ := by simp [U, hE0]
  have hK0 : K 0 = G := by simp [K, hU0]
  rw [hK0, ell_zero] at hθ
  exact colorable_of_isLamMap (by simpa using hθ)

end Erdos74Aux
