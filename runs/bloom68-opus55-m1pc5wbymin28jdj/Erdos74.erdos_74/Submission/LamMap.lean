import Mathlib

/-!
# `λ`-maps (circular-type maps) for simple graphs

A `λ`-map of a graph `G` is a function `θ : V → ℝ` such that along every edge `uv`
the difference `θ u - θ v` lies within distance `λ` of an odd integer.
-/

open SimpleGraph

namespace Erdos74Aux

variable {V : Type*}

/-- `θ` is a `lam`-map for `G`. -/
def IsLamMap (G : SimpleGraph V) (θ : V → ℝ) (lam : ℝ) : Prop :=
  ∀ u v, G.Adj u v → ∃ k : ℤ, |θ u - θ v - (2 * k + 1)| ≤ lam

lemma IsLamMap.mono {G : SimpleGraph V} {θ : V → ℝ} {lam lam' : ℝ} (h : IsLamMap G θ lam)
    (hl : lam ≤ lam') : IsLamMap G θ lam' := fun u v huv => by
  obtain ⟨k, hk⟩ := h u v huv
  exact ⟨k, hk.trans hl⟩

lemma IsLamMap.anti {G H : SimpleGraph V} {θ : V → ℝ} {lam : ℝ} (h : IsLamMap G θ lam)
    (hHG : H ≤ G) : IsLamMap H θ lam := fun u v huv => h u v (hHG huv)

lemma isLamMap_bot (θ : V → ℝ) (lam : ℝ) : IsLamMap (⊥ : SimpleGraph V) θ lam :=
  fun u v h => absurd h (by simp)

/-- A `1/3`-map yields a proper `3`-coloring. -/
lemma colorable_of_isLamMap {G : SimpleGraph V} {θ : V → ℝ} (h : IsLamMap G θ (1 / 3)) :
    G.Colorable 3 := by
  let c : V → ZMod 3 := fun v => ((⌊3 * θ v / 2⌋ : ℤ) : ZMod 3)
  have hc : ∀ {u v}, G.Adj u v → c u ≠ c v := by
    intro u v huv hcuv
    obtain ⟨k, hk⟩ := h u v huv
    rw [abs_le] at hk
    have h1 := Int.floor_le (3 * θ u / 2)
    have h2 := Int.lt_floor_add_one (3 * θ u / 2)
    have h3 := Int.floor_le (3 * θ v / 2)
    have h4 := Int.lt_floor_add_one (3 * θ v / 2)
    have hlo : ((3 * k : ℤ) : ℝ) < ((⌊3 * θ u / 2⌋ - ⌊3 * θ v / 2⌋ : ℤ) : ℝ) := by
      push_cast; linarith
    have hhi : ((⌊3 * θ u / 2⌋ - ⌊3 * θ v / 2⌋ : ℤ) : ℝ) < ((3 * k + 3 : ℤ) : ℝ) := by
      push_cast; linarith
    have hlo' : 3 * k < ⌊3 * θ u / 2⌋ - ⌊3 * θ v / 2⌋ := by exact_mod_cast hlo
    have hhi' : ⌊3 * θ u / 2⌋ - ⌊3 * θ v / 2⌋ < 3 * k + 3 := by exact_mod_cast hhi
    have hdvd : ((3 : ℕ) : ℤ) ∣ ⌊3 * θ v / 2⌋ - ⌊3 * θ u / 2⌋ :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mp hcuv
    push_cast at hdvd
    omega
  have := (Coloring.mk c (fun huv => hc huv)).colorable
  simpa using this

/-- Summing along a walk. -/
lemma walk_approx {G : SimpleGraph V} {θ : V → ℝ} {lam : ℝ} (h : IsLamMap G θ lam)
    {u v : V} (p : G.Walk u v) :
    ∃ m : ℤ, |θ u - θ v - ((p.length : ℝ) + 2 * m)| ≤ p.length * lam := by
  induction p with
  | nil => exact ⟨0, by simp⟩
  | @cons a b c hadj p ih =>
    obtain ⟨k, hk⟩ := h _ _ hadj
    obtain ⟨m, hm⟩ := ih
    refine ⟨k + m, ?_⟩
    simp only [Walk.length_cons]
    push_cast
    calc |θ a - θ c - (((p.length : ℝ) + 1) + 2 * ((k : ℝ) + m))|
        = |(θ a - θ b - (2 * k + 1)) + (θ b - θ c - (p.length + 2 * m))| := by ring_nf
      _ ≤ |θ a - θ b - (2 * k + 1)| + |θ b - θ c - (p.length + 2 * m)| := abs_add_le _ _
      _ ≤ lam + p.length * lam := add_le_add hk hm
      _ = ((p.length : ℝ) + 1) * lam := by ring

lemma dist_adj_le {H : SimpleGraph V} {u v : V} (y : V) (h : H.Adj u v) :
    (H.dist u y : ℝ) ≤ H.dist v y + 1 := by
  have := (h.reachable).dist_triangle_left y
  rw [dist_eq_one_iff_adj.mpr h] at this
  exact_mod_cast (by omega : H.dist u y ≤ H.dist v y + 1)

lemma bump_lip {H : SimpleGraph V} (y : V) {d : ℝ} (hd : 0 < d) (s : ℝ) {u v : V}
    (h : H.Adj u v) :
    |s * min 1 (H.dist u y / d) - s * min 1 (H.dist v y / d)| ≤ |s| / d := by
  rw [← mul_sub, abs_mul, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg s)
  have h1 := dist_adj_le y h
  have h2 := dist_adj_le y h.symm
  have h3 : |min 1 ((H.dist u y : ℝ) / d) - min 1 ((H.dist v y : ℝ) / d)| ≤
      |(H.dist u y : ℝ) / d - H.dist v y / d| := by
    have := abs_min_sub_min_le_max (1 : ℝ) ((H.dist u y : ℝ) / d) 1 (H.dist v y / d)
    simpa using this
  calc _ ≤ _ := h3
    _ = |(H.dist u y - H.dist v y : ℝ)| / d := by rw [← sub_div, abs_div, abs_of_pos hd]
    _ ≤ 1 / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      rw [abs_le]; constructor <;> linarith
    _ = d⁻¹ := one_div d

lemma abs_shift_le (a b c e t : ℝ) : |a + b - (c + e) - t| ≤ |a - c - t| + |b - e| := by
  calc |a + b - (c + e) - t| = |(a - c - t) + (b - e)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

lemma bump_map {H : SimpleGraph V} {θ : V → ℝ} {lam Λ : ℝ} (hθ : IsLamMap H θ lam) {x y : V}
    (hxy : x ≠ y) (hr : H.Reachable x y) (s : ℝ) (M : ℤ)
    (hM : |θ x - θ y + s - (2 * M + 1)| ≤ Λ) (hν : lam + |s| / H.dist x y ≤ Λ) :
    IsLamMap (H ⊔ edge x y) (fun v => θ v + s * min 1 ((H.dist v y : ℝ) / H.dist x y)) Λ := by
  have hd0 : (0 : ℝ) < H.dist x y := by exact_mod_cast hr.pos_dist_of_ne hxy
  have hbx : s * min 1 ((H.dist x y : ℝ) / H.dist x y) = s := by
    rw [div_self hd0.ne', min_self, mul_one]
  have hby : s * min 1 ((H.dist y y : ℝ) / H.dist x y) = 0 := by simp
  intro u v huv
  rw [sup_adj, edge_adj] at huv
  rcases huv with huv | ⟨hxy', -⟩
  · obtain ⟨k, hk⟩ := hθ u v huv
    refine ⟨k, ?_⟩
    calc _ ≤ |θ u - θ v - (2 * k + 1)| + |s * min 1 ((H.dist u y : ℝ) / H.dist x y) -
          s * min 1 ((H.dist v y : ℝ) / H.dist x y)| := abs_shift_le _ _ _ _ _
      _ ≤ lam + |s| / H.dist x y := add_le_add hk (bump_lip y hd0 s huv)
      _ ≤ Λ := hν
  · rcases hxy' with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · refine ⟨M, ?_⟩
      dsimp only
      rw [hu, hv, hbx, hby]
      calc |θ x + s - (θ y + 0) - (2 * M + 1)| = |θ x - θ y + s - (2 * M + 1)| := by ring_nf
        _ ≤ Λ := hM
    · refine ⟨-M - 1, ?_⟩
      dsimp only
      rw [hu, hv, hbx, hby]
      calc |θ y + 0 - (θ x + s) - (2 * ((-M - 1 : ℤ) : ℝ) + 1)|
          = |-(θ x - θ y + s - (2 * M + 1))| := by push_cast; ring_nf
        _ = |θ x - θ y + s - (2 * M + 1)| := abs_neg _
        _ ≤ Λ := hM

lemma ext_step {H : SimpleGraph V} {θ : V → ℝ} {lam δ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hθ : IsLamMap H θ lam) {x y : V} (hxy : x ≠ y)
    (hyp : H.Reachable x y → Even (H.dist x y) → 1 ≤ δ * ((H.dist x y : ℝ) + 1)) :
    ∃ θ' : V → ℝ, IsLamMap (H ⊔ edge x y) θ' (2 * lam + δ) := by
  classical
  by_cases hr : H.Reachable x y
  · have hd0 : (0 : ℝ) < H.dist x y := by exact_mod_cast hr.pos_dist_of_ne hxy
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    obtain ⟨m, hm⟩ := walk_approx hθ p
    rw [hp] at hm
    rcases Nat.even_or_odd (H.dist x y) with hev | hodd
    · -- even case
      have hδd := hyp hr hev
      have hdd1 : (0 : ℝ) < (H.dist x y : ℝ) + 1 := by positivity
      have hδ' : 1 / ((H.dist x y : ℝ) + 1) ≤ δ := by
        rw [div_le_iff₀ hdd1]; linarith
      have hR : |(θ x - θ y - 1) / 2 - round ((θ x - θ y - 1) / 2)| ≤ 1 / 2 := abs_sub_round _
      have hr1 : |(2 * (round ((θ x - θ y - 1) / 2) : ℝ) + 1) - (θ x - θ y)| ≤ 1 := by
        have : (2 * (round ((θ x - θ y - 1) / 2) : ℝ) + 1) - (θ x - θ y) =
            -2 * ((θ x - θ y - 1) / 2 - round ((θ x - θ y - 1) / 2)) := by ring
        rw [this, abs_mul]; norm_num; linarith
      set r : ℝ := (2 * (round ((θ x - θ y - 1) / 2) : ℝ) + 1) - (θ x - θ y) with hrdef
      set dd : ℝ := (H.dist x y : ℝ) with hdd
      refine ⟨_, bump_map hθ hxy hr (r * dd / (dd + 1)) (round ((θ x - θ y - 1) / 2)) ?_ ?_⟩
      · have : θ x - θ y + r * dd / (dd + 1) - (2 * (round ((θ x - θ y - 1) / 2) : ℝ) + 1) =
            -(r / (dd + 1)) := by
          rw [hrdef]; field_simp; ring
        rw [this, abs_neg, abs_div, abs_of_pos hdd1]
        calc |r| / (dd + 1) ≤ 1 / (dd + 1) := by gcongr
          _ ≤ δ := hδ'
          _ ≤ 2 * lam + δ := by linarith
      · have : |r * dd / (dd + 1)| / dd = |r| / (dd + 1) := by
          rw [abs_div, abs_mul, abs_of_pos hd0, abs_of_pos hdd1]; field_simp
        rw [this]
        calc lam + |r| / (dd + 1) ≤ lam + 1 / (dd + 1) := by gcongr
          _ ≤ lam + δ := by linarith
          _ ≤ 2 * lam + δ := by linarith
    · -- odd case
      obtain ⟨t, ht⟩ := hodd
      set r : ℝ := (2 * ((t + m : ℤ) : ℝ) + 1) - (θ x - θ y) with hrdef
      have hr' : |r| ≤ H.dist x y * lam := by
        have : r = -(θ x - θ y - ((H.dist x y : ℝ) + 2 * m)) := by
          rw [hrdef, ht]; push_cast; ring
        rw [this, abs_neg]; exact hm
      refine ⟨_, bump_map hθ hxy hr r (t + m) ?_ ?_⟩
      · have : θ x - θ y + r - (2 * ((t + m : ℤ) : ℝ) + 1) = 0 := by rw [hrdef]; ring
        rw [this, abs_zero]; positivity
      · have : |r| / H.dist x y ≤ lam := by rw [div_le_iff₀ hd0]; linarith
        linarith
  · -- unreachable
    refine ⟨fun v => θ v + if H.Reachable x v then 1 - (θ x - θ y) else 0, ?_⟩
    intro u v huv
    rw [sup_adj, edge_adj] at huv
    rcases huv with huv | ⟨hxy', -⟩
    · obtain ⟨k, hk⟩ := hθ u v huv
      refine ⟨k, ?_⟩
      have hiff : H.Reachable x u ↔ H.Reachable x v :=
        ⟨fun h => h.trans huv.reachable, fun h => h.trans huv.reachable.symm⟩
      by_cases hxu : H.Reachable x u
      · have hxv := hiff.mp hxu
        simp only [hxu, hxv, if_true]
        calc |θ u + (1 - (θ x - θ y)) - (θ v + (1 - (θ x - θ y))) - (2 * k + 1)|
            = |θ u - θ v - (2 * k + 1)| := by ring_nf
          _ ≤ lam := hk
          _ ≤ 2 * lam + δ := by linarith
      · have hxv : ¬ H.Reachable x v := fun h => hxu (hiff.mpr h)
        simp only [hxu, hxv, if_false, add_zero]
        linarith
    · rcases hxy' with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · refine ⟨0, ?_⟩
        rw [hu, hv]
        simp only [Reachable.refl, if_true, hr, if_false]
        have : θ x + (1 - (θ x - θ y)) - (θ y + 0) - (2 * ((0 : ℤ) : ℝ) + 1) = 0 := by
          push_cast; ring
        rw [this, abs_zero]; positivity
      · refine ⟨-1, ?_⟩
        rw [hu, hv]
        simp only [Reachable.refl, if_true, hr, if_false]
        have : θ y + 0 - (θ x + (1 - (θ x - θ y))) - (2 * ((-1 : ℤ) : ℝ) + 1) = 0 := by
          push_cast; ring
        rw [this, abs_zero]; positivity

lemma block {K H : SimpleGraph V} (hHK : H ≤ K) {δ : ℝ} (hδ : 0 ≤ δ)
    (hyp : ∀ H' : SimpleGraph V, H' ≤ K → ∀ x y, K.Adj x y → H'.Reachable x y →
      Even (H'.dist x y) → 1 ≤ δ * ((H'.dist x y : ℝ) + 1))
    (B : Finset (Sym2 V)) (hB : ∀ e ∈ B, e ∈ K.edgeSet) {θ : V → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hθ : IsLamMap H θ lam) :
    ∃ θ' : V → ℝ, IsLamMap (H ⊔ fromEdgeSet (B : Set (Sym2 V))) θ'
      (2 ^ B.card * lam + (2 ^ B.card - 1) * δ) := by
  classical
  induction B using Finset.induction_on with
  | empty => exact ⟨θ, by simpa using hθ⟩
  | insert e B heB ih =>
    have hB' : ∀ e ∈ B, e ∈ K.edgeSet := fun e he => hB e (Finset.mem_insert_of_mem he)
    obtain ⟨θ₁, hθ₁⟩ := ih hB'
    have hle : H ⊔ fromEdgeSet (B : Set (Sym2 V)) ≤ K := by
      refine sup_le hHK ?_
      intro u v huv
      rw [fromEdgeSet_adj] at huv
      exact hB' _ huv.1
    have heK : e ∈ K.edgeSet := hB e (Finset.mem_insert_self e B)
    rw [Finset.card_insert_of_notMem heB]
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeSet] at heK
      have hlam1 : 0 ≤ 2 ^ B.card * lam + (2 ^ B.card - 1) * δ := by
        have : (1 : ℝ) ≤ 2 ^ B.card := one_le_pow₀ (by norm_num)
        have : 0 ≤ (2 : ℝ) ^ B.card - 1 := by linarith
        positivity
      obtain ⟨θ', hθ'⟩ := ext_step hlam1 hδ hθ₁ (K.ne_of_adj heK) (hyp _ hle x y heK)
      have heq : H ⊔ fromEdgeSet ((insert s(x, y) B : Finset (Sym2 V)) : Set (Sym2 V)) =
          (H ⊔ fromEdgeSet (B : Set (Sym2 V))) ⊔ edge x y := by
        ext u v
        simp only [sup_adj, fromEdgeSet_adj, edge_adj, Finset.coe_insert, Set.mem_insert_iff,
          Finset.mem_coe, Sym2.eq_iff]
        tauto
      refine ⟨θ', ?_⟩
      rw [heq]
      refine hθ'.mono (le_of_eq ?_)
      rw [pow_succ]
      ring

end Erdos74Aux
