import FormalConjecturesUtil

/-! The four-cycle case of the extremal-exponent question. -/

open SimpleGraph Filter Asymptotics Finset

namespace Erdos713C4

abbrev K22 := completeBipartiteGraph (Fin 2) (Fin 2)

theorem no_rectangle {V : Type*} {G : SimpleGraph V} (h : K22.Free G)
    {u v a b : V} (huv : u ≠ v) (hab : a ≠ b)
    (hua : G.Adj u a) (hva : G.Adj v a)
    (hub : G.Adj u b) (hvb : G.Adj v b) : False := by
  classical
  apply h
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{u, v}, {a, b}, by simp [huv], by simp [hab], ?_⟩
  intro x hx y hy
  simp only [mem_coe, mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> assumption

theorem unique_common_of_free {V : Type*} {G : SimpleGraph V} (h : K22.Free G)
    {u v a b : V} (huv : u ≠ v)
    (hua : G.Adj u a) (hva : G.Adj v a)
    (hub : G.Adj u b) (hvb : G.Adj v b) : a = b := by
  by_contra hab
  exact no_rectangle h huv hab hua hva hub hvb

theorem free_of_unique_common {V : Type*} {G : SimpleGraph V}
    (h : ∀ {u v a b : V}, u ≠ v → G.Adj u a → G.Adj v a →
      G.Adj u b → G.Adj v b → a = b) : K22.Free G := by
  rintro ⟨f⟩
  have huv : f (.inl 0) ≠ f (.inl 1) := fun he => by
    have := f.injective he
    simp at this
  have he := h huv
    (f.toHom.map_rel' (show K22.Adj (.inl 0) (.inr 0) by simp [K22, completeBipartiteGraph]))
    (f.toHom.map_rel' (show K22.Adj (.inl 1) (.inr 0) by simp [K22, completeBipartiteGraph]))
    (f.toHom.map_rel' (show K22.Adj (.inl 0) (.inr 1) by simp [K22, completeBipartiteGraph]))
    (f.toHom.map_rel' (show K22.Adj (.inl 1) (.inr 1) by simp [K22, completeBipartiteGraph]))
  have := f.injective he
  simp at this

open scoped Classical in
 theorem common_card_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : K22.Free G) (u v : V) :
    Fintype.card (G.commonNeighbors u v) ≤ 1 + if u = v then Fintype.card V else 0 := by
  classical
  by_cases huv : u = v
  · simp only [huv, ↓reduceIte]
    exact (Fintype.card_subtype_le _).trans (by omega)
  · simp only [huv, ↓reduceIte, add_zero]
    letI : Subsingleton (G.commonNeighbors u v) := ⟨fun a b => by
      apply Subtype.ext
      exact unique_common_of_free h huv a.prop.1 a.prop.2 b.prop.1 b.prop.2⟩
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

open scoped Classical in
 theorem sum_degree_sq_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : K22.Free G) :
    ∑ v, G.degree v ^ 2 ≤ 2 * Fintype.card V ^ 2 := by
  classical
  let r : V → V × V → Prop := fun x p => G.Adj x p.1 ∧ G.Adj x p.2
  have hAbove (x : V) :
      ((univ : Finset (V × V)).bipartiteAbove r x).card = G.degree x ^ 2 := by
    have hs : (univ : Finset (V × V)).bipartiteAbove r x =
        G.neighborFinset x ×ˢ G.neighborFinset x := by
      ext p
      simp [r, bipartiteAbove]
    rw [hs, card_product, card_neighborFinset_eq_degree, pow_two]
  have hBelow (p : V × V) :
      ((univ : Finset V).bipartiteBelow r p).card =
        Fintype.card (G.commonNeighbors p.1 p.2) := by
    have hs : (univ : Finset V).bipartiteBelow r p =
        (G.commonNeighbors p.1 p.2).toFinset := by
      ext x
      simp [r, bipartiteBelow, mem_commonNeighbors, adj_comm]
    rw [hs, Set.toFinset_card]
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := (univ : Finset V)) (t := (univ : Finset (V × V)))
  simp_rw [hAbove, hBelow] at hsum
  rw [hsum, Fintype.sum_prod_type]
  calc
    ∑ u, ∑ v, Fintype.card (G.commonNeighbors u v) ≤
        ∑ u : V, ∑ v : V, (1 + if u = v then Fintype.card V else 0) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      exact common_card_le G h u v
    _ = 2 * Fintype.card V ^ 2 := by
      simp [sum_add_distrib, sum_ite_eq, pow_two, Nat.mul_add]
      ring

open scoped Classical in
 theorem edge_sq_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : K22.Free G) :
    G.edgeFinset.card ^ 2 ≤ Fintype.card V ^ 3 := by
  have hc := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun v => G.degree v)
  rw [card_univ, sum_degrees_eq_twice_card_edges] at hc
  have hb := sum_degree_sq_bound G h
  have hm := Nat.mul_le_mul_left (Fintype.card V) hb
  nlinarith

open scoped Classical in
 theorem edge_rpow_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : K22.Free G) :
    (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) := by
  have hsq : (G.edgeFinset.card : ℝ) ^ 2 ≤ (Fintype.card V : ℝ) ^ 3 := by
    exact_mod_cast edge_sq_bound G h
  have hpow : ((Fintype.card V : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 =
      (Fintype.card V : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hn : 0 ≤ (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  nlinarith

theorem extremal_upper (n : ℕ) :
    (extremalNumber n K22 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ hG
  exact edge_rpow_bound G hG

def affineGraph (F : Type*) [Field F] : SimpleGraph ((F × F) ⊕ (F × F)) where
  Adj u v := match u, v with
    | .inl p, .inr l => p.2 = l.1 * p.1 + l.2
    | .inr l, .inl p => p.2 = l.1 * p.1 + l.2
    | _, _ => False
  symm u v := by cases u <;> cases v <;> simp
  loopless u := by cases u <;> simp

instance affineGraph_decidable (F : Type*) [Field F] [DecidableEq F] :
    DecidableRel (affineGraph F).Adj := by
  intro u v
  cases u <;> cases v <;> dsimp [affineGraph] <;> infer_instance

theorem rectangle_unique {F : Type*} [Field F] {p q l r : F × F} (hpq : p ≠ q)
    (hlp : p.2 = l.1 * p.1 + l.2) (hlq : q.2 = l.1 * q.1 + l.2)
    (hrp : p.2 = r.1 * p.1 + r.2) (hrq : q.2 = r.1 * q.1 + r.2) : l = r := by
  have hx : p.1 ≠ q.1 := by
    intro hx
    apply hpq
    apply Prod.ext hx
    rw [hlp, hlq, hx]
  have hm : (l.1 - r.1) * (p.1 - q.1) = 0 := by
    linear_combination -hlp + hlq + hrp - hrq
  have ha : l.1 = r.1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hx))
  apply Prod.ext ha
  linear_combination -hlp + hrp - ha * p.1

theorem affineGraph_free (F : Type*) [Field F] : K22.Free (affineGraph F) := by
  apply free_of_unique_common
  intro u v a b huv hua hva hub hvb
  cases u <;> cases v <;> cases a <;> cases b <;>
    simp only [affineGraph] at hua hva hub hvb
  all_goals simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq] at huv ⊢
  · exact rectangle_unique huv hua hva hub hvb
  · by_contra hab
    exact huv (rectangle_unique hab hua hub hva hvb)

open scoped Classical in
 theorem affineGraph_degree_left (F : Type*) [Field F] [Fintype F] [DecidableEq F] (p : F × F) :
    (affineGraph F).degree (.inl p) = Fintype.card F := by
  classical
  let f : F → (affineGraph F).neighborSet (.inl p) :=
    fun a => ⟨.inr (a, p.2 - a * p.1), by
      change p.2 = a * p.1 + (p.2 - a * p.1)
      ring⟩
  have hi : Function.Injective f := by
    intro a b hab
    have he := congrArg Subtype.val hab
    exact congrArg Prod.fst (Sum.inr.inj he)
  have hs : Function.Surjective f := by
    rintro ⟨w, hw⟩
    cases w with
    | inl q => exact hw.elim
    | inr l =>
      refine ⟨l.1, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inr
      refine Prod.ext ?_ ?_
      · rfl
      · change p.2 = l.1 * p.1 + l.2 at hw
        dsimp
        linear_combination hw
  rw [← card_neighborSet_eq_degree]
  exact (Fintype.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm

open scoped Classical in
 theorem affineGraph_degree_right (F : Type*) [Field F] [Fintype F] [DecidableEq F] (l : F × F) :
    (affineGraph F).degree (.inr l) = Fintype.card F := by
  classical
  let f : F → (affineGraph F).neighborSet (.inr l) :=
    fun x => ⟨.inl (x, l.1 * x + l.2), rfl⟩
  have hi : Function.Injective f := by
    intro a b hab
    have he := congrArg Subtype.val hab
    exact congrArg Prod.fst (Sum.inl.inj he)
  have hs : Function.Surjective f := by
    rintro ⟨w, hw⟩
    cases w with
    | inr p => exact hw.elim
    | inl p =>
      refine ⟨p.1, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inl
      change p.2 = l.1 * p.1 + l.2 at hw
      exact Prod.ext rfl hw.symm
  rw [← card_neighborSet_eq_degree]
  exact (Fintype.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm

open scoped Classical in
 theorem affineGraph_edges (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    (affineGraph F).edgeFinset.card = Fintype.card F ^ 3 := by
  classical
  have hsum := (affineGraph F).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at hsum
  simp_rw [affineGraph_degree_left, affineGraph_degree_right, sum_const, card_univ,
    Fintype.card_prod, smul_eq_mul] at hsum
  nlinarith

theorem extremal_lower_prime (p : ℕ) (hp : p.Prime) :
    p ^ 3 ≤ extremalNumber (2 * p ^ 2) K22 := by
  letI : Fact p.Prime := ⟨hp⟩
  classical
  have h := card_edgeFinset_le_extremalNumber (affineGraph_free (ZMod p))
  rw [affineGraph_edges] at h
  simpa [Fintype.card_sum, Fintype.card_prod, ZMod.card, pow_two, two_mul] using h

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

theorem lower_exponent_of_prime_bound {f : ℕ → ℕ} {a : ℝ}
    (hO : (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hlow : ∀ p : ℕ, p.Prime → p ^ 3 ≤ f (2 * p ^ 2)) : (3 : ℝ) / 2 ≤ a := by
  by_contra ha
  have ha' : a < (3 : ℝ) / 2 := lt_of_not_ge ha
  obtain ⟨C, _, hC⟩ := hO.exists_pos
  have ht : Tendsto (fun p : ℕ => 2 * p ^ 2) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro p
    by_cases hp : p = 0
    · simp [hp]
    · have hp' : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
      change p ≤ 2 * p ^ 2
      nlinarith [Nat.mul_le_mul_left p hp']
  have hratio : ∀ᶠ p : ℕ in atTop,
      p.Prime → (p : ℝ) ^ (3 - 2 * a) ≤ C * (2 : ℝ) ^ a := by
    filter_upwards [ht.eventually hC.bound, eventually_gt_atTop (0 : ℕ)] with p hp hpos
    intro hprime
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpos
    have hl : (p : ℝ) ^ 3 ≤ (f (2 * p ^ 2) : ℝ) := by
      exact_mod_cast hlow p hprime
    have hu : (f (2 * p ^ 2) : ℝ) ≤ C * (2 * (p : ℝ) ^ 2) ^ a := by
      rw [Real.norm_natCast, Real.norm_of_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg (2 * p ^ 2)) a)] at hp
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hp
    have he := hl.trans hu
    have hp2 : ((p : ℝ) ^ 2) ^ a = (p : ℝ) ^ (2 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      norm_num
    rw [Real.mul_rpow (by norm_num) (sq_nonneg _), hp2] at he
    rw [Real.rpow_sub hp0,
      div_le_iff₀ (Real.rpow_pos_of_pos hp0 (2 * a))]
    have hp3 : (p : ℝ) ^ (3 : ℝ) = (p : ℝ) ^ (3 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (p : ℝ) 3
    rw [hp3]
    simpa only [mul_assoc] using he
  have htop : Tendsto (fun p : ℕ => (p : ℝ) ^ (3 - 2 * a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * a)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hratio.and (htop.eventually_gt_atTop (C * (2 : ℝ) ^ a)))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  exact (not_lt_of_ge ((hN p hpN).1 hp)) ((hN p hpN).2)

theorem exponent_eq_three_halves {a c : ℝ} (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n K22 : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (3 : ℝ) / 2 := by
  have hUpper : (fun n : ℕ => (extremalNumber n K22 : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) := by
    apply isBigO_of_le
    intro n
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
    exact extremal_upper n
  have hpower : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) :=
    (isBigO_const_mul_left_iff hc.ne').mp (h.isBigO_symm.trans hUpper)
  have hO : (fun n : ℕ => (extremalNumber n K22 : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc.ne').mp h.isBigO
  exact le_antisymm (exponent_le_of_isBigO hpower)
    (lower_exponent_of_prime_bound hO extremal_lower_prime)

theorem rational_exponent {a c : ℝ} (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n K22 : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3 / 2, ?_⟩
  simpa using (exponent_eq_three_halves hc h).symm

theorem rational_exponent_of_iso {W : Type*} {G : SimpleGraph W}
    (e : G ≃g K22) {a c : ℝ} (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  apply rational_exponent hc
  simpa only [extremalNumber_congr_right e] using h

end Erdos713C4


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

namespace Erdos713Minus

open Finset

def D33 : SimpleGraph (Fin 3 ⊕ Fin 3) where
  Adj u v := match u, v with
    | Sum.inl i, Sum.inr j => i ≠ 2 ∨ j ≠ 2
    | Sum.inr j, Sum.inl i => i ≠ 2 ∨ j ≠ 2
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp
  loopless := by intro v; cases v <;> simp

theorem contained_of_maps {V : Type*} (G : SimpleGraph V) (a b : Fin 3 → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (hAdj : ∀ i j, i ≠ 2 ∨ j ≠ 2 → G.Adj (a i) (b j)) : D33 ⊑ G := by
  refine ⟨⟨⟨Sum.elim a b, ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact huv.elim
      | inr j => exact hAdj i j huv
    | inr j =>
      cases v with
      | inl i => exact (hAdj i j huv).symm
      | inr i => exact huv.elim
  · intro u v huv
    change Sum.elim a b u = Sum.elim a b v at huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (ha huv)
      | inr j => exact (hab i j huv).elim
    | inr j =>
      cases v with
      | inl i => exact (hab i j huv.symm).elim
      | inr i => exact congrArg Sum.inr (hb huv)

theorem triple_injective {V : Type*} {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Function.Injective ![u, v, w] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

open scoped Classical in
theorem third_common_neighbor {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v x y : V} (hc : 3 ≤ Fintype.card (G.commonNeighbors u v)) :
    ∃ z, G.Adj u z ∧ G.Adj v z ∧ z ≠ x ∧ z ≠ y := by
  classical
  have hsmall : ({x, y} : Finset V).card < (G.commonNeighbors u v).toFinset.card := by
    rw [Set.toFinset_card]
    have hh : ({x, y} : Finset V).card ≤ 2 := by simpa using card_insert_le x ({y} : Finset V)
    omega
  obtain ⟨z, hz, hzne⟩ := exists_mem_notMem_of_card_lt_card hsmall
  have hz' : z ∈ G.commonNeighbors u v := by simpa using hz
  have hneq : z ≠ x ∧ z ≠ y := by simpa using hzne
  exact ⟨z, hz'.1, hz'.2, hneq.1, hneq.2⟩

open scoped Classical in
theorem rectangle_has_light_pair {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hBip : G.IsBipartite) (hfree : D33.Free G)
    {u v x y : V} (huv : u ≠ v) (hxy : x ≠ y)
    (hux : G.Adj u x) (hvx : G.Adj v x) (huy : G.Adj u y) (hvy : G.Adj v y) :
    Fintype.card (G.commonNeighbors u v) ≤ 2 ∨ Fintype.card (G.commonNeighbors x y) ≤ 2 := by
  classical
  by_contra hh
  push_neg at hh
  obtain ⟨z, huz, hvz, hzx, hzy⟩ := third_common_neighbor G (x := x) (y := y) hh.1
  obtain ⟨w, hxw, hyw, hwu, hwv⟩ := third_common_neighbor G (x := u) (y := v) hh.2
  obtain ⟨χ⟩ := hBip
  have hcolv : χ v = χ u := by have h1 := χ.valid hux; have h2 := χ.valid hvx; omega
  have hcolw : χ w = χ u := by have h1 := χ.valid hux; have h2 := χ.valid hxw; omega
  have hcolx : χ x ≠ χ u := (χ.valid hux).symm
  have hcoly : χ y ≠ χ u := (χ.valid huy).symm
  have hcolz : χ z ≠ χ u := (χ.valid huz).symm
  apply hfree
  apply contained_of_maps G ![u, v, w] ![x, y, z]
    (triple_injective huv hwu.symm hwv.symm) (triple_injective hxy hzx.symm hzy.symm)
  · intro i j he
    have hci : χ (![u, v, w] i) = χ u := by fin_cases i <;> first | rfl | assumption
    have hcj : χ (![x, y, z] j) ≠ χ u := by fin_cases j <;> assumption
    exact hcj (he ▸ hci)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [adj_comm]

abbrev Pair (V : Type*) := {p : V × V // p.1 ≠ p.2}

def Rectangle {V : Type*} (G : SimpleGraph V) (p q : Pair V) : Prop :=
  G.Adj p.val.1 q.val.1 ∧ G.Adj p.val.2 q.val.1 ∧
    G.Adj p.val.1 q.val.2 ∧ G.Adj p.val.2 q.val.2

theorem rectangle_symm {V : Type*} {G : SimpleGraph V} {p q : Pair V}
    (h : Rectangle G p q) : Rectangle G q p :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

open scoped Classical in
theorem row_card {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : Pair V) :
    ((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p).card =
      (Fintype.card (G.commonNeighbors p.val.1 p.val.2)).descFactorial 2 := by
  classical
  let e : ↥((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p) ≃
      (Fin 2 ↪ G.commonNeighbors p.val.1 p.val.2) :=
    { toFun := fun q =>
        ⟨![⟨q.val.val.1, ((mem_bipartiteAbove _).mp q.prop).2.1,
            ((mem_bipartiteAbove _).mp q.prop).2.2.1⟩,
          ⟨q.val.val.2, ((mem_bipartiteAbove _).mp q.prop).2.2.2.1,
            ((mem_bipartiteAbove _).mp q.prop).2.2.2.2⟩], by
          intro i j hij
          fin_cases i <;> fin_cases j
          · rfl
          · exact (q.val.prop (congrArg Subtype.val hij)).elim
          · exact (q.val.prop (congrArg Subtype.val hij).symm).elim
          · rfl⟩
      invFun := fun f =>
        ⟨⟨((f 0).val, (f 1).val), fun he =>
          (show (0 : Fin 2) ≠ 1 by decide) (f.injective (Subtype.ext he))⟩,
          (mem_bipartiteAbove _).mpr ⟨mem_univ _, (f 0).prop.1, (f 0).prop.2,
            (f 1).prop.1, (f 1).prop.2⟩⟩
      left_inv := by intro q; rfl
      right_inv := by intro f; ext i; fin_cases i <;> rfl }
  rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_fin]

open scoped Classical in
theorem sum_rows_le_of_light {I : Type*} [Fintype I] (r : I → I → Prop)
    (P : I → Prop) (k : ℕ) (hsymm : ∀ i j, r i j → r j i)
    (hlight : ∀ i j, r i j → P i ∨ P j)
    (hrow : ∀ i, P i → ((univ : Finset I).bipartiteAbove r i).card ≤ k) :
    ∑ i, ((univ : Finset I).bipartiteAbove r i).card ≤ 2 * k * Fintype.card I := by
  classical
  let r₁ : I → I → Prop := fun i j => r i j ∧ P i
  let r₂ : I → I → Prop := fun i j => r i j ∧ P j
  have hcov (i : I) : ((univ : Finset I).bipartiteAbove r i).card ≤
      ((univ : Finset I).bipartiteAbove r₁ i).card +
      ((univ : Finset I).bipartiteAbove r₂ i).card := by
    apply (card_le_card ?_).trans (card_union_le _ _)
    intro j hj
    have hr : r i j := ((mem_bipartiteAbove r).mp hj).2
    rcases hlight i j hr with hi | hj'
    · exact mem_union_left _ ((mem_bipartiteAbove r₁).mpr ⟨mem_univ _, hr, hi⟩)
    · exact mem_union_right _ ((mem_bipartiteAbove r₂).mpr ⟨mem_univ _, hr, hj'⟩)
  have hrow₁ (i : I) : ((univ : Finset I).bipartiteAbove r₁ i).card ≤ k := by
    by_cases hi : P i
    · apply (card_le_card ?_).trans (hrow i hi)
      intro j hj
      exact (mem_bipartiteAbove r).mpr ⟨mem_univ _, ((mem_bipartiteAbove r₁).mp hj).2.1⟩
    · have he : (univ : Finset I).bipartiteAbove r₁ i = ∅ := by
        ext j
        simp [r₁, bipartiteAbove, hi]
      simp [he]
  have hcol₂ (j : I) : ((univ : Finset I).bipartiteBelow r₂ j).card ≤ k := by
    by_cases hj : P j
    · apply (card_le_card ?_).trans (hrow j hj)
      intro i hi
      exact (mem_bipartiteAbove r).mpr ⟨mem_univ _,
        hsymm i j ((mem_bipartiteBelow r₂).mp hi).2.1⟩
    · have he : (univ : Finset I).bipartiteBelow r₂ j = ∅ := by
        ext i
        simp [r₂, bipartiteBelow, hj]
      simp [he]
  calc
    ∑ i, ((univ : Finset I).bipartiteAbove r i).card ≤
        ∑ i, (((univ : Finset I).bipartiteAbove r₁ i).card +
          ((univ : Finset I).bipartiteAbove r₂ i).card) := sum_le_sum fun i _ => hcov i
    _ = (∑ i, ((univ : Finset I).bipartiteAbove r₁ i).card) +
        (∑ j, ((univ : Finset I).bipartiteBelow r₂ j).card) := by
      rw [sum_add_distrib, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r₂]
    _ ≤ (∑ _ : I, k) + (∑ _ : I, k) :=
      Nat.add_le_add (sum_le_sum fun i _ => hrow₁ i) (sum_le_sum fun j _ => hcol₂ j)
    _ = 2 * k * Fintype.card I := by simp only [sum_const, card_univ, Nat.nsmul_eq_mul]; ring

open scoped Classical in
theorem sum_rectangles_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : D33.Free G) :
    ∑ p : Pair V, ((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p).card ≤
      4 * Fintype.card (Pair V) := by
  apply sum_rows_le_of_light (Rectangle G)
    (fun p => Fintype.card (G.commonNeighbors p.val.1 p.val.2) ≤ 2) 2
    (fun _ _ h => rectangle_symm h)
  · intro p q h
    exact rectangle_has_light_pair G hBip hfree p.prop q.prop h.1 h.2.1 h.2.2.1 h.2.2.2
  · intro p hp
    rw [row_card]
    exact (Nat.descFactorial_le 2 hp).trans (by decide)

theorem le_descFactorial_two_add_one (n : ℕ) : n ≤ n.descFactorial 2 + 1 := by
  by_cases hn : n ≤ 1
  · omega
  · have hpos : 0 < n - 1 := by omega
    have hh := Nat.le_mul_of_pos_left n hpos
    simpa [Nat.descFactorial_succ] using hh.trans (Nat.le_succ _)

open scoped Classical in
theorem sum_common_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : D33.Free G) :
    ∑ p : Pair V, Fintype.card (G.commonNeighbors p.val.1 p.val.2) ≤ 5 * Fintype.card V ^ 2 := by
  have hh : (∑ p : Pair V, Fintype.card (G.commonNeighbors p.val.1 p.val.2)) ≤
      (∑ p : Pair V, ((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p).card) +
        Fintype.card (Pair V) := by
    calc
      _ ≤ ∑ p : Pair V, (((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p).card + 1) := by
        apply sum_le_sum
        intro p _
        rw [row_card]
        exact le_descFactorial_two_add_one _
      _ = _ := by simp [sum_add_distrib]
  have hsum := sum_rectangles_le G hBip hfree
  have hc : Fintype.card (Pair V) ≤ Fintype.card V ^ 2 := by
    simpa only [Fintype.card_prod, pow_two] using Fintype.card_subtype_le
      (fun p : V × V => p.1 ≠ p.2)
  omega

open scoped Classical in
theorem sum_degree_sq_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : D33.Free G) :
    ∑ v, G.degree v ^ 2 ≤ 6 * Fintype.card V ^ 2 := by
  classical
  let r : V → V × V → Prop := fun x p => G.Adj x p.1 ∧ G.Adj x p.2
  have hAbove (x : V) : ((univ : Finset (V × V)).bipartiteAbove r x).card = G.degree x ^ 2 := by
    have hs : (univ : Finset (V × V)).bipartiteAbove r x =
        G.neighborFinset x ×ˢ G.neighborFinset x := by
      ext p
      simp [r, bipartiteAbove]
    rw [hs, card_product, card_neighborFinset_eq_degree, pow_two]
  have hBelow (p : V × V) : ((univ : Finset V).bipartiteBelow r p).card =
      Fintype.card (G.commonNeighbors p.1 p.2) := by
    have hs : (univ : Finset V).bipartiteBelow r p = (G.commonNeighbors p.1 p.2).toFinset := by
      ext x
      simp [r, bipartiteBelow, mem_commonNeighbors, adj_comm]
    rw [hs, Set.toFinset_card]
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := (univ : Finset V)) (t := (univ : Finset (V × V)))
  simp_rw [hAbove, hBelow] at hsum
  rw [hsum]
  have hdiag : Fintype.card {p : V × V // ¬p.1 ≠ p.2} = Fintype.card V := by
    apply Fintype.card_congr
    refine ⟨fun p => p.val.1, fun v => ⟨(v, v), by simp⟩, ?_, ?_⟩
    · intro p
      apply Subtype.ext
      exact Prod.ext rfl (not_not.mp p.prop)
    · intro v; rfl
  have hdiagSum : (∑ p : {p : V × V // ¬p.1 ≠ p.2},
      Fintype.card (G.commonNeighbors p.val.1 p.val.2)) ≤ Fintype.card V ^ 2 := by
    calc
      _ ≤ ∑ _ : {p : V × V // ¬p.1 ≠ p.2}, Fintype.card V :=
        sum_le_sum fun p _ => Fintype.card_subtype_le _
      _ = _ := by simp only [sum_const, card_univ, hdiag, Nat.nsmul_eq_mul, pow_two]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun p : V × V => p.1 ≠ p.2)]
  have hh := sum_common_le G hBip hfree
  calc
    _ ≤ 5 * Fintype.card V ^ 2 + Fintype.card V ^ 2 := by
      apply Nat.add_le_add
      · convert hh using 1 <;> congr! 2
      · exact hdiagSum
    _ = _ := by omega

open scoped Classical in
theorem bipartite_edge_sq_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : D33.Free G) :
    G.edgeFinset.card ^ 2 ≤ 6 * Fintype.card V ^ 3 := by
  have hc := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun v => G.degree v)
  rw [card_univ, sum_degrees_eq_twice_card_edges] at hc
  have hb := Nat.mul_le_mul_left (Fintype.card V) (sum_degree_sq_le G hBip hfree)
  nlinarith

end Erdos713Minus

namespace Erdos713Minus

open Finset

open scoped Classical in
theorem edge_sq_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : D33.Free G) : G.edgeFinset.card ^ 2 ≤ 24 * Fintype.card V ^ 3 := by
  classical
  obtain ⟨K, hKG, hKBip, hhalf⟩ := Erdos713Cut.exists_bipartite_half G
  have hKfree : D33.Free K := fun hc => hfree (hc.mono_right hKG)
  have hb := bipartite_edge_sq_le K hKBip hKfree
  have hp := Nat.pow_le_pow_left hhalf 2
  nlinarith only [hb, hp]

theorem extremal_sq_le (n : ℕ) : (extremalNumber n D33) ^ 2 ≤ 24 * n ^ 3 := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | D33.Free G}
  change (S.sup (fun G => G.edgeFinset.card)) ^ 2 ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨G, hG, he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
    rw [he]
    have hfree : D33.Free G := by simpa [S] using hG
    simpa only [Fintype.card_fin] using edge_sq_le G hfree
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp

theorem exponent_upper_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : H ⊑ D33) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ (3 : ℝ) / 2 := by
  have hO : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ)) :=
    (isBigO_const_mul_left_iff hc).mp h.isBigO_symm
  have hP : (fun n : ℕ => (n : ℝ) ^ (a * (2 : ℝ))) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ) ^ (2 : ℕ)) := by
    have he (n : ℕ) : ((n : ℝ) ^ a) ^ (2 : ℕ) = (n : ℝ) ^ (a * (2 : ℝ)) := by
      have hh := Real.rpow_mul_natCast (Nat.cast_nonneg (α := ℝ) n) a 2
      norm_num only [Nat.cast_ofNat] at hh
      exact hh.symm
    simpa only [he] using hO.pow 2
  have hB : (fun n : ℕ => (extremalNumber n H : ℝ) ^ (2 : ℕ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (3 : ℝ)) := by
    apply IsBigO.of_bound (24 : ℝ)
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    have hn3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ (3 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (n : ℝ) 3
    rw [hn3, Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    exact_mod_cast (Nat.pow_le_pow_left (hH.extremalNumber_le (n := n)) 2).trans
      (extremal_sq_le n)
  have hExp := Erdos713C4.exponent_le_of_isBigO (hP.trans hB)
  linarith

theorem exponent_eq_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ D33) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (3 : ℝ) / 2 := by
  apply le_antisymm (exponent_upper_of_containment hhi hc h)
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc).mp h.isBigO
  apply Erdos713C4.lower_exponent_of_prime_bound hO
  intro p hp
  exact (Erdos713C4.extremal_lower_prime p hp).trans hlo.extremalNumber_le

theorem rational_exponent_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ D33) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3 / 2, ?_⟩
  simpa using (exponent_eq_of_containment hlo hhi hc h).symm

theorem contains_K22 : Erdos713C4.K22 ⊑ D33 := by
  let f : Fin 2 ⊕ Fin 2 → Fin 3 ⊕ Fin 3 :=
    Sum.map (Fin.castLE (by decide : 2 ≤ 3)) (Fin.castLE (by decide : 2 ≤ 3))
  refine ⟨⟨⟨f, ?_⟩, Sum.map_injective.mpr ⟨Fin.castLE_injective _, Fin.castLE_injective _⟩⟩⟩
  intro u v huv
  cases u <;> cases v <;>
    simp [f, D33, Erdos713C4.K22, completeBipartiteGraph, Fin.ext_iff] at huv ⊢ <;> omega

theorem rational_exponent {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n D33 : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) :=
  rational_exponent_of_containment contains_K22 (.refl _) hc h

end Erdos713Minus

#print axioms Erdos713Minus.rational_exponent
