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

namespace Erdos713K2t

abbrev K2t (t : ℕ) := completeBipartiteGraph (Fin 2) (Fin t)

open scoped Classical in
theorem common_card_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : ℕ} (h : (K2t t).Free G) {u v : V} (huv : u ≠ v) :
    Fintype.card (G.commonNeighbors u v) < t := by
  classical
  by_contra ht
  have ht' : t ≤ (G.commonNeighbors u v).toFinset.card := by
    rw [Set.toFinset_card]
    exact Nat.le_of_not_gt ht
  obtain ⟨R, hR, hcardR⟩ := Finset.exists_subset_card_eq ht'
  apply h
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{u, v}, R, by simp [huv], by simpa using hcardR, ?_⟩
  intro x hx y hy
  have hy' : y ∈ G.commonNeighbors u v := by simpa using hR hy
  simp only [mem_coe, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hy'.1
  · exact hy'.2

open scoped Classical in
theorem common_card_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : ℕ} (h : (K2t t).Free G) (u v : V) :
    Fintype.card (G.commonNeighbors u v) ≤ t + if u = v then Fintype.card V else 0 := by
  classical
  by_cases huv : u = v
  · simp only [huv, ↓reduceIte]
    exact (Fintype.card_subtype_le _).trans (by omega)
  · simpa only [huv, ↓reduceIte, add_zero] using (common_card_lt G h huv).le

open scoped Classical in
theorem sum_degree_sq_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : ℕ} (h : (K2t t).Free G) :
    ∑ v, G.degree v ^ 2 ≤ (t + 1) * Fintype.card V ^ 2 := by
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
        ∑ u : V, ∑ v : V, (t + if u = v then Fintype.card V else 0) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      exact common_card_le G h u v
    _ = (t + 1) * Fintype.card V ^ 2 := by
      simp [sum_add_distrib, sum_ite_eq, pow_two, Nat.mul_add]
      ring

open scoped Classical in
theorem edge_sq_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : ℕ} (h : (K2t t).Free G) :
    G.edgeFinset.card ^ 2 ≤ (t + 1) * Fintype.card V ^ 3 := by
  have hc := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun v => G.degree v)
  rw [card_univ, sum_degrees_eq_twice_card_edges] at hc
  have hb := sum_degree_sq_bound G h
  have hm := Nat.mul_le_mul_left (Fintype.card V) hb
  nlinarith

open scoped Classical in
theorem edge_rpow_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : ℕ} (h : (K2t t).Free G) :
    (G.edgeFinset.card : ℝ) ≤ ((t : ℝ) + 1) * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) := by
  have hsq : (G.edgeFinset.card : ℝ) ^ 2 ≤
      ((t : ℝ) + 1) * (Fintype.card V : ℝ) ^ 3 := by
    exact_mod_cast edge_sq_bound G h
  have hpow : ((Fintype.card V : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 =
      (Fintype.card V : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hc : (t : ℝ) + 1 ≤ ((t : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have hm := mul_le_mul_of_nonneg_right hc
    (pow_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card V)) 3)
  have heq : (((t : ℝ) + 1) * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 =
      ((t : ℝ) + 1) ^ 2 * (Fintype.card V : ℝ) ^ 3 := by
    rw [mul_pow, hpow]
  have hn : 0 ≤ ((t : ℝ) + 1) * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  nlinarith

theorem extremal_upper (t n : ℕ) :
    (extremalNumber n (K2t t) : ℝ) ≤ ((t : ℝ) + 1) * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ hG
  exact edge_rpow_bound G hG

theorem contains_K22 {t : ℕ} (ht : 2 ≤ t) : Erdos713C4.K22 ⊑ K2t t := by
  refine ⟨⟨⟨Sum.map id (Fin.castLE ht), ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u <;> cases v <;> simpa [Erdos713C4.K22, K2t, completeBipartiteGraph] using huv
  · exact Sum.map_injective.mpr ⟨Function.injective_id, Fin.castLE_injective ht⟩

theorem exponent_eq_of_containment {W : Type*} {G : SimpleGraph W} {t : ℕ}
    (hlo : Erdos713C4.K22 ⊑ G) (hhi : G ⊑ K2t t) {a c : ℝ} (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (3 : ℝ) / 2 := by
  have hUpper : (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) := by
    apply IsBigO.of_bound ((t : ℝ) + 1)
    filter_upwards with n
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
    calc
      (extremalNumber n G : ℝ) ≤ (extremalNumber n (K2t t) : ℝ) := by
        exact_mod_cast hhi.extremalNumber_le (n := n)
      _ ≤ ((t : ℝ) + 1) * (n : ℝ) ^ ((3 : ℝ) / 2) := extremal_upper t n
  have hpower : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) :=
    (isBigO_const_mul_left_iff hc.ne').mp (h.isBigO_symm.trans hUpper)
  have hO : (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc.ne').mp h.isBigO
  apply le_antisymm (Erdos713C4.exponent_le_of_isBigO hpower)
  apply Erdos713C4.lower_exponent_of_prime_bound hO
  intro p hp
  exact (Erdos713C4.extremal_lower_prime p hp).trans hlo.extremalNumber_le

theorem rational_exponent_of_containment {W : Type*} {G : SimpleGraph W} {t : ℕ}
    (hlo : Erdos713C4.K22 ⊑ G) (hhi : G ⊑ K2t t) {a c : ℝ} (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3 / 2, ?_⟩
  simpa using (exponent_eq_of_containment hlo hhi hc h).symm

theorem rational_exponent {t : ℕ} (ht : 2 ≤ t) {a c : ℝ} (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n (K2t t) : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) :=
  rational_exponent_of_containment (contains_K22 ht) (.refl _) hc h

end Erdos713K2t


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

end Erdos713Leaf

namespace Erdos713Reduction

universe u

open scoped Classical in
inductive Reduces : (W : Type u) → [Fintype W] → SimpleGraph W → Prop where
  | core {W : Type u} [Fintype W] {G : SimpleGraph W} {t : ℕ}
      (hlo : Erdos713C4.K22 ⊑ G) (hhi : G ⊑ Erdos713K2t.K2t t) : Reduces W G
  | leaf {W : Type u} [Fintype W] {G : SimpleGraph W} {x y : W}
      (hx : Nat.card (G.neighborSet x) = 1) (hxy : G.Adj x y)
      (h : Reduces ↥({x}ᶜ : Set W) (G.induce {x}ᶜ)) : Reduces W G

theorem rational_of_reduces {W : Type u} [Fintype W] {G : SimpleGraph W}
    (hr : Reduces W G) {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  revert h
  induction hr with
  | core hlo hhi =>
    intro h
    exact Erdos713K2t.rational_exponent_of_containment hlo hhi hc h
  | @leaf W inst G x y hx hxy hr ih =>
    intro h
    have hx' : G.degree x = 1 := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hx
    exact ih (Erdos713Leaf.leaf_asymptotic G hx' hxy ha hc.ne' h)

end Erdos713Reduction

#print axioms Erdos713Reduction.rational_of_reduces
