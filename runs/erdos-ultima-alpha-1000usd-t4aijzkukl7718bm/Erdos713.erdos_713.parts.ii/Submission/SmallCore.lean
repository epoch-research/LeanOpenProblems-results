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


namespace Erdos713SmallCore

open Finset

open scoped Classical in
theorem exists_two_neighbors {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (v : W) (hd : 2 ≤ H.degree v) :
    ∃ x y, H.Adj v x ∧ H.Adj v y ∧ x ≠ y := by
  have hc : 1 < (H.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp hc
  exact ⟨x, y, by simpa using hx, by simpa using hy, hxy⟩

open scoped Classical in
theorem adjacent_of_left_right {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] {t : ℕ} (f : Copy H (Erdos713K2t.K2t t))
    {u v : W} {i : Fin 2} {j : Fin t}
    (hu : f u = Sum.inl i) (hv : f v = Sum.inr j) (hd : 2 ≤ H.degree v) :
    H.Adj u v := by
  classical
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_neighbors H v hd
  have hfx := f.toHom.map_rel' hx
  have hfy := f.toHom.map_rel' hy
  change (Erdos713K2t.K2t t).Adj (f v) (f x) at hfx
  change (Erdos713K2t.K2t t).Adj (f v) (f y) at hfy
  cases hX : f x with
  | inr a => simp [hX, hv, Erdos713K2t.K2t, completeBipartiteGraph] at hfx
  | inl a =>
    cases hY : f y with
    | inr b => simp [hY, hv, Erdos713K2t.K2t, completeBipartiteGraph] at hfy
    | inl b =>
      have hab : a ≠ b := by
        intro he
        exact hxy (f.injective (hX.trans ((congrArg Sum.inl he).trans hY.symm)))
      have hi : i = a ∨ i = b := by omega
      rcases hi with hi | hi
      · have he : u = x := f.injective (hu.trans ((congrArg Sum.inl hi).trans hX.symm))
        exact he ▸ hx.symm
      · have he : u = y := f.injective (hu.trans ((congrArg Sum.inl hi).trans hY.symm))
        exact he ▸ hy.symm

open scoped Classical in
theorem contains_K22_of_degree_two {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {t : ℕ}
    (hd : ∀ v, 2 ≤ H.degree v) (hH : H ⊑ Erdos713K2t.K2t t) : Erdos713C4.K22 ⊑ H := by
  classical
  obtain ⟨f⟩ := hH
  have hleft : ∃ (u : W) (i : Fin 2), f u = Sum.inl i := by
    let v : W := Classical.choice inferInstance
    obtain ⟨w, hw⟩ := (H.degree_pos_iff_exists_adj v).mp (by have := hd v; omega)
    have hfw := f.toHom.map_rel' hw
    change (Erdos713K2t.K2t t).Adj (f v) (f w) at hfw
    cases hv : f v with
    | inl i => exact ⟨v, i, hv⟩
    | inr j =>
      cases hw' : f w with
      | inl i => exact ⟨w, i, hw'⟩
      | inr k => simp [hv, hw', Erdos713K2t.K2t, completeBipartiteGraph] at hfw
  obtain ⟨u, i, hu⟩ := hleft
  obtain ⟨x, y, hux, huy, hxy⟩ := exists_two_neighbors H u (hd u)
  have hright {z : W} (hz : H.Adj u z) : ∃ j : Fin t, f z = Sum.inr j := by
    have hF := f.toHom.map_rel' hz
    change (Erdos713K2t.K2t t).Adj (f u) (f z) at hF
    cases hZ : f z with
    | inl j => simp [hu, hZ, Erdos713K2t.K2t, completeBipartiteGraph] at hF
    | inr j => exact ⟨j, rfl⟩
  obtain ⟨j, hX⟩ := hright hux
  obtain ⟨k, hY⟩ := hright huy
  obtain ⟨a, b, hxa, hxb, hab⟩ := exists_two_neighbors H x (hd x)
  have hv : ∃ v, v ≠ u ∧ H.Adj x v := by
    by_cases hau : a = u
    · exact ⟨b, fun hbu => hab (hau.trans hbu.symm), hxb⟩
    · exact ⟨a, hau, hxa⟩
  obtain ⟨v, hvu, hxv⟩ := hv
  have hV : ∃ l : Fin 2, f v = Sum.inl l := by
    have hF := f.toHom.map_rel' hxv
    change (Erdos713K2t.K2t t).Adj (f x) (f v) at hF
    cases hV : f v with
    | inl l => exact ⟨l, rfl⟩
    | inr l => simp [hX, hV, Erdos713K2t.K2t, completeBipartiteGraph] at hF
  obtain ⟨l, hV⟩ := hV
  have hvy : H.Adj v y := adjacent_of_left_right H f hV hY (hd y)
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{u, v}, {x, y}, by simp [hvu.symm], by simp [hxy], ?_⟩
  intro a ha b hb
  simp only [mem_coe, mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hux
  · exact huy
  · exact hxv.symm
  · exact hvy

open scoped Classical in
theorem contained_of_small_bipartition {W : Type*} [Fintype W]
    (H : SimpleGraph W) (S : Set W) (hS : Nat.card S ≤ 2)
    (hB : H.IsBipartiteWith S Sᶜ) : H ⊑ Erdos713K2t.K2t (Fintype.card W) := by
  classical
  let eL : S ↪ Fin 2 := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hS))
  let eR : ↥(Sᶜ) ↪ Fin (Fintype.card W) :=
    (Function.Embedding.subtype _).trans (Fintype.equivFin W).toEmbedding
  let e := (Equiv.Set.sumCompl S).symm.toEmbedding.trans (eL.sumMap eR)
  refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
  intro u v huv
  rcases hB.2 huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hv' : v ∉ S := hv
    simp [e, Equiv.Set.sumCompl_symm_apply_of_mem hu,
      Equiv.Set.sumCompl_symm_apply_of_notMem hv', Erdos713K2t.K2t, completeBipartiteGraph]
  · have hu' : u ∉ S := hu
    simp [e, Equiv.Set.sumCompl_symm_apply_of_mem hv,
      Equiv.Set.sumCompl_symm_apply_of_notMem hu', Erdos713K2t.K2t, completeBipartiteGraph]

open scoped Classical in
theorem small_bipartite_contained {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hB : H.IsBipartite) (hcard : Fintype.card W ≤ 5) :
    H ⊑ Erdos713K2t.K2t (Fintype.card W) := by
  classical
  obtain ⟨χ⟩ := hB
  let S : Set W := {v | χ v = 0}
  have hS : H.IsBipartiteWith S Sᶜ := by
    refine ⟨disjoint_compl_right, ?_⟩
    intro u v huv
    have hχ := χ.valid huv
    simp only [S, Set.mem_setOf_eq, Set.mem_compl_iff]
    omega
  by_cases hcS : Nat.card S ≤ 2
  · exact contained_of_small_bipartition H S hcS hS
  · have hcSc : Nat.card ↥(Sᶜ) ≤ 2 := by
      have he : Nat.card ↥(Sᶜ) = Fintype.card W - Nat.card S := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_compl_set]
      rw [he]
      omega
    apply contained_of_small_bipartition H Sᶜ hcSc
    simpa only [compl_compl] using hS.symm

open scoped Classical in
theorem rational_exponent_of_card_le_five {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hB : H.IsBipartite)
    (hcard : Fintype.card W ≤ 5) (hd : ∀ v, 2 ≤ H.degree v)
    {a c : ℝ} (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  have hhi := small_bipartite_contained H hB hcard
  exact Erdos713K2t.rational_exponent_of_containment
    (contains_K22_of_degree_two H hd hhi) hhi hc h

end Erdos713SmallCore

#print axioms Erdos713SmallCore.rational_exponent_of_card_le_five
