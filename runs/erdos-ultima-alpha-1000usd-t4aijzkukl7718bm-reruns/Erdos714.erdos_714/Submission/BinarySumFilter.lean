import FormalConjecturesUtil

/-!
Characteristic-two sum filters of weighted norm graphs. This file proves
an obstruction to these constructions, not Erdős Problem 714.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000

namespace Erdos714BinarySumFilter
variable {E : Type*} [Field E] [CharP E 2]

/-- A bipartite graph whose edge condition depends only on the sum. -/
def graph (S : Finset E) : SimpleGraph (Bool × E) where
  Adj u v := u.1 ≠ v.1 ∧ u.2 + v.2 ∈ S
  symm := by intro u v h; exact ⟨h.1.symm, by simpa [add_comm] using h.2⟩
  loopless := by intro u h; exact h.1 rfl

/-- Four distinct elements summing to zero form the columns of a copied K44. -/
theorem cube_not_free (S : Finset E) (a b c d : E)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hs : a + b + c + d = 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S) := by
  let L : Fin 4 → Bool × E := ![(false, 0), (false, a+b), (false, a+c), (false, a+d)]
  let R : Fin 4 → Bool × E := ![(true, a), (true, b), (true, c), (true, d)]
  have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hab0 : a+b ≠ 0 := by
    intro h
    apply hab
    linear_combination h - b*h2
  have hac0 : a+c ≠ 0 := by
    intro h
    apply hac
    linear_combination h - c*h2
  have had0 : a+d ≠ 0 := by
    intro h
    apply had
    linear_combination h - d*h2
  have hL : Function.Injective L := by
    intro i j hij
    have hp := congrArg Prod.snd hij
    fin_cases i <;> fin_cases j <;>
      simp [L, hab0, hac0, had0, hab0.symm, hac0.symm, had0.symm,
        hbc, hbd, hcd, hbc.symm, hbd.symm, hcd.symm] at hp ⊢
  have hR : Function.Injective R := by
    intro i j hij
    have hp := congrArg Prod.snd hij
    fin_cases i <;> fin_cases j <;>
      simp [R, hab, hac, had, hbc, hbd, hcd,
        hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm] at hp ⊢
  have habc : a+b+c = d := by linear_combination hs - d*h2
  have habd : a+b+d = c := by linear_combination hs - c*h2
  have hacd : a+c+d = b := by linear_combination hs - b*h2
  have hE : ∀ i j, (graph S).Adj (L i) (R j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [L, R, graph, ha, hb, hc, hd,
        habc, habd, hacd, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left,
        show a+(b+c)=d by simpa [add_assoc] using habc, show a+(b+d)=c by simpa [add_assoc] using habd,
        show a+(c+d)=b by simpa [add_assoc] using hacd, add_comm, add_left_comm]
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim L R, ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u with
    | inl i => cases v with
      | inl j => simp at huv
      | inr j => exact hE i j
    | inr i => cases v with
      | inl j => exact (hE j i).symm
      | inr j => simp at huv
  · intro u v huv
    cases u with
    | inl i => cases v with
      | inl j => exact congrArg Sum.inl (hL huv)
      | inr j =>
        have h := congrArg Prod.fst huv
        have hLi : (L i).1 = false := by fin_cases i <;> rfl
        have hRj : (R j).1 = true := by fin_cases j <;> rfl
        change (L i).1 = (R j).1 at h
        rw [hLi,hRj] at h
        exact False.elim (Bool.false_ne_true h)
    | inr i => cases v with
      | inl j =>
        have h := congrArg Prod.fst huv
        have hRi : (R i).1 = true := by fin_cases i <;> rfl
        have hLj : (L j).1 = false := by fin_cases j <;> rfl
        change (R i).1 = (L j).1 at h
        rw [hRi,hLj] at h
        exact False.elim (Bool.false_ne_true h.symm)
      | inr j => exact congrArg Sum.inr (hR huv)

/-- K44-freeness forces uniqueness of sums of unordered pairs. -/
theorem pair_sum_injective (S : Finset E)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S)) :
    Set.InjOn (fun T : Finset E => ∑ x ∈ T, x) (S.powersetCard 2) := by
  intro T hT U hU heq
  obtain ⟨hTS,hTc⟩ := mem_powersetCard.mp hT
  obtain ⟨hUS,hUc⟩ := mem_powersetCard.mp hU
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hTc
  obtain ⟨c,d,hcd,rfl⟩ := card_eq_two.mp hUc
  simp only [sum_insert, mem_singleton, hab, hcd, not_false_eq_true, sum_singleton] at heq
  by_cases hac : a = c
  · subst c
    have hbd := add_left_cancel heq
    subst d
    rfl
  by_cases had : a = d
  · subst d
    have hbc : b = c := by simpa [add_comm] using heq
    subst c
    exact pair_comm a b
  by_cases hbc : b = c
  · subst c
    have had : a = d := by linear_combination heq
    exact False.elim (‹a ≠ d› had)
  by_cases hbd : b = d
  · subst d
    exact False.elim (hac (add_right_cancel heq))
  have hs : a+b+c+d = 0 := by
    rw [add_assoc, ← heq]
    exact CharTwo.add_self_eq_zero (a+b)
  exact False.elim (cube_not_free S a b c d hab hac had hbc hbd hcd
    (hTS (by simp)) (hTS (by simp)) (hUS (by simp)) (hUS (by simp)) hs hfree)

/-- An exact Sidon-type bound for characteristic-two sum graphs. -/
theorem choose_card_le [Fintype E] (S : Finset E)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S)) :
    S.card.choose 2 ≤ Fintype.card E - 1 := by
  rw [← card_powersetCard]
  have hb : (S.powersetCard 2).card ≤ (univ.erase (0 : E)).card := by
    apply card_le_card_of_injOn (fun T : Finset E => ∑ x ∈ T, x)
    · intro T hT
      obtain ⟨_,hc⟩ := mem_powersetCard.mp hT
      obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
      simp only [sum_insert, mem_singleton, hab, not_false_eq_true, sum_singleton,
        Finset.mem_coe, mem_erase, mem_univ, and_true]
      intro h
      apply hab
      have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
      linear_combination h - b*h2
    · exact pair_sum_injective S hfree
  simpa using hb

/-- A convenient real-valued consequence of the exact pair bound. -/
theorem sq_card_le [Fintype E] (S : Finset E)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S)) :
    (S.card : ℝ)^2 ≤ 2 * Fintype.card E + S.card := by
  have h : (S.card.choose 2 : ℝ) ≤ Fintype.card E := by
    exact_mod_cast (choose_card_le S hfree).trans (Nat.sub_le _ _)
  rw [Nat.cast_choose_two] at h
  nlinarith

section Weighted
variable {A : Type*} [CommGroup A]

/-- Weighted sum graphs, including unit-valued norms. `D` is an arbitrary
connection set; the label need not have any algebraic properties. -/
def weightedGraph (D : Finset E) (N : E → A) : SimpleGraph (Bool × (E × A)) where
  Adj u v := u.1 ≠ v.1 ∧ u.2.1 + v.2.1 ∈ D ∧ N (u.2.1 + v.2.1) = u.2.2 * v.2.2
  symm := by intro u v h; exact ⟨h.1.symm, by simpa [add_comm, mul_comm] using h.2⟩
  loopless := by intro u h; exact h.1 rfl

/-- A single-label sum graph copies into the full weighted graph. -/
def fiberCopy (D : Finset E) (N : E → A) (c : A) :
    (graph (D.filter (fun z => N z = c))).Copy (weightedGraph D N) where
  toHom := {
    toFun v := (v.1, (v.2, if v.1 then c else 1))
    map_rel' := by
      rintro ⟨bu,x⟩ ⟨bv,y⟩ h
      change bu ≠ bv ∧ x+y ∈ D.filter (fun z => N z = c) at h
      have hm := mem_filter.mp h.2
      cases bu <;> cases bv <;> simp_all [weightedGraph]
  }
  injective' := by
    rintro ⟨bu,x⟩ ⟨bv,y⟩ h
    have hb := congrArg (fun v : Bool × (E × A) => v.1) h
    have hx := congrArg (fun v : Bool × (E × A) => v.2.1) h
    exact Prod.ext hb hx

omit [CharP E 2] in
/-- Every label fiber of a K44-free weighted graph satisfies the pair bound. -/
theorem fiber_free (D : Finset E) (N : E → A)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (weightedGraph D N)) (c : A) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (D.filter (fun z => N z = c))) := by
  rintro ⟨f⟩
  exact hfree ⟨(fiberCopy D N c).comp f⟩

/-- Arbitrary connection restrictions of a binary weighted sum graph obey
this density-loss bound if they are K44-free. -/
theorem connection_bound [Fintype E] [Fintype A] (D : Finset E) (N : E → A)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (weightedGraph D N)) :
    (D.card : ℝ)^2 ≤ Fintype.card A *
      (2 * Fintype.card E * Fintype.card A + D.card) := by
  let s : A → ℝ := fun c => (D.filter (fun z => N z = c)).card
  have hsum : ∑ c, s c = (D.card : ℝ) := by
    have h : ∑ c : A, (D.filter (fun z => N z = c)).card = D.card := by
      simpa using (card_eq_sum_card_fiberwise (s := D)
        (t := (univ : Finset A)) (f := N) (by intro z hz; simp)).symm
    dsimp [s]
    exact_mod_cast h
  have hsq : ∑ c, s c ^ 2 ≤ 2 * Fintype.card E * Fintype.card A + D.card := by
    calc
      ∑ c, s c ^ 2 ≤ ∑ c, (2 * (Fintype.card E : ℝ) + s c) := by
        apply sum_le_sum
        intro c _
        exact sq_card_le _ (fiber_free D N hfree c)
      _ = _ := by rw [sum_add_distrib, hsum]; simp; ring
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset A) (fun _ => (1 : ℝ)) s
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, hsum] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))

/-- For any label map, a neighbor is determined by its retained sum. -/
def neighborEquiv (D : Finset E) (N : E → A) (p : Bool × (E × A)) :
    (weightedGraph D N).neighborSet p ≃ D where
  toFun v := ⟨p.2.1 + v.val.2.1, v.property.2.1⟩
  invFun z := ⟨(!p.1, ((z : E)-p.2.1, N z / p.2.2)), by
    constructor
    · cases p.1 <;> simp
    · change p.2.1 + ((z : E)-p.2.1) ∈ D ∧
        N (p.2.1 + ((z : E)-p.2.1)) = p.2.2 * (N z / p.2.2)
      rw [show p.2.1 + ((z : E)-p.2.1) = z by ring]
      exact ⟨z.property, (by simp [div_eq_mul_inv])⟩⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · change (!p.1) = v.val.1
      have h := v.property.1
      cases hp : p.1 <;> cases hv : v.val.1 <;> simp_all
    · apply Prod.ext
      · change p.2.1 + v.val.2.1 - p.2.1 = v.val.2.1
        ring
      · change N (p.2.1 + v.val.2.1) / p.2.2 = v.val.2.2
        rw [v.property.2.2]
        simp [div_eq_mul_inv, mul_assoc]
  right_inv z := by apply Subtype.ext; change p.2.1 + ((z : E)-p.2.1) = z; ring

omit [CharP E 2] in
lemma degree_eq [Fintype E] [Fintype A] (D : Finset E) (N : E → A)
    (p : Bool × (E × A)) : (weightedGraph D N).degree p = D.card := by
  rw [← card_neighborSet_eq_degree, ← Fintype.card_coe]
  exact Fintype.card_congr (neighborEquiv D N p)

omit [CharP E 2] in
/-- Exact edge count, including for non-algebraic label maps. -/
theorem edge_count [Fintype E] [Fintype A] (D : Finset E) (N : E → A) :
    (weightedGraph D N).edgeFinset.card = Fintype.card E * Fintype.card A * D.card := by
  have h := (weightedGraph D N).sum_degrees_eq_twice_card_edges
  simp only [degree_eq, sum_const, card_univ, Fintype.card_prod, Fintype.card_bool,
    nsmul_eq_mul] at h
  nlinarith

/-- At cubic scales, a free connection set has size O(q^(5/2)). -/
theorem cubic_connection_bound [Fintype E] [Fintype A] (D : Finset E) (N : E → A)
    (q : ℕ) (hq : 1 ≤ q) (hE : Fintype.card E = q^3) (hA : Fintype.card A ≤ q)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (weightedGraph D N)) :
    (D.card : ℝ)^2 ≤ 3 * (q : ℝ)^5 := by
  have h := connection_bound D N hfree
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hAR : (Fintype.card A : ℝ) ≤ q := by exact_mod_cast hA
  have hER : (Fintype.card E : ℝ) = (q : ℝ)^3 := by exact_mod_cast hE
  have hdR : (D.card : ℝ) ≤ (q : ℝ)^3 := by
    rw [← hER]
    exact_mod_cast card_le_univ D
  have hs : (D.card : ℝ)^2 ≤ 3*(q : ℝ)^5 := by
    calc
      (D.card : ℝ)^2 ≤ Fintype.card A *
          (2 * Fintype.card E * Fintype.card A + D.card) := h
      _ ≤ (q : ℝ) * (2 * (q : ℝ)^3 * q + (q : ℝ)^3) := by
        rw [hER]
        gcongr
      _ ≤ 3 * (q : ℝ)^5 := by nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ) ≤ q) 4) (sub_nonneg.mpr hqR)]
  exact hs

/-- A strict power loss in edges at the cubic norm-graph scale. -/
theorem cubic_scale_bound [Fintype E] [Fintype A] (D : Finset E) (N : E → A)
    (q : ℕ) (hq : 1 ≤ q) (hE : Fintype.card E = q^3) (hA : Fintype.card A ≤ q)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (weightedGraph D N)) :
    ((weightedGraph D N).edgeFinset.card : ℝ)^2 ≤ 3 * (q : ℝ)^13 := by
  have hs := cubic_connection_bound D N q hq hE hA hfree
  have hAR : (Fintype.card A : ℝ) ≤ q := by exact_mod_cast hA
  have hER : (Fintype.card E : ℝ) = (q : ℝ)^3 := by exact_mod_cast hE
  rw [edge_count]
  push_cast
  rw [hER, mul_pow, mul_pow]
  calc
    ((q : ℝ)^3)^2 * (Fintype.card A : ℝ)^2 * (D.card : ℝ)^2 ≤
        ((q : ℝ)^3)^2 * (q : ℝ)^2 * (3*(q : ℝ)^5) := by gcongr
    _ = _ := by ring

/-- A uniform exclusion of fixed-density connection sets. The constant 16
is deliberately non-sharp and avoids analytic estimates. -/
theorem fixed_index_not_free [Fintype E] [Fintype A] (D : Finset E) (N : E → A)
    (q ell : ℕ) (hell : 1 ≤ ell) (hq : 16*ell^2 ≤ q)
    (hE : Fintype.card E = q^3) (hA : Fintype.card A ≤ q)
    (hsize : D.card * ell = q^3 - 1) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (weightedGraph D N) := by
  have hq2 : 2 ≤ q := by nlinarith
  have hq1 : 1 ≤ q := by omega
  have hq3 : 1 ≤ q^3 := one_le_pow₀ hq1
  have hqR : 16*(ell : ℝ)^2 ≤ q := by exact_mod_cast hq
  have hq2R : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq3R : (2 : ℝ) ≤ (q : ℝ)^3 := by
    have h : (2 : ℝ)^3 ≤ (q : ℝ)^3 := by gcongr
    norm_num at h
    linarith
  have hsizeR : (D.card : ℝ) * ell = (q : ℝ)^3 - 1 := by
    exact_mod_cast hsize
  intro hfree
  have hb := cubic_connection_bound D N q hq1 hE hA hfree
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (ell : ℝ))
  have hmul := mul_le_mul_of_nonneg_right hqR
    (show 0 ≤ 3*(q : ℝ)^5 by positivity)
  have hlo : (q : ℝ)^6 ≤ 4*((q : ℝ)^3-1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq3R)
      (show (0 : ℝ) ≤ 3*(q : ℝ)^3-2 by linarith)]
  have heq := congrArg (fun x : ℝ => x^2) hsizeR
  have hpos : (0 : ℝ) < (q : ℝ)^6 := by positivity
  nlinarith

end Weighted

#print axioms cube_not_free
#print axioms pair_sum_injective
#print axioms choose_card_le
#print axioms sq_card_le
#print axioms fiber_free
#print axioms connection_bound
#print axioms edge_count
#print axioms cubic_connection_bound
#print axioms cubic_scale_bound
#print axioms fixed_index_not_free
end Erdos714BinarySumFilter
