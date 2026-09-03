import Submission.Packing

/-!
Binary Cayley obstructions for arbitrary additive groups of exponent two and
arbitrary weighted membership relations, including additive quotient points.
This is not a solution of Erdős 714.
-/

noncomputable section
open SimpleGraph Finset Classical

namespace Erdos714BinaryQuotientLaw

variable {G : Type*} [AddCommGroup G]

lemma add_eq_zero (h₂ : ∀ x : G, x+x=0) {a b : G} (h : a+b=0) : a=b := by
  calc
    a = (a+b)+b := by rw [add_assoc, h₂, add_zero]
    _ = b := by rw [h, zero_add]

lemma double_add (h₂ : ∀ x : G, x+x=0) (x y : G) : x+(x+y)=y := by
  rw [← add_assoc, h₂, zero_add]

/-- The bipartite Cayley graph with connection set `S`. -/
def cayley (S : Set G) : SimpleGraph (Bool × G) where
  Adj x y := x.1 ≠ y.1 ∧ x.2 + y.2 ∈ S
  symm := by
    intro x y h
    exact ⟨h.1.symm, by simpa only [add_comm] using h.2⟩
  loopless := by intro x h; exact h.1 rfl

/-- The four elements of a binary plane through zero. -/
def plane (u v : G) : Fin 4 → G := ![0, u, v, u + v]

lemma plane_injective (h₂ : ∀ x : G, x+x=0) {u v : G} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Function.Injective (plane u v) := by
  have huv0 : u + v ≠ 0 := fun h => huv (add_eq_zero h₂ h)
  have huuv : u ≠ u + v := by
    intro h
    apply hv
    exact (add_left_cancel (show u + 0 = u + v by simpa using h)).symm
  have hvuv : v ≠ u + v := by
    intro h
    apply hu
    exact (add_right_cancel (show 0 + v = u + v by simpa using h)).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [plane, hu, hv, huv, huv0, huuv, hvuv, Ne.symm hu, Ne.symm hv,
      Ne.symm huv, Ne.symm huv0, Ne.symm huuv, Ne.symm hvuv] at hij ⊢

lemma plane_closed (h₂ : ∀ x : G, x+x=0) (u v : G) (i j : Fin 4) :
    ∃ k, plane u v i + plane u v j = plane u v k := by
  fin_cases i <;> fin_cases j <;>
    simp [h₂, double_add h₂, Fin.exists_fin_succ, plane, add_left_comm, add_comm]

/-- An affine binary plane in the connection set gives a `K_{4,4}`. -/
theorem not_free_of_plane (h₂ : ∀ x : G, x+x=0) (S : Set G) {p u v : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hS : ∀ i, p + plane u v i ∈ S) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (cayley S) := by
  intro hfree
  apply hfree
  let L (i : Fin 4) : Bool × G := (false, plane u v i)
  let R (i : Fin 4) : Bool × G := (true, p + plane u v i)
  have hL : Function.Injective L := by
    intro i j h
    exact plane_injective h₂ hu hv huv (congrArg Prod.snd h)
  have hR : Function.Injective R := by
    intro i j h
    exact plane_injective h₂ hu hv huv (add_left_cancel (congrArg Prod.snd h))
  have hE : ∀ i j, (cayley S).Adj (L i) (R j) := by
    intro i j
    refine ⟨Bool.false_ne_true, ?_⟩
    obtain ⟨k, hk⟩ := plane_closed h₂ u v i j
    change plane u v i + (p + plane u v j) ∈ S
    rw [add_left_comm, hk]
    exact hS k
  refine ⟨⟨⟨Sum.elim L R, ?_⟩, ?_⟩⟩
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => simp at hab
      | inr j => exact hE i j
    | inr i =>
      cases b with
      | inl j => exact (hE j i).symm
      | inr j => simp at hab
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hL hab)
      | inr j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst hab))
    | inr i =>
      cases b with
      | inl j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst hab).symm)
      | inr j => exact congrArg Sum.inr (hR hab)

/-- Pair-sum counting forces an affine binary plane in a large connection set. -/
theorem exists_plane_of_card [Fintype G] (h₂ : ∀ x : G, x+x=0) (S : Finset G)
    (hcard : 2 * Fintype.card G < S.card * (S.card - 1)) :
    ∃ p u v : G, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
      ∀ i, p + plane u v i ∈ S := by
  classical
  have hc : (Finset.univ : Finset G).card * 2 < S.offDiag.card := by
    simpa only [Finset.card_univ, Finset.offDiag_card, Nat.mul_sub_left_distrib,
      Nat.mul_one, mul_comm] using hcard
  obtain ⟨z, _, hz⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S.offDiag) (t := Finset.univ) (f := fun xy : G × G => xy.1 + xy.2)
    (fun _ _ => Finset.mem_univ _) hc
  let T := S.offDiag.filter (fun xy : G × G => xy.1 + xy.2 = z)
  have hT : 2 < T.card := hz
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  obtain ⟨y, hy, hyn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    ((Finset.card_le_two (a := x) (b := (x.2, x.1))).trans_lt hT)
  obtain ⟨hab, hsum⟩ := Finset.mem_filter.mp hx
  obtain ⟨hcd, hsum'⟩ := Finset.mem_filter.mp hy
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hab
  obtain ⟨hc, hd, hcd⟩ := Finset.mem_offDiag.mp hcd
  have hne : y ≠ x ∧ y ≠ (x.2, x.1) := by simpa using hyn
  have heq : x.1 + x.2 = y.1 + y.2 := hsum.trans hsum'.symm
  have hca : y.1 ≠ x.1 := by
    intro h
    apply hne.1
    apply Prod.ext h
    exact (add_left_cancel (heq.trans (by rw [h]))).symm
  have hcb : y.1 ≠ x.2 := by
    intro h
    apply hne.2
    apply Prod.ext h
    have hh : x.2 + x.1 = x.2 + y.2 := by
      simpa only [h, add_comm] using heq
    exact (add_left_cancel hh).symm
  refine ⟨x.1, x.1 + x.2, x.1 + y.1, ?_, ?_, ?_, ?_⟩
  · exact fun h => hab (add_eq_zero h₂ h)
  · exact fun h => hca (add_eq_zero h₂ h).symm
  · exact fun h => hcb (add_left_cancel h).symm
  · intro i
    fin_cases i
    · simpa [h₂, double_add h₂, plane] using ha
    · simpa [h₂, double_add h₂, plane, add_assoc, add_left_comm, add_comm] using hb
    · simpa [h₂, double_add h₂, plane, add_assoc, add_left_comm, add_comm] using hc
    · have hh : x.1 + x.2 + y.1 = y.2 := by
        rw [heq]
        simp [double_add h₂, add_comm]
      simpa [h₂, double_add h₂, plane, add_assoc, add_left_comm, add_comm, ← hh] using hd

/-- A binary Cayley graph free of `K_{4,4}` must have a Sidon-sized connection set. -/
theorem cayley_card_bound [Fintype G] (h₂ : ∀ x : G, x+x=0) (S : Finset G)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (cayley (S : Set G))) :
    S.card * (S.card - 1) ≤ 2 * Fintype.card G := by
  by_contra h
  obtain ⟨p, u, v, hu, hv, huv, hS⟩ := exists_plane_of_card h₂ S (by omega)
  exact not_free_of_plane h₂ _ hu hv huv hS hfree



variable {A B : Type*}

/-- The membership relation need not be a fiber of a single-valued function. -/
def graph [Fintype G] [Fintype B] (R : G → A → B → Prop) :
    SimpleGraph ((G × A) ⊕ (G × B)) :=
  Erdos714Packing.incidence (fun p => univ.filter (fun q => R (p.1+q.1) p.2 q.2))

variable [Fintype G] [Fintype A] [Fintype B]

def fiberCopy (R : G → A → B → Prop) (a : A) (b : B) :
    Copy (cayley {x | R x a b}) (graph R) where
  toHom := {
    toFun := fun p => if p.1 then Sum.inr (p.2,b) else Sum.inl (p.2,a)
    map_rel' := by
      rintro ⟨bx,x⟩ ⟨cy,y⟩ h
      cases bx <;> cases cy <;>
        simp_all [cayley, graph, Erdos714Packing.incidence, add_comm] }
  injective' := by
    rintro ⟨bx,x⟩ ⟨cy,y⟩ h
    cases bx <;> cases cy <;> simp_all

omit [Fintype A] in
theorem fiber_bound (h₂ : ∀ x : G, x+x=0) (R : G → A → B → Prop)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph R))
    (a : A) (b : B) :
    let m := (univ.filter (fun x => R x a b)).card
    m*(m-1) ≤ 2*Fintype.card G := by
  apply cayley_card_bound h₂
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (cayley {x | R x a b}) := by
    rintro ⟨g⟩
    exact hfree ⟨(fiberCopy R a b).comp g⟩
  simpa only [coe_filter, coe_univ, Set.setOf_mem_eq, Set.mem_univ, mem_univ, true_and] using hf

omit [Fintype A] in
lemma fiber_square_bound (h₂ : ∀ x : G, x+x=0) (R : G → A → B → Prop)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph R))
    (a : A) (b : B) :
    (univ.filter (fun x => R x a b)).card ^ 2 ≤ 3*Fintype.card G := by
  let m := (univ.filter (fun x => R x a b)).card
  have hm : m ≤ Fintype.card G := card_filter_le _ _
  have h := fiber_bound h₂ R hfree a b
  change m*(m-1) ≤ 2*Fintype.card G at h
  change m^2 ≤ 3*Fintype.card G
  by_cases hz : m = 0
  · simp [hz]
  · have hs : m-1+1=m := Nat.sub_add_cancel (by omega)
    nlinarith

lemma fiber_translate_card (S : G → Prop) (x : G) :
    (univ.filter (fun y => S (x+y))).card = (univ.filter S).card := by
  apply card_bij (fun y _ => x+y)
  · intro y hy
    simpa using hy
  · intro y hy z hz he
    exact add_left_cancel he
  · intro z hz
    exact ⟨-x+z, by simpa using hz, by simp⟩

omit [Fintype A] in
lemma neighbor_card (R : G → A → B → Prop) (x : G) (a : A) :
    (univ.filter (fun q : G × B => R (x+q.1) a q.2)).card =
      ∑ b : B, (univ.filter (fun y => R y a b)).card := by
  calc
    _ = ∑ b : B, (univ.filter (fun y => R (x+y) a b)).card := by
      simp only [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
      rw [sum_comm]
    _ = _ := sum_congr rfl (fun b _ => fiber_translate_card (fun y => R y a b) x)

/-- Exact edge count for arbitrary weighted membership relations. -/
theorem edges (R : G → A → B → Prop) :
    (graph R).edgeFinset.card = Fintype.card G *
      ∑ p : A × B, (univ.filter (fun y => R y p.1 p.2)).card := by
  rw [graph, Erdos714Packing.incidence_edges]
  simp_rw [Fintype.sum_prod_type, neighbor_card]
  rw [sum_const, card_univ, smul_eq_mul]

/-- General full-relation edge bound, without any ring structure on the point group. -/
theorem edge_square_bound (h₂ : ∀ x : G, x+x=0) (R : G → A → B → Prop)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph R)) :
    (graph R).edgeFinset.card ^ 2 ≤
      3 * Fintype.card G ^ 3 * Fintype.card A ^ 2 * Fintype.card B ^ 2 := by
  let m (p : A × B) := (univ.filter (fun y => R y p.1 p.2)).card
  have hm : (∑ p, m p)^2 ≤ Fintype.card (A × B) * ∑ p, m p^2 := by
    simpa only [one_mul, one_pow, sum_const, card_univ, smul_eq_mul, mul_one] using
      (sum_mul_sq_le_sq_mul_sq (R := ℕ) (univ : Finset (A × B)) (fun _ => 1) m)
  have hs : ∑ p, m p^2 ≤ Fintype.card (A × B) * (3*Fintype.card G) := by
    calc
      _ ≤ ∑ _p : A × B, 3*Fintype.card G :=
        sum_le_sum (fun p _ => fiber_square_bound h₂ R hfree p.1 p.2)
      _ = _ := by simp
  rw [edges, mul_pow]
  calc
    Fintype.card G ^ 2 * (∑ p, m p)^2 ≤
        Fintype.card G ^ 2 * (Fintype.card (A × B) *
          (Fintype.card (A × B) * (3*Fintype.card G))) :=
      Nat.mul_le_mul_left _ (hm.trans (Nat.mul_le_mul_left _ hs))
    _ = _ := by simp only [Fintype.card_prod]; ring

/-- At the additive norm-quotient size, freeness loses a half-power in q. -/
theorem quotient_scale_bound (h₂ : ∀ x : G, x+x=0) (R : G → A → B → Prop)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph R))
    (q : ℕ) (hG : Fintype.card G ≤ q^5)
    (hA : Fintype.card A ≤ q^3) (hB : Fintype.card B ≤ q^3) :
    (graph R).edgeFinset.card ^ 2 ≤ 3*q^27 := by
  calc
    _ ≤ 3 * Fintype.card G ^ 3 * Fintype.card A ^ 2 * Fintype.card B ^ 2 :=
      edge_square_bound h₂ R hfree
    _ ≤ 3 * (q^5)^3 * (q^3)^2 * (q^3)^2 := by gcongr
    _ = _ := by ring

/-- A critical-scale positive edge constant can only occur at bounded q. -/
theorem quotient_scale_budget (h₂ : ∀ x : G, x+x=0) (R : G → A → B → Prop)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph R))
    (q K : ℕ) (hq : 0 < q) (hG : Fintype.card G ≤ q^5)
    (hA : Fintype.card A ≤ q^3) (hB : Fintype.card B ≤ q^3)
    (he : q^14 ≤ K*(graph R).edgeFinset.card) : q ≤ 3*K^2 := by
  have h := quotient_scale_bound h₂ R hfree q hG hA hB
  have he2 := Nat.pow_le_pow_left he 2
  have hq27 : 0 < q^27 := pow_pos hq 27
  apply Nat.le_of_mul_le_mul_right (c := q^27) ?_ hq27
  calc
    q*q^27 = (q^14)^2 := by ring
    _ ≤ (K*(graph R).edgeFinset.card)^2 := he2
    _ = K^2 * (graph R).edgeFinset.card^2 := by ring
    _ ≤ K^2 * (3*q^27) := Nat.mul_le_mul_left _ h
    _ = (3*K^2)*q^27 := by ring


section ActualQuotient

variable {F : Type*} [Field F] [CharP F 2] [Fintype F]

abbrev QuotientPoint (K : Subfield F) := (F ⧸ K.toAddSubgroup) × F

local instance quotientFintype (K : Subfield F) : Fintype (F ⧸ K.toAddSubgroup) :=
  Fintype.ofFinite _

omit [Fintype F] in
lemma quotient_two (K : Subfield F) (x : QuotientPoint K) : x+x=0 := by
  apply Prod.ext
  · obtain ⟨a,ha⟩ := QuotientAddGroup.mk'_surjective K.toAddSubgroup x.1
    change x.1+x.1=0
    rw [← ha, ← map_add, CharTwo.add_self_eq_zero, map_zero]
  · exact CharTwo.add_self_eq_zero x.2

omit [CharP F 2] in
lemma quotient_card (K : Subfield F) [Fintype K]
    (hcard : Fintype.card F = Fintype.card K ^ 3) :
    Fintype.card (QuotientPoint K) = Fintype.card K ^ 5 := by
  have h : Fintype.card F =
      Fintype.card (F ⧸ K.toAddSubgroup) * Fintype.card K := by
    have h0 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K.toAddSubgroup
    change Nat.card F = Nat.card (F ⧸ K.toAddSubgroup) * Nat.card K at h0
    simpa only [Nat.card_eq_fintype_card] using h0
  have he : Fintype.card (F ⧸ K.toAddSubgroup) = Fintype.card K ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right (Fintype.card_pos (α := K))
    rw [← h,hcard]
    ring
  simp only [QuotientPoint, Fintype.card_prod, he, hcard]
  ring

/-- An actual additive quotient with cubic ambient field and multiplicative
weights inherits the obstruction, even for an arbitrary membership law. -/
theorem actual_quotient_bound (K : Subfield F) [Fintype K]
    (hcard : Fintype.card F = Fintype.card K ^ 3)
    (R : QuotientPoint K → Fˣ → Fˣ → Prop)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph R)) :
    (graph R).edgeFinset.card^2 ≤ 3*Fintype.card K ^ 27 := by
  have hw : Fintype.card Fˣ ≤ Fintype.card K ^ 3 := by
    rw [Fintype.card_units, hcard]
    exact Nat.sub_le _ _
  exact quotient_scale_bound (quotient_two K) R hfree _ (quotient_card K hcard).le hw hw

/-- The binary quadratic norm projection is a membership relation, not the
fiber of a single-valued function on the quotient. -/
def normRelation (K : Subfield F) (ν : F)
    (x : QuotientPoint K) (a b : Fˣ) : Prop :=
  ∃ t : F, QuotientAddGroup.mk' K.toAddSubgroup t = x.1 ∧
    t^2+t*x.2+ν*x.2^2=(a : F)*(b : F)

theorem norm_quotient_bound (K : Subfield F) [Fintype K]
    (hcard : Fintype.card F = Fintype.card K ^ 3) (ν : F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (normRelation K ν))) :
    (graph (normRelation K ν)).edgeFinset.card^2 ≤ 3*Fintype.card K ^ 27 :=
  actual_quotient_bound K hcard _ hfree

theorem norm_quotient_budget (K : Subfield F) [Fintype K]
    (hcard : Fintype.card F = Fintype.card K ^ 3) (ν : F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (normRelation K ν)))
    (C : ℕ) (he : Fintype.card K ^ 14 ≤ C*(graph (normRelation K ν)).edgeFinset.card) :
    Fintype.card K ≤ 3*C^2 := by
  have hw : Fintype.card Fˣ ≤ Fintype.card K ^ 3 := by
    rw [Fintype.card_units, hcard]
    exact Nat.sub_le _ _
  exact quotient_scale_budget (quotient_two K) _ hfree _ C Fintype.card_pos
    (quotient_card K hcard).le hw hw he

end ActualQuotient

end Erdos714BinaryQuotientLaw

#print axioms Erdos714BinaryQuotientLaw.not_free_of_plane
#print axioms Erdos714BinaryQuotientLaw.cayley_card_bound
#print axioms Erdos714BinaryQuotientLaw.edge_square_bound
#print axioms Erdos714BinaryQuotientLaw.quotient_scale_bound
#print axioms Erdos714BinaryQuotientLaw.quotient_scale_budget

#print axioms Erdos714BinaryQuotientLaw.quotient_two
#print axioms Erdos714BinaryQuotientLaw.quotient_card
#print axioms Erdos714BinaryQuotientLaw.actual_quotient_bound
#print axioms Erdos714BinaryQuotientLaw.norm_quotient_budget
