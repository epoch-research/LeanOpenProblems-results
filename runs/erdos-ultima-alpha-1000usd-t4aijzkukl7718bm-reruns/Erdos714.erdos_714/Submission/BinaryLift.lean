import FormalConjecturesUtil

/-!
Obstructions to binary Cayley and weighted constructions for Erdős Problem 714.
This file does not prove or disprove the conjecture.
-/

open SimpleGraph
open scoped CharTwo

namespace Erdos714BinaryLift

variable {G : Type*} [Ring G] [CharP G 2]

/-- The bipartite Cayley graph with connection set `S`. -/
def cayley (S : Set G) : SimpleGraph (Bool × G) where
  Adj x y := x.1 ≠ y.1 ∧ x.2 + y.2 ∈ S
  symm := by
    intro x y h
    exact ⟨h.1.symm, by simpa only [add_comm] using h.2⟩
  loopless := by intro x h; exact h.1 rfl

/-- The four elements of a binary plane through zero. -/
def plane (u v : G) : Fin 4 → G := ![0, u, v, u + v]

lemma plane_injective {u v : G} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Function.Injective (plane u v) := by
  have huv0 : u + v ≠ 0 := fun h => huv (CharTwo.add_eq_zero.mp h)
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

lemma plane_closed (u v : G) (i j : Fin 4) :
    ∃ k, plane u v i + plane u v j = plane u v k := by
  fin_cases i <;> fin_cases j <;>
    simp [Fin.exists_fin_succ, plane, add_assoc, add_left_comm, add_comm]

/-- An affine binary plane in the connection set gives a `K_{4,4}`. -/
theorem not_free_of_plane (S : Set G) {p u v : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hS : ∀ i, p + plane u v i ∈ S) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (cayley S) := by
  intro hfree
  apply hfree
  let L (i : Fin 4) : Bool × G := (false, plane u v i)
  let R (i : Fin 4) : Bool × G := (true, p + plane u v i)
  have hL : Function.Injective L := by
    intro i j h
    exact plane_injective hu hv huv (congrArg Prod.snd h)
  have hR : Function.Injective R := by
    intro i j h
    exact plane_injective hu hv huv (add_left_cancel (congrArg Prod.snd h))
  have hE : ∀ i j, (cayley S).Adj (L i) (R j) := by
    intro i j
    refine ⟨Bool.false_ne_true, ?_⟩
    obtain ⟨k, hk⟩ := plane_closed u v i j
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

variable {A B : Type*} [Ring A] [CharP A 2] [Ring B] [CharP B 2]

/-- Adjacency is `a+b=f(x+y)` between opposite sides. -/
def additiveLift (f : A → B) : SimpleGraph (Bool × (A × B)) :=
  cayley {z | z.2 = f z.1}

/-- Every sufficiently unbalanced binary additive lift contains `K_{4,4}`. -/
theorem additiveLift_not_free [Fintype A] [Fintype B] [Nontrivial A]
    (f : A → B) (hcard : Fintype.card B * 2 < Fintype.card A) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (additiveLift f) := by
  classical
  obtain ⟨u, hu⟩ := exists_ne (0 : A)
  obtain ⟨b, hb⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (fun x : A => f (x + u) + f x) hcard
  let T : Finset A := Finset.univ.filter (fun x => f (x + u) + f x = b)
  have hT : 2 < T.card := hb
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    ((Finset.card_le_two (a := x) (b := x + u)).trans_lt hT)
  have hyn : y ≠ x ∧ y ≠ x + u := by simpa using hy'
  have hyx := hyn.1
  have hyxu := hyn.2
  have hxy : f (x + u) + f x = f (y + u) + f y := by
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  have hfinal : f (x + u) + f x + f y = f (y + u) := by
    rw [hxy]
    simp [add_assoc]
  let p : A × B := (x, f x)
  let U : A × B := (u, f (x + u) + f x)
  let V : A × B := (x + y, f y + f x)
  apply not_free_of_plane (p := p) (u := U) (v := V)
  · intro h
    exact hu (congrArg Prod.fst h)
  · intro h
    apply hyx
    exact (CharTwo.add_eq_zero.mp (congrArg Prod.fst h)).symm
  · intro h
    apply hyxu
    have h' : u = x + y := congrArg Prod.fst h
    rw [h']
    simp [add_assoc]
  · intro i
    fin_cases i
    · simp [p, plane]
    · simp [p, U, plane, add_assoc, add_left_comm, add_comm]
    · simp [p, V, plane, add_assoc, add_left_comm, add_comm]
    · change (p + (U + V)).2 = f (p + (U + V)).1
      simpa [p, U, V, add_assoc, add_left_comm, add_comm] using hfinal

/-- The proposed lift has exactly the desired degree; freeness is the obstruction. -/
def liftNeighborEquiv (f : A → B) (v : Bool × (A × B)) :
    (additiveLift f).neighborSet v ≃ A where
  toFun w := w.val.2.1
  invFun x := ⟨(!v.1, (x, f (v.2.1 + x) + v.2.2)), by
    constructor
    · cases hv : v.1 <;> simp [hv]
    · change v.2.2 + (f (v.2.1 + x) + v.2.2) = f (v.2.1 + x)
      simp [add_comm, add_left_comm]⟩
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · change (!v.1) = w.val.1
      have h := w.property.1
      cases hv : v.1 <;> cases hw : w.val.1 <;> simp_all
    · apply Prod.ext
      · rfl
      · have h : v.2.2 + w.val.2.2 = f (v.2.1 + w.val.2.1) := w.property.2
        change f (v.2.1 + w.val.2.1) + v.2.2 = w.val.2.2
        rw [← h]
        simp [add_comm, add_left_comm]
  right_inv _ := rfl

open Classical in
theorem additiveLift_degree [Fintype A] [Fintype B] (f : A → B)
    (v : Bool × (A × B)) :
    (additiveLift f).degree v = Fintype.card A := by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (liftNeighborEquiv f v)

open Classical in
theorem additiveLift_edges [Fintype A] [Fintype B] (f : A → B) :
    (additiveLift f).edgeFinset.card = Fintype.card A ^ 2 * Fintype.card B := by
  have h := (additiveLift f).sum_degrees_eq_twice_card_edges
  simp only [additiveLift_degree, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool, smul_eq_mul] at h
  nlinarith

/-- No function on a binary three-dimensional field space rescues the additive lift. -/
theorem cubic_lift_not_free {F : Type*} [Field F] [CharP F 2] [Fintype F]
    (f : (F × F × F) → F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (additiveLift f) := by
  apply additiveLift_not_free
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  simp only [Fintype.card_prod]
  nlinarith

/-- Pair-sum counting forces an affine binary plane in a large connection set. -/
theorem exists_plane_of_card [Fintype G] (S : Finset G)
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
  · exact fun h => hab (CharTwo.add_eq_zero.mp h)
  · exact fun h => hca (CharTwo.add_eq_zero.mp h).symm
  · exact fun h => hcb (add_left_cancel h).symm
  · intro i
    fin_cases i
    · simpa [plane] using ha
    · simpa [plane, add_assoc, add_left_comm, add_comm] using hb
    · simpa [plane, add_assoc, add_left_comm, add_comm] using hc
    · have hh : x.1 + x.2 + y.1 = y.2 := by
        rw [heq]
        simp [add_assoc, add_left_comm, add_comm]
      simpa [plane, add_assoc, add_left_comm, add_comm, ← hh] using hd

/-- A binary Cayley graph free of `K_{4,4}` must have a Sidon-sized connection set. -/
theorem cayley_card_bound [Fintype G] (S : Finset G)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (cayley (S : Set G))) :
    S.card * (S.card - 1) ≤ 2 * Fintype.card G := by
  by_contra h
  obtain ⟨p, u, v, hu, hv, huv, hS⟩ := exists_plane_of_card S (by omega)
  exact not_free_of_plane _ hu hv huv hS hfree

section Multiplicative

variable {F : Type*} [Field F]

/-- The multiplicative-weight version; the point group still has characteristic two. -/
def multiplicativeLift (f : G → F) : SimpleGraph (Bool × (G × Fˣ)) where
  Adj x y := x.1 ≠ y.1 ∧ f (x.2.1 + y.2.1) = (x.2.2 : F) * (y.2.2 : F)
  symm := by
    intro x y h
    exact ⟨h.1.symm, by simpa only [add_comm, mul_comm] using h.2⟩
  loopless := by intro x h; exact h.1 rfl

/-- A nonzero fiber's Cayley graph embeds using constant weights on each side. -/
def fiberCopy (f : G → F) (t : Fˣ) :
    Copy (cayley {x | f x = (t : F)}) (multiplicativeLift f) where
  toHom := {
    toFun := fun x => (x.1, x.2, if x.1 then t else 1)
    map_rel' := by
      intro x y h
      refine ⟨h.1, ?_⟩
      change f (x.2 + y.2) = _
      have he : f (x.2 + y.2) = (t : F) := h.2
      rw [he]
      have hn := h.1
      cases hx : x.1 <;> cases hy : y.1 <;> simp_all }
  injective' := by
    intro x y h
    have h1 : x.1 = y.1 := congrArg (fun z : Bool × (G × Fˣ) => z.1) h
    have h2 : x.2 = y.2 := congrArg (fun z : Bool × (G × Fˣ) => z.2.1) h
    exact Prod.ext h1 h2

open Classical in
/-- Every nonzero fiber of a free multiplicative lift satisfies the binary Sidon bound. -/
theorem multiplicative_fiber_bound [Fintype G] (f : G → F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (multiplicativeLift f))
    (t : F) (ht : t ≠ 0) :
    let m := (Finset.univ.filter (fun x => f x = t)).card
    m * (m - 1) ≤ 2 * Fintype.card G := by
  apply cayley_card_bound
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (cayley {x | f x = t}) := by
    rintro ⟨g⟩
    exact hfree ⟨(fiberCopy f (Units.mk0 t ht)).comp g⟩
  simpa only [Finset.coe_filter, Finset.coe_univ, Set.setOf_mem_eq, Set.mem_univ, Finset.mem_univ,
    true_and] using hf

/-- The neighbors are parametrized by the nonzero support of `f`. -/
def multiplicativeNeighborEquiv (f : G → F) (v : Bool × (G × Fˣ)) :
    (multiplicativeLift f).neighborSet v ≃ {z : G // f z ≠ 0} where
  toFun w := ⟨v.2.1 + w.val.2.1, by
    rw [w.property.2]
    exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)⟩
  invFun z := ⟨(!v.1, v.2.1 + z.val, (Units.mk0 (f z.val) z.property) / v.2.2), by
    refine ⟨?_, ?_⟩
    · cases hv : v.1 <;> simp [hv]
    · dsimp only
      rw [Units.val_div_eq_div_val]
      simp [← add_assoc, mul_div_cancel₀, Units.ne_zero]⟩
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · change (!v.1) = w.val.1
      have h := w.property.1
      cases hv : v.1 <;> cases hw : w.val.1 <;> simp_all
    · apply Prod.ext
      · change v.2.1 + (v.2.1 + w.val.2.1) = w.val.2.1
        simp [← add_assoc]
      · apply Units.ext
        dsimp only
        rw [Units.val_div_eq_div_val]
        change f (v.2.1 + w.val.2.1) / (v.2.2 : F) = (w.val.2.2 : F)
        rw [w.property.2]
        exact mul_div_cancel_left₀ _ (Units.ne_zero _)
  right_inv z := by
    apply Subtype.ext
    change v.2.1 + (v.2.1 + z.val) = z.val
    simp [← add_assoc]

open Classical in
theorem multiplicative_degree [Fintype G] [Fintype F] (f : G → F)
    (v : Bool × (G × Fˣ)) :
    (multiplicativeLift f).degree v =
      (Finset.univ.filter (fun x => f x ≠ 0)).card := by
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (multiplicativeNeighborEquiv f v)]
  exact Fintype.card_subtype _

open Classical in
theorem multiplicative_edges [Fintype G] [Fintype F] (f : G → F) :
    (multiplicativeLift f).edgeFinset.card = Fintype.card G * (Fintype.card F - 1) *
      (Finset.univ.filter (fun x => f x ≠ 0)).card := by
  have h := (multiplicativeLift f).sum_degrees_eq_twice_card_edges
  simp only [multiplicative_degree, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_units, smul_eq_mul] at h
  nlinarith

open Classical in
/-- A support bound for every free binary multiplicative lift, allowing arbitrary zero fibers. -/
theorem multiplicative_support_bound [Fintype G] [Fintype F] (f : G → F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (multiplicativeLift f)) :
    let M := (Finset.univ.filter (fun x => f x ≠ 0)).card
    M ^ 2 ≤ (Fintype.card F - 1) * M +
      2 * (Fintype.card F - 1) ^ 2 * Fintype.card G := by
  let T := (Finset.univ : Finset F).erase 0
  let m (t : F) := (Finset.univ.filter (fun x => f x = t)).card
  let M := (Finset.univ.filter (fun x => f x ≠ 0)).card
  have hsum : ∑ t ∈ T, m t = M := by
    simpa [T, m, M] using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset G) T f
  have hpoint : ∀ t ∈ T, m t ^ 2 ≤ m t + 2 * Fintype.card G := by
    intro t ht
    have h := multiplicative_fiber_bound f hfree t (Finset.mem_erase.mp ht).1
    change m t * (m t - 1) ≤ 2 * Fintype.card G at h
    by_cases hm : m t = 0
    · simp [hm]
    · have hs : m t - 1 + 1 = m t := Nat.sub_add_cancel (by omega)
      nlinarith
  have hsum2 : ∑ t ∈ T, m t ^ 2 ≤ M + T.card * (2 * Fintype.card G) := by
    calc
      _ ≤ ∑ t ∈ T, (m t + 2 * Fintype.card G) := Finset.sum_le_sum hpoint
      _ = _ := by rw [Finset.sum_add_distrib, hsum]; simp
  have hc : M ^ 2 ≤ T.card * ∑ t ∈ T, m t ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) T (fun _ => 1) m
    simpa only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one, hsum] using h
  have hcard : T.card = Fintype.card F - 1 := by simp [T]
  calc
    M ^ 2 ≤ T.card * (M + T.card * (2 * Fintype.card G)) :=
      hc.trans (Nat.mul_le_mul_left _ hsum2)
    _ = _ := by rw [hcard]; ring

open Classical in
/-- The entire multiplicative-lift model has a uniform edge bound in characteristic two. -/
theorem multiplicative_edge_power_bound [Fintype G] [Fintype F] (f : G → F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (multiplicativeLift f)) :
    (multiplicativeLift f).edgeFinset.card ^ 2 ≤
      3 * Fintype.card F ^ 4 * Fintype.card G ^ 3 := by
  let q := Fintype.card F
  let N := Fintype.card G
  let M := (Finset.univ.filter (fun x => f x ≠ 0)).card
  have hM : M ≤ N := Finset.card_filter_le _ _
  have hq : 1 ≤ q := Fintype.card_pos
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hsup := multiplicative_support_bound f hfree
  change M ^ 2 ≤ (q - 1) * M + 2 * (q - 1) ^ 2 * N at hsup
  have hsup' : M ^ 2 ≤ 3 * q ^ 2 * N := by
    calc
      M ^ 2 ≤ (q - 1) * M + 2 * (q - 1) ^ 2 * N := hsup
      _ ≤ q * N + 2 * q ^ 2 * N := by gcongr <;> exact Nat.sub_le _ _
      _ ≤ q ^ 2 * N + 2 * q ^ 2 * N := by gcongr
      _ = _ := by ring
  rw [multiplicative_edges]
  change (N * (q - 1) * M) ^ 2 ≤ 3 * q ^ 4 * N ^ 3
  calc
    (N * (q - 1) * M) ^ 2 = N ^ 2 * (q - 1) ^ 2 * M ^ 2 := by ring
    _ ≤ N ^ 2 * q ^ 2 * (3 * q ^ 2 * N) := by gcongr <;> exact Nat.sub_le _ _
    _ = _ := by ring

open Classical in
/-- With q^3 point parameters, the bound is below the required asymptotic edge order. -/
theorem multiplicative_cubic_edge_bound [Fintype G] [Fintype F] (f : G → F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (multiplicativeLift f))
    (hcard : Fintype.card G = Fintype.card F ^ 3) :
    (multiplicativeLift f).edgeFinset.card ^ 2 ≤ 3 * Fintype.card F ^ 13 := by
  have h := multiplicative_edge_power_bound f hfree
  rw [hcard] at h
  convert h using 1 <;> ring

/-- In dimension three, every map vanishing only at zero fails, not just the norm. -/
theorem multiplicative_cubic_not_free [Fintype G] [Fintype F]
    (f : G → F) (hf : ∀ x, f x = 0 ↔ x = 0)
    (hcard : Fintype.card G = Fintype.card F ^ 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (multiplicativeLift f) := by
  classical
  intro hfree
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hmap : ∀ x ∈ (Finset.univ : Finset G).erase 0,
      f x ∈ (Finset.univ : Finset F).erase 0 := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx ⊢
    exact fun he => hx ((hf x).mp he)
  have hc : ((Finset.univ : Finset F).erase 0).card * q ^ 2 <
      ((Finset.univ : Finset G).erase 0).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
    change (q - 1) * q ^ 2 < q ^ 3 - 1
    have hpos : 1 ≤ q := by omega
    have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hpos
    have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hpos
    have hs3 : q ^ 3 - 1 + 1 = q ^ 3 := Nat.sub_add_cancel hq3
    have he := congrArg (fun z : ℕ => z * q ^ 2) hsub
    nlinarith
  obtain ⟨t, ht, hm⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap hc
  have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
  let m := (Finset.univ.filter (fun x => f x = t)).card
  have hqm : q ^ 2 < m := hm.trans_le (Finset.card_le_card (by
    intro x hx
    obtain ⟨hx, he⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩))
  have hbound := multiplicative_fiber_bound f hfree t ht0
  change m * (m - 1) ≤ 2 * Fintype.card G at hbound
  rw [hcard] at hbound
  change m * (m - 1) ≤ 2 * q ^ 3 at hbound
  have hmpos : 1 ≤ m := by omega
  have hsub : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
  have hmprod : (q ^ 2 + 1) * q ^ 2 ≤ m * (m - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hqpow : 2 * q ^ 3 < (q ^ 2 + 1) * q ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (q ^ 2) (show 2 * q ≤ q ^ 2 by nlinarith)]
  omega

end Multiplicative

#print axioms multiplicative_cubic_edge_bound
#print axioms multiplicative_edges
#print axioms multiplicative_support_bound
#print axioms multiplicative_fiber_bound
#print axioms multiplicative_cubic_not_free
#print axioms exists_plane_of_card
#print axioms cayley_card_bound
#print axioms additiveLift_not_free
#print axioms additiveLift_edges
#print axioms cubic_lift_not_free

end Erdos714BinaryLift
