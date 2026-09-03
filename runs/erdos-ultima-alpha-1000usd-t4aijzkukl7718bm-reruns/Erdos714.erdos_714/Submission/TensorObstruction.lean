import FormalConjecturesUtil

/-!
A direct tensor-product obstruction for the remaining construction problem.
These results do not prove or disprove Erdős Problem 714.
-/

open SimpleGraph

namespace Erdos714Tensor

variable {A B C D : Type*}

/-- The bipartite graph associated to an arbitrary relation. -/
def incidence (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj x y := match x, y with
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | _, _ => False
  symm := by intro x y h; cases x <;> cases y <;> exact h
  loopless := by intro x; cases x <;> exact not_false

/-- Tensoring relations retains the ordinary bipartite component. -/
def tensor (R : A → B → Prop) (S : C → D → Prop) :
    SimpleGraph ((A × C) ⊕ (B × D)) :=
  incidence fun x y => R x.1 y.1 ∧ S x.2 y.2

/-- Oppositely oriented stars in the factors create a complete bipartite graph. -/
def copy_of_stars (R : A → B → Prop) (S : C → D → Prop)
    {s t : ℕ} (a : A) (d : D) (f : Fin s ↪ C) (g : Fin t ↪ B)
    (hf : ∀ i, S (f i) d) (hg : ∀ j, R a (g j)) :
    (completeBipartiteGraph (Fin s) (Fin t)).Copy (tensor R S) where
  toHom := {
    toFun := Sum.elim (fun i => Sum.inl (a, f i)) (fun j => Sum.inr (g j, d))
    map_rel' := by
      intro x y h
      cases x with
      | inl i =>
        cases y with
        | inl j => simpa using h
        | inr j => exact ⟨hg j, hf i⟩
      | inr i =>
        cases y with
        | inl j => exact ⟨hg i, hf j⟩
        | inr j => simpa using h
  }
  injective' := by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        exact congrArg Sum.inl (f.injective (congrArg Prod.snd (Sum.inl.inj h)))
      | inr j => cases h
    | inr i =>
      cases y with
      | inl j => cases h
      | inr j =>
        exact congrArg Sum.inr (g.injective (congrArg Prod.fst (Sum.inr.inj h)))

/-- In particular, large degrees on both sides prevent a free tensor square. -/
theorem square_not_free (R : A → B → Prop) {r : ℕ}
    (a : A) (b : B) (f : Fin r ↪ A) (g : Fin r ↪ B)
    (hf : ∀ i, R (f i) b) (hg : ∀ j, R a (g j)) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (tensor R R) := by
  intro h
  exact h ⟨copy_of_stars R R a b f g hf hg⟩


section BicliqueCovers

variable {V I : Type*}

/-- A complete bipartite block in a free graph has a small side. -/
lemma rectangle_small (G : SimpleGraph V) {r : ℕ}
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free G)
    (L R : Finset V) (hrect : ∀ v ∈ L, ∀ w ∈ R, G.Adj v w) :
    L.card < r ∨ R.card < r := by
  classical
  by_contra! h
  obtain ⟨L', hL', hcL⟩ := Finset.exists_subset_card_eq h.1
  obtain ⟨R', hR', hcR⟩ := Finset.exists_subset_card_eq h.2
  exact hfree ⟨Copy.completeBipartiteGraph L' R' (by simpa using hcL) (by simpa using hcR)
    (fun v hv w hw => hrect v (hL' hv) w (hR' hw))⟩

lemma product_le_small_side {a b r : ℕ} (h : a < r ∨ b < r) :
    a * b ≤ (r - 1) * (a + b) := by
  rcases h with h | h
  · have ha : a ≤ r - 1 := by omega
    exact (Nat.mul_le_mul_right b ha).trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  · have hb : b ≤ r - 1 := by omega
    calc
      a * b ≤ a * (r - 1) := Nat.mul_le_mul_left a hb
      _ = (r - 1) * a := Nat.mul_comm _ _
      _ ≤ (r - 1) * (a + b) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

open Classical in
/-- A biclique cover bounds the edges of a free graph by its total vertex incidences. -/
theorem edge_bound_of_biclique_cover [Fintype V] [Fintype I]
    (G : SimpleGraph V) {r : ℕ}
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free G)
    (L R : I → Finset V)
    (hrect : ∀ i, ∀ v ∈ L i, ∀ w ∈ R i, G.Adj v w)
    (hcover : ∀ v w, G.Adj v w → ∃ i,
      (v ∈ L i ∧ w ∈ R i) ∨ (w ∈ L i ∧ v ∈ R i)) :
    G.edgeFinset.card ≤ (r - 1) * ∑ i, ((L i).card + (R i).card) := by
  classical
  let T (i : I) : Finset (Sym2 V) := ((L i) ×ˢ (R i)).image (fun p => s(p.1,p.2))
  have hedge : G.edgeFinset ⊆ Finset.univ.biUnion T := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf v w =>
      have hvw : G.Adj v w := by simpa using he
      obtain ⟨i, hi⟩ := hcover v w hvw
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rcases hi with h | h
      · exact Finset.mem_image.mpr ⟨(v,w), Finset.mem_product.mpr h, rfl⟩
      · exact Finset.mem_image.mpr ⟨(w,v), Finset.mem_product.mpr h, Sym2.eq_swap⟩
  calc
    G.edgeFinset.card ≤ (Finset.univ.biUnion T).card := Finset.card_le_card hedge
    _ ≤ ∑ i, (T i).card := Finset.card_biUnion_le
    _ ≤ ∑ i, ((L i).card * (R i).card) := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.card_image_le).trans_eq (Finset.card_product _ _)
    _ ≤ ∑ i, (r - 1) * ((L i).card + (R i).card) := by
      apply Finset.sum_le_sum
      intro i _
      exact product_le_small_side (rectangle_small G hfree (L i) (R i) (hrect i))
    _ = (r - 1) * ∑ i, ((L i).card + (R i).card) := by rw [Finset.mul_sum]

end BicliqueCovers

section RestrictedProducts

variable {X Y : Type*}

/-- A tensor relation pulled back to selected (or repeatedly indexed) vertices. -/
def pullTensor (R : A → B → Prop) (S : C → D → Prop)
    (f : X → A × C) (g : Y → B × D) : SimpleGraph (X ⊕ Y) :=
  incidence fun x y => R (f x).1 (g y).1 ∧ S (f x).2 (g y).2

open Classical in
lemma filter_mass [Fintype X] [Fintype A] [Fintype D]
    (f : X → A × C) (S : C → D → Prop) :
    (∑ p : A × D, (Finset.univ.filter
      (fun x : X => (f x).1 = p.1 ∧ S (f x).2 p.2)).card) =
    ∑ x : X, (Finset.univ.filter (fun d : D => S (f x).2 d)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.sum_prod_type]
  simp [ite_and, eq_comm]

open Classical in
/-- Vertex restriction cannot evade the biclique-block counting bound. -/
theorem pullTensor_edge_bound [Fintype X] [Fintype Y] [Fintype A] [Fintype D]
    (R : A → B → Prop) (S : C → D → Prop)
    (f : X → A × C) (g : Y → B × D) {r dR dS : ℕ}
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (pullTensor R S f g))
    (hR : ∀ b, (Finset.univ.filter (fun a => R a b)).card ≤ dR)
    (hS : ∀ c, (Finset.univ.filter (fun d => S c d)).card ≤ dS) :
    (pullTensor R S f g).edgeFinset.card ≤
      (r - 1) * (dS * Fintype.card X + dR * Fintype.card Y) := by
  classical
  let L (p : A × D) : Finset (X ⊕ Y) :=
    (Finset.univ.filter (fun x : X => (f x).1 = p.1 ∧ S (f x).2 p.2)).map
      (Function.Embedding.inl : X ↪ X ⊕ Y)
  let T (p : A × D) : Finset (X ⊕ Y) :=
    (Finset.univ.filter (fun y : Y => (g y).2 = p.2 ∧ R p.1 (g y).1)).map
      (Function.Embedding.inr : Y ↪ X ⊕ Y)
  have hrect : ∀ p, ∀ v ∈ L p, ∀ w ∈ T p, (pullTensor R S f g).Adj v w := by
    intro p v hv w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    change R (f x).1 (g y).1 ∧ S (f x).2 (g y).2
    rw [hx'.1, hy'.1]
    exact ⟨hy'.2, hx'.2⟩
  have hcover : ∀ v w, (pullTensor R S f g).Adj v w → ∃ p,
      (v ∈ L p ∧ w ∈ T p) ∨ (w ∈ L p ∧ v ∈ T p) := by
    intro v w h
    cases v with
    | inl x =>
      cases w with
      | inl x' => exact False.elim h
      | inr y =>
        change R (f x).1 (g y).1 ∧ S (f x).2 (g y).2 at h
        refine ⟨((f x).1, (g y).2), Or.inl ?_⟩
        simp [L, T, h]
    | inr y =>
      cases w with
      | inl x =>
        change R (f x).1 (g y).1 ∧ S (f x).2 (g y).2 at h
        refine ⟨((f x).1, (g y).2), Or.inr ?_⟩
        simp [L, T, h]
      | inr y' => exact False.elim h
  have hLmass : ∑ p, (L p).card =
      ∑ x : X, (Finset.univ.filter (fun d => S (f x).2 d)).card := by
    simp only [L, Finset.card_map]
    exact filter_mass f S
  have hTmass : ∑ p, (T p).card =
      ∑ y : Y, (Finset.univ.filter (fun a => R a (g y).1)).card := by
    simp only [T, Finset.card_map]
    have h := filter_mass (fun y : Y => ((g y).2, (g y).1)) (fun b a => R a b)
    rw [Fintype.sum_prod_type, Finset.sum_comm] at h
    simpa only [Fintype.sum_prod_type] using h
  have hmass : ∑ p, ((L p).card + (T p).card) ≤
      dS * Fintype.card X + dR * Fintype.card Y := by
    rw [Finset.sum_add_distrib, hLmass, hTmass]
    apply Nat.add_le_add
    · calc
        _ ≤ ∑ _ : X, dS := Finset.sum_le_sum (fun x _ => hS (f x).2)
        _ = _ := by simp [Nat.mul_comm]
    · calc
        _ ≤ ∑ _ : Y, dR := Finset.sum_le_sum (fun y _ => hR (g y).1)
        _ = _ := by simp [Nat.mul_comm]
  exact (edge_bound_of_biclique_cover _ hfree L T hrect hcover).trans
    (Nat.mul_le_mul_left (r - 1) hmass)

open Classical in
/-- A uniform factor-degree bound gives a linear edge bound in the retained vertices. -/
theorem pullTensor_edge_bound_uniform [Fintype X] [Fintype Y] [Fintype A] [Fintype D]
    (R : A → B → Prop) (S : C → D → Prop)
    (f : X → A × C) (g : Y → B × D) {r d : ℕ}
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (pullTensor R S f g))
    (hR : ∀ b, (Finset.univ.filter (fun a => R a b)).card ≤ d)
    (hS : ∀ c, (Finset.univ.filter (fun a => S c a)).card ≤ d) :
    (pullTensor R S f g).edgeFinset.card ≤
      (r - 1) * d * (Fintype.card X + Fintype.card Y) := by
  simpa only [← Nat.mul_add, Nat.mul_assoc] using pullTensor_edge_bound R S f g hfree hR hS

/-- Coordinatewise powers of a bipartite relation. -/
def relPower (R : A → B → Prop) (k : ℕ) (x : Fin k → A) (y : Fin k → B) : Prop :=
  ∀ i, R (x i) (y i)

open Classical in
lemma relPower_right_degree [Fintype B] (R : A → B → Prop) (k : ℕ) (x : Fin k → A) :
    (Finset.univ.filter (fun y => relPower R k x y)).card =
      ∏ i, (Finset.univ.filter (fun b => R (x i) b)).card := by
  classical
  have he : Finset.univ.filter (fun y => relPower R k x y) =
      Fintype.piFinset (fun i => Finset.univ.filter (fun b => R (x i) b)) := by
    ext y
    simp [relPower]
  rw [he, Fintype.card_piFinset]

open Classical in
lemma relPower_left_degree [Fintype A] (R : A → B → Prop) (k : ℕ) (y : Fin k → B) :
    (Finset.univ.filter (fun x => relPower R k x y)).card =
      ∏ i, (Finset.univ.filter (fun a => R a (y i))).card :=
  relPower_right_degree (fun b a => R a b) k y

open Classical in
/-- Every vertex-restricted even tensor power satisfies the corresponding degree bound. -/
theorem even_power_edge_bound [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (R : A → B → Prop) (k : ℕ)
    (f : X → (Fin k → A) × (Fin k → A))
    (g : Y → (Fin k → B) × (Fin k → B)) {r d : ℕ}
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free
      (pullTensor (relPower R k) (relPower R k) f g))
    (hR : ∀ b, (Finset.univ.filter (fun a => R a b)).card ≤ d)
    (hS : ∀ a, (Finset.univ.filter (fun b => R a b)).card ≤ d) :
    (pullTensor (relPower R k) (relPower R k) f g).edgeFinset.card ≤
      (r - 1) * d^k * (Fintype.card X + Fintype.card Y) := by
  apply pullTensor_edge_bound_uniform _ _ f g hfree
  · intro y
    rw [relPower_left_degree]
    calc
      _ ≤ ∏ _ : Fin k, d := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hR (y i))
      _ = d^k := by simp
  · intro x
    rw [relPower_right_degree]
    calc
      _ ≤ ∏ _ : Fin k, d := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hS (x i))
      _ = d^k := by simp

/-- The fourth-case target forces an explicit size budget under the tensor edge bound. -/
lemma fourth_case_size_budget {N e d k C : ℕ} (hN : 0 < N)
    (he : e ≤ 3 * d^k * N) (htarget : N^7 ≤ C * e^4) :
    N^3 ≤ 81 * C * d^(4*k) := by
  have hp := Nat.pow_le_pow_left he 4
  have hmul : N^4 * N^3 ≤ N^4 * (81 * C * d^(4*k)) := by
    calc
      N^4 * N^3 = N^7 := by ring
      _ ≤ C * e^4 := htarget
      _ ≤ C * (3 * d^k * N)^4 := Nat.mul_le_mul_left C hp
      _ = N^4 * (81 * C * d^(4*k)) := by
        rw [Nat.mul_comm 4 k, pow_mul]
        ring
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos hN)

/-- With a fixed positive fraction of the ambient vertices, only finitely many powers
can satisfy both the free-tensor bound and the desired fourth-case edge scale. -/
theorem dense_selection_power_bound {N e q d k C C₀ : ℕ} (hq : 2 ≤ q) (hd : d ≤ q)
    (hN : 0 < N) (hsize : q^(2*k) ≤ C₀ * N)
    (he : e ≤ 3 * d^k * N) (htarget : N^7 ≤ C * e^4) :
    k < 81 * C * C₀^3 := by
  have hbudget := fourth_case_size_budget hN he htarget
  have h6 : q^(6*k) ≤ C₀^3 * N^3 := by
    have h := Nat.pow_le_pow_left hsize 3
    rw [mul_pow, ← pow_mul] at h
    convert h using 1 <;> congr 1 <;> omega
  have hupper : q^(6*k) ≤ (81 * C * C₀^3) * q^(4*k) := by
    calc
      q^(6*k) ≤ C₀^3 * N^3 := h6
      _ ≤ C₀^3 * (81 * C * d^(4*k)) := Nat.mul_le_mul_left _ hbudget
      _ ≤ C₀^3 * (81 * C * q^(4*k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _))
      _ = (81 * C * C₀^3) * q^(4*k) := by ring
  have hsmall : q^(2*k) ≤ 81 * C * C₀^3 := by
    apply Nat.le_of_mul_le_mul_left (c := q^(4*k)) ?_ (Nat.pow_pos (by omega))
    convert hupper using 1
    · rw [← pow_add]
      congr 1
      omega
    · exact Nat.mul_comm _ _
  have hkg : k < q^(2*k) := by
    apply (show k < 2^k from Nat.lt_two_pow_self).trans_le
    exact (Nat.pow_le_pow_left hq k).trans
      (Nat.pow_le_pow_right (by omega) (by omega : k ≤ 2*k))
  exact hkg.trans_le hsmall

end RestrictedProducts

end Erdos714Tensor

#print axioms Erdos714Tensor.square_not_free
#print axioms Erdos714Tensor.edge_bound_of_biclique_cover
#print axioms Erdos714Tensor.pullTensor_edge_bound
#print axioms Erdos714Tensor.even_power_edge_bound
#print axioms Erdos714Tensor.fourth_case_size_budget
#print axioms Erdos714Tensor.dense_selection_power_bound
