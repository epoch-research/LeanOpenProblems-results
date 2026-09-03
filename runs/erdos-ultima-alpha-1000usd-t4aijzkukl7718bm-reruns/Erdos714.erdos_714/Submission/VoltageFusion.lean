import Submission.BlowupThinning

/-!
Uniform fusion in a group-voltage cover has an exact biclique edge partition.
Every K44-free edge thinning loses density when both block sides grow.
This does not concern arbitrary unions of unrelated voltage tables.
-/

noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000

namespace Erdos714FusionBounds
open Erdos714Packing

/-- An unbalanced bound, normalized by the number of edges of the full block. -/
lemma relative_fourth {A B : Type*} [Fintype A] [Fintype B]
    (R : A → Finset B)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R))
    (L : ℕ) (hL : L ≤ Fintype.card A) (hL' : L ≤ Fintype.card B) :
    L * (∑ a, (R a).card)^4 ≤ 672 * (Fintype.card A * Fintype.card B)^4 := by
  have aux (m n e : ℕ) (hmn : m ≤ n)
      (he : e^4 ≤ 24*m^3*n^4+648*m^4) : m*e^4 ≤ 672*(m*n)^4 := by
    have hn : m ≤ n^4 := hmn.trans (Nat.le_self_pow (by decide) n)
    have hp : m^4 ≤ m^3*n^4 := by
      calc
        _ = m^3*m := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hn
    calc
      _ ≤ m*(24*m^3*n^4+648*m^4) := Nat.mul_le_mul_left _ he
      _ ≤ m*(24*m^3*n^4+648*(m^3*n^4)) := by gcongr
      _ = _ := by ring
  rcases le_total (Fintype.card A) (Fintype.card B) with h | h
  · exact (Nat.mul_le_mul_right _ hL).trans
      (aux _ _ _ h (Erdos714Unbalanced.fourth_power_bound R hf))
  · have hd : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (dual R)) := by
      rw [free_iff_common_card _ (by decide)]
      exact (common_card_dual_iff _ (by decide)).mp
        ((free_iff_common_card _ (by decide)).mp hf)
    have hb := aux _ _ _ h (Erdos714Unbalanced.fourth_power_bound (dual R) hd)
    rw [Erdos714Blowup.sum_dual_card] at hb
    exact (Nat.mul_le_mul_right _ hL').trans (by simpa only [mul_comm] using hb)

/-- A common homogeneous fourth-power estimate passes to sums without loss. -/
lemma sum_relative_fourth {I : Type*} [Fintype I] (e w : I → ℕ)
    (L C : ℕ) (hL : 0 < L) (h : ∀ i, L*(e i)^4 ≤ C*(w i)^4) :
    L*(∑ i, e i)^4 ≤ C*(∑ i, w i)^4 := by
  let a : ℝ := Real.sqrt (Real.sqrt ((C : ℝ) / L))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have ha4 : a^4 = (C : ℝ)/L := by
    calc
      a^4 = (a^2)^2 := by ring
      _ = (Real.sqrt ((C : ℝ)/L))^2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = _ := Real.sq_sqrt (by positivity)
  have hb (i : I) : (e i : ℝ) ≤ a*(w i : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4 ≠ 0)).mp
    rw [mul_pow, ha4, div_mul_eq_mul_div]
    apply (le_div_iff₀ hLr).mpr
    have hc : (L : ℝ)*(e i : ℝ)^4 ≤ (C : ℝ)*(w i : ℝ)^4 := by exact_mod_cast h i
    simpa only [div_mul_eq_mul_div, mul_comm] using hc
  have hs : (∑ i, (e i : ℝ)) ≤ a * ∑ i, (w i : ℝ) := by
    simpa only [mul_sum] using sum_le_sum (fun i _ => hb i)
  have hp : (L : ℝ)*(∑ i, (e i : ℝ))^4 ≤ (C : ℝ)*(∑ i, (w i : ℝ))^4 := by
    calc
      _ ≤ (L : ℝ)*(a*∑ i, (w i : ℝ))^4 := by gcongr
      _ = _ := by rw [mul_pow, ha4]; field_simp
  exact_mod_cast hp

#print axioms relative_fourth
#print axioms sum_relative_fourth
end Erdos714FusionBounds

namespace Erdos714VoltageFusion
open Erdos714Packing
variable {X Y Γ : Type*} [Group Γ]

/-- Fusion is inserted between the sheet label and the voltage; Γ need not commute. -/
def neighbors (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (p : X × Γ) : Finset (Y × Γ) :=
  ((S p.1).product T).map ⟨fun z => (z.1,p.2*z.2*v p.1 z.1), by
    rintro ⟨y,s⟩ ⟨z,t⟩ h
    have hy : y = z := congrArg Prod.fst h
    subst z
    have ht := congrArg Prod.snd h
    exact Prod.ext rfl (mul_left_cancel (mul_right_cancel ht))⟩

@[simp] lemma mem_neighbors (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (x : X) (g : Γ) (y : Y) (h : Γ) :
    (y,h) ∈ neighbors S T v (x,g) ↔ y ∈ S x ∧ ∃ s ∈ T, h = g*s*v x y := by
  simp only [neighbors, mem_map, Finset.product_eq_sprod, Finset.mem_product, Function.Embedding.coeFn_mk,
    Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨z,s,⟨hz,hs⟩,hy,he⟩
    subst z
    exact ⟨hz,s,hs,he.symm⟩
  · rintro ⟨hy,s,hs,he⟩
    exact ⟨y,s,⟨hy,hs⟩,rfl,he.symm⟩

def graph (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ) :
    SimpleGraph ((X × Γ) ⊕ (Y × Γ)) := incidence (neighbors S T v)

def rows (T : Finset Γ) (x : X) (t : Γ) : T ↪ X × Γ :=
  ⟨fun s => (x,t*s.val⁻¹), by
    intro s s' h
    apply Subtype.ext
    exact inv_injective (mul_left_cancel (congrArg Prod.snd h))⟩

def columns (S : X → Finset Y) (v : X → Y → Γ) (x : X) (t : Γ) :
    S x ↪ Y × Γ :=
  ⟨fun y => (y.val,t*v x y.val), fun _ _ h => Subtype.ext (congrArg Prod.fst h)⟩

/-- A genuine full block, with separately injective vertex maps. -/
theorem block_incidence (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (x : X) (t : Γ) (s : T) (y : S x) :
    columns S v x t y ∈ neighbors S T v (rows T x t s) := by
  apply (mem_neighbors S T v _ _ _ _).mpr
  refine ⟨y.property,s.val,s.property,?_⟩
  dsimp [rows,columns]
  group

/-- A large uniform fusion always creates a biclique, regardless of its voltage. -/
theorem not_free (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    {r : ℕ} (hr : 0 < r) (hT : r ≤ T.card) (x : X) (hS : r ≤ (S x).card) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph S T v) := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card (Fin r) ≤ Fintype.card T by simpa using hT)
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card (Fin r) ≤ Fintype.card (S x) by simpa using hS)
  intro hf
  exact (free_iff_no_rectangle (neighbors S T v) hr).mp hf
    (f.trans (rows T x 1)) (g.trans (columns S v x 1))
    (fun i j => block_incidence S T v x 1 (f i) (g j))

lemma neighbors_card (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (x : X) (g : Γ) : (neighbors S T v (x,g)).card = (S x).card*T.card := by
  simp only [neighbors, card_map, Finset.product_eq_sprod, Finset.card_product]

variable [Fintype X] [Fintype Y] [Fintype Γ]

/-- Every undirected edge is counted once. -/
theorem edge_count (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ) :
    (graph S T v).edgeFinset.card = Fintype.card Γ*T.card*∑ x, (S x).card := by
  rw [graph, incidence_edges, Fintype.sum_prod_type]
  simp only [neighbors_card, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  ring

/-- The selected edges in the block indexed by (x,t). -/
def block (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (R : X × Γ → Finset (Y × Γ)) (x : X) (t : Γ) (s : T) : Finset (S x) :=
  univ.filter (fun y => columns S v x t y ∈ R (rows T x t s))

omit [Fintype X] [Fintype Y] [Fintype Γ] in
lemma block_free (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (R : X × Γ → Finset (Y × Γ))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R)) (x : X) (t : Γ) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (block S T v R x t)) := by
  rw [free_iff_no_rectangle _ (by decide)] at hf ⊢
  intro f g h
  apply hf (f.trans (rows T x t)) (g.trans (columns S v x t))
  intro i j
  exact (mem_filter.mp (h i j)).2

omit [Fintype X] [Fintype Y] [Fintype Γ] in
lemma row_count (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (R : X × Γ → Finset (Y × Γ)) (hR : ∀ p, R p ⊆ neighbors S T v p)
    (x : X) (g : Γ) :
    (R (x,g)).card = ∑ s : T, (block S T v R x (g*s.val) s).card := by
  let f : (Σ s : T, block S T v R x (g*s.val) s) → R (x,g) := fun p =>
    ⟨columns S v x (g*p.1.val) p.2.val, by
      have h := (mem_filter.mp p.2.property).2
      simpa only [rows, Function.Embedding.coeFn_mk, mul_inv_cancel_right] using h⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨s,⟨y,hy⟩⟩ ⟨s',⟨y',hy'⟩⟩ h
      have he : (y.val,(g*s.val)*v x y.val) = (y'.val,(g*s'.val)*v x y'.val) := congrArg Subtype.val h
      have hyy : y = y' := Subtype.ext (congrArg Prod.fst he)
      subst y'
      have hss : s = s' := Subtype.ext (mul_left_cancel (mul_right_cancel (congrArg Prod.snd he)))
      subst s'
      rfl
    · rintro ⟨⟨y,h⟩,hp⟩
      obtain ⟨hy,s,hs,he⟩ := (mem_neighbors S T v x g y h).mp (hR (x,g) hp)
      refine ⟨⟨⟨s,hs⟩,⟨⟨y,hy⟩,?_⟩⟩,?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        simpa only [columns,rows,Function.Embedding.coeFn_mk,mul_inv_cancel_right,he] using hp
      · apply Subtype.ext
        change (y,g*s*v x y) = (y,h)
        exact Prod.ext rfl he.symm
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [Fintype.card_sigma,Fintype.card_coe] using hc.symm

/-- The full blocks partition even an arbitrary selected subset of the edges. -/
theorem edge_partition (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (R : X × Γ → Finset (Y × Γ)) (hR : ∀ p, R p ⊆ neighbors S T v p) :
    (incidence R).edgeFinset.card = ∑ p : X × Γ, ∑ s : T, (block S T v R p.1 p.2 s).card := by
  rw [incidence_edges, Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  simp_rw [row_count S T v R hR]
  rw [sum_comm, sum_comm (s := (univ : Finset Γ)) (t := (univ : Finset T))]
  apply sum_congr rfl
  intro s _
  exact Equiv.sum_comp (Equiv.mulRight s.val) (fun t => (block S T v R x t s).card)

/-- Arbitrary selected edges, with a lower bound on both sides of every
nonempty partition block. Empty base neighborhoods are allowed. -/
theorem set_system_thinning (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (R : X × Γ → Finset (Y × Γ)) (hR : ∀ p, R p ⊆ neighbors S T v p)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R))
    (L : ℕ) (hL : 0 < L) (hT : L ≤ T.card)
    (hS : ∀ x, (S x).card = 0 ∨ L ≤ (S x).card) :
    L*(incidence R).edgeFinset.card^4 ≤ 672*(graph S T v).edgeFinset.card^4 := by
  have hb (p : X × Γ) :
      L*(∑ s : T, (block S T v R p.1 p.2 s).card)^4 ≤
        672*(T.card*(S p.1).card)^4 := by
    rcases hS p.1 with he | he
    · have hz (s : T) : (block S T v R p.1 p.2 s).card = 0 := by
        apply Nat.eq_zero_of_le_zero
        simpa only [Fintype.card_coe,he] using card_le_univ (block S T v R p.1 p.2 s)
      simp only [hz,he,sum_const_zero,mul_zero,zero_pow (by decide : 4 ≠ 0),le_refl]
    · simpa only [Fintype.card_coe] using Erdos714FusionBounds.relative_fourth
        (block S T v R p.1 p.2) (block_free S T v R hf p.1 p.2) L
        (by simpa only [Fintype.card_coe] using hT)
        (by simpa only [Fintype.card_coe] using he)
  have hh : (∑ p : X × Γ, T.card*(S p.1).card) = (graph S T v).edgeFinset.card := by
    rw [edge_count,Fintype.sum_prod_type]
    simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  rw [edge_partition S T v R hR,← hh]
  exact Erdos714FusionBounds.sum_relative_fourth _ _ L 672 hL hb

/-- The estimate applies to every simple-graph edge thinning, not just to
thinnings that retain entire levels, rows, or voltage classes. -/
theorem graph_thinning (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (H : SimpleGraph ((X × Γ) ⊕ (Y × Γ))) (hH : H ≤ graph S T v)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (L : ℕ) (hL : 0 < L) (hT : L ≤ T.card)
    (hS : ∀ x, (S x).card = 0 ∨ L ≤ (S x).card) :
    L*H.edgeFinset.card^4 ≤ 672*(graph S T v).edgeFinset.card^4 := by
  let R := Erdos714Unbalanced.neighborhoods H
  have hbi : H ≤ completeBipartiteGraph (X × Γ) (Y × Γ) := by
    intro a b hab
    have h := hH hab
    cases a <;> cases b <;> simp_all [graph]
  have he : incidence R = H := Erdos714Unbalanced.incidence_neighborhoods H hbi
  have hr : ∀ p, R p ⊆ neighbors S T v p := by
    intro p q hq
    have hadj : H.Adj (.inl p) (.inr q) := (mem_filter.mp hq).2
    exact hH hadj
  have hb := set_system_thinning S T v R hr (by rwa [he]) L hL hT hS
  rw [he] at hb
  exact hb

/-- A retained fraction of at least 1/K bounds the smaller partition dimension. -/
theorem density_budget (S : X → Finset Y) (T : Finset Γ) (v : X → Y → Γ)
    (H : SimpleGraph ((X × Γ) ⊕ (Y × Γ))) (hH : H ≤ graph S T v)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (L K : ℕ) (hL : 0 < L) (hT : L ≤ T.card)
    (hS : ∀ x, (S x).card = 0 ∨ L ≤ (S x).card)
    (hpos : 0 < (graph S T v).edgeFinset.card)
    (hretain : (graph S T v).edgeFinset.card ≤ K*H.edgeFinset.card) : L ≤ 672*K^4 := by
  have hb := graph_thinning S T v H hH hf L hL hT hS
  have hh : (graph S T v).edgeFinset.card^4*L ≤
      (graph S T v).edgeFinset.card^4*(672*K^4) := by
    calc
      _ = L*(graph S T v).edgeFinset.card^4 := by ring
      _ ≤ L*(K*H.edgeFinset.card)^4 := by gcongr
      _ = K^4*(L*H.edgeFinset.card^4) := by ring
      _ ≤ K^4*(672*(graph S T v).edgeFinset.card^4) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos hpos 4)


#print axioms block_incidence
#print axioms not_free
#print axioms edge_count
#print axioms block_free
#print axioms row_count
#print axioms edge_partition
#print axioms set_system_thinning
#print axioms graph_thinning
#print axioms density_budget
end Erdos714VoltageFusion
