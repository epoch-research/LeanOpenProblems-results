import FormalConjecturesUtil

open SimpleGraph Filter Asymptotics Finset

namespace Erdos713KST

abbrev Kst (s t : ℕ) := completeBipartiteGraph (Fin s) (Fin t)

open scoped Classical in
theorem common_card_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {s t : ℕ} (h : (Kst s t).Free G) (f : Fin s ↪ V) :
    (univ.filter (fun v => ∀ i, G.Adj v (f i))).card < t := by
  classical
  by_contra ht
  obtain ⟨R, hR, hcardR⟩ := exists_subset_card_eq (Nat.le_of_not_gt ht)
  apply h
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨univ.map f, R, by simp, by simpa using hcardR, ?_⟩
  intro u hu v hv
  change u ∈ (univ.map f : Finset V) at hu
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
  exact ((mem_filter.mp (hR hv)).2 i).symm

open scoped Classical in
theorem sum_descFactorial_degree_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {s t : ℕ} (h : (Kst s t).Free G) :
    ∑ v, (G.degree v).descFactorial s ≤ t * (Fintype.card V) ^ s := by
  classical
  let r : V → (Fin s ↪ V) → Prop := fun v f => ∀ i, G.Adj v (f i)
  have hAbove (v : V) : ((univ : Finset (Fin s ↪ V)).bipartiteAbove r v).card =
      (G.degree v).descFactorial s := by
    let e : ↥((univ : Finset (Fin s ↪ V)).bipartiteAbove r v) ≃
        (Fin s ↪ G.neighborSet v) :=
      { toFun := fun f =>
          ⟨fun i => ⟨f.val i, ((mem_bipartiteAbove r).mp f.prop).2 i⟩,
            fun i j hij => f.val.injective (congrArg Subtype.val hij)⟩
        invFun := fun f =>
          ⟨f.trans (Function.Embedding.subtype _),
            (mem_bipartiteAbove r).mpr ⟨mem_univ _, fun i => (f i).prop⟩⟩
        left_inv := by intro f; rfl
        right_inv := by intro f; rfl }
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq,
      Fintype.card_fin, card_neighborSet_eq_degree]
  have hBelow (f : Fin s ↪ V) : ((univ : Finset V).bipartiteBelow r f).card ≤ t :=
    (common_card_lt G h f).le
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := (univ : Finset V)) (t := (univ : Finset (Fin s ↪ V)))
  simp_rw [hAbove] at hsum
  rw [hsum]
  calc
    ∑ f : Fin s ↪ V, ((univ : Finset V).bipartiteBelow r f).card ≤
        ∑ _ : Fin s ↪ V, t := sum_le_sum fun f _ => hBelow f
    _ = t * (Fintype.card V).descFactorial s := by simp [Nat.mul_comm]
    _ ≤ t * (Fintype.card V) ^ s :=
      Nat.mul_le_mul_left t (Nat.descFactorial_le_pow _ _)

/-- A deliberately coarse polynomial bound for powers in terms of falling factorials. -/
theorem pow_le_descFactorial (d s : ℕ) :
    d ^ s ≤ (s + 1) ^ s * (d.descFactorial s + 1) := by
  by_cases hsd : s ≤ d
  · have hx : 0 < d + 1 - s := by omega
    have hsx : s ≤ s * (d + 1 - s) := Nat.le_mul_of_pos_right s hx
    have hd : d ≤ (s + 1) * (d + 1 - s) := by
      rw [Nat.add_mul, one_mul]
      omega
    calc
      d ^ s ≤ ((s + 1) * (d + 1 - s)) ^ s := Nat.pow_le_pow_left hd _
      _ = (s + 1) ^ s * (d + 1 - s) ^ s := Nat.mul_pow _ _ _
      _ ≤ (s + 1) ^ s * d.descFactorial s :=
        Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial d s)
      _ ≤ (s + 1) ^ s * (d.descFactorial s + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ _)
  · have hd : d ≤ s + 1 := by omega
    calc
      d ^ s ≤ (s + 1) ^ s := Nat.pow_le_pow_left hd _
      _ ≤ (s + 1) ^ s * (d.descFactorial s + 1) :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

open scoped Classical in
theorem sum_degree_pow_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {s t : ℕ} (hs : 1 ≤ s) (h : (Kst s t).Free G) :
    ∑ v, G.degree v ^ s ≤ (s + 1) ^ s * (t + 1) * (Fintype.card V) ^ s := by
  calc
    ∑ v, G.degree v ^ s ≤ ∑ v, (s + 1) ^ s * ((G.degree v).descFactorial s + 1) :=
      sum_le_sum fun v _ => pow_le_descFactorial _ _
    _ = (s + 1) ^ s * ((∑ v, (G.degree v).descFactorial s) + Fintype.card V) := by
      simp [sum_add_distrib, ← mul_sum]
    _ ≤ (s + 1) ^ s * (t * (Fintype.card V) ^ s + (Fintype.card V) ^ s) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (sum_descFactorial_degree_le G h)
        (Nat.le_self_pow (by omega) _))
    _ = (s + 1) ^ s * (t + 1) * (Fintype.card V) ^ s := by ring

open scoped Classical in
theorem edge_pow_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {s t : ℕ} (hs : 1 ≤ s) (h : (Kst s t).Free G) :
    G.edgeFinset.card ^ s ≤ (s + 1) ^ s * (t + 1) * (Fintype.card V) ^ (s - 1 + s) := by
  have hJ := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg univ
    (f := fun v => (G.degree v : ℝ)) (show (1 : ℝ) ≤ s by exact_mod_cast hs)
    (fun v _ => Nat.cast_nonneg _)
  have he : (s : ℝ) - 1 = ((s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hs, Nat.cast_one]
  rw [he] at hJ
  simp only [Real.rpow_natCast, card_univ] at hJ
  have hJN : (∑ v, G.degree v) ^ s ≤
      Fintype.card V ^ (s - 1) * ∑ v, G.degree v ^ s := by exact_mod_cast hJ
  rw [sum_degrees_eq_twice_card_edges] at hJN
  calc
    G.edgeFinset.card ^ s ≤ (2 * G.edgeFinset.card) ^ s :=
      Nat.pow_le_pow_left (by omega) _
    _ ≤ Fintype.card V ^ (s - 1) * ∑ v, G.degree v ^ s := hJN
    _ ≤ Fintype.card V ^ (s - 1) *
        ((s + 1) ^ s * (t + 1) * Fintype.card V ^ s) :=
      Nat.mul_le_mul_left _ (sum_degree_pow_le G hs h)
    _ = (s + 1) ^ s * (t + 1) * Fintype.card V ^ (s - 1 + s) := by
      rw [pow_add]
      ring

open scoped Classical in
theorem extremal_pow_le (s t n : ℕ) (hs : 1 ≤ s) :
    (extremalNumber n (Kst s t)) ^ s ≤ (s + 1) ^ s * (t + 1) * n ^ (s - 1 + s) := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | (Kst s t).Free G}
  change (S.sup (fun G => G.edgeFinset.card)) ^ s ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨G, hG, he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
    rw [he]
    have hfree : (Kst s t).Free G := by simpa [S] using hG
    simpa only [Fintype.card_fin] using edge_pow_le G hs hfree
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp [Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hs)]

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

theorem exponent_upper_of_containment {W : Type*} {H : SimpleGraph W}
    {s t : ℕ} (hs : 1 ≤ s) (hH : H ⊑ Kst s t) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ 2 - 1 / (s : ℝ) := by
  have hO : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ)) :=
    (isBigO_const_mul_left_iff hc).mp h.isBigO_symm
  have hP : (fun n : ℕ => (n : ℝ) ^ (a * (s : ℝ))) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ) ^ s) := by
    simpa only [Real.rpow_mul_natCast (Nat.cast_nonneg _)] using hO.pow s
  have hB : (fun n : ℕ => (extremalNumber n H : ℝ) ^ s) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((s - 1 + s : ℕ) : ℝ)) := by
    apply IsBigO.of_bound (((s + 1) ^ s * (t + 1) : ℕ) : ℝ)
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _),
      Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    exact_mod_cast (Nat.pow_le_pow_left (hH.extremalNumber_le (n := n)) s).trans
      (extremal_pow_le s t n hs)
  have hExp := exponent_le_of_isBigO (hP.trans hB)
  have hs' : (0 : ℝ) < s := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
  have he : ((s - 1 + s : ℕ) : ℝ) = 2 * (s : ℝ) - 1 := by
    rw [Nat.cast_add, Nat.cast_sub hs, Nat.cast_one]
    ring
  rw [he] at hExp
  calc
    a ≤ (2 * (s : ℝ) - 1) / (s : ℝ) := (le_div_iff₀ hs').mpr hExp
    _ = 2 - 1 / (s : ℝ) := by field_simp

/-- A two-colouring gives an injective homomorphism into a finite complete
bipartite graph after retaining the vertex label within each colour class. -/
theorem bipartite_contained {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hH : H.IsBipartite) :
    H ⊑ Kst (Fintype.card W) (Fintype.card W) := by
  classical
  obtain ⟨χ⟩ := hH
  let e := Fintype.equivFin W
  let f : W → Fin (Fintype.card W) ⊕ Fin (Fintype.card W) :=
    fun v => if χ v = 0 then Sum.inl (e v) else Sum.inr (e v)
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro u v huv
    have hχ : χ u ≠ χ v := χ.valid huv
    by_cases hu : χ u = 0 <;> by_cases hv : χ v = 0
    · exact (hχ (hu.trans hv.symm)).elim
    · simp [f, hu, hv, Kst, completeBipartiteGraph]
    · simp [f, hu, hv, Kst, completeBipartiteGraph]
    · have heq : χ u = χ v := by omega
      exact (hχ heq).elim
  · intro u v huv
    change f u = f v at huv
    by_cases hu : χ u = 0 <;> by_cases hv : χ v = 0
    · simpa [f, hu, hv] using huv
    · simp [f, hu, hv] at huv
    · simp [f, hu, hv] at huv
    · simpa [f, hu, hv] using huv

theorem bipartite_exponent_upper {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) (hH : H.IsBipartite) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ 2 - 1 / (Fintype.card W : ℝ) :=
  exponent_upper_of_containment Fintype.card_pos (bipartite_contained H hH) hc h

end Erdos713KST



namespace Erdos713Norm

variable {F : Type*} [Field F]

/-- The multiplicative expression used for a quadratic norm. -/
def normMap (σ : F →+* F) : F →*₀ F where
  toFun x := x * σ x
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]; ring

@[simp]
theorem normMap_apply (σ : F →+* F) (x : F) : normMap σ x = x * σ x := rfl

theorem normMap_ne_zero (σ : F →+* F) {x : F} (hx : x ≠ 0) : normMap σ x ≠ 0 :=
  mul_ne_zero hx ((map_ne_zero σ).mpr hx)

/-- Two norm-circle equations with distinct centres have at most two solutions.
The argument only needs an injective field endomorphism. -/
theorem norm_circles_no_three (σ : F →+* F) {c d A B x y z : F} (hcd : c ≠ d)
    (hx : normMap σ (x + c) = A) (hx' : normMap σ (x + d) = B)
    (hy : normMap σ (y + c) = A) (hy' : normMap σ (y + d) = B)
    (hz : normMap σ (z + c) = A) (hz' : normMap σ (z + d) = B) :
    x = y ∨ x = z ∨ y = z := by
  have hroot (v : F) (h1 : normMap σ (v + c) = A) (h2 : normMap σ (v + d) = B) :
      (σ c - σ d) * (v + c) * (v + d) - A * (v + d) + B * (v + c) = 0 := by
    simp only [normMap_apply, map_add] at h1 h2
    linear_combination (v + d) * h1 - (v + c) * h2
  have hxP := hroot x hx hx'
  have hyP := hroot y hy hy'
  have hzP := hroot z hz hz'
  have hp : (σ c - σ d) * (x - y) * (x - z) * (y - z) = 0 := by
    linear_combination (y - z) * hxP + (z - x) * hyP + (x - y) * hzP
  by_contra hn
  push_neg at hn
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr (σ.injective.ne hcd)) (sub_ne_zero.mpr hn.1))
    (sub_ne_zero.mpr hn.2.1)) (sub_ne_zero.mpr hn.2.2)) hp

theorem normalized_circle (σ : F →+* F) {r s z a a₀ b : F}
    (hrs : r ≠ s) (hsz : s + z ≠ 0) (ha₀ : a₀ ≠ 0) (hb : b ≠ 0)
    (h1 : normMap σ (r + z) = a * b) (h2 : normMap σ (s + z) = a₀ * b) :
    normMap σ ((s + z)⁻¹ + (r - s)⁻¹) = a / (a₀ * normMap σ (r - s)) := by
  have hdiff : r - s ≠ 0 := sub_ne_zero.mpr hrs
  have he : (s + z)⁻¹ + (r - s)⁻¹ = (r + z) / ((s + z) * (r - s)) := by
    field_simp
    ring
  rw [he, map_div₀, map_mul, h1, h2]
  field_simp

/-- The algebraic obstruction to a complete three-by-three rectangle. -/
theorem no_norm_rectangle (σ : F →+* F) (a A b B : Fin 3 → F)
    (hA : ∀ i, A i ≠ 0) (hB : ∀ j, B j ≠ 0)
    (haA : Function.Injective (fun i => (a i, A i)))
    (hbB : Function.Injective (fun j => (b j, B j)))
    (he : ∀ i j, normMap σ (a i + b j) = A i * B j) : False := by
  have ha : Function.Injective a := by
    intro i k hik
    have hmul : A i * B 0 = A k * B 0 := by rw [← he, hik, he]
    exact haA (Prod.ext hik (mul_right_cancel₀ (hB 0) hmul))
  have hb : Function.Injective b := by
    intro j k hjk
    have hmul : A 0 * B j = A 0 * B k := by rw [← he, hjk, he]
    exact hbB (Prod.ext hjk (mul_left_cancel₀ (hA 0) hmul))
  have hsum (j : Fin 3) : a 2 + b j ≠ 0 := by
    intro hz
    have hh := he 2 j
    rw [hz, map_zero] at hh
    exact mul_ne_zero (hA 2) (hB j) hh.symm
  let x : Fin 3 → F := fun j => (a 2 + b j)⁻¹
  let c : F := (a 0 - a 2)⁻¹
  let d : F := (a 1 - a 2)⁻¹
  have hc : c ≠ d := by
    intro hcd
    have hh : a 0 = a 1 := sub_left_injective (inv_injective hcd)
    exact (show (0 : Fin 3) ≠ 1 by decide) (ha hh)
  have hcircle0 (j : Fin 3) : normMap σ (x j + c) =
      A 0 / (A 2 * normMap σ (a 0 - a 2)) :=
    normalized_circle σ (ha.ne (by decide : (0 : Fin 3) ≠ 2)) (hsum j)
      (hA 2) (hB j) (he 0 j) (he 2 j)
  have hcircle1 (j : Fin 3) : normMap σ (x j + d) =
      A 1 / (A 2 * normMap σ (a 1 - a 2)) :=
    normalized_circle σ (ha.ne (by decide : (1 : Fin 3) ≠ 2)) (hsum j)
      (hA 2) (hB j) (he 1 j) (he 2 j)
  have hx : Function.Injective x := by
    intro j k hjk
    exact hb (add_left_cancel (inv_injective hjk))
  rcases norm_circles_no_three σ hc (hcircle0 0) (hcircle1 0)
      (hcircle0 1) (hcircle1 1) (hcircle0 2) (hcircle1 2) with hh | hh | hh
  · exact (show (0 : Fin 3) ≠ 1 by decide) (hx hh)
  · exact (show (0 : Fin 3) ≠ 2 by decide) (hx hh)
  · exact (show (1 : Fin 3) ≠ 2 by decide) (hx hh)

section Graph

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

abbrev Vertex := F × Kˣ

def graph : SimpleGraph (Vertex K F ⊕ Vertex K F) where
  Adj u v := match u, v with
    | Sum.inl x, Sum.inr y => Algebra.norm K (x.1 + y.1) = (x.2 : K) * (y.2 : K)
    | Sum.inr y, Sum.inl x => Algebra.norm K (x.1 + y.1) = (x.2 : K) * (y.2 : K)
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp
  loopless := by intro v; cases v <;> simp

def project : Vertex K F ⊕ Vertex K F → Vertex K F := Sum.elim id id

theorem eq_of_common_neighbor {u v w : Vertex K F ⊕ Vertex K F}
    (hu : (graph K F).Adj u w) (hv : (graph K F).Adj v w)
    (he : project K F u = project K F v) : u = v := by
  cases u <;> cases v <;> cases w <;> simp_all [graph, project]

theorem norm_eq_of_adj {u v : Vertex K F ⊕ Vertex K F} (h : (graph K F).Adj u v) :
    Algebra.norm K ((project K F u).1 + (project K F v).1) =
      ((project K F u).2 : K) * ((project K F v).2 : K) := by
  cases u <;> cases v <;> simp_all [graph, project, add_comm, mul_comm]

theorem vertex_embed_injective : Function.Injective
    (fun x : Vertex K F => (x.1, algebraMap K F (x.2 : K))) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun z : F × F => z.1) h
  exact Units.ext ((algebraMap K F).injective (congrArg (fun z : F × F => z.2) h))

theorem graph_free (σ : F →+* F)
    (hNorm : ∀ x : F, algebraMap K F (Algebra.norm K x) = normMap σ x) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Free (graph K F) := by
  rintro ⟨f⟩
  have hAdj (i j : Fin 3) : (graph K F).Adj (f (Sum.inl i)) (f (Sum.inr j)) :=
    f.toHom.map_rel' (by simp [completeBipartiteGraph])
  let L : Fin 3 → Vertex K F := fun i => project K F (f (Sum.inl i))
  let R : Fin 3 → Vertex K F := fun j => project K F (f (Sum.inr j))
  have hL : Function.Injective L := by
    intro i k hik
    exact Sum.inl.inj (f.injective (eq_of_common_neighbor K F (hAdj i 0) (hAdj k 0) hik))
  have hR : Function.Injective R := by
    intro j k hjk
    exact Sum.inr.inj (f.injective
      (eq_of_common_neighbor K F (hAdj 0 j).symm (hAdj 0 k).symm hjk))
  apply no_norm_rectangle σ (fun i => (L i).1) (fun i => algebraMap K F ((L i).2 : K))
    (fun j => (R j).1) (fun j => algebraMap K F ((R j).2 : K))
  · intro i
    exact (map_ne_zero _).mpr (L i).2.ne_zero
  · intro j
    exact (map_ne_zero _).mpr (R j).2.ne_zero
  · exact (vertex_embed_injective K F).comp hL
  · exact (vertex_embed_injective K F).comp hR
  · intro i j
    rw [← hNorm, ← map_mul]
    exact congrArg (algebraMap K F) (norm_eq_of_adj K F (hAdj i j))

variable [FiniteDimensional K F]

noncomputable def leftNeighbors (v : Vertex K F) : Fˣ ↪ (graph K F).neighborSet (Sum.inl v) where
  toFun z := ⟨Sum.inr ((z : F) - v.1, (Units.mk0 (Algebra.norm K (z : F))
      (Algebra.norm_ne_zero_iff.mpr z.ne_zero)) / v.2), by
    change Algebra.norm K (v.1 + ((z : F) - v.1)) = _
    rw [show v.1 + ((z : F) - v.1) = z by ring]
    simp only [Units.val_div_eq_div_val, Units.val_mk0]
    exact (mul_div_cancel₀ _ v.2.ne_zero).symm⟩
  inj' := by
    intro z w h
    have h' := congrArg (fun t => (project K F t.val).1) h
    change (z : F) - v.1 = (w : F) - v.1 at h'
    exact Units.ext (sub_left_injective h')

noncomputable def rightNeighbors (v : Vertex K F) : Fˣ ↪ (graph K F).neighborSet (Sum.inr v) where
  toFun z := ⟨Sum.inl ((z : F) - v.1, (Units.mk0 (Algebra.norm K (z : F))
      (Algebra.norm_ne_zero_iff.mpr z.ne_zero)) / v.2), by
    change Algebra.norm K (((z : F) - v.1) + v.1) = _
    simp only [sub_add_cancel, Units.val_div_eq_div_val, Units.val_mk0]
    exact (div_mul_cancel₀ _ v.2.ne_zero).symm⟩
  inj' := by
    intro z w h
    have h' := congrArg (fun t => (project K F t.val).1) h
    change (z : F) - v.1 = (w : F) - v.1 at h'
    exact Units.ext (sub_left_injective h')

open scoped Classical in
theorem degree_lower [Fintype K] [Fintype F] (v : Vertex K F ⊕ Vertex K F) :
    Fintype.card F - 1 ≤ (graph K F).degree v := by
  classical
  have hcard : Fintype.card Fˣ = Fintype.card F - 1 := Fintype.card_units F
  rw [← hcard, ← card_neighborSet_eq_degree]
  cases v with
  | inl v => exact Fintype.card_le_of_embedding (leftNeighbors K F v)
  | inr v => exact Fintype.card_le_of_embedding (rightNeighbors K F v)

open scoped Classical in
theorem edge_lower [Fintype K] [Fintype F] :
    Fintype.card F * (Fintype.card K - 1) * (Fintype.card F - 1) ≤ (graph K F).edgeFinset.card := by
  classical
  have hsum : ∑ v : Vertex K F ⊕ Vertex K F, (Fintype.card F - 1) ≤
      ∑ v : Vertex K F ⊕ Vertex K F, (graph K F).degree v :=
    sum_le_sum fun v _ => degree_lower K F v
  rw [sum_degrees_eq_twice_card_edges] at hsum
  simp only [sum_const, card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_units,
    Nat.nsmul_eq_mul, Vertex] at hsum
  nlinarith

theorem extremal_lower [Fintype K] [Fintype F]
    (hfree : (completeBipartiteGraph (Fin 3) (Fin 3)).Free (graph K F)) :
    Fintype.card F * (Fintype.card K - 1) * (Fintype.card F - 1) ≤
      extremalNumber (2 * Fintype.card F * (Fintype.card K - 1))
        (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  have hE := edge_lower K F
  have hExt := card_edgeFinset_le_extremalNumber hfree
  have hN : Fintype.card (Vertex K F ⊕ Vertex K F) =
      2 * Fintype.card F * (Fintype.card K - 1) := by
    simp only [Vertex, Fintype.card_sum, Fintype.card_prod, Fintype.card_units]
    ring
  rw [hN] at hExt
  exact hE.trans hExt

end Graph

section FiniteField

variable (p : ℕ) [Fact p.Prime]

theorem finite_norm_formula (x : GaloisField p 2) :
    algebraMap (ZMod p) (GaloisField p 2) (Algebra.norm (ZMod p) x) =
      normMap (frobenius (GaloisField p 2) p) x := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hK : Nat.card (ZMod p) = p := by simp [Nat.card_eq_fintype_card]
  have hF : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by decide)
  have he : (p ^ 2 - 1) / (p - 1) = p + 1 := by
    have hp1 : 0 < p - 1 := by omega
    have hmul : p ^ 2 - 1 = (p + 1) * (p - 1) := by
      have he1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
      have hp2 : 1 ≤ p ^ 2 := by nlinarith
      have he2 := Nat.sub_add_cancel hp2
      nlinarith
    rw [hmul, Nat.mul_div_cancel _ hp1]
  rw [FiniteField.algebraMap_norm_eq_pow, hK, hF, he, normMap_apply, frobenius_def,
    pow_succ, mul_comm]

theorem finite_graph_free :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Free (graph (ZMod p) (GaloisField p 2)) :=
  graph_free (ZMod p) (GaloisField p 2) (frobenius (GaloisField p 2) p)
    (finite_norm_formula p)

end FiniteField

abbrev K33 := completeBipartiteGraph (Fin 3) (Fin 3)

set_option maxHeartbeats 400000 in
theorem extremal_lower_prime (p : ℕ) (hp : p.Prime) :
    p ^ 5 ≤ 4 * extremalNumber (2 * p ^ 2 * (p - 1)) K33 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p 2 (by decide)
  have hBound := extremal_lower (ZMod p) (GaloisField p 2) (finite_graph_free p)
  rw [hF, ZMod.card] at hBound
  have hp1 : p ≤ 2 * (p - 1) := by have := hp.two_le; omega
  have hp2 : p ^ 2 ≤ 2 * (p ^ 2 - 1) := by
    have hh : 2 ≤ p ^ 2 := by nlinarith only [hp.two_le]
    omega
  have hprod := Nat.mul_le_mul_left (p ^ 2) (Nat.mul_le_mul hp1 hp2)
  have hlow : p ^ 5 ≤ 4 * (p ^ 2 * (p - 1) * (p ^ 2 - 1)) := by
    nlinarith only [hprod]
  exact hlow.trans (Nat.mul_le_mul_left 4 hBound)

theorem lower_exponent_of_prime_bound {f : ℕ → ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hO : (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hlow : ∀ p : ℕ, p.Prime → p ^ 5 ≤ 4 * f (2 * p ^ 2 * (p - 1))) :
    (5 : ℝ) / 3 ≤ a := by
  by_contra hna
  have ha' : a < (5 : ℝ) / 3 := lt_of_not_ge hna
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  have ht : Tendsto (fun p : ℕ => 2 * p ^ 2 * (p - 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop (max N 2)] with p hp
    have hp2 : 2 ≤ p := (le_max_right _ _).trans hp
    have hpN : N ≤ p := (le_max_left _ _).trans hp
    have hp1 : 1 ≤ p - 1 := by omega
    have hpow : p ≤ 2 * p ^ 2 := by nlinarith
    have hprod := Nat.mul_le_mul_left (2 * p ^ 2) hp1
    omega
  have hratio : ∀ᶠ p : ℕ in atTop,
      p.Prime → (p : ℝ) ^ (5 - 3 * a) ≤ 4 * C * (2 : ℝ) ^ a := by
    filter_upwards [ht.eventually hC.bound, eventually_gt_atTop (0 : ℕ)] with p hp hpos
    intro hprime
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpos
    have hl : (p : ℝ) ^ 5 ≤ 4 * (f (2 * p ^ 2 * (p - 1)) : ℝ) := by
      exact_mod_cast hlow p hprime
    have hsize : ((2 * p ^ 2 * (p - 1) : ℕ) : ℝ) ≤ 2 * (p : ℝ) ^ 3 := by
      have hb := Nat.mul_le_mul_left (2 * p ^ 2) (Nat.sub_le p 1)
      have hb' : 2 * p ^ 2 * (p - 1) ≤ 2 * p ^ 3 := by nlinarith only [hb]
      exact_mod_cast hb'
    have hu : (f (2 * p ^ 2 * (p - 1)) : ℝ) ≤ C * (2 * (p : ℝ) ^ 3) ^ a := by
      rw [Real.norm_natCast, Real.norm_of_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg _) a)] at hp
      exact hp.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hsize ha) hCpos.le)
    have he : (p : ℝ) ^ 5 ≤ 4 * C * (2 * (p : ℝ) ^ 3) ^ a := by
      nlinarith only [hl, hu]
    have hp3 : ((p : ℝ) ^ 3) ^ a = (p : ℝ) ^ (3 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      norm_num
    rw [Real.mul_rpow (by norm_num) (pow_nonneg hp0.le 3), hp3] at he
    rw [Real.rpow_sub hp0, div_le_iff₀ (Real.rpow_pos_of_pos hp0 (3 * a))]
    have hp5 : (p : ℝ) ^ (5 : ℝ) = (p : ℝ) ^ (5 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (p : ℝ) 5
    rw [hp5]
    simpa only [mul_assoc] using he
  have htop : Tendsto (fun p : ℕ => (p : ℝ) ^ (5 - 3 * a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 5 - 3 * a)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hratio.and (htop.eventually_gt_atTop (4 * C * (2 : ℝ) ^ a)))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  exact (not_lt_of_ge ((hN p hpN).1 hp)) ((hN p hpN).2)

end Erdos713Norm

namespace Erdos713K3t

abbrev K3t (t : ℕ) := completeBipartiteGraph (Fin 3) (Fin t)

theorem exponent_eq_of_containment {W : Type*} {H : SimpleGraph W} {t : ℕ}
    (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ K3t t) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (5 : ℝ) / 3 := by
  have hu : a ≤ (5 : ℝ) / 3 := by
    have hh := Erdos713KST.exponent_upper_of_containment (by decide : 1 ≤ 3) hhi hc.ne' h
    norm_num at hh
    exact hh
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc.ne').mp h.isBigO
  apply le_antisymm hu
  apply Erdos713Norm.lower_exponent_of_prime_bound ha hO
  intro p hp
  exact (Erdos713Norm.extremal_lower_prime p hp).trans
    (Nat.mul_le_mul_left 4 hlo.extremalNumber_le)

theorem rational_exponent_of_containment {W : Type*} {H : SimpleGraph W} {t : ℕ}
    (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ K3t t) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨5 / 3, ?_⟩
  simpa using (exponent_eq_of_containment hlo hhi ha hc h).symm

theorem contains_K33 {t : ℕ} (ht : 3 ≤ t) : Erdos713Norm.K33 ⊑ K3t t := by
  refine ⟨⟨⟨Sum.map id (Fin.castLE ht), ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u <;> cases v <;> simpa [Erdos713Norm.K33, K3t, completeBipartiteGraph] using huv
  · exact Sum.map_injective.mpr ⟨Function.injective_id, Fin.castLE_injective ht⟩

theorem rational_exponent {t : ℕ} (ht : 3 ≤ t) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n (K3t t) : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) :=
  rational_exponent_of_containment (contains_K33 ht) (.refl _) ha hc h

end Erdos713K3t

#print axioms Erdos713K3t.rational_exponent
