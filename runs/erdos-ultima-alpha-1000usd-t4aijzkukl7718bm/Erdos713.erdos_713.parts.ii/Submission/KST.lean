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

#print axioms Erdos713KST.edge_pow_le

#print axioms Erdos713KST.exponent_upper_of_containment

#print axioms Erdos713KST.bipartite_exponent_upper
