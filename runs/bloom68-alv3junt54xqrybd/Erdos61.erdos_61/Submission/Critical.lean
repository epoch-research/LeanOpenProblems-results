import FormalConjecturesUtil

/-!
# Exact finite-graph bounds and critical pure-pair pressure

The invariant `kappa` is the product of the independence and clique numbers.
Disjoint anticomplete pairs, and dually complete pairs, give additive lower
bounds for this invariant. All graphs in these bounds have finite vertex types.
For exponent-critical graphs these bounds yield strict real-power pressure
inequalities, both before and after normalization by the ambient vertex count.
-/

namespace Erdos61Research

open SimpleGraph

variable {V W : Type*}

/-- The natural-number product of the independence and clique numbers. -/
noncomputable def kappa (G : SimpleGraph V) : ℕ := G.indepNum * G.cliqueNum

@[simp] theorem kappa_compl (G : SimpleGraph V) : kappa Gᶜ = kappa G := by
  simp [kappa, Nat.mul_comm]

/-- Pullback along an embedding commutes with graph complementation. -/
@[simp] theorem comap_compl (G : SimpleGraph V) (f : W ↪ V) :
    (Gᶜ).comap f = (G.comap f)ᶜ := by
  ext u v
  simp only [SimpleGraph.comap_adj, SimpleGraph.compl_adj, f.injective.ne_iff]

@[simp] theorem induce_compl (G : SimpleGraph V) (A : Set V) :
    (Gᶜ).induce A = (G.induce A)ᶜ :=
  comap_compl G (Function.Embedding.subtype _)

/-- A clique in an embedding pullback maps to a clique in the original graph. -/
theorem isClique_comap_map {G : SimpleGraph V} {f : W ↪ V} {s : Finset W}
    (h : (G.comap f).IsClique s) : G.IsClique (s.map f) := by
  rw [Finset.coe_map]
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
  exact h hu hv (ne_of_apply_ne f huv)

/-- An independent set in an embedding pullback remains independent after mapping. -/
theorem isIndepSet_comap_map {G : SimpleGraph V} {f : W ↪ V} {s : Finset W}
    (h : (G.comap f).IsIndepSet s) : G.IsIndepSet (s.map f) := by
  rw [Finset.coe_map]
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
  exact h hu hv (ne_of_apply_ne f huv)

/-- Clique numbers cannot increase under an embedding pullback. -/
theorem cliqueNum_comap_le [Finite V] [Finite W] (G : SimpleGraph V) (f : W ↪ V) :
    (G.comap f).cliqueNum ≤ G.cliqueNum := by
  obtain ⟨s, hs⟩ := (G.comap f).exists_isNClique_cliqueNum
  have h := (isClique_comap_map hs.isClique).card_le_cliqueNum
  simpa only [Finset.card_map, hs.card_eq] using h

/-- Independence numbers cannot increase under an embedding pullback. -/
theorem indepNum_comap_le [Finite V] [Finite W] (G : SimpleGraph V) (f : W ↪ V) :
    (G.comap f).indepNum ≤ G.indepNum := by
  obtain ⟨s, hs⟩ := (G.comap f).exists_isNIndepSet_indepNum
  have h := (isIndepSet_comap_map hs.isIndepSet).card_le_indepNum
  simpa only [Finset.card_map, hs.card_eq] using h

theorem cliqueNum_induce_le [Finite V] (G : SimpleGraph V) (A : Set V) :
    (G.induce A).cliqueNum ≤ G.cliqueNum :=
  cliqueNum_comap_le G (Function.Embedding.subtype _)

theorem indepNum_induce_le [Finite V] (G : SimpleGraph V) (A : Set V) :
    (G.induce A).indepNum ≤ G.indepNum :=
  indepNum_comap_le G (Function.Embedding.subtype _)

/-- The mapped vertices of a finset in a finset subtype lie in that finset. -/
theorem map_subtype_subset (A : Finset V) (s : Finset (A : Set V)) :
    s.map (Function.Embedding.subtype (fun v : V => v ∈ A)) ⊆ A := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hv
  exact u.property

/-- Independent sets with no edges between them have independent union. -/
theorem isIndepSet_union_of_anticomplete [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} (hA : G.IsIndepSet A) (hB : G.IsIndepSet B)
    (hanti : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) :
    G.IsIndepSet (A ∪ B : Finset V) := by
  rw [Finset.coe_union, SimpleGraph.isIndepSet_iff, Set.pairwise_union]
  refine ⟨hA, hB, ?_⟩
  intro a ha b hb _
  exact ⟨hanti a ha b hb, fun h => hanti a ha b hb h.symm⟩

/-- Maximum independent sets on disjoint anticomplete sides can be united. -/
theorem indepNum_induce_add_le_of_anticomplete [Finite V]
    (G : SimpleGraph V) (A B : Finset V) (hdis : Disjoint A B)
    (hanti : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) :
    (G.induce (A : Set V)).indepNum + (G.induce (B : Set V)).indepNum ≤ G.indepNum := by
  classical
  obtain ⟨sA, hsA⟩ := (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  obtain ⟨sB, hsB⟩ := (G.induce (B : Set V)).exists_isNIndepSet_indepNum
  let IA := sA.map (Function.Embedding.subtype (fun v : V => v ∈ A))
  let IB := sB.map (Function.Embedding.subtype (fun v : V => v ∈ B))
  have hIA : IA ⊆ A := map_subtype_subset A sA
  have hIB : IB ⊆ B := map_subtype_subset B sB
  have hIAd : G.IsIndepSet IA := isIndepSet_comap_map hsA.isIndepSet
  have hIBd : G.IsIndepSet IB := isIndepSet_comap_map hsB.isIndepSet
  have hIJ : Disjoint IA IB := hdis.mono hIA hIB
  have hUnion : G.IsIndepSet (IA ∪ IB : Finset V) :=
    isIndepSet_union_of_anticomplete hIAd hIBd
      (fun a ha b hb => hanti a (hIA ha) b (hIB hb))
  have hcard := hUnion.card_le_indepNum
  rw [Finset.card_union_of_disjoint hIJ] at hcard
  simpa only [IA, IB, Finset.card_map, hsA.card_eq, hsB.card_eq] using hcard

/-- The product invariant is superadditive on disjoint anticomplete pairs. -/
theorem kappa_add_le_of_anticomplete [Finite V]
    (G : SimpleGraph V) (A B : Finset V) (hdis : Disjoint A B)
    (hanti : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) :
    kappa (G.induce (A : Set V)) + kappa (G.induce (B : Set V)) ≤ kappa G := by
  have hA := cliqueNum_induce_le G (A : Set V)
  have hB := cliqueNum_induce_le G (B : Set V)
  have hI := indepNum_induce_add_le_of_anticomplete G A B hdis hanti
  calc
    kappa (G.induce (A : Set V)) + kappa (G.induce (B : Set V))
        ≤ (G.induce (A : Set V)).indepNum * G.cliqueNum +
          (G.induce (B : Set V)).indepNum * G.cliqueNum :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hA) (Nat.mul_le_mul_left _ hB)
    _ = ((G.induce (A : Set V)).indepNum + (G.induce (B : Set V)).indepNum) *
          G.cliqueNum := by rw [Nat.add_mul]
    _ ≤ kappa G := Nat.mul_le_mul_right _ hI

/-- Maximum cliques on disjoint complete sides can be united, by complementation. -/
theorem cliqueNum_induce_add_le_of_complete [Finite V]
    (G : SimpleGraph V) (A B : Finset V) (hdis : Disjoint A B)
    (hcomplete : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    (G.induce (A : Set V)).cliqueNum + (G.induce (B : Set V)).cliqueNum ≤ G.cliqueNum := by
  have hanti : ∀ a ∈ A, ∀ b ∈ B, ¬(Gᶜ).Adj a b := by
    intro a ha b hb h
    exact ((SimpleGraph.compl_adj G a b).mp h).2 (hcomplete a ha b hb)
  simpa only [induce_compl, SimpleGraph.indepNum_compl] using
    indepNum_induce_add_le_of_anticomplete Gᶜ A B hdis hanti

/-- The complete-pair dual of the anticomplete product bound. -/
theorem kappa_add_le_of_complete [Finite V]
    (G : SimpleGraph V) (A B : Finset V) (hdis : Disjoint A B)
    (hcomplete : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    kappa (G.induce (A : Set V)) + kappa (G.induce (B : Set V)) ≤ kappa G := by
  have hanti : ∀ a ∈ A, ∀ b ∈ B, ¬(Gᶜ).Adj a b := by
    intro a ha b hb h
    exact ((SimpleGraph.compl_adj G a b).mp h).2 (hcomplete a ha b hb)
  simpa only [induce_compl, kappa_compl] using
    kappa_add_le_of_anticomplete Gᶜ A B hdis hanti

/-- Either anticompleteness or completeness is enough for the product bound. -/
theorem kappa_add_le_of_pure_pair [Finite V]
    (G : SimpleGraph V) (A B : Finset V) (hdis : Disjoint A B)
    (hpure : (∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) ∨ (∀ a ∈ A, ∀ b ∈ B, G.Adj a b)) :
    kappa (G.induce (A : Set V)) + kappa (G.induce (B : Set V)) ≤ kappa G := by
  rcases hpure with hanti | hcomplete
  · exact kappa_add_le_of_anticomplete G A B hdis hanti
  · exact kappa_add_le_of_complete G A B hdis hcomplete

/-- A finite graph is exponent-critical when its product invariant is strictly
below the indicated real power, while every proper induced vertex set satisfies
the corresponding lower bound. Empty proper vertex sets are included. -/
structure IsExponentCritical [Fintype V] (G : SimpleGraph V) (τ : ℝ) : Prop where
  kappa_lt : (kappa G : ℝ) < (Fintype.card V : ℝ) ^ τ
  induced_ge : ∀ A : Finset V, A ≠ Finset.univ →
    (A.card : ℝ) ^ τ ≤ (kappa (G.induce (A : Set V)) : ℝ)

/-- Criticality is preserved by complementation. -/
theorem IsExponentCritical.compl [Fintype V] {G : SimpleGraph V} {τ : ℝ}
    (hcrit : IsExponentCritical G τ) : IsExponentCritical Gᶜ τ := by
  refine ⟨?_, ?_⟩
  · simpa only [kappa_compl] using hcrit.kappa_lt
  · intro A hA
    simpa only [induce_compl, kappa_compl] using hcrit.induced_ge A hA

@[simp] theorem isExponentCritical_compl [Fintype V] (G : SimpleGraph V) (τ : ℝ) :
    IsExponentCritical Gᶜ τ ↔ IsExponentCritical G τ := by
  constructor
  · intro hcrit
    simpa only [compl_compl] using hcrit.compl
  · exact IsExponentCritical.compl

/-- For positive exponents a critical graph must have a positive vertex count. -/
theorem IsExponentCritical.card_pos_of_exponent_pos [Fintype V]
    {G : SimpleGraph V} {τ : ℝ} (hcrit : IsExponentCritical G τ) (hτ : 0 < τ) :
    0 < Fintype.card V := by
  by_contra hn
  have hn0 : Fintype.card V = 0 := Nat.eq_zero_of_not_pos hn
  have hlt := hcrit.kappa_lt
  rw [hn0, Nat.cast_zero, Real.zero_rpow (ne_of_gt hτ)] at hlt
  exact (not_lt_of_ge (Nat.cast_nonneg (kappa G))) hlt

/-- Criticality and the exact pure-pair bound give an unnormalized strict
real-power inequality. The exponent may be any real number. -/
theorem IsExponentCritical.card_rpow_add_lt_of_pure_pair [Fintype V]
    {G : SimpleGraph V} {τ : ℝ} (hcrit : IsExponentCritical G τ) (A B : Finset V)
    (hAproper : A ≠ Finset.univ) (hBproper : B ≠ Finset.univ)
    (hdis : Disjoint A B)
    (hpure : (∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) ∨ (∀ a ∈ A, ∀ b ∈ B, G.Adj a b)) :
    (A.card : ℝ) ^ τ + (B.card : ℝ) ^ τ < (Fintype.card V : ℝ) ^ τ := by
  calc
    (A.card : ℝ) ^ τ + (B.card : ℝ) ^ τ
        ≤ (kappa (G.induce (A : Set V)) : ℝ) +
          (kappa (G.induce (B : Set V)) : ℝ) :=
      add_le_add (hcrit.induced_ge A hAproper) (hcrit.induced_ge B hBproper)
    _ ≤ (kappa G : ℝ) := by
      exact_mod_cast kappa_add_le_of_pure_pair G A B hdis hpure
    _ < (Fintype.card V : ℝ) ^ τ := hcrit.kappa_lt

/-- Normalized pure-pair pressure in a critical graph. Positivity of the vertex
count is enough for normalization: neither a positive exponent nor nonempty
sides is needed once properness of both sides is assumed. -/
theorem IsExponentCritical.pure_pair_pressure [Fintype V]
    {G : SimpleGraph V} {τ : ℝ} (hcrit : IsExponentCritical G τ) (A B : Finset V)
    (hn : 0 < Fintype.card V) (hAproper : A ≠ Finset.univ) (hBproper : B ≠ Finset.univ)
    (hdis : Disjoint A B)
    (hpure : (∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) ∨ (∀ a ∈ A, ∀ b ∈ B, G.Adj a b)) :
    ((A.card : ℝ) / (Fintype.card V : ℝ)) ^ τ +
      ((B.card : ℝ) / (Fintype.card V : ℝ)) ^ τ < 1 := by
  have hnR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hnPow : 0 < (Fintype.card V : ℝ) ^ τ := Real.rpow_pos_of_pos hnR τ
  rw [Real.div_rpow (Nat.cast_nonneg A.card) (Nat.cast_nonneg (Fintype.card V)) τ,
    Real.div_rpow (Nat.cast_nonneg B.card) (Nat.cast_nonneg (Fintype.card V)) τ,
    ← add_div]
  exact (div_lt_one hnPow).mpr
    (hcrit.card_rpow_add_lt_of_pure_pair A B hAproper hBproper hdis hpure)

/-- For disjoint nonempty sides, properness and a positive ambient vertex count
follow automatically. This in particular supplies the pressure inequality for
positive exponents and nonempty proper pure pairs. -/
theorem IsExponentCritical.pure_pair_pressure_of_nonempty [Fintype V]
    {G : SimpleGraph V} {τ : ℝ} (hcrit : IsExponentCritical G τ) (A B : Finset V)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdis : Disjoint A B)
    (hpure : (∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) ∨ (∀ a ∈ A, ∀ b ∈ B, G.Adj a b)) :
    ((A.card : ℝ) / (Fintype.card V : ℝ)) ^ τ +
      ((B.card : ℝ) / (Fintype.card V : ℝ)) ^ τ < 1 := by
  have hn : 0 < Fintype.card V := (Finset.card_pos.mpr hA).trans_le A.card_le_univ
  have hAproper : A ≠ Finset.univ := by
    intro hEq
    obtain ⟨b, hb⟩ := hB
    exact Finset.disjoint_left.mp hdis (by simp [hEq]) hb
  have hBproper : B ≠ Finset.univ := by
    intro hEq
    obtain ⟨a, ha⟩ := hA
    exact Finset.disjoint_left.mp hdis.symm (by simp [hEq]) ha
  exact hcrit.pure_pair_pressure A B hn hAproper hBproper hdis hpure

/-- Normalized strict power pressure amplifies the deficit of the second side.
All sizes here are arbitrary nonnegative reals, not just vertex counts. -/
theorem rpow_pressure_amplifier {τ n a b : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hn : 0 < n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbn : b ≤ n)
    (hpressure : (a / n) ^ τ + (b / n) ^ τ < 1) :
    n ^ (1 - τ) * a ^ τ < n - b := by
  have hbPow : b / n ≤ (b / n) ^ τ := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' (div_nonneg hb hn.le)
        ((div_le_one hn).mpr hbn) hτ.le hτ1
  have hratio : (a / n) ^ τ < 1 - b / n := by
    linarith
  calc
    n ^ (1 - τ) * a ^ τ = n * (a / n) ^ τ := by
      rw [Real.rpow_sub hn 1 τ, Real.rpow_one, Real.div_rpow ha hn.le τ]
      ring
    _ < n * (1 - b / n) := mul_lt_mul_of_pos_left hratio hn
    _ = n - b := by
      field_simp [hn.ne']

/-- If the second side covers all but at most `E`, strict power pressure makes
`n ^ (1 - τ) * a ^ τ` strictly smaller than `E`. No sign assumption on `E`
is needed: its positivity follows from the hypotheses. -/
theorem rpow_pressure_amplifier_of_cover {τ n a b E : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hn : 0 < n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbn : b ≤ n) (hcover : n - E ≤ b)
    (hpressure : (a / n) ^ τ + (b / n) ^ τ < 1) :
    n ^ (1 - τ) * a ^ τ < E := by
  exact (rpow_pressure_amplifier hτ hτ1 hn ha hb hbn hpressure).trans_le
    (by linarith)

/-- For `0 < τ < 1` and a positive first side, the cover-error amplifier also
bounds the ambient size. The hypotheses themselves ensure the quotient is positive. -/
theorem rpow_pressure_order_lt_of_cover {τ n a b E : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hn : 0 < n)
    (ha : 0 < a) (hb : 0 ≤ b) (hbn : b ≤ n) (hcover : n - E ≤ b)
    (hpressure : (a / n) ^ τ + (b / n) ^ τ < 1) :
    n < (E / a ^ τ) ^ (1 / (1 - τ)) := by
  have haPow : 0 < a ^ τ := Real.rpow_pos_of_pos ha τ
  have hbound := rpow_pressure_amplifier_of_cover hτ hτ1.le hn ha.le hb hbn
    hcover hpressure
  have hpow : n ^ (1 - τ) < E / a ^ τ := (lt_div_iff₀ haPow).mpr hbound
  have hquot : 0 ≤ E / a ^ τ :=
    (Real.rpow_pos_of_pos hn (1 - τ)).le.trans hpow.le
  simpa only [one_div] using
    (Real.lt_rpow_inv_iff_of_pos hn.le hquot (sub_pos.mpr hτ1)).mpr hpow

/-- In an exponent-critical graph, disjoint nonempty pure sides obey the
near-cover amplifier with the exact real-valued deficit of the second side. -/
theorem IsExponentCritical.pure_pair_near_cover [Fintype V]
    {G : SimpleGraph V} {τ : ℝ} (hcrit : IsExponentCritical G τ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (A B : Finset V)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdis : Disjoint A B)
    (hpure : (∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) ∨
      (∀ a ∈ A, ∀ b ∈ B, G.Adj a b)) :
    (Fintype.card V : ℝ) ^ (1 - τ) * (A.card : ℝ) ^ τ <
      (Fintype.card V : ℝ) - (B.card : ℝ) := by
  have hn : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast hcrit.card_pos_of_exponent_pos hτ
  exact rpow_pressure_amplifier hτ hτ1 hn (Nat.cast_nonneg A.card)
    (Nat.cast_nonneg B.card) (by exact_mod_cast B.card_le_univ)
    (hcrit.pure_pair_pressure_of_nonempty A B hA hB hdis hpure)

/-- A pure second side covering all but at most `E` vertices gives a strict
amplified bound by `E`; all cardinalities and the cover condition are real-valued. -/
theorem IsExponentCritical.pure_pair_near_cover_of_cover [Fintype V]
    {G : SimpleGraph V} {τ E : ℝ} (hcrit : IsExponentCritical G τ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (A B : Finset V)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdis : Disjoint A B)
    (hpure : (∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) ∨
      (∀ a ∈ A, ∀ b ∈ B, G.Adj a b))
    (hcover : (Fintype.card V : ℝ) - E ≤ (B.card : ℝ)) :
    (Fintype.card V : ℝ) ^ (1 - τ) * (A.card : ℝ) ^ τ < E := by
  exact (hcrit.pure_pair_near_cover hτ hτ1 A B hA hB hdis hpure).trans_le
    (by linarith)

/-- When `0 < τ < 1`, a nonempty pure first side and a cover-error bound
also impose an upper bound on the ambient vertex count. -/
theorem IsExponentCritical.pure_pair_order_lt_of_cover [Fintype V]
    {G : SimpleGraph V} {τ E : ℝ} (hcrit : IsExponentCritical G τ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (A B : Finset V)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdis : Disjoint A B)
    (hpure : (∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) ∨
      (∀ a ∈ A, ∀ b ∈ B, G.Adj a b))
    (hcover : (Fintype.card V : ℝ) - E ≤ (B.card : ℝ)) :
    (Fintype.card V : ℝ) < (E / (A.card : ℝ) ^ τ) ^ (1 / (1 - τ)) := by
  have hn : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast hcrit.card_pos_of_exponent_pos hτ
  have ha : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  exact rpow_pressure_order_lt_of_cover hτ hτ1 hn ha (Nat.cast_nonneg B.card)
    (by exact_mod_cast B.card_le_univ) hcover
    (hcrit.pure_pair_pressure_of_nonempty A B hA hB hdis hpure)

end Erdos61Research
