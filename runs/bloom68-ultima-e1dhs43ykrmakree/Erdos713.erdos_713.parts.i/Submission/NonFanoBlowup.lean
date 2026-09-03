import Submission.NonFanoAvoidance

/-!
# Capacity-two non-Fano avoidance

Development only. The lower-bound constructions here do not supply the
unrestricted upper bound required to resolve `Spec.lean`.
-/

open Matrix

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 1000

namespace Erdos713

private def coreLinePoints : Fin 6 → Finset (Fin 7) :=
  ![{0, 1, 4}, {2, 3, 4}, {0, 2, 5}, {1, 3, 5}, {0, 3, 6}, {1, 2, 6}]

/-- No three distinct arguments have the same image. -/
def CapacityTwo {A V : Type*} (f : A → V) : Prop :=
  ∀ a b c, a ≠ b → a ≠ c → b ≠ c → f a = f b → f a ≠ f c

private theorem pointCollapseWitness : ∀ a b : Fin 7, a ≠ b →
    ∃ (i j k : Fin 6) (c d : Fin 7),
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (a ∈ coreLinePoints i ∨ b ∈ coreLinePoints i) ∧
      (a ∈ coreLinePoints j ∨ b ∈ coreLinePoints j) ∧
      (a ∈ coreLinePoints k ∨ b ∈ coreLinePoints k) ∧
      c ≠ a ∧ c ≠ b ∧ c ∈ coreLinePoints i ∧ c ∈ coreLinePoints j ∧
      d ≠ a ∧ d ≠ b ∧ d ∈ coreLinePoints i ∧ d ∈ coreLinePoints k := by
  decide

private theorem lineCollapseWitness : ∀ i j : Fin 6, i ≠ j →
    ∃ (k : Fin 6) (a b : Fin 7), i ≠ k ∧ j ≠ k ∧ a ≠ b ∧
      a ∈ coreLinePoints i ∧ b ∈ coreLinePoints j ∧
      a ∈ coreLinePoints k ∧ b ∈ coreLinePoints k := by
  decide

/-- Capacity two and unique joins force injectivity on the seven point roles. -/
private theorem core_points_injective {V : Type*} (R : V → V → Prop)
    (hU : ∀ a b x y, a ≠ b → R a x → R b x → R a y → R b y → x = y)
    (p : Fin 7 → V) (l : Fin 6 → V)
    (hp : CapacityTwo p) (hl : CapacityTwo l)
    (hinc : ∀ i j, j ∈ coreLinePoints i → R (p j) (l i)) :
    Function.Injective p := by
  intro a b hab
  by_contra hne
  obtain ⟨i, j, k, c, d, hij, hik, hjk, hi, hj, hk,
    hca, hcb, hci, hcj, hda, hdb, hdi, hdk⟩ := pointCollapseWitness a b hne
  have hcenter : ∀ t, (a ∈ coreLinePoints t ∨ b ∈ coreLinePoints t) → R (p a) (l t) := by
    intro t ht
    rcases ht with ht | ht
    · exact hinc t a ht
    · rw [hab]
      exact hinc t b ht
  have heij : l i = l j := hU (p a) (p c) (l i) (l j)
    (hp a b c hne hca.symm hcb.symm hab)
    (hcenter i hi) (hinc i c hci) (hcenter j hj) (hinc j c hcj)
  have heik : l i = l k := hU (p a) (p d) (l i) (l k)
    (hp a b d hne hda.symm hdb.symm hab)
    (hcenter i hi) (hinc i d hdi) (hcenter k hk) (hinc k d hdk)
  exact hl i j k hij hik hjk heij heik

/-- With distinct points, capacity two also forces distinctness of the six sidelines. -/
private theorem core_lines_injective {V : Type*} (R : V → V → Prop)
    (hU : ∀ a b x y, a ≠ b → R a x → R b x → R a y → R b y → x = y)
    (p : Fin 7 → V) (l : Fin 6 → V)
    (hp : Function.Injective p) (hl : CapacityTwo l)
    (hinc : ∀ i j, j ∈ coreLinePoints i → R (p j) (l i)) :
    Function.Injective l := by
  intro i j he
  by_contra hne
  obtain ⟨k, a, b, hik, hjk, hab, hai, hbj, hak, hbk⟩ := lineCollapseWitness i j hne
  have hb : R (p b) (l i) := by rw [he]; exact hinc j b hbj
  have hek : l i = l k := hU (p a) (p b) (l i) (l k)
    (fun h => hab (hp h)) (hinc i a hai) hb (hinc k a hak) (hinc k b hbk)
  exact hl i j k hne hik hjk he hek

/-- Two distinct projective points have at most one orthogonal projective point
in common. Self-incidences are allowed in this auxiliary statement. -/
theorem polarity_orthogonal_unique {K : Type*} [Field K]
    (a b x y : PolarityPoint K) (hab : a ≠ b)
    (hax : polarityVector a ⬝ᵥ polarityVector x = 0)
    (hbx : polarityVector b ⬝ᵥ polarityVector x = 0)
    (hay : polarityVector a ⬝ᵥ polarityVector y = 0)
    (hby : polarityVector b ⬝ᵥ polarityVector y = 0) : x = y := by
  obtain ⟨r, hr⟩ := exists_smul_cross_of_orthogonal
    (polarityVector a) (polarityVector b) (polarityVector x)
    (polarityVector_cross_ne_zero a b hab) hax hbx
  obtain ⟨s, hs⟩ := exists_smul_cross_of_orthogonal
    (polarityVector a) (polarityVector b) (polarityVector y)
    (polarityVector_cross_ne_zero a b hab) hay hby
  by_contra hxy
  apply polarityVector_cross_ne_zero x y hxy
  simp [hr, hs, map_smul, cross_self]


private theorem capacityTwo_comp {A B V : Type*} {f : A → V}
    (hf : CapacityTwo f) (g : B → A) (hg : Function.Injective g) :
    CapacityTwo (f ∘ g) := by
  intro a b c hab hac hbc he
  exact hf (g a) (g b) (g c) (fun h => hab (hg h)) (fun h => hac (hg h))
    (fun h => hbc (hg h)) he

private def sideIndex (i : Fin 6) : Fin 9 := ⟨i, by omega⟩

private theorem sideIndex_injective : Function.Injective sideIndex := by decide

private theorem core_membership : ∀ (i : Fin 6) (j : Fin 7),
    j ∈ coreLinePoints i ↔ j ∈ homogeneousNonFanoLinePoints (sideIndex i) := by decide

private theorem cross_cross_common_right {R : Type*} [CommRing R]
    (u v w : Fin 3 → R) :
    (u ⨯₃ w) ⨯₃ (v ⨯₃ w) = (u ⬝ᵥ (v ⨯₃ w)) • w := by
  ext i
  fin_cases i <;> simp only [cross_apply, vec3_dotProduct] <;> dsimp <;> ring

/-- Even allowing two representatives of each projective point or line does not
allow the full non-Fano incidence configuration in characteristic two. -/
theorem nonFano_not_capacityTwo_orthogonal {K : Type*} [Field K] [CharP K 2]
    (p : Fin 7 → PolarityPoint K) (l : Fin 9 → PolarityPoint K)
    (hp : CapacityTwo p) (hl : CapacityTwo l)
    (hinc : ∀ i j, j ∈ homogeneousNonFanoLinePoints i →
      polarityVector (p j) ⬝ᵥ polarityVector (l i) = 0) : False := by
  let R : PolarityPoint K → PolarityPoint K → Prop :=
    fun u v => polarityVector u ⬝ᵥ polarityVector v = 0
  let lc : Fin 6 → PolarityPoint K := l ∘ sideIndex
  have hlc : CapacityTwo lc := capacityTwo_comp hl sideIndex sideIndex_injective
  have hic : ∀ i j, j ∈ coreLinePoints i → R (p j) (lc i) := by
    intro i j h
    exact hinc (sideIndex i) j ((core_membership i j).mp h)
  have hpi : Function.Injective p :=
    core_points_injective R polarity_orthogonal_unique p lc hp hlc hic
  have hli : Function.Injective lc :=
    core_lines_injective R polarity_orthogonal_unique p lc hpi hlc hic
  have hpx : ∀ i j, i ≠ j → polarityVector (p i) ⨯₃ polarityVector (p j) ≠ 0 :=
    fun i j h => polarityVector_cross_ne_zero _ _ (fun he => h (hpi he))
  have h01 : polarityVector (l 0) ⨯₃ polarityVector (l 1) ≠ 0 :=
    polarityVector_cross_ne_zero _ _ (hli.ne (by decide : (0 : Fin 6) ≠ 1))
  have h23 : polarityVector (l 2) ⨯₃ polarityVector (l 3) ≠ 0 :=
    polarityVector_cross_ne_zero _ _ (hli.ne (by decide : (2 : Fin 6) ≠ 3))
  have h45 : polarityVector (l 4) ⨯₃ polarityVector (l 5) ≠ 0 :=
    polarityVector_cross_ne_zero _ _ (hli.ne (by decide : (4 : Fin 6) ≠ 5))
  have hdiag := homogeneousNonFano_diagonal_zero
    (polarityVector ∘ p) (polarityVector ∘ l) hpx h01 h23 h45 hinc
  change polarityVector (p 4) ⬝ᵥ
    (polarityVector (p 5) ⨯₃ polarityVector (p 6)) = 0 at hdiag
  obtain ⟨r6, hr6⟩ := exists_smul_cross_of_orthogonal
    (polarityVector (p 4)) (polarityVector (p 5)) (polarityVector (l 6))
    (hpx 4 5 (by decide)) (hinc 6 4 (by decide)) (hinc 6 5 (by decide))
  obtain ⟨r7, hr7⟩ := exists_smul_cross_of_orthogonal
    (polarityVector (p 4)) (polarityVector (p 6)) (polarityVector (l 7))
    (hpx 4 6 (by decide)) (hinc 7 4 (by decide)) (hinc 7 6 (by decide))
  obtain ⟨r8, hr8⟩ := exists_smul_cross_of_orthogonal
    (polarityVector (p 5)) (polarityVector (p 6)) (polarityVector (l 8))
    (hpx 5 6 (by decide)) (hinc 8 5 (by decide)) (hinc 8 6 (by decide))
  have h67 : l 6 = l 7 := by
    by_contra h
    apply polarityVector_cross_ne_zero _ _ h
    simp [hr6, hr7, map_smul, cross_cross_common_left, hdiag]
  have h78 : l 7 = l 8 := by
    by_contra h
    apply polarityVector_cross_ne_zero _ _ h
    simp [hr7, hr8, map_smul, cross_cross_common_right, hdiag]
  exact hl 7 6 8 (by decide) (by decide) (by decide) h67.symm h78

private theorem capacityTwo_fst {A V : Type*} (f : A → V × Fin 2)
    (hf : Function.Injective f) : CapacityTwo (Prod.fst ∘ f) := by
  intro a b c hab hac hbc heab heac
  have hs : ∀ i j, (f i).1 = (f j).1 → i ≠ j → (f i).2 ≠ (f j).2 := by
    intro i j he hij hs
    exact hij (hf (Prod.ext he hs))
  have h01 : (f a).2.val ≠ (f b).2.val :=
    fun h => hs a b heab hab (Fin.ext h)
  have h02 : (f a).2.val ≠ (f c).2.val :=
    fun h => hs a c heac hac (Fin.ext h)
  have h12 : (f b).2.val ≠ (f c).2.val :=
    fun h => hs b c (heab.symm.trans heac) hbc (Fin.ext h)
  omega

private def pointIndex (i : Fin 7) : Fin 16 := ⟨i, by omega⟩
private def lineIndex (i : Fin 9) : Fin 16 := ⟨i + 7, by omega⟩

private theorem pointIndex_injective : Function.Injective pointIndex := by decide
private theorem lineIndex_injective : Function.Injective lineIndex := by decide

private theorem role_membership : ∀ (i : Fin 9) (j : Fin 7),
    j ∈ homogeneousNonFanoLinePoints i ↔ nonFanoGraph.Adj (pointIndex j) (lineIndex i) := by
  decide

/-- Replace every polarity-graph vertex by two independent twins. -/
def doubledPolarityGraph (K : Type*) [Field K] :
    SimpleGraph (PolarityPoint K × Fin 2) := (polarityGraph K).comap Prod.fst

instance {K : Type*} [Field K] [DecidableEq K] : DecidableRel (doubledPolarityGraph K).Adj :=
  inferInstanceAs (DecidableRel ((polarityGraph K).comap
    (Prod.fst : PolarityPoint K × Fin 2 → PolarityPoint K)).Adj)

/-- The doubled loopless polarity graph is still free of the full non-Fano graph. -/
theorem nonFanoGraph_free_doubledPolarityGraph (K : Type*) [Field K] [CharP K 2] :
    nonFanoGraph.Free (doubledPolarityGraph K) := by
  rintro ⟨f⟩
  have hc := capacityTwo_fst f f.injective
  apply nonFano_not_capacityTwo_orthogonal
    ((Prod.fst ∘ f) ∘ pointIndex) ((Prod.fst ∘ f) ∘ lineIndex)
    (capacityTwo_comp hc pointIndex pointIndex_injective)
    (capacityTwo_comp hc lineIndex lineIndex_injective)
  intro i j h
  exact (f.toHom.map_adj ((role_membership i j).mp h)).2


open scoped BigOperators

theorem card_doubledPolarityPoint (K : Type*) [Field K] [Fintype K] :
    Fintype.card (PolarityPoint K × Fin 2) =
      2 * ((Fintype.card K)^2 + Fintype.card K + 1) := by
  rw [Fintype.card_prod, Fintype.card_fin, card_polarityPoint, Nat.mul_comm]

theorem doubledPolarity_degree (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (u : PolarityPoint K × Fin 2) :
    (doubledPolarityGraph K).degree u = 2 * (polarityGraph K).degree u.1 := by
  have hb : (polarityGraph K).degree u.1 =
      ∑ v : PolarityPoint K, (if (polarityGraph K).Adj u.1 v then 1 else 0 : ℕ) := by
    simpa using (polarityGraph K).degree_eq_sum_if_adj (R := ℕ) u.1
  calc
    _ = ∑ v : PolarityPoint K × Fin 2,
        (if (polarityGraph K).Adj u.1 v.1 then 1 else 0 : ℕ) := by
      simpa only [doubledPolarityGraph, SimpleGraph.comap_adj, Nat.cast_id] using
        (doubledPolarityGraph K).degree_eq_sum_if_adj (R := ℕ) u
    _ = 2 * ∑ v : PolarityPoint K, (if (polarityGraph K).Adj u.1 v then 1 else 0 : ℕ) := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two, two_mul, Finset.sum_add_distrib]
    _ = _ := by rw [hb]

/-- Doubling multiplies the edge count by four. -/
theorem doubledPolarity_edge_count (K : Type*) [Field K] [CharP K 2]
    [Fintype K] [DecidableEq K] :
    (doubledPolarityGraph K).edgeFinset.card =
      2 * Fintype.card K * (Fintype.card K + 1)^2 := by
  have h : (∑ u : PolarityPoint K × Fin 2, (doubledPolarityGraph K).degree u) =
      4 * ∑ v : PolarityPoint K, (polarityGraph K).degree v := by
    simp_rw [doubledPolarity_degree]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    omega
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges,
    SimpleGraph.sum_degrees_eq_twice_card_edges, polarity_twice_edge_count] at h
  nlinarith [h]

/-- The sharper lower bound from doubled polarity graphs, for the ordinary
single-forbidden-graph extremal number. -/
theorem nonFano_extremal_lower_doubled_finiteField (K : Type*) [Field K] [CharP K 2]
    [Fintype K] :
    2 * Fintype.card K * (Fintype.card K + 1)^2 ≤
      SimpleGraph.extremalNumber (2 * ((Fintype.card K)^2 + Fintype.card K + 1))
        nonFanoGraph := by
  classical
  have h := SimpleGraph.card_edgeFinset_le_extremalNumber
    (nonFanoGraph_free_doubledPolarityGraph K)
  rwa [card_doubledPolarityPoint, doubledPolarity_edge_count] at h

/-- The doubled construction exists at every positive power of two. -/
theorem nonFano_extremal_lower_doubled_power_two (k : ℕ) (hk : k ≠ 0) :
    2 * 2^k * (2^k + 1)^2 ≤
      SimpleGraph.extremalNumber (2 * ((2^k)^2 + 2^k + 1)) nonFanoGraph := by
  letI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 2 k) = 2^k := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 k hk
  simpa only [hc] using nonFano_extremal_lower_doubled_finiteField (GaloisField 2 k)

end Erdos713

#print axioms Erdos713.polarity_orthogonal_unique

#print axioms Erdos713.nonFano_not_capacityTwo_orthogonal
#print axioms Erdos713.nonFanoGraph_free_doubledPolarityGraph

#print axioms Erdos713.card_doubledPolarityPoint
#print axioms Erdos713.doubledPolarity_degree
#print axioms Erdos713.doubledPolarity_edge_count
#print axioms Erdos713.nonFano_extremal_lower_doubled_finiteField
#print axioms Erdos713.nonFano_extremal_lower_doubled_power_two
