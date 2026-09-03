import Submission.PolynomialCertificate

/-!
# Proper-quotient obstructions in small blowups

This file never assumes that an ordinary `H`-free graph has an `H`-free
blowup. It instead quantifies the obstructions to that assertion.

A copy of `H` in the `k`-fold independent blowup projects to a homomorphism
into the base graph with fibers of size at most `k`. If the base is
`H`-free, that projection is necessarily noninjective. Its image is thus
a proper ordinary quotient of `H`, and its projected edge set has at most
`e(H)` edges.
-/

open SimpleGraph Filter Asymptotics
open scoped Topology

namespace Erdos713Blowup

universe u v

variable {V : Type u} {W : Type v}

/-- Replace each vertex by `k` independent clones and each edge by a complete
bipartite graph between the two clone sets. This is not a tensor product. -/
def blowup (G : SimpleGraph V) (k : ℕ) : SimpleGraph (V × Fin k) where
  Adj x y := G.Adj x.1 y.1
  symm := by intros a b h; exact h.symm
  loopless := fun x => G.loopless x.1

instance {G : SimpleGraph V} [DecidableRel G.Adj] (k : ℕ) :
    DecidableRel (blowup G k).Adj := fun _ _ => inferInstanceAs (Decidable (G.Adj _ _))

@[simp]
lemma blowup_adj (G : SimpleGraph V) (k : ℕ) (x y : V × Fin k) :
    (blowup G k).Adj x y ↔ G.Adj x.1 y.1 := Iff.rfl

lemma blowup_mono {G F : SimpleGraph V} (h : F ≤ G) (k : ℕ) :
    blowup F k ≤ blowup G k := fun _ _ hxy => h hxy

/-- Project a copy in a blowup to a (possibly noninjective) homomorphism. -/
def projectHom {H : SimpleGraph W} {G : SimpleGraph V} {k : ℕ}
    (f : H.Copy (blowup G k)) : H →g G where
  toFun x := (f x).1
  map_rel' h := f.toHom.map_adj h

@[simp]
lemma projectHom_apply {H : SimpleGraph W} {G : SimpleGraph V} {k : ℕ}
    (f : H.Copy (blowup G k)) (x : W) : projectHom f x = (f x).1 := rfl

/-- Ordinary injective freeness forces every projected copy to be a proper
quotient. This is the point where injectivity, not homomorphism-freeness,
is essential. -/
theorem projectHom_not_injective {H : SimpleGraph W} {G : SimpleGraph V} {k : ℕ}
    (hG : H.Free G) (f : H.Copy (blowup G k)) :
    ¬ Function.Injective (projectHom f) := fun hi => hG ⟨(projectHom f).toCopy hi⟩

open scoped Classical in
/-- The fibers of a projected copy have size at most the blowup factor. -/
theorem projectHom_fiber_card_le [Fintype W] {H : SimpleGraph W}
    {G : SimpleGraph V} {k : ℕ} (f : H.Copy (blowup G k)) (x : V) :
    Fintype.card {w : W // projectHom f w = x} ≤ k := by
  classical
  let g : {w : W // projectHom f w = x} → Fin k := fun w => (f w.1).2
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply f.injective
    exact Prod.ext (a.2.trans b.2.symm) hab
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective g hg

/-- Neighbor sets in a blowup are products of base neighbor sets with the
clone index type. -/
def neighborEquiv (G : SimpleGraph V) (k : ℕ) (x : V × Fin k) :
    (blowup G k).neighborSet x ≃ G.neighborSet x.1 × Fin k where
  toFun y := (⟨y.1.1, y.2⟩, y.1.2)
  invFun y := ⟨(y.1.1, y.2), y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
lemma degree_blowup [Fintype V] (G : SimpleGraph V) (k : ℕ) (x : V × Fin k) :
    (blowup G k).degree x = G.degree x.1 * k := by
  classical
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (neighborEquiv G k x),
    Fintype.card_prod, Fintype.card_fin, card_neighborSet_eq_degree]

open scoped Classical in
/-- A `k`-fold independent blowup has exactly `k²` times as many edges. -/
lemma card_edges_blowup [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (blowup G k).edgeFinset.card = k ^ 2 * G.edgeFinset.card := by
  classical
  have h := (blowup G k).sum_degrees_eq_twice_card_edges
  simp only [degree_blowup, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  simp_rw [mul_left_comm k] at h
  rw [← Finset.sum_mul] at h
  rw [G.sum_degrees_eq_twice_card_edges] at h
  nlinarith


/-- A finite family of nonempty sets has a disjoint packing whose union
meets every member of the family. This is maximality, not optimality. -/
lemma exists_disjoint_packing_hitting_all {I E : Type*} [Fintype I] [DecidableEq E]
    (f : I → Finset E) (hf : ∀ i, (f i).Nonempty) :
    ∃ P : Finset I, (P : Set I).PairwiseDisjoint f ∧
      ∀ i, ¬ Disjoint (f i) (P.biUnion f) := by
  classical
  let C : Finset (Finset I) := Finset.univ.filter (fun P => (P : Set I).PairwiseDisjoint f)
  have hC : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨P, hPC, hmax⟩ := Finset.exists_max_image C Finset.card hC
  have hP : (P : Set I).PairwiseDisjoint f := (Finset.mem_filter.mp hPC).2
  refine ⟨P, hP, ?_⟩
  intro i hdis
  have hi : i ∉ P := by
    intro hi
    obtain ⟨x, hx⟩ := hf i
    exact Finset.disjoint_left.mp hdis hx (Finset.mem_biUnion.mpr ⟨i, hi, hx⟩)
  have hins : ((insert i P : Finset I) : Set I).PairwiseDisjoint f := by
    rw [Finset.coe_insert]
    apply hP.insert
    intro j hj _
    apply Finset.disjoint_of_subset_right _ hdis
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨j, hj, hx⟩
  have hmem : insert i P ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hins⟩
  have h := hmax (insert i P) hmem
  rw [Finset.card_insert_of_notMem hi] at h
  omega

section Finite

variable [Fintype V] [Fintype W]
variable {H : SimpleGraph W} {G : SimpleGraph V} {k : ℕ}

open scoped Classical in
/-- The edge set of the ordinary quotient associated to a copy in a blowup. -/
noncomputable def projectedEdges (f : H.Copy (blowup G k)) : Finset (Sym2 V) :=
  H.edgeFinset.image (Sym2.map (projectHom f))

open scoped Classical in
lemma projectedEdges_subset (f : H.Copy (blowup G k)) :
    projectedEdges f ⊆ G.edgeFinset := by
  classical
  rintro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  exact mem_edgeFinset.mpr ((projectHom f).map_mem_edgeSet (mem_edgeFinset.mp hd))

omit [Fintype V] in
open scoped Classical in
lemma card_projectedEdges_le (f : H.Copy (blowup G k)) :
    (projectedEdges f).card ≤ H.edgeFinset.card := Finset.card_image_le

omit [Fintype V] in
open scoped Classical in
lemma projectedEdges_nonempty (hH : H.edgeFinset.Nonempty) (f : H.Copy (blowup G k)) :
    (projectedEdges f).Nonempty := hH.image _

omit [Fintype W] in
open scoped Classical in
/-- Every subgraph whose blowup is `H`-free satisfies the correctly rescaled
ordinary extremal bound. No closure of `H`-freeness under blowups is claimed. -/
theorem edge_bound_of_free_blowup (F : SimpleGraph V) (hF : H.Free (blowup F k)) :
    k ^ 2 * F.edgeFinset.card ≤ extremalNumber (k * Fintype.card V) H := by
  classical
  have h := card_edgeFinset_le_extremalNumber hF
  simpa only [card_edges_blowup, Fintype.card_prod, Fintype.card_fin, mul_comm] using h


set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- Pack projected copies edge-disjointly. If the base is `H`-free, every
member is a proper quotient with fibers at most `k`. Deleting the union
of these projected edge sets makes the blowup `H`-free, giving the displayed
finite extremal bound. -/
theorem exists_projected_packing (hH : H.edgeFinset.Nonempty) (hG : H.Free G) :
    ∃ P : Finset (H.Copy (blowup G k)),
      (P : Set (H.Copy (blowup G k))).PairwiseDisjoint projectedEdges ∧
      (∀ f ∈ P, ¬ Function.Injective (projectHom f)) ∧
      H.Free (blowup (G.deleteEdges (P.biUnion projectedEdges : Set (Sym2 V))) k) ∧
      k ^ 2 * G.edgeFinset.card ≤ extremalNumber (k * Fintype.card V) H +
        k ^ 2 * (P.biUnion projectedEdges).card ∧
      k ^ 2 * G.edgeFinset.card ≤ extremalNumber (k * Fintype.card V) H +
        k ^ 2 * (H.edgeFinset.card * P.card) := by
  classical
  obtain ⟨P, hP, hhit⟩ := exists_disjoint_packing_hitting_all
    (projectedEdges (H := H) (G := G) (k := k)) (projectedEdges_nonempty hH)
  let D := P.biUnion projectedEdges
  have hD : D ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨f, _, hf⟩ := Finset.mem_biUnion.mp he
    exact projectedEdges_subset f hf
  have hDcard : D.card ≤ P.card * H.edgeFinset.card :=
    Finset.card_biUnion_le_card_mul P projectedEdges H.edgeFinset.card
      (fun f _ => card_projectedEdges_le f)
  let F := G.deleteEdges (D : Set (Sym2 V))
  letI : DecidableRel F.Adj := fun _ _ => Classical.propDecidable _
  have hF : H.Free (blowup F k) := by
    rintro ⟨f⟩
    let f' : H.Copy (blowup G k) :=
      (Copy.ofLE _ _ (blowup_mono (G.deleteEdges_le D) k)).comp f
    apply hhit f'
    apply Finset.disjoint_left.mpr
    intro e he heD
    have heF : e ∈ F.edgeSet := mem_edgeFinset.mp
      (projectedEdges_subset f (show e ∈ projectedEdges f from he))
    have heD' : e ∉ D := by
      change e ∈ (G.deleteEdges (D : Set (Sym2 V))).edgeSet at heF
      rw [edgeSet_deleteEdges] at heF
      exact heF.2
    exact heD' heD
  have hbound := edge_bound_of_free_blowup F hF
  have hsplit : F.edgeFinset.card + D.card = G.edgeFinset.card := by
    change (G.deleteEdges (D : Set (Sym2 V))).edgeFinset.card + D.card = _
    rw [edgeFinset_deleteEdges, Finset.card_sdiff_of_subset hD]
    exact Nat.sub_add_cancel (Finset.card_le_card hD)
  have hcover : k ^ 2 * G.edgeFinset.card ≤
      extremalNumber (k * Fintype.card V) H + k ^ 2 * D.card := by
    rw [← hsplit, Nat.mul_add]
    exact Nat.add_le_add_right hbound _
  refine ⟨P, hP, fun f _ => projectHom_not_injective hG f, hF, hcover, ?_⟩
  calc
    k ^ 2 * G.edgeFinset.card = k ^ 2 * F.edgeFinset.card + k ^ 2 * D.card := by
      rw [← hsplit, Nat.mul_add]
    _ ≤ extremalNumber (k * Fintype.card V) H +
        k ^ 2 * (P.card * H.edgeFinset.card) :=
      Nat.add_le_add hbound (Nat.mul_le_mul_left _ hDcard)
    _ = extremalNumber (k * Fintype.card V) H +
        k ^ 2 * (H.edgeFinset.card * P.card) := by ring

end Finite


/-- Normalize a fixed integer rescaling of a pure power asymptotic at the
original scale. This uses limits, not assumptions about discrete derivatives. -/
lemma tendsto_rescaled_power {f : ℕ → ℝ} {a c : ℝ}
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a)) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => f (k * n) / (n : ℝ) ^ a) atTop (𝓝 (c * (k : ℝ) ^ a)) := by
  have hkn : Tendsto (fun n : ℕ => k * n) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun N => ⟨N, fun n hn => by nlinarith⟩)
  have h := ((Erdos713Polynomial.tendsto_div_rpow_of_equivalent hf).comp hkn).mul_const
    ((k : ℝ) ^ a)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hkp : (k : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hk' a).ne'
  have hnp : (n : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hn' a).ne'
  change f (k * n) / ((k * n : ℕ) : ℝ) ^ a * (k : ℝ) ^ a = _
  rw [Nat.cast_mul, Real.mul_rpow hk'.le hn'.le]
  field_simp

open scoped Classical in
/-- Every coefficient strictly below the first-order lower bound from the
finite packing inequality is eventually attained by a packing of proper
bounded-fiber quotients.
For `k ≥ 2`, `a < 2`, and `c > 0`, the limiting coefficient is positive. -/
theorem eventually_large_projected_packing [Fintype W] (H : SimpleGraph W)
    (hH : H.edgeFinset.Nonempty) {a c : ℝ}
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a))
    {k : ℕ} (hk : 0 < k) {b : ℝ}
    (hb : b < (((k : ℝ) ^ 2 - (k : ℝ) ^ a) * c /
      ((k : ℝ) ^ 2 * (H.edgeFinset.card : ℝ)))) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), H.Free G →
      G.edgeFinset.card = extremalNumber n H →
      ∃ P : Finset (H.Copy (blowup G k)),
        (P : Set (H.Copy (blowup G k))).PairwiseDisjoint projectedEdges ∧
        (∀ f ∈ P, ¬ Function.Injective (projectHom f)) ∧
        b * (n : ℝ) ^ a ≤ (P.card : ℝ) := by
  classical
  let D : ℝ := (k : ℝ) ^ 2 * (H.edgeFinset.card : ℝ)
  have hD : 0 < D := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hH' : 0 < (H.edgeFinset.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hH
    dsimp [D]
    positivity
  have ht : Tendsto (fun n : ℕ =>
      ((k : ℝ) ^ 2 * ((extremalNumber n H : ℝ) / (n : ℝ) ^ a) -
        (extremalNumber (k * n) H : ℝ) / (n : ℝ) ^ a) / D) atTop
        (𝓝 ((((k : ℝ) ^ 2 - (k : ℝ) ^ a) * c) / D)) := by
    convert (((Erdos713Polynomial.tendsto_div_rpow_of_equivalent hf).const_mul
      ((k : ℝ) ^ 2)).sub (tendsto_rescaled_power hf hk)).div_const D using 1
    rw [sub_mul, mul_comm ((k : ℝ) ^ a) c]
  filter_upwards [ht.eventually_const_lt hb, eventually_gt_atTop 0] with n hn hn0
  intro G hG hmax
  obtain ⟨P, hP, hproper, _, _, hbound⟩ := exists_projected_packing (k := k) hH hG
  refine ⟨P, hP, hproper, ?_⟩
  have hbound' : (k : ℝ) ^ 2 * (extremalNumber n H : ℝ) ≤
      (extremalNumber (k * n) H : ℝ) + D * (P.card : ℝ) := by
    rw [Fintype.card_fin, hmax] at hbound
    dsimp [D]
    rw [mul_assoc]
    exact_mod_cast hbound
  have hnp : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos (by exact_mod_cast hn0) a
  have hn' := (lt_div_iff₀ hD).mp hn
  have hfrac : (k : ℝ) ^ 2 * ((extremalNumber n H : ℝ) / (n : ℝ) ^ a) -
      (extremalNumber (k * n) H : ℝ) / (n : ℝ) ^ a =
      ((k : ℝ) ^ 2 * (extremalNumber n H : ℝ) -
        (extremalNumber (k * n) H : ℝ)) / (n : ℝ) ^ a := by ring
  rw [hfrac] at hn'
  have hgain := (lt_div_iff₀ hnp).mp hn'
  apply (mul_le_mul_iff_right₀ hD).mp
  calc
    D * (b * (n : ℝ) ^ a) = (b * D) * (n : ℝ) ^ a := by ring
    _ ≤ (k : ℝ) ^ 2 * (extremalNumber n H : ℝ) -
        (extremalNumber (k * n) H : ℝ) := hgain.le
    _ ≤ D * (P.card : ℝ) := by linarith

open scoped Classical in
/-- The exact leading coefficient gives a genuinely positive packing bound
already for a twofold blowup. A large factor depending on unknown Theta
constants is unnecessary. -/
lemma packing_coefficient_pos [Fintype W] (H : SimpleGraph W)
    (hH : H.edgeFinset.Nonempty) {k : ℕ} (hk : 2 ≤ k)
    {a c : ℝ} (ha : a < 2) (hc : 0 < c) :
    0 < (((k : ℝ) ^ 2 - (k : ℝ) ^ a) * c /
      ((k : ℝ) ^ 2 * (H.edgeFinset.card : ℝ))) := by
  classical
  have hk' : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hp : (k : ℝ) ^ a < (k : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_lt_rpow_of_exponent_lt hk' ha
  have hH' : 0 < (H.edgeFinset.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hH
  exact div_pos (mul_pos (sub_pos.mpr hp) hc) (mul_pos (sq_pos_of_pos (by linarith)) hH')

end Erdos713Blowup

#print axioms Erdos713Blowup.projectHom_not_injective
#print axioms Erdos713Blowup.projectHom_fiber_card_le
#print axioms Erdos713Blowup.card_edges_blowup
#print axioms Erdos713Blowup.edge_bound_of_free_blowup
#print axioms Erdos713Blowup.exists_projected_packing
#print axioms Erdos713Blowup.eventually_large_projected_packing
#print axioms Erdos713Blowup.packing_coefficient_pos
