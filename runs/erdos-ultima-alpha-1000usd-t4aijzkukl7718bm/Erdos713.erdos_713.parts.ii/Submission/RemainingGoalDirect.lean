import FormalConjecturesUtil
import Submission.NearOptimalExpanders
import Submission.LinearRobustCopies

/-! Direct final-goal search; not a completed proof. -/
open Filter SimpleGraph Asymptotics

namespace Erdos713
set_option maxHeartbeats 2000000

open scoped Classical in
/--
Must $\alpha$ be rational?

The same nondegeneracy condition on $G$ is used as in part (i). Rationality means that the real
number $\alpha$ lies in the image of the canonical embedding $\mathbb{Q}\to\mathbb{R}$.
-/
theorem erdos_713.parts.ii :
    ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
      ∀ α c : ℝ, α ∈ Set.Ico 1 2 → 0 < c →
        Asymptotics.IsEquivalent atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => c * (n : ℝ) ^ α) →
        α ∈ Set.range ((↑) : ℚ → ℝ) := by
  intro q G hBipartite hEdges α c hα hc hAsymptotic
  by_cases hBlockRates : Erdos713ActualBlocks.BlockRates G
  · exact Erdos713ActualBlocks.rational_of_blocks G hBlockRates hα.1 hc.ne' hAsymptotic
  have hNoAtomRates : ¬ Erdos713EdgeSeparators.AtomRates G :=
    fun h => hBlockRates (Erdos713EdgeSeparators.block_rates_of_atoms G h)
  by_cases hAssembly : Erdos713CycleAssembly.Assembly G
  · exact hAssembly.rational hα.1 hc.ne' hAsymptotic
  by_cases hSquares : Erdos713Squares.Sandwich G
  · exact hSquares.rational hα.1 hc.ne' hAsymptotic
  by_cases hTheta : Erdos713Theta3.Sandwich G
  · exact hTheta.rational hα.1 hc.ne' hAsymptotic
  by_cases hMixedEdges : Erdos713RootedEdges.MixedBuilt G
  · exact hMixedEdges.rational hα.1 hc.ne' hAsymptotic
  by_cases hCoherentSmall : Erdos713CoherentEdges.SmallSandwich G
  · exact hCoherentSmall.rational hα.1 hc.ne' hAsymptotic
  by_cases hHex : Erdos713EdgeAttachments.Sandwich Erdos713C6.C6 0 1 G
  · refine ⟨4/3,?_⟩
    norm_num
    exact (Erdos713EdgeAttachments.hexagon_sandwich_rate hHex).unique
      (Erdos713Rate.rate_of_asymptotic hα.1 hc.ne' hAsymptotic)
  by_cases hDec : Erdos713EdgeAttachments.Sandwich Erdos713C10.C10 0 1 G
  · refine ⟨6/5,?_⟩
    norm_num
    exact (Erdos713EdgeAttachments.decagon_sandwich_rate hDec).unique
      (Erdos713Rate.rate_of_asymptotic hα.1 hc.ne' hAsymptotic)
  by_cases hLadder : ∃ m : ℕ, 1 ≤ m ∧ Erdos713C4.K22 ⊑ G ∧ G ⊑ Erdos713Ladder.graph m
  · obtain ⟨m,hm,hlo,hhi⟩ := hLadder
    have hr := Erdos713Ladder.rate_of_containment hm hlo hhi
    refine ⟨3/2,?_⟩
    norm_num
    exact (Erdos713Rate.exponent_eq hr hα.1 hc.ne' hAsymptotic).symm
  by_cases hForest : G.IsAcyclic
  · exact Erdos713Forest.rational_exponent_of_acyclic
      q G hForest hEdges α c hα hc hAsymptotic
  by_cases hTwo : ∃ t : ℕ, G ⊑ Erdos713K2t.K2t t
  · obtain ⟨t, hhi⟩ := hTwo
    exact Erdos713K2t.rational_exponent_of_containment
      (Erdos713SmallCore.contains_K22_of_not_acyclic G hForest hhi) hhi hc hAsymptotic
  by_cases hThree : ∃ S : Set (Fin q), G.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3
  · obtain ⟨S, hS, hcard⟩ := hThree
    exact Erdos713ThreeSide.rational_of_small_bipartition G S hS hcard hα.1 hc hAsymptotic
  by_cases hsmall : q ≤ 7
  · exact Erdos713ThreeSide.rational_exponent_all_small_graphs G hBipartite
      (by simpa using hsmall) hα.1 hc hAsymptotic
  by_cases hComponents : ∀ C : G.ConnectedComponent, ∃ S : Set C,
      C.toSimpleGraph.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3
  · exact Erdos713ComponentRates.rational_of_small_component_bipartitions
      G hComponents hα.1 hc.ne' hAsymptotic
  let S : Set (Fin q) := Erdos713Pruning.coreVertices G
  have hPrunes : Erdos713Pruning.PrunesTo G S := Erdos713Pruning.core_prunes G
  by_cases hCoreSmall : Erdos713Pruning.SmallComponents (G.induce S)
  · exact hPrunes.rational_of_small_components hCoreSmall hα.1 hc.ne' hAsymptotic
  have hq : 8 ≤ q := by omega
  by_cases hαone : α = 1
  · exact ⟨1, by simpa using hαone.symm⟩
  have hαgt : 1 < α := lt_of_le_of_ne hα.1 (Ne.symm hαone)
  let H := G.induce S
  have hHAsymptotic : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ α) := hPrunes.asymptotic hαgt hc.ne' hAsymptotic
  have hHBipartite : H.IsBipartite := Colorable.of_hom (Copy.induce G S).toHom hBipartite
  have hHDegree : ∀ v, 2 ≤ Nat.card (H.neighborSet v) := Erdos713Pruning.core_min_degree G
  have hHNoIsolates : ∀ v, ∃ w, H.Adj v w := by
    intro v
    apply (H.degree_pos_iff_exists_adj v).mp
    have hdv := hHDegree v
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using
      (show 0 < Nat.card (H.neighborSet v) by omega)
  have hHNotAssembly : ¬ Erdos713CycleAssembly.Assembly H := fun h =>
    hAssembly (Erdos713CycleAssembly.Assembly.prunes G S hPrunes h)
  have hHRate := Erdos713Rate.rate_of_asymptotic hα.1 hc.ne' hHAsymptotic
  -- Exact transfer holds unless there are containment-incomparable
  -- components at the same attained exponent. The second branch asserts
  -- no exact asymptotic for either component.
  have hHExactComponentAlternative := Erdos713SharpUnion.exact_component_or_incomparable_rates
    H hαgt hc.ne' hHAsymptotic
  -- Exact extremal witnesses can simultaneously have a past power record,
  -- minimum degree, cut expansion, and positive cloning-obstruction mass.
  -- The identified graphs need not be bipartite, and no rate is transferred.
  have hHCloneJoint := Erdos713Cloning.joint_of_asymptotic H
    (r := (1+α)/2) (s := (α+2)/2)
    (by linarith) (by linarith) (by linarith [hα.2]) hc hHAsymptotic
  -- A separate family is extremal among bipartite H-free hosts, not among
  -- all hosts. Its edge count is at least half the ordinary extremal number.
  have hHBipCloneJoint := Erdos713BipExtremal.joint_of_asymptotic H
    (r := (1+α)/2) (s := (α+2)/2)
    (by linarith) (by linarith) (by linarith [hα.2]) hc hHAsymptotic
  -- On another SAME-host witness family, neighbourhood supports have
  -- positive packing mass and bounded multiplicity at roots. This does not
  -- assert disjointness of the entire folded copies or transfer their rates.
  have hHSupportJoint := Erdos713PartialCloning.joint_supports_of_asymptotic H hHNoIsolates
    (r := (1+α)/2) (s := (α+2)/2)
    (by linarith) (by linarith) (by linarith [hα.2]) hc hHAsymptotic
  -- One fixed smaller bipartite quotient carries positive degree-weighted
  -- mass independently of size and exponent tolerance. It occurs at arbitrarily
  -- many distinct roots on the SAME joint witnesses. These are not disjoint
  -- full copies, and no rate or exact asymptotic passes to the quotient.
  have hHFixedBipIdentificationMass :=
    Erdos713FixedFold.uniform_identification_many_roots H hαgt hα.2 hc hHAsymptotic
  -- A stronger, separate SAME-host selection uses degree-square symmetrization.
  -- One quotient, fixed before tolerance/size/minimum-degree targets, occurs
  -- at >= n/(2*|H|^2) distinct roots, carrying >= e(G)/(2*|H|^2) degree mass.
  -- These bipartite-extremal hosts retain joint records and cut expansion.
  -- Full copies may overlap, and the quotient inherits no asserted rate.
  have hHBipSymmetrizedRoots := Erdos713SymmRoots.uniform_identification_vertices H
    hHBipartite hαgt hα.2 hc hHAsymptotic
  -- The attained threshold passes to this component; the exact asymptotic does not.
  obtain ⟨C,hCRate⟩ := Erdos713ComponentRates.exists_component_rate H hαgt hHRate
  -- For this SAME chosen C, failure of exact transfer forces another
  -- threshold component not contained in C.
  have hCExactOrUncontained := Erdos713SharpUnion.component_asymptotic_or_uncontained_rate
    H C hαgt hc.ne' hHAsymptotic
  by_cases hCRational : ∃ r : ℚ, Erdos713Rate.HasRate C.toSimpleGraph (r : ℝ)
  · obtain ⟨r,hr⟩ := hCRational
    exact ⟨r,hr.unique hCRate⟩
  have hCNotAssembly : ¬ Erdos713CycleAssembly.Assembly C.toSimpleGraph :=
    fun h => hCRational h.rate
  have hCNotBlocks : ¬ Erdos713ActualBlocks.BlockRates C.toSimpleGraph :=
    fun h => hCRational (Erdos713ActualBlocks.rate_of_blocks C.toSimpleGraph h)
  -- Matching edge roles are required in the coherent construction. Its
  -- rate equivalence excludes every base with a known rational rate.
  have hCNotCoherent : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) (r : ℚ),
      Erdos713Rate.HasRate F (r : ℝ) →
        ¬ Erdos713CoherentEdges.Sandwich F C.toSimpleGraph := by
    intro k F r hF hSandwich
    exact hCRational ⟨r,hSandwich.rate_iff.mpr hF⟩
  have hC : ¬ ∃ T : Set C, C.toSimpleGraph.IsBipartiteWith T Tᶜ ∧ Nat.card T ≤ 3 := by
    rintro ⟨T,hT,hcard⟩
    exact hCNotAssembly (Erdos713CycleAssembly.Assembly.side C.toSimpleGraph T hT hcard)
  have hCBipartite : C.toSimpleGraph.IsBipartite := hHBipartite.of_hom C.toSimpleGraph_hom
  have hCConnected : C.toSimpleGraph.Connected := C.connected_toSimpleGraph
  -- A separate family is exactly extremal at EVERY size. Summation by
  -- parts, not termwise differentiation, gives a positive lower density
  -- of sizes with quantitative cloning-obstruction mass. These hosts are
  -- not asserted bipartite, regular, or past-record witnesses.
  obtain ⟨vC⟩ := hCConnected.nonempty
  obtain ⟨w,hvw⟩ := hHNoIsolates vC.val
  have hHClonePositiveDensity := Erdos713CloneAverage.exists_positive_density H
    ⟨vC.val,w,hvw⟩ hHNoIsolates (η := (2-α)/2) (by linarith : 0 ≤ α) hc
    (by linarith [hα.2]) (by linarith [hα.2]) hHAsymptotic
  -- Choosing maximum degree-square energy among ordinary edge maximizers
  -- yields obstruction mass >= 2*ex(n,H)-|H|^2*n at EVERY size. In this
  -- selected family the mass/ex ratio tends to 2. These hosts are not
  -- asserted bipartite, regular, or members of the previous record families;
  -- no rate is transferred to the identified graphs.
  have hHCloneAlmostAllMass := Erdos713CloneSymm.exists_asymptotic_obstruction_mass H
    hHBipartite ⟨vC.val,w,hvw⟩ hαgt hc hHAsymptotic
  -- A SEPARATE cofinal family combines exact ordinary extremality, a fold
  -- at EVERY vertex, relative minimum degree e/(24*n), and uniform cut
  -- expansion on the SAME host. Arbitrary absolute degree targets are also
  -- retained. Small-curvature quadratic supports and integrality preserve
  -- exact edge maximality. These hosts are not asserted bipartite,
  -- secondary-optimal, or members of the past/future-record families above.
  have hHExactAllFold := Erdos713RelativeExpansion.exact_saturated_expanders H
    hHBipartite ⟨vC.val,w,hvw⟩ hαgt hα.2 hc hHAsymptotic
  -- Restrictions of exact expanding parents approach the FULL coefficient c.
  -- One lower-degree/expansion constant is fixed before the accuracy; the
  -- upper-degree constant may depend on it. The retained hosts are NOT
  -- asserted exactly extremal, bipartite, secondary-optimal, or saturated,
  -- and no folded copy is asserted to survive the deletion.
  have hHNearFullExpanders := Erdos713NearOptimalExpanders.near_full_density H
    hHBipartite ⟨vC.val,w,hvw⟩ hαgt hα.2 hc hHAsymptotic
  have hCDegree : ∀ v, 2 ≤ Nat.card (C.toSimpleGraph.neighborSet v) :=
    Erdos713Pruning.component_min_degree H hHDegree C
  have hCNoIsolates : ∀ v, ∃ w, C.toSimpleGraph.Adj v w := by
    intro v
    apply (C.toSimpleGraph.degree_pos_iff_exists_adj v).mp
    have hdv := hCDegree v
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using
      (show 0 < Nat.card (C.toSimpleGraph.neighborSet v) by omega)
  -- A rooted threshold transfers to a block only in the first alternative.
  -- The second alternative asserts no rate or asymptotic for a double.
  have hCRootAlternative := Erdos713RootBlocks.root_block_or_double_gap
    C.toSimpleGraph hCConnected hCNoIsolates hαgt hCRate
  have hCCard : 8 ≤ Nat.card C := by
    by_contra hsmallC
    apply hC
    apply Erdos713ThreeSide.small_bipartition_of_card_le_seven C.toSimpleGraph hCBipartite
    simpa only [Fintype.card_eq_nat_card] using (show Nat.card C ≤ 7 by omega)
  have hCSides : ∀ T : Set C, C.toSimpleGraph.IsBipartiteWith T Tᶜ → 4 ≤ Nat.card T := by
    intro T hT
    by_contra hsmallT
    exact hC ⟨T,hT,by omega⟩
  have hαIrr : α ∉ Set.range ((↑) : ℚ → ℝ) := by
    rintro ⟨t,ht⟩
    apply hCRational
    exact ⟨t,by simpa only [ht] using hCRate⟩
  -- A rational-rate pattern actually contained in H has a STRICT exponent
  -- gap under irrationality. EVERY sufficiently large host with at least
  -- half ex(n,H) edges has a polynomial-size disjoint packing of the pattern,
  -- and no smaller-than-c/8*n^(alpha-1) vertex transversal. These are SAME-host
  -- conclusions, not inferences from distinct quotient roots. Identification
  -- quotients need not be contained in H and have no presumed rational rate.
  have hHRobustKnown : ∀ (k : ℕ) (Q : SimpleGraph (Fin k)) (r : ℚ),
      Q ⊑ H → Erdos713Rate.HasRate Q (r : ℝ) → ∃ δ : ℝ, 0 < δ ∧
        ∀ᶠ n : ℕ in atTop, ∀ K : SimpleGraph (Fin n),
          extremalNumber n H ≤ 2*Nat.card K.edgeSet →
            Erdos713RobustCopies.DisjointCopies ⌊δ*(n : ℝ)^(α-1)⌋₊ Q K ∧
            ∀ T : Finset (Fin n), Q.Free (K.induce (T : Set (Fin n))ᶜ) →
              c/8*(n : ℝ)^(α-1) < (T.card : ℝ) := by
    intro k Q r hQH hQ
    exact Erdos713RobustCopies.known_subgraphs_quantitative H Q hα.1 hc hHAsymptotic hαIrr hQH hQ
  -- In H-FREE dense hosts, uniform small-set incidence bounds strengthen
  -- this to LINEAR vertex-disjoint packings and LINEAR transversals. All
  -- previous extremal witness families meet this additional freeness
  -- hypothesis. The conclusion still concerns actual contained patterns,
  -- not arbitrary identification quotients, and transfers no rates.
  have hHLinearKnown : ∀ (k : ℕ) (Q : SimpleGraph (Fin k)) (r : ℚ),
      Q ⊑ H → Erdos713Rate.HasRate Q (r : ℝ) → ∃ δ : ℝ, 0 < δ ∧
        ∀ᶠ n : ℕ in atTop, ∀ K : SimpleGraph (Fin n), H.Free K →
          extremalNumber n H ≤ 2*Nat.card K.edgeSet →
            Erdos713RobustCopies.DisjointCopies ⌊δ*(n : ℝ)⌋₊ Q K ∧
            ∀ T : Finset (Fin n), Q.Free (K.induce (T : Set (Fin n))ᶜ) →
              δ*n < (T.card : ℝ) := by
    intro k Q r hQH hQ
    exact Erdos713LinearRobustCopies.known_subgraphs_linear H Q hαgt hc hHAsymptotic hαIrr hQH hQ
  -- This SAME block has a rooted lower threshold at alpha, and either the
  -- ordinary attained rate alpha or a genuine positive ordinary/rooted gap.
  -- Neither alternative asserts an exact asymptotic for the block.
  obtain ⟨B,hBBlock,hBBipartite,hBCard,hBDegree,hBSides,hBNotC10,hBNotRooted,
      hBRootLower,hBRateOrGap⟩ :=
    Erdos713RootBlocks.remaining_block_with_rate_or_gap
      C.toSimpleGraph hCConnected hCBipartite hαgt hCRate hαIrr
  have hBConnected := hBBlock.connected
  have hBNoCut := hBBlock.noCut
  have hBNotSquares : ¬ Erdos713Squares.Sandwich (C.toSimpleGraph.induce B) :=
    fun h => hBNotRooted h.rooted_rate
  have hBNotTheta : ¬ Erdos713Theta3.Sandwich (C.toSimpleGraph.induce B) :=
    fun h => hBNotRooted h.rooted_rate
  -- Rooted bounds are transferred only when known for the connected base.
  -- They are not inferred from its ordinary rate alone.
  have hBNotCoherent : ∀ (k : ℕ) (F : SimpleGraph (Fin k)),
      F.Connected → Erdos713ActualBlocks.RootedRate F →
        ¬ Erdos713CoherentEdges.Sandwich F (C.toSimpleGraph.induce B) := by
    intro k F hConn hF hSandwich
    exact hBNotRooted ((hSandwich.rooted_rate_iff hConn).mpr hF)
  have hBNotCoherentSmall : ¬ Erdos713CoherentEdges.SmallSandwich (C.toSimpleGraph.induce B) :=
    fun h => hBNotRooted h.rooted_rate
  -- With matching rooted base data, arbitrary edge attachments also
  -- preserve the rate. No edge-alignment assumption is needed here.
  have hBNotArbitraryEdges : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) (x y : Fin k),
      F.Adj x y → F.Connected → Erdos713ActualBlocks.RootedRate F →
        ¬ Erdos713EdgeAttachments.Sandwich F x y (C.toSimpleGraph.induce B) := by
    intro k F x y hxy hConn hF hSandwich
    exact hBNotRooted (Erdos713RootedEdges.sandwich_rooted_rate hxy hConn hF hSandwich)
  have hBNotMixedEdges : ¬ Erdos713RootedEdges.MixedBuilt (C.toSimpleGraph.induce B) :=
    fun h => hBNotRooted h.rooted_rate
  -- These are conditional on a proved rational rate for the base cycle.
  -- No rational rate for C8 or for an arbitrary even cycle is assumed.
  have hBNotCycleAttachments : ∀ n : ℕ, ∀ r : ℚ,
      Erdos713Rate.HasRate (cycleGraph (n+2)) (r : ℝ) →
      ¬ Erdos713EdgeAttachments.Sandwich (cycleGraph (n+2)) 0 1 (C.toSimpleGraph.induce B) :=
    fun n r hr h => hBNotRooted (Erdos713EdgeAttachments.cycle_sandwich_rooted_rate hr h)
  have hBNotLadder : ∀ m : ℕ, 1 ≤ m → Erdos713C4.K22 ⊑ C.toSimpleGraph.induce B →
      ¬ C.toSimpleGraph.induce B ⊑ Erdos713Ladder.graph m := by
    intro m hm hlo hhi
    exact hBNotRooted (Erdos713Ladder.rooted_rate_of_containment hm hlo hhi)
  have hBNoIsolates : ∀ v, ∃ w, (C.toSimpleGraph.induce B).Adj v w := by
    intro v
    apply ((C.toSimpleGraph.induce B).degree_pos_iff_exists_adj v).mp
    have hdv := hBDegree v
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using
      (show 0 < Nat.card ((C.toSimpleGraph.induce B).neighborSet v) by omega)
  -- In the gap branch, rational p<q bracket a STRICT polynomial separation;
  -- no upper rate or exact asymptotic is asserted for the doubles.
  have hBSharpAlternative :
      Erdos713Rate.HasRate (C.toSimpleGraph.induce B) α ∨
      ∃ p t : ℚ, 1 ≤ p ∧ p < t ∧ (t : ℝ) < α ∧
        Asymptotics.IsBigO atTop
          (fun n : ℕ => (extremalNumber n (C.toSimpleGraph.induce B) : ℝ))
          (fun n : ℕ => (n : ℝ)^(p : ℝ)) ∧
        ∀ x y, (C.toSimpleGraph.induce B).Adj x y →
          ¬ Asymptotics.IsBigO atTop
            (fun n : ℕ => (extremalNumber n
              (Erdos713Gluing.wedge (C.toSimpleGraph.induce B) x
                (C.toSimpleGraph.induce B) y) : ℝ))
            (fun n : ℕ => (n : ℝ)^(t : ℝ)) := by
    rcases hBRateOrGap with hRate | ⟨a,ha,haα,hu⟩
    · exact Or.inl hRate
    · exact Or.inr (Erdos713RootBlocks.rational_bracket_of_strict_root_gap
        (C.toSimpleGraph.induce B) ha haα hu hBRootLower)
  -- If this block has a rational ordinary threshold, its opposite-root double
  -- is not O(n^r) at that same threshold. No rate or exact asymptotic for the
  -- double is inferred from the asymptotic for the original graph.
  have hBDouble : ∀ (r : ℚ), Erdos713Rate.HasRate (C.toSimpleGraph.induce B) (r : ℝ) →
      ∀ x y, (C.toSimpleGraph.induce B).Adj x y →
        ¬ Asymptotics.IsBigO atTop
          (fun n : ℕ => (extremalNumber n
            (Erdos713Gluing.wedge (C.toSimpleGraph.induce B) x (C.toSimpleGraph.induce B) y) : ℝ))
          (fun n : ℕ => (n : ℝ)^(r : ℝ)) := by
    intro r hr x y hxy
    exact Erdos713ActualBlocks.unmatched_opposite_wedge hBConnected hBNoIsolates hBNotRooted hxy hr
  -- Inside this SAME block, extract an induced atom with no cut vertex
  -- and no adjacent two-vertex separator. Nonadjacent two-vertex separators
  -- are not excluded. Only the rooted LOWER threshold passes to this atom.
  have hBUpper : Asymptotics.IsBigO atTop
      (fun n : ℕ => (extremalNumber n (C.toSimpleGraph.induce B) : ℝ))
      (fun n : ℕ => (n : ℝ)^α) :=
    (Erdos713Rate.extremal_mono_bigO ⟨Copy.induce C.toSimpleGraph B⟩).trans hCRate.upper
  obtain ⟨b⟩ := hBConnected.nonempty
  obtain ⟨A,hAAtom,hABipartite,hACard,hADegree,hASides,hANotC10,hANotRooted,
      hARootLower,hARateOrGap⟩ :=
    Erdos713EdgeSeparators.remaining_atom_with_rate_or_gap
      (C.toSimpleGraph.induce B) hBConnected hBBipartite hαgt (hBRootLower b) hBUpper hαIrr
  have hAConnected := hAAtom.connected
  have hANoCut := hAAtom.noCut
  have hANoEdgeCut := hAAtom.noEdgeCut
  have hAInheritedUpper := Erdos713Rate.extremal_mono_bigO
    ⟨Copy.induce (C.toSimpleGraph.induce B) A⟩
  have hANotMixedEdges : ¬ Erdos713RootedEdges.MixedBuilt ((C.toSimpleGraph.induce B).induce A) :=
    fun h => hANotRooted h.rooted_rate
  have hASharpAlternative :
      Erdos713Rate.HasRate ((C.toSimpleGraph.induce B).induce A) α ∨
      ∃ p t : ℚ, 1 ≤ p ∧ p < t ∧ (t : ℝ) < α ∧
        Asymptotics.IsBigO atTop
          (fun n : ℕ => (extremalNumber n ((C.toSimpleGraph.induce B).induce A) : ℝ))
          (fun n : ℕ => (n : ℝ)^(p : ℝ)) ∧
        ∀ x y, ((C.toSimpleGraph.induce B).induce A).Adj x y →
          ¬ Asymptotics.IsBigO atTop
            (fun n : ℕ => (extremalNumber n
              (Erdos713Gluing.wedge ((C.toSimpleGraph.induce B).induce A) x
                ((C.toSimpleGraph.induce B).induce A) y) : ℝ))
            (fun n : ℕ => (n : ℝ)^(t : ℝ)) := by
    rcases hARateOrGap with hRate | ⟨a,ha,haα,hu⟩
    · exact Or.inl hRate
    · exact Or.inr (Erdos713RootBlocks.rational_bracket_of_strict_root_gap
        ((C.toSimpleGraph.induce B).induce A) ha haα hu hARootLower)
  trace "Reached the final proof obligation"
  trace_state
  solve_by_elim (maxDepth := 1)

end Erdos713
