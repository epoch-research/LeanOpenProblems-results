import Submission.Critical
import Submission.Weighted

/-!
# Cardinal integer-gap approximate-quotient certificates

The finite-bag interpolation inequality and its actual-graph specialization
formalize Theorem 2.1 of `eh_cardinal_core_resolution/report.md`. Quotient
capacity budgets and the integer product gap are hypotheses; no capacity repair,
structural decomposition, weighted criticality, or Erdős–Hajnal claim is made.
-/

namespace Erdos61Research

open SimpleGraph

variable {V I : Type*}

/-- Cardinal criticality stated directly at the cardinal exponent `p`.
Every proper actual induced set, including the empty set, is cardinally good. -/
structure IsCardinalCritical [Fintype V] (G : SimpleGraph V) (p : ℝ) : Prop where
  kappa_pow_lt : (kappa G : ℝ) ^ p < (Fintype.card V : ℝ)
  card_le_pow : ∀ U : Finset V, U ≠ Finset.univ →
    (U.card : ℝ) ≤ (kappa (G.induce (U : Set V)) : ℝ) ^ p

/-- Interpolation over any finite index bag, allowing zero weights and sizes. -/
theorem finite_bag_interpolation (s : Finset I) (size k : I → ℝ)
    {K p q : ℝ} (hK : 1 < K) (hq : 1 ≤ q) (hp : q + 1 ≤ p)
    (hk0 : ∀ i ∈ s, 0 ≤ k i) (hgap : ∀ i ∈ s, k i ≤ K - 1)
    (hsize : ∀ i ∈ s, size i ≤ k i ^ p)
    (hbudget : ∑ i ∈ s, k i ^ q ≤ K ^ q) :
    ∑ i ∈ s, size i ≤ K ^ q * (K - 1) ^ (p - q) := by
  have hd : 0 ≤ p - q := by linarith
  have hq0 : 0 ≤ q := by linarith
  calc
    ∑ i ∈ s, size i ≤ ∑ i ∈ s, k i ^ p := Finset.sum_le_sum hsize
    _ ≤ ∑ i ∈ s, (K - 1) ^ (p - q) * k i ^ q := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        k i ^ p = k i ^ (p - q) * k i ^ q := by
          rw [← Real.rpow_add_of_nonneg (hk0 i hi) hd hq0]
          congr 1
          ring
        _ ≤ (K - 1) ^ (p - q) * k i ^ q :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hk0 i hi) (hgap i hi) hd)
            (Real.rpow_nonneg (hk0 i hi) q)
    _ = (K - 1) ^ (p - q) * ∑ i ∈ s, k i ^ q := (Finset.mul_sum _ _ _).symm
    _ ≤ (K - 1) ^ (p - q) * K ^ q :=
      mul_le_mul_of_nonneg_left hbudget (Real.rpow_nonneg (by linarith) _)
    _ = K ^ q * (K - 1) ^ (p - q) := mul_comm _ _

/-- The sharp real-power deficit and its strict `n / K` consequence.
There is no assumption about the magnitude of the critical excess `n - K^p`. -/
theorem rpow_integer_gap {n e K p q : ℝ}
    (hK : 1 < K) (hp : q + 1 ≤ p) (hbad : K ^ p < n)
    (hcap : n - e ≤ K ^ q * (K - 1) ^ (p - q)) :
    n * (1 - (1 - 1 / K) ^ (p - q)) < e ∧ n / K < e := by
  have hK0 : 0 < K := by linarith
  have hKm1 : 0 < K - 1 := sub_pos.mpr hK
  have hr0 : 0 < (K - 1) / K := div_pos hKm1 hK0
  have hr1 : (K - 1) / K ≤ 1 := (div_le_one hK0).mpr (by linarith)
  have hn : 0 < n := (Real.rpow_pos_of_pos hK0 p).trans hbad
  have hratio : ((K - 1) / K) ^ (p - q) ≤ (K - 1) / K := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (show (1 : ℝ) ≤ p - q by linarith)
  have hsplit : K ^ p = K ^ q * K ^ (p - q) := by
    rw [← Real.rpow_add hK0]
    congr 1
    ring
  have hid : K ^ q * (K - 1) ^ (p - q) =
      K ^ p * ((K - 1) / K) ^ (p - q) := by
    rw [hsplit, Real.div_rpow hKm1.le hK0.le]
    field_simp [(Real.rpow_pos_of_pos hK0 (p - q)).ne']
  have hstrict : n - e < n * ((K - 1) / K) ^ (p - q) := by
    calc
      n - e ≤ K ^ q * (K - 1) ^ (p - q) := hcap
      _ = K ^ p * ((K - 1) / K) ^ (p - q) := hid
      _ < n * ((K - 1) / K) ^ (p - q) :=
        mul_lt_mul_of_pos_right hbad (Real.rpow_pos_of_pos hr0 _)
  have hexact : n * (1 - ((K - 1) / K) ^ (p - q)) < e := by linarith
  have hlower : n / K ≤ n * (1 - ((K - 1) / K) ^ (p - q)) := by
    calc
      n / K = n * (1 - (K - 1) / K) := by field_simp; ring
      _ ≤ n * (1 - ((K - 1) / K) ^ (p - q)) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hratio 1) hn.le
  have hr : (K - 1) / K = 1 - 1 / K := by field_simp
  exact ⟨by simpa only [hr] using hexact, hlower.trans_lt hexact⟩

/-- The general finite-bag certificate, before any graph interpretation. -/
theorem finite_bag_integer_gap (s : Finset I) (size k : I → ℝ)
    {n e K p q : ℝ} (hK : 1 < K) (hq : 1 ≤ q) (hp : q + 1 ≤ p)
    (hbad : K ^ p < n) (hcover : ∑ i ∈ s, size i = n - e)
    (hk0 : ∀ i ∈ s, 0 ≤ k i) (hgap : ∀ i ∈ s, k i ≤ K - 1)
    (hsize : ∀ i ∈ s, size i ≤ k i ^ p)
    (hbudget : ∑ i ∈ s, k i ^ q ≤ K ^ q) :
    n - e ≤ K ^ q * (K - 1) ^ (p - q) ∧
      n * (1 - (1 - 1 / K) ^ (p - q)) < e ∧ n / K < e := by
  have hcap := finite_bag_interpolation s size k hK hq hp hk0 hgap hsize hbudget
  rw [hcover] at hcap
  exact ⟨hcap, rpow_integer_gap hK hp hbad hcap⟩

/-- A `W_q` reference quotient with the actual bag capacity budgets supplies
exactly the power budget on the bag products. No cross-bag purity is assumed. -/
theorem quotient_kappa_power_budget [Fintype V] [Fintype I]
    (G : SimpleGraph V) (Q : SimpleGraph I) (U : I → Finset V) {q : ℝ}
    (hK : 1 < (kappa G : ℝ)) (hQ : WpOn Q Finset.univ q)
    (hstable : WeightStableBound Q Finset.univ
      (fun i => ((G.induce (U i : Set V)).indepNum : ℝ)) (G.indepNum : ℝ))
    (hclique : WeightCliqueBound Q Finset.univ
      (fun i => ((G.induce (U i : Set V)).cliqueNum : ℝ)) (G.cliqueNum : ℝ)) :
    ∑ i : I, (kappa (G.induce (U i : Set V)) : ℝ) ^ q ≤ (kappa G : ℝ) ^ q := by
  have hprod : 0 < (G.indepNum : ℝ) * (G.cliqueNum : ℝ) := by
    simpa only [kappa, Nat.cast_mul] using (show 0 < (kappa G : ℝ) by linarith)
  have ha : 0 < (G.indepNum : ℝ) :=
    pos_of_mul_pos_left hprod (Nat.cast_nonneg G.cliqueNum)
  have hb : 0 < (G.cliqueNum : ℝ) :=
    pos_of_mul_pos_right hprod (Nat.cast_nonneg G.indepNum)
  simpa only [kappa, Nat.cast_mul] using hQ.scale
    (fun i => Nat.cast_nonneg (G.induce (U i : Set V)).indepNum)
    (fun i => Nat.cast_nonneg (G.induce (U i : Set V)).cliqueNum) hstable hclique ha hb

/-- Ordinary positive-exponent criticality implies the direct cardinal form
at `p = 1 / τ`; this is only a change of exponents, not weighted criticality. -/
theorem IsExponentCritical.to_cardinal [Fintype V]
    {G : SimpleGraph V} {τ : ℝ} (hcrit : IsExponentCritical G τ) (hτ : 0 < τ) :
    IsCardinalCritical G (1 / τ) := by
  have hp : 0 < 1 / τ := one_div_pos.mpr hτ
  constructor
  · have h := Real.rpow_lt_rpow (Nat.cast_nonneg (kappa G)) hcrit.kappa_lt hp
    simpa only [one_div, Real.rpow_rpow_inv (Nat.cast_nonneg (Fintype.card V)) hτ.ne']
      using h
  · intro U hU
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg U.card) τ)
      (hcrit.induced_ge U hU) hp.le
    simpa only [one_div, Real.rpow_rpow_inv (Nat.cast_nonneg U.card) hτ.ne'] using h

/-- A nonempty finite graph has a positive integer product invariant. -/
theorem kappa_pos [Finite V] [Nonempty V] (G : SimpleGraph V) : 0 < kappa G := by
  have hclique : 0 < G.cliqueNum := by
    simpa only [SimpleGraph.indepNum_compl] using (SimpleGraph.indepNum_pos (G := Gᶜ))
  exact Nat.mul_pos (SimpleGraph.indepNum_pos (G := G)) hclique

/-- Every nonempty actual induced bag has integer product at least one. -/
theorem kappa_induce_nonempty [Finite V] (G : SimpleGraph V) (U : Finset V)
    (hU : U.Nonempty) : 0 < kappa (G.induce (U : Set V)) := by
  obtain ⟨v, hv⟩ := hU
  letI : Nonempty (U : Set V) := ⟨⟨v, hv⟩⟩
  exact kappa_pos _

/-- Direct cardinal criticality implies a positive ambient order. -/
theorem IsCardinalCritical.card_pos [Fintype V] {G : SimpleGraph V} {p : ℝ}
    (hcrit : IsCardinalCritical G p) : 0 < Fintype.card V := by
  have hn : 0 < (Fintype.card V : ℝ) :=
    (Real.rpow_nonneg (Nat.cast_nonneg (kappa G)) p).trans_lt hcrit.kappa_pow_lt
  exact_mod_cast hn

/-- Positive-exponent cardinal criticality automatically has `K > 1`.
Two distinct singletons are a pure pair, regardless of their adjacency bit. -/
theorem IsCardinalCritical.kappa_gt_one [Fintype V] {G : SimpleGraph V} {p : ℝ}
    (hcrit : IsCardinalCritical G p) (hp : 0 < p) : 1 < (kappa G : ℝ) := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp hcrit.card_pos
  have hK1 : (1 : ℝ) ≤ (kappa G : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (kappa_pos G))
  have hpow : (1 : ℝ) ≤ (kappa G : ℝ) ^ p := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hK1 hp.le
  have hn : 1 < Fintype.card V := by exact_mod_cast hpow.trans_lt hcrit.kappa_pow_lt
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  have hpair := kappa_add_le_of_pure_pair G ({u} : Finset V) {v}
    (by simp [huv]) (by
      by_cases h : G.Adj u v
      · right; simpa using h
      · left; simpa using h)
  have hu := kappa_induce_nonempty G {u} (Finset.singleton_nonempty u)
  have hv := kappa_induce_nonempty G {v} (Finset.singleton_nonempty v)
  have hK : 1 < kappa G := by omega
  exact_mod_cast hK

/-- The cardinal approximate-quotient certificate on disjoint actual proper
bags. Their union covers exactly `|V| - e` actual vertices. The reference graph
need not be realized as a pure substitution in `G`; its capacity budgets and
all bag product gaps must genuinely hold. Empty bags are permitted. -/
theorem IsCardinalCritical.approximate_quotient_certificate
    [Fintype V] [Fintype I] [DecidableEq V]
    {G : SimpleGraph V} {p q e : ℝ} (hcrit : IsCardinalCritical G p)
    (Q : SimpleGraph I) (U : I → Finset V)
    (hq : 1 ≤ q) (hp : q + 1 ≤ p)
    (hproper : ∀ i, U i ≠ Finset.univ)
    (hdis : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint U)
    (hcover : ((Finset.univ.biUnion U).card : ℝ) = (Fintype.card V : ℝ) - e)
    (hQ : WpOn Q Finset.univ q)
    (hstable : WeightStableBound Q Finset.univ
      (fun i => ((G.induce (U i : Set V)).indepNum : ℝ)) (G.indepNum : ℝ))
    (hclique : WeightCliqueBound Q Finset.univ
      (fun i => ((G.induce (U i : Set V)).cliqueNum : ℝ)) (G.cliqueNum : ℝ))
    (hgap : ∀ i, (kappa (G.induce (U i : Set V)) : ℝ) ≤ (kappa G : ℝ) - 1) :
    (Fintype.card V : ℝ) - e ≤ (kappa G : ℝ) ^ q * ((kappa G : ℝ) - 1) ^ (p - q) ∧
      (Fintype.card V : ℝ) * (1 - (1 - 1 / (kappa G : ℝ)) ^ (p - q)) < e ∧
      (Fintype.card V : ℝ) / (kappa G : ℝ) < e := by
  have hK := hcrit.kappa_gt_one (show 0 < p by linarith)
  have hsum : ∑ i : I, ((U i).card : ℝ) = (Fintype.card V : ℝ) - e := by
    rw [← Nat.cast_sum, ← Finset.card_biUnion hdis]
    exact hcover
  exact finite_bag_integer_gap Finset.univ (fun i => ((U i).card : ℝ))
    (fun i => (kappa (G.induce (U i : Set V)) : ℝ)) hK hq hp hcrit.kappa_pow_lt hsum
    (fun i _ => Nat.cast_nonneg _) (fun i _ => hgap i)
    (fun i _ => hcrit.card_le_pow (U i) (hproper i))
    (quotient_kappa_power_budget G Q U hK hQ hstable hclique)

/-- A proper side pure to an outside singleton has product at most `K - 1`.
For `p ≥ 1` this gives a strict cardinal bound on the side's complement. -/
theorem IsCardinalCritical.singleton_pure_deficit [Fintype V]
    {G : SimpleGraph V} {p : ℝ} (hcrit : IsCardinalCritical G p) (hp : 1 ≤ p)
    (B : Finset V) (v : V) (hv : v ∉ B)
    (hpure : (∀ b ∈ B, ¬G.Adj v b) ∨ (∀ b ∈ B, G.Adj v b)) :
    (Fintype.card V : ℝ) / (kappa G : ℝ) < (Fintype.card V : ℝ) - (B.card : ℝ) := by
  classical
  have hpair := kappa_add_le_of_pure_pair G ({v} : Finset V) B
    (by simpa using hv) (by simpa using hpure)
  have hsingle := kappa_induce_nonempty G {v} (Finset.singleton_nonempty v)
  have hgap : (kappa (G.induce (B : Set V)) : ℝ) ≤ (kappa G : ℝ) - 1 := by
    have hnat : kappa (G.induce (B : Set V)) + 1 ≤ kappa G := by omega
    have hreal : (kappa (G.induce (B : Set V)) : ℝ) + 1 ≤ (kappa G : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hproper : B ≠ Finset.univ := by
    intro hB
    exact hv (by simp [hB])
  have hcap : (B.card : ℝ) ≤ ((kappa G : ℝ) - 1) ^ p :=
    (hcrit.card_le_pow B hproper).trans
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hgap (by linarith))
  exact (rpow_integer_gap (q := 0) (e := (Fintype.card V : ℝ) - (B.card : ℝ))
    (hcrit.kappa_gt_one (by linarith)) (by simpa using hp) hcrit.kappa_pow_lt
    (by simpa using hcap)).2

/-- Every vertex of a cardinally critical graph at `p ≥ 1` has
`degree + 1 > n / K`, using its anticomplete singleton/nonneighbor pair. -/
theorem IsCardinalCritical.degree_add_one_gt [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : ℝ}
    (hcrit : IsCardinalCritical G p) (hp : 1 ≤ p) (v : V) :
    (Fintype.card V : ℝ) / (kappa G : ℝ) < (G.degree v : ℝ) + 1 := by
  classical
  have hdef := hcrit.singleton_pure_deficit hp (nonneighborVertices G v) v
    (notMem_nonneighborVertices_self G v)
    (Or.inl (fun b hb => ((mem_nonneighborVertices G v b).mp hb).2))
  have hcard : (Fintype.card V : ℝ) = (neighborVertices G v).card +
      (nonneighborVertices G v).card + 1 := by
    simpa using sum_univ_link_partition G v (fun _ => (1 : ℝ))
  have hdegree : (neighborVertices G v).card = G.degree v := by
    calc
      _ = (G.neighborFinset v).card := by congr 1; ext w; simp
      _ = G.degree v := G.card_neighborFinset_eq_degree v
  rw [hdegree] at hcard
  linarith

/-- For ANY ordinary positive-`τ` critical graph with `1 / τ ≥ 1`, both
minimum degree plus one and minimum codegree plus one strictly exceed `n / K`.
No primeness, partition, or all-weight criticality hypothesis is used. -/
theorem IsExponentCritical.min_degree_codegree_gt [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {τ : ℝ}
    (hcrit : IsExponentCritical G τ) (hp : 1 ≤ 1 / τ) :
    (Fintype.card V : ℝ) / (kappa G : ℝ) < (G.minDegree : ℝ) + 1 ∧
      (Fintype.card V : ℝ) / (kappa G : ℝ) < (Gᶜ.minDegree : ℝ) + 1 := by
  have hτ : 0 < τ := one_div_pos.mp (lt_of_lt_of_le zero_lt_one hp)
  have hcard := hcrit.to_cardinal hτ
  letI : Nonempty V := Fintype.card_pos_iff.mp hcard.card_pos
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  obtain ⟨w, hw⟩ := Gᶜ.exists_minimal_degree_vertex
  constructor
  · rw [hv]
    exact hcard.degree_add_one_gt hp v
  · rw [hw]
    simpa only [kappa_compl] using (hcrit.compl.to_cardinal hτ).degree_add_one_gt hp w


end Erdos61Research
