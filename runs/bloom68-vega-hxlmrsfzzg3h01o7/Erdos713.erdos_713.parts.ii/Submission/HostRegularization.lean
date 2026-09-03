import Submission.DegreeTail
import Submission.ExactConstantCore

/-!
# Fixed-error regularization of extremal hosts

An exact positive power asymptotic, with exponent strictly between one and
two, yields induced cores retaining arbitrarily large fixed fractions of the
vertices and edges. Their minimum degree is bounded below by the discrete
increment of the power potential, and their maximum degree has a fixed host-scale cap.
The cap may depend on the requested error. No asymptotic for increments of the
extremal number, mean value theorem, or fixed-ratio almost-regularity is used.

The all-sizes hereditary bound is derived here, including size zero and all
finite initial exceptions. Forbidden-subgraph freeness is ordinary injective
freeness. This file neither imports nor uses `Submission.Spec`.
-/

open SimpleGraph Filter Asymptotics
open scoped Topology Classical

namespace Erdos713HostRegularization

universe u v

/-- There are no edges on zero vertices, regardless of the forbidden graph. -/
lemma extremalNumber_zero {W : Type v} (H : SimpleGraph W) :
    extremalNumber 0 H = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  rw [← Fintype.card_fin 0, extremalNumber_le_iff]
  intro G _ _
  simpa using (G.card_edgeFinset_le_card_choose_two)

/-- A positive power asymptotic bounds every extremal number by one fixed
multiple of that power. The finitely many exceptions are absorbed into `C`;
size zero is handled separately, without any hypothesis about isolates in `H`. -/
theorem exists_uniform_extremal_power_bound {W : Type v} (H : SimpleGraph W)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (extremalNumber n H : ℝ) ≤ C * (n : ℝ) ^ a := by
  have herr := hf.isLittleO.of_const_mul_right.bound (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp herr
  let B : ℝ := ∑ j ∈ Finset.range N, (extremalNumber j H : ℝ)
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  let C : ℝ := c + 1 + B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [extremalNumber_zero, Real.zero_rpow ha.ne']
  by_cases hn : N ≤ n
  · have h := hN n hn
    simp only [Pi.sub_apply, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)] at h
    have hu := (abs_le.mp h).2
    have hpow := Real.rpow_nonneg (Nat.cast_nonneg n) a
    have hBp := mul_nonneg hB hpow
    dsimp [C]
    nlinarith
  · have hsmall : (extremalNumber n H : ℝ) ≤ B :=
      Finset.single_le_sum (fun j _ => Nat.cast_nonneg (extremalNumber j H))
        (Finset.mem_range.mpr (by omega))
    have hpow : 1 ≤ (n : ℝ) ^ a :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) ha.le
    calc
      (extremalNumber n H : ℝ) ≤ B := hsmall
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ C * (n : ℝ) ^ a := le_mul_of_one_le_right hC.le hpow

/-- An all-sizes extremal bound applies to every induced subset of every
ordinary `H`-free finite graph. No nonemptiness hypothesis is needed. -/
lemma hereditaryPowerBound_of_extremal_bound {V : Type u} {W : Type v}
    [Fintype V] (G : SimpleGraph V) (H : SimpleGraph W) {C a : ℝ}
    (hfree : H.Free G)
    (hcap : ∀ n : ℕ, (extremalNumber n H : ℝ) ≤ C * (n : ℝ) ^ a) :
    Erdos713DegreeTail.HereditaryPowerBound G C a := by
  intro U
  have hU : H.Free (G.induce (U : Set V)) :=
    fun h => hfree (h.trans ⟨(SimpleGraph.Embedding.induce (U : Set V)).toCopy⟩)
  have he := card_edgeFinset_le_extremalNumber hU
  have hb := (Nat.cast_le.mpr he :
    ((G.induce (U : Set V)).edgeFinset.card : ℝ) ≤
      (extremalNumber (Fintype.card (U : Set V)) H : ℝ)).trans
        (hcap (Fintype.card (U : Set V)))
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hb

/-- One cutoff makes both the removed vertex fraction and the incident-edge
loss arbitrarily small, uniformly over all finite hosts with a hereditary cap. -/
theorem exists_uniform_trimming_cutoff {C a δ η : ℝ}
    (hC : 0 < C) (ha1 : 1 < a) (ha2 : a < 2) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        Erdos713DegreeTail.HereditaryPowerBound G C a →
        ((Erdos713DegreeTail.highDegreeSet G a L).card : ℝ) ≤ δ * (n : ℝ) ∧
        ((Erdos713DegreeTail.incidentEdges G
          (Erdos713DegreeTail.highDegreeSet G a L)).card : ℝ) ≤ η * (n : ℝ) ^ a := by
  have hp : 0 < (a - 1) / (2 - a) := div_pos (sub_pos.mpr ha1) (sub_pos.mpr ha2)
  have hdiv : Tendsto (fun L : ℝ => 8 * C / L) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop (8 * C)
  have hlim : Tendsto (fun L : ℝ => (8 * C) * (8 * C / L) ^ ((a - 1) / (2 - a)))
      atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne', mul_zero] using
      (hdiv.rpow_const (Or.inr hp.le)).const_mul (8 * C)
  obtain ⟨L, hL, hLδ, hsmall⟩ := ((eventually_ge_atTop (4 * C)).and
    ((eventually_ge_atTop (2 * C / δ)).and (hlim.eventually (gt_mem_nhds hη)))).exists
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * C) hL
  refine ⟨L, hLpos, ?_⟩
  intro n G hG
  constructor
  · have hmarkov := Erdos713DegreeTail.highDegree_card_mul_le G hG L
    simp only [Fintype.card_fin] at hmarkov
    have hcoeff : 2 * C ≤ L * δ := (div_le_iff₀ hδ).mp hLδ
    have hscale := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    apply (mul_le_mul_iff_of_pos_right hLpos).mp
    nlinarith
  · calc
      _ ≤ (8 * C) * (n : ℝ) ^ a * (8 * C / L) ^ ((a - 1) / (2 - a)) := by
        simpa only [Fintype.card_fin] using
          Erdos713DegreeTail.highDegree_incident_edges_le G hC ha1 ha2 hG hL
      _ = ((8 * C) * (8 * C / L) ^ ((a - 1) / (2 - a))) * (n : ℝ) ^ a := by ring
      _ ≤ η * (n : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg (Nat.cast_nonneg n) a)

/-- Induced embeddings cannot increase the degree of a vertex. -/
lemma degree_le_of_embedding {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : K ↪g G) (x : W) :
    K.degree x ≤ G.degree (f x) := by
  simpa only [card_neighborSet_eq_degree] using Fintype.card_le_of_embedding (f.mapNeighborSet x)

set_option maxHeartbeats 800000 in
/-- For every fixed error in `(0,1)`, every sufficiently large ordinary
`H`-free extremal host has an induced, nonempty, near-spanning core losing at
most that error times `c n^a` edges. Its minimum degree is bounded below by the
corresponding power-potential increment, and its maximum degree is at most
`L n^(a-1)`. The same `L` and `N` work for all these hosts. -/
theorem exists_host_regularization {W : Type v} (H : SimpleGraph W)
    {a c : ℝ} (ha1 : 1 < a) (ha2 : a < 2) (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ L : ℝ, 0 < L ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), H.Free G →
        G.edgeFinset.card = extremalNumber n H →
        ∃ m : ℕ, ∃ K : SimpleGraph (Fin m),
          Nonempty (K ↪g G) ∧ 0 < m ∧ m ≤ n ∧ H.Free K ∧
          (1 - ε) * (n : ℝ) ≤ (m : ℝ) ∧
          (G.edgeFinset.card : ℝ) - (K.edgeFinset.card : ℝ) ≤ ε * c * (n : ℝ) ^ a ∧
          (∀ x, (1 - ε) * c * ((m : ℝ) ^ a - ((m - 1 : ℕ) : ℝ) ^ a) ≤
            (K.degree x : ℝ)) ∧
          (∀ x, (K.degree x : ℝ) ≤ L * (n : ℝ) ^ (a - 1)) := by
  have ha : 0 < a := lt_trans zero_lt_one ha1
  have hεnonneg : 0 ≤ 1 - ε := sub_nonneg.mpr hε1.le
  let η : ℝ := ε * ε * c / 6
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC, hcap⟩ := exists_uniform_extremal_power_bound H ha hc hf
  obtain ⟨L, hL, hcut⟩ := exists_uniform_trimming_cutoff hC ha1 ha2
    (show 0 < ε / 2 by positivity) hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Erdos713ExactCore.eventually_uniform_power_error ha hf hη).and
      (eventually_ge_atTop 1))
  refine ⟨L, hL, N, ?_⟩
  intro n hn G hG hmax
  obtain ⟨herr, hn1⟩ := hN n hn
  have hhered := hereditaryPowerBound_of_extremal_bound G H hG hcap
  obtain ⟨_hcard, hincident⟩ := hcut n G hhered
  let T : Set (Fin n) := ((Erdos713DegreeTail.highDegreeSet G a L)ᶜ : Finset (Fin n))
  let F : SimpleGraph T := G.induce T
  let p : ℕ → ℝ := fun j => c * (j : ℝ) ^ a
  have hTn : Fintype.card T ≤ n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_subtype_le (fun x : Fin n => x ∈ T)
  have hF : H.Free F :=
    fun h => hG (h.trans ⟨(SimpleGraph.Embedding.induce T).toCopy⟩)
  have haccount : (F.edgeFinset.card : ℝ) +
      ((Erdos713DegreeTail.incidentEdges G
        (Erdos713DegreeTail.highDegreeSet G a L)).card : ℝ) =
      (G.edgeFinset.card : ℝ) := by
    exact_mod_cast Erdos713DegreeTail.card_edges_induce_compl_add_incident G
      (Erdos713DegreeTail.highDegreeSet G a L)
  have htrim : (G.edgeFinset.card : ℝ) - (F.edgeFinset.card : ℝ) ≤ η * (n : ℝ) ^ a := by
    linarith
  have hGlower : p n - η * (n : ℝ) ^ a ≤ (G.edgeFinset.card : ℝ) := by
    rw [hmax]
    have h := (abs_le.mp (herr n le_rfl)).1
    dsimp [p]
    linarith
  -- The signed defect keeps the reference scale at the original `n`.
  -- The finite peeling theorem does not require that its defect parameter be positive.
  have hlower : p (Fintype.card T) -
      (p (Fintype.card T) - p n + 2 * η * (n : ℝ) ^ a) ≤
      (F.edgeFinset.card : ℝ) := by
    linarith
  have hupper : ∀ j ≤ Fintype.card T,
      (extremalNumber j H : ℝ) ≤ p j + η * (n : ℝ) ^ a := by
    intro j hj
    have h := (abs_le.mp (herr j (hj.trans hTn))).2
    dsimp [p]
    linarith
  obtain ⟨m, K, ⟨f⟩, hm, hK, hd, hb, he⟩ :=
    Erdos713ExactCore.exists_defect_controlled_core F H p ε
      (p (Fintype.card T) - p n + 2 * η * (n : ℝ) ^ a)
      (η * (n : ℝ) ^ a) hF hlower hupper
  have hp0 : p (Fintype.card T) ≤ p n := by
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hTn) ha.le) hc.le
  have hbudget : ε * (p n - p m) ≤ 3 * η * (n : ℝ) ^ a := by
    have hsign := mul_nonneg hεnonneg (sub_nonneg.mpr hp0)
    nlinarith
  have hgap : p n - p m ≤ (ε / 2) * c * (n : ℝ) ^ a := by
    apply (mul_le_mul_iff_of_pos_left hε).mp
    dsimp [η] at hbudget
    nlinarith
  have hnpow : 0 ≤ (n : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg n) a
  have hpower : (1 - ε) * (n : ℝ) ^ a ≤ (m : ℝ) ^ a := by
    apply (mul_le_mul_iff_of_pos_left hc).mp
    dsimp [p] at hgap
    have hpositive := mul_nonneg (mul_nonneg hε.le hc.le) hnpow
    nlinarith
  have hmn : (1 - ε) * (n : ℝ) ≤ (m : ℝ) := by
    by_contra! hlt
    have hltpow := Real.rpow_lt_rpow (Nat.cast_nonneg m) hlt ha
    rw [Real.mul_rpow hεnonneg (Nat.cast_nonneg n)] at hltpow
    have hbase : (1 - ε) ^ a ≤ 1 - ε :=
      Real.rpow_le_self_of_le_one hεnonneg (by linarith) ha1.le
    have hbound := mul_le_mul_of_nonneg_right hbase hnpow
    linarith
  have hmpos : 0 < m := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    exact_mod_cast (mul_pos (sub_pos.mpr hε1) hnpos).trans_le hmn
  refine ⟨m, K, ⟨(SimpleGraph.Embedding.induce T).comp f⟩, hmpos,
    hm.trans hTn, hK, hmn, ?_, ?_, ?_⟩
  · have hpeel := mul_le_mul_of_nonneg_left (sub_le_sub_right hp0 (p m)) hεnonneg
    have hscaledgap := mul_le_mul_of_nonneg_left hgap hεnonneg
    have hηle : η ≤ (ε / 2) * c := by
      calc
        η = (ε / 6) * (ε * c) := by dsimp [η]; ring
        _ ≤ (1 / 2) * (ε * c) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hε.le hc.le)
        _ = (ε / 2) * c := by ring
    have hηscale := mul_le_mul_of_nonneg_right hηle hnpow
    have hone : (1 - ε) * ((ε / 2) * c * (n : ℝ) ^ a) ≤
        (ε / 2) * c * (n : ℝ) ^ a :=
      mul_le_of_le_one_left (by positivity) (by linarith)
    linarith
  · intro x
    have hdx := hd x
    dsimp [p] at hdx
    nlinarith
  · intro x
    have hdx := degree_le_of_embedding f x
    have hcapx := Erdos713DegreeTail.degree_induce_compl_highDegree_le G a L (f x)
    simp only [Fintype.card_fin] at hcapx
    exact (Nat.cast_le.mpr hdx).trans hcapx

end Erdos713HostRegularization

#print axioms Erdos713HostRegularization.extremalNumber_zero
#print axioms Erdos713HostRegularization.exists_uniform_extremal_power_bound
#print axioms Erdos713HostRegularization.hereditaryPowerBound_of_extremal_bound
#print axioms Erdos713HostRegularization.exists_uniform_trimming_cutoff
#print axioms Erdos713HostRegularization.degree_le_of_embedding
#print axioms Erdos713HostRegularization.exists_host_regularization
