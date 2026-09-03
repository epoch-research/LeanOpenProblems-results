import FormalConjecturesUtil
import Submission.DegreePenalty

/-! Global support comparisons for degree-penalized extremizers.
No centered asymptotic selection or rationality is asserted here. -/
open SimpleGraph Finset Filter
open scoped Classical Topology
namespace Erdos713DegreePenaltySupports
open Erdos713DegreePenalty Erdos713Cloning
variable {V W U : Type*}
set_option maxHeartbeats 1000000

lemma degreeR_iso [Fintype V] [Fintype U] {G : SimpleGraph V} {J : SimpleGraph U}
    (f : G ≃g J) (v : V) : degreeR J (f v) = degreeR G v := by
  unfold degreeR
  simp only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, f.degree_eq]

lemma edgesR_iso [Fintype V] [Fintype U] {G : SimpleGraph V} {J : SimpleGraph U}
    (f : G ≃g J) : edgesR J = edgesR G := by
  unfold edgesR
  have he := f.card_edgeFinset_eq
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at he
  exact_mod_cast he.symm

lemma energy_iso [Fintype V] [Fintype U] {G : SimpleGraph V} {J : SimpleGraph U}
    (f : G ≃g J) : energy J = energy G := by
  unfold energy
  exact (Fintype.sum_equiv f.toEquiv _ _ (fun v => by
    exact congrArg (fun x : ℝ => x ^ 2) (degreeR_iso f v).symm)).symm

lemma score_iso [Fintype V] [Fintype U] {G : SimpleGraph V} {J : SimpleGraph U}
    (f : G ≃g J) (lam : ℝ) : score lam J = score lam G := by
  simp only [score, edgesR_iso f, energy_iso f]

noncomputable def potential [Fintype V] (lam mu : ℝ) (G : SimpleGraph V) : ℝ :=
  score lam G - mu * (Fintype.card V : ℝ)^2

lemma potential_iso [Fintype V] [Fintype U] {G : SimpleGraph V} {J : SimpleGraph U}
    (f : G ≃g J) (lam mu : ℝ) : potential lam mu J = potential lam mu G := by
  simp only [potential, score_iso f, Fintype.card_congr f.toEquiv]

/-- Optimality ranges over every finite order, not just the order of G. -/
structure GlobalOptimal [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (lam mu : ℝ) : Prop where
  free : H.Free G
  compare_fin : ∀ (m : ℕ) (J : SimpleGraph (Fin m)), H.Free J →
    potential lam mu J ≤ potential lam mu G

lemma GlobalOptimal.compare_graph [Fintype V] [Fintype U]
    {H : SimpleGraph W} {G : SimpleGraph V} {lam mu : ℝ}
    (hg : GlobalOptimal H G lam mu) (J : SimpleGraph U) (hf : H.Free J) :
    potential lam mu J ≤ potential lam mu G := by
  let e : U ≃ Fin (Fintype.card U) := Fintype.equivFin U
  let K := J.map e.toEmbedding
  let f : J ≃g K := Iso.map e J
  have hk : H.Free K := fun h => hf (h.trans ⟨f.symm.toCopy⟩)
  have hh := hg.compare_fin _ K hk
  rwa [potential_iso f] at hh

lemma GlobalOptimal.optimal [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) : Optimal H G lam := by
  refine ⟨hg.free, ?_⟩
  intro J hJ
  have hh := hg.compare_graph J hJ
  unfold potential at hh
  linarith

lemma GlobalOptimal.safe_clone [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (v : V)
    (hf : H.Free (clone G v)) :
    score lam (clone G v) ≤ score lam G + mu * (2 * Fintype.card V + 1) := by
  have hh := hg.compare_graph (clone G v) hf
  unfold potential at hh
  simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one] at hh
  nlinarith only [hh]

lemma GlobalOptimal.fold_mass [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    2 * edgesR G - lam * (3 * energy G + 2 * edgesR G) -
        (Fintype.card V : ℝ) * (mu * (2 * Fintype.card V + 1)) ≤
      ∑ v, if SingleFold H G v then degreeR G v else 0 := by
  exact fold_degree_mass H G hg.free hlam (by positivity) hg.safe_clone

lemma score_le_extremal [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) {lam : ℝ} (hlam : 0 ≤ lam) :
    score lam G ≤ (extremalNumber (Fintype.card V) H : ℝ) := by
  have hh := card_edgeFinset_le_extremalNumber hf
  have he : edgesR G ≤ (extremalNumber (Fintype.card V) H : ℝ) := by
    unfold edgesR
    exact_mod_cast (by simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using hh)
  unfold score
  exact (sub_le_self _ (mul_nonneg hlam (energy_nonneg G))).trans he

/-- A positive baseline and the subquadratic extremal bound give a genuine
maximizer over all orders. The energy parameter stays fixed during this
maximization. -/
theorem exists_global (H : SimpleGraph W) (hH : H ≠ ⊥) {lam mu : ℝ}
    (hlam : 0 ≤ lam) (hmu : 0 < mu)
    (hz : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ)^2) atTop (𝓝 0))
    {k : ℕ} (K : SimpleGraph (Fin k)) (hK : H.Free K)
    (hpos : 0 < potential lam mu K) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), GlobalOptimal H G lam mu ∧
      potential lam mu K ≤ potential lam mu G := by
  classical
  choose g hg using fun n : ℕ =>
    exists_optimal (V := Fin n) H lam ⟨⊥, free_bot hH⟩
  have htail : ∀ᶠ n : ℕ in atTop,
      (extremalNumber n H : ℝ) - mu * (n : ℝ)^2 < 0 := by
    filter_upwards [hz.eventually_lt_const hmu, eventually_gt_atTop (0 : ℕ)] with n hn hnp
    have hp : 0 < (n : ℝ)^2 := by positivity
    have hh := (div_lt_iff₀ hp).mp hn
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp htail
  obtain ⟨n, _, hmax⟩ := (range (M + k + 1)).exists_max_image
    (fun n => potential lam mu (g n)) ⟨k, by simp⟩
  have hbase : potential lam mu K ≤ potential lam mu (g k) := by
    have hh := (hg k).compare K hK
    unfold potential
    linarith
  have hkn : potential lam mu K ≤ potential lam mu (g n) :=
    hbase.trans (hmax k (by simp))
  refine ⟨n, g n, ⟨(hg n).free, ?_⟩, hkn⟩
  intro m J hJ
  have hjg : potential lam mu J ≤ potential lam mu (g m) := by
    have hh := (hg m).compare J hJ
    unfold potential
    linarith
  apply hjg.trans
  by_cases hm : m < M + k + 1
  · exact hmax m (mem_range.mpr hm)
  · have he := score_le_extremal H (g m) (hg m).free hlam
    have ht := hM m (by omega)
    simp only [Fintype.card_fin] at he
    unfold potential
    simp only [Fintype.card_fin]
    have hp : 0 < potential lam mu (g n) := hpos.trans_le hkn
    unfold potential at hp
    simp only [Fintype.card_fin] at hp
    linarith

lemma degreeR_induce_le [Fintype V] (G : SimpleGraph V) (S : Set V) (v : S) :
    degreeR (G.induce S) v ≤ degreeR G v.val := by
  classical
  let f : (G.induce S).neighborSet v → G.neighborSet v.val :=
    fun w => ⟨w.val.val, w.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : G.neighborSet v.val => z.val) hab))
  unfold degreeR
  exact_mod_cast Nat.card_le_card_of_injective f hf

lemma energy_induce_le [Fintype V] (G : SimpleGraph V) (S : Set V) :
    energy (G.induce S) ≤ energy G := by
  classical
  have hle : energy (G.induce S) ≤ ∑ v : S, degreeR G v.val ^ 2 := by
    unfold energy
    apply sum_le_sum
    intro v _
    exact pow_le_pow_left₀ (degreeR_nonneg _ _) (degreeR_induce_le G S v) 2
  apply hle.trans
  calc
    _ = ∑ v ∈ S.toFinset, degreeR G v ^ 2 :=
      (sum_subtype S.toFinset (fun x => by simp) (fun v => degreeR G v ^ 2)).symm
    _ ≤ energy G := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun _ _ _ => sq_nonneg _)

/-- Deleting a vertex supplies a lower degree bound on the same globally
optimal host. The upper bound comes from deletion of its incident edges. -/
lemma GlobalOptimal.degree_bounds [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 < lam) (v : V) :
    mu * (2 * Fintype.card V - 1) ≤ degreeR G v ∧ degreeR G v ≤ 1 / lam := by
  classical
  refine ⟨?_, hg.optimal.degree_bound hlam v⟩
  let S : Set V := {v}ᶜ
  let J := G.induce S
  have hf : H.Free J := fun h => hg.free (h.trans ⟨Copy.induce G S⟩)
  have hcomp := hg.compare_graph J hf
  have henergy := mul_le_mul_of_nonneg_left (energy_induce_le G S) hlam.le
  have he : edgesR J = edgesR G - degreeR G v := by
    have hh := G.card_edgeFinset_induce_compl_singleton v
    simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hh
    change (Nat.card (G.induce {v}ᶜ).edgeSet : ℝ) = _
    rw [hh]
    exact deletion_edges G v
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hcard : Fintype.card S = Fintype.card V - 1 := by
    change Fintype.card {x : V // ¬ x = v} = _
    rw [Fintype.card_subtype_compl]
    simp
  unfold potential at hcomp
  rw [hcard, Nat.cast_sub hn, Nat.cast_one] at hcomp
  unfold score at hcomp
  rw [he] at hcomp
  have henergy' : lam * energy J ≤ lam * energy G := by
    convert henergy using 1
    congr 2
    exact Subsingleton.elim _ _
  nlinarith only [hcomp, henergy']

lemma energy_le_max_degree [Fintype V] (G : SimpleGraph V) {D : ℝ}
    (hD : ∀ v, degreeR G v ≤ D) : energy G ≤ 2 * D * edgesR G := by
  have hpoint (v : V) : degreeR G v ^ 2 ≤ D * degreeR G v := by
    have hh := mul_le_mul_of_nonneg_right (hD v) (degreeR_nonneg G v)
    nlinarith only [hh]
  have hh := sum_le_sum (s := (univ : Finset V)) (fun v _ => hpoint v)
  rw [← mul_sum, degreeR_sum] at hh
  unfold energy
  nlinarith only [hh]

#print axioms GlobalOptimal.degree_bounds
#print axioms energy_le_max_degree
#print axioms score_iso
#print axioms GlobalOptimal.compare_graph
#print axioms GlobalOptimal.optimal
#print axioms GlobalOptimal.safe_clone
#print axioms GlobalOptimal.fold_mass
#print axioms exists_global
end Erdos713DegreePenaltySupports
