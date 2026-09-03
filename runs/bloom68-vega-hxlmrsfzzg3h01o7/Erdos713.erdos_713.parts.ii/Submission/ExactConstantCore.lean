import FormalConjecturesUtil

/-!
# A defect-controlled induced core

These lemmas give a structural consequence of an exact positive leading
constant for an ordinary forbidden-subgraph extremal number. They do not
assert rationality of the exponent, and do not import `Submission.Spec`.

The finite lemma uses the potential `e(G) - p(v(G))`: deleting a vertex
whose degree is less than `p(m) - p(m - 1)` increases this potential.
The core remains an induced subgraph of the host. Forbidden-subgraph
freeness below is still ordinary injective freeness, not induced freeness.
-/

open SimpleGraph Filter Asymptotics
open scoped Topology

namespace Erdos713ExactCore

universe u v

open scoped Classical in
/-- Peeling with an arbitrary real potential produces an induced core with
at least the original potential and with the corresponding minimum degree.
No monotonicity or sign assumption on the potential is needed. -/
theorem exists_induced_degree_core {V : Type u} [Fintype V]
    (G : SimpleGraph V) (p : ℕ → ℝ) :
    ∃ m : ℕ, ∃ K : SimpleGraph (Fin m),
      Nonempty (K ↪g G) ∧ m ≤ Fintype.card V ∧
      (∀ x, p m - p (m - 1) ≤ (K.degree x : ℝ)) ∧
      (G.edgeFinset.card : ℝ) - p (Fintype.card V) ≤
        (K.edgeFinset.card : ℝ) - p m := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hd : ∀ x, p (Fintype.card V) - p (Fintype.card V - 1) ≤
        (G.degree x : ℝ)
    · let e := Fintype.equivFin V
      let K : SimpleGraph (Fin (Fintype.card V)) := G.map e.toEmbedding
      letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
      refine ⟨Fintype.card V, K, ⟨(Iso.map e G).symm.toEmbedding⟩,
        hn.le, ?_, ?_⟩
      · intro x
        have heq := (Iso.map e G).degree_eq (e.symm x)
        change K.degree (e (e.symm x)) = G.degree (e.symm x) at heq
        rw [e.apply_symm_apply] at heq
        rw [heq]
        exact hd (e.symm x)
      · have heq := (Iso.map e G).card_edgeFinset_eq
        change G.edgeFinset.card = K.edgeFinset.card at heq
        rw [heq, ← hn]
    · push_neg at hd
      obtain ⟨x, hx⟩ := hd
      let S : Set V := {x}ᶜ
      have hsize : Fintype.card S < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := x) (by simp [S])
      have hsize_eq : Fintype.card S = Fintype.card V - 1 := by
        change Fintype.card ({x}ᶜ : Set V) = Fintype.card V - 1
        rw [Fintype.card_compl_set]
        simp only [Fintype.card_unique]
      obtain ⟨m, K, ⟨f⟩, hm, hdeg, hpot⟩ :=
        ih (Fintype.card S) hsize (G.induce S) rfl
      refine ⟨m, K, ⟨(SimpleGraph.Embedding.induce S).comp f⟩,
        hm.trans (by omega), hdeg, ?_⟩
      have hedge : (G.induce S).edgeFinset.card + G.degree x = G.edgeFinset.card := by
        change (G.induce ({x}ᶜ : Set V)).edgeFinset.card + G.degree x = G.edgeFinset.card
        rw [G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet]
        exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset x)
      have hedge' : ((G.induce S).edgeFinset.card : ℝ) + (G.degree x : ℝ) =
          (G.edgeFinset.card : ℝ) := by exact_mod_cast hedge
      rw [hsize_eq] at hpot
      rw [← hn]
      linarith

open scoped Classical in
/-- Quantitative core lemma. Suppose the edge count of the host is at least
`p(n) - A`, and every relevant extremal number is at most `p(m) + B`.
Peeling with potential `(1 - ε) * p` loses at most `(A + B) / ε` in `p`.
The conclusion retains ordinary `H`-freeness and induced containment. -/
theorem exists_defect_controlled_core {V : Type u} {W : Type v} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (p : ℕ → ℝ) (ε A B : ℝ)
    (hfree : H.Free G)
    (hlower : p (Fintype.card V) - A ≤ (G.edgeFinset.card : ℝ))
    (hupper : ∀ m ≤ Fintype.card V, (extremalNumber m H : ℝ) ≤ p m + B) :
    ∃ m : ℕ, ∃ K : SimpleGraph (Fin m),
      Nonempty (K ↪g G) ∧ m ≤ Fintype.card V ∧ H.Free K ∧
      (∀ x, (1 - ε) * (p m - p (m - 1)) ≤ (K.degree x : ℝ)) ∧
      ε * (p (Fintype.card V) - p m) ≤ A + B ∧
      (G.edgeFinset.card : ℝ) - (K.edgeFinset.card : ℝ) ≤
        (1 - ε) * (p (Fintype.card V) - p m) := by
  classical
  obtain ⟨m, K, ⟨f⟩, hm, hdeg, hpot⟩ :=
    exists_induced_degree_core G (fun j => (1 - ε) * p j)
  have hKfree : H.Free K := fun hK => hfree (hK.trans ⟨f.toCopy⟩)
  have hKbound : (K.edgeFinset.card : ℝ) ≤ p m + B := by
    have h := card_edgeFinset_le_extremalNumber hKfree
    rw [Fintype.card_fin] at h
    exact (by exact_mod_cast h : (K.edgeFinset.card : ℝ) ≤
      (extremalNumber m H : ℝ)).trans (hupper m hm)
  refine ⟨m, K, ⟨f⟩, hm, hKfree, ?_, ?_, ?_⟩
  · intro x
    have hx := hdeg x
    nlinarith
  · nlinarith
  · nlinarith


/-- A pure-power asymptotic is uniformly accurate on all smaller arguments,
when the error is measured at the current scale `n ^ a`. In particular, no
smoothness of the discrete increments of the sequence is being assumed. -/
lemma eventually_uniform_power_error {f : ℕ → ℝ} {a c : ℝ}
    (ha : 0 < a) (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ m ≤ n, |f m - c * (m : ℝ) ^ a| ≤ η * (n : ℝ) ^ a := by
  have herr := hf.isLittleO.of_const_mul_right.bound hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp herr
  let C : ℝ := ∑ j ∈ Finset.range N, |f j - c * (j : ℝ) ^ a|
  have ht : Tendsto (fun n : ℕ => η * (n : ℝ) ^ a) atTop atTop :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).const_mul_atTop hη
  filter_upwards [ht.eventually_ge_atTop C] with n hn
  intro m hmn
  by_cases hm : N ≤ m
  · have h := hN m hm
    simp only [Pi.sub_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) a)] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmn) ha.le) hη.le)
  · have hmN : m ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hC : |f m - c * (m : ℝ) ^ a| ≤ C :=
      Finset.single_le_sum (fun j _ => abs_nonneg (f j - c * (j : ℝ) ^ a)) hmN
    exact hC.trans hn

open scoped Classical in
/-- Exact positive power asymptotics give cores losing arbitrarily small
fractions of vertices and edges. The degree threshold is the discrete
increment of the power potential, not an assumed derivative of `ex(n,H)`.
This works for every extremal host, uniformly once `n` is sufficiently large. -/
theorem eventually_near_spanning_core {W : Type v} (H : SimpleGraph W)
    {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a))
    {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), H.Free G →
      G.edgeFinset.card = extremalNumber n H →
      ∃ m : ℕ, ∃ K : SimpleGraph (Fin m),
        Nonempty (K ↪g G) ∧ m ≤ n ∧ H.Free K ∧
        (1 - ρ) * (n : ℝ) ≤ (m : ℝ) ∧
        (∀ x, (1 - ε) * c * ((m : ℝ) ^ a - ((m - 1 : ℕ) : ℝ) ^ a) ≤
          (K.degree x : ℝ)) ∧
        (G.edgeFinset.card : ℝ) - (K.edgeFinset.card : ℝ) ≤ ρ * c * (n : ℝ) ^ a := by
  classical
  let η := ε * ρ * c / 2
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [eventually_uniform_power_error (lt_trans zero_lt_one ha) hf hη]
    with n hn
  intro G hG hmax
  let p : ℕ → ℝ := fun j => c * (j : ℝ) ^ a
  have hlower : p (Fintype.card (Fin n)) - η * (n : ℝ) ^ a ≤
      (G.edgeFinset.card : ℝ) := by
    rw [Fintype.card_fin, hmax]
    have h := (abs_le.mp (hn n le_rfl)).1
    dsimp [p]
    linarith
  have hupper : ∀ j ≤ Fintype.card (Fin n),
      (extremalNumber j H : ℝ) ≤ p j + η * (n : ℝ) ^ a := by
    intro j hj
    rw [Fintype.card_fin] at hj
    have h := (abs_le.mp (hn j hj)).2
    dsimp [p]
    linarith
  obtain ⟨m, K, hKG, hm, hK, hd, hb, he⟩ := exists_defect_controlled_core
    G H p ε (η * (n : ℝ) ^ a) (η * (n : ℝ) ^ a) hG hlower hupper
  simp only [Fintype.card_fin] at hm hb he
  have hp : (1 - ρ) * (n : ℝ) ^ a ≤ (m : ℝ) ^ a := by
    dsimp [p, η] at hb
    nlinarith [mul_pos hε hc]
  have hmn : (1 - ρ) * (n : ℝ) ≤ (m : ℝ) := by
    by_contra! hlt
    have hltpow := Real.rpow_lt_rpow (Nat.cast_nonneg m) hlt (lt_trans zero_lt_one ha)
    rw [Real.mul_rpow (sub_nonneg.mpr hρ1.le) (Nat.cast_nonneg n)] at hltpow
    have hbase : (1 - ρ) ^ a ≤ 1 - ρ :=
      Real.rpow_le_self_of_le_one (sub_nonneg.mpr hρ1.le) (by linarith) ha.le
    have hbound := mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (Nat.cast_nonneg n) a)
    linarith
  refine ⟨m, K, hKG, hm, hK, hmn, ?_, ?_⟩
  · intro x
    have hdx := hd x
    dsimp [p] at hdx
    nlinarith
  · dsimp [p] at he
    have hnp : 0 ≤ (n : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg n) a
    have hdiff : c * (n : ℝ) ^ a - c * (m : ℝ) ^ a ≤ ρ * c * (n : ℝ) ^ a := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hdiff (sub_nonneg.mpr hε1.le)
    have hnonneg : 0 ≤ ρ * c * (n : ℝ) ^ a := by positivity
    nlinarith

end Erdos713ExactCore

#print axioms Erdos713ExactCore.exists_induced_degree_core
#print axioms Erdos713ExactCore.exists_defect_controlled_core
#print axioms Erdos713ExactCore.eventually_uniform_power_error
#print axioms Erdos713ExactCore.eventually_near_spanning_core
