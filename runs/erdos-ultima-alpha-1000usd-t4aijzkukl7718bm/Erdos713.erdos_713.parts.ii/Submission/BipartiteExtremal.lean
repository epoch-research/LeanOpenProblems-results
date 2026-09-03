import FormalConjecturesUtil
import Submission.CompactCloneAudit

/-! Extremal numbers restricted to bipartite hosts. They are comparable with
ordinary extremal numbers, but no equality or exact-asymptotic transfer is
asserted. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713BipExtremal

open scoped Classical in
noncomputable def number (n : ℕ) {W : Type*} (H : SimpleGraph W) : ℕ :=
  ({G : SimpleGraph (Fin n) | H.Free G ∧ G.IsBipartite} : Finset _).sup
    (fun G => G.edgeFinset.card)

lemma card_bound_fin {W : Type*} (H : SimpleGraph W) {n : ℕ} (G : SimpleGraph (Fin n))
    (hfree : H.Free G) (hB : G.IsBipartite) : Nat.card G.edgeSet ≤ number n H := by
  classical
  change Nat.card G.edgeSet ≤
    ({K : SimpleGraph (Fin n) | H.Free K ∧ K.IsBipartite} : Finset _).sup (fun K => K.edgeFinset.card)
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using
    (le_sup (f := fun K : SimpleGraph (Fin n) => K.edgeFinset.card)
      (show G ∈ ({K : SimpleGraph (Fin n) | H.Free K ∧ K.IsBipartite} : Finset _) by exact mem_filter.mpr ⟨mem_univ G,hfree,hB⟩))

lemma card_bound {W V : Type*} [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hfree : H.Free G) (hB : G.IsBipartite) : Nat.card G.edgeSet ≤ number (Fintype.card V) H := by
  classical
  let e := Fintype.equivFin V
  let K := G.map e.toEmbedding
  let i : G ≃g K := Iso.map e G
  have hf : H.Free K := fun hh => hfree (hh.trans ⟨i.symm.toCopy⟩)
  have hb : K.IsBipartite := hB.of_hom i.symm.toHom
  have hc := card_bound_fin H K hf hb
  have hi := i.card_edgeFinset_eq
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hi
  rwa [← hi] at hc

lemma number_le {W : Type*} (H : SimpleGraph W) (n : ℕ) : number n H ≤ extremalNumber n H := by
  classical
  unfold number
  apply Finset.sup_le
  intro G hG
  obtain ⟨hf,hb⟩ : H.Free G ∧ G.IsBipartite := by simpa using hG
  simpa only [Fintype.card_fin] using card_edgeFinset_le_extremalNumber hf

lemma ordinary_le_two {W : Type*} (H : SimpleGraph W) (n : ℕ) :
    extremalNumber n H ≤ 2*number n H := by
  classical
  rw [← Fintype.card_fin n,extremalNumber_le_iff]
  intro G _ hf
  obtain ⟨K,hKG,hKB,hhalf⟩ := Erdos713Cut.exists_bipartite_half G
  have hfree : H.Free K := fun hh => hf (hh.mono_right hKG)
  have hk := card_bound_fin H K hfree hKB
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hhalf ⊢
  simpa only [Fintype.card_fin,Nat.card_fin] using hhalf.trans (Nat.mul_le_mul_left 2 hk)

lemma exists_extremal_of_pos {W : Type*} (H : SimpleGraph W) (n : ℕ) (hn : 0 < number n H) :
    ∃ G : SimpleGraph (Fin n), H.Free G ∧ G.IsBipartite ∧ Nat.card G.edgeSet = number n H := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | H.Free G ∧ G.IsBipartite}
  have hS : S.Nonempty := by
    by_contra hs
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp hs
    change 0 < S.sup (fun G => G.edgeFinset.card) at hn
    simp only [he,sup_empty,bot_eq_zero,lt_self_iff_false] at hn
  obtain ⟨G,hG,he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
  obtain ⟨hf,hb⟩ : H.Free G ∧ G.IsBipartite := by simpa [S] using hG
  refine ⟨G,hf,hb,?_⟩
  change Nat.card G.edgeSet = S.sup (fun G => G.edgeFinset.card)
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using he.symm

lemma number_zero {W : Type*} (H : SimpleGraph W) : number 0 H = 0 :=
  Nat.eq_zero_of_le_zero ((number_le H 0).trans_eq (Erdos713Cloning.extremal_zero H))

lemma clone_bipartite {V : Type*} {G : SimpleGraph V} (hG : G.IsBipartite) (v : V) :
    (Erdos713Cloning.clone G v).IsBipartite := hG.of_hom (Erdos713Cloning.projectionHom G v)

lemma safe_clone_bound {W V : Type*} [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hB : G.IsBipartite) (v : V) (hfree : H.Free (Erdos713Cloning.clone G v)) :
    Nat.card G.edgeSet+Nat.card (G.neighborSet v) ≤ number (Fintype.card V+1) H := by
  have hh := card_bound H (Erdos713Cloning.clone G v) hfree (clone_bipartite hB v)
  simpa only [Erdos713Cloning.card_edges_clone,Fintype.card_option] using hh

open scoped Topology in
lemma higher_ratio_zero {W : Type*} (H : SimpleGraph W) {α c r : ℝ} (har : α < r)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => (number n H : ℝ)/(n : ℝ)^r) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun n => div_le_div_of_nonneg_right (Nat.cast_le.mpr (number_le H n))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  exact Erdos713FutureRecords.higher_ratio_zero har h

lemma lower_ratio_top {W : Type*} (H : SimpleGraph W) {α c r : ℝ} (hra : r < α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => (number n H : ℝ)/(n : ℝ)^r) atTop atTop := by
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)*((extremalNumber n H : ℝ)/(n : ℝ)^r)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) (Erdos713FutureRecords.lower_ratio_top hra hc h)
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards with n
  have hh : (1/2 : ℝ)*(extremalNumber n H : ℝ) ≤ (number n H : ℝ) := by
    have hh : (extremalNumber n H : ℝ) ≤ 2*(number n H : ℝ) := by exact_mod_cast ordinary_le_two H n
    linarith
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh (Real.rpow_nonneg (Nat.cast_nonneg n) r)

#print axioms card_bound
#print axioms number_le
#print axioms ordinary_le_two
#print axioms safe_clone_bound
#print axioms higher_ratio_zero
#print axioms lower_ratio_top
end Erdos713BipExtremal
