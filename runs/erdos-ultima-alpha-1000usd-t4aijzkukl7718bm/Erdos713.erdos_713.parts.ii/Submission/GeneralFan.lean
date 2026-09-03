import FormalConjecturesUtil
import Submission.Verified
import Submission.RootedFan
import Submission.Blocking
import Submission.SupportTransfer

/-! Rooted-fan rate preservation, including base graphs with isolated vertices. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713Fan
open Finset Erdos713Blocking Erdos713Rate

open scoped Classical in
theorem free_edge_bound_general {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) (x : W) (t : ℕ) (hfree : (fan H x t).Free G) :
    G.edgeFinset.card ≤ 2 ^ (2 * (t * Fintype.card W) + 2) *
      (extremalNumber (Fintype.card V) H + Fintype.card W * Fintype.card V) +
      (t * Fintype.card W) * Fintype.card V := by
  classical
  choose B hb hk hB using blockers_of_fan_free H G x t hfree
  apply edges_le_of_keep_bound G B (t * Fintype.card W) _ hb hk
  intro σ
  let S : Set V := {v | selected B σ v}
  have hS : (keep G B σ).support ⊆ S := by
    rintro v ⟨w, hvw⟩
    exact hvw.2.1
  apply Erdos713Support.edges_le_of_free_induce H (keep G B σ) S hS
  rintro ⟨f⟩
  let g : H.Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp ((Copy.induce _ S).comp f)
  obtain ⟨a, _, ha⟩ := hB (g x) g rfl
  have hsel (a : W) : selected B σ (f a).val := (f a).prop
  change (f a).val ∈ B (f x).val at ha
  exact Bool.noConfusion ((hsel a).1.symm.trans ((hsel x).2 (f a).val ha))

open scoped Classical in
theorem extremal_bound_general {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W) (t n : ℕ) :
    extremalNumber n (fan H x t) ≤ 2 ^ (2 * (t * Fintype.card W) + 2) *
      (extremalNumber n H + Fintype.card W * n) + (t * Fintype.card W) * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using free_edge_bound_general H G x t hfree

theorem fan_upper_general {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W) (t : ℕ)
    {r : ℝ} (hr : 1 ≤ r)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    (fun n : ℕ => (extremalNumber n (fan H x t) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
  let C : ℕ := 2 ^ (2 * (t * Fintype.card W) + 2)
  have hA := (hH.add (cast_linear_bigO hr (Fintype.card W))).const_mul_left (C : ℝ)
  have hB := cast_linear_bigO hr (t * Fintype.card W)
  apply IsBigO.trans _ (hA.add hB)
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast extremal_bound_general H x t n

theorem fan_rate_general {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W) {t : ℕ} (ht : 1 ≤ t)
    {r : ℝ} (h : HasRate H r) : HasRate (fan H x t) r := by
  refine ⟨h.one_le, fan_upper_general H x t h.one_le h.upper, ?_⟩
  intro a ha hA
  exact h.lower a ha ((extremal_mono_bigO ⟨petalCopy H x ⟨0, by omega⟩⟩).trans hA)

theorem fan_rate_converse_general {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W) {t : ℕ}
    (ht : 1 ≤ t) {r : ℝ} (h : HasRate (fan H x t) r) : HasRate H r := by
  refine ⟨h.one_le, (extremal_mono_bigO ⟨petalCopy H x ⟨0, by omega⟩⟩).trans h.upper, ?_⟩
  intro a ha hA
  exact h.lower a ha (fan_upper_general H x t ha hA)

theorem rate_of_sandwich {W U : Type*} [Fintype W] (J : SimpleGraph W) (x : W) (t : ℕ)
    {H : SimpleGraph U} (hlo : J ⊑ H) (hhi : H ⊑ fan J x t) {r : ℝ} (h : HasRate J r) :
    HasRate H r := by
  refine ⟨h.one_le, (extremal_mono_bigO hhi).trans (fan_upper_general J x t h.one_le h.upper), ?_⟩
  intro a ha hA
  exact h.lower a ha ((extremal_mono_bigO hlo).trans hA)

theorem rate_of_sandwich_converse {W U : Type*} [Fintype W] (J : SimpleGraph W) (x : W) (t : ℕ)
    {H : SimpleGraph U} (hlo : J ⊑ H) (hhi : H ⊑ fan J x t) {r : ℝ} (h : HasRate H r) :
    HasRate J r := by
  refine ⟨h.one_le, (extremal_mono_bigO hlo).trans h.upper, ?_⟩
  intro a ha hA
  exact h.lower a ha ((extremal_mono_bigO hhi).trans (fan_upper_general J x t ha hA))

#print axioms rate_of_sandwich
#print axioms rate_of_sandwich_converse
#print axioms extremal_bound_general
#print axioms fan_rate_general
#print axioms fan_rate_converse_general

end Erdos713Fan
