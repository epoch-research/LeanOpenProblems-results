import FormalConjecturesUtil
import Submission.Verified
import Submission.RootedFan
import Submission.Blocking

/-! The upper growth rate is preserved by a nonempty rooted fan. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713Fan
open Finset Erdos713Blocking Erdos713Rate

open scoped Classical in
theorem free_edge_bound {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) (x : W) (t : ℕ)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) (hfree : (fan H x t).Free G) :
    G.edgeFinset.card ≤ 2 ^ (2 * (t * Fintype.card W) + 2) *
      extremalNumber (Fintype.card V) H + (t * Fintype.card W) * Fintype.card V := by
  classical
  choose B hb hk hB using blockers_of_fan_free H G x t hfree
  apply edges_le_of_keep_bound G B (t * Fintype.card W) _ hb hk
  intro σ
  apply card_edgeFinset_le_extremalNumber
  rintro ⟨f⟩
  let g : H.Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp f
  obtain ⟨a, _, ha⟩ := hB (g x) g rfl
  have hsel (a : W) : selected B σ (f a) := by
    obtain ⟨b, hab⟩ := hNoIso a
    have hh := f.toHom.map_adj hab
    exact hh.2.1
  change f a ∈ B (f x) at ha
  have htrue := (hsel a).1
  have hfalse := (hsel x).2 (f a) ha
  exact Bool.noConfusion (htrue.symm.trans hfalse)

open scoped Classical in
theorem extremal_bound {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W) (t n : ℕ)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) :
    extremalNumber n (fan H x t) ≤ 2 ^ (2 * (t * Fintype.card W) + 2) *
      extremalNumber n H + (t * Fintype.card W) * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using free_edge_bound H G x t hNoIso hfree

theorem fan_upper {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W) (t : ℕ)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) {r : ℝ} (hr : 1 ≤ r)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    (fun n : ℕ => (extremalNumber n (fan H x t) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
  let C : ℕ := 2 ^ (2 * (t * Fintype.card W) + 2)
  have hA := hH.const_mul_left (C : ℝ)
  have hB := cast_linear_bigO hr (t * Fintype.card W)
  apply IsBigO.trans _ (hA.add hB)
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast extremal_bound H x t n hNoIso

theorem fan_rate {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W) {t : ℕ} (ht : 1 ≤ t)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) {r : ℝ} (h : HasRate H r) : HasRate (fan H x t) r := by
  refine ⟨h.one_le, fan_upper H x t hNoIso h.one_le h.upper, ?_⟩
  intro a ha hA
  exact h.lower a ha ((extremal_mono_bigO ⟨petalCopy H x ⟨0, by omega⟩⟩).trans hA)

theorem fan_rate_converse {W : Type*} [Fintype W] (H : SimpleGraph W) (x : W) {t : ℕ} (ht : 1 ≤ t)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) {r : ℝ} (h : HasRate (fan H x t) r) : HasRate H r := by
  refine ⟨h.one_le, (extremal_mono_bigO ⟨petalCopy H x ⟨0, by omega⟩⟩).trans h.upper, ?_⟩
  intro a ha hA
  exact h.lower a ha (fan_upper H x t hNoIso ha hA)

#print axioms extremal_bound
#print axioms fan_rate
#print axioms fan_rate_converse

end Erdos713Fan
