import Submission.WeightedReduction
import Submission.APReduction
import Submission.APGluing

/-! Finite endpoint and sliding-window bounds for sets avoiding a fixed AP length. -/

namespace Erdos3Window

open Erdos3Weighted

/-- Right endpoints of the runs with step `d`. -/
def endpoints (F : Finset ℕ) (d : ℕ) : Finset ℕ :=
  F.filter (fun a ↦ a + d ∉ F)

lemma exists_missing_term {k d : ℕ} {F : Finset ℕ}
    (hd : 0 < d) (hF : Avoids k (F : Set ℕ)) (a : ℕ) :
    ∃ j < k, a + j * d ∉ F := by
  by_contra! h
  apply hF {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} ?_
    ⟨a, d, Erdos3Reduction.isAPOfLengthWith_prefix (Nat.ne_of_gt hd) k⟩
  rintro x ⟨n, hn, rfl⟩
  simpa only [nsmul_eq_mul] using h n (by exact_mod_cast hn)

lemma exists_endpoint {k d : ℕ} {F : Finset ℕ}
    (hd : 0 < d) (hF : Avoids k (F : Set ℕ)) {a : ℕ} (ha : a ∈ F) :
    ∃ j < k - 1, a + j * d ∈ endpoints F d := by
  classical
  have hex := exists_missing_term hd hF a
  let j := Nat.find hex
  have hj : j < k ∧ a + j * d ∉ F := Nat.find_spec hex
  have hjpos : 1 ≤ j := by
    by_contra h
    have hz : j = 0 := by omega
    exact hj.2 (by simpa only [hz, zero_mul, add_zero] using ha)
  have hprev : a + (j - 1) * d ∈ F := by
    by_contra h
    exact Nat.find_min hex (show j - 1 < j by omega) ⟨by omega, h⟩
  refine ⟨j - 1, by omega, Finset.mem_filter.mpr ⟨hprev, ?_⟩⟩
  have heq : a + (j - 1) * d + d = a + j * d := by
    calc
      a + (j - 1) * d + d = a + (j - 1 + 1) * d := by ring
      _ = a + j * d := by rw [Nat.sub_add_cancel hjpos]
  simpa only [heq] using hj.2

lemma subset_endpoint_image {k d : ℕ} {F : Finset ℕ}
    (hd : 0 < d) (hF : Avoids k (F : Set ℕ)) :
    F ⊆ ((endpoints F d) ×ˢ Finset.range (k - 1)).image
      (fun p : ℕ × ℕ ↦ p.1 - p.2 * d) := by
  intro a ha
  obtain ⟨j, hj, he⟩ := exists_endpoint hd hF ha
  exact Finset.mem_image.mpr ⟨(a + j * d, j),
    Finset.mem_product.mpr ⟨he, Finset.mem_range.mpr hj⟩, Nat.add_sub_cancel a (j * d)⟩

/-- In particular this gives the endpoint bound for every `k ≥ 3`. -/
theorem card_le_mul_endpoints {k d : ℕ} {F : Finset ℕ}
    (hd : 0 < d) (hF : Avoids k (F : Set ℕ)) :
    F.card ≤ (k - 1) * (endpoints F d).card := by
  calc
    F.card ≤ (((endpoints F d) ×ˢ Finset.range (k - 1)).image
        (fun p : ℕ × ℕ ↦ p.1 - p.2 * d)).card :=
      Finset.card_le_card (subset_endpoint_image hd hF)
    _ ≤ ((endpoints F d) ×ˢ Finset.range (k - 1)).card := Finset.card_image_le
    _ = (k - 1) * (endpoints F d).card := by simp [mul_comm]

/-- The points of `F` in `[n + 1, n + m]`. -/
def window (F : Finset ℕ) (n m : ℕ) : Finset ℕ :=
  F.filter (fun a ↦ n < a ∧ a ≤ n + m)

/-- The exact left-boundary error in the window sum. -/
def boundaryError (F : Finset ℕ) (m : ℕ) : ℕ :=
  ∑ t ∈ Finset.Icc 1 m, (window F 0 t).card

lemma endpoint_window_eq_insert {F : Finset ℕ} {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (he : n ∈ endpoints F m) :
    window F (n - 1) m = insert n (window F n m) := by
  obtain ⟨hnF, hnout⟩ := Finset.mem_filter.mp he
  ext a
  simp only [window, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨haF, ha₁, ha₂⟩
    by_cases h : a = n
    · exact Or.inl h
    · exact Or.inr ⟨haF, by omega, by omega⟩
  · rintro (rfl | ⟨haF, ha₁, ha₂⟩)
    · exact ⟨hnF, by omega, by omega⟩
    · have hne : a ≠ n + m := by
        intro h
        exact hnout (h ▸ haF)
      exact ⟨haF, by omega, by omega⟩

lemma endpoint_window_drop {F : Finset ℕ} {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (he : n ∈ endpoints F m) :
    (window F (n - 1) m).card = (window F n m).card + 1 := by
  rw [endpoint_window_eq_insert hn hm he, Finset.card_insert_of_notMem]
  simp [window]

lemma sum_windows_add_endpoints_le {F : Finset ℕ} {N m R : ℕ}
    (hFN : F ⊆ Finset.Icc 1 N) (hm : 1 ≤ m)
    (hcap : ∀ n ≤ N, (window F n m).card ≤ R) :
    (∑ n ∈ Finset.Icc 1 N, (window F n m).card) + (endpoints F m).card ≤ N * R := by
  classical
  have hD : endpoints F m ⊆ Finset.Icc 1 N :=
    (Finset.filter_subset _ F).trans hFN
  have hfilter : (Finset.Icc 1 N).filter (fun n ↦ n ∈ endpoints F m) =
      endpoints F m := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hn ↦ ⟨hD hn, hn⟩⟩
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 N)
    (f := fun n ↦ (window F n m).card + if n ∈ endpoints F m then 1 else 0)
    (g := fun _ ↦ R) (by
      intro n hn
      dsimp only
      have hn' := Finset.mem_Icc.mp hn
      by_cases he : n ∈ endpoints F m
      · rw [if_pos he, ← endpoint_window_drop hn'.1 hm he]
        exact hcap (n - 1) (by omega)
      · simpa only [if_neg he, add_zero] using hcap n hn'.2)
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, hfilter,
    Nat.cast_id, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    smul_eq_mul] using hsum

lemma window_incidence_count {a N m : ℕ} (ha : a ∈ Finset.Icc 1 N) :
    ((Finset.Icc 1 N).filter (fun n ↦ n < a ∧ a ≤ n + m)).card +
      ((Finset.Icc 1 m).filter (fun t ↦ 0 < a ∧ a ≤ t)).card = m := by
  have ha' := Finset.mem_Icc.mp ha
  have h₁ : (Finset.Icc 1 N).filter (fun n ↦ n < a ∧ a ≤ n + m) =
      Finset.Ico (max 1 (a - m)) a := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, max_le_iff]
    omega
  have h₂ : (Finset.Icc 1 m).filter (fun t ↦ 0 < a ∧ a ≤ t) =
      Finset.Icc a m := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h₁, h₂, Nat.card_Ico, Nat.card_Icc]
  omega

/-- Double counting, with no truncating subtraction and no assumption `m ≤ N`. -/
theorem sum_windows_add_boundary {F : Finset ℕ} {N : ℕ}
    (hFN : F ⊆ Finset.Icc 1 N) (m : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (window F n m).card) + boundaryError F m = m * F.card := by
  have h₁ : (∑ n ∈ Finset.Icc 1 N, (window F n m).card) =
      ∑ a ∈ F, ((Finset.Icc 1 N).filter (fun n ↦ n < a ∧ a ≤ n + m)).card := by
    simp only [window, Finset.card_filter]
    exact Finset.sum_comm
  have h₂ : boundaryError F m =
      ∑ a ∈ F, ((Finset.Icc 1 m).filter (fun t ↦ 0 < a ∧ a ≤ t)).card := by
    simp only [boundaryError, window, Finset.card_filter, zero_add]
    exact Finset.sum_comm
  rw [h₁, h₂, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _a ∈ F, m := Finset.sum_congr rfl (fun a ha ↦ window_incidence_count (hFN ha))
    _ = m * F.card := by simp [mul_comm]

/-- Cleared-denominator window bound with a scalar cap and the exact prefix error. -/
theorem window_bound {k N m R : ℕ} {F : Finset ℕ}
    (hm : 1 ≤ m) (hF : Avoids k (F : Set ℕ)) (hFN : F ⊆ Finset.Icc 1 N)
    (hcap : ∀ n ≤ N, (window F n m).card ≤ R) :
    ((k - 1) * m + 1) * F.card ≤ (k - 1) * (N * R + boundaryError F m) := by
  have he := card_le_mul_endpoints (by omega : 0 < m) hF
  have hw := sum_windows_add_endpoints_le hFN hm hcap
  have hc := sum_windows_add_boundary hFN m
  calc
    ((k - 1) * m + 1) * F.card =
        (k - 1) * ((∑ n ∈ Finset.Icc 1 N, (window F n m).card) + boundaryError F m) +
          F.card := by rw [hc]; ring
    _ ≤ (k - 1) * ((∑ n ∈ Finset.Icc 1 N, (window F n m).card) + boundaryError F m) +
          (k - 1) * (endpoints F m).card := Nat.add_le_add_left he _
    _ = (k - 1) * ((∑ n ∈ Finset.Icc 1 N, (window F n m).card) +
          (endpoints F m).card + boundaryError F m) := by ring
    _ ≤ (k - 1) * (N * R + boundaryError F m) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right hw _)

lemma exists_normalized_window {k : ℕ} {F : Finset ℕ}
    (hF : Avoids k (F : Set ℕ)) (n m : ℕ) :
    ∃ G : Finset ℕ, G ⊆ Finset.Icc 1 m ∧ Avoids k (G : Set ℕ) ∧
      G.card = (window F n m).card := by
  let G := (window F n m).image (fun a ↦ a - n)
  have hmem : ∀ a ∈ window F n m, n < a ∧ a ≤ n + m := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  refine ⟨G, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have hb' := hmem b hb
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · apply (Erdos3Gluing.no_isAPOfLength_image_add_iff (E := (G : Set ℕ))
      (l := (k : ℕ∞)) n).mp
    apply avoids_subset hF
    rintro a ⟨b, hb, rfl⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    have hc' := Finset.mem_filter.mp hc
    have heq : n + (c - n) = c := by omega
    simpa only [heq] using hc'.1
  · apply Finset.card_image_of_injOn
    intro a ha b hb hab
    dsimp only at hab
    have ha' := hmem a ha
    have hb' := hmem b hb
    omega

/-- The maximum size of an AP-free subset of `[1, n]` (attained for `k > 0`). -/
noncomputable def extremal (k n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter
    (fun F : Finset ℕ ↦ Avoids k (F : Set ℕ))).sup Finset.card

lemma card_le_extremal {k n : ℕ} {F : Finset ℕ}
    (hFn : F ⊆ Finset.Icc 1 n) (hF : Avoids k (F : Set ℕ)) :
    F.card ≤ extremal k n := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hFn, hF⟩)

lemma avoids_empty {k : ℕ} (hk : 0 < k) : Avoids k (∅ : Set ℕ) := by
  intro S hS
  rw [Set.subset_empty_iff.mp hS]
  exact Set.not_isAPOfLength_empty (by exact_mod_cast hk)

lemma exists_extremal {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ∃ F : Finset ℕ, F ⊆ Finset.Icc 1 n ∧ Avoids k (F : Set ℕ) ∧ F.card = extremal k n := by
  classical
  let s := (Finset.Icc 1 n).powerset.filter (fun F : Finset ℕ ↦ Avoids k (F : Set ℕ))
  have hs : s.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    simpa only [Finset.coe_empty] using avoids_empty hk
  obtain ⟨F, hFs, hcard⟩ := Finset.exists_mem_eq_sup s hs Finset.card
  obtain ⟨hFn, hF⟩ := Finset.mem_filter.mp hFs
  exact ⟨F, Finset.mem_powerset.mp hFn, hF, hcard.symm⟩

lemma window_card_le_extremal {k : ℕ} {F : Finset ℕ}
    (hF : Avoids k (F : Set ℕ)) (n m : ℕ) :
    (window F n m).card ≤ extremal k m := by
  obtain ⟨G, hGm, hG, hcard⟩ := exists_normalized_window hF n m
  rw [← hcard]
  exact card_le_extremal hGm hG

lemma boundaryError_le_sum_extremal {k : ℕ} {F : Finset ℕ}
    (hF : Avoids k (F : Set ℕ)) (m : ℕ) :
    boundaryError F m ≤ ∑ t ∈ Finset.Icc 1 m, extremal k t := by
  exact Finset.sum_le_sum (fun t _ ↦ window_card_le_extremal hF 0 t)

theorem card_window_bound_extremal {k N m : ℕ} {F : Finset ℕ}
    (hm : 1 ≤ m) (hF : Avoids k (F : Set ℕ)) (hFN : F ⊆ Finset.Icc 1 N) :
    ((k - 1) * m + 1) * F.card ≤
      (k - 1) * (N * extremal k m + ∑ t ∈ Finset.Icc 1 m, extremal k t) := by
  exact (window_bound hm hF hFN (fun n _ ↦ window_card_le_extremal hF n m)).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (boundaryError_le_sum_extremal hF m) _))

/-- The extremal sliding-window inequality, with denominators cleared in `ℕ`. -/
theorem extremal_window_bound {k N m : ℕ} (hk : 3 ≤ k) (hm : 1 ≤ m) :
    ((k - 1) * m + 1) * extremal k N ≤
      (k - 1) * (N * extremal k m + ∑ t ∈ Finset.Icc 1 m, extremal k t) := by
  obtain ⟨F, hFN, hF, hcard⟩ := exists_extremal (by omega : 0 < k) N
  simpa only [hcard] using card_window_bound_extremal hm hF hFN

/-- The real form; in particular it applies whenever `1 ≤ m ≤ N`. -/
theorem extremal_window_bound_real {k N m : ℕ} (hk : 3 ≤ k) (hm : 1 ≤ m) :
    ((m : ℝ) + 1 / ((k : ℝ) - 1)) * (extremal k N : ℝ) ≤
      (N : ℝ) * (extremal k m : ℝ) + ∑ t ∈ Finset.Icc 1 m, (extremal k t : ℝ) := by
  have hnat := extremal_window_bound (N := N) hk hm
  have hreal : (((k - 1 : ℕ) : ℝ) * (m : ℝ) + 1) * (extremal k N : ℝ) ≤
      ((k - 1 : ℕ) : ℝ) *
        ((N : ℝ) * (extremal k m : ℝ) + ∑ t ∈ Finset.Icc 1 m, (extremal k t : ℝ)) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at hreal
  have hkreal : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  apply (mul_le_mul_iff_right₀ hkpos).mp
  calc
    ((k : ℝ) - 1) * (((m : ℝ) + 1 / ((k : ℝ) - 1)) * (extremal k N : ℝ)) =
        (((k : ℝ) - 1) * (m : ℝ) + 1) * (extremal k N : ℝ) := by
      rw [← mul_assoc, mul_add, mul_one_div_cancel (ne_of_gt hkpos)]
    _ ≤ ((k : ℝ) - 1) *
        ((N : ℝ) * (extremal k m : ℝ) + ∑ t ∈ Finset.Icc 1 m, (extremal k t : ℝ)) := hreal

end Erdos3Window

#print axioms Erdos3Window.card_le_mul_endpoints
#print axioms Erdos3Window.endpoint_window_drop
#print axioms Erdos3Window.sum_windows_add_endpoints_le
#print axioms Erdos3Window.sum_windows_add_boundary
#print axioms Erdos3Window.window_bound
#print axioms Erdos3Window.exists_extremal
#print axioms Erdos3Window.window_card_le_extremal
#print axioms Erdos3Window.extremal_window_bound
#print axioms Erdos3Window.extremal_window_bound_real
