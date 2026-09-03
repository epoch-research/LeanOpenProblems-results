import FormalConjecturesUtil

/-!
# Safe gluing of arithmetic-progression-free sets of natural numbers

The lower block lies in `[1, M]` and the upper block in `[2 * M, 3 * M)`.
Every progression of length at least three in their union lies in a single
block. The strict endpoints matter: a step inside either block is less than
`M`, whereas a step crossing the gap is at least `M`.

Translation preserves both arithmetic progressions and their absence. Thus an
AP-free set in `[1, M]` can be glued to the translate by `2 * M` of an AP-free
set in `[0, M)`. No finiteness hypothesis is needed for the set versions.

This file is independent of `Submission.Spec` and `Submission.APReduction`.
-/

namespace Erdos3Gluing

/-- The cardinality clause rules out a zero step for a nontrivial AP. -/
theorem isAPOfLengthWith_step_pos {S : Set ℕ} {l : ℕ∞} {a d : ℕ}
    (hS : S.IsAPOfLengthWith l a d) (hl : 1 < l) : 0 < d := by
  apply Nat.pos_of_ne_zero
  intro hd
  have hsub : S ⊆ ({a} : Set ℕ) := by
    rw [hS.eq]
    rintro x ⟨n, hn, rfl⟩
    simp [hd]
  have hcard : l ≤ 1 := by
    calc
      l = S.encard := hS.card.symm
      _ ≤ ({a} : Set ℕ).encard := Set.encard_le_encard hsub
      _ = 1 := Set.encard_singleton a
  exact (not_le_of_gt hl) hcard

/-- An AP of length at least three cannot cross between these separated blocks. -/
theorem isAPOfLength_subset_or_subset_of_separated
    {M k : ℕ} {X Y S : Set ℕ} (hM : 1 ≤ M) (hk : 3 ≤ k)
    (hX : X ⊆ Set.Icc 1 M) (hY : Y ⊆ Set.Ico (2 * M) (3 * M))
    (hS : S.IsAPOfLength (k : ℕ∞)) (hsub : S ⊆ X ∪ Y) :
    S ⊆ X ∨ S ⊆ Y := by
  obtain ⟨a, d, hAP⟩ := hS
  have hdpos : 0 < d := isAPOfLengthWith_step_pos hAP
    (by exact_mod_cast (show 1 < k by omega))
  have hmono : StrictMono (fun n : ℕ ↦ a + n * d) := by
    intro i j hij
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hij hdpos) a
  have hterm : ∀ n : ℕ, n < k → a + n * d ∈ X ∪ Y := by
    intro n hn
    apply hsub
    rw [hAP.eq]
    exact ⟨n, by exact_mod_cast hn, by simp⟩
  have ha := hterm 0 (by omega)
  simp only [zero_mul, add_zero] at ha
  rcases ha with ha | ha
  · obtain ⟨ha1, haM⟩ := hX ha
    have hfirst := hterm 1 (by omega)
    simp only [one_mul] at hfirst
    have hthird : a + 2 * d < 3 * M := by
      rcases hterm 2 (by omega) with hx | hy
      · have := (hX hx).2
        omega
      · exact (hY hy).2
    -- A crossing on the first step would already put the third term at least at `3 * M`.
    have hd : d < M := by
      rcases hfirst with hx | hy
      · have := (hX hx).2
        omega
      · have := (hY hy).1
        omega
    have hall : ∀ n : ℕ, n < k → a + n * d ∈ X := by
      intro n
      induction n with
      | zero =>
          intro _
          simpa only [zero_mul, add_zero] using ha
      | succ n ih =>
          intro hn
          have hprev : a + n * d ≤ M := (hX (ih (by omega))).2
          rcases hterm (n + 1) hn with hx | hy
          · exact hx
          · have hnext := (hY hy).1
            simp only [Nat.add_mul, one_mul] at hnext
            omega
    left
    rw [hAP.eq]
    rintro x ⟨n, hn, rfl⟩
    simpa only [nsmul_eq_mul] using hall n (by exact_mod_cast hn)
  · right
    rw [hAP.eq]
    rintro x ⟨n, hn, rfl⟩
    rcases hterm n (by exact_mod_cast hn) with hx | hy
    · have hstart := (hY ha).1
      have hbound := (hX hx).2
      have hle : a ≤ a + n * d := by
        simpa only [zero_mul, add_zero] using hmono.monotone (Nat.zero_le n)
      omega
    · simpa only [nsmul_eq_mul] using hy

/-- Translation by a natural number preserves the parameters and exact length of an AP. -/
theorem isAPOfLengthWith_image_add {S : Set ℕ} {l : ℕ∞} {a d : ℕ}
    (hS : S.IsAPOfLengthWith l a d) (c : ℕ) :
    ((fun x : ℕ ↦ c + x) '' S).IsAPOfLengthWith l (c + a) d := by
  refine ⟨?_, ?_⟩
  · rw [ENat.card_image_of_injective _ _ (fun _ _ h ↦ Nat.add_left_cancel h)]
    exact hS.card
  · rw [hS.eq]
    ext x
    constructor
    · rintro ⟨y, ⟨n, hn, rfl⟩, rfl⟩
      exact ⟨n, hn, by simp only [add_assoc]⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨a + n • d, ⟨n, hn, rfl⟩, by simp only [add_assoc]⟩

/-- Translation also reflects APs, including length zero and infinite length. -/
theorem isAPOfLength_image_add_iff {S : Set ℕ} {l : ℕ∞} (c : ℕ) :
    ((fun x : ℕ ↦ c + x) '' S).IsAPOfLength l ↔ S.IsAPOfLength l := by
  constructor
  · intro h
    by_cases hl : l = 0
    · subst l
      simpa using h
    obtain ⟨a, d, hAP⟩ := h
    have ha : a ∈ (fun x : ℕ ↦ c + x) '' S := by
      rw [hAP.eq]
      exact ⟨0, by simpa using (pos_iff_ne_zero.mpr hl : (0 : ℕ∞) < l), by simp⟩
    obtain ⟨b, hb, hab⟩ := ha
    refine ⟨b, d, ?_, ?_⟩
    · rw [← hAP.card]
      exact (ENat.card_image_of_injective _ _
        (fun _ _ h ↦ Nat.add_left_cancel h)).symm
    · ext x
      constructor
      · intro hx
        have hx' : c + x ∈ (fun x : ℕ ↦ c + x) '' S := ⟨x, hx, rfl⟩
        rw [hAP.eq] at hx'
        obtain ⟨n, hn, hxn⟩ := hx'
        refine ⟨n, hn, ?_⟩
        apply Nat.add_left_cancel (n := c)
        calc
          c + (b + n • d) = a + n • d := by rw [← hab, add_assoc]
          _ = c + x := hxn
      · rintro ⟨n, hn, rfl⟩
        have hx' : c + (b + n • d) ∈ (fun x : ℕ ↦ c + x) '' S := by
          rw [hAP.eq]
          exact ⟨n, hn, by rw [← hab, add_assoc]⟩
        obtain ⟨x, hx, hxn⟩ := hx'
        have hxb : x = b + n • d := Nat.add_left_cancel hxn
        simpa only [hxb] using hx
  · rintro ⟨a, d, hAP⟩
    exact ⟨c + a, d, isAPOfLengthWith_image_add hAP c⟩

/-- Containing an AP of a specified length is invariant under translation. -/
theorem exists_isAPOfLength_image_add_iff {E : Set ℕ} {l : ℕ∞} (c : ℕ) :
    (∃ S ⊆ (fun x : ℕ ↦ c + x) '' E, S.IsAPOfLength l) ↔
      ∃ T ⊆ E, T.IsAPOfLength l := by
  constructor
  · rintro ⟨S, hSE, hAP⟩
    let T : Set ℕ := (fun x : ℕ ↦ c + x) ⁻¹' S
    have hTE : T ⊆ E := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hSE hx
      have hxy : y = x := Nat.add_left_cancel hyx
      simpa only [hxy] using hy
    have himage : (fun x : ℕ ↦ c + x) '' T = S := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        obtain ⟨y, hy, rfl⟩ := hSE hx
        exact ⟨y, hx, rfl⟩
    refine ⟨T, hTE, (isAPOfLength_image_add_iff c).mp ?_⟩
    rwa [himage]
  · rintro ⟨T, hTE, hAP⟩
    exact ⟨(fun x : ℕ ↦ c + x) '' T, Set.image_mono hTE,
      (isAPOfLength_image_add_iff c).mpr hAP⟩

/-- AP-freeness in the literal sense of excluding every AP subset is translation invariant. -/
theorem no_isAPOfLength_image_add_iff {E : Set ℕ} {l : ℕ∞} (c : ℕ) :
    (∀ S ⊆ (fun x : ℕ ↦ c + x) '' E, ¬ S.IsAPOfLength l) ↔
      ∀ T ⊆ E, ¬ T.IsAPOfLength l := by
  simpa only [not_exists, not_and] using
    not_congr (exists_isAPOfLength_image_add_iff (E := E) (l := l) c)

/-- Safe gluing for sets. This also covers `M = 0`, when the upper block is empty. -/
theorem no_isAPOfLength_gluing {M k : ℕ} {F E : Set ℕ} (hk : 3 ≤ k)
    (hF : F ⊆ Set.Icc 1 M) (hE : E ⊆ Set.Ico 0 M)
    (hFfree : ∀ S ⊆ F, ¬ S.IsAPOfLength (k : ℕ∞))
    (hEfree : ∀ S ⊆ E, ¬ S.IsAPOfLength (k : ℕ∞)) :
    ∀ S ⊆ F ∪ ((fun x : ℕ ↦ 2 * M + x) '' E), ¬ S.IsAPOfLength (k : ℕ∞) := by
  by_cases hM : 1 ≤ M
  · have hY : (fun x : ℕ ↦ 2 * M + x) '' E ⊆ Set.Ico (2 * M) (3 * M) := by
      rintro x ⟨y, hy, rfl⟩
      have := (hE hy).2
      change 2 * M ≤ 2 * M + y ∧ 2 * M + y < 3 * M
      constructor <;> omega
    have hYfree := (no_isAPOfLength_image_add_iff (E := E) (l := (k : ℕ∞))
      (2 * M)).mpr hEfree
    intro S hsub hAP
    rcases isAPOfLength_subset_or_subset_of_separated hM hk hF hY hAP hsub with h | h
    · exact hFfree S h hAP
    · exact hYfree S h hAP
  · have hEempty : E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have := (hE hx).2
      omega
    simpa only [hEempty, Set.image_empty, Set.union_empty] using hFfree

/-- Safe gluing using the library's `IsAPOfLengthFree` predicate. -/
theorem isAPOfLengthFree_gluing {M k : ℕ} {F E : Set ℕ} (hk : 3 ≤ k)
    (hF : F ⊆ Set.Icc 1 M) (hE : E ⊆ Set.Ico 0 M)
    (hFfree : F.IsAPOfLengthFree (k : ℕ∞))
    (hEfree : E.IsAPOfLengthFree (k : ℕ∞)) :
    (F ∪ ((fun x : ℕ ↦ 2 * M + x) '' E)).IsAPOfLengthFree (k : ℕ∞) := by
  have hk' : ¬ (k : ℕ∞) ≤ 1 := by
    exact_mod_cast (show ¬ k ≤ 1 by omega)
  have hFno : ∀ S ⊆ F, ¬ S.IsAPOfLength (k : ℕ∞) :=
    fun S hS hAP ↦ hk' (hFfree S hS hAP)
  have hEno : ∀ S ⊆ E, ¬ S.IsAPOfLength (k : ℕ∞) :=
    fun S hS hAP ↦ hk' (hEfree S hS hAP)
  intro S hS hAP
  exact (no_isAPOfLength_gluing hk hF hE hFno hEno S hS hAP).elim

/-- Finite-set form, with the upper source block given as a subset of `Finset.range M`. -/
theorem no_isAPOfLength_gluing_finset {M k : ℕ} {F E : Finset ℕ} (hk : 3 ≤ k)
    (hF : F ⊆ Finset.Icc 1 M) (hE : E ⊆ Finset.range M)
    (hFfree : ∀ S ⊆ (F : Set ℕ), ¬ S.IsAPOfLength (k : ℕ∞))
    (hEfree : ∀ S ⊆ (E : Set ℕ), ¬ S.IsAPOfLength (k : ℕ∞)) :
    ∀ S ⊆ ((F ∪ E.image (fun x : ℕ ↦ 2 * M + x) : Finset ℕ) : Set ℕ),
      ¬ S.IsAPOfLength (k : ℕ∞) := by
  have hF' : (F : Set ℕ) ⊆ Set.Icc 1 M := by
    intro x hx
    exact Finset.mem_Icc.mp (hF hx)
  have hE' : (E : Set ℕ) ⊆ Set.Ico 0 M := by
    intro x hx
    exact ⟨Nat.zero_le x, Finset.mem_range.mp (hE hx)⟩
  simpa only [Finset.coe_union, Finset.coe_image] using
    no_isAPOfLength_gluing hk hF' hE' hFfree hEfree

end Erdos3Gluing

#print axioms Erdos3Gluing.isAPOfLengthWith_step_pos
#print axioms Erdos3Gluing.isAPOfLength_subset_or_subset_of_separated
#print axioms Erdos3Gluing.isAPOfLengthWith_image_add
#print axioms Erdos3Gluing.isAPOfLength_image_add_iff
#print axioms Erdos3Gluing.exists_isAPOfLength_image_add_iff
#print axioms Erdos3Gluing.no_isAPOfLength_image_add_iff
#print axioms Erdos3Gluing.no_isAPOfLength_gluing
#print axioms Erdos3Gluing.isAPOfLengthFree_gluing
#print axioms Erdos3Gluing.no_isAPOfLength_gluing_finset
