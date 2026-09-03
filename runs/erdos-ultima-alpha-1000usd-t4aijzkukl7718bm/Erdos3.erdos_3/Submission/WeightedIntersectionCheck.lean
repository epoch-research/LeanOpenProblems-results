import Submission.ThinningCheck

/-! A uniform weighted obstruction to fixed-shift intersection arguments.
This file does not settle Erdős Problem 3. -/

namespace Erdos3WeightedIntersectionCheck

open Erdos3ThinningCheck
open scoped Classical
set_option maxHeartbeats 1000000

lemma recip_le_one (n : ℕ) : 1 / (n : ℝ) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn'

lemma weight_mono {S T : Finset ℕ} (h : S ⊆ T) : recipWeight S ≤ recipWeight T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ ↦ by positivity)

lemma nonsummable_tail {A : Set ℕ}
    (hA : ¬ Summable (fun x : A ↦ 1 / (x : ℝ))) (M : ℕ) :
    ¬ Summable (fun x : (A ∩ Set.Ioi M : Set ℕ) ↦ 1 / (x : ℝ)) := by
  intro hs
  apply hA
  apply (summable_subtype_iff_indicator (s := A) (f := fun n : ℕ ↦ 1 / (n : ℝ))).mpr
  have heq : A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) =ᶠ[Filter.cofinite]
      (A ∩ Set.Ioi M).indicator (fun n : ℕ ↦ 1 / (n : ℝ)) := by
    have hlarge : ∀ᶠ n : ℕ in Filter.cofinite, M < n := by
      simpa only [Nat.cofinite_eq_atTop] using Filter.eventually_gt_atTop M
    filter_upwards [hlarge] with n hn
    by_cases hna : n ∈ A <;> simp [Set.indicator, hna, hn]
  exact (summable_congr_cofinite heq).mpr (summable_subtype_iff_indicator.mp hs)

lemma bounded_weight_piece {A : Set ℕ}
    (hA : ¬ Summable (fun x : A ↦ 1 / (x : ℝ))) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ 1 < recipWeight S ∧ recipWeight S ≤ 2 := by
  obtain ⟨T, hTA, hT⟩ := large_finite_weight hA 1
  let F := T.powerset.filter (fun S ↦ 1 < recipWeight S)
  have hF : F.Nonempty := ⟨T, by simp [F, hT]⟩
  obtain ⟨S, hSF, hmin⟩ := Finset.exists_min_image F Finset.card hF
  have hST : S ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hSF).1
  have hSW : 1 < recipWeight S := (Finset.mem_filter.mp hSF).2
  have hne : S.Nonempty := by
    by_contra! he
    norm_num [he, recipWeight] at hSW
  obtain ⟨x, hx⟩ := hne
  have hsmall : recipWeight (S.erase x) ≤ 1 := by
    by_contra! hh
    have heF : S.erase x ∈ F := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset x S).trans hST), hh⟩
    have := hmin (S.erase x) heF
    have := Finset.card_erase_lt_of_mem hx
    omega
  refine ⟨S, fun n hn ↦ hTA (hST hn), hSW, ?_⟩
  have he := Finset.sum_erase_add S (fun n : ℕ ↦ 1 / (n : ℝ)) hx
  have hr := recip_le_one x
  change recipWeight (S.erase x) + 1 / (x : ℝ) = recipWeight S at he
  linarith

lemma separated_piece {A : Set ℕ}
    (hA : ¬ Summable (fun x : A ↦ 1 / (x : ℝ))) (M : ℕ) :
    ∃ V : Finset ℕ, (V : Set ℕ) ⊆ A ∧
      (∀ x ∈ V, 2 * M < x) ∧
      (∀ x ∈ V, ∀ y ∈ V, x < y → M < y - x) ∧
      1 < recipWeight V ∧ recipWeight V ≤ 2 := by
  let color : ℕ → Fin (M + 1) := fun n ↦ ⟨n % (M + 1), Nat.mod_lt _ (by omega)⟩
  obtain ⟨c, hc⟩ := nonsummable_color_class color hA
  obtain ⟨V, hV, hlow, hupp⟩ := bounded_weight_piece (nonsummable_tail hc (2 * M))
  refine ⟨V, fun x hx ↦ (hV hx).1.1, fun x hx ↦ (hV hx).2, ?_, hlow, hupp⟩
  intro x hx y hy hxy
  have he : x % (M + 1) = y % (M + 1) := congrArg Fin.val
    ((hV hx).1.2.trans (hV hy).1.2.symm)
  have hxdiv := Nat.mod_add_div x (M + 1)
  have hydiv := Nat.mod_add_div y (M + 1)
  have hq : x / (M + 1) < y / (M + 1) := by
    by_contra! hq
    have := Nat.mul_le_mul_left (M + 1) hq
    omega
  have hm := Nat.mul_le_mul_left (M + 1) (show x / (M + 1) + 1 ≤ y / (M + 1) by omega)
  have hsub : y - x + x = y := Nat.sub_add_cancel hxy.le
  nlinarith

noncomputable def shiftPart (S : Finset ℕ) (d : ℕ) : Finset ℕ :=
  S.filter (fun x ↦ x + d ∈ S)

def ShiftBound (S : Finset ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → recipWeight (shiftPart S d) ≤ 3

lemma extend_shift_bound {U V : Finset ℕ} {M : ℕ} (hU : ShiftBound U)
    (hUM : ∀ x ∈ U, x ≤ M) (hVL : ∀ x ∈ V, 2 * M < x)
    (hgap : ∀ x ∈ V, ∀ y ∈ V, x < y → M < y - x)
    (hVW : recipWeight V ≤ 2) : ShiftBound (U ∪ V) := by
  have hdis : Disjoint U V := Finset.disjoint_left.mpr (by
    intro x hx hy
    have := hUM x hx
    have := hVL x hy
    omega)
  intro d hd
  by_cases hdM : d ≤ M
  · have heq : shiftPart (U ∪ V) d = shiftPart U d := by
      ext x
      simp only [shiftPart, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hy | hy⟩
        · exact ⟨hx, hy⟩
        · have := hUM x hx
          have := hVL (x + d) hy
          omega
        · have := hVL x hx
          have := hUM (x + d) hy
          omega
        · have := hgap x hx (x + d) hy (by omega)
          omega
      · rintro ⟨hx, hy⟩
        exact ⟨Or.inl hx, Or.inl hy⟩
    rw [heq]
    exact hU d hd
  · let X := U.filter (fun x ↦ x + d ∈ V)
    have hXcard : X.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      obtain ⟨hxU, hxV⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyU, hyV⟩ := Finset.mem_filter.mp hy
      have hxM := hUM x hxU
      have hyM := hUM y hyU
      rcases lt_trichotomy x y with hxy | hxy | hxy
      · have := hgap (x + d) hxV (y + d) hyV (by omega)
        omega
      · exact hxy
      · have := hgap (y + d) hyV (x + d) hxV (by omega)
        omega
    have hXW : recipWeight X ≤ 1 := calc
      _ ≤ ∑ _x ∈ X, (1 : ℝ) := Finset.sum_le_sum (fun x _ ↦ recip_le_one x)
      _ = (X.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hXcard
    have hsub : shiftPart (U ∪ V) d ⊆ X ∪ V := by
      intro x hx
      obtain ⟨hx, hy⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp hx with hx | hx
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨hx, ?_⟩
        rcases Finset.mem_union.mp hy with hy | hy
        · have := hUM (x + d) hy
          omega
        · exact hy
      · exact Finset.mem_union_right _ hx
    have hXV : Disjoint X V := hdis.mono_left (Finset.filter_subset _ _)
    have hsum : recipWeight (X ∪ V) = recipWeight X + recipWeight V :=
      Finset.sum_union hXV
    exact (weight_mono hsub).trans (by rw [hsum]; linarith)

lemma finite_subset_chain {f : ℕ → Finset ℕ} (hf : Monotone f) {S : Finset ℕ}
    (hS : ∀ x ∈ S, ∃ n : ℕ, x ∈ f n) : ∃ n, S ⊆ f n := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert a S ha ih =>
    obtain ⟨i, hi⟩ := hS a (Finset.mem_insert_self _ _)
    obtain ⟨j, hj⟩ := ih (fun x hx ↦ hS x (Finset.mem_insert_of_mem hx))
    refine ⟨i + j, Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
    · exact hf (by omega : i ≤ i + j) hi
    · exact hj.trans (hf (by omega : j ≤ i + j))

lemma summable_and_tsum_le_of_finite_bound {A : Set ℕ} {C : ℝ}
    (hbound : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ A → recipWeight S ≤ C) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) ∧ (∑' a : A, 1 / (a : ℝ)) ≤ C := by
  have hsum (F : Finset A) : (∑ a ∈ F, 1 / (a : ℝ)) ≤ C := by
    let e : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
    have hsub : (F.map e : Set ℕ) ⊆ A := by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
      exact a.property
    simpa [recipWeight, e] using hbound (F.map e) hsub
  have hs : Summable (fun a : A ↦ 1 / (a : ℝ)) :=
    summable_of_sum_le (fun _ ↦ by positivity) hsum
  exact ⟨hs, hs.tsum_le_of_sum_le hsum⟩

/-- Every divergent set has a divergent subset whose positive-shift intersections
have reciprocal sums bounded by the same absolute constant. -/
theorem divergent_subset_uniform_shift_bound {A : Set ℕ}
    (hA : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ B ⊆ A, (¬ Summable (fun a : B ↦ 1 / (a : ℝ))) ∧
      ∀ d : ℕ, 0 < d →
        Summable (fun a : {x : ℕ | x ∈ B ∧ x + d ∈ B} ↦ 1 / (a : ℝ)) ∧
        (∑' a : {x : ℕ | x ∈ B ∧ x + d ∈ B}, 1 / (a : ℝ)) ≤ 3 := by
  have hp : ∀ U : Finset ℕ, ∃ V : Finset ℕ, (V : Set ℕ) ⊆ A ∧
      (∀ x ∈ V, 2 * U.sup id < x) ∧
      (∀ x ∈ V, ∀ y ∈ V, x < y → U.sup id < y - x) ∧
      1 < recipWeight V ∧ recipWeight V ≤ 2 := fun U ↦ separated_piece hA (U.sup id)
  choose piece hpiece using hp
  let chain : ℕ → Finset ℕ := Nat.rec ∅ (fun _ U ↦ U ∪ piece U)
  have hstep (n : ℕ) : chain (n + 1) = chain n ∪ piece (chain n) := rfl
  have hmono : Monotone chain :=
    monotone_nat_of_le_succ (fun n ↦ by rw [hstep]; exact Finset.subset_union_left)
  have hdis (U : Finset ℕ) : Disjoint U (piece U) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxM : x ≤ U.sup id := Finset.le_sup (f := id) hx
    have hyM := (hpiece U).2.1 x hy
    omega
  have hCA (n : ℕ) : ∀ x ∈ chain n, x ∈ A := by
    induction n with
    | zero => simp [chain]
    | succ n ih =>
      intro x hx
      rw [hstep] at hx
      exact (Finset.mem_union.mp hx).elim (ih x) (fun hx ↦ (hpiece (chain n)).1 hx)
  have hCW (n : ℕ) : (n : ℝ) ≤ recipWeight (chain n) := by
    induction n with
    | zero => simp [chain, recipWeight]
    | succ n ih =>
      have he : recipWeight (chain (n + 1)) =
          recipWeight (chain n) + recipWeight (piece (chain n)) := by
        rw [hstep]
        exact Finset.sum_union (hdis (chain n))
      have hl := (hpiece (chain n)).2.2.2.1
      rw [he]
      push_cast
      linarith
  have hCB (n : ℕ) : ShiftBound (chain n) := by
    induction n with
    | zero => intro d hd; norm_num [chain, shiftPart, recipWeight]
    | succ n ih =>
      rw [hstep]
      exact extend_shift_bound ih (fun _ hx ↦ Finset.le_sup (f := id) hx)
        (hpiece (chain n)).2.1 (hpiece (chain n)).2.2.1 (hpiece (chain n)).2.2.2.2
  let B : Set ℕ := {x | ∃ n : ℕ, x ∈ chain n}
  have hBA : B ⊆ A := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    exact hCA n x hn
  have hB : ¬ Summable (fun a : B ↦ 1 / (a : ℝ)) := by
    intro hs
    have hsI : Summable (B.indicator (fun x : ℕ ↦ 1 / (x : ℝ))) :=
      summable_subtype_iff_indicator.mp hs
    obtain ⟨n, hn⟩ := exists_nat_gt (∑' x : ℕ, B.indicator (fun x : ℕ ↦ 1 / (x : ℝ)) x)
    have hb : recipWeight (chain n) ≤
        ∑' x : ℕ, B.indicator (fun x : ℕ ↦ 1 / (x : ℝ)) x := by
      calc
        recipWeight (chain n) = ∑ x ∈ chain n,
            B.indicator (fun x : ℕ ↦ 1 / (x : ℝ)) x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (Set.indicator_of_mem (show x ∈ B from ⟨n, hx⟩)
            (fun x : ℕ ↦ 1 / (x : ℝ))).symm
        _ ≤ _ := Summable.sum_le_tsum _
          (fun x _ ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) x) hsI
    exact (not_lt_of_ge ((hCW n).trans hb)) hn
  refine ⟨B, hBA, hB, ?_⟩
  intro d hd
  apply summable_and_tsum_le_of_finite_bound
  intro S hS
  let T := S ∪ S.image (fun x ↦ x + d)
  have hTB : (T : Set ℕ) ⊆ B := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (hS hx).1
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (hS hy).2
  obtain ⟨n, hn⟩ := finite_subset_chain hmono (fun _ hx ↦ hTB hx)
  have hsub : S ⊆ shiftPart (chain n) d := by
    intro x hx
    simp only [shiftPart, Finset.mem_filter]
    exact ⟨hn (Finset.mem_union_left _ hx),
        hn (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))⟩
  exact (weight_mono hsub).trans (hCB n d hd)

#print axioms divergent_subset_uniform_shift_bound

def UniformShiftWeightBound (A : Set ℕ) : Prop :=
  ∀ d : ℕ, 0 < d →
    Summable (fun a : {x : ℕ | x ∈ A ∧ x + d ∈ A} ↦ 1 / (a : ℝ)) ∧
    (∑' a : {x : ℕ | x ∈ A ∧ x + d ∈ A}, 1 / (a : ℝ)) ≤ 3

lemma affineThin_subset {A B : Set ℕ} (hA : AffineThin A) (hBA : B ⊆ A) :
    AffineThin B := by
  intro a b c d ha hc hne
  apply (hA a b c d ha hc hne).subset
  rintro x ⟨hx, y, hy, heq⟩
  exact ⟨hBA hx, y, hBA hy, heq⟩

/-- The uniform intersection bound can be imposed alongside the earlier
absence of infinitely many solutions to every fixed nonidentity affine relation. -/
theorem divergent_affine_thin_subset_uniform_shift_bound {A : Set ℕ}
    (hA : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ B ⊆ A, (¬ Summable (fun a : B ↦ 1 / (a : ℝ))) ∧
      AffineThin B ∧ UniformShiftWeightBound B := by
  obtain ⟨C, hCA, hC, hthin⟩ := divergent_affine_thin_subset hA
  obtain ⟨B, hBC, hB, hbound⟩ := divergent_subset_uniform_shift_bound hC
  exact ⟨B, hBC.trans hCA, hB, affineThin_subset hthin hBC, hbound⟩

/-- The exact AP conjecture reduces to sets with both additional sparsity
properties. This equivalence is not a proof of either side. -/
theorem conjecture_iff_uniform_shift_bound_case :
    (∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    (∀ A : Set ℕ, AffineThin A → UniformShiftWeightBound A →
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) := by
  constructor
  · intro h A _ _
    exact h A
  · intro h A hA
    obtain ⟨B, hBA, hB, hthin, hbound⟩ := divergent_affine_thin_subset_uniform_shift_bound hA
    apply (h B hthin hbound hB).mono
    rintro k ⟨S, hSB, hS⟩
    exact ⟨S, hSB.trans hBA, hS⟩

theorem exists_divergent_uniform_shift_bound :
    ∃ B : Set ℕ, (¬ Summable (fun a : B ↦ 1 / (a : ℝ))) ∧
      AffineThin B ∧ UniformShiftWeightBound B := by
  obtain ⟨A, hA, _⟩ := exists_divergent_affine_thin
  obtain ⟨B, _, hB, hthin, hbound⟩ := divergent_affine_thin_subset_uniform_shift_bound hA
  exact ⟨B, hB, hthin, hbound⟩

/-- Even allowing the shift to vary does not force unbounded reciprocal
intersection sums. This negates an auxiliary reduction, not Erdős Problem 3. -/
theorem unbounded_shift_weight_reduction_fails :
    ¬ (∀ A : Set ℕ, (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) →
      ∀ C : ℝ, ∃ d : ℕ, 0 < d ∧
        C < ∑' a : {x : ℕ | x ∈ A ∧ x + d ∈ A}, 1 / (a : ℝ)) := by
  intro h
  obtain ⟨B, hB, _, hbound⟩ := exists_divergent_uniform_shift_bound
  obtain ⟨d, hd, hlarge⟩ := h B hB 3
  exact (not_lt_of_ge (hbound d hd).2) hlarge

#print axioms divergent_affine_thin_subset_uniform_shift_bound
#print axioms conjecture_iff_uniform_shift_bound_case
#print axioms exists_divergent_uniform_shift_bound
#print axioms unbounded_shift_weight_reduction_fails

end Erdos3WeightedIntersectionCheck
