import FormalConjecturesUtil

/-! Direct divergence-preserving thinning. This does not settle Erdős Problem 3. -/

namespace Erdos3ThinningCheck

private theorem unused_color (K : ℕ) (s : Finset (Fin (K + 1))) (hs : s.card ≤ K) :
    ∃ c : Fin (K + 1), c ∉ s := by
  classical
  by_contra! h
  have hsub : Finset.univ ⊆ s := by intro c _; exact h c
  have hc := Finset.card_le_card hsub
  simpa using hc.trans hs

private theorem color_choice (nb : ℕ → Finset ℕ) (K : ℕ)
    (hnb : ∀ n, (nb n).card ≤ K) (n : ℕ) (prev : Fin n → Fin (K + 1)) :
    ∃ c : Fin (K + 1), ∀ m : Fin n, m.val ∈ nb n → c ≠ prev m := by
  classical
  let s := ((nb n).filter (· < n)).attach.image
    (fun m ↦ prev ⟨m.val, by
      have hh : m.val ∈ nb n ∧ m.val < n := by
        simpa only [Finset.mem_filter] using m.property
      exact hh.2⟩)
  have hs : s.card ≤ K :=
    Finset.card_image_le.trans ((by simp : ((nb n).filter (· < n)).attach.card =
      ((nb n).filter (· < n)).card).le.trans
      ((Finset.card_filter_le _ _).trans (hnb n)))
  obtain ⟨c, hc⟩ := unused_color K s hs
  refine ⟨c, fun m hm heq ↦ hc ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨⟨m.val, Finset.mem_filter.mpr ⟨hm, m.isLt⟩⟩, by simp, ?_⟩
  exact heq.symm

noncomputable def greedyColor (nb : ℕ → Finset ℕ) (K : ℕ)
    (hnb : ∀ n, (nb n).card ≤ K) : ℕ → Fin (K + 1) :=
  Nat.strongRec fun n prev ↦
    (color_choice nb K hnb n (fun m ↦ prev m.val m.isLt)).choose

private theorem greedyColor_ne (nb : ℕ → Finset ℕ) (K : ℕ)
    (hnb : ∀ n, (nb n).card ≤ K) {m n : ℕ} (hmn : m < n) (hm : m ∈ nb n) :
    greedyColor nb K hnb n ≠ greedyColor nb K hnb m := by
  conv_lhs => unfold greedyColor; rw [Nat.strongRec_eq]
  exact (color_choice nb K hnb n (fun i ↦ greedyColor nb K hnb i.val)).choose_spec
    ⟨m, hmn⟩ hm

abbrev AffineCode (D : ℕ) := Fin (D + 1) × Fin (D + 1) × Fin (D + 1) × Fin (D + 1)

def affineNeighbor (D n : ℕ) (t : AffineCode D) : ℕ :=
  (t.1.val * n + t.2.1.val - t.2.2.2.val) / t.2.2.1.val

noncomputable def affineNeighbors (D n : ℕ) : Finset ℕ :=
  Finset.univ.image (affineNeighbor D n)

private theorem card_affineNeighbors (D n : ℕ) :
    (affineNeighbors D n).card ≤ Fintype.card (AffineCode D) := by
  exact Finset.card_image_le.trans (by simp)

noncomputable def affineColor (D : ℕ) : ℕ → Fin (Fintype.card (AffineCode D) + 1) :=
  greedyColor (affineNeighbors D) _ (card_affineNeighbors D)

private theorem mem_affineNeighbors {D a b c d x y : ℕ}
    (ha : a ≤ D) (hb : b ≤ D) (hc : 0 < c) (hcD : c ≤ D) (hd : d ≤ D)
    (heq : a * x + b = c * y + d) : y ∈ affineNeighbors D x := by
  apply Finset.mem_image.mpr
  refine ⟨(⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩, ⟨d, by omega⟩), by simp, ?_⟩
  dsimp [affineNeighbor]
  rw [heq, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel_left y hc

/-- A finite coloring separates unequal points in every affine relation with bounded coefficients. -/
theorem affineColor_ne {D a b c d x y : ℕ}
    (ha : 0 < a) (haD : a ≤ D) (hbD : b ≤ D)
    (hc : 0 < c) (hcD : c ≤ D) (hdD : d ≤ D)
    (hxy : x ≠ y) (heq : a * x + b = c * y + d) :
    affineColor D x ≠ affineColor D y := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact (greedyColor_ne _ _ (card_affineNeighbors D) hlt
      (mem_affineNeighbors hcD hdD ha haD hbD heq.symm)).symm
  · exact greedyColor_ne _ _ (card_affineNeighbors D) hgt
      (mem_affineNeighbors haD hbD hc hcD hdD heq)

noncomputable def recipWeight (S : Finset ℕ) : ℝ := ∑ x ∈ S, 1 / (x : ℝ)

theorem large_finite_weight {A : Set ℕ}
    (hA : ¬ Summable (fun x : A ↦ 1 / (x : ℝ))) (M : ℝ) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ M < recipWeight S := by
  classical
  by_contra! h
  apply hA
  apply summable_of_sum_le (c := M) (fun _ ↦ by positivity)
  intro u
  let S := u.image (fun x : A ↦ (x : ℕ))
  have hSA : (S : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hw := h S hSA
  simpa only [recipWeight, S, Finset.sum_image Subtype.val_injective.injOn] using hw

theorem nonsummable_color_class {κ : Type*} [Fintype κ] (color : ℕ → κ)
    {A : Set ℕ} (hA : ¬ Summable (fun x : A ↦ 1 / (x : ℝ))) :
    ∃ c : κ, ¬ Summable (fun x : (A ∩ {x | color x = c} : Set ℕ) ↦ 1 / (x : ℝ)) := by
  classical
  by_contra! h
  apply hA
  apply (summable_subtype_iff_indicator (s := A) (f := fun x : ℕ ↦ 1 / (x : ℝ))).mpr
  have hs : Summable (fun x : ℕ ↦ ∑ c : κ,
      (A ∩ {x | color x = c}).indicator (fun n : ℕ ↦ 1 / (n : ℝ)) x) :=
    summable_sum (fun c _ ↦ summable_subtype_iff_indicator.mp (h c))
  apply hs.congr
  intro x
  by_cases hx : x ∈ A <;> simp [Set.indicator, hx, eq_comm]

/-- Countably many finite colorings admit a divergent subset that is eventually
monochromatic for each coloring. -/
theorem nonsummable_eventually_monochromatic {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (color : ∀ n, ℕ → κ n) {A : Set ℕ}
    (hA : ¬ Summable (fun x : A ↦ 1 / (x : ℝ))) :
    ∃ B ⊆ A, (¬ Summable (fun x : B ↦ 1 / (x : ℝ))) ∧
      ∀ n, ∃ F : Finset ℕ, ∀ x ∈ B, ∀ y ∈ B, x ∉ F → y ∉ F → color n x = color n y := by
  classical
  let P := {C : Set ℕ // ¬ Summable (fun x : C ↦ 1 / (x : ℝ))}
  have refine_set : ∀ C : P, ∀ n, ∃ T : P, T.val ⊆ C.val ∧
      ∀ x ∈ T.val, ∀ y ∈ T.val, color n x = color n y := by
    intro C n
    obtain ⟨c, hc⟩ := nonsummable_color_class (color n) C.property
    refine ⟨⟨C.val ∩ {x | color n x = c}, hc⟩, Set.inter_subset_left, ?_⟩
    intro x hx y hy
    exact hx.2.trans hy.2.symm
  choose next hnext using refine_set
  let chain : ℕ → P := Nat.rec ⟨A, hA⟩ (fun n C ↦ next C n)
  have hstep (n : ℕ) : (chain (n + 1)).val ⊆ (chain n).val ∧
      ∀ x ∈ (chain (n + 1)).val, ∀ y ∈ (chain (n + 1)).val,
        color n x = color n y := hnext (chain n) n
  have hanti : Antitone (fun n ↦ (chain n).val) :=
    antitone_nat_of_succ_le (fun n ↦ (hstep n).1)
  have hpieces : ∀ n : ℕ, ∃ S : Finset ℕ, (S : Set ℕ) ⊆ (chain n).val ∧
      (n : ℝ) < recipWeight S := fun n ↦ large_finite_weight (chain n).property n
  choose piece hpiece using hpieces
  let B : Set ℕ := ⋃ n : ℕ, (piece n : Set ℕ)
  have hBA : B ⊆ A := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact hanti (Nat.zero_le n) (hpiece n |>.1 hn)
  have hB : ¬ Summable (fun x : B ↦ 1 / (x : ℝ)) := by
    intro hs
    have hsI : Summable (B.indicator (fun x : ℕ ↦ 1 / (x : ℝ))) :=
      summable_subtype_iff_indicator.mp hs
    obtain ⟨n, hn⟩ := exists_nat_gt (∑' x : ℕ, B.indicator (fun x : ℕ ↦ 1 / (x : ℝ)) x)
    have hbound : recipWeight (piece n) ≤
        ∑' x : ℕ, B.indicator (fun x : ℕ ↦ 1 / (x : ℝ)) x := by
      calc
        recipWeight (piece n) = ∑ x ∈ piece n,
            B.indicator (fun x : ℕ ↦ 1 / (x : ℝ)) x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (Set.indicator_of_mem (Set.mem_iUnion.mpr ⟨n, hx⟩)
            (fun x : ℕ ↦ 1 / (x : ℝ))).symm
        _ ≤ _ := Summable.sum_le_tsum _
          (fun x _ ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) x) hsI
    exact (not_lt_of_ge hbound) (hn.trans (hpiece n).2)
  refine ⟨B, hBA, hB, fun n ↦ ?_⟩
  let F := (Finset.range (n + 1)).biUnion piece
  have htail : ∀ x ∈ B, x ∉ F → x ∈ (chain (n + 1)).val := by
    intro x hx hxF
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    have hnm : n + 1 ≤ m := by
      by_contra hlt
      exact hxF (Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (by omega), hm⟩)
    exact hanti hnm ((hpiece m).1 hm)
  exact ⟨F, fun x hx y hy hxF hyF ↦ (hstep n).2 x (htail x hx hxF) y (htail y hy hyF)⟩

/-- Finiteness of solutions to every fixed nonidentity positive affine relation. -/
def AffineThin (B : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < c → (a ≠ c ∨ b ≠ d) →
    {x : ℕ | x ∈ B ∧ ∃ y ∈ B, a * x + b = c * y + d}.Finite

/-- Every reciprocal-divergent set has a reciprocal-divergent affine-thin subset.
No AP-freeness assumption or unproved extremal estimate is used. -/
theorem divergent_affine_thin_subset {A : Set ℕ}
    (hA : ¬ Summable (fun x : A ↦ 1 / (x : ℝ))) :
    ∃ B ⊆ A, (¬ Summable (fun x : B ↦ 1 / (x : ℝ))) ∧ AffineThin B := by
  classical
  obtain ⟨B, hBA, hB, hmono⟩ := nonsummable_eventually_monochromatic affineColor hA
  refine ⟨B, hBA, hB, ?_⟩
  intro a b c d ha hc hneq
  let D := a + b + c + d
  obtain ⟨F, hF⟩ := hmono D
  let f : ℕ → ℕ := fun y ↦ (c * y + d - b) / a
  have hfin : ((F : Set ℕ) ∪ f '' (F : Set ℕ) ∪ Set.Iic (b + d)).Finite :=
    (F.finite_toSet.union (F.finite_toSet.image f)).union (Set.finite_Iic _)
  apply hfin.subset
  rintro x ⟨hxB, y, hyB, heq⟩
  by_cases hxF : x ∈ F
  · exact Or.inl (Or.inl hxF)
  by_cases hyF : y ∈ F
  · refine Or.inl (Or.inr ⟨y, hyF, ?_⟩)
    dsimp [f]
    rw [← heq, Nat.add_sub_cancel]
    exact Nat.mul_div_cancel_left x ha
  have hxy : x = y := by
    by_contra hxy
    exact (affineColor_ne ha (by dsimp [D]; omega) (by dsimp [D]; omega)
      hc (by dsimp [D]; omega) (by dsimp [D]; omega) hxy heq)
      (hF x hxB y hyB hxF hyF)
  subst y
  apply Or.inr
  change x ≤ b + d
  rcases lt_trichotomy a c with hlt | heqac | hgt
  · have hmul := Nat.mul_le_mul_right x (Nat.succ_le_of_lt hlt)
    nlinarith
  · rcases hneq with hac | hbd
    · exact False.elim (hac heqac)
    · have : b = d := by rw [heqac] at heq; omega
      contradiction
  · have hmul := Nat.mul_le_mul_right x (Nat.succ_le_of_lt hgt)
    nlinarith

/-- A direct reduction of the exact conjecture to affine-thin sets. -/
theorem conjecture_iff_affine_thin_case :
    (∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    (∀ A : Set ℕ, AffineThin A →
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) := by
  constructor
  · intro h A _
    exact h A
  · intro h A hA
    obtain ⟨B, hBA, hB, hthin⟩ := divergent_affine_thin_subset hA
    apply (h B hthin hB).mono
    rintro k ⟨S, hSB, hS⟩
    exact ⟨S, hSB.trans hBA, hS⟩

/-- Affine thinness itself does not imply reciprocal summability. This is not
a counterexample to the AP conjecture. -/
theorem exists_divergent_affine_thin :
    ∃ B : Set ℕ, (¬ Summable (fun x : B ↦ 1 / (x : ℝ))) ∧ AffineThin B := by
  have hN : ¬ Summable (fun x : (Set.univ : Set ℕ) ↦ 1 / (x : ℝ)) := by
    intro hs
    apply Real.not_summable_one_div_natCast
    have hs' := (summable_subtype_iff_indicator (s := (Set.univ : Set ℕ))
      (f := fun x : ℕ ↦ 1 / (x : ℝ))).mp hs
    simpa only [Set.indicator_univ] using hs'
  obtain ⟨B, _, hB, hthin⟩ := divergent_affine_thin_subset hN
  exact ⟨B, hB, hthin⟩

#print axioms exists_divergent_affine_thin
#print axioms divergent_affine_thin_subset
#print axioms conjecture_iff_affine_thin_case
#print axioms affineColor_ne
#print axioms nonsummable_eventually_monochromatic

end Erdos3ThinningCheck
