import Submission.CRTCube

/-! The exact exponential Helly bound for covering arbitrary finite sets by one
residue class per modulus. This bound does not exploit consecutiveness. -/
namespace Erdos970.ResidueHelly

/-- A separated family of coordinate patterns and deletion witnesses has size at most `2^k`.
The proof factors a nonsingular diagonal matrix through the space indexed by subsets of coordinates. -/
theorem separated_card_le {I J : Type*} [Fintype I] [Fintype J]
    (a b : I → J → ℚ)
    (hown : ∀ i j, a i j ≠ b i j)
    (hcross : ∀ i i', i ≠ i' → ∃ j, a i j = b i' j) :
    Fintype.card I ≤ 2 ^ Fintype.card J := by
  classical
  let A : Matrix I (Finset J) ℚ := fun i S => ∏ j ∈ S, a i j
  let B : Matrix (Finset J) I ℚ := fun S i => ∏ j ∈ Sᶜ, -b i j
  let d : I → ℚ := fun i => ∏ j, (a i j - b i j)
  have hdiag : A * B = Matrix.diagonal d := by
    ext i i'
    have hprod : (A * B) i i' = ∏ j, (a i j - b i' j) := by
      change (∑ S : Finset J, (∏ j ∈ S, a i j) * ∏ j ∈ Sᶜ, -b i' j) = _
      simpa only [sub_eq_add_neg] using (Fintype.prod_add (a i) (fun j => -b i' j)).symm
    rw [hprod]
    by_cases he : i = i'
    · subst i'
      simp [d]
    · rw [Matrix.diagonal_apply_ne _ he]
      obtain ⟨j, hj⟩ := hcross i i' he
      exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_eq_zero.mpr hj)
  have hd (i : I) : d i ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (hown i j))
  have hrank : (Matrix.diagonal d).rank = Fintype.card I := by
    rw [Matrix.rank_diagonal]
    exact Fintype.card_congr
      { toFun := Subtype.val
        invFun := fun i => ⟨i, hd i⟩
        left_inv := fun i => rfl
        right_inv := fun i => rfl }
  have hbound := (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)
  rwa [hdiag, hrank, Fintype.card_finset] at hbound

/-- A minimal noncoverable finite family needs at most exponentially many positions.
No primality or positivity of the moduli is required. -/
theorem minimal_noncoverable_card_le (P X : Finset ℕ)
    (hX : ¬∃ r, CRTCube.Covers P X r)
    (hdel : ∀ x ∈ X, ∃ r, CRTCube.Covers P (X.erase x) r) :
    X.card ≤ 2 ^ P.card := by
  classical
  choose r hr using (fun x : X => hdel x.val x.property)
  let a : X → P → ℚ := fun x p => (x.val % p.val : ℕ)
  let b : X → P → ℚ := fun x p => (r x p.val % p.val : ℕ)
  have hown (x : X) (p : P) : a x p ≠ b x p := by
    intro he
    dsimp [a, b] at he
    have he' : x.val ≡ r x p.val [MOD p.val] := by
      change x.val % p.val = r x p.val % p.val
      exact_mod_cast he
    apply hX
    refine ⟨r x, fun y hy => ?_⟩
    by_cases hyx : y = x.val
    · subst y
      exact ⟨p.val, p.property, he'⟩
    · exact hr x y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
  have hcross (x y : X) (hxy : x ≠ y) : ∃ p, a x p = b y p := by
    have hxne : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
    obtain ⟨p, hp, he⟩ := hr y x.val (Finset.mem_erase.mpr ⟨hxne, x.property⟩)
    refine ⟨⟨p, hp⟩, ?_⟩
    dsimp [a, b]
    exact_mod_cast (show x.val % p = r y p % p from he)
  simpa only [Fintype.card_coe] using separated_card_le a b hown hcross

/-- A noncoverable finite position set has a noncoverable subset of size at most `2^|P|`. -/
theorem exists_small_obstruction (P X : Finset ℕ)
    (hX : ¬∃ r, CRTCube.Covers P X r) :
    ∃ Y ⊆ X, Y.card ≤ 2 ^ P.card ∧ ¬∃ r, CRTCube.Covers P Y r := by
  classical
  let bad := X.powerset.filter (fun Y => ¬∃ r, CRTCube.Covers P Y r)
  have hbad : X ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun _ h => h), hX⟩
  obtain ⟨Y, hY, hmin⟩ := bad.exists_min_image Finset.card ⟨X, hbad⟩
  obtain ⟨hYX, hnc⟩ := Finset.mem_filter.mp hY
  have hsub := Finset.mem_powerset.mp hYX
  refine ⟨Y, hsub, minimal_noncoverable_card_le P Y hnc ?_, hnc⟩
  intro y hy
  by_contra hdel
  have hey : Y.erase y ∈ bad := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr ((Finset.erase_subset y Y).trans hsub), hdel⟩
  have := hmin (Y.erase y) hey
  have := Finset.card_lt_card (Finset.erase_ssubset hy)
  omega

/-- Checking all subsets of size at most `2^|P|` suffices for arbitrary finite position sets. -/
theorem coverable_iff_small_subsets (P X : Finset ℕ) :
    (∃ r, CRTCube.Covers P X r) ↔
    ∀ Y ⊆ X, Y.card ≤ 2 ^ P.card → ∃ r, CRTCube.Covers P Y r := by
  constructor
  · rintro ⟨r, hr⟩ Y hY hcard
    exact ⟨r, fun y hy => hr y (hY hy)⟩
  · intro h
    by_contra hX
    obtain ⟨Y, hYX, hYcard, hYnc⟩ := exists_small_obstruction P X hX
    exact hYnc (h Y hYX hYcard)

/-- For prime moduli, the preceding exponential threshold is attained exactly. -/
theorem sharpness (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ X : Finset ℕ, X.card = 2 ^ P.card ∧
      (¬∃ r, CRTCube.Covers P X r) ∧
      ∀ Y ⊆ X, Y.card < 2 ^ P.card → ∃ r, CRTCube.Covers P Y r := by
  refine ⟨CRTCube.points P, CRTCube.card_points P hP, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    exact CRTCube.not_covers P hP r hr
  · intro Y hY hcard
    apply CRTCube.proper_subset_coverable P hP Y
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hY, ?_⟩
    rintro rfl
    rw [CRTCube.card_points P hP] at hcard
    omega

#print axioms separated_card_le
#print axioms minimal_noncoverable_card_le
#print axioms coverable_iff_small_subsets
#print axioms sharpness

end Erdos970.ResidueHelly
