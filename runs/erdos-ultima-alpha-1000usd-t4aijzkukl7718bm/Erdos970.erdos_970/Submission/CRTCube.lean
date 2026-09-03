import Submission.MixedPatternRescaling

/-! Binary CRT cubes are exponentially large minimal obstructions for arbitrary
finite position sets. The points are not claimed to be consecutive. -/

namespace Erdos970.CRTCube

/-- Canonical CRT representatives with binary residues at every selected prime. -/
def points (P : Finset ℕ) : Finset ℕ :=
  (Finset.range (∏ p ∈ P, p)).filter (fun x => ∀ p ∈ P, x % p ≤ 1)

/-- One chosen residue class for each modulus covers the finite set `X`. -/
def Covers (P X : Finset ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ x ∈ X, ∃ p ∈ P, x ≡ r p [MOD p]

theorem mem_points {P : Finset ℕ} {x : ℕ} :
    x ∈ points P ↔ x < ∏ p ∈ P, p ∧ ∀ p ∈ P, x % p ≤ 1 := by
  simp [points]

theorem exists_pattern (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (hr : ∀ p ∈ P, r p ≤ 1) :
    ∃ x ∈ points P, ∀ p ∈ P, x % p = r p := by
  classical
  obtain ⟨b, hb⟩ := BrunCriterion.intersection_residue P hP r
  have hb' := (hb b).mpr (Nat.ModEq.refl b)
  let N := ∏ p ∈ P, p
  have hN : 0 < N := Finset.prod_pos (fun p hp => (hP p hp).pos)
  have hres (p : ℕ) (hp : p ∈ P) : b % N % p = r p := by
    have hdvd : p ∣ N := Finset.dvd_prod_of_mem id hp
    rw [Nat.mod_mod_of_dvd b hdvd]
    exact (show b % p = r p % p from hb' p hp).trans (Nat.mod_eq_of_lt (lt_of_le_of_lt (hr p hp) (hP p hp).one_lt))
  refine ⟨b % N, mem_points.mpr ⟨Nat.mod_lt _ hN, ?_⟩, hres⟩
  intro p hp
  rw [hres p hp]
  exact hr p hp

theorem eq_of_residues {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {x y : ℕ} (hx : x ∈ points P) (hy : y ∈ points P)
    (hxy : ∀ p ∈ P, x % p = y % p) : x = y := by
  obtain ⟨b, hb⟩ := BrunCriterion.intersection_residue P hP (fun _ => y)
  have hx' := (hb x).mp hxy
  have hy' := (hb y).mp (fun p hp => Nat.ModEq.refl y)
  exact (hx'.trans hy'.symm).eq_of_lt_of_lt (mem_points.mp hx).1 (mem_points.mp hy).1

/-- No selection of one residue per prime covers the whole binary CRT cube. -/
theorem not_covers (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ) :
    ¬Covers P (points P) r := by
  classical
  let b := fun p => if r p % p = 0 then 1 else 0
  obtain ⟨x, hx, hres⟩ := exists_pattern P hP b (by intro p hp; dsimp [b]; split <;> omega)
  intro hc
  obtain ⟨p, hp, he⟩ := hc x hx
  have he' : x % p = r p % p := he
  rw [hres p hp] at he'
  dsimp [b] at he'
  split_ifs at he' with hh <;> omega

/-- Every proper subset of the binary CRT cube can be covered. -/
theorem proper_subset_coverable (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (X : Finset ℕ) (hX : X ⊂ points P) : ∃ r, Covers P X r := by
  classical
  obtain ⟨x, hx, hxX⟩ := Finset.exists_of_ssubset hX
  refine ⟨fun p => 1 - x % p, fun y hy => ?_⟩
  have hyp : y ∈ points P := hX.subset hy
  have hne : x ≠ y := by rintro rfl; exact hxX hy
  have hex : ∃ p ∈ P, x % p ≠ y % p := by
    by_contra h
    push_neg at h
    exact hne (eq_of_residues hP hx hyp h)
  obtain ⟨p, hp, hdiff⟩ := hex
  refine ⟨p, hp, ?_⟩
  have hxbit := (mem_points.mp hx).2 p hp
  have hybit := (mem_points.mp hyp).2 p hp
  have hp2 := (hP p hp).two_le
  change y % p = (1 - x % p) % p
  rw [Nat.mod_eq_of_lt (show 1 - x % p < p by omega)]
  omega

/-- Every binary pattern has exactly one representative, hence there are `2^|P|` points. -/
theorem card_points (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (points P).card = 2 ^ P.card := by
  classical
  rw [← Finset.card_powerset]
  apply Finset.card_bij (fun x _ => P.filter (fun p => x % p = 1))
  · intro x hx
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · intro x hx y hy he
    apply eq_of_residues hP hx hy
    intro p hp
    have hxbit := (mem_points.mp hx).2 p hp
    have hybit := (mem_points.mp hy).2 p hp
    have hh : x % p = 1 ↔ y % p = 1 := by
      have := Finset.ext_iff.mp he p
      simpa only [Finset.mem_filter, hp, true_and] using this
    omega
  · intro A hA
    have hAP := Finset.mem_powerset.mp hA
    obtain ⟨x, hx, hres⟩ := exists_pattern P hP (fun p => if p ∈ A then 1 else 0)
      (by intro p hp; dsimp only; split <;> omega)
    refine ⟨x, hx, ?_⟩
    ext p
    by_cases hp : p ∈ P
    · simp only [Finset.mem_filter, hp, true_and, hres p hp]
      split_ifs with ha <;> simp [ha]
    · simp only [Finset.mem_filter, hp, false_and]
      exact iff_false_intro (fun h => hp (hAP h)) |>.symm

#print axioms card_points
#print axioms not_covers
#print axioms proper_subset_coverable

end Erdos970.CRTCube
