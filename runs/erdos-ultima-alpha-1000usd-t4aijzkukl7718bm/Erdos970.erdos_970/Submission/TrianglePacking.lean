import Submission.PatternPackingGeneral

/-! Exact three-position compatibility for hit patterns. Unlike a lower bound
on pairwise distances, this keeps the additive relation between the three
actual distances. No uniform Jacobsthal bound is asserted. -/
namespace Erdos970.PatternPacking
open BrunCriterion

def commonProduct (A B : Finset ℕ) : ℕ := ∏ p ∈ A ∩ B, p

/-- The three patterns can be placed at 0,u,u+v inside the interval as far as
all their required congruences are concerned. -/
def AdmitsTriangle (m : ℕ) (A B C : Finset ℕ) : Prop :=
  ∃ u v : Fin m, 0 < u.val ∧ 0 < v.val ∧ u.val + v.val < m ∧
    commonProduct A B ∣ u.val ∧ commonProduct B C ∣ v.val ∧
    commonProduct A C ∣ u.val + v.val

instance (m : ℕ) (A B C : Finset ℕ) : Decidable (AdmitsTriangle m A B C) := by
  unfold AdmitsTriangle
  infer_instance

def NoTriangle (m : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, ¬AdmitsTriangle m A B C

instance (m : ℕ) (F : Finset (Finset ℕ)) : Decidable (NoTriangle m F) := by
  unfold NoTriangle
  infer_instance

def patternCount (m : ℕ) (F : Finset (Finset ℕ)) (r : ℕ → ℕ) : ℕ :=
  ((Finset.range m).filter (fun i => ∃ A ∈ F, ∀ p ∈ A, i ≡ r p [MOD p])).card

lemma commonProduct_dvd_difference (A B : Finset ℕ) (r : ℕ → ℕ) {x y : ℕ}
    (hprime : ∀ p ∈ A ∩ B, p.Prime) (hxy : x ≤ y)
    (hx : ∀ p ∈ A, x ≡ r p [MOD p])
    (hy : ∀ p ∈ B, y ≡ r p [MOD p]) : commonProduct A B ∣ y - x := by
  obtain ⟨a, ha⟩ := intersection_residue (A ∩ B) hprime r
  have hxa := (ha x).mp (fun p hp => hx p (Finset.mem_inter.mp hp).1)
  have hya := (ha y).mp (fun p hp => hy p (Finset.mem_inter.mp hp).2)
  exact (Nat.modEq_iff_dvd' hxy).mp (hxa.trans hya.symm)

/-- A triangle obstruction gives a packing budget of two. All three patterns
may be equal; such cases are included in `NoTriangle`. -/
theorem patternCount_le_two_of_noTriangle (m : ℕ) (F : Finset (Finset ℕ))
    (hprime : ∀ A ∈ F, ∀ p ∈ A, p.Prime) (hno : NoTriangle m F) (r : ℕ → ℕ) :
    patternCount m F r ≤ 2 := by
  classical
  let S := (Finset.range m).filter (fun i => ∃ A ∈ F, ∀ p ∈ A, i ≡ r p [MOD p])
  change S.card ≤ 2
  by_contra hbad
  have hs : 3 ≤ S.card := by omega
  let e := S.orderEmbOfFin rfl
  let a : Fin S.card := ⟨0, by omega⟩
  let b : Fin S.card := ⟨1, by omega⟩
  let c : Fin S.card := ⟨2, by omega⟩
  have hab : e a < e b := e.strictMono (by change 0 < 1; decide)
  have hbc : e b < e c := e.strictMono (by change 1 < 2; decide)
  have haS : e a ∈ S := S.orderEmbOfFin_mem rfl a
  have hbS : e b ∈ S := S.orderEmbOfFin_mem rfl b
  have hcS : e c ∈ S := S.orderEmbOfFin_mem rfl c
  obtain ⟨ham, A, hAF, hA⟩ := Finset.mem_filter.mp haS
  obtain ⟨hbm, B, hBF, hB⟩ := Finset.mem_filter.mp hbS
  obtain ⟨hcm, C, hCF, hC⟩ := Finset.mem_filter.mp hcS
  have haM := Finset.mem_range.mp ham
  have hbM := Finset.mem_range.mp hbm
  have hcM := Finset.mem_range.mp hcm
  apply hno A hAF B hBF C hCF
  refine ⟨⟨e b - e a, by omega⟩, ⟨e c - e b, by omega⟩,
    by change 0 < e b - e a; omega,
    by change 0 < e c - e b; omega,
    by change e b - e a + (e c - e b) < m; omega, ?_, ?_, ?_⟩
  · exact commonProduct_dvd_difference A B r
      (fun p hp => hprime A hAF p (Finset.mem_inter.mp hp).1) hab.le hA hB
  · exact commonProduct_dvd_difference B C r
      (fun p hp => hprime B hBF p (Finset.mem_inter.mp hp).1) hbc.le hB hC
  · have hh := commonProduct_dvd_difference A C r
      (fun p hp => hprime A hAF p (Finset.mem_inter.mp hp).1)
      (hab.trans hbc).le hA hC
    change commonProduct A C ∣ e b - e a + (e c - e b)
    rwa [show e b - e a + (e c - e b) = e c - e a by omega]

/-- Conversely, every admitted triangle really can be realized by one common
residue vector. No primality hypothesis is needed in this direction. -/
theorem exists_three_positions_of_triangle (m : ℕ) (F : Finset (Finset ℕ))
    {A B C : Finset ℕ} (hA : A ∈ F) (hB : B ∈ F) (hC : C ∈ F)
    (htri : AdmitsTriangle m A B C) : ∃ r : ℕ → ℕ, 3 ≤ patternCount m F r := by
  classical
  obtain ⟨u, v, hu, hv, huv, hab, hbc, hac⟩ := htri
  let r : ℕ → ℕ := fun p => if p ∈ A then 0 else if p ∈ B then u.val else u.val + v.val
  have hzero : ∀ p ∈ A, (0 : ℕ) ≡ r p [MOD p] := by
    intro p hp
    simp [r, hp, Nat.ModEq]
  have hmid : ∀ p ∈ B, u.val ≡ r p [MOD p] := by
    intro p hp
    by_cases hpA : p ∈ A
    · have hd : p ∣ u.val :=
        (Finset.dvd_prod_of_mem (fun q => q) (Finset.mem_inter.mpr ⟨hpA, hp⟩)).trans hab
      simpa [r, hpA] using Nat.modEq_zero_iff_dvd.mpr hd
    · simp [r, hpA, hp, Nat.ModEq]
  have hlast : ∀ p ∈ C, u.val + v.val ≡ r p [MOD p] := by
    intro p hp
    by_cases hpA : p ∈ A
    · have hd : p ∣ u.val + v.val :=
        (Finset.dvd_prod_of_mem (fun q => q) (Finset.mem_inter.mpr ⟨hpA, hp⟩)).trans hac
      simpa [r, hpA] using Nat.modEq_zero_iff_dvd.mpr hd
    · by_cases hpB : p ∈ B
      · have hd : p ∣ v.val :=
          (Finset.dvd_prod_of_mem (fun q => q) (Finset.mem_inter.mpr ⟨hpB, hp⟩)).trans hbc
        have hh := (Nat.modEq_zero_iff_dvd.mpr hd).add_left u.val
        simpa [r, hpA, hpB] using hh
      · simp [r, hpA, hpB, Nat.ModEq]
  refine ⟨r, ?_⟩
  let S := (Finset.range m).filter (fun i => ∃ D ∈ F, ∀ p ∈ D, i ≡ r p [MOD p])
  have h0 : 0 ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), A, hA, hzero⟩
  have h1 : u.val ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr u.isLt, B, hB, hmid⟩
  have h2 : u.val + v.val ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huv, C, hC, hlast⟩
  have hsub : {0, u.val, u.val + v.val} ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hh := Finset.card_le_card hsub
  have hcard : ({0, u.val, u.val + v.val} : Finset ℕ).card = 3 := by
    have h0ne : (0 : ℕ) ∉ ({u.val, u.val + v.val} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have h1ne : u.val ∉ ({u.val + v.val} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      omega
    rw [Finset.card_insert_of_notMem h0ne, Finset.card_insert_of_notMem h1ne,
      Finset.card_singleton]
  rw [hcard] at hh
  exact hh

/-- An exact finite characterization of the universal packing budget two. -/
theorem patternCount_le_two_iff_noTriangle (m : ℕ) (F : Finset (Finset ℕ))
    (hprime : ∀ A ∈ F, ∀ p ∈ A, p.Prime) :
    (∀ r : ℕ → ℕ, patternCount m F r ≤ 2) ↔ NoTriangle m F := by
  constructor
  · intro h A hA B hB C hC htri
    obtain ⟨r, hr⟩ := exists_three_positions_of_triangle m F hA hB hC htri
    have hh := h r
    omega
  · intro h r
    exact patternCount_le_two_of_noTriangle m F hprime h r

#print axioms patternCount_le_two_iff_noTriangle
end Erdos970.PatternPacking
