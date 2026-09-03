import Submission.TriangleMultipliers

/-! Repeated patterns explain why nontrivial budget-two cuts must use rare
intersection events. -/
namespace Erdos970.PatternPacking

lemma commonProduct_dvd_self (A B : Finset ℕ) :
    commonProduct A B ∣ commonProduct A A := by
  unfold commonProduct
  rw [Finset.inter_self]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.inter_subset_left)

/-- If one full pattern can occur twice, a genuinely smaller common pattern
can be inserted strictly between its two occurrences. -/
theorem admits_repeated_triangle (m : ℕ) (A B : Finset ℕ)
    (hd : 0 < commonProduct A B)
    (hlt : commonProduct A B < commonProduct A A)
    (hm : commonProduct A A < m) : AdmitsTriangle m A B A := by
  let d := commonProduct A B
  let e := commonProduct A A
  have he : d + (e - d) = e := Nat.add_sub_of_le hlt.le
  have hcomm : commonProduct B A = d := by simp [d, commonProduct, Finset.inter_comm]
  refine ⟨⟨d, hlt.trans hm⟩, ⟨e - d, by omega⟩, hd,
    by change 0 < e - d; omega, ?_, dvd_refl _, ?_, ?_⟩
  · change d + (e - d) < m
    rwa [he]
  · change commonProduct B A ∣ e - d
    rw [hcomm]
    exact Nat.dvd_sub (commonProduct_dvd_self A B) (dvd_refl d)
  · change e ∣ d + (e - d)
    rw [he]

/-- Necessary rarity condition for a universal budget-two family. -/
theorem length_le_patternProduct_of_noTriangle (m : ℕ) (F : Finset (Finset ℕ))
    (hno : NoTriangle m F) {A B : Finset ℕ} (hA : A ∈ F) (hB : B ∈ F)
    (hd : 0 < commonProduct A B)
    (hlt : commonProduct A B < commonProduct A A) :
    m ≤ commonProduct A A := by
  by_contra hbad
  exact hno A hA B hB A hA (admits_repeated_triangle m A B hd hlt (by omega))

#print axioms admits_repeated_triangle
#print axioms length_le_patternProduct_of_noTriangle
end Erdos970.PatternPacking
