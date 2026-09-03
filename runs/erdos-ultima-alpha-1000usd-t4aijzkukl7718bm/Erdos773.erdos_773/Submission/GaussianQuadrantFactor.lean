import Submission.GaussianOddFactor

/-! Unit and quadrant normalizations for the small-factor collision encoding. -/
namespace Erdos773.GaussianQuadrantFactor
open GaussianCollisionFactorization GaussianOddFactor
set_option maxHeartbeats 1000000
noncomputable section

def squareCoords (z : G) : Finset ℤ := {z.re^2,z.im^2}

lemma unit_coords (u : Gˣ) :
    ((u:G).re=1 ∧ (u:G).im=0) ∨ ((u:G).re= -1 ∧ (u:G).im=0) ∨
    ((u:G).re=0 ∧ (u:G).im=1) ∨ ((u:G).re=0 ∧ (u:G).im= -1) := by
  have hn : (u:G).norm=1 := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1:ℤ) ≤ 0) _).mpr u.isUnit
  have hn' : (u:G).re^2+(u:G).im^2=1 := by rw [Zsqrtd.norm_def] at hn; nlinarith
  have hr : -1 ≤ (u:G).re ∧ (u:G).re ≤ 1 := by constructor <;> nlinarith [sq_nonneg (u:G).im]
  have hi : -1 ≤ (u:G).im ∧ (u:G).im ≤ 1 := by constructor <;> nlinarith [sq_nonneg (u:G).re]
  obtain ⟨hr₁,hr₂⟩ := hr
  obtain ⟨hi₁,hi₂⟩ := hi
  interval_cases hr' : (u:G).re <;> interval_cases hi' : (u:G).im <;> norm_num [hr',hi'] at *

lemma squareCoords_star (z : G) : squareCoords (star z)=squareCoords z := by
  simp [squareCoords]

lemma squareCoords_associated {z w : G} (h : Associated z w) : squareCoords z=squareCoords w := by
  obtain ⟨u,rfl⟩ := h
  rcases unit_coords u with ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ <;>
    simp [squareCoords,Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hi,Finset.pair_comm]

lemma coprime_mul_unit {h : G} (hc : IsCoprime h.re h.im) (u : Gˣ) :
    IsCoprime (h*(u:G)).re (h*(u:G)).im := by
  rcases unit_coords u with ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ <;>
    simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hi,mul_one,mul_zero,mul_neg_one,
      add_zero,zero_add,neg_mul,neg_neg,one_mul,IsCoprime.neg_left_iff,IsCoprime.neg_right_iff]
  · exact hc
  · exact hc
  · exact hc.symm
  · exact hc.symm

lemma parity_mul_unit {h : G} (hp : h.re%2 ≠ h.im%2) (u : Gˣ) :
    (h*(u:G)).re%2 ≠ (h*(u:G)).im%2 := by
  rcases unit_coords u with ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ <;>
    simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hi,mul_one,mul_zero,mul_neg_one,
      add_zero,zero_add,neg_mul,neg_neg] <;> omega

lemma exists_quadrant_unit {h : G} (hh : h ≠ 0) :
    ∃ u : Gˣ, 0<(h*(u:G)).re ∧ 0 ≤ (h*(u:G)).im := by
  by_cases hr : 0<h.re
  · by_cases hi : 0 ≤ h.im
    · exact ⟨1,by simpa using And.intro hr hi⟩
    · refine ⟨imagUnit,?_⟩
      simp [imagUnit]
      omega
  · by_cases hi : 0<h.im
    · refine ⟨-imagUnit,?_⟩
      simp [imagUnit]
      omega
    · by_cases hr' : h.re<0
      · have hi' : 0 ≤ -h.im := by omega
        exact ⟨-1,by simpa using And.intro (neg_pos.mpr hr') hi'⟩
      · have hr0 : h.re=0 := by omega
        have hi' : h.im<0 := by
          by_contra hi'
          apply hh
          have hi0 : h.im=0 := by omega
          ext <;> simp [hr0,hi0]
        refine ⟨imagUnit,?_⟩
        simp [imagUnit,hr0]
        omega

/-- Both the input factorization and the unordered output coordinates survive
    first-quadrant normalization of the small primitive odd factor. -/
theorem quadrant_factor {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ 0<h.re ∧ 0 ≤ h.im ∧ IsCoprime h.re h.im ∧
      h.re%2 ≠ h.im%2 ∧ h.norm^2 ≤ z.norm ∧ squareCoords w=squareCoords (g*star h) := by
  obtain ⟨g,h,hz',hh,hcop,hpar,hsmall,hw⟩ := small_odd_factor hz he
  obtain ⟨u,hur,hui⟩ := exists_quadrant_unit hh
  let g' := g*(↑(u⁻¹):G)
  let h' := h*(u:G)
  have hz'' : z=g'*h' := by
    rw [hz']
    dsimp [g',h']
    calc
      g*h = (g*h)*((↑(u⁻¹):G)*(u:G)) := by simp
      _ = _ := by ring
  have ha : Associated (g*star h) (g'*star h') := by
    refine ⟨u⁻¹*star u,?_⟩
    dsimp [g',h']
    simp only [star_mul]
    ring
  have hnorm : h.norm=h'.norm := norm_eq_of_associated (show Associated h h' from ⟨u,rfl⟩)
  refine ⟨g',h',hz'',hur,hui,coprime_mul_unit hcop u,parity_mul_unit hpar u,?_,?_⟩
  · rwa [← hnorm]
  · rcases hw with hw | hw
    · exact squareCoords_associated (hw.trans ha)
    · simpa only [squareCoords_star] using squareCoords_associated (hw.trans ha)

#print axioms unit_coords
#print axioms squareCoords_associated
#print axioms exists_quadrant_unit
#print axioms quadrant_factor
end
end Erdos773.GaussianQuadrantFactor
