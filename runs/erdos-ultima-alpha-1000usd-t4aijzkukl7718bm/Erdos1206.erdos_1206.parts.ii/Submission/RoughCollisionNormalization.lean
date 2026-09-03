import Submission.NearUnitPrimitiveMass

/-! Gcd normalization preserves avoidance of a fixed finite-prime modulus
when raw coordinates are all 18 modulo 18 times that modulus. -/
namespace Erdos1206.RoughCollisionNormalization
open PrimitiveCollisionMass (Collision)

lemma divide_eighteen {a : ℤ} {Q : ℕ} (h : (18*(Q:ℤ)) ∣ a-18) :
    ∃ u : ℤ, a=18*u ∧ IsCoprime u (Q:ℤ) := by
  obtain ⟨z,hz⟩ := h
  refine ⟨1+(Q:ℤ)*z,?_,?_⟩
  · linear_combination hz
  · exact ⟨1,-z,by ring⟩

/-- The primitive normalized collision remains coprime to `Q` in every root.
No upper bound on the common factor is needed. -/
lemma primitive_lift_coprime {a b c d : ℤ} {Q : ℕ}
    (ha : 0<a) (hab : a<b) (hbc : b<c) (hcd : c<d)
    (he : a^3+d^3=b^3+c^3)
    (hA : (18*(Q:ℤ)) ∣ a-18) (hB : (18*(Q:ℤ)) ∣ b-18)
    (hC : (18*(Q:ℤ)) ∣ c-18) (hD : (18*(Q:ℤ)) ∣ d-18) :
    ∃ e : Collision, ∃ g : ℕ, 0<g ∧
      a=(18*g:ℤ)*e.val.1 ∧ b=(18*g:ℤ)*e.val.2.1 ∧
      c=(18*g:ℤ)*e.val.2.2.1 ∧ d=(18*g:ℤ)*e.val.2.2.2 ∧
      Nat.Coprime e.val.1 Q ∧ Nat.Coprime e.val.2.1 Q ∧
      Nat.Coprime e.val.2.2.1 Q ∧ Nat.Coprime e.val.2.2.2 Q := by
  obtain ⟨a',ha',hca⟩ := divide_eighteen hA
  obtain ⟨b',hb',hcb⟩ := divide_eighteen hB
  obtain ⟨c',hc',hcc⟩ := divide_eighteen hC
  obtain ⟨d',hd',hcd'⟩ := divide_eighteen hD
  have hapos : 0<a' := by rw [ha'] at ha; linarith
  have hab' : a'<b' := by rw [ha',hb'] at hab; linarith
  have hbc' : b'<c' := by rw [hb',hc'] at hbc; linarith
  have hcdd : c'<d' := by rw [hc',hd'] at hcd; linarith
  have he' : a'^3+d'^3=b'^3+c'^3 := by
    rw [ha',hb',hc',hd'] at he
    nlinarith only [he]
  obtain ⟨e,g,hg,hea,heb,hec,hed⟩ := NearUnitPrimitiveMass.primitive_lift hapos hab' hbc' hcdd he'
  refine ⟨e,g,hg,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ha',hea]; ring
  · rw [hb',heb]; ring
  · rw [hc',hec]; ring
  · rw [hd',hed]; ring
  · rw [hea] at hca
    exact Nat.isCoprime_iff_coprime.mp hca.of_mul_left_right
  · rw [heb] at hcb
    exact Nat.isCoprime_iff_coprime.mp hcb.of_mul_left_right
  · rw [hec] at hcc
    exact Nat.isCoprime_iff_coprime.mp hcc.of_mul_left_right
  · rw [hed] at hcd'
    exact Nat.isCoprime_iff_coprime.mp hcd'.of_mul_left_right

#print axioms primitive_lift_coprime
end Erdos1206.RoughCollisionNormalization
