import Submission.PolynomialRingGraphCapacityExplore

/-! Capacity of arbitrary finite covers by polynomial graphs over a square
modulus. The covered set may use any subset of each graph. -/
namespace Erdos66PolynomialRingCoverCapacity
open AdditiveCombinatorics Erdos66PolynomialRingGraphCapacity
open scoped Classical
set_option maxHeartbeats 2200000

variable (q : ℕ) [NeZero q]

/-- The degree and coefficients may vary freely from graph to graph. -/
theorem polynomial_cover_capacity (h : ℕ) (P : Fin h → Polynomial (ZMod (q^2)))
    (a : Fin h → ℕ) (aMax : ℕ) (ha : ∀ i, a i ≤ aMax)
    (S : Finset ℕ) (A : Set ℕ) (hSA : (S : Set ℕ) ⊆ A)
    (hcover : ∀ n ∈ S, ∃ i x, n = encodeGraph q (P i) (a i) x)
    (V : ℝ) (hV : 0 ≤ V)
    (hcap : ∀ n, n < 2*(aMax+q^4) → (sumRep A n : ℝ) ≤ V) :
    (S.card : ℝ)^2 ≤ 4*(h : ℝ)^2*(q : ℝ)^3*V := by
  by_cases hh : h=0
  · subst h
    have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨i,_,_⟩ := hcover n hn
      exact Fin.elim0 i
    simp only [he,Finset.card_empty,Nat.cast_zero,zero_pow (by decide : 2≠0),mul_zero,zero_mul,le_refl]
  · let B : Fin h → Finset (ZMod (q^2)) := fun i ↦
      Finset.univ.filter (fun x ↦ encodeGraph q (P i) (a i) x ∈ S)
    have hn : (Finset.univ : Finset (Fin h)).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
    obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin h)) (fun i ↦ (B i).card) hn
    have hsub : S ⊆ Finset.univ.biUnion (fun i ↦ (B i).image (encodeGraph q (P i) (a i))) := by
      intro n hn
      obtain ⟨j,x,rfl⟩ := hcover n hn
      apply Finset.mem_biUnion.mpr
      refine ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨x,?_,rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
    have hc : S.card ≤ h*(B i).card := by
      have hh := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul Finset.univ
        (fun j ↦ (B j).image (encodeGraph q (P j) (a j))) (B i).card (by
          intro j hj
          rw [Finset.card_image_of_injective _ (encodeGraph_injective q (P j) (a j))]
          exact hmax j hj))
      simpa only [Finset.card_univ,Fintype.card_fin] using hh
    have hp := polynomial_graph_capacity q (P i) (a i) (B i) A
      (fun x hx ↦ hSA (Finset.mem_filter.mp hx).2) V hV (fun n _ hn ↦ hcap n (by have := ha i; omega))
    have hc' : (S.card : ℝ) ≤ h*(B i).card := by exact_mod_cast hc
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) S.card) hc' 2
    have hh' := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (h : ℝ)^2 by positivity)
    nlinarith only [hs,hh']

theorem polynomial_cover_log_capacity (h : ℕ) (P : Fin h → Polynomial (ZMod (q^2)))
    (a : Fin h → ℕ) (aMax : ℕ) (ha : ∀ i, a i ≤ aMax)
    (S : Finset ℕ) (A : Set ℕ) (hSA : (S : Set ℕ) ⊆ A)
    (hcover : ∀ n ∈ S, ∃ i x, n = encodeGraph q (P i) (a i) x)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (henv : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2)) :
    (S.card : ℝ)^2 ≤ 4*(h : ℝ)^2*(q : ℝ)^3*(K+C*Real.log (2*((aMax : ℝ)+q^4)+2)) := by
  have hlog : 0 ≤ Real.log (2*((aMax : ℝ)+(q : ℝ)^4)+2) := by
    apply Real.log_nonneg
    have hh : (0 : ℝ) ≤ (aMax : ℝ)+(q : ℝ)^4 := by positivity
    linarith
  apply polynomial_cover_capacity q h P a aMax ha S A hSA hcover _ (add_nonneg hK (mul_nonneg hC hlog))
  intro n hn
  have hln := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ)+2)
    (show (n : ℝ)+2 ≤ 2*((aMax : ℝ)+(q : ℝ)^4)+2 by exact_mod_cast (show n+2 ≤ 2*(aMax+q^4)+2 by omega))
  exact (henv n).trans (add_le_add_right (mul_le_mul_of_nonneg_left hln hC) K)

end Erdos66PolynomialRingCoverCapacity
