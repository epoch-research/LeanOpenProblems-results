import Submission.BuchstabLocalCost
import Submission.BuchstabDominatingTransfer

/-! Fully charged marginal-domination transfer with a linear level error. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg

theorem survivor_of_scaled_linear_refinement {α : Type*} (A : Finset α) (w : α → ℝ)
    (ω : α → ℕ → Bool) (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hmono : StrictMono p) (x D : ℝ) (K J : ℕ) (hKJ : K ≤ J) (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hw : ∀ j ∈ A, 0 ≤ w j)
    (hmoment : ∀ T : Finset ℕ, T ⊆ range K →
      |moment A w ω T-x*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1)
    (n : ℕ)
    (hpos : 4*(1+prefixReciprocal p J)^(2*n+1)*D <
      x*lowerStep (fun i => 1/(p i : ℝ)) (primeKeep p)
        (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSelbergBase p) n) K D) :
    ∃ j ∈ A, ∀ i < K, ω j i = false := by
  apply survivor_of_refinement A w ω (fun i => 1/(p i : ℝ)) x D K (primeKeep p)
    (scaledSelbergBase p) scaledSelbergCost hw (fun i => by positivity) hx
      scaledSelbergCost_nonneg hmoment _ n
  · exact (scaled_refined_lowerError_le_linear p hp hmono n K J hKJ D hD).trans_lt hpos
  · intro k hk T hTK hT
    simpa only [scaledSelbergBase,scaledSelbergCost,mul_assoc] using
      conditional_selberg_upper A w ω p hp hmono.injective x (4*D) K hw hmoment k hk T hTK hT

theorem survivor_from_dominating_linear_refinement (k J m : ℕ) (hkJ : k ≤ J) (q : Fin k → ℝ)
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (hq : ∀ i, q i < 1 ∧ q i ≤ 1/(p i.val : ℝ))
    (ω : ℕ → Fin k → Bool)
    (herr : ∀ T : Finset (Fin k),
      |(∑ j ∈ range m, hitMonomial T (ω j))-(m : ℝ)*∏ i ∈ T, q i| ≤ 1)
    (D : ℝ) (hD : 0 ≤ D) (n : ℕ)
    (hpos : 4*(1+prefixReciprocal p J)^(2*n+1)*D <
      (m : ℝ)*lowerStep (fun i => 1/(p i : ℝ)) (primeKeep p)
        (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSelbergBase p) n) k D) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  let q' (i : Fin k) : ℝ := 1/(p i.val : ℝ)
  have hq' (i : Fin k) : q' i ≤ 1 := by
    have hp' : (1 : ℝ) < p i.val := by exact_mod_cast (hp i.val).one_lt
    exact ((div_lt_one (by linarith : (0 : ℝ) < p i.val)).mpr hp').le
  let b (i : Fin k) := (q' i-q i)/(1-q i)
  have hb (i : Fin k) : 0 ≤ b i ∧ b i ≤ 1 := by
    have hd : 0 < 1-q i := sub_pos.mpr (hq i).1
    exact ⟨div_nonneg (sub_nonneg.mpr (hq i).2) hd.le,
      (div_le_one hd).mpr (by linarith [hq' i])⟩
  have hbq (i : Fin k) : b i+(1-b i)*q i = q' i := by
    have hd : 1-q i ≠ 0 := (sub_pos.mpr (hq i).1).ne'
    dsimp [b]
    field_simp
    ring
  let A := (range m) ×ˢ (univ : Finset (Fin k → Bool))
  let w (x : ℕ × (Fin k → Bool)) := probability b x.2
  let v (x : ℕ × (Fin k → Bool)) := extendPattern (fun i => ω x.1 i || x.2 i)
  have hw : ∀ x ∈ A, 0 ≤ w x := by
    intro x hx
    apply prod_nonneg
    intro i hi
    split_ifs
    · exact (hb i).1
    · exact sub_nonneg.mpr (hb i).2
  have hmom (T : Finset ℕ) (hT : T ⊆ range k) :
      |moment A w v T-(m : ℝ)*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1 := by
    have hh := added_hits_moment_error b q hb m ω herr (liftSet k T)
    simp_rw [hbq] at hh
    dsimp only [q'] at hh
    rw [liftSet_prod T hT (fun i => 1/(p i : ℝ))] at hh
    simpa only [A,w,v,boosted_moment] using hh
  obtain ⟨x,hx,hxall⟩ := survivor_of_scaled_linear_refinement A w v p hp hmono
    (m : ℝ) D k J hkJ (Nat.cast_nonneg m) hD hw hmom n hpos
  refine ⟨x.1,mem_range.mp (mem_product.mp hx).1,fun i => ?_⟩
  have hh := hxall i.val i.isLt
  simp only [v,extendPattern,i.isLt,↓reduceDIte] at hh
  exact (Bool.or_eq_false_iff.mp hh).1


#print axioms survivor_from_dominating_linear_refinement
end Erdos970.RecursiveSieve.Buchstab
