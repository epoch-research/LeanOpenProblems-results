import Submission.ParameterPeakTransfer
import Submission.Spec

/-! The parameter-count criterion connected to the exact representation count
in the conjecture. Repeated parameter outputs are explicitly bounded. -/
namespace Erdos322Research.RepresentationParameterPeaks
noncomputable section
open Finset
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

private def forgetBounds (k n : ℕ) : (Fin k → Fin (n+1)) ↪ (Fin k → ℕ) where
  toFun := fun a i ↦ (a i : ℕ)
  inj' := by
    intro a b h
    funext i
    exact Fin.ext (congrFun h i)

/-- The same finite representation set, with bounds forgotten after construction. -/
def natRepresentations (k n : ℕ) : Finset (Fin k → ℕ) :=
  ((Finset.univ : Finset (Fin k → Fin (n+1))).filter
    (fun a ↦ ∑ i, (a i : ℕ)^k=n)).map (forgetBounds k n)

theorem natRepresentations_card (k n : ℕ) :
    (natRepresentations k n).card=Erdos322.representationCount k n := by
  simp only [natRepresentations,card_map,Erdos322.representationCount]

theorem mem_natRepresentations (k n : ℕ) (hk : 0<k) (x : Fin k → ℕ) :
    x∈natRepresentations k n ↔ ∑ i, x i^k=n := by
  constructor
  · intro hx
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    exact (mem_filter.mp ha).2
  · intro hx
    have hb (i) : x i<n+1 := by
      have hle : x i≤x i^k := Nat.le_pow hk
      have hs : x i^k≤∑ j, x j^k := single_le_sum (f := fun j : Fin k ↦ x j^k) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
      omega
    let a : Fin k → Fin (n+1) := fun i ↦ ⟨x i,hb i⟩
    apply mem_map.mpr
    refine ⟨a,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_univ _,hx⟩

/-- A fully explicit sufficient condition for the power peaks requested by the
conjecture. The exponent loss from repeated outputs is `f`, not zero by default. -/
theorem representation_peaks_of_parameters {α : ℕ → Type*}
    (k : ℕ) (hk : 0<k) (S : ∀ B, Finset (α B)) (T : ℕ → Finset ℕ)
    (N : ∀ B, α B → ℕ) (P : ∀ B, α B → Fin k → ℕ)
    (m e f d B₀ : ℕ) (hd : 0<d) (hgap : e + f < m)
    (hS : ∀ B, B₀≤B → B^m≤(S B).card)
    (hT : ∀ B, B₀≤B → (T B).card≤B^e)
    (hN : ∀ B, B₀≤B → ∀ a∈S B, N B a∈T B)
    (hsum : ∀ B, B₀≤B → ∀ a∈S B, ∑ i, (P B a i)^k=N B a)
    (hmult : ∀ B, B₀≤B → ∀ x : Fin k → ℕ,
      ((S B).filter (fun a ↦ P B a=x)).card≤B^f)
    (hheight : ∀ B, B₀≤B → ∀ n∈T B, n≤B^d) :
    {n : ℕ | (n : ℝ)^(((m-e-f : ℕ) : ℝ)/(2*d)) <
      (Erdos322.representationCount k n : ℝ)}.Infinite := by
  apply ParameterPeakTransfer.peaks_of_parameter_counts S T N
    (Erdos322.representationCount k) m e f d B₀ hd hgap hS hT hN ?_ hheight
  intro B hB n _
  rw [← natRepresentations_card]
  apply ParameterPeakTransfer.fiber_bound_of_output_multiplicity
    (S B) (N B) (P B) (natRepresentations k) (B^f) n
  · intro a ha
    exact (mem_natRepresentations k (N B a) hk (P B a)).mpr (hsum B hB a ha)
  · intro x _
    calc
      _ ≤ ((S B).filter (fun a ↦ P B a=x)).card := by
        apply card_le_card
        intro a ha
        simp only [mem_filter] at ha ⊢
        exact ⟨ha.1.1,ha.2⟩
      _ ≤ B^f := hmult B hB x

end
end Erdos322Research.RepresentationParameterPeaks
