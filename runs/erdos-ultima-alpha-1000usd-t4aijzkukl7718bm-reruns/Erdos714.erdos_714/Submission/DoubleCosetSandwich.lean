import Submission.DoubleCosetOrbital

/-!
Transport of double-coset biclique certificates under left multiplication of
representatives. This is a conditional construction lemma, not an extremal
lower bound. All conjugation and subgroup-inclusion hypotheses are explicit.
-/
noncomputable section
open SimpleGraph Classical
namespace Erdos714DoubleCoset
variable {Γ : Type*} [Group Γ]

/-- A two-sided change of representatives can transfer a biclique to smaller
stabilizers, provided its individual factors land in those stabilizers.
The entire old stabilizers need not land in the new ones. -/
def sandwichCopy (P Q H K : Subgroup Γ) (g a b : Γ) {r s : ℕ}
    (L : Fin r → Γ) (R : Fin s → Γ)
    (hL : ∀ i j, L j * (L i)⁻¹ ∈ P → i = j)
    (hR : ∀ i j, R j * (R i)⁻¹ ∈ Q → i = j)
    (hH : ∀ x ∈ H, a⁻¹ * x * a ∈ P)
    (hK : ∀ x ∈ K, b⁻¹ * x * b ∈ Q)
    (hg : b * g * a⁻¹ = g)
    (hedge : ∀ i j, ∃ k h : Γ,
      b * k * b⁻¹ ∈ K ∧ a * h * a⁻¹ ∈ H ∧ R j * (L i)⁻¹ = k * g * h) :
    Copy (completeBipartiteGraph (Fin r) (Fin s)) (graph H K g) := by
  apply representativesCopy H K g (fun i => a * L i) (fun j => b * R j)
  · intro i j hij
    apply hL i j
    have hh := hH _ hij
    convert hh using 1; group
  · intro i j hij
    apply hR i j
    have hh := hK _ hij
    convert hh using 1; group
  · intro i j
    obtain ⟨k,h,hk,hh,he⟩ := hedge i j
    refine ⟨b*k*b⁻¹,hk,a*h*a⁻¹,hh,?_⟩
    calc
      (b*R j)*(a*L i)⁻¹ = b*(R j*(L i)⁻¹)*a⁻¹ := by group
      _ = b*(k*g*h)*a⁻¹ := by rw [he]
      _ = (b*k*b⁻¹)*(b*g*a⁻¹)*(a*h*a⁻¹) := by group
      _ = (b*k*b⁻¹)*g*(a*h*a⁻¹) := by rw [hg]

/-- Useful for involutions inverted by a diagonal torus: the sandwich identity
also holds with the inverse torus parameter. No commutation is assumed. -/
lemma inverse_sandwich {g a : Γ} (h : a*g*a = g) : a⁻¹*g*a⁻¹ = g := by
  calc
    a⁻¹*g*a⁻¹ = a⁻¹*(a*g*a)*a⁻¹ := by rw [h]
    _ = g := by group

end Erdos714DoubleCoset
#print axioms Erdos714DoubleCoset.sandwichCopy
#print axioms Erdos714DoubleCoset.inverse_sandwich
