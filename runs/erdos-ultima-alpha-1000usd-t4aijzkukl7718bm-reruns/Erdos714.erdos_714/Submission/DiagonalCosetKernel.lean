import Submission.DoubleCosetAveraging

/-!
A kernel obstruction for diagonal-subgroup coset constructions.
This is a construction criterion, not a disproof of Erdős 714.
-/
noncomputable section
open SimpleGraph Classical
namespace Erdos714DiagonalCosetKernel
open Erdos714DoubleCoset
variable {P A : Type*} [Group P] [Group A]

/-- Embed a subgroup together with the value of a homomorphism. -/
def diagonalMap (B : Subgroup P) (φ : B →* A) : B →* P × A :=
  B.subtype.prod φ

def diagonal (B : Subgroup P) (φ : B →* A) : Subgroup (P × A) :=
  (diagonalMap B φ).range

lemma diagonal_mem (B : Subgroup P) (φ : B →* A) (b : B) :
    ((b : P), φ b) ∈ diagonal B φ := ⟨b, rfl⟩

lemma first_one (B : Subgroup P) (φ : B →* A) {a : A}
    (h : ((1 : P), a) ∈ diagonal B φ) : a = 1 := by
  obtain ⟨b,hb⟩ := h
  have hf : (b : P) = 1 := congrArg Prod.fst hb
  have hs : φ b = a := congrArg Prod.snd hb
  have hb1 : b = 1 := Subtype.ext hf
  simpa [hb1] using hs.symm

/-- An element in the diagonal subgroup has its first coordinate in B. -/
lemma fst_mem (B : Subgroup P) (φ : B →* A) {p : P × A}
    (h : p ∈ diagonal B φ) : p.1 ∈ B := by
  obtain ⟨b,rfl⟩ := h
  exact b.property

/--
A family of Bruhat factorizations with the same first coordinate gives one
side of a grid; elements forgotten by φ give the other side. The last
hypothesis checks distinctness in the actual opposite cosets.
-/
def kernelCopy (B : Subgroup P) (φ : B →* A) (w : P) (a : A)
    {r s : ℕ} (u v : Fin r → B) (k : Fin s → B)
    (hfactor : ∀ i, (u i : P) * w * (v i : P) = w)
    (hkernel : ∀ j, φ (k j) = 1)
    (hlabels : Function.Injective (fun i => φ (u i) * a * φ (v i)))
    (hcosets : ∀ i j, w⁻¹ * ((k i : P)⁻¹ * (k j : P)) * w ∈ B → i = j) :
    Copy (completeBipartiteGraph (Fin r) (Fin s))
      (graph (diagonal B φ) (diagonal B φ) ((w,a)⁻¹)) := by
  let z (i : Fin r) := φ (u i) * a * φ (v i)
  let L (i : Fin r) : P × A := (1,z i)
  let R (j : Fin s) : P × A := (w⁻¹ * (k j : P)⁻¹,1)
  apply representativesCopy (diagonal B φ) (diagonal B φ) ((w,a)⁻¹) L R
  · intro i j hij
    have hz : z j * (z i)⁻¹ = 1 := first_one B φ (by simpa [L] using hij)
    exact hlabels (mul_inv_eq_one.mp hz).symm
  · intro i j hij
    have hm := fst_mem B φ hij
    have he : (R j * (R i)⁻¹).1 =
        w⁻¹ * ((k j : P)⁻¹ * (k i : P)) * w := by
      dsimp [R]
      group
    rw [he] at hm
    exact (hcosets j i hm).symm
  · intro i j
    let U : P × A := ((u i : P),φ (u i))
    let V : P × A := ((v i : P),φ (v i))
    let K : P × A := ((k j : P),φ (k j))
    have hU : U ∈ diagonal B φ := diagonal_mem B φ (u i)
    have hV : V ∈ diagonal B φ := diagonal_mem B φ (v i)
    have hK : K ∈ diagonal B φ := diagonal_mem B φ (k j)
    refine ⟨V⁻¹,(diagonal B φ).inv_mem hV,(K*U)⁻¹,
      (diagonal B φ).inv_mem ((diagonal B φ).mul_mem hK hU),?_⟩
    have hf : (K*U)*(w,a)*V = ((k j : P)*w,z i) := by
      apply Prod.ext
      · change ((k j : P)*(u i : P))*w*(v i : P) = (k j : P)*w
        calc
          _ = (k j : P)*((u i : P)*w*(v i : P)) := by group
          _ = _ := by rw [hfactor]
      · change (φ (k j)*φ (u i))*a*φ (v i) = z i
        simp [hkernel,z]
    calc
      R j * (L i)⁻¹ = ((k j : P)*w,z i)⁻¹ := by
        apply Prod.ext <;> simp [R,L]
      _ = ((K*U)*(w,a)*V)⁻¹ := congrArg Inv.inv hf.symm
      _ = V⁻¹*(w,a)⁻¹*(K*U)⁻¹ := by group

/-- Four distinct labels and four distinct forgotten parameters suffice. -/
theorem not_free (B : Subgroup P) (φ : B →* A) (w : P) (a : A)
    (u v : Fin 4 → B) (k : Fin 4 → B)
    (hfactor : ∀ i, (u i : P) * w * (v i : P) = w)
    (hkernel : ∀ j, φ (k j) = 1)
    (hlabels : Function.Injective (fun i => φ (u i) * a * φ (v i)))
    (hcosets : ∀ i j, w⁻¹ * ((k i : P)⁻¹ * (k j : P)) * w ∈ B → i = j) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (diagonal B φ) (diagonal B φ) ((w,a)⁻¹)) := by
  intro hfree
  exact hfree ⟨kernelCopy B φ w a u v k hfactor hkernel hlabels hcosets⟩

/-- The same kernel grids bound arbitrary edge deletions, not only the full graph. -/
theorem thinning_bound [Fintype P] [Fintype A]
    (B : Subgroup P) (φ : B →* A) (w : P) (a : A) (r t : ℕ)
    (u v : Fin t → B) (k : Fin t → B)
    (hfactor : ∀ i, (u i : P) * w * (v i : P) = w)
    (hkernel : ∀ j, φ (k j) = 1)
    (hlabels : Function.Injective (fun i => φ (u i) * a * φ (v i)))
    (hcosets : ∀ i j, w⁻¹ * ((k i : P)⁻¹ * (k j : P)) * w ∈ B → i = j)
    (J : SimpleGraph (Cosets (diagonal B φ) ⊕ Cosets (diagonal B φ)))
    (hJ : J ≤ graph (diagonal B φ) (diagonal B φ) ((w,a)⁻¹))
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free J) :
    t^2 * J.edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r)) *
        (graph (diagonal B φ) (diagonal B φ) ((w,a)⁻¹)).edgeFinset.card :=
  biclique_thinning_bound _ _ _ J r t
    (kernelCopy B φ w a u v k hfactor hkernel hlabels hcosets) hJ hfree

end Erdos714DiagonalCosetKernel
#print axioms Erdos714DiagonalCosetKernel.kernelCopy
#print axioms Erdos714DiagonalCosetKernel.not_free
#print axioms Erdos714DiagonalCosetKernel.thinning_bound
