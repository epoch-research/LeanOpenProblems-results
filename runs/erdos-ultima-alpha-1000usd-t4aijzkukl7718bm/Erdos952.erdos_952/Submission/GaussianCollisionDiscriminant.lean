import Submission.GaussianHigherSmoothingLower
import Submission.GaussianRootCRT

/-! Arithmetic constraints on the root counts of a finite Gaussian pattern.
Collisions modulo coprime Gaussian moduli force powers of those moduli into
an ordered product of differences. This is a finite larger-sieve input, not
a Gaussian-moat disproof. -/
namespace Erdos952Investigation.GaussianCollisionDiscriminant
open GaussianIdealRepresentatives GaussianPolynomialBoxCounts GaussianHigherSmoothingLower
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

def classes {ι : Type*} [Fintype ι] (z : ι → GaussianInt) (g : GaussianInt) :
    Finset (GaussianInt ⧸ multiples g) :=
  Finset.univ.image (fun i => Submodule.Quotient.mk (z i))

def collisions {ι : Type*} [Fintype ι] (z : ι → GaussianInt) (g : GaussianInt) : Finset (ι × ι) :=
  (Finset.univ : Finset ι).offDiag.filter (fun ij => g ∣ z ij.1-z ij.2)

def collisionCount {ι : Type*} [Fintype ι] (z : ι → GaussianInt) (g : GaussianInt) : ℕ :=
  (collisions z g).card

lemma mem_collisions {ι : Type*} [Fintype ι] (z : ι → GaussianInt) (g : GaussianInt) (ij : ι × ι) :
    ij ∈ collisions z g ↔ ij.1 ≠ ij.2 ∧ g ∣ z ij.1-z ij.2 := by
  simp [collisions,Finset.mem_offDiag]

/-- The roots of the translated linear-factor product are the negatives of
these classes, hence have the same cardinality. -/
lemma classes_card_eq_rootCount {ι : Type*} [Fintype ι] (z : ι → GaussianInt)
    (g : GaussianInt) (hg : Prime g) :
    (classes z g).card = rootCount g hg.ne_zero (patternPolynomial z) := by
  rw [rootCount,rootClasses_prime_pattern z g hg]
  have he : Finset.univ.image (fun i => (Submodule.Quotient.mk (-z i) : GaussianInt ⧸ multiples g)) =
      (classes z g).image (fun q => -q) := by
    simp only [classes,Finset.image_image,Submodule.Quotient.mk_neg,Function.comp_def]
  rw [he,Finset.card_image_of_injective _ neg_injective]

/-- Cauchy-Schwarz forces collisions when a pattern occupies few classes.
The collision count is ORDERED and excludes equal indices. -/
theorem class_collision_inequality {ι : Type*} [Fintype ι] (z : ι → GaussianInt) (g : GaussianInt) :
    (Fintype.card ι)^2 ≤ (classes z g).card*(Fintype.card ι+collisionCount z g) := by
  let c : ι → classes z g := fun i => ⟨Submodule.Quotient.mk (z i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let f : SameCell c → ι ⊕ collisions z g := fun s =>
    if he : s.val.1 = s.val.2 then Sum.inl s.val.1
    else Sum.inr ⟨s.val,(mem_collisions z g s.val).mpr ⟨he,
      (quotient_eq_iff_dvd g _ _).mp (congrArg Subtype.val s.property)⟩⟩
  let back : ι ⊕ collisions z g → ι × ι := Sum.elim (fun i => (i,i)) Subtype.val
  have hb (s : SameCell c) : back (f s) = s.val := by
    dsimp [f]
    split_ifs with he
    · change (s.val.1,s.val.1) = s.val
      exact Prod.ext rfl he
    · rfl
  have hf : Function.Injective f := by
    intro s t he
    apply Subtype.ext
    have hh := congrArg back he
    simpa only [hb] using hh
  have hcard := Nat.card_le_card_of_injective f hf
  have hs : Nat.card (SameCell c) ≤ Fintype.card ι+collisionCount z g := by
    simpa only [Nat.card_sum,Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_coe,collisionCount] using hcard
  have hh := sameCell_card c
  simp only [Fintype.card_coe] at hh
  exact hh.trans (Nat.mul_le_mul_left _ hs)

theorem root_collision_inequality {ι : Type*} [Fintype ι] (z : ι → GaussianInt)
    (g : GaussianInt) (hg : Prime g) :
    (Fintype.card ι)^2 ≤ rootCount g hg.ne_zero (patternPolynomial z)*
      (Fintype.card ι+collisionCount z g) := by
  rw [← classes_card_eq_rootCount z g hg]
  exact class_collision_inequality z g

/-- Ordered product: each unordered difference occurs in both orientations.
This convention matches collisionCount exactly. -/
def discriminant {ι : Type*} [Fintype ι] (z : ι → GaussianInt) : GaussianInt :=
  ∏ ij ∈ (Finset.univ : Finset ι).offDiag, (z ij.1-z ij.2)

lemma discriminant_ne_zero {ι : Type*} [Fintype ι] (z : ι → GaussianInt)
    (hz : Function.Injective z) : discriminant z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro ij hij
  have hne := (Finset.mem_offDiag.mp hij).2.2
  exact sub_ne_zero.mpr (fun he => hne (hz he))

/-- Each colliding ordered pair contributes at least one factor g. No
primality assumption is needed for this divisibility statement. -/
theorem collision_power_dvd {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (g : GaussianInt) : g^(collisionCount z g) ∣ discriminant z := by
  have hd := Finset.prod_dvd_prod_of_dvd (s := collisions z g) (fun _ => g)
    (fun ij => z ij.1-z ij.2) (fun ij hij => ((mem_collisions z g ij).mp hij).2)
  rw [Finset.prod_const] at hd
  apply hd.trans
  exact Finset.prod_dvd_prod_of_subset (collisions z g) (Finset.univ.offDiag)
    (fun ij => z ij.1-z ij.2) (Finset.filter_subset _ _)

/-- Contributions from coprime moduli can be multiplied, rather than merely
bounded separately. -/
theorem collision_product_dvd {ι J : Type*} [Fintype ι]
    (z : ι → GaussianInt) (g : J → GaussianInt) (S : Finset J)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j))) :
    (∏ j ∈ S, (g j)^(collisionCount z (g j))) ∣ discriminant z := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact (hc hi hj hij).pow
  · exact fun j _ => collision_power_dvd z (g j)

lemma norm_discriminant {ι : Type*} [Fintype ι] (z : ι → GaussianInt) :
    (discriminant z).norm = ∏ ij ∈ (Finset.univ : Finset ι).offDiag, (z ij.1-z ij.2).norm := by
  change Zsqrtd.normMonoidHom (∏ ij ∈ (Finset.univ : Finset ι).offDiag, (z ij.1-z ij.2)) = _
  exact map_prod Zsqrtd.normMonoidHom _ _

/-- The collision exponents have a finite multiplicative budget controlled
by the actual geometry of the configuration. -/
theorem collision_norm_product_le {ι J : Type*} [Fintype ι]
    (z : ι → GaussianInt) (hz : Function.Injective z)
    (g : J → GaussianInt) (S : Finset J)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j))) :
    (∏ j ∈ S, (g j).norm^(collisionCount z (g j))) ≤
      ∏ ij ∈ (Finset.univ : Finset ι).offDiag, (z ij.1-z ij.2).norm := by
  have hd := Zsqrtd.normMonoidHom.map_dvd (collision_product_dvd z g S hc)
  have hp := GaussianInt.norm_pos.mpr (discriminant_ne_zero z hz)
  have hh := Int.le_of_dvd hp hd
  change Zsqrtd.normMonoidHom (∏ j ∈ S, (g j)^(collisionCount z (g j))) ≤ (discriminant z).norm at hh
  simp only [map_prod,map_pow] at hh
  rwa [norm_discriminant] at hh

/-- Any explicit pairwise distance bounds can be inserted into the budget. -/
theorem collision_norm_product_le_bounds {ι J : Type*} [Fintype ι]
    (z : ι → GaussianInt) (hz : Function.Injective z)
    (g : J → GaussianInt) (S : Finset J)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j)))
    (B : ι × ι → ℤ) (hB : ∀ i j, i ≠ j → (z i-z j).norm ≤ B (i,j)) :
    (∏ j ∈ S, (g j).norm^(collisionCount z (g j))) ≤
      ∏ ij ∈ (Finset.univ : Finset ι).offDiag, B ij := by
  apply (collision_norm_product_le z hz g S hc).trans
  apply Finset.prod_le_prod
  · exact fun _ _ => GaussianInt.norm_nonneg _
  · intro ij hij
    exact hB ij.1 ij.2 (Finset.mem_offDiag.mp hij).2.2

/-- A coarser diameter-only consequence, valid also for empty configurations. -/
theorem collision_norm_product_le_diameter {ι J : Type*} [Fintype ι]
    (z : ι → GaussianInt) (hz : Function.Injective z)
    (g : J → GaussianInt) (S : Finset J)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j)))
    (B : ℤ) (hB : ∀ i j, i ≠ j → (z i-z j).norm ≤ B) :
    (∏ j ∈ S, (g j).norm^(collisionCount z (g j))) ≤
      B^((Fintype.card ι)^2-Fintype.card ι) := by
  have hh := collision_norm_product_le_bounds z hz g S hc (fun _ => B) hB
  simpa only [Finset.prod_const,Finset.offDiag_card,Finset.card_univ,pow_two] using hh

#print axioms root_collision_inequality
#print axioms collision_power_dvd
#print axioms collision_norm_product_le
#print axioms collision_norm_product_le_bounds
#print axioms collision_norm_product_le_diameter
end
end Erdos952Investigation.GaussianCollisionDiscriminant
