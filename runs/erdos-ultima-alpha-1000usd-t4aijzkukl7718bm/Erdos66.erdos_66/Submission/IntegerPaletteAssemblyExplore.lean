import Submission.IntegerPaletteSlicesExplore

/-! Exact assembly and a quantitative error bound for piecewise palette sets.
Only same-modulus mixed estimates are used. -/
namespace Erdos66IntegerPaletteAssembly
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66IntegerPaletteSlices
  Erdos66OuterMixedPrefix Erdos66OuterCarryProfile Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 2400000

lemma pairs_biUnion_left {ι : Type*} (s : Finset ι) (A : ι → Finset ℕ)
    (B : Finset ℕ) (n : ℕ) (hA : (s:Set ι).PairwiseDisjoint A) :
    pairs (s.biUnion A) B n = ∑ i∈s, pairs (A i) B n := by
  simp only [pairs_eq_filter,Finset.filter_biUnion]
  apply Finset.card_biUnion
  intro i hi j hj hij
  exact Finset.disjoint_filter_filter (hA hi hj hij)

lemma pairs_biUnion_right {ι : Type*} (s : Finset ι) (A : Finset ℕ)
    (B : ι → Finset ℕ) (n : ℕ) (hB : (s:Set ι).PairwiseDisjoint B) :
    pairs A (s.biUnion B) n = ∑ i∈s, pairs A (B i) n := by
  rw [pairs_comm,pairs_biUnion_left s B A n hB]
  apply Finset.sum_congr rfl
  intro i hi
  exact pairs_comm _ _ _

lemma sumRep_biUnion {ι : Type*} (s : Finset ι) (A : ι → Finset ℕ)
    (n : ℕ) (hA : (s:Set ι).PairwiseDisjoint A) :
    sumRep (s.biUnion A : Set ℕ) n = ∑ i∈s, ∑ j∈s, pairs (A i) (A j) n := by
  rw [←pairs_self,pairs_biUnion_left s A _ n hA]
  apply Finset.sum_congr rfl
  intro i hi
  exact pairs_biUnion_right s (A i) A n hA

variable (M : ℕ) [NeZero M]

noncomputable def assembled {ι : Type*} (s : Finset ι) (C : ι → Finset (ZMod M))
    (a b : ι → ℕ) : Finset ℕ := s.biUnion (fun i ↦ slice M (C i) (a i) (b i))

noncomputable def profile {ι : Type*} (s : Finset ι) (C : ι → Finset (ZMod M))
    (a b : ι → ℕ) (n : ℕ) : ℝ :=
  ∑ i∈s, ∑ j∈s,
    (((cutHi (b i) (a j) n:ℝ)-cutLo (a i) (b i) (a j) (b j) n)/M)*actualMean M (C i) (C j)

lemma slice_pairwiseDisjoint {ι : Type*} (s : Finset ι) (C : ι → Finset (ZMod M))
    (a b : ι → ℕ) (h : ∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (s:Set ι).PairwiseDisjoint (fun i ↦ slice M (C i) (a i) (b i)) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hxM,hxa,hxb,hxC⟩ := (mem_slice M (C i) (a i) (b i) x).mp hx
  obtain ⟨hyM,hya,hyb,hyC⟩ := (mem_slice M (C j) (a j) (b j) x).mp hy
  rcases h i hi j hj hij with hh | hh <;> omega

/-- A finite piecewise spatial choice from a jointly prefix-flat palette has
an explicitly controlled integer convolution. No monotonicity of the choices
is assumed. The cost is summed over the finitely many pairs of pieces. -/
theorem assembled_profile_error {ι : Type*} (s : Finset ι)
    (C : ι → Finset (ZMod M)) (a b : ι → ℕ)
    (hdisj : ∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    (hb : ∀ i∈s, b i ≤ M) (η : ℝ)
    (hprefix : ∀ i∈s, ∀ j∈s, ∀ z u, u ≤ M →
      |(prefixCount M (C i) (C j) z u:ℝ)-(u:ℝ)/M*actualMean M (C i) (C j)| ≤
        η*actualMean M (C i) (C j)) (n : ℕ) :
    |(sumRep (assembled M s C a b : Set ℕ) n:ℝ)-profile M s C a b n| ≤
      (2*η/M)*(∑ i∈s, ((C i).card:ℝ))^2 := by
  have he := sumRep_biUnion s (fun i ↦ slice M (C i) (a i) (b i)) n
    (slice_pairwiseDisjoint M s C a b hdisj)
  have he' : (sumRep (assembled M s C a b : Set ℕ) n:ℝ) =
      ∑ i∈s, ∑ j∈s, (pairs (slice M (C i) (a i) (b i)) (slice M (C j) (a j) (b j)) n:ℝ) := by
    exact_mod_cast he
  rw [he',profile,←Finset.sum_sub_distrib]
  simp_rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i∈s, ∑ j∈s,
        |(pairs (slice M (C i) (a i) (b i)) (slice M (C j) (a j) (b j)) n:ℝ)-
          (((cutHi (b i) (a j) n:ℝ)-cutLo (a i) (b i) (a j) (b j) n)/M)*actualMean M (C i) (C j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi ↦ Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i∈s, ∑ j∈s, 2*η*actualMean M (C i) (C j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact pairs_slice_error M (C i) (C j) (a i) (b i) (a j) (b j) n (hb i hi) (hb j hj) η (hprefix i hi j hj)
    _ = _ := by
      rw [pow_two,Finset.sum_mul_sum]
      simp only [actualMean,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma slice_card_error (C : Finset (ZMod M)) (a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ M) (η : ℝ)
    (hprefix : ∀ z u, u ≤ M →
      |(prefixCount M C Finset.univ z u:ℝ)-(u:ℝ)/M*(C.card:ℝ)| ≤ η*(C.card:ℝ)) :
    |((slice M C a b).card:ℝ)-((b:ℝ)-a)/M*(C.card:ℝ)| ≤ 2*η*(C.card:ℝ) := by
  have he : (slice M C a b).card = intervalCount M C Finset.univ 0 a b := by
    rw [Erdos66IntegerPaletteSlices.slice,Finset.card_image_of_injective _ (ZMod.val_injective M),intervalCount]
    simp only [Finset.mem_univ,and_true]
  rw [he]
  have hh := interval_error_of_prefix_error M C Finset.univ 0 a b hab
    C.card (η*(C.card:ℝ)) (hprefix _ _ (hab.trans hb)) (hprefix _ _ hb)
  simpa only [mul_assoc] using hh

/-- The same assembled set also has the expected total cardinality. -/
theorem assembled_card_error {ι : Type*} (s : Finset ι)
    (C : ι → Finset (ZMod M)) (a b : ι → ℕ)
    (hdisj : ∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    (hab : ∀ i∈s, a i ≤ b i) (hb : ∀ i∈s, b i ≤ M) (η : ℝ)
    (hprefix : ∀ i∈s, ∀ z u, u ≤ M →
      |(prefixCount M (C i) Finset.univ z u:ℝ)-(u:ℝ)/M*((C i).card:ℝ)| ≤ η*((C i).card:ℝ)) :
    |((assembled M s C a b).card:ℝ)-∑ i∈s, ((b i:ℝ)-a i)/M*((C i).card:ℝ)| ≤
      2*η*(∑ i∈s, ((C i).card:ℝ)) := by
  have he := Finset.card_biUnion (slice_pairwiseDisjoint M s C a b hdisj)
  have he' : ((assembled M s C a b).card:ℝ) = ∑ i∈s, ((slice M (C i) (a i) (b i)).card:ℝ) := by
    exact_mod_cast he
  rw [he',←Finset.sum_sub_distrib,Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
    (fun i hi ↦ slice_card_error M (C i) (a i) (b i) (hab i hi) (hb i hi) η (hprefix i hi)))

end Erdos66IntegerPaletteAssembly
