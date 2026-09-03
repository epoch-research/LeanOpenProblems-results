import Submission.IntegerPaletteQuantizationExplore
import Submission.CompactnessExplore
import Submission.TransitionLinearExplore

/-! A genuine prefix-preserving finite extension for old pieces drawn from a
fixed joint palette. It does not replace that palette or change its modulus. -/
namespace Erdos66PalettePrefixExtension
open AdditiveCombinatorics Erdos66IntegerPaletteAssembly Erdos66IntegerPaletteSlices
  Erdos66IntegerPaletteQuantization Erdos66OuterMixedPrefix Erdos66SaturatingCyclicFamily
  Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 2800000

variable (M : ℕ) [NeZero M]

lemma assembled_mono_indices {ι : Type*} (s t : Finset ι) (hst : s ⊆ t)
    (C : ι → Finset (ZMod M)) (a b : ι → ℕ) :
    assembled M s C a b ⊆ assembled M t C a b := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨i,hst hi,hx⟩

lemma assembled_agrees_on_indices {ι : Type*} (s : Finset ι)
    (C D : ι → Finset (ZMod M)) (a b : ι → ℕ) (h : ∀ i∈s, C i=D i) :
    assembled M s C a b = assembled M s D a b := by
  apply Finset.biUnion_congr rfl
  intro i hi
  rw [h i hi]

lemma assembled_prefix {ι : Type*} (s old : Finset ι) (hold : old ⊆ s)
    (C D : ι → Finset (ZMod M)) (a b : ι → ℕ) (L : ℕ)
    (hC : ∀ i∈old, C i=D i)
    (hnew : ∀ i∈s, i∉old → L ≤ a i) :
    ∀ x<L, x∈assembled M s C a b ↔ x∈assembled M old D a b := by
  intro x hxL
  constructor
  · intro hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    have hiold : i∈old := by
      by_contra hn
      have hxa := ((mem_slice M (C i) (a i) (b i) x).mp hx).2.1
      have hh := hnew i hi hn
      omega
    exact Finset.mem_biUnion.mpr ⟨i,hiold,by rwa [←hC i hiold]⟩
  · intro hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨i,hold hi,by rwa [hC i hi]⟩

/-- All old choices may be prescribed first. The only extension hypotheses
on those choices are membership in the joint palette and the same cardinality
brackets as for the new pieces. -/
theorem exists_prefix_preserving_quantized_extension {ι : Type*}
    (s old : Finset ι) (hold : old ⊆ s)
    (B : Finset (ZMod M)) (P : Finset (Finset (ZMod M)))
    (D : ι → Finset (ZMod M)) (w : ι → ℝ) (a b : ι → ℕ) (L : ℕ)
    (hw : ∀ i∈s, 1 ≤ w i) (hfit : ∀ i∈s, w i*(B.card:ℝ) ≤ M)
    (hdisj : ∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    (hb : ∀ i∈s, b i ≤ M)
    (hold_end : ∀ i∈old, b i ≤ L) (hnew : ∀ i∈s, i∉old → L ≤ a i)
    (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hD : ∀ i∈old, D i∈P ∧ w i*(B.card:ℝ) ≤ (D i).card ∧
      ((D i).card:ℝ) ≤ (1+ε)*w i*B.card)
    (hcover : ∀ x : ℝ, (B.card:ℝ) ≤ x → x ≤ M →
      ∃ C∈P, x ≤ (C.card:ℝ) ∧ (C.card:ℝ) ≤ (1+ε)*x)
    (hprefix : ∀ C∈P, ∀ E∈P, ∀ z u, u ≤ M →
      |(prefixCount M C E z u:ℝ)-(u:ℝ)/M*actualMean M C E| ≤ η*actualMean M C E) :
    ∃ A : Finset ℕ, A ⊆ Finset.range M ∧ assembled M old D a b ⊆ A ∧
      (∀ x<L, x∈A ↔ x∈assembled M old D a b) ∧
      (∀ n<L, sumRep (A:Set ℕ) n = sumRep (assembled M old D a b:Set ℕ) n) ∧
      (∀ x∈A \ assembled M old D a b, L ≤ x) ∧
      (∀ n<2*L, sumRep (A:Set ℕ) n = sumRep (assembled M old D a b:Set ℕ) n+
        2*pairs (assembled M old D a b) (A \ assembled M old D a b) n) ∧
      ∀ n : ℕ,
        |(sumRep (A:Set ℕ) n:ℝ)-actualMean M B B*weightedProfile M s w a b n| ≤
          ((1+2*η)*(1+ε)^2-1)*actualMean M B B*(∑ i∈s, w i)^2 := by
  have hchoose : ∀ i, ∃ E : Finset (ZMod M), i∈s → E∈P ∧
      w i*(B.card:ℝ) ≤ E.card ∧ (E.card:ℝ) ≤ (1+ε)*w i*B.card := by
    intro i
    by_cases hi : i∈s
    · have hlow : (B.card:ℝ) ≤ w i*B.card := le_mul_of_one_le_left (by positivity) (hw i hi)
      obtain ⟨E,hEP,hl,hu⟩ := hcover (w i*B.card) hlow (hfit i hi)
      exact ⟨E,fun _ ↦ ⟨hEP,hl,by nlinarith only [hu]⟩⟩
    · exact ⟨B,fun hh ↦ False.elim (hi hh)⟩
  choose E hE using hchoose
  let C : ι → Finset (ZMod M) := fun i ↦ if i∈old then D i else E i
  have hCold : ∀ i∈old, C i=D i := by intro i hi; simp [C,hi]
  have hC : ∀ i∈s, C i∈P ∧ w i*(B.card:ℝ) ≤ (C i).card ∧
      ((C i).card:ℝ) ≤ (1+ε)*w i*B.card := by
    intro i hi
    by_cases hio : i∈old
    · simpa only [C,if_pos hio] using hD i hio
    · simpa only [C,if_neg hio] using hE i hi
  let A := assembled M s C a b
  have hAs : A ⊆ Finset.range M := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_range.mpr ((mem_slice M (C i) (a i) (b i) x).mp hx).1
  have hsub : assembled M old D a b ⊆ A := by
    rw [←assembled_agrees_on_indices M old C D a b hCold]
    exact assembled_mono_indices M old s hold C a b
  have hagree := assembled_prefix M s old hold C D a b L hCold hnew
  have hnewF : ∀ x∈A \ assembled M old D a b, L ≤ x := by
    intro x hx
    have hxA := (Finset.mem_sdiff.mp hx).1
    have hxold := (Finset.mem_sdiff.mp hx).2
    by_contra hh
    exact hxold ((hagree x (by omega)).mp hxA)
  have hOldbounds : ∀ x∈assembled M old D a b, x<L := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    exact (((mem_slice M (D i) (a i) (b i) x).mp hx).2.2.1).trans_le (hold_end i hi)
  refine ⟨A,hAs,hsub,hagree,?_,hnewF,?_,?_⟩
  · intro n hn
    apply Erdos66Compactness.sumRep_congr_below
    intro x hx
    exact hagree x (by omega)
  · intro n hn
    have hh := Erdos66TransitionLinear.transition_exact (assembled M old D a b)
      (A \ assembled M old D a b) L n hOldbounds hnewF hn
    rwa [Finset.union_sdiff_of_subset hsub] at hh
  · intro n
    exact quantized_assembly_error M s B C w a b hdisj hb
      (fun i hi ↦ by linarith [hw i hi]) (1+ε) η (by linarith) hη
      (fun i hi ↦ (hC i hi).2) (fun i hi j hj ↦ hprefix _ (hC i hi).1 _ (hC j hj).1) n

end Erdos66PalettePrefixExtension
