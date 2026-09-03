import Submission.LogarithmicPrefixSystemExplore

/-! One fixed list of palette members simultaneously realizes every spatial
arrangement of a fixed list of heights. No new choices depend on the intervals. -/
namespace Erdos66UniversalHeightPalette
open AdditiveCombinatorics Erdos66LogarithmicPrefixSystem Erdos66IntegerPaletteAssembly
  Erdos66IntegerPaletteQuantization
open scoped Classical
set_option maxHeartbeats 2400000

theorem exists_universal_height_realizer {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i∈s, 1 ≤ w i) (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) (N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ 1<M ∧ ∃ hM : NeZero M,
      ∃ C : ι → Finset (ZMod M), ∀ a b : ι → ℕ,
        (∀ i∈s, b i ≤ M) →
        (∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) →
        ∀ n : ℕ, |(sumRep (assembled M s C a b:Set ℕ) n:ℝ)/Real.log M-
          c*weightedProfile M s w a b n| ≤ δ := by
  obtain ⟨t,ht,ht1,hsys⟩ := exists_logarithmic_prefix_extension_system s w hw c δ hc hδ
  obtain ⟨M,hMN,hM1,hM,B,P,hBpos,hBmem,hfit,hcover,hext⟩ := hsys N₀
  letI := hM
  have hchoose : ∀ i, ∃ D : Finset (ZMod M), i∈s → D∈P ∧
      w i*(B.card:ℝ) ≤ D.card ∧ (D.card:ℝ) ≤ (1+t)*w i*B.card := by
    intro i
    by_cases hi : i∈s
    · have hlow : (B.card:ℝ) ≤ w i*B.card := le_mul_of_one_le_left (by positivity) (hw i hi)
      obtain ⟨D,hDP,hl,hu⟩ := hcover (w i*B.card) hlow (hfit i hi)
      exact ⟨D,fun _ ↦ ⟨hDP,hl,by nlinarith only [hu]⟩⟩
    · exact ⟨B,fun hh ↦ False.elim (hi hh)⟩
  choose C hC using hchoose
  refine ⟨M,hMN,hM1,hM,C,fun a b hb hdisj ↦ ?_⟩
  obtain ⟨A,hAs,hsub,hagree,hreps,hgood⟩ := hext s (Finset.Subset.refl _) C a b M
    hdisj hb hb (fun i hi hn ↦ False.elim (hn hi)) hC
  have he : A=assembled M s C a b := by
    apply Finset.Subset.antisymm _ hsub
    intro x hx
    exact (hagree x (Finset.mem_range.mp (hAs hx))).mp hx
  rwa [he] at hgood

end Erdos66UniversalHeightPalette
