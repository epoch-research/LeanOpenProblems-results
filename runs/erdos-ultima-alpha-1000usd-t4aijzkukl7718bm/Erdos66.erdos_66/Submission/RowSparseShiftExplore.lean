import Submission.GraphPrefixLimitExplore
import Submission.TranslateExplore

/-! Row bounds pass to subsets and, with a factor of two, to arbitrary
natural translations. -/
namespace Erdos66RowSparseShift
open Erdos66RowSparsePrefix Erdos66WindowPerturbation Erdos66Translate
open scoped Classical

lemma localCount_mono {A B : Set ℕ} (hAB : A⊆B) (t L : ℕ) :
    localCount A t L ≤ localCount B t L := by
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ha,haA⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨ha,hAB haA⟩

lemma rowSparse_mono {A B : Set ℕ} {b H : ℕ} (hAB : A⊆B) (hB : RowSparse B b H) :
    RowSparse A b H := fun q ↦ (localCount_mono hAB _ _).trans (hB q)

lemma shifted_localCount (B : Set ℕ) (M t L : ℕ) :
    localCount (shift B M) t L ≤ localCount B (t-M) L := by
  apply Finset.card_le_card_of_injOn (fun n : ℕ ↦ n-M)
  · intro n hn
    change n∈(Finset.Ico t (t+L)).filter (fun a ↦ a∈shift B M) at hn
    obtain ⟨hnI,hnB⟩ := Finset.mem_filter.mp hn
    obtain ⟨a,ha,rfl⟩ := hnB
    have hh := Finset.mem_Ico.mp hnI
    change (a+M)-M ∈ (Finset.Ico (t-M) (t-M+L)).filter (fun a ↦ a∈B)
    dsimp only at hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
    simpa only [Nat.add_sub_cancel] using ha
  · intro n hn m hm he
    change n∈(Finset.Ico t (t+L)).filter (fun a ↦ a∈shift B M) at hn
    change m∈(Finset.Ico t (t+L)).filter (fun a ↦ a∈shift B M) at hm
    have hnM := shift_ge B M (Finset.mem_filter.mp hn).2
    have hmM := shift_ge B M (Finset.mem_filter.mp hm).2
    change n-M=m-M at he
    omega

lemma rowSparse_shift {B : Set ℕ} {b H : ℕ} (hb : 0<b) (hB : RowSparse B b H) (M : ℕ) :
    RowSparse (shift B M) b (2*H) := fun q ↦
  (shifted_localCount B M (q*b) b).trans (rowSparse_local hb hB le_rfl _)

end Erdos66RowSparseShift
