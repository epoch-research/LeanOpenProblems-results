import Submission.OrderedPipageGeometryExplore

/-! Prefix floor/ceiling bounds survive rounding the first two fractional
coordinates. This is a finite dependent-rounding invariant. -/
namespace Erdos66OrderedPipagePrefix
open Erdos66OrderedPipageGeometry
open scoped Classical
set_option maxHeartbeats 1800000

variable {N : ℕ}
noncomputable def pref (x : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ i∈Finset.univ.filter (fun i : Fin N ↦ i.val<k), x i
noncomputable def fractional (x : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ 0<x i ∧ x i<1)
def Brackets (p x : Fin N → ℝ) : Prop :=
  ∀ k, (⌊pref p k⌋ : ℝ)≤pref x k ∧ pref x k≤(⌈pref p k⌉ : ℝ)

lemma mem_fractional (x : Fin N → ℝ) (i : Fin N) :
    i∈fractional x ↔ 0<x i ∧ x i<1 := by simp [fractional]

lemma binary_of_not_fractional (x : Fin N → ℝ) (hx : ∀ i, 0≤x i ∧ x i≤1)
    (i : Fin N) (hi : i∉fractional x) : x i=0 ∨ x i=1 := by
  rw [mem_fractional] at hi
  by_cases h : x i=0
  · exact Or.inl h
  · right
    have hh := hx i
    have hp : 0<x i := lt_of_le_of_ne hh.1 (Ne.symm h)
    have hge : 1≤x i := not_lt.mp (fun hlt ↦ hi ⟨hp,hlt⟩)
    exact le_antisymm hh.2 hge

lemma Brackets.refl (p : Fin N → ℝ) : Brackets p p :=
  fun k ↦ ⟨Int.floor_le _,Int.le_ceil _⟩

lemma Brackets.trans {p x y : Fin N → ℝ} (hpx : Brackets p x) (hxy : Brackets x y) :
    Brackets p y := by
  intro k
  have hlo := Int.floor_mono (hpx k).1
  have hhi := Int.ceil_mono (hpx k).2
  rw [Int.floor_intCast] at hlo
  rw [Int.ceil_intCast] at hhi
  have hl : (⌊pref p k⌋ : ℝ)≤(⌊pref x k⌋ : ℝ) := by exact_mod_cast hlo
  have hu : (⌈pref x k⌉ : ℝ)≤(⌈pref p k⌉ : ℝ) := by exact_mod_cast hhi
  exact ⟨hl.trans (hxy k).1,(hxy k).2.trans hu⟩

lemma sum_binary {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i∈S, x i=0 ∨ x i=1) : ∃ m : ℕ, (∑ i∈S, x i)=(m:ℝ) := by
  refine ⟨(S.filter (fun i ↦ x i=1)).card,?_⟩
  rw [Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hx i hi with hh | hh <;> simp [hh]

lemma bracket_single_fraction (S : Finset (Fin N)) (x y : Fin N → ℝ)
    (i : Fin N) (hi : i∈S) (hxi : 0<x i ∧ x i<1) (hyi : 0≤y i ∧ y i≤1)
    (hother : ∀ j∈S, j≠i → (x j=0 ∨ x j=1) ∧ y j=x j) :
    (⌊∑ j∈S, x j⌋ : ℝ)≤∑ j∈S, y j ∧ (∑ j∈S, y j)≤(⌈∑ j∈S, x j⌉ : ℝ) := by
  obtain ⟨m,hm⟩ := sum_binary (S.erase i) x (fun j hj ↦
    (hother j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1).1)
  have hy : (∑ j∈S.erase i, y j)=(m:ℝ) := by
    rw [←hm]
    exact Finset.sum_congr rfl (fun j hj ↦
      (hother j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1).2)
  have hsx : (∑ j∈S, x j)=(m:ℝ)+x i := by rw [←Finset.sum_erase_add S x hi,hm]
  have hsy : (∑ j∈S, y j)=(m:ℝ)+y i := by rw [←Finset.sum_erase_add S y hi,hy]
  have hfloor : ⌊(m:ℝ)+x i⌋=(m:ℤ) := Int.floor_eq_iff.mpr (by push_cast; constructor <;> linarith)
  have hceil : ⌈(m:ℝ)+x i⌉=(m:ℤ)+1 := Int.ceil_eq_iff.mpr (by push_cast; constructor <;> linarith)
  rw [hsx,hsy,hfloor,hceil]
  push_cast
  constructor <;> linarith

lemma first_two_fractional (x : Fin N → ℝ) (h : 1<(fractional x).card) :
    ∃ i j : Fin N, i<j ∧ i∈fractional x ∧ j∈fractional x ∧
      ∀ k∈fractional x, k<j → k=i := by
  have hne : (fractional x).Nonempty := Finset.card_pos.mp (by omega)
  let i := (fractional x).min' hne
  have hi : i∈fractional x := Finset.min'_mem _ _
  obtain ⟨j0,hj0,hj0i⟩ := Finset.exists_mem_ne h i
  have he : ((fractional x).erase i).Nonempty := ⟨j0,Finset.mem_erase.mpr ⟨hj0i,hj0⟩⟩
  let j := ((fractional x).erase i).min' he
  have hj := Finset.min'_mem _ he
  have hji : j≠i := (Finset.mem_erase.mp hj).1
  have hjx : j∈fractional x := (Finset.mem_erase.mp hj).2
  have hij : i<j := lt_of_le_of_ne (Finset.min'_le _ j hjx) (Ne.symm hji)
  refine ⟨i,j,hij,hi,hjx,?_⟩
  intro k hk hkj
  by_contra hki
  have hh : j≤k := Finset.min'_le _ k (Finset.mem_erase.mpr ⟨hki,hk⟩)
  exact (not_le_of_gt hkj) hh

lemma replaceTwo_box (x : Fin N → ℝ) (hx : ∀ k, 0≤x k ∧ x k≤1)
    (i j : Fin N) (a b : ℝ) (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1) :
    ∀ k, 0≤replaceTwo x i j a b k ∧ replaceTwo x i j a b k≤1 := by
  intro k
  dsimp [replaceTwo]
  split_ifs
  · exact ha
  · exact hb
  · exact hx k

lemma pref_replaceTwo (x : Fin N → ℝ) (i j : Fin N) (hij : i≠j) (a b : ℝ) (k : ℕ) :
    pref (replaceTwo x i j a b) k = pref x k+
      (if i.val<k then a-x i else 0)+(if j.val<k then b-x j else 0) := by
  have he (r : Fin N) : replaceTwo x i j a b r =
      x r+(if r=i then a-x i else 0)+(if r=j then b-x j else 0) := by
    by_cases hi : r=i <;> by_cases hj : r=j <;> simp_all [replaceTwo] <;> ring
  simp only [pref,he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_filter,
    Finset.mem_univ,true_and]

lemma brackets_replaceTwo (x : Fin N → ℝ) (hx : ∀ k, 0≤x k ∧ x k≤1)
    (i j : Fin N) (hij : i<j) (hi : i∈fractional x)
    (hfirst : ∀ k∈fractional x, k<j → k=i)
    (a b : ℝ) (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1) (hs : a+b=x i+x j) :
    Brackets x (replaceTwo x i j a b) := by
  intro k
  by_cases hjk : j.val<k
  · have hik : i.val<k := lt_trans hij hjk
    rw [pref_replaceTwo x i j (ne_of_lt hij),if_pos hik,if_pos hjk]
    have he : pref x k+(a-x i)+(b-x j)=pref x k := by linarith
    rw [he]
    exact ⟨Int.floor_le _,Int.le_ceil _⟩
  · by_cases hik : i.val<k
    · apply bracket_single_fraction _ x _ i (by simp [hik]) (mem_fractional x i |>.mp hi)
        (by simpa [replaceTwo] using ha)
      intro r hr hri
      have hrk : r.val<k := (Finset.mem_filter.mp hr).2
      have hrj : r<j := by change r.val<j.val; omega
      have hrf : r∉fractional x := fun hrf ↦ hri (hfirst r hrf hrj)
      exact ⟨binary_of_not_fractional x hx r hrf,by simp [replaceTwo,hri,ne_of_lt hrj]⟩
    · rw [pref_replaceTwo x i j (ne_of_lt hij),if_neg hik,if_neg hjk,add_zero,add_zero]
      exact ⟨Int.floor_le _,Int.le_ceil _⟩

lemma fractional_replaceTwo_subset (x : Fin N → ℝ) (i j : Fin N)
    (hi : i∈fractional x) (hj : j∈fractional x) (a b : ℝ) :
    fractional (replaceTwo x i j a b) ⊆ fractional x := by
  intro k hk
  by_cases hki : k=i
  · simpa only [hki] using hi
  by_cases hkj : k=j
  · simpa only [hkj] using hj
  simpa only [mem_fractional,replaceTwo,if_neg hki,if_neg hkj] using hk

lemma fractional_replaceTwo_card_lt (x : Fin N → ℝ) (i j : Fin N) (hij : i≠j)
    (hi : i∈fractional x) (hj : j∈fractional x) (a b : ℝ)
    (hend : a=0 ∨ a=1 ∨ b=0 ∨ b=1) :
    (fractional (replaceTwo x i j a b)).card<(fractional x).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fractional_replaceTwo_subset x i j hi hj a b,?_⟩
  intro he
  have hai : i∈fractional (replaceTwo x i j a b) := by rw [he]; exact hi
  have haj : j∈fractional (replaceTwo x i j a b) := by rw [he]; exact hj
  simp only [mem_fractional,replaceTwo,ite_true,if_neg (Ne.symm hij)] at hai haj
  rcases hend with h | h | h | h <;> simp_all

end Erdos66OrderedPipagePrefix
