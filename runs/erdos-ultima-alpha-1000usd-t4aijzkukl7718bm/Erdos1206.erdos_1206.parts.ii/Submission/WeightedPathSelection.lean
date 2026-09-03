import FormalConjecturesUtil

/-! Weighted selection of separated bins on the natural-number path. This
preserves a fixed proportion of prefix weight after a bounded index expansion. -/
namespace Erdos1206.WeightedPathSelection
open Finset Filter
open scoped Classical Topology

def near (R k : ℕ) : Finset ℕ := Icc (k-R) (k+R)
def Separated (R : ℕ) (I : Set ℕ) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≤ j+R → j ≤ i+R → i=j

lemma mem_near (R k j : ℕ) : j ∈ near R k ↔ k ≤ j+R ∧ j ≤ k+R := by
  simp only [near,mem_Icc]
  omega
lemma self_mem_near (R k : ℕ) : k ∈ near R k := by rw [mem_near]; omega
lemma near_symm (R k j : ℕ) : j ∈ near R k ↔ k ∈ near R j := by
  simp only [mem_near,and_comm]
lemma card_near_le (R k : ℕ) : (near R k).card ≤ 2*R+1 := by
  simp only [near,Nat.card_Icc]
  omega

lemma insert_sdiff_separated {R k : ℕ} {F : Finset ℕ}
    (hF : Separated R (F : Set ℕ)) :
    Separated R ((insert k (F \ near R k) : Finset ℕ) : Set ℕ) := by
  intro i hi j hj hij hji
  rcases mem_insert.mp hi with rfl | hi <;> rcases mem_insert.mp hj with rfl | hj
  · rfl
  · exact False.elim ((mem_sdiff.mp hj).2 ((mem_near _ _ _).mpr ⟨hij,hji⟩))
  · exact False.elim ((mem_sdiff.mp hi).2 ((mem_near _ _ _).mpr ⟨hji,hij⟩))
  · exact hF i (mem_sdiff.mp hi).1 j (mem_sdiff.mp hj).1 hij hji

lemma finite_selection (R N : ℕ) (w : ℕ → ℕ) :
    ∃ F : Finset ℕ, F ⊆ range N ∧ Separated R (F : Set ℕ) ∧
      ∀ k < N, w k ≤ ∑ j ∈ near R k, if j ∈ F then w j else 0 := by
  let C : Finset (Finset ℕ) := (range N).powerset.filter (fun (F : Finset ℕ) => Separated R (F : Set ℕ))
  have hC : C.Nonempty := by
    refine ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),?_⟩⟩
    intro i hi
    simp at hi
  obtain ⟨F,hFC,hmax⟩ := exists_max_image C (fun F => ∑ j ∈ F, w j) hC
  have hF := mem_filter.mp hFC
  have hsub : F ⊆ range N := mem_powerset.mp hF.1
  refine ⟨F,hsub,hF.2,?_⟩
  intro k hk
  let G := insert k (F \ near R k)
  have hG : G ∈ C := by
    apply mem_filter.mpr
    constructor
    · apply mem_powerset.mpr
      exact insert_subset (mem_range.mpr hk) (sdiff_subset.trans hsub)
    · exact insert_sdiff_separated hF.2
  have hh := hmax G hG
  have hknot : k ∉ F \ near R k := fun h => (mem_sdiff.mp h).2 (self_mem_near R k)
  rw [show G=insert k (F \ near R k) from rfl,sum_insert hknot] at hh
  have he := sum_inter_add_sum_diff F (near R k) w
  have hw : w k ≤ ∑ j ∈ F ∩ near R k, w j := by omega
  have heq : (∑ j ∈ F ∩ near R k, w j) =
      ∑ j ∈ near R k, if j ∈ F then w j else 0 := by
    rw [← sum_filter]
    congr 1
    ext j
    simp [and_comm]
  exact heq ▸ hw

/-- A locally maximal weighted independent set exists, even when total weight
is infinite. The domination inequalities involve only finite neighborhoods. -/
theorem exists_selection (R : ℕ) (w : ℕ → ℕ) :
    ∃ I : Set ℕ, Separated R I ∧
      ∀ k, w k ≤ ∑ j ∈ near R k, if j ∈ I then w j else 0 := by
  choose F hsub hsep hdom using fun N => finite_selection R N w
  let x : ℕ → ℕ → Bool := fun N k => decide (k ∈ F N)
  obtain ⟨f,φ,hφ,hf⟩ := SeqCompactSpace.tendsto_subseq x
  let I : Set ℕ := {k | f k=true}
  have hev (k : ℕ) : ∀ᶠ n in atTop, (k ∈ F (φ n) ↔ k ∈ I) := by
    have hn := tendsto_pi_nhds.mp hf k
    have heq := hn.eventually (isOpen_discrete {f k} |>.mem_nhds (by simp))
    filter_upwards [heq] with n hn
    change decide (k ∈ F (φ n))=f k at hn
    change (k ∈ F (φ n) ↔ f k=true)
    rw [←hn]
    simp
  refine ⟨I,?_,?_⟩
  · intro i hi j hj hij hji
    obtain ⟨n,hn,hjn⟩ := ((hev i).and (hev j)).exists
    exact hsep (φ n) i (hn.mpr hi) j (hjn.mpr hj) hij hji
  · intro k
    have hh : ∀ᶠ n in atTop, ∀ j ∈ near R k, (j ∈ F (φ n) ↔ j ∈ I) :=
      (Finset.eventually_all _).mpr (fun j _ => hev j)
    have hb : ∀ᶠ n in atTop, k < φ n := hφ.tendsto_atTop.eventually (eventually_gt_atTop k)
    obtain ⟨n,hn,hkn⟩ := (hh.and hb).exists
    calc
      w k ≤ ∑ j ∈ near R k, if j ∈ F (φ n) then w j else 0 := hdom (φ n) k hkn
      _ = _ := by
        apply sum_congr rfl
        intro j hj
        by_cases h : j ∈ I
        · have h' := (hn j hj).mpr h
          simp only [h,h',if_true]
        · have h' : j ∉ F (φ n) := fun he => h ((hn j hj).mp he)
          simp only [h,h',if_false]

lemma prefix_domination {R : ℕ} {w : ℕ → ℕ} {I : Set ℕ}
    (hdom : ∀ k, w k ≤ ∑ j ∈ near R k, if j ∈ I then w j else 0) (K : ℕ) :
    (∑ k ∈ range (K+1), w k) ≤
      (2*R+1)*∑ j ∈ range (K+R+1), if j ∈ I then w j else 0 := by
  let v : ℕ → ℕ := fun j => if j ∈ I then w j else 0
  have he (k : ℕ) (hk : k ∈ range (K+1)) :
      (∑ j ∈ near R k, v j) =
      ∑ j ∈ range (K+R+1), if j ∈ near R k then v j else 0 := by
    rw [←sum_filter (fun j => j ∈ near R k) v]
    apply congrArg (fun T : Finset ℕ => ∑ j ∈ T, v j)
    ext j
    have hb : j ∈ near R k → j < K+R+1 := by
      intro hj
      have := (mem_near R k j).mp hj
      have := mem_range.mp hk
      omega
    simp only [mem_filter,mem_range]
    exact ⟨fun h => ⟨hb h,h⟩,fun h => h.2⟩
  have hj (j : ℕ) :
      (∑ k ∈ range (K+1), if j ∈ near R k then v j else 0) ≤ (2*R+1)*v j := by
    simp_rw [near_symm R _ j]
    rw [←sum_filter (fun k => k ∈ near R j) (fun _ => v j)]
    calc
      _ ≤ ∑ k ∈ near R j, v j := sum_le_sum_of_subset_of_nonneg
        (fun k hk => (mem_filter.mp hk).2) (by intros; omega)
      _ = (near R j).card*v j := by simp
      _ ≤ _ := Nat.mul_le_mul_right (v j) (card_near_le R j)
  calc
    _ ≤ ∑ k ∈ range (K+1), ∑ j ∈ near R k, v j := sum_le_sum (fun k _ => hdom k)
    _ = ∑ k ∈ range (K+1), ∑ j ∈ range (K+R+1), if j ∈ near R k then v j else 0 :=
      sum_congr rfl he
    _ = ∑ j ∈ range (K+R+1), ∑ k ∈ range (K+1), if j ∈ near R k then v j else 0 := sum_comm
    _ ≤ ∑ j ∈ range (K+R+1), (2*R+1)*v j := sum_le_sum (fun j _ => hj j)
    _ = _ := by rw [mul_sum]

#print axioms exists_selection
#print axioms prefix_domination
end Erdos1206.WeightedPathSelection
