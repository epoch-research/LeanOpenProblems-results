import Submission.CenteredCumulativeRoundingExplore

/-! Rounding an exactly linear cumulative segment concentrates many paired
ranks at at most two adjacent sum targets. -/
namespace Erdos66LinearRoundingPeak
open AdditiveCombinatorics Erdos66Generating Erdos66Counting
  Erdos66CenteredCumulativeRounding
open scoped Classical
set_option maxHeartbeats 2600000

lemma reflected_rank_sum {K : ℕ} (j : Fin K) : j.val+j.rev.val=K-1 := by
  simp only [Fin.val_rev]
  omega

/-- Paired ranks whose sums occupy an interval of length two force a peak
of at least half the number of ranks. -/
theorem paired_ranks_peak (A : Set ℕ) (K : ℕ) (hK : 0<K) (f : Fin K → ℕ)
    (hf : Function.Injective f) (hA : ∀ j, f j∈A) (S : ℝ)
    (hS : ∀ j, S-2≤ (f j+f j.rev:ℕ) ∧ (f j+f j.rev:ℕ)<S) :
    ∃ j : Fin K, K≤ 2*sumRep A (f j+f j.rev) := by
  let σ : Fin K → ℕ := fun j ↦ f j+f j.rev
  let T := Finset.univ.image σ
  have hT : T.Nonempty := ⟨σ ⟨0,hK⟩,Finset.mem_image.mpr ⟨⟨0,hK⟩,Finset.mem_univ _,rfl⟩⟩
  let t := T.min' hT
  have ht : t∈T := Finset.min'_mem T hT
  have hsmall : T.card≤ 2 := by
    apply (Finset.card_le_card (t:={t,t+1}) ?_).trans Finset.card_le_two
    intro n hn
    have hlow : t≤ n := Finset.min'_le T n hn
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hn
    obtain ⟨j,hj,hje⟩ := Finset.mem_image.mp ht
    have hlt : (n:ℝ)<(t:ℝ)+2 := by
      have h₁ := (hS i).2
      have h₂ := (hS j).1
      change σ i=n at he
      change σ j=t at hje
      change (σ i:ℝ)<S at h₁
      change S-2≤ (σ j:ℝ) at h₂
      rw [he] at h₁
      rw [hje] at h₂
      linarith
    have hlt' : n<t+2 := by exact_mod_cast hlt
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have hfiber (n : ℕ) : ((Finset.univ : Finset (Fin K)).filter (fun j ↦ σ j=n)).card≤ sumRep A n := by
    rw [sumRep_def]
    apply Finset.card_le_card_of_injOn (fun j : Fin K ↦ (f j,f j.rev))
    · intro j hj
      change j∈(Finset.univ.filter (fun j : Fin K ↦ σ j=n)) at hj
      have hjn := (Finset.mem_filter.mp hj).2
      change (f j,f j.rev)∈(Finset.antidiagonal n).filter (fun ab ↦ ab.1∈A ∧ ab.2∈A)
      exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (show f j+f j.rev=n from hjn),hA j,hA j.rev⟩
    · intro i hi j hj he
      exact hf (congrArg Prod.fst he)
  have hmass : K≤ ∑ n∈T, sumRep A n := by
    have he := Finset.card_eq_sum_card_image σ (Finset.univ : Finset (Fin K))
    simpa only [Finset.card_univ,Fintype.card_fin] using
      he.trans_le (Finset.sum_le_sum (fun n hn ↦ hfiber n))
  by_contra hh
  push_neg at hh
  have hstrict (n : ℕ) (hn : n∈T) : 2*sumRep A n<K := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
    exact hh j
  have hs := Finset.sum_lt_sum_of_nonempty hT hstrict
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hs
  have hcard := Nat.mul_le_mul_right K hsmall
  norm_cast at hs
  nlinarith

/-- Location of the j-th crossing of an affine cumulative function. -/
noncomputable def crossing (v θ : ℝ) (j : ℕ) : ℕ :=
  ⌈((j:ℝ)+1-θ)/v⌉₊-1

lemma crossing_bounds (v θ : ℝ) (hv : 0<v) (hθ : θ<1) (j : ℕ) :
    ((j:ℝ)+1-θ)/v-1≤ (crossing v θ j:ℝ) ∧
      (crossing v θ j:ℝ)<((j:ℝ)+1-θ)/v := by
  have hx : 0<((j:ℝ)+1-θ)/v := by
    apply div_pos _ hv
    have hj : (0:ℝ)≤ j := by positivity
    linarith
  have hc : 0<⌈((j:ℝ)+1-θ)/v⌉₊ := Nat.ceil_pos.mpr hx
  have hlo := Nat.le_ceil (((j:ℝ)+1-θ)/v)
  have hhi := Nat.ceil_lt_add_one hx.le
  unfold crossing
  rw [Nat.cast_sub (by omega),Nat.cast_one]
  constructor <;> linarith

lemma crossing_inside (v θ : ℝ) (hv : 0<v) (hθ0 : 0≤ θ) (hθ1 : θ<1)
    (W K : ℕ) (hK : (K:ℝ)≤ v*W) (j : Fin K) : crossing v θ j.val<W := by
  have hb := (crossing_bounds v θ hv hθ1 j.val).2
  have hj : (j.val:ℝ)+1≤ K := by exact_mod_cast j.isLt
  have hx : ((j.val:ℝ)+1-θ)/v≤ W := by
    apply (div_le_iff₀ hv).mpr
    nlinarith
  exact_mod_cast hb.trans_le hx

lemma crossing_floor (α v : ℝ) (hv : 0<v) (hv1 : v≤ 1) (j : ℕ) :
    ⌊α+v*(crossing v (Int.fract α) j:ℝ)⌋=⌊α⌋+j ∧
      ⌊α+v*((crossing v (Int.fract α) j:ℝ)+1)⌋=⌊α⌋+j+1 := by
  have hθ : Int.fract α<1 := Int.fract_lt_one α
  have hb := crossing_bounds v (Int.fract α) hv hθ j
  have hlow := mul_le_mul_of_nonneg_left hb.1 hv.le
  have hhi := mul_lt_mul_of_pos_left hb.2 hv
  have he : v*(((j:ℝ)+1-Int.fract α)/v)=(j:ℝ)+1-Int.fract α := by field_simp
  have hf : α=(⌊α⌋:ℝ)+Int.fract α := (Int.floor_add_fract α).symm
  have hlow' : (j:ℝ)+1-Int.fract α-v≤ v*(crossing v (Int.fract α) j:ℝ) := by
    nlinarith [show v*(((j:ℝ)+1-Int.fract α)/v-1)=
      v*(((j:ℝ)+1-Int.fract α)/v)-v by ring]
  rw [he] at hhi
  constructor
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith

lemma crossing_injective (α v : ℝ) (hv : 0<v) (hv1 : v≤ 1) :
    Function.Injective (crossing v (Int.fract α)) := by
  intro i j hij
  have hi := (crossing_floor α v hv hv1 i).1
  have hj := (crossing_floor α v hv hv1 j).1
  rw [hij, hj] at hi
  omega

/-- An affine segment with K complete mass crossings produces a large
representation at a target supported entirely by that segment. -/
theorem linear_segment_peak (F : ℕ → ℝ) (L W K : ℕ) (α v : ℝ)
    (hv : 0<v) (hv1 : v≤ 1) (hK : 0<K) (hKW : (K:ℝ)≤ v*W)
    (hline : ∀ j≤ W, F (L+j)=α+v*j) :
    ∃ n : ℕ, 2*L≤ n ∧ n<2*(L+W) ∧ K≤ 2*sumRep (rounded F) n := by
  let f : Fin K → ℕ := fun j ↦ L+crossing v (Int.fract α) j.val
  have hinside (j : Fin K) : crossing v (Int.fract α) j.val<W :=
    crossing_inside v (Int.fract α) hv (Int.fract_nonneg α) (Int.fract_lt_one α) W K hKW j
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply crossing_injective α v hv hv1
    dsimp only [f] at hij
    omega
  have hmem (j : Fin K) : f j∈rounded F := by
    change ⌊F (f j+1)⌋-⌊F (f j)⌋=1
    have he : f j+1=L+(crossing v (Int.fract α) j.val+1) := by dsimp [f]; omega
    rw [he,hline _ (by have := hinside j; omega)]
    change ⌊α+v*↑(crossing v (Int.fract α) j.val+1)⌋-
      ⌊F (L+crossing v (Int.fract α) j.val)⌋=1
    rw [hline _ (hinside j).le]
    push_cast
    rw [(crossing_floor α v hv hv1 j.val).1,(crossing_floor α v hv hv1 j.val).2]
    omega
  let S : ℝ := 2*L+((K:ℝ)+1-2*Int.fract α)/v
  have hS (j : Fin K) : S-2≤ (f j+f j.rev:ℕ) ∧ (f j+f j.rev:ℕ)<S := by
    have hi := crossing_bounds v (Int.fract α) hv (Int.fract_lt_one α) j.val
    have hj := crossing_bounds v (Int.fract α) hv (Int.fract_lt_one α) j.rev.val
    have hr : (j.val:ℝ)+(j.rev.val:ℝ)=(K:ℝ)-1 := by
      have hh := reflected_rank_sum j
      exact_mod_cast (show (j.val:ℤ)+(j.rev.val:ℤ)=(K:ℤ)-1 by omega)
    have he : ((j.val:ℝ)+1-Int.fract α)/v+((j.rev.val:ℝ)+1-Int.fract α)/v=
        ((K:ℝ)+1-2*Int.fract α)/v := by rw [←add_div]; congr 1; linarith
    simp only [Fin.val_rev] at hi hj he
    dsimp [S,f]
    push_cast
    constructor <;> linarith
  obtain ⟨j,hj⟩ := paired_ranks_peak (rounded F) K hK f hf hmem S hS
  refine ⟨f j+f j.rev,?_,?_,hj⟩
  · dsimp [f]; omega
  · have h₁ := hinside j
    have h₂ := hinside j.rev
    simp only [Fin.val_rev] at h₂
    dsimp [f]
    omega

end Erdos66LinearRoundingPeak
