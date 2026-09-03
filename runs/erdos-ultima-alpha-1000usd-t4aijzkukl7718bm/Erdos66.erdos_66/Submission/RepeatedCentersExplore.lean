import Submission.SummableSpikesExplore

/-! Enumerating positive finite multiplicities as one ordered coordinate list.
Block estimates transfer summability to the repeated-center list. -/
namespace Erdos66RepeatedCenters
open Filter Erdos66JointInfiniteRepair Erdos66SummableSpikes Erdos66ClippedRepair
open scoped Classical
set_option maxHeartbeats 1400000

noncomputable def start (r : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, r j
@[simp] lemma start_zero (r : ℕ → ℕ) : start r 0 = 0 := by simp [start]
lemma start_succ (r : ℕ → ℕ) (k : ℕ) : start r (k+1) = start r k + r k := Finset.sum_range_succ _ _
lemma start_strictMono (r : ℕ → ℕ) (hr : ∀ k, 0 < r k) : StrictMono (start r) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [start_succ]
  exact Nat.lt_add_of_pos_right (hr k)
lemma le_start (r : ℕ → ℕ) (hr : ∀ k, 0 < r k) (k : ℕ) : k ≤ start r k := by
  induction k with
  | zero => simp
  | succ k ih => rw [start_succ]; have hh := hr k; omega
lemma block_exists (r : ℕ → ℕ) (hr : ∀ k, 0 < r k) (i : ℕ) : ∃ k, i < start r (k+1) :=
  ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (le_start r hr (i+1))⟩
noncomputable def blockIndex (r : ℕ → ℕ) (hr : ∀ k, 0 < r k) (i : ℕ) : ℕ :=
  Nat.find (block_exists r hr i)
lemma block_bounds (r : ℕ → ℕ) (hr : ∀ k, 0 < r k) (i : ℕ) :
    start r (blockIndex r hr i) ≤ i ∧ i < start r (blockIndex r hr i + 1) := by
  have hu := Nat.find_spec (block_exists r hr i)
  refine ⟨?_,hu⟩
  cases he : blockIndex r hr i with
  | zero => simp
  | succ k =>
    have hk : k < Nat.find (block_exists r hr i) := by change k < blockIndex r hr i; omega
    have hh := Nat.find_min (block_exists r hr i) hk
    omega
lemma blockIndex_eq_of_bounds (r : ℕ → ℕ) (hr : ∀ k, 0 < r k) (i k : ℕ)
    (hl : start r k ≤ i) (hu : i < start r (k+1)) : blockIndex r hr i = k := by
  have hb := block_bounds r hr i
  have hm := (start_strictMono r hr).monotone
  apply Nat.le_antisymm
  · exact Nat.find_min' (block_exists r hr i) hu
  · by_contra hn
    have hle : blockIndex r hr i + 1 ≤ k := by omega
    have hh := hm hle
    omega

noncomputable def position (r : ℕ → ℕ) (p : Sigma (fun k ↦ Fin (r k))) : ℕ := start r p.1 + p.2.val
lemma position_bounds (r : ℕ → ℕ) (p : Sigma (fun k ↦ Fin (r k))) :
    start r p.1 ≤ position r p ∧ position r p < start r (p.1+1) := by
  have hh := p.2.isLt
  rw [start_succ]
  dsimp [position]
  omega
lemma index_position (r : ℕ → ℕ) (hr : ∀ k, 0 < r k) (p : Sigma (fun k ↦ Fin (r k))) :
    blockIndex r hr (position r p) = p.1 :=
  blockIndex_eq_of_bounds r hr _ _ (position_bounds r p).1 (position_bounds r p).2
lemma position_bijective (r : ℕ → ℕ) (hr : ∀ k, 0 < r k) : Function.Bijective (position r) := by
  constructor
  · rintro ⟨k,i⟩ ⟨l,j⟩ he
    have hh := congrArg (blockIndex r hr) he
    rw [index_position,index_position] at hh
    dsimp only at hh
    subst l
    have hij : i = j := Fin.ext (by dsimp [position] at he; omega)
    subst j
    rfl
  · intro i
    let k := blockIndex r hr i
    have hb := block_bounds r hr i
    have hi : i-start r k < r k := by
      rw [start_succ] at hb
      dsimp only [k]
      omega
    refine ⟨⟨k,⟨i-start r k,hi⟩⟩,?_⟩
    dsimp [position,k]
    omega
noncomputable def blockEquiv (r : ℕ → ℕ) (hr : ∀ k, 0 < r k) :
    Sigma (fun k ↦ Fin (r k)) ≃ ℕ := Equiv.ofBijective (position r) (position_bijective r hr)

noncomputable def repeated (n r : ℕ → ℕ) (hr : ∀ k, 0 < r k) (i : ℕ) : ℕ := n (blockIndex r hr i)
lemma repeat_position (n r : ℕ → ℕ) (hr : ∀ k, 0 < r k) (p : Sigma (fun k ↦ Fin (r k))) :
    repeated n r hr (position r p) = n p.1 := by rw [repeated,index_position]

noncomputable def multiplicity (n r : ℕ → ℕ) (z : ℕ) : ℕ :=
  if h : z ∈ Set.range n then r (Classical.choose h) else 0
lemma multiplicity_at (n r : ℕ → ℕ) (hn : Function.Injective n) (k : ℕ) : multiplicity n r (n k) = r k := by
  have h : n k ∈ Set.range n := ⟨k,rfl⟩
  rw [multiplicity,dif_pos h]
  have he := Classical.choose_spec h
  rw [hn he]
lemma multiplicity_off (n r : ℕ → ℕ) (z : ℕ) (hz : z ∉ Set.range n) : multiplicity n r z = 0 := by
  simp [multiplicity,hz]

lemma centerCount_repeat_at (n r : ℕ → ℕ) (hn : Function.Injective n) (hr : ∀ k, 0 < r k)
    (k L : ℕ) (hL : start r (k+1) ≤ L) : centerCount (repeated n r hr) L (n k) = r k := by
  rw [centerCount]
  symm
  calc
    r k = (Finset.univ : Finset (Fin (r k))).card := by simp
    _ = _ := by
      apply Finset.card_bij (fun j _ ↦ (⟨position r ⟨k,j⟩,
        (position_bounds r ⟨k,j⟩).2.trans_le hL⟩ : Fin L))
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, repeat_position n r hr ⟨k,j⟩⟩
      · intro i hi j hj he
        have hh := congrArg (fun x : Fin L ↦ x.val) he
        apply Fin.ext
        dsimp [position] at hh
        omega
      · intro i hi
        have he := (Finset.mem_filter.mp hi).2
        have hk : blockIndex r hr i.val = k := hn he
        have hb := block_bounds r hr i.val
        rw [hk,start_succ] at hb
        have hval : i.val-start r k < r k := by omega
        refine ⟨⟨i.val-start r k,hval⟩,Finset.mem_univ _,?_⟩
        apply Fin.ext
        dsimp [position]
        omega

lemma centerCount_repeat_stabilizes (n r : ℕ → ℕ) (hn : Function.Injective n) (hr : ∀ k, 0 < r k) (z : ℕ) :
    ∃ J : ℕ, ∀ L ≥ J, centerCount (repeated n r hr) L z = multiplicity n r z := by
  by_cases hz : z ∈ Set.range n
  · obtain ⟨k,rfl⟩ := hz
    refine ⟨start r (k+1),fun L hL ↦ ?_⟩
    rw [multiplicity_at n r hn k]
    exact centerCount_repeat_at n r hn hr k L hL
  · refine ⟨0,fun L hL ↦ ?_⟩
    rw [multiplicity_off n r z hz,centerCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    intro i hi he
    exact hz ⟨blockIndex r hr i.val,he⟩

lemma sigma_summable_of_weighted (r : ℕ → ℕ) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hs : Summable (fun k ↦ (r k : ℝ)*g k)) :
    Summable (fun p : Sigma (fun k ↦ Fin (r k)) ↦ g p.1) := by
  apply (summable_sigma_of_nonneg (fun p ↦ hg p.1)).mpr
  refine ⟨fun k ↦ (hasSum_fintype _).summable,?_⟩
  simpa only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hs

/-- A bound for an entire block can be multiplied by its finite multiplicity
before checking summability over blocks. -/
lemma summable_of_block_bound (r : ℕ → ℕ) (hr : ∀ k, 0 < r k)
    (f g : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ k, 0 ≤ g k)
    (hbound : ∀ p : Sigma (fun k ↦ Fin (r k)), f (position r p) ≤ g p.1)
    (hs : Summable (fun k ↦ (r k : ℝ)*g k)) : Summable f := by
  apply (blockEquiv r hr).summable_iff.mp
  exact Summable.of_nonneg_of_le (fun p ↦ hf (position r p)) hbound
    (sigma_summable_of_weighted r g hg hs)

theorem repeated_summability (n r : ℕ → ℕ) (hr : ∀ k, 0 < r k)
    (hc : Summable (fun k ↦ (r k : ℝ)*(start r (k+1) : ℝ)^4 / ((n k : ℝ)+1)))
    (hf : Summable (fun k ↦ (r k : ℝ)*Real.sqrt (logScale (n k)) / Real.sqrt ((n k : ℝ)+1)))
    (hq : Summable (fun k ↦ (r k : ℝ) / Real.sqrt ((n k : ℝ)+1))) :
    Summable (fun i : ℕ ↦ ((i : ℝ)+1)^4 / ((repeated n r hr i : ℝ)+1)) ∧
    Summable (fun i : ℕ ↦ Real.sqrt (logScale (repeated n r hr i)) / Real.sqrt ((repeated n r hr i : ℝ)+1)) ∧
    Summable (fun i : ℕ ↦ 1 / Real.sqrt ((repeated n r hr i : ℝ)+1)) := by
  constructor
  · refine summable_of_block_bound r hr _
      (fun k ↦ (start r (k+1) : ℝ)^4 / ((n k : ℝ)+1)) (fun i ↦ by positivity) (fun k ↦ by positivity) ?_ ?_
    · intro p
      rw [repeat_position]
      have hp : (position r p : ℝ)+1 ≤ start r (p.1+1) := by
        exact_mod_cast Nat.succ_le_of_lt (position_bounds r p).2
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp 4) (by positivity)
    · simpa only [mul_div_assoc] using hc
  constructor
  · refine summable_of_block_bound r hr _
      (fun k ↦ Real.sqrt (logScale (n k)) / Real.sqrt ((n k : ℝ)+1))
      (fun i ↦ by positivity) (fun k ↦ by positivity) ?_ ?_
    · intro p; rw [repeat_position]
    · simpa only [mul_div_assoc] using hf
  · refine summable_of_block_bound r hr _
      (fun k ↦ 1 / Real.sqrt ((n k : ℝ)+1)) (fun i ↦ by positivity) (fun k ↦ by positivity) ?_ ?_
    · intro p; rw [repeat_position]
    · simpa only [mul_one_div] using hq

end Erdos66RepeatedCenters
