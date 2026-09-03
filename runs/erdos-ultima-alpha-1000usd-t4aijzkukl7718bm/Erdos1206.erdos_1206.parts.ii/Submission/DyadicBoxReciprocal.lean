import FormalConjecturesUtil

/-! An abstract dyadic-box criterion for reciprocal quadratic-height
summability in two natural parameters. -/
namespace Erdos1206.DyadicBoxReciprocal
open Finset Filter
open scoped Classical Topology
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma sum_union_le (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (S T : Finset α) :
    (∑ x ∈ S ∪ T, f x) ≤ (∑ x ∈ S, f x)+(∑ x ∈ T, f x) := by
  have hh : (∑ x ∈ S ∪ T, f x)+(∑ x ∈ S ∩ T, f x)=
      (∑ x ∈ S, f x)+(∑ x ∈ T, f x) := Finset.sum_union_inter
  have hn := sum_nonneg (fun x (_ : x ∈ S ∩ T) => hf x)
  linarith

lemma sum_biUnion_le (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (S : Finset β) (F : β → Finset α) :
    (∑ x ∈ S.biUnion F, f x) ≤ ∑ j ∈ S, ∑ x ∈ F j, f x := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    rw [biUnion_insert,sum_insert hj]
    exact (sum_union_le f hf (F j) (S.biUnion F)).trans (add_le_add le_rfl ih)

/-- Countable finite covers with summable costs, allowing a finite head. -/
lemma summable_of_finset_cover (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (H : Finset α) (F : ℕ → Finset α)
    (hcover : ∀ x, x ∈ H ∨ ∃ j, x ∈ F j)
    (hs : Summable (fun j => ∑ x ∈ F j, f x)) : Summable f := by
  have hex (x : α) : ∃ j, x ∈ H ∨ x ∈ F j := by
    rcases hcover x with hx | ⟨j,hj⟩
    · exact ⟨0,Or.inl hx⟩
    · exact ⟨j,Or.inr hj⟩
  choose j hj using hex
  apply summable_of_sum_le hf (c := (∑ x ∈ H, f x)+∑' j, ∑ x ∈ F j, f x)
  intro S
  let J := S.image j
  have hsub : S ⊆ H ∪ J.biUnion F := by
    intro x hx
    rcases hj x with hh | hh
    · exact mem_union_left _ hh
    · exact mem_union_right _ (mem_biUnion.mpr ⟨j x,mem_image.mpr ⟨x,hx,rfl⟩,hh⟩)
  calc
    _ ≤ ∑ x ∈ H ∪ J.biUnion F, f x := sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hf x)
    _ ≤ (∑ x ∈ H, f x)+(∑ x ∈ J.biUnion F, f x) := sum_union_le f hf _ _
    _ ≤ (∑ x ∈ H, f x)+(∑ i ∈ J, ∑ x ∈ F i, f x) :=
      add_le_add le_rfl (sum_biUnion_le f hf J F)
    _ ≤ _ := add_le_add le_rfl
      (Summable.sum_le_tsum J (fun i _ => sum_nonneg (fun x _ => hf x)) hs)

def box (N : ℕ) : Finset (ℕ × ℕ) := (range N) ×ˢ (range N)
def height (x : ℕ × ℕ) : ℕ := max x.1 x.2
noncomputable def weight (T : Set (ℕ × ℕ)) (x : ℕ × ℕ) : ℝ :=
  if x ∈ T then 1/(height x:ℝ)^2 else 0
def shell (r : ℕ) : Finset (ℕ × ℕ) := box (2^(r+1)) \ box (2^r)
def band (r s : ℕ) : Finset (ℕ × ℕ) := (Ico r s).biUnion shell

lemma weight_nonneg (T : Set (ℕ × ℕ)) (x : ℕ × ℕ) : 0 ≤ weight T x := by
  dsimp only [weight]
  split_ifs <;> positivity

lemma mem_box (x : ℕ × ℕ) (N : ℕ) : x ∈ box N ↔ height x < N := by
  simp only [box,mem_product,mem_range,height,max_lt_iff]

lemma shell_lower {r : ℕ} {x : ℕ × ℕ} (hx : x ∈ shell r) : 2^r ≤ height x := by
  exact le_of_not_gt (fun h => (mem_sdiff.mp hx).2 ((mem_box x _).mpr h))

lemma shell_upper {r : ℕ} {x : ℕ × ℕ} (hx : x ∈ shell r) : height x < 2^(r+1) :=
  (mem_box x _).mp (mem_sdiff.mp hx).1

lemma shell_cost (T : Set (ℕ × ℕ)) (r : ℕ) {δ : ℝ}
    (hcount : (((box (2^(r+1))).filter (· ∈ T)).card:ℝ) ≤ ((2^(r+1):ℕ):ℝ)^2*δ) :
    (∑ x ∈ shell r, weight T x) ≤ 4*δ := by
  let S := (shell r).filter (· ∈ T)
  have hsum : (∑ x ∈ shell r, weight T x)=∑ x ∈ S, 1/(height x:ℝ)^2 := by
    rw [show S=(shell r).filter (· ∈ T) from rfl,sum_filter]
    rfl
  rw [hsum]
  have hsub : S ⊆ (box (2^(r+1))).filter (· ∈ T) := by
    intro x hx
    obtain ⟨hxS,hxT⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_sdiff.mp hxS).1,hxT⟩
  have hc : (S.card:ℝ) ≤ (((box (2^(r+1))).filter (· ∈ T)).card:ℝ) := by
    exact_mod_cast card_le_card hsub
  have hpow : (0:ℝ) < (2:ℝ)^r := by positivity
  calc
    _ ≤ ∑ _x ∈ S, 1/((2:ℝ)^r)^2 := by
      apply sum_le_sum
      intro x hx
      have hxL : (2:ℝ)^r ≤ (height x:ℝ) := by
        exact_mod_cast shell_lower (mem_filter.mp hx).1
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpow.le hxL 2)
    _ = (S.card:ℝ)*(1/((2:ℝ)^r)^2) := by simp
    _ ≤ (((box (2^(r+1))).filter (· ∈ T)).card:ℝ)*(1/((2:ℝ)^r)^2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (((2^(r+1):ℕ):ℝ)^2*δ)*(1/((2:ℝ)^r)^2) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 4*δ := by
      push_cast
      rw [pow_succ]
      field_simp
      ring

lemma band_cost (T : Set (ℕ × ℕ)) (r s : ℕ) {δ : ℝ}
    (hcount : ∀ t, r ≤ t → t < s →
      (((box (2^(t+1))).filter (· ∈ T)).card:ℝ) ≤ ((2^(t+1):ℕ):ℝ)^2*δ) :
    (∑ x ∈ band r s, weight T x) ≤ 4*((s-r:ℕ):ℝ)*δ := by
  unfold band
  calc
    _ ≤ ∑ t ∈ Ico r s, ∑ x ∈ shell t, weight T x :=
      sum_biUnion_le _ (weight_nonneg T) _ _
    _ ≤ ∑ _t ∈ Ico r s, 4*δ := sum_le_sum (fun t ht =>
      shell_cost T t (hcount t (mem_Ico.mp ht).1 (mem_Ico.mp ht).2))
    _ = _ := by simp only [sum_const,Nat.card_Ico,nsmul_eq_mul]; ring

lemma exists_adjacent {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) {s : ℕ} (hs : r 0 ≤ s) :
    ∃ j, r j ≤ s ∧ s < r (j+1) := by
  have hex : ∃ j, s < r j := (hr.eventually (eventually_gt_atTop s)).exists
  let k := Nat.find hex
  have hk : s < r k := Nat.find_spec hex
  have hk0 : 0 < k := by
    by_contra hh
    have he : k=0 := by omega
    rw [he] at hk
    omega
  refine ⟨k-1,?_,?_⟩
  · exact le_of_not_gt (Nat.find_min hex (show k-1 < k by omega))
  · simpa only [Nat.sub_add_cancel hk0] using hk

/-- The bands cover all parameter points beyond a finite initial box. -/
lemma band_cover {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (x : ℕ × ℕ) :
    x ∈ box (2^(r 0)) ∨ ∃ j, x ∈ band (r j) (r (j+1)) := by
  by_cases hx : x ∈ box (2^(r 0))
  · exact Or.inl hx
  have hxheight : 2^(r 0) ≤ height x := le_of_not_gt (fun h => hx ((mem_box x _).mpr h))
  have hx0 : 0 < height x := (pow_pos (by decide : 0 < (2:ℕ)) _).trans_le hxheight
  let s := Nat.log 2 (height x)
  have hsL : 2^s ≤ height x := Nat.pow_log_le_self 2 hx0.ne'
  have hsU : height x < 2^(s+1) := Nat.lt_pow_succ_log_self (by decide) _
  have hrs : r 0 ≤ s := by
    by_contra hh
    have hr : s+1 ≤ r 0 := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hr
    omega
  obtain ⟨j,hjL,hjU⟩ := exists_adjacent hr hrs
  refine Or.inr ⟨j,mem_biUnion.mpr ⟨s,mem_Ico.mpr ⟨hjL,hjU⟩,?_⟩⟩
  exact mem_sdiff.mpr ⟨(mem_box x _).mpr hsU,fun h => (not_lt_of_ge hsL) ((mem_box x _).mp h)⟩

/-- Summable normalized box-count costs imply summability of reciprocal
quadratic heights, with no assumption about how the sparse set is defined. -/
theorem summable_of_dyadic_bands (T : Set (ℕ × ℕ)) (r : ℕ → ℕ) (δ : ℕ → ℝ)
    (hr : Tendsto r atTop atTop)
    (hs : Summable (fun j => ((r (j+1)-r j:ℕ):ℝ)*δ j))
    (hcount : ∀ j t, r j ≤ t → t < r (j+1) →
      (((box (2^(t+1))).filter (· ∈ T)).card:ℝ) ≤ ((2^(t+1):ℕ):ℝ)^2*δ j) :
    Summable (weight T) := by
  apply summable_of_finset_cover _ (weight_nonneg T) (box (2^(r 0)))
    (fun j => band (r j) (r (j+1))) (band_cover hr)
  apply (hs.mul_left 4).of_nonneg_of_le
  · intro j
    exact sum_nonneg (fun x _ => weight_nonneg T x)
  · intro j
    simpa only [mul_assoc] using band_cost T (r j) (r (j+1)) (hcount j)

#print axioms summable_of_finset_cover
#print axioms shell_cost
#print axioms band_cover
#print axioms summable_of_dyadic_bands
end Erdos1206.DyadicBoxReciprocal
