import Submission.RepresentationPipageExplore

/-! A pending-target budget pays for the unique exceptional pair in ordered
rounding. This yields finite two-sided exponential selection with prefix
floor/ceiling constraints. -/
namespace Erdos66CompensatedPipage
open AdditiveCombinatorics Erdos66OrderedPipageGeometry Erdos66OrderedPipagePrefix
  Erdos66RepresentationPipage Erdos66PrefixBalancedUpperSelection Erdos66FiniteBernoulli
open scoped Classical
set_option maxHeartbeats 2600000

variable {N : ℕ}
def Pending (x : Fin N → ℝ) (n : ℕ) : Prop :=
  ∃ i j : Fin N, i<j ∧ i∈fractional x ∧ j∈fractional x ∧ i.val+j.val≤n

lemma pending_mono {x y : Fin N → ℝ} (h : fractional y⊆fractional x) (n : ℕ) :
    Pending y n → Pending x n := by
  rintro ⟨i,j,hij,hi,hj,hn⟩
  exact ⟨i,j,hij,h hi,h hj,hn⟩

lemma not_pending_of_card_le_one (x : Fin N → ℝ) (h : (fractional x).card≤1) (n : ℕ) :
    ¬Pending x n := by
  rintro ⟨i,j,hij,hi,hj,_⟩
  exact (ne_of_lt hij) (Finset.card_le_one.mp h i hi j hj)

lemma not_pending_of_binary (x : Fin N → ℝ) (h : ∀ i, x i=0 ∨ x i=1) (n : ℕ) :
    ¬Pending x n := by
  rintro ⟨i,j,hij,hi,hj,_⟩
  have hh := (mem_fractional x i).mp hi
  rcases h i with he | he <;> rw [he] at hh <;> linarith

lemma pending_removed_at_pair (x : Fin N → ℝ) (i j : Fin N) (hij : i<j)
    (hfirst : ∀ k∈fractional x, k<j → k=i)
    (hi : i∈fractional x) (hj : j∈fractional x)
    (a b : ℝ) (hend : a=0 ∨ a=1 ∨ b=0 ∨ b=1) :
    ¬Pending (replaceTwo x i j a b) (i.val+j.val) := by
  rintro ⟨u,v,huv,hu,hv,hs⟩
  have hsub := fractional_replaceTwo_subset x i j hi hj a b
  have huold := hsub hu
  have hvold := hsub hv
  have hiu : i≤u := by
    by_contra hh
    have hui : u < i := lt_of_not_ge hh
    have he := hfirst u huold (hui.trans hij)
    exact (ne_of_lt hui) he
  have hjv : j≤v := by
    by_contra hh
    have hvj : v<j := lt_of_not_ge hh
    have he := hfirst v hvold hvj
    have hh' : i<v := hiu.trans_lt huv
    exact (ne_of_lt hh') he.symm
  have hui : u=i := Fin.ext (by change i.val≤u.val at hiu; change j.val≤v.val at hjv; omega)
  have hvj : v=j := Fin.ext (by change i.val≤u.val at hiu; change j.val≤v.val at hjv; omega)
  subst u
  subst v
  simp only [mem_fractional,replaceTwo,ite_true,if_neg (Ne.symm (ne_of_lt hij))] at hu hv
  rcases hend with he | he | he | he <;> simp_all

noncomputable def penalty (x : Fin N → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if Pending x n then Real.exp (2*|t|) else 1

lemma penalty_nonneg (x : Fin N → ℝ) (n : ℕ) (t : ℝ) : 0≤penalty x n t := by
  unfold penalty
  split_ifs; exact (Real.exp_pos _).le; exact zero_le_one

lemma penalty_le_exp (x : Fin N → ℝ) (n : ℕ) (t : ℝ) : penalty x n t≤Real.exp (2*|t|) := by
  unfold penalty
  split_ifs
  · exact le_rfl
  · exact Real.one_le_exp_iff.mpr (by positivity)

lemma penalty_mono {x y : Fin N → ℝ} (h : fractional y⊆fractional x) (n : ℕ) (t : ℝ) :
    penalty y n t≤penalty x n t := by
  by_cases hx : Pending x n
  · simpa only [penalty,if_pos hx] using penalty_le_exp y n t
  · have hy : ¬Pending y n := fun hy ↦ hx (pending_mono h n hy)
    simp only [penalty,if_neg hx,if_neg hy,le_refl]

noncomputable def row (L n : ℕ) (t : ℝ) (x : Fin (L+1) → ℝ) : ℝ :=
  penalty x n t*expPoly L n t x

lemma row_pair_average (L n : ℕ) (t : ℝ) (x : Fin (L+1) → ℝ)
    (hx : ∀ k, 0≤x k ∧ x k≤1) (i j : Fin (L+1)) (hij : i<j)
    (hi : i∈fractional x) (hj : j∈fractional x)
    (hfirst : ∀ k∈fractional x, k<j → k=i)
    (a b d e w : ℝ) (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1)
    (hd : 0≤d ∧ d≤1) (he : 0≤e ∧ e≤1) (hw : 0≤w ∧ w≤1)
    (hmi : w*a+(1-w)*d=x i) (hmj : w*b+(1-w)*e=x j)
    (hp : w*(a*b)+(1-w)*(d*e)≤x i*x j)
    (hend0 : a=0 ∨ a=1 ∨ b=0 ∨ b=1) (hend1 : d=0 ∨ d=1 ∨ e=0 ∨ e=1) :
    w*row L n t (replaceTwo x i j a b)+(1-w)*row L n t (replaceTwo x i j d e)≤row L n t x := by
  by_cases hn : i.val+j.val=n
  · have hpend : Pending x n := ⟨i,j,hij,hi,hj,hn.le⟩
    have hnp0 : ¬Pending (replaceTwo x i j a b) n := by
      rw [←hn]; exact pending_removed_at_pair x i j hij hfirst hi hj a b hend0
    have hnp1 : ¬Pending (replaceTwo x i j d e) n := by
      rw [←hn]; exact pending_removed_at_pair x i j hij hfirst hi hj d e hend1
    simp only [row,penalty,if_pos hpend,if_neg hnp0,if_neg hnp1,one_mul]
    have h0 := mul_le_mul_of_nonneg_left (expPoly_pair_ratio L n t x hx i j hij hn a b ha hb) hw.1
    have h1 := mul_le_mul_of_nonneg_left (expPoly_pair_ratio L n t x hx i j hij hn d e hd he)
      (sub_nonneg.mpr hw.2)
    nlinarith only [h0,h1]
  · have hrow := expPoly_pipage_distinct L n t x hx i j (ne_of_lt hij) hn a b d e w hmi hmj hp
    have h0 := mul_le_mul_of_nonneg_right
      (penalty_mono (fractional_replaceTwo_subset x i j hi hj a b) n t)
      (expPoly_nonneg L n t _ (replaceTwo_box x hx i j a b ha hb))
    have h1 := mul_le_mul_of_nonneg_right
      (penalty_mono (fractional_replaceTwo_subset x i j hi hj d e) n t)
      (expPoly_nonneg L n t _ (replaceTwo_box x hx i j d e hd he))
    have h0' := mul_le_mul_of_nonneg_left h0 hw.1
    have h1' := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hw.2)
    have hh := mul_le_mul_of_nonneg_left hrow (penalty_nonneg x n t)
    dsimp only [row]
    nlinarith only [h0',h1',hh]

lemma single_rounding_brackets (x : Fin N → ℝ) (hx : ∀ i, 0≤x i ∧ x i≤1)
    (hcard : (fractional x).card≤1) (i : Fin N) (hi : i∈fractional x)
    (a : ℝ) (ha : 0≤a ∧ a≤1) : Brackets x (replaceOne x i a) := by
  intro k
  by_cases hik : i.val<k
  · apply bracket_single_fraction _ x _ i (by simp [hik]) ((mem_fractional x i).mp hi)
      (by simpa [replaceOne] using ha)
    intro j hj hji
    exact ⟨binary_of_not_fractional x hx j (fun hjf ↦ hji (Finset.card_le_one.mp hcard j hjf i hi)),
      by simp [replaceOne,hji]⟩
  · have he : pref (replaceOne x i a) k=pref x k := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk := (Finset.mem_filter.mp hj).2
      have hji : j≠i := by intro h; subst j; exact hik hjk
      simp only [replaceOne,if_neg hji]
    rw [he]
    exact ⟨Int.floor_le _,Int.le_ceil _⟩

lemma single_rounding_binary (x : Fin N → ℝ) (hx : ∀ i, 0≤x i ∧ x i≤1)
    (hcard : (fractional x).card≤1) (i : Fin N) (hi : i∈fractional x)
    (a : ℝ) (ha : a=0 ∨ a=1) : ∀ k, replaceOne x i a k=0 ∨ replaceOne x i a k=1 := by
  intro k
  by_cases hki : k=i
  · simpa only [replaceOne,if_pos hki] using ha
  · simp only [replaceOne,if_neg hki]
    exact binary_of_not_fractional x hx k (fun hk ↦ hki (Finset.card_le_one.mp hcard k hk i hi))

lemma endpoint_le_of_average (u v z w : ℝ) (hw : 0≤w ∧ w≤1)
    (h : w*u+(1-w)*v≤z) : u≤z ∨ v≤z := by
  by_contra hh
  push_neg at hh
  have hp : 0<w := by
    by_contra hn
    have hz : w=0 := le_antisymm (not_lt.mp hn) hw.1
    rw [hz] at h
    simp only [zero_mul,sub_zero,one_mul,zero_add] at h
    exact (not_le_of_gt hh.2) h
  have h0 := mul_lt_mul_of_pos_left hh.1 hp
  have h1 := mul_le_mul_of_nonneg_left hh.2.le (sub_nonneg.mpr hw.2)
  nlinarith

variable {κ : Type*}
noncomputable def cost (L : ℕ) (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ)
    (x : Fin (L+1) → ℝ) : ℝ := ∑ k∈T, w k*row L (n k) (t k) x

lemma row_of_binary (L n : ℕ) (t : ℝ) (x : Fin (L+1) → ℝ)
    (hx : ∀ i, x i=0 ∨ x i=1) : row L n t x=expPoly L n t x := by
  simp only [row,penalty,if_neg (not_pending_of_binary x hx n),one_mul]

/-- Every target pays the factor exp(2|t|) at most once, even for negative
tilts. All prefix brackets are preserved by the same finite selection. -/
theorem exists_compensated_rounding (L : ℕ) (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ)
    (hw : ∀ k∈T, 0≤w k) (p : Fin (L+1) → ℝ) (hp : ∀ i, 0≤p i ∧ p i≤1) :
    ∃ y : Fin (L+1) → ℝ, (∀ i, y i=0 ∨ y i=1) ∧ Brackets p y ∧
      (∑ k∈T, w k*expPoly L (n k) (t k) y)≤
        ∑ k∈T, w k*(Real.exp (2*|t k|)*expPoly L (n k) (t k) p) := by
  have aux (m : ℕ) : ∀ x : Fin (L+1) → ℝ, (∀ i, 0≤x i ∧ x i≤1) →
      (fractional x).card=m → ∃ y : Fin (L+1) → ℝ,
        (∀ i, y i=0 ∨ y i=1) ∧ Brackets x y ∧ cost L T n t w y≤cost L T n t w x := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hx hm
      by_cases hcard : (fractional x).card≤1
      · by_cases hne : (fractional x).Nonempty
        · obtain ⟨i,hi⟩ := hne
          have hxi := (mem_fractional x i).mp hi
          have hb (a : ℝ) (ha : a=0 ∨ a=1) := single_rounding_binary x hx hcard i hi a ha
          have hmean : (1-x i)*cost L T n t w (replaceOne x i 0)+
              x i*cost L T n t w (replaceOne x i 1)=cost L T n t w x := by
            simp only [cost,Finset.mul_sum,←Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            rw [row_of_binary L (n k) (t k) _ (hb 0 (Or.inl rfl)),
              row_of_binary L (n k) (t k) _ (hb 1 (Or.inr rfl))]
            have hrow : row L (n k) (t k) x=expPoly L (n k) (t k) x := by
              simp only [row,penalty,if_neg (not_pending_of_card_le_one x hcard _),one_mul]
            rw [hrow]
            have he := expPoly_single_average L (n k) (t k) x i 0 1 (1-x i) (by ring)
            have he' := congrArg (fun z : ℝ ↦ w k*z) he
            nlinarith only [he']
          have hc := endpoint_le_of_average _ _ _ (1-x i) ⟨by linarith,by linarith⟩
            (by simpa only [sub_sub_cancel] using hmean.le)
          rcases hc with h | h
          · exact ⟨replaceOne x i 0,hb 0 (Or.inl rfl),single_rounding_brackets x hx hcard i hi 0 (by norm_num),h⟩
          · exact ⟨replaceOne x i 1,hb 1 (Or.inr rfl),single_rounding_brackets x hx hcard i hi 1 (by norm_num),h⟩
        · exact ⟨x,fun i ↦ binary_of_not_fractional x hx i (fun hi ↦ hne ⟨i,hi⟩),Brackets.refl x,le_rfl⟩
      · obtain ⟨i,j,hij,hi,hj,hfirst⟩ := first_two_fractional x (by omega)
        obtain ⟨a,b,d,e,v,ha,hb,hd,he,hv,hs0,hs1,hmi,hmj,hprod,hend0,hend1⟩ :=
          two_coordinate_rounding (x i) (x j) ((mem_fractional x i).mp hi) ((mem_fractional x j).mp hj)
        have hmean : v*cost L T n t w (replaceTwo x i j a b)+
            (1-v)*cost L T n t w (replaceTwo x i j d e)≤cost L T n t w x := by
          simp only [cost,Finset.mul_sum,←Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro k hk
          have hh := mul_le_mul_of_nonneg_left
            (row_pair_average L (n k) (t k) x hx i j hij hi hj hfirst a b d e v ha hb hd he hv
              hmi hmj hprod hend0 hend1) (hw k hk)
          nlinarith only [hh]
        have hchoice := endpoint_le_of_average _ _ _ v hv hmean
        have hfinish (a b : ℝ) (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1)
            (hs : a+b=x i+x j) (hend : a=0 ∨ a=1 ∨ b=0 ∨ b=1)
            (hcost : cost L T n t w (replaceTwo x i j a b)≤cost L T n t w x) :
            ∃ y : Fin (L+1) → ℝ, (∀ i, y i=0 ∨ y i=1) ∧ Brackets x y ∧
              cost L T n t w y≤cost L T n t w x := by
          have hlt := fractional_replaceTwo_card_lt x i j (ne_of_lt hij) hi hj a b hend
          obtain ⟨y,hy,hbr,hcost'⟩ := ih _ (by omega) (replaceTwo x i j a b)
            (replaceTwo_box x hx i j a b ha hb) rfl
          exact ⟨y,hy,(brackets_replaceTwo x hx i j hij hi hfirst a b ha hb hs).trans hbr,hcost'.trans hcost⟩
        rcases hchoice with h | h
        · exact hfinish a b ha hb hs0 hend0 h
        · exact hfinish d e hd he hs1 hend1 h
  obtain ⟨y,hy,hbr,hcost⟩ := aux _ p hp rfl
  refine ⟨y,hy,hbr,?_⟩
  have he : cost L T n t w y=∑ k∈T, w k*expPoly L (n k) (t k) y := by
    simp only [cost,row_of_binary L _ _ y hy]
  rw [←he]
  apply hcost.trans
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (penalty_le_exp p (n k) (t k)) (expPoly_nonneg L (n k) (t k) p hp)) (hw k hk)

end Erdos66CompensatedPipage
