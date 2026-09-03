import Submission.CompensatedPipageExplore

/-! Ordered selection with a positive multilinear cost in addition to the
compensated two-sided representation potentials. -/
namespace Erdos66CombinedPipage
open Erdos66OrderedPipageGeometry Erdos66OrderedPipagePrefix
  Erdos66OrderedPositiveRounding Erdos66RepresentationPipage Erdos66CompensatedPipage
  Erdos66PrefixBalancedUpperSelection Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2400000

variable {N : ℕ}

 theorem exists_ordered_rounding_for_cost (F : (Fin N → ℝ) → ℝ)
    (hpair : ∀ x : Fin N → ℝ, (∀ k, 0≤x k ∧ x k≤1) →
      ∀ i j : Fin N, i<j → i∈fractional x → j∈fractional x →
      (∀ k∈fractional x, k<j → k=i) →
      ∀ a b d e w : ℝ, (0≤a ∧ a≤1) → (0≤b ∧ b≤1) → (0≤d ∧ d≤1) →
      (0≤e ∧ e≤1) → (0≤w ∧ w≤1) →
      w*a+(1-w)*d=x i → w*b+(1-w)*e=x j → w*(a*b)+(1-w)*(d*e)≤x i*x j →
      (a=0 ∨ a=1 ∨ b=0 ∨ b=1) → (d=0 ∨ d=1 ∨ e=0 ∨ e=1) →
      w*F (replaceTwo x i j a b)+(1-w)*F (replaceTwo x i j d e)≤F x)
    (hsingle : ∀ x : Fin N → ℝ, (∀ k, 0≤x k ∧ x k≤1) → (fractional x).card≤1 →
      ∀ i∈fractional x, (1-x i)*F (replaceOne x i 0)+x i*F (replaceOne x i 1)≤F x)
    (p : Fin N → ℝ) (hp : ∀ i, 0≤p i ∧ p i≤1) :
    ∃ y : Fin N → ℝ, (∀ i, y i=0 ∨ y i=1) ∧ Brackets p y ∧ F y≤F p := by
  have aux (m : ℕ) : ∀ x : Fin N → ℝ, (∀ i, 0≤x i ∧ x i≤1) →
      (fractional x).card=m → ∃ y : Fin N → ℝ,
        (∀ i, y i=0 ∨ y i=1) ∧ Brackets x y ∧ F y≤F x := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hx hm
      by_cases hcard : (fractional x).card≤1
      · by_cases hne : (fractional x).Nonempty
        · obtain ⟨i,hi⟩ := hne
          have hxi := (mem_fractional x i).mp hi
          have hb (a : ℝ) (ha : a=0 ∨ a=1) := single_rounding_binary x hx hcard i hi a ha
          have hc := endpoint_le_of_average _ _ _ (1-x i) ⟨by linarith,by linarith⟩
            (by simpa only [sub_sub_cancel] using hsingle x hx hcard i hi)
          rcases hc with h | h
          · exact ⟨replaceOne x i 0,hb 0 (Or.inl rfl),single_rounding_brackets x hx hcard i hi 0 (by norm_num),h⟩
          · exact ⟨replaceOne x i 1,hb 1 (Or.inr rfl),single_rounding_brackets x hx hcard i hi 1 (by norm_num),h⟩
        · exact ⟨x,fun i ↦ binary_of_not_fractional x hx i (fun hi ↦ hne ⟨i,hi⟩),Brackets.refl x,le_rfl⟩
      · obtain ⟨i,j,hij,hi,hj,hfirst⟩ := first_two_fractional x (by omega)
        obtain ⟨a,b,d,e,v,ha,hb,hd,he,hv,hs0,hs1,hmi,hmj,hprod,hend0,hend1⟩ :=
          two_coordinate_rounding (x i) (x j) ((mem_fractional x i).mp hi) ((mem_fractional x j).mp hj)
        have hmean := hpair x hx i j hij hi hj hfirst a b d e v ha hb hd he hv hmi hmj hprod hend0 hend1
        have hfinish (a b : ℝ) (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1)
            (hs : a+b=x i+x j) (hend : a=0 ∨ a=1 ∨ b=0 ∨ b=1)
            (hcost : F (replaceTwo x i j a b)≤F x) :
            ∃ y : Fin N → ℝ, (∀ i, y i=0 ∨ y i=1) ∧ Brackets x y ∧ F y≤F x := by
          have hlt := fractional_replaceTwo_card_lt x i j (ne_of_lt hij) hi hj a b hend
          obtain ⟨y,hy,hbr,hcost'⟩ := ih _ (by omega) (replaceTwo x i j a b)
            (replaceTwo_box x hx i j a b ha hb) rfl
          exact ⟨y,hy,(brackets_replaceTwo x hx i j hij hi hfirst a b ha hb hs).trans hbr,hcost'.trans hcost⟩
        rcases endpoint_le_of_average _ _ _ v hv hmean with h | h
        · exact hfinish a b ha hb hs0 hend0 h
        · exact hfinish d e hd he hs1 hend1 h
  exact aux _ p hp rfl

variable {κ η : Type*}

lemma poly_single_average (S : Finset η) (c : η → ℝ) (E : η → Finset (Fin N))
    (x : Fin N → ℝ) (i : Fin N) (a b w : ℝ) (hm : w*a+(1-w)*b=x i) :
    w*poly S c E (replaceOne x i a)+(1-w)*poly S c E (replaceOne x i b)=poly S c E x := by
  simp only [poly,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hh := congrArg (fun z : ℝ ↦ c k*z) (monomial_single_average (E k) x i a b w hm)
  nlinarith only [hh]

 theorem exists_compensated_rounding_with_poly (L : ℕ)
    (S : Finset η) (c : η → ℝ) (E : η → Finset (Fin (L+1))) (hc : ∀ k∈S, 0≤c k)
    (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ) (hw : ∀ k∈T, 0≤w k)
    (p : Fin (L+1) → ℝ) (hp : ∀ i, 0≤p i ∧ p i≤1) :
    ∃ y : Fin (L+1) → ℝ, (∀ i, y i=0 ∨ y i=1) ∧ Brackets p y ∧
      poly S c E y+(∑ k∈T, w k*expPoly L (n k) (t k) y)≤
        poly S c E p+∑ k∈T, w k*(Real.exp (2*|t k|)*expPoly L (n k) (t k) p) := by
  let F : (Fin (L+1) → ℝ) → ℝ := fun x ↦ poly S c E x+cost L T n t w x
  have hpair : ∀ x : Fin (L+1) → ℝ, (∀ k, 0≤x k ∧ x k≤1) →
      ∀ i j : Fin (L+1), i<j → i∈fractional x → j∈fractional x →
      (∀ k∈fractional x, k<j → k=i) →
      ∀ a b d e v : ℝ, (0≤a ∧ a≤1) → (0≤b ∧ b≤1) → (0≤d ∧ d≤1) →
      (0≤e ∧ e≤1) → (0≤v ∧ v≤1) →
      v*a+(1-v)*d=x i → v*b+(1-v)*e=x j → v*(a*b)+(1-v)*(d*e)≤x i*x j →
      (a=0 ∨ a=1 ∨ b=0 ∨ b=1) → (d=0 ∨ d=1 ∨ e=0 ∨ e=1) →
      v*F (replaceTwo x i j a b)+(1-v)*F (replaceTwo x i j d e)≤F x := by
    intro x hx i j hij hi hj hfirst a b d e v ha hb hd he hv hmi hmj hprod hend0 hend1
    have hp' := poly_rounding_inequality S c E hc x (fun k ↦ (hx k).1) i j (ne_of_lt hij)
      a b d e v hmi hmj hprod
    have hr : v*cost L T n t w (replaceTwo x i j a b)+
        (1-v)*cost L T n t w (replaceTwo x i j d e)≤cost L T n t w x := by
      simp only [cost,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k hk
      have hh := mul_le_mul_of_nonneg_left
        (row_pair_average L (n k) (t k) x hx i j hij hi hj hfirst a b d e v ha hb hd he hv
          hmi hmj hprod hend0 hend1) (hw k hk)
      nlinarith only [hh]
    dsimp only [F]
    nlinarith only [hp',hr]
  have hsingle : ∀ x : Fin (L+1) → ℝ, (∀ k, 0≤x k ∧ x k≤1) → (fractional x).card≤1 →
      ∀ i∈fractional x, (1-x i)*F (replaceOne x i 0)+x i*F (replaceOne x i 1)≤F x := by
    intro x hx hcard i hi
    have hb (a : ℝ) (ha : a=0 ∨ a=1) := single_rounding_binary x hx hcard i hi a ha
    have hp' := poly_single_average S c E x i 0 1 (1-x i) (by ring)
    simp only [sub_sub_cancel] at hp'
    have hr : (1-x i)*cost L T n t w (replaceOne x i 0)+
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
    dsimp only [F]
    nlinarith only [hp',hr]
  obtain ⟨y,hy,hbr,hF⟩ := exists_ordered_rounding_for_cost F hpair hsingle p hp
  refine ⟨y,hy,hbr,?_⟩
  have he : cost L T n t w y=∑ k∈T, w k*expPoly L (n k) (t k) y := by
    simp only [cost,row_of_binary L _ _ y hy]
  rw [←he]
  apply hF.trans
  dsimp only [F]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (penalty_le_exp p (n k) (t k)) (expPoly_nonneg L (n k) (t k) p hp)) (hw k hk)

end Erdos66CombinedPipage
