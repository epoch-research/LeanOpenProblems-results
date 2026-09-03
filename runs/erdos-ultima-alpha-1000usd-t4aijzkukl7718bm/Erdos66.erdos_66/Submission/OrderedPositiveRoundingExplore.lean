import Submission.OrderedPipagePrefixExplore

/-! Ordered rounding of nonnegative multilinear polynomials with simultaneous
prefix floor/ceiling bounds. This is a finite selection theorem. -/
namespace Erdos66OrderedPositiveRounding
open Erdos66OrderedPipageGeometry Erdos66OrderedPipagePrefix
open scoped Classical
set_option maxHeartbeats 2000000

variable {N : ℕ} {κ : Type*}
noncomputable def poly (T : Finset κ) (c : κ → ℝ) (E : κ → Finset (Fin N))
    (x : Fin N → ℝ) : ℝ := ∑ k∈T, c k*∏ i∈E k, x i

lemma poly_mono (T : Finset κ) (c : κ → ℝ) (E : κ → Finset (Fin N))
    (hc : ∀ k∈T, 0≤c k) (x y : Fin N → ℝ) (hx : ∀ i, 0≤x i) (hxy : ∀ i, x i≤y i) :
    poly T c E x≤poly T c E y := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun i _ ↦ hx i) (fun i _ ↦ hxy i)) (hc k hk)

lemma poly_rounding_inequality (T : Finset κ) (c : κ → ℝ) (E : κ → Finset (Fin N))
    (hc : ∀ k∈T, 0≤c k) (x : Fin N → ℝ) (hx : ∀ i, 0≤x i)
    (i j : Fin N) (hij : i≠j) (a b d e w : ℝ)
    (hi : w*a+(1-w)*d=x i) (hj : w*b+(1-w)*e=x j)
    (hp : w*(a*b)+(1-w)*(d*e)≤x i*x j) :
    w*poly T c E (replaceTwo x i j a b)+(1-w)*poly T c E (replaceTwo x i j d e)≤poly T c E x := by
  calc
    _ = ∑ k∈T, c k*(w*(∏ r∈E k, replaceTwo x i j a b r)+
        (1-w)*(∏ r∈E k, replaceTwo x i j d e r)) := by
      simp only [poly,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ _ := Finset.sum_le_sum (fun k hk ↦ mul_le_mul_of_nonneg_left
      (monomial_rounding_inequality (E k) x hx i j hij a b d e w hi hj hp) (hc k hk))

lemma round_last_fractional (x : Fin N → ℝ) (hx : ∀ i, 0≤x i ∧ x i≤1)
    (hcard : (fractional x).card≤1) :
    ∃ y : Fin N → ℝ, (∀ i, y i=0 ∨ y i=1) ∧ Brackets x y ∧
      (∀ i, 0≤y i) ∧ ∀ i, y i≤x i := by
  by_cases he : (fractional x).Nonempty
  · obtain ⟨i,hi⟩ := he
    let y : Fin N → ℝ := fun j ↦ if j=i then 0 else x j
    have hbinary (j : Fin N) (hji : j≠i) : x j=0 ∨ x j=1 :=
      binary_of_not_fractional x hx j (fun hj ↦ hji (Finset.card_le_one.mp hcard j hj i hi))
    refine ⟨y,?_,?_,?_,?_⟩
    · intro j
      by_cases hji : j=i
      · exact Or.inl (if_pos hji)
      · simpa only [y,if_neg hji] using hbinary j hji
    · intro k
      by_cases hik : i.val<k
      · apply bracket_single_fraction _ x y i (by simp [hik]) ((mem_fractional x i).mp hi)
          (by simp [y])
        intro j hj hji
        exact ⟨hbinary j hji,if_neg hji⟩
      · have hp : pref y k=pref x k := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjk := (Finset.mem_filter.mp hj).2
          have hji : j≠i := by intro h; subst j; exact hik hjk
          exact if_neg hji
        rw [hp]
        exact ⟨Int.floor_le _,Int.le_ceil _⟩
    · intro j
      dsimp [y]
      split_ifs; exact le_rfl; exact (hx j).1
    · intro j
      dsimp [y]
      split_ifs; exact (hx j).1; exact le_rfl
  · refine ⟨x,fun i ↦ binary_of_not_fractional x hx i (fun hi ↦ he ⟨i,hi⟩),
      Brackets.refl x,fun i ↦ (hx i).1,fun _ ↦ le_rfl⟩

/-- Every nonnegative multilinear polynomial admits a 0/1 rounding that does
not increase it and keeps every prefix between the original floor and ceil. -/
theorem exists_prefix_balanced_rounding (T : Finset κ) (c : κ → ℝ)
    (E : κ → Finset (Fin N)) (hc : ∀ k∈T, 0≤c k)
    (p : Fin N → ℝ) (hp : ∀ i, 0≤p i ∧ p i≤1) :
    ∃ y : Fin N → ℝ, (∀ i, y i=0 ∨ y i=1) ∧ Brackets p y ∧ poly T c E y≤poly T c E p := by
  have aux (m : ℕ) : ∀ x : Fin N → ℝ, (∀ i, 0≤x i ∧ x i≤1) →
      (fractional x).card=m → ∃ y : Fin N → ℝ,
        (∀ i, y i=0 ∨ y i=1) ∧ Brackets x y ∧ poly T c E y≤poly T c E x := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hx hm
      by_cases hcard : (fractional x).card≤1
      · obtain ⟨y,hy,hbr,hy0,hyx⟩ := round_last_fractional x hx hcard
        exact ⟨y,hy,hbr,poly_mono T c E hc y x hy0 hyx⟩
      · have hcard' : 1<(fractional x).card := by omega
        obtain ⟨i,j,hij,hi,hj,hfirst⟩ := first_two_fractional x hcard'
        obtain ⟨a,b,d,e,w,ha,hb,hd,he,hw,hs0,hs1,hmi,hmj,hprod,hend0,hend1⟩ :=
          two_coordinate_rounding (x i) (x j) ((mem_fractional x i).mp hi) ((mem_fractional x j).mp hj)
        have hmean := poly_rounding_inequality T c E hc x (fun k ↦ (hx k).1)
          i j (ne_of_lt hij) a b d e w hmi hmj hprod
        have hchoice : poly T c E (replaceTwo x i j a b)≤poly T c E x ∨
            poly T c E (replaceTwo x i j d e)≤poly T c E x := by
          by_contra hn
          push_neg at hn
          have hsum := add_lt_add_of_lt_of_le
            (mul_lt_mul_of_pos_left hn.1 (show 0<w from by
              by_contra hh
              have hw0 : w=0 := le_antisymm (not_lt.mp hh) hw.1
              rw [hw0] at hmean
              simp only [zero_mul,sub_zero,one_mul,zero_add] at hmean
              exact (not_le_of_gt hn.2) hmean))
            (mul_le_mul_of_nonneg_left hn.2.le (sub_nonneg.mpr hw.2))
          nlinarith
        have hfinish (a b : ℝ) (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1)
            (hs : a+b=x i+x j) (hend : a=0 ∨ a=1 ∨ b=0 ∨ b=1)
            (hcost : poly T c E (replaceTwo x i j a b)≤poly T c E x) :
            ∃ y : Fin N → ℝ, (∀ i, y i=0 ∨ y i=1) ∧ Brackets x y ∧
              poly T c E y≤poly T c E x := by
          have hlt := fractional_replaceTwo_card_lt x i j (ne_of_lt hij) hi hj a b hend
          obtain ⟨y,hy,hbr,hycost⟩ := ih _ (by omega) (replaceTwo x i j a b)
            (replaceTwo_box x hx i j a b ha hb) rfl
          exact ⟨y,hy,(brackets_replaceTwo x hx i j hij hi hfirst a b ha hb hs).trans hbr,
            hycost.trans hcost⟩
        rcases hchoice with h | h
        · exact hfinish a b ha hb hs0 hend0 h
        · exact hfinish d e hd he hs1 hend1 h
  exact aux _ p hp rfl

end Erdos66OrderedPositiveRounding
