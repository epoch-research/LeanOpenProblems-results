import Submission.DigitBlockingExplore

/-! A sharper digit-box exponent: if b<=2^e then a contained Cartesian
base-b digit box has at most M^e elements under a representation cap M.
This is useful when the digit base itself grows through grouping. -/
namespace Erdos66DigitBoxExponent
open AdditiveCombinatorics Erdos66DigitBoxEnergy Erdos66LayeredDigitProgram
open scoped Classical
set_option maxHeartbeats 2600000
variable {b k e : ℕ}

lemma two_point_power_bound (hbe : b≤2^e) (D : Finset (Fin b)) (hD : D.Nonempty) :
    ∃ a∈D, ∃ d∈D, D.card≤({a,d} : Finset (Fin b)).card^e := by
  by_cases hcard : D.card≤1
  · obtain ⟨a,ha⟩ := hD
    exact ⟨a,ha,a,ha,by simpa using hcard⟩
  · obtain ⟨a,ha,d,hd,had⟩ := Finset.one_lt_card.mp (by omega : 1<D.card)
    refine ⟨a,ha,d,hd,?_⟩
    rw [Finset.card_pair had]
    exact (show D.card≤b by simpa using Finset.card_le_univ D).trans hbe

/-- The exponent depends logarithmically, rather than linearly, on the
base. All representation counts use ordinary natural addition. -/
theorem box_card_le_cap_power (hb : 1 < b) (hbe : b≤2^e)
    (A : Set ℕ) (D : Fin k → Finset (Fin b))
    (hA : (box D : Set ℕ)⊆A) (M : ℕ)
    (hM : ∀ n<2*b^k, sumRep A n≤M) : (box D).card≤M^e := by
  by_cases hD : ∀ i, (D i).Nonempty
  · choose a ha d hd hc using fun i ↦ two_point_power_bound hbe (D i) (hD i)
    have hsub : (box (fun i ↦ ({a i,d i} : Finset (Fin b))) : Set ℕ)⊆A := by
      intro n hn
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hn
      apply hA
      apply mem_box
      intro i
      have hi := Fintype.mem_piFinset.mp hx i
      rcases Finset.mem_insert.mp hi with hi | hi
      · simpa only [hi] using ha i
      · simpa only [Finset.mem_singleton.mp hi] using hd i
    have hpeak := (two_point_box_peak hb A a d hsub).trans
      (hM _ (by have h1 := encode_lt hb a; have h2 := encode_lt hb d; omega))
    have hprod : (box D).card≤
        (Fintype.piFinset (fun i ↦ ({a i,d i} : Finset (Fin b)))).card^e := by
      rw [box_card hb,Fintype.card_piFinset,←Finset.prod_pow]
      exact Finset.prod_le_prod (fun i _ ↦ Nat.zero_le _) (fun i _ ↦ hc i)
    exact hprod.trans (Nat.pow_le_pow_left hpeak e)
  · have he : Fintype.piFinset D=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa only [Fintype.piFinset_nonempty] using hD
    simp only [box,he,Finset.image_empty,Finset.card_empty]
    exact Nat.zero_le _

theorem accepted_card_le {σ : Type*} [Fintype σ] (hb : 1 < b) (hbe : b≤2^e)
    (P : Program b k σ) (A : Set ℕ) (hA : (accepted P : Set ℕ)⊆A) (M : ℕ)
    (hM : ∀ n<2*b^k, sumRep A n≤M) :
    (accepted P).card≤(Fintype.card σ)^(k+1)*M^e := by
  have hbox (q : Fin (k+1) → σ) (hq : q∈paths P) :
      (box (pathDigits P q)).card≤M^e := by
    apply box_card_le_cap_power hb hbe A _ _ M hM
    intro n hn
    exact hA (Finset.mem_biUnion.mpr ⟨q,hq,hn⟩)
  have hpaths : (paths P).card≤(Fintype.card σ)^(k+1) := by
    simpa using Finset.card_le_univ (paths P)
  calc
    _ ≤ ∑ q∈paths P, (box (pathDigits P q)).card := Finset.card_biUnion_le
    _ ≤ ∑ _q∈paths P, M^e := Finset.sum_le_sum hbox
    _ = (paths P).card*M^e := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hpaths

lemma grouped_base_bound (b d : ℕ) : b^d≤2^(b*d) := by
  simpa only [pow_mul] using Nat.pow_le_pow_left (Nat.lt_two_pow_self.le : b≤2^b) d

end Erdos66DigitBoxExponent
