import FormalConjecturesUtil

/-!
# Erdős Problem 41

*Reference:* [erdosproblems.com/41](https://www.erdosproblems.com/41)
-/

open Filter Set

namespace Erdos41
variable {α : Type} [AddCommMonoid α]

/--
For a given set `A`, the n-tuple sums `a₁ + ... + aₙ` are all distinct for `a₁, ..., aₙ` in `A`
(aside from the trivial coincidences).
-/
def NtupleCondition (A : Set α) (n : ℕ) : Prop := ∀ (I : Finset α) (J : Finset α),
  ↑I ⊆ A ∧ ↑J ⊆ A ∧ I.card = n ∧ J.card = n ∧
  (∑ i ∈ I, i = ∑ j ∈ J, j) → I = J

lemma triple_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) (N : ℕ) (hN : ∀ a ∈ S, a ≤ N) :
    S.card.choose 3 ≤ 3 * N + 1 := by
  have hi : Set.InjOn (fun I : Finset ℕ => ∑ i ∈ I, i) (S.powersetCard 3 : Set (Finset ℕ)) := by
    intro I hI J hJ heq
    obtain ⟨hIS, hIc⟩ := Finset.mem_powersetCard.mp hI
    obtain ⟨hJS, hJc⟩ := Finset.mem_powersetCard.mp hJ
    exact h I J ⟨fun a ha => hS (hIS ha), fun a ha => hS (hJS ha), hIc, hJc, heq⟩
  have hm : Set.MapsTo (fun I : Finset ℕ => ∑ i ∈ I, i)
      (S.powersetCard 3 : Set (Finset ℕ)) (Finset.range (3 * N + 1) : Set ℕ) := by
    intro I hI
    obtain ⟨hIS, hIc⟩ := Finset.mem_powersetCard.mp hI
    apply Finset.mem_range.mpr
    have hx : ∑ i ∈ I, i ≤ I.card * N := by
      calc
        ∑ i ∈ I, i ≤ ∑ _ ∈ I, N := Finset.sum_le_sum (fun i hi => hN i (hIS hi))
        _ = I.card * N := by simp
    simpa [hIc] using Nat.lt_succ_of_le hx
  simpa using Finset.card_le_card_of_injOn _ hm hi

lemma cutoff_count_bound {A : Set ℕ} (h : NtupleCondition A 3) (N : ℕ) :
    (A ∩ Icc 1 N).ncard.choose 3 ≤ 3 * N + 1 := by
  classical
  let S := (Finset.Icc 1 N).filter (· ∈ A)
  have hSc : (S : Set ℕ) = A ∩ Icc 1 N := by ext; simp [S, and_left_comm, and_comm]
  have hc : S.card = (A ∩ Icc 1 N).ncard := by rw [← hSc]; simp
  rw [← hc]
  apply triple_count_bound h S
  · intro a ha
    exact (Finset.mem_filter.mp (show a ∈ (Finset.Icc 1 N).filter (· ∈ A) from ha)).2
  · intro a ha
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2


lemma NtupleCondition.pred {A : Set α} {n : ℕ}
    (h : NtupleCondition A (n + 1)) (hA : A.Infinite) : NtupleCondition A n := by
  classical
  intro I J ⟨hI, hJ, hIc, hJc, hs⟩
  obtain ⟨a, haA, ha⟩ := hA.exists_notMem_finset (I ∪ J)
  have haI : a ∉ I := fun h' => ha (Finset.mem_union_left _ h')
  have haJ : a ∉ J := fun h' => ha (Finset.mem_union_right _ h')
  have heq : insert a I = insert a J := h (insert a I) (insert a J) ⟨
    by simpa using Set.insert_subset haA hI,
    by simpa using Set.insert_subset haA hJ,
    by simp [haI, hIc], by simp [haJ, hJc], by simpa [haI, haJ] using congrArg (a + ·) hs⟩
  simpa [haI, haJ] using congrArg (Finset.erase · a) heq

lemma cube_count_bound {A : Set ℕ} (h : NtupleCondition A 3) (N : ℕ) :
    ((A ∩ Icc 1 N).ncard - 2)^3 ≤ 18 * N + 6 := by
  let k := (A ∩ Icc 1 N).ncard
  have hc : k.choose 3 ≤ 3 * N + 1 := cutoff_count_bound h N
  have hf := Nat.descFactorial_eq_factorial_mul_choose k 3
  have heq : k * (k - 1) * (k - 2) = 6 * k.choose 3 := by
    simpa [Nat.descFactorial_succ, Nat.factorial, mul_assoc, mul_left_comm, mul_comm] using hf
  have h1 : k - 2 ≤ k - 1 := Nat.sub_le_sub_left (by decide) k
  have h2 : k - 2 ≤ k := Nat.sub_le _ _
  have hm := Nat.mul_le_mul (Nat.mul_le_mul h2 h1) (le_refl (k - 2))
  calc
    (k - 2)^3 ≤ k * (k - 1) * (k - 2) := by simpa [pow_succ] using hm
    _ = 6 * k.choose 3 := heq
    _ ≤ 18 * N + 6 := by omega

lemma density_nonneg (A : Set ℕ) (N : ℕ) :
    0 ≤ (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ) := by positivity

lemma density_le_five {A : Set ℕ} (h : NtupleCondition A 3) {N : ℕ} (hN : 1 ≤ N) :
    (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ) ≤ 5 := by
  let k := (A ∩ Icc 1 N).ncard
  let x := (N : ℝ) ^ (1/3 : ℝ)
  have hx : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hx3 : x^3 = (N : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hk : (k : ℝ) ≤ 5 * x := by
    by_cases hk2 : 2 ≤ k
    · have hcube : ((k : ℝ) - 2)^3 ≤ 18 * (N : ℝ) + 6 := by
        have hh := cube_count_bound h N
        change (k - 2)^3 ≤ 18 * N + 6 at hh
        exact_mod_cast (show (↑(k - 2) : ℝ)^3 ≤ 18 * (N : ℝ) + 6 by exact_mod_cast hh)
      have hk2' : (0 : ℝ) ≤ (k : ℝ) - 2 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        linarith
      have h3 : (k : ℝ) - 2 ≤ 3 * x := by
        apply (pow_le_pow_iff_left₀ hk2' (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
        nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
      linarith
    · have hk' : (k : ℝ) < 2 := by exact_mod_cast (lt_of_not_ge hk2)
      linarith
  change (k : ℝ) / x ≤ 5
  exact (div_le_iff₀ (by linarith : 0 < x)).mpr hk


lemma density_liminf_eq_zero_iff {A : Set ℕ} (h : NtupleCondition A 3) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 ↔
    ∀ ε : ℝ, 0 < ε → ∀ M : ℕ, ∃ N ≥ M,
      (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ) < ε := by
  let f := fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)
  have hlow : ∀ᶠ N in atTop, 0 ≤ f N := Eventually.of_forall (density_nonneg A)
  have hupp : ∀ᶠ N in atTop, f N ≤ 5 :=
    (eventually_ge_atTop 1).mono (fun _ hN => density_le_five h hN)
  have hl := isBoundedUnder_of_eventually_ge hlow
  have hu := isBoundedUnder_of_eventually_le hupp
  have hn : 0 ≤ atTop.liminf f := le_liminf_of_le hu.isCoboundedUnder_ge hlow
  have he : atTop.liminf f ≤ 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ M : ℕ,
      ∃ N ≥ M, f N < ε := by
    rw [liminf_le_iff hu.isCoboundedUnder_ge hl]
    simp only [frequently_atTop]
  constructor
  · intro hz
    exact he.mp (le_of_eq hz)
  · intro hz
    exact le_antisymm (he.mpr hz) hn

lemma density_liminf_ne_zero_iff {A : Set ℕ} (h : NtupleCondition A 3) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0 ↔
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℕ, ∀ N ≥ M,
      ε ≤ (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ) := by
  rw [ne_eq, density_liminf_eq_zero_iff h]
  push_neg
  rfl


lemma card_le_five_of_pairwise_mem {β : Type*} (S : Finset β) (P : β → Finset β)
    (hP : ∀ i ∈ S, (P i).card ≤ 2)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → j ∈ P i ∨ i ∈ P j) : S.card ≤ 5 := by
  classical
  let E := (S ×ˢ S).filter (fun p => p.2 ∈ P p.1)
  have hE : E.card ≤ 2 * S.card := by
    have heq : E.card = ∑ i ∈ S, (E.filter (fun p => p.1 = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
    rw [heq]
    calc
      ∑ i ∈ S, (E.filter (fun p => p.1 = i)).card ≤ ∑ i ∈ S, (P i).card := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.card_le_card_of_injOn Prod.snd
        · intro p hp
          obtain ⟨hpE, hp1⟩ := Finset.mem_filter.mp hp
          have hpm := (Finset.mem_filter.mp hpE).2
          simpa [hp1] using hpm
        · intro p hp q hq heq
          have hp1 := (Finset.mem_filter.mp hp).2
          have hq1 := (Finset.mem_filter.mp hq).2
          exact Prod.ext (hp1.trans hq1.symm) heq
      _ ≤ ∑ _ ∈ S, 2 := Finset.sum_le_sum hP
      _ = 2 * S.card := by simp [mul_comm]
  have hcover : S.offDiag ⊆ E ∪ E.image Prod.swap := by
    intro p hp
    obtain ⟨hi, hj, hij⟩ := Finset.mem_offDiag.mp hp
    rcases hpair p.1 hi p.2 hj hij with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, h⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨p.swap, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hj, hi⟩, h⟩, Prod.swap_swap p⟩
  have hcount : S.card * S.card - S.card ≤ 4 * S.card := by
    calc
      S.card * S.card - S.card = S.offDiag.card := (Finset.offDiag_card S).symm
      _ ≤ (E ∪ E.image Prod.swap).card := Finset.card_le_card hcover
      _ ≤ E.card + (E.image Prod.swap).card := Finset.card_union_le _ _
      _ ≤ E.card + E.card := Nat.add_le_add_left (Finset.card_image_le) _
      _ ≤ 4 * S.card := by omega
  by_cases hzero : S.card = 0
  · omega
  have hpos : 1 ≤ S.card := by omega
  have hsq : S.card ≤ S.card * S.card := by nlinarith
  have hh := Nat.sub_add_cancel hsq
  nlinarith

lemma signed_sum_fiber_card_le_five {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (t : ℤ) (R : Finset (Finset ℕ × ℕ))
    (hR : ∀ p ∈ R, (p.1 : Set ℕ) ⊆ A ∧ p.1.card = 2 ∧ p.2 ∈ A ∧ p.2 ∉ p.1 ∧
      (↑(∑ a ∈ p.1, a) : ℤ) - (p.2 : ℤ) = t) : R.card ≤ 5 := by
  classical
  have h2 : NtupleCondition A 2 := h.pred hA
  have hn : Set.InjOn (fun p : Finset ℕ × ℕ => p.2) (R : Set (Finset ℕ × ℕ)) := by
    intro p hp q hq hpq
    change p.2 = q.2 at hpq
    obtain ⟨hpA, hpc, hpa, hpn, hps⟩ := hR p hp
    obtain ⟨hqA, hqc, hqa, hqn, hqs⟩ := hR q hq
    have hs : ∑ a ∈ p.1, a = ∑ a ∈ q.1, a := by
      have hz : (↑(∑ a ∈ p.1, a) : ℤ) = ↑(∑ a ∈ q.1, a) := by rw [hpq] at hps; omega
      exact_mod_cast hz
    exact Prod.ext (h2 p.1 q.1 ⟨hpA, hqA, hpc, hqc, hs⟩) hpq
  let P := fun p : Finset ℕ × ℕ => R.filter (fun q => q.2 ∈ p.1)
  apply card_le_five_of_pairwise_mem R P
  · intro p hp
    calc
      (P p).card ≤ p.1.card := by
        apply Finset.card_le_card_of_injOn (fun q : Finset ℕ × ℕ => q.2)
        · intro q hq
          exact (Finset.mem_filter.mp hq).2
        · intro q hq r hr heq
          exact hn (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hr).1 heq
      _ = 2 := (hR p hp).2.1
  · intro p hp q hq hpq
    have hc : q.2 ∈ p.1 ∨ p.2 ∈ q.1 := by
      by_contra! hc
      obtain ⟨hpA, hpc, hpa, hpn, hps⟩ := hR p hp
      obtain ⟨hqA, hqc, hqa, hqn, hqs⟩ := hR q hq
      have hs : (∑ a ∈ p.1, a) + q.2 = (∑ a ∈ q.1, a) + p.2 := by
        have hz : (↑(∑ a ∈ p.1, a) : ℤ) + (q.2 : ℤ) =
            ↑(∑ a ∈ q.1, a) + (p.2 : ℤ) := by omega
        exact_mod_cast hz
      have heq : insert q.2 p.1 = insert p.2 q.1 := h _ _ ⟨
        by simpa using Set.insert_subset hqa hpA,
        by simpa using Set.insert_subset hpa hqA,
        by simp [hc.1, hpc], by simp [hc.2, hqc],
        by simpa [hc.1, hc.2, add_comm] using hs⟩
      have hm : q.2 ∈ insert p.2 q.1 := heq ▸ Finset.mem_insert_self _ _
      have hnq : q.2 = p.2 := (Finset.mem_insert.mp hm).resolve_right hqn
      exact hpq (hn hp hq hnq.symm)
    rcases hc with hc | hc
    · exact Or.inl (Finset.mem_filter.mpr ⟨hq, hc⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hp, hc⟩)


lemma signed_sum_interval_card_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (L U : ℤ) (R : Finset (Finset ℕ × ℕ))
    (hR : ∀ p ∈ R, (p.1 : Set ℕ) ⊆ A ∧ p.1.card = 2 ∧ p.2 ∈ A ∧ p.2 ∉ p.1 ∧
      L ≤ (↑(∑ a ∈ p.1, a) : ℤ) - (p.2 : ℤ) ∧
      (↑(∑ a ∈ p.1, a) : ℤ) - (p.2 : ℤ) ≤ U) :
    R.card ≤ 5 * (U + 1 - L).toNat := by
  classical
  let f := fun p : Finset ℕ × ℕ => (↑(∑ a ∈ p.1, a) : ℤ) - (p.2 : ℤ)
  have hm : ∀ p ∈ R, f p ∈ Finset.Icc L U := by
    intro p hp
    exact Finset.mem_Icc.mpr (hR p hp).2.2.2.2
  have he : R.card = ∑ t ∈ Finset.Icc L U, (R.filter (fun p => f p = t)).card :=
    Finset.card_eq_sum_card_fiberwise hm
  rw [he]
  calc
    ∑ t ∈ Finset.Icc L U, (R.filter (fun p => f p = t)).card ≤
        ∑ _ ∈ Finset.Icc L U, 5 := by
      apply Finset.sum_le_sum
      intro t ht
      apply signed_sum_fiber_card_le_five h hA t
      intro p hp
      obtain ⟨hpR, hpt⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpA, hpc, hpa, hpn, _⟩ := hR p hpR
      exact ⟨hpA, hpc, hpa, hpn, hpt⟩
    _ = 5 * (U + 1 - L).toNat := by simp [Int.card_Icc, mul_comm]


lemma sorted_triples_interval_card_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (L U : ℤ) (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 ∈ A ∧ p.2.1 ∈ A ∧ p.2.2 ∈ A ∧
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
      L ≤ (p.1 : ℤ) + (p.2.1 : ℤ) - (p.2.2 : ℤ) ∧
      (p.1 : ℤ) + (p.2.1 : ℤ) - (p.2.2 : ℤ) ≤ U) :
    T.card ≤ 5 * (U + 1 - L).toNat := by
  classical
  let f : ℕ × ℕ × ℕ → Finset ℕ × ℕ := fun p => ({p.1, p.2.1}, p.2.2)
  have hf : Set.InjOn f (T : Set (ℕ × ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hp' := hT p hp
    have hq' := hT q hq
    have he : ({p.1, p.2.1} : Finset ℕ) = {q.1, q.2.1} := congrArg Prod.fst hpq
    have hc : p.2.2 = q.2.2 := congrArg (fun r : Finset ℕ × ℕ => r.2) hpq
    have ha : p.1 = q.1 ∨ p.1 = q.2.1 := by
      have hm : p.1 ∈ ({q.1, q.2.1} : Finset ℕ) := he ▸ (by simp)
      simpa using hm
    have hb : q.1 = p.1 ∨ q.1 = p.2.1 := by
      have hm : q.1 ∈ ({p.1, p.2.1} : Finset ℕ) := he.symm ▸ (by simp)
      simpa using hm
    have hab : p.2.1 = q.1 ∨ p.2.1 = q.2.1 := by
      have hm : p.2.1 ∈ ({q.1, q.2.1} : Finset ℕ) := he ▸ (by simp)
      simpa using hm
    exact Prod.ext (by omega) (Prod.ext (by omega) hc)
  rw [← Finset.card_image_of_injOn hf]
  apply signed_sum_interval_card_bound h hA
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨ha, hb, hc, hab, hbc, hlo, hup⟩ := hT q hq
  have hab' : q.1 ≠ q.2.1 := ne_of_lt hab
  refine ⟨?_, ?_, hc, ?_, ?_, ?_⟩
  · intro x hx
    simp only [f, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · simp [f, hab']
  · simp only [f, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt (lt_trans hab hbc), ne_of_gt hbc⟩
  · simpa [f, Finset.sum_pair hab'] using hlo
  · simpa [f, Finset.sum_pair hab'] using hup

lemma interval_box_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H : ℕ) (hH : 0 < H) (S : ℕ → Finset ℕ)
    (hS : ∀ m a, a ∈ S m → a ∈ A ∧ m * H + 1 ≤ a ∧ a ≤ (m + 1) * H)
    (D : Finset (ℕ × ℕ)) (hD : ∀ p ∈ D, 1 ≤ p.1 ∧ p.1 < p.2) :
    ∑ p ∈ D, (S p.1).card * ((S p.2).card * (S (p.1 + p.2)).card) ≤
      5 * (3 * H + 1) := by
  classical
  let box : ℕ × ℕ → Finset (ℕ × ℕ × ℕ) :=
    fun p => S p.1 ×ˢ (S p.2 ×ˢ S (p.1 + p.2))
  have hindex : ∀ {m n a}, a ∈ S m → a ∈ S n → m = n := by
    intro m n a ham han
    obtain ⟨_, hmlo, hmhi⟩ := hS m a ham
    obtain ⟨_, hnlo, hnhi⟩ := hS n a han
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx := Nat.mul_le_mul_right H (show m + 1 ≤ n by omega)
      omega
    · have hx := Nat.mul_le_mul_right H (show n + 1 ≤ m by omega)
      omega
  have hdisj : (D : Set (ℕ × ℕ)).PairwiseDisjoint box := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro a hap haq
    obtain ⟨hpa, hpbc⟩ := Finset.mem_product.mp hap
    obtain ⟨hpb, hpc⟩ := Finset.mem_product.mp hpbc
    obtain ⟨hqa, hqbc⟩ := Finset.mem_product.mp haq
    obtain ⟨hqb, hqc⟩ := Finset.mem_product.mp hqbc
    exact hpq (Prod.ext (hindex hpa hqa) (hindex hpb hqb))
  have hcard : (D.biUnion box).card =
      ∑ p ∈ D, (S p.1).card * ((S p.2).card * (S (p.1 + p.2)).card) := by
    rw [Finset.card_biUnion hdisj]
    simp [box, Finset.card_product]
  rw [← hcard]
  have hb := sorted_triples_interval_card_bound h hA (-(H : ℤ)) (2 * (H : ℤ))
    (D.biUnion box) (by
      intro a ha
      obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨ham, hanc⟩ := Finset.mem_product.mp hap
      obtain ⟨han, hac⟩ := Finset.mem_product.mp hanc
      obtain ⟨hma, hmlo, hmhi⟩ := hS p.1 a.1 ham
      obtain ⟨hna, hnlo, hnhi⟩ := hS p.2 a.2.1 han
      obtain ⟨hca, hclo, hchi⟩ := hS (p.1 + p.2) a.2.2 hac
      obtain ⟨hp1, hp2⟩ := hD p hp
      have hmn := Nat.mul_le_mul_right H (show p.1 + 1 ≤ p.2 by omega)
      have hnc := Nat.mul_le_mul_right H (show p.2 + 1 ≤ p.1 + p.2 by omega)
      refine ⟨hma, hna, hca, by omega, by omega, ?_, ?_⟩
      · have hlow : a.2.2 ≤ a.1 + a.2.1 + H := by nlinarith
        have hlow' : (a.2.2 : ℤ) ≤ (a.1 : ℤ) + (a.2.1 : ℤ) + (H : ℤ) := by exact_mod_cast hlow
        omega
      · have hupp : a.1 + a.2.1 ≤ a.2.2 + 2 * H := by nlinarith
        have hupp' : (a.1 : ℤ) + (a.2.1 : ℤ) ≤ (a.2.2 : ℤ) + 2 * (H : ℤ) := by exact_mod_cast hupp
        omega)
  convert hb using 1; omega



noncomputable def initialSegment (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (· ∈ A)

lemma mem_initialSegment {A : Set ℕ} {N a : ℕ} :
    a ∈ initialSegment A N ↔ a ∈ A ∧ 1 ≤ a ∧ a ≤ N := by
  classical
  simp [initialSegment, and_comm, and_left_comm]

lemma card_initialSegment (A : Set ℕ) (N : ℕ) :
    (initialSegment A N).card = (A ∩ Icc 1 N).ncard := by
  have he : (initialSegment A N : Set ℕ) = A ∩ Icc 1 N := by
    ext a
    simp [mem_initialSegment]
  rw [← he]
  simp

lemma initialSegment_mono (A : Set ℕ) {M N : ℕ} (hMN : M ≤ N) :
    initialSegment A M ⊆ initialSegment A N := by
  intro a ha
  rw [mem_initialSegment] at ha ⊢
  exact ⟨ha.1, ha.2.1, ha.2.2.trans hMN⟩

noncomputable def intervalBin (A : Set ℕ) (H m : ℕ) : Finset ℕ :=
  initialSegment A ((m + 1) * H) \ initialSegment A (m * H)

lemma mem_intervalBin {A : Set ℕ} {H m a : ℕ} :
    a ∈ intervalBin A H m ↔ a ∈ A ∧ m * H + 1 ≤ a ∧ a ≤ (m + 1) * H := by
  classical
  simp only [intervalBin, Finset.mem_sdiff, mem_initialSegment]
  constructor
  · rintro ⟨⟨ha, h1, hu⟩, hl⟩
    refine ⟨ha, ?_, hu⟩
    by_contra hn
    exact hl ⟨ha, h1, by omega⟩
  · rintro ⟨ha, hl, hu⟩
    refine ⟨⟨ha, by omega, hu⟩, ?_⟩
    rintro ⟨_, _, hn⟩
    omega

lemma card_intervalBin (A : Set ℕ) (H m : ℕ) :
    ((intervalBin A H m).card : ℝ) =
      ((initialSegment A ((m + 1) * H)).card : ℝ) -
        ((initialSegment A (m * H)).card : ℝ) := by
  have hh := Finset.card_sdiff_add_card_eq_card
    (initialSegment_mono A (Nat.mul_le_mul_right H (Nat.le_succ m)))
  change (intervalBin A H m).card + (initialSegment A (m * H)).card =
    (initialSegment A ((m + 1) * H)).card at hh
  have hh' : ((intervalBin A H m).card : ℝ) +
      ((initialSegment A (m * H)).card : ℝ) =
      ((initialSegment A ((m + 1) * H)).card : ℝ) := by exact_mod_cast hh
  linarith

lemma scaled_initialSegment_tendsto {A : Set ℕ} {c : ℝ}
    (hc : Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ))
      atTop (nhds c)) (m : ℕ) :
    Tendsto (fun N => ((initialSegment A (m * N)).card : ℝ) / (N : ℝ)^(1/3 : ℝ))
      atTop (nhds (c * (m : ℝ)^(1/3 : ℝ))) := by
  by_cases hm : m = 0
  · subst m
    simp [initialSegment]
  have hmt : Tendsto (fun N : ℕ => m * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hm)) tendsto_id
  have ht := (hc.comp hmt).mul_const ((m : ℝ)^(1/3 : ℝ))
  apply ht.congr'
  filter_upwards [] with N
  dsimp only [Function.comp_def]
  rw [← card_initialSegment A, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  have hm' : (m : ℝ)^(1/3 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) _)
  rw [div_mul_eq_mul_div, mul_comm ((m : ℝ)^(1/3 : ℝ)), mul_div_mul_right _ _ hm']

lemma scaled_intervalBin_tendsto {A : Set ℕ} {c : ℝ}
    (hc : Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ))
      atTop (nhds c)) (m : ℕ) :
    Tendsto (fun N => ((intervalBin A N m).card : ℝ) / (N : ℝ)^(1/3 : ℝ))
      atTop (nhds (c * (((m + 1 : ℕ) : ℝ)^(1/3 : ℝ) - (m : ℝ)^(1/3 : ℝ)))) := by
  convert (scaled_initialSegment_tendsto hc (m + 1)).sub
    (scaled_initialSegment_tendsto hc m) using 1
  · ext N
    rw [card_intervalBin, sub_div]
  · congr 1
    ring

lemma interval_profile_bound {A : Set ℕ} (h : NtupleCondition A 3) (hA : A.Infinite)
    {c : ℝ} (hc : Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ))
      atTop (nhds c)) (D : Finset (ℕ × ℕ)) (hD : ∀ p ∈ D, 1 ≤ p.1 ∧ p.1 < p.2) :
    ∑ p ∈ D, (c * (((p.1 + 1 : ℕ) : ℝ)^(1/3 : ℝ) - (p.1 : ℝ)^(1/3 : ℝ))) *
      ((c * (((p.2 + 1 : ℕ) : ℝ)^(1/3 : ℝ) - (p.2 : ℝ)^(1/3 : ℝ))) *
      (c * (((p.1 + p.2 + 1 : ℕ) : ℝ)^(1/3 : ℝ) - ((p.1 + p.2 : ℕ) : ℝ)^(1/3 : ℝ)))) ≤ 15 := by
  have ht := tendsto_finset_sum D (fun p _ => (scaled_intervalBin_tendsto hc p.1).mul
    ((scaled_intervalBin_tendsto hc p.2).mul (scaled_intervalBin_tendsto hc (p.1 + p.2))))
  have hu : Tendsto (fun N : ℕ => (15 : ℝ) + 5 * (N : ℝ)⁻¹) atTop (nhds 15) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (5 : ℝ))
  apply le_of_tendsto_of_tendsto ht hu
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNc : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : ((N : ℝ)^(1/3 : ℝ))^3 = N := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hb := interval_box_count_bound h hA N (by omega) (intervalBin A N)
    (fun m a ha => mem_intervalBin.mp ha) D hD
  have hb' : ∑ p ∈ D, ((intervalBin A N p.1).card : ℝ) *
      (((intervalBin A N p.2).card : ℝ) * ((intervalBin A N (p.1 + p.2)).card : ℝ)) ≤
      5 * (3 * (N : ℝ) + 1) := by exact_mod_cast hb
  calc
    ∑ p ∈ D, ((intervalBin A N p.1).card : ℝ) / (N : ℝ)^(1/3 : ℝ) *
        (((intervalBin A N p.2).card : ℝ) / (N : ℝ)^(1/3 : ℝ) *
        (((intervalBin A N (p.1 + p.2)).card : ℝ) / (N : ℝ)^(1/3 : ℝ))) =
      (∑ p ∈ D, ((intervalBin A N p.1).card : ℝ) *
        (((intervalBin A N p.2).card : ℝ) * ((intervalBin A N (p.1 + p.2)).card : ℝ))) / N := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = (((intervalBin A N p.1).card : ℝ) *
          (((intervalBin A N p.2).card : ℝ) * ((intervalBin A N (p.1 + p.2)).card : ℝ))) /
          ((N : ℝ)^(1/3 : ℝ))^3 := by ring
        _ = _ := by rw [hroot]
    _ ≤ (5 * (3 * (N : ℝ) + 1)) / N := (div_le_div_iff_of_pos_right hNc).mpr hb'
    _ = 15 + 5 * (N : ℝ)⁻¹ := by field_simp; ring



noncomputable def cubeRootIncrement (m : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ)^(1/3 : ℝ) - (m : ℝ)^(1/3 : ℝ)

lemma cubeRootIncrement_nonneg (m : ℕ) : 0 ≤ cubeRootIncrement m := by
  apply sub_nonneg.mpr
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_succ m) (by norm_num)

lemma cubeRootIncrement_lower (i m : ℕ) (hm : m + 1 ≤ 8^(i + 1)) :
    1 ≤ (12 * (4 : ℝ)^i) * cubeRootIncrement m := by
  let a := ((m + 1 : ℕ) : ℝ)^(1/3 : ℝ)
  let b := (m : ℝ)^(1/3 : ℝ)
  let q := (2 : ℝ)^(i + 1)
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hq0 : 0 ≤ q := by positivity
  have ha3 : a^3 = (m : ℝ) + 1 := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hb3 : b^3 = (m : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hq3 : q^3 = (8 : ℝ)^(i + 1) := by
    dsimp [q]
    rw [pow_right_comm]
    norm_num
  have hba : b ≤ a := Real.rpow_le_rpow (by positivity)
    (by exact_mod_cast Nat.le_succ m) (by norm_num)
  have haq : a ≤ q := by
    apply (pow_le_pow_iff_left₀ ha0 hq0 (by decide : (3 : ℕ) ≠ 0)).mp
    rw [ha3, hq3]
    exact_mod_cast hm
  have hbq : b ≤ q := hba.trans haq
  have hsum : a^2 + a*b + b^2 ≤ 3*q^2 := by
    have h1 := (sq_le_sq₀ ha0 hq0).mpr haq
    have h2 := (sq_le_sq₀ hb0 hq0).mpr hbq
    have h3 := mul_le_mul haq hbq hb0 hq0
    nlinarith
  have heq : (a-b)*(a^2+a*b+b^2) = 1 := by nlinarith [ha3, hb3]
  have hbnd := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hba)
  have hq2 : q^2 = 4 * (4 : ℝ)^i := by
    dsimp [q]
    rw [pow_right_comm]
    norm_num [pow_succ]
    ring
  change 1 ≤ (12 * (4 : ℝ)^i) * (a-b)
  rw [hq2] at hbnd
  nlinarith

def indexBlock (i : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Ico (8^i) (2*8^i) ×ˢ Finset.Ico (2*8^i) (3*8^i)

lemma mem_indexBlock {i m n : ℕ} : (m,n) ∈ indexBlock i ↔
    8^i ≤ m ∧ m < 2*8^i ∧ 2*8^i ≤ n ∧ n < 3*8^i := by
  simp only [indexBlock, Finset.mem_product, Finset.mem_Ico]
  tauto

lemma indexBlock_ordered {i : ℕ} {p : ℕ × ℕ} (hp : p ∈ indexBlock i) :
    1 ≤ p.1 ∧ p.1 < p.2 := by
  obtain ⟨hmlo, hmhi, hnlo, hnhi⟩ := mem_indexBlock.mp hp
  have hpow := Nat.one_le_pow i 8 (by decide)
  omega

lemma indexBlock_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (indexBlock i) (indexBlock j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨hmlo, hmhi, hnlo, hnhi⟩ := mem_indexBlock.mp hp
  obtain ⟨hmlo', hmhi', hnlo', hnhi'⟩ := mem_indexBlock.mp hq
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hx := Nat.pow_le_pow_right (by decide : 0 < 8) (Nat.succ_le_of_lt hij)
    rw [pow_succ] at hx
    omega
  · have hx := Nat.pow_le_pow_right (by decide : 0 < 8) (Nat.succ_le_of_lt hji)
    rw [pow_succ] at hx
    omega

lemma card_indexBlock (i : ℕ) : (indexBlock i).card = (8^i)^2 := by
  simp only [indexBlock, Finset.card_product, Nat.card_Ico]
  have h1 : 2*8^i - 8^i = 8^i := by omega
  have h2 : 3*8^i - 2*8^i = 8^i := by omega
  rw [h1, h2]
  ring

lemma indexBlock_increment_lower (i : ℕ) :
    (1 : ℝ) / 1728 ≤ ∑ p ∈ indexBlock i,
      cubeRootIncrement p.1 * (cubeRootIncrement p.2 * cubeRootIncrement (p.1 + p.2)) := by
  let w := (12 * (4 : ℝ)^i)^3
  have hw : ∀ p ∈ indexBlock i, 1 ≤ w *
      (cubeRootIncrement p.1 * (cubeRootIncrement p.2 * cubeRootIncrement (p.1 + p.2))) := by
    intro p hp
    obtain ⟨hmlo, hmhi, hnlo, hnhi⟩ := mem_indexBlock.mp hp
    have hx : 8^(i + 1) = 8^i * 8 := pow_succ _ _
    have h1 := cubeRootIncrement_lower i p.1 (by omega)
    have h2 := cubeRootIncrement_lower i p.2 (by omega)
    have h3 := cubeRootIncrement_lower i (p.1 + p.2) (by omega)
    have h12 : 1 ≤ ((12 * (4 : ℝ)^i) * cubeRootIncrement p.1) *
        ((12 * (4 : ℝ)^i) * cubeRootIncrement p.2) :=
      one_le_mul_of_one_le_of_one_le h1 h2
    have h123 := one_le_mul_of_one_le_of_one_le h12 h3
    dsimp [w]
    nlinarith only [h123]
  have hh := Finset.sum_le_sum hw
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum, card_indexBlock,
    Nat.cast_pow, Nat.cast_ofNat] at hh
  have hpow : ((4 : ℝ)^i)^3 = ((8 : ℝ)^i)^2 := by
    rw [pow_right_comm 4 i 3, pow_right_comm 8 i 2]
    norm_num
  have he : w = 1728 * ((8 : ℝ)^i)^2 := by
    dsimp [w]
    rw [mul_pow, hpow]
    norm_num
  rw [he] at hh
  have hpos : 0 < ((8 : ℝ)^i)^2 := by positivity
  have hh' : 1 ≤ 1728 * ∑ p ∈ indexBlock i,
      cubeRootIncrement p.1 * (cubeRootIncrement p.2 * cubeRootIncrement (p.1 + p.2)) := by
    apply (mul_le_mul_iff_of_pos_left hpos).mp
    nlinarith only [hh]
  linarith

/-- A conditional consequence: if the normalized counting function converges,
its limit must be zero. This does not assume or establish convergence. -/
lemma density_limit_eq_zero {A : Set ℕ} (h : NtupleCondition A 3) (hA : A.Infinite)
    {c : ℝ} (hc : Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ))
      atTop (nhds c)) : c = 0 := by
  have hc0 : 0 ≤ c := ge_of_tendsto hc (Eventually.of_forall (density_nonneg A))
  have hb : ∀ K : ℕ, (K : ℝ) * c^3 ≤ 25920 := by
    intro K
    let D := (Finset.range K).biUnion indexBlock
    have hdisj : (Finset.range K : Set ℕ).PairwiseDisjoint indexBlock := by
      intro i hi j hj hij
      exact indexBlock_disjoint hij
    have hD : ∀ p ∈ D, 1 ≤ p.1 ∧ p.1 < p.2 := by
      intro p hp
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
      exact indexBlock_ordered hpi
    have hupper := interval_profile_bound h hA hc D hD
    change ∑ p ∈ D, (c * cubeRootIncrement p.1) *
      ((c * cubeRootIncrement p.2) * (c * cubeRootIncrement (p.1 + p.2))) ≤ 15 at hupper
    have hsum : ∑ p ∈ D, (c * cubeRootIncrement p.1) *
        ((c * cubeRootIncrement p.2) * (c * cubeRootIncrement (p.1 + p.2))) =
        c^3 * ∑ i ∈ Finset.range K, ∑ p ∈ indexBlock i,
          cubeRootIncrement p.1 * (cubeRootIncrement p.2 * cubeRootIncrement (p.1 + p.2)) := by
      rw [Finset.mul_sum]
      change (∑ p ∈ (Finset.range K).biUnion indexBlock, _) = _
      rw [Finset.sum_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [hsum] at hupper
    have hlower : (K : ℝ) / 1728 ≤ ∑ i ∈ Finset.range K, ∑ p ∈ indexBlock i,
        cubeRootIncrement p.1 * (cubeRootIncrement p.2 * cubeRootIncrement (p.1 + p.2)) := by
      simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.range K) => indexBlock_increment_lower i)
    have hmul := mul_le_mul_of_nonneg_left hlower (show 0 ≤ c^3 by positivity)
    nlinarith
  by_contra hne
  have hpos : 0 < c^3 := pow_pos (lt_of_le_of_ne hc0 (Ne.symm hne)) _
  obtain ⟨K, hK⟩ := exists_nat_gt ((25920 : ℝ) / c^3)
  have hk' : 25920 < (K : ℝ) * c^3 := (div_lt_iff₀ hpos).mp hK
  exact (not_lt_of_ge (hb K)) hk'


/-- The prefix count controls the number of short differences in the tail, without
assuming convergence of the normalized counting function. -/
lemma short_difference_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H : ℕ) (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ A ∧ H < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ p.1 + H) :
    (A ∩ Icc 1 H).ncard * P.card ≤ 5 * (2 * H + 1) := by
  have hb := sorted_triples_interval_card_bound h hA (-(H : ℤ)) (H : ℤ)
    (initialSegment A H ×ˢ P) (by
      intro p hp
      obtain ⟨hs, hpP⟩ := Finset.mem_product.mp hp
      obtain ⟨hsA, hslo, hshi⟩ := mem_initialSegment.mp hs
      obtain ⟨haA, hbA, hHa, hab, hbhi⟩ := hP p.2 hpP
      refine ⟨hsA, haA, hbA, by omega, hab, ?_, ?_⟩ <;> omega)
  rw [Finset.card_product, card_initialSegment] at hb
  convert hb using 1; omega

/-- The same bound for any finite collection of pairs lying in common width-`H` bins. -/
lemma tail_bin_pair_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H : ℕ) (D : Finset ℕ) (hD : ∀ m ∈ D, 1 ≤ m) :
    (A ∩ Icc 1 H).ncard *
      (∑ m ∈ D, (intervalBin A H m).card.choose 2) ≤ 5 * (2 * H + 1) := by
  classical
  let pairs := fun m => ((intervalBin A H m) ×ˢ (intervalBin A H m)).filter
    (fun p : ℕ × ℕ => p.1 < p.2)
  have hindex : ∀ {m n a}, a ∈ intervalBin A H m → a ∈ intervalBin A H n → m = n := by
    intro m n a ham han
    obtain ⟨_, hmlo, hmhi⟩ := mem_intervalBin.mp ham
    obtain ⟨_, hnlo, hnhi⟩ := mem_intervalBin.mp han
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx := Nat.mul_le_mul_right H (show m + 1 ≤ n by omega)
      omega
    · have hx := Nat.mul_le_mul_right H (show n + 1 ≤ m by omega)
      omega
  have hdisj : (D : Set ℕ).PairwiseDisjoint pairs := by
    intro m hm n hn hmn
    apply Finset.disjoint_left.mpr
    intro p hpm hpn
    have hm' := (Finset.mem_product.mp (Finset.mem_filter.mp hpm).1).1
    have hn' := (Finset.mem_product.mp (Finset.mem_filter.mp hpn).1).1
    exact hmn (hindex hm' hn')
  have hpairs : ∀ m, (pairs m).card = (intervalBin A H m).card.choose 2 := by
    intro m
    let f : ℕ × ℕ → Finset ℕ := fun p => {p.1, p.2}
    have hmaps : Set.MapsTo f (pairs m : Set (ℕ × ℕ))
        ((intervalBin A H m).powersetCard 2 : Set (Finset ℕ)) := by
      intro p hp
      obtain ⟨hpm, hpord⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hpm
      change f p ∈ (intervalBin A H m).powersetCard 2
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, ?_⟩
      · intro a ha
        simp only [f, Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hpa
        · exact hpb
      · simp [f, ne_of_lt hpord]
    have hinj : Set.InjOn f (pairs m : Set (ℕ × ℕ)) := by
      intro p hp q hq he
      have hpord := (Finset.mem_filter.mp hp).2
      have hqord := (Finset.mem_filter.mp hq).2
      change ({p.1, p.2} : Finset ℕ) = {q.1, q.2} at he
      have h1 : p.1 = q.1 ∨ p.1 = q.2 := by
        have hx : p.1 ∈ ({q.1, q.2} : Finset ℕ) := he ▸ (by simp)
        simpa using hx
      have h2 : q.1 = p.1 ∨ q.1 = p.2 := by
        have hx : q.1 ∈ ({p.1, p.2} : Finset ℕ) := he.symm ▸ (by simp)
        simpa using hx
      have h3 : p.2 = q.1 ∨ p.2 = q.2 := by
        have hx : p.2 ∈ ({q.1, q.2} : Finset ℕ) := he ▸ (by simp)
        simpa using hx
      exact Prod.ext (by omega) (by omega)
    have hsurj : Set.SurjOn f (pairs m : Set (ℕ × ℕ))
        ((intervalBin A H m).powersetCard 2 : Set (Finset ℕ)) := by
      intro I hI
      change I ∈ (intervalBin A H m).powersetCard 2 at hI
      obtain ⟨hIS, hIc⟩ := Finset.mem_powersetCard.mp hI
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hIc
      have ha : a ∈ intervalBin A H m := hIS (by simp)
      have hb : b ∈ intervalBin A H m := hIS (by simp)
      rcases lt_or_gt_of_ne hab with hab | hba
      · exact ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hab⟩, rfl⟩
      · refine ⟨(b,a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb,ha⟩, hba⟩, ?_⟩
        simp [f, Finset.pair_comm]
    simpa using le_antisymm (Finset.card_le_card_of_injOn f hmaps hinj)
      (Finset.card_le_card_of_surjOn f hsurj)
  have hb := short_difference_count_bound h hA H (D.biUnion pairs) (by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpS, hpord⟩ := Finset.mem_filter.mp hpm
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hpS
    obtain ⟨haA, halo, hahi⟩ := mem_intervalBin.mp hpa
    obtain ⟨hbA, hblo, hbhi⟩ := mem_intervalBin.mp hpb
    have hm1 := hD m hm
    have hHm : H ≤ m * H := Nat.le_mul_of_pos_left H hm1
    refine ⟨haA, hbA, by omega, hpord, ?_⟩
    nlinarith)
  simpa only [Finset.card_biUnion hdisj, hpairs] using hb



lemma normalized_prefix_eq (A : Set ℕ) (H m : ℕ) :
    ((initialSegment A (m * H)).card : ℝ) / (H : ℝ)^(1/3 : ℝ) =
      ((A ∩ Icc 1 (m * H)).ncard / ((m * H : ℕ) : ℝ)^(1/3 : ℝ)) *
        (m : ℝ)^(1/3 : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simp [initialSegment]
  rw [← card_initialSegment A, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  have hm' : (m : ℝ)^(1/3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) _)
  rw [div_mul_eq_mul_div, mul_comm ((m : ℝ)^(1/3 : ℝ)), mul_div_mul_right _ _ hm']

lemma normalized_prefix_le {A : Set ℕ} (h : NtupleCondition A 3) (H m : ℕ) (hH : 1 ≤ H) :
    ((initialSegment A (m * H)).card : ℝ) / (H : ℝ)^(1/3 : ℝ) ≤
      5 * (m : ℝ)^(1/3 : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simp [initialSegment]
  rw [normalized_prefix_eq]
  exact mul_le_mul_of_nonneg_right (density_le_five h (by
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm
    nlinarith)) (by positivity)

/-- A hypothetical counterexample has a subsequential prefix profile. No convergence
of the original normalized counting function is assumed here. -/
lemma exists_prefix_scaling_limit {A : Set ℕ} (h : NtupleCondition A 3)
    {ε : ℝ} (M : ℕ)
    (hlow : ∀ N ≥ M, ε ≤ (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) :
    ∃ (F : ℕ → ℝ) (τ : ℕ → ℕ), StrictMono τ ∧
      (∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
        ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m))) ∧
      F 0 = 0 ∧ Monotone F ∧
      (∀ m : ℕ, ε * (m : ℝ)^(1/3 : ℝ) ≤ F m ∧ F m ≤ 5 * (m : ℝ)^(1/3 : ℝ)) := by
  let f : ℕ → ℕ → ℝ := fun n m => ((initialSegment A (m * (n + 1))).card : ℝ) /
    ((n + 1 : ℕ) : ℝ)^(1/3 : ℝ)
  let s : Set (ℕ → ℝ) := {F | ∀ m : ℕ, F m ∈ Icc 0 (5 * (m : ℝ)^(1/3 : ℝ))}
  have hs : IsCompact s := isCompact_pi_infinite (fun m => isCompact_Icc)
  have hf : ∀ n, f n ∈ s := by
    intro n m
    exact ⟨by positivity, normalized_prefix_le h (n+1) m (by omega)⟩
  obtain ⟨F, hFs, τ, hτ, hlim⟩ := hs.tendsto_subseq hf
  have hlim' : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m)) := fun m => hlim.apply_nhds m
  have hzero : F 0 = 0 := by
    have hz := hlim' 0
    simp only [zero_mul, initialSegment, Finset.Icc_eq_empty_of_lt (by decide : 0 < 1),
      Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_div] at hz
    exact tendsto_nhds_unique hz tendsto_const_nhds
  refine ⟨F, τ, hτ, hlim', hzero, ?_, ?_⟩
  · intro i j hij
    apply le_of_tendsto_of_tendsto (hlim' i) (hlim' j)
    filter_upwards [] with n
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (initialSegment_mono A (Nat.mul_le_mul_right _ hij))
  · intro m
    refine ⟨?_, (hFs m).2⟩
    by_cases hm : m = 0
    · subst m
      simp [hzero]
    apply ge_of_tendsto (hlim' m)
    have hτlim : Tendsto (fun n => τ n + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hτ.tendsto_atTop
    filter_upwards [hτlim.eventually (eventually_ge_atTop M)] with n hn
    rw [normalized_prefix_eq]
    have hmul : M ≤ m * (τ n + 1) := hn.trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm))
    exact mul_le_mul_of_nonneg_right (hlow _ hmul) (by positivity)

lemma scaling_limit_intervalBin {A : Set ℕ} {F : ℕ → ℝ} {τ : ℕ → ℕ}
    (hlim : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m))) (m : ℕ) :
    Tendsto (fun n => ((intervalBin A (τ n + 1) m).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F (m+1) - F m)) := by
  convert (hlim (m+1)).sub (hlim m) using 1
  ext n
  rw [card_intervalBin, sub_div]

lemma scaling_limit_box_bound {A : Set ℕ} (h : NtupleCondition A 3) (hA : A.Infinite)
    {F : ℕ → ℝ} {τ : ℕ → ℕ} (hτ : StrictMono τ)
    (hlim : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m)))
    (D : Finset (ℕ × ℕ)) (hD : ∀ p ∈ D, 1 ≤ p.1 ∧ p.1 < p.2) :
    ∑ p ∈ D, (F (p.1+1) - F p.1) *
      ((F (p.2+1) - F p.2) * (F (p.1+p.2+1) - F (p.1+p.2))) ≤ 15 := by
  have ht := tendsto_finset_sum D (fun p _ => (scaling_limit_intervalBin hlim p.1).mul
    ((scaling_limit_intervalBin hlim p.2).mul (scaling_limit_intervalBin hlim (p.1+p.2))))
  have hτlim : Tendsto (fun n => τ n + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hτ.tendsto_atTop
  have hu : Tendsto (fun n => (15 : ℝ) + 5 * ((τ n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 15) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hτlim)).const_mul (5 : ℝ))
  apply le_of_tendsto_of_tendsto ht hu
  filter_upwards [] with n
  let H := τ n + 1
  have hH : 0 < H := Nat.succ_pos _
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hroot : ((H : ℝ)^(1/3 : ℝ))^3 = H := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hb := interval_box_count_bound h hA H hH (intervalBin A H)
    (fun m a ha => mem_intervalBin.mp ha) D hD
  have hb' : ∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) *
      (((intervalBin A H p.2).card : ℝ) * ((intervalBin A H (p.1+p.2)).card : ℝ)) ≤
      5 * (3 * (H : ℝ) + 1) := by exact_mod_cast hb
  change (∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) / (H : ℝ)^(1/3 : ℝ) *
    (((intervalBin A H p.2).card : ℝ) / (H : ℝ)^(1/3 : ℝ) *
      (((intervalBin A H (p.1+p.2)).card : ℝ) / (H : ℝ)^(1/3 : ℝ)))) ≤ 15 + 5 * (H : ℝ)⁻¹
  calc
    _ = (∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) *
      (((intervalBin A H p.2).card : ℝ) * ((intervalBin A H (p.1+p.2)).card : ℝ))) / H := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = (((intervalBin A H p.1).card : ℝ) *
          (((intervalBin A H p.2).card : ℝ) * ((intervalBin A H (p.1+p.2)).card : ℝ))) /
          ((H : ℝ)^(1/3 : ℝ))^3 := by ring
        _ = _ := by rw [hroot]
    _ ≤ (5 * (3 * (H : ℝ) + 1)) / H := (div_le_div_iff_of_pos_right hHr).mpr hb'
    _ = 15 + 5 * (H : ℝ)⁻¹ := by field_simp; ring



lemma square_eq_twice_choose_two_add (k : ℕ) : k^2 = 2 * k.choose 2 + k := by
  have hf := Nat.descFactorial_eq_factorial_mul_choose k 2
  have he : k * (k-1) = 2 * k.choose 2 := by
    simpa [Nat.descFactorial_succ, Nat.factorial, mul_comm] using hf
  by_cases hk : k = 0
  · subst k
    simp
  have hk' : k-1+1 = k := by omega
  nlinarith

lemma tail_bin_square_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H : ℕ) (D : Finset ℕ) (hD : ∀ m ∈ D, 1 ≤ m) :
    (A ∩ Icc 1 H).ncard * (∑ m ∈ D, (intervalBin A H m).card^2) ≤
      10 * (2 * H + 1) + (A ∩ Icc 1 H).ncard * (∑ m ∈ D, (intervalBin A H m).card) := by
  have hb := tail_bin_pair_count_bound h hA H D hD
  simp_rw [square_eq_twice_choose_two_add]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith

lemma tail_bin_normalized_square_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H : ℕ) (hH : 0 < H) (D : Finset ℕ) (hD : ∀ m ∈ D, 1 ≤ m) :
    ((initialSegment A H).card / (H : ℝ)^(1/3 : ℝ)) *
      (∑ m ∈ D, (((intervalBin A H m).card : ℝ) / (H : ℝ)^(1/3 : ℝ))^2) ≤
      20 + 10 * (H : ℝ)⁻¹ +
      ((initialSegment A H).card / (H : ℝ)^(1/3 : ℝ)) *
        (∑ m ∈ D, ((intervalBin A H m).card : ℝ) / (H : ℝ)^(1/3 : ℝ)) *
          ((H : ℝ)^(1/3 : ℝ))⁻¹ := by
  have hb := tail_bin_square_count_bound h hA H D hD
  rw [← card_initialSegment] at hb
  have hb' : ((initialSegment A H).card : ℝ) *
      (∑ m ∈ D, ((intervalBin A H m).card : ℝ)^2) ≤ 10 * (2 * (H : ℝ) + 1) +
      ((initialSegment A H).card : ℝ) * (∑ m ∈ D, ((intervalBin A H m).card : ℝ)) := by exact_mod_cast hb
  let r := (H : ℝ)^(1/3 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos (by exact_mod_cast hH) _
  have hr3 : r^3 = (H : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  change ((initialSegment A H).card / r) *
      (∑ m ∈ D, (((intervalBin A H m).card : ℝ) / r)^2) ≤
      20 + 10 * (H : ℝ)⁻¹ + ((initialSegment A H).card / r) *
        (∑ m ∈ D, ((intervalBin A H m).card : ℝ) / r) * r⁻¹
  simp_rw [div_pow]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have heq1 (a b : ℝ) : (a/r)*(b/r^2) = a*b/(H : ℝ) := by
    rw [← hr3]
    ring
  have heq2 (a b : ℝ) : (a/r)*(b/r)*r⁻¹ = a*b/(H : ℝ) := by
    rw [← hr3]
    ring
  rw [heq1, heq2]
  calc
    _ ≤ (10 * (2 * (H : ℝ) + 1) + ((initialSegment A H).card : ℝ) *
        (∑ m ∈ D, ((intervalBin A H m).card : ℝ))) / H :=
      (div_le_div_iff_of_pos_right hHr).mpr hb'
    _ = _ := by field_simp; ring

lemma scaling_limit_square_bound {A : Set ℕ} (h : NtupleCondition A 3) (hA : A.Infinite)
    {F : ℕ → ℝ} {τ : ℕ → ℕ} (hτ : StrictMono τ)
    (hlim : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m)))
    (D : Finset ℕ) (hD : ∀ m ∈ D, 1 ≤ m) :
    F 1 * (∑ m ∈ D, (F (m+1) - F m)^2) ≤ 20 := by
  have hτlim : Tendsto (fun n => τ n + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hτ.tendsto_atTop
  have hcast : Tendsto (fun n => ((τ n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hτlim
  have hroot : Tendsto (fun n => (((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp hcast)
  have hprefix : Tendsto (fun n => ((initialSegment A (τ n + 1)).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F 1)) := by simpa using hlim 1
  have hsum := tendsto_finset_sum D (fun m _ => scaling_limit_intervalBin hlim m)
  have hsquare := tendsto_finset_sum D (fun m _ => (scaling_limit_intervalBin hlim m).pow 2)
  have hupper : Tendsto (fun n => (20 : ℝ) + 10 * ((τ n + 1 : ℕ) : ℝ)⁻¹ +
      (((initialSegment A (τ n + 1)).card : ℝ) / ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) *
      (∑ m ∈ D, ((intervalBin A (τ n + 1) m).card : ℝ) / ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) *
        (((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ))⁻¹) atTop (nhds 20) := by
    simpa using (tendsto_const_nhds.add ((tendsto_inv_atTop_zero.comp hcast).const_mul (10 : ℝ))).add
      ((hprefix.mul hsum).mul hroot)
  apply le_of_tendsto_of_tendsto (hprefix.mul hsquare) hupper
  exact Eventually.of_forall (fun n => tail_bin_normalized_square_bound h hA (τ n + 1) (by omega) D hD)

lemma scaling_limit_increments_square_summable {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    {F : ℕ → ℝ} {τ : ℕ → ℕ} (hτ : StrictMono τ)
    (hlim : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m)))
    (hF : 0 < F 1) : Summable (fun m : ℕ => (F (m+2) - F (m+1))^2) := by
  apply summable_of_sum_le (c := 20 / F 1) (fun _ => sq_nonneg _)
  intro D
  have hb := scaling_limit_square_bound h hA hτ hlim (D.image (·+1)) (by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    omega)
  rw [Finset.sum_image] at hb
  · apply (le_div_iff₀ hF).mpr
    simpa [mul_comm] using hb
  · intro i hi j hj he
    change i + 1 = j + 1 at he
    omega



lemma shifted_interval_box_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H k : ℕ) (S : ℕ → Finset ℕ)
    (hS : ∀ m a, a ∈ S m → a ∈ A ∧ m * H + 1 ≤ a ∧ a ≤ (m + 1) * H)
    (D : Finset (ℕ × ℕ)) (hD : ∀ p ∈ D, 1 ≤ p.1 ∧ p.1 < p.2) :
    ∑ p ∈ D, (S p.1).card * ((S p.2).card * (S (p.1 + p.2 + k)).card) ≤
      5 * (3 * H + 1) := by
  classical
  let box : ℕ × ℕ → Finset (ℕ × ℕ × ℕ) :=
    fun p => S p.1 ×ˢ (S p.2 ×ˢ S (p.1 + p.2 + k))
  have hindex : ∀ {m n a}, a ∈ S m → a ∈ S n → m = n := by
    intro m n a ham han
    obtain ⟨_, hmlo, hmhi⟩ := hS m a ham
    obtain ⟨_, hnlo, hnhi⟩ := hS n a han
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx := Nat.mul_le_mul_right H (show m + 1 ≤ n by omega)
      omega
    · have hx := Nat.mul_le_mul_right H (show n + 1 ≤ m by omega)
      omega
  have hdisj : (D : Set (ℕ × ℕ)).PairwiseDisjoint box := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro a hap haq
    obtain ⟨hpa, hpbc⟩ := Finset.mem_product.mp hap
    obtain ⟨hpb, hpc⟩ := Finset.mem_product.mp hpbc
    obtain ⟨hqa, hqbc⟩ := Finset.mem_product.mp haq
    obtain ⟨hqb, hqc⟩ := Finset.mem_product.mp hqbc
    exact hpq (Prod.ext (hindex hpa hqa) (hindex hpb hqb))
  have hcard : (D.biUnion box).card =
      ∑ p ∈ D, (S p.1).card * ((S p.2).card * (S (p.1 + p.2 + k)).card) := by
    rw [Finset.card_biUnion hdisj]
    simp [box, Finset.card_product]
  rw [← hcard]
  have hb := sorted_triples_interval_card_bound h hA (-((k : ℤ) + 1) * (H : ℤ)) ((2 - (k : ℤ)) * (H : ℤ))
    (D.biUnion box) (by
      intro a ha
      obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨ham, hanc⟩ := Finset.mem_product.mp hap
      obtain ⟨han, hac⟩ := Finset.mem_product.mp hanc
      obtain ⟨hma, hmlo, hmhi⟩ := hS p.1 a.1 ham
      obtain ⟨hna, hnlo, hnhi⟩ := hS p.2 a.2.1 han
      obtain ⟨hca, hclo, hchi⟩ := hS (p.1 + p.2 + k) a.2.2 hac
      obtain ⟨hp1, hp2⟩ := hD p hp
      have hmn := Nat.mul_le_mul_right H (show p.1 + 1 ≤ p.2 by omega)
      have hnc := Nat.mul_le_mul_right H (show p.2 + 1 ≤ p.1 + p.2 + k by omega)
      refine ⟨hma, hna, hca, by omega, by omega, ?_, ?_⟩
      · have hlow : a.2.2 ≤ a.1 + a.2.1 + (k + 1) * H := by nlinarith
        have hlow' : (a.2.2 : ℤ) ≤ (a.1 : ℤ) + (a.2.1 : ℤ) + ((k : ℤ) + 1) * (H : ℤ) := by exact_mod_cast hlow
        nlinarith
      · have hupp : a.1 + a.2.1 + k * H ≤ a.2.2 + 2 * H := by nlinarith
        have hupp' : (a.1 : ℤ) + (a.2.1 : ℤ) + (k : ℤ) * (H : ℤ) ≤ (a.2.2 : ℤ) + 2 * (H : ℤ) := by exact_mod_cast hupp
        nlinarith)
  have hlen : ((2 - (k : ℤ)) * (H : ℤ) + 1 - (-((k : ℤ) + 1) * (H : ℤ))).toNat = 3 * H + 1 := by
    have he : (2 - (k : ℤ)) * (H : ℤ) + 1 - (-((k : ℤ) + 1) * (H : ℤ)) =
        ((3 * H + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [he, Int.toNat_natCast]
  simpa only [hlen] using hb


lemma scaling_limit_shifted_box_bound {A : Set ℕ} (h : NtupleCondition A 3) (hA : A.Infinite)
    {F : ℕ → ℝ} {τ : ℕ → ℕ} (hτ : StrictMono τ)
    (hlim : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m)))
    (k : ℕ) (D : Finset (ℕ × ℕ)) (hD : ∀ p ∈ D, 1 ≤ p.1 ∧ p.1 < p.2) :
    ∑ p ∈ D, (F (p.1+1) - F p.1) *
      ((F (p.2+1) - F p.2) * (F (p.1+p.2+k+1) - F (p.1+p.2+k))) ≤ 15 := by
  have ht := tendsto_finset_sum D (fun p _ => (scaling_limit_intervalBin hlim p.1).mul
    ((scaling_limit_intervalBin hlim p.2).mul (scaling_limit_intervalBin hlim (p.1+p.2+k))))
  have hτlim : Tendsto (fun n => τ n + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hτ.tendsto_atTop
  have hu : Tendsto (fun n => (15 : ℝ) + 5 * ((τ n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 15) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hτlim)).const_mul (5 : ℝ))
  apply le_of_tendsto_of_tendsto ht hu
  filter_upwards [] with n
  let H := τ n + 1
  have hH : 0 < H := Nat.succ_pos _
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hroot : ((H : ℝ)^(1/3 : ℝ))^3 = H := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hb := shifted_interval_box_count_bound h hA H k (intervalBin A H)
    (fun m a ha => mem_intervalBin.mp ha) D hD
  have hb' : ∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) *
      (((intervalBin A H p.2).card : ℝ) * ((intervalBin A H (p.1+p.2+k)).card : ℝ)) ≤
      5 * (3 * (H : ℝ) + 1) := by exact_mod_cast hb
  change (∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) / (H : ℝ)^(1/3 : ℝ) *
    (((intervalBin A H p.2).card : ℝ) / (H : ℝ)^(1/3 : ℝ) *
      (((intervalBin A H (p.1+p.2+k)).card : ℝ) / (H : ℝ)^(1/3 : ℝ)))) ≤ 15 + 5 * (H : ℝ)⁻¹
  calc
    _ = (∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) *
      (((intervalBin A H p.2).card : ℝ) * ((intervalBin A H (p.1+p.2+k)).card : ℝ))) / H := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = (((intervalBin A H p.1).card : ℝ) *
          (((intervalBin A H p.2).card : ℝ) * ((intervalBin A H (p.1+p.2+k)).card : ℝ))) /
          ((H : ℝ)^(1/3 : ℝ))^3 := by ring
        _ = _ := by rw [hroot]
    _ ≤ (5 * (3 * (H : ℝ) + 1)) / H := (div_le_div_iff_of_pos_right hHr).mpr hb'
    _ = 15 + 5 * (H : ℝ)⁻¹ := by field_simp; ring




/-- Necessary analytic conditions on a scaling profile of any counterexample.
This is a reduction, not an assertion that these conditions are contradictory. -/
lemma failure_yields_profile {A : Set ℕ} (h : NtupleCondition A 3) (hA : A.Infinite)
    (hfail : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0) :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ F : ℕ → ℝ,
      F 0 = 0 ∧ Monotone F ∧
      (∀ m : ℕ, ε * (m : ℝ)^(1/3 : ℝ) ≤ F m ∧ F m ≤ 5 * (m : ℝ)^(1/3 : ℝ)) ∧
      (∀ (k : ℕ) (D : Finset (ℕ × ℕ)), (∀ p ∈ D, 1 ≤ p.1 ∧ p.1 < p.2) →
        ∑ p ∈ D, (F (p.1+1) - F p.1) * ((F (p.2+1) - F p.2) *
          (F (p.1+p.2+k+1) - F (p.1+p.2+k))) ≤ 15) ∧
      (∀ D : Finset ℕ, (∀ m ∈ D, 1 ≤ m) →
        F 1 * (∑ m ∈ D, (F (m+1) - F m)^2) ≤ 20) ∧
      Summable (fun m : ℕ => (F (m+2) - F (m+1))^2) := by
  obtain ⟨ε, hε, M, hlow⟩ := (density_liminf_ne_zero_iff h).mp hfail
  obtain ⟨F, τ, hτ, hlim, hF0, hmono, hbound⟩ := exists_prefix_scaling_limit h M hlow
  have hF1 : 0 < F 1 := lt_of_lt_of_le hε (by simpa using (hbound 1).1)
  exact ⟨ε, hε, F, hF0, hmono, hbound,
    scaling_limit_shifted_box_bound h hA hτ hlim,
    scaling_limit_square_bound h hA hτ hlim,
    scaling_limit_increments_square_summable h hA hτ hlim hF1⟩


lemma positive_pair_triples_interval_card_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (L U : ℤ) (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 ∈ A ∧ p.2.1 ∈ A ∧ p.2.2 ∈ A ∧
      p.1 < p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1 ∧
      L ≤ (p.1 : ℤ) + (p.2.1 : ℤ) - (p.2.2 : ℤ) ∧
      (p.1 : ℤ) + (p.2.1 : ℤ) - (p.2.2 : ℤ) ≤ U) :
    T.card ≤ 5 * (U + 1 - L).toNat := by
  classical
  let f : ℕ × ℕ × ℕ → Finset ℕ × ℕ := fun p => ({p.1, p.2.1}, p.2.2)
  have hf : Set.InjOn f (T : Set (ℕ × ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hp' := hT p hp
    have hq' := hT q hq
    have he : ({p.1, p.2.1} : Finset ℕ) = {q.1, q.2.1} := congrArg Prod.fst hpq
    have hc : p.2.2 = q.2.2 := congrArg (fun r : Finset ℕ × ℕ => r.2) hpq
    have ha : p.1 = q.1 ∨ p.1 = q.2.1 := by
      have hm : p.1 ∈ ({q.1, q.2.1} : Finset ℕ) := he ▸ (by simp)
      simpa using hm
    have hb : q.1 = p.1 ∨ q.1 = p.2.1 := by
      have hm : q.1 ∈ ({p.1, p.2.1} : Finset ℕ) := he.symm ▸ (by simp)
      simpa using hm
    have hab : p.2.1 = q.1 ∨ p.2.1 = q.2.1 := by
      have hm : p.2.1 ∈ ({q.1, q.2.1} : Finset ℕ) := he ▸ (by simp)
      simpa using hm
    exact Prod.ext (by omega) (Prod.ext (by omega) hc)
  rw [← Finset.card_image_of_injOn hf]
  apply signed_sum_interval_card_bound h hA
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨ha, hb, hc, hab, hca, hcb, hlo, hup⟩ := hT q hq
  have hab' : q.1 ≠ q.2.1 := ne_of_lt hab
  refine ⟨?_, ?_, hc, ?_, ?_, ?_⟩
  · intro x hx
    simp only [f, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · simp [f, hab']
  · simp only [f, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hca, hcb⟩
  · simpa [f, Finset.sum_pair hab'] using hlo
  · simpa [f, Finset.sum_pair hab'] using hup



lemma signed_box_count_bound {A : Set ℕ} (h : NtupleCondition A 3) (hA : A.Infinite)
    (H : ℕ) (S : ℕ → Finset ℕ)
    (hS : ∀ m a, a ∈ S m → a ∈ A ∧ m * H + 1 ≤ a ∧ a ≤ (m + 1) * H)
    (K : ℤ) (D : Finset (ℕ × ℕ × ℕ))
    (hD : ∀ p ∈ D, p.1 < p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1 ∧
      (p.1 : ℤ) + (p.2.1 : ℤ) - (p.2.2 : ℤ) = K) :
    ∑ p ∈ D, (S p.1).card * ((S p.2.1).card * (S p.2.2).card) ≤ 5 * (3 * H + 1) := by
  classical
  let box : ℕ × ℕ × ℕ → Finset (ℕ × ℕ × ℕ) :=
    fun p => S p.1 ×ˢ (S p.2.1 ×ˢ S p.2.2)
  have hindex : ∀ {m n a}, a ∈ S m → a ∈ S n → m = n := by
    intro m n a ham han
    obtain ⟨_, hmlo, hmhi⟩ := hS m a ham
    obtain ⟨_, hnlo, hnhi⟩ := hS n a han
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx := Nat.mul_le_mul_right H (show m + 1 ≤ n by omega)
      omega
    · have hx := Nat.mul_le_mul_right H (show n + 1 ≤ m by omega)
      omega
  have hdisj : (D : Set (ℕ × ℕ × ℕ)).PairwiseDisjoint box := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro a hap haq
    obtain ⟨hpa, hpbc⟩ := Finset.mem_product.mp hap
    obtain ⟨hpb, hpc⟩ := Finset.mem_product.mp hpbc
    obtain ⟨hqa, hqbc⟩ := Finset.mem_product.mp haq
    obtain ⟨hqb, hqc⟩ := Finset.mem_product.mp hqbc
    exact hpq (Prod.ext (hindex hpa hqa) (Prod.ext (hindex hpb hqb) (hindex hpc hqc)))
  have hcard : (D.biUnion box).card =
      ∑ p ∈ D, (S p.1).card * ((S p.2.1).card * (S p.2.2).card) := by
    rw [Finset.card_biUnion hdisj]
    simp [box, Finset.card_product]
  rw [← hcard]
  have hb := positive_pair_triples_interval_card_bound h hA ((K-1)*(H:ℤ)) ((K+2)*(H:ℤ))
    (D.biUnion box) (by
      intro a ha
      obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨ham, hanc⟩ := Finset.mem_product.mp hap
      obtain ⟨han, hac⟩ := Finset.mem_product.mp hanc
      obtain ⟨hma, hmlo, hmhi⟩ := hS p.1 a.1 ham
      obtain ⟨hna, hnlo, hnhi⟩ := hS p.2.1 a.2.1 han
      obtain ⟨hca, hclo, hchi⟩ := hS p.2.2 a.2.2 hac
      obtain ⟨hmn, hlm, hln, heq⟩ := hD p hp
      have hmn' := Nat.mul_le_mul_right H (show p.1 + 1 ≤ p.2.1 by omega)
      have hcne : a.2.2 ≠ a.1 := by
        intro he
        rw [he] at hac
        exact hlm (hindex hac ham)
      have hcne' : a.2.2 ≠ a.2.1 := by
        intro he
        rw [he] at hac
        exact hln (hindex hac han)
      have hml : (p.1 : ℤ)*(H:ℤ)+1 ≤ (a.1:ℤ) := by exact_mod_cast hmlo
      have hmu : (a.1:ℤ) ≤ ((p.1:ℤ)+1)*(H:ℤ) := by exact_mod_cast hmhi
      have hnl : (p.2.1 : ℤ)*(H:ℤ)+1 ≤ (a.2.1:ℤ) := by exact_mod_cast hnlo
      have hnu : (a.2.1:ℤ) ≤ ((p.2.1:ℤ)+1)*(H:ℤ) := by exact_mod_cast hnhi
      have hcl : (p.2.2 : ℤ)*(H:ℤ)+1 ≤ (a.2.2:ℤ) := by exact_mod_cast hclo
      have hcu : (a.2.2:ℤ) ≤ ((p.2.2:ℤ)+1)*(H:ℤ) := by exact_mod_cast hchi
      have heq' := congrArg (fun x : ℤ => x*(H:ℤ)) heq
      exact ⟨hma, hna, hca, by omega, hcne, hcne', by nlinarith, by nlinarith⟩)
  have hlen : ((K+2)*(H:ℤ) + 1 - (K-1)*(H:ℤ)).toNat = 3*H+1 := by
    have he : (K+2)*(H:ℤ) + 1 - (K-1)*(H:ℤ) = ((3*H+1:ℕ):ℤ) := by push_cast; ring
    rw [he, Int.toNat_natCast]
  simpa only [hlen] using hb

lemma scaling_limit_signed_box_bound {A : Set ℕ} (h : NtupleCondition A 3) (hA : A.Infinite)
    {F : ℕ → ℝ} {τ : ℕ → ℕ} (hτ : StrictMono τ)
    (hlim : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m)))
    (K : ℤ) (D : Finset (ℕ × ℕ × ℕ))
    (hD : ∀ p ∈ D, p.1 < p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1 ∧
      (p.1 : ℤ) + (p.2.1 : ℤ) - (p.2.2 : ℤ) = K) :
    ∑ p ∈ D, (F (p.1+1) - F p.1) *
      ((F (p.2.1+1) - F p.2.1) * (F (p.2.2+1) - F p.2.2)) ≤ 15 := by
  have ht := tendsto_finset_sum D (fun p _ => (scaling_limit_intervalBin hlim p.1).mul
    ((scaling_limit_intervalBin hlim p.2.1).mul (scaling_limit_intervalBin hlim p.2.2)))
  have hτlim : Tendsto (fun n => τ n + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hτ.tendsto_atTop
  have hu : Tendsto (fun n => (15 : ℝ) + 5 * ((τ n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 15) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hτlim)).const_mul (5 : ℝ))
  apply le_of_tendsto_of_tendsto ht hu
  filter_upwards [] with n
  let H := τ n + 1
  have hH : 0 < H := Nat.succ_pos _
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hroot : ((H : ℝ)^(1/3 : ℝ))^3 = H := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hb := signed_box_count_bound h hA H (intervalBin A H)
    (fun m a ha => mem_intervalBin.mp ha) K D hD
  have hb' : ∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) *
      (((intervalBin A H p.2.1).card : ℝ) * ((intervalBin A H p.2.2).card : ℝ)) ≤
      5 * (3 * (H : ℝ) + 1) := by exact_mod_cast hb
  change (∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) / (H : ℝ)^(1/3 : ℝ) *
    (((intervalBin A H p.2.1).card : ℝ) / (H : ℝ)^(1/3 : ℝ) *
      (((intervalBin A H p.2.2).card : ℝ) / (H : ℝ)^(1/3 : ℝ)))) ≤ 15 + 5 * (H : ℝ)⁻¹
  calc
    _ = (∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) *
      (((intervalBin A H p.2.1).card : ℝ) * ((intervalBin A H p.2.2).card : ℝ))) / H := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = (((intervalBin A H p.1).card : ℝ) *
          (((intervalBin A H p.2.1).card : ℝ) * ((intervalBin A H p.2.2).card : ℝ))) /
          ((H : ℝ)^(1/3 : ℝ))^3 := by ring
        _ = _ := by rw [hroot]
    _ ≤ (5 * (3 * (H : ℝ) + 1)) / H := (div_le_div_iff_of_pos_right hHr).mpr hb'
    _ = 15 + 5 * (H : ℝ)⁻¹ := by field_simp; ring



/-- Bounds for distinct bin indices extend to all indices when the bin weights have
bounded square sums. The constant need not be sharp. -/
lemma full_signed_weight_bound (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) (C : ℝ) (hC : 0 ≤ C)
    (hsq : ∀ I : Finset ℕ, ∑ i ∈ I, (b i)^2 ≤ C)
    (hgood : ∀ (K : ℤ) (D : Finset (ℕ × ℕ × ℕ)),
      (∀ p ∈ D, p.1 < p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1 ∧
        (p.1 : ℤ) + (p.2.1 : ℤ) - (p.2.2 : ℤ) = K) →
      ∑ p ∈ D, b p.1 * (b p.2.1 * b p.2.2) ≤ 15)
    (K : ℤ) (D : Finset (ℕ × ℕ × ℕ))
    (hD : ∀ p ∈ D, (p.1 : ℤ) + (p.2.1 : ℤ) - (p.2.2 : ℤ) = K) :
    ∑ p ∈ D, b p.1 * (b p.2.1 * b p.2.2) ≤ 30 + 3 * (C+1) * C := by
  classical
  let w : ℕ × ℕ × ℕ → ℝ := fun p => b p.1 * (b p.2.1 * b p.2.2)
  have hw : ∀ p, 0 ≤ w p := fun p => mul_nonneg (hb _) (mul_nonneg (hb _) (hb _))
  have hbound : ∀ i, b i ≤ C+1 := by
    intro i
    have hx : (b i)^2 ≤ C := by simpa using hsq {i}
    nlinarith [sq_nonneg (b i - 1)]
  let G := D.filter (fun p => p.1 < p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1)
  let R := D.filter (fun p => p.2.1 < p.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1)
  let E := D.filter (fun p => p.1 = p.2.1)
  let L := D.filter (fun p => p.2.2 = p.1)
  let U := D.filter (fun p => p.2.2 = p.2.1)
  have hG : ∑ p ∈ G, w p ≤ 15 := by
    apply hgood K
    intro p hp
    obtain ⟨hpD, hab, hca, hcb⟩ := Finset.mem_filter.mp hp
    exact ⟨hab, hca, hcb, hD p hpD⟩
  let sw : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.2.1, p.1, p.2.2)
  have hsw : Function.Injective sw := by
    intro p q he
    have hx := congrArg sw he
    simpa [sw] using hx
  have hR : ∑ p ∈ R, w p ≤ 15 := by
    have hx := hgood K (R.image sw) (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqD, hab, hca, hcb⟩ := Finset.mem_filter.mp hq
      have heq := hD q hqD
      exact ⟨hab, hcb, hca, by dsimp [sw]; omega⟩)
    rw [Finset.sum_image (hsw.injOn)] at hx
    convert hx using 1
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [w, sw]
    ring
  have diag_bound (T : Finset (ℕ × ℕ × ℕ)) (f : ℕ × ℕ × ℕ → ℕ)
      (hi : Set.InjOn f (T : Set (ℕ × ℕ × ℕ)))
      (ht : ∀ p ∈ T, w p ≤ (C+1)*(b (f p))^2) : ∑ p ∈ T, w p ≤ (C+1)*C := by
    calc
      _ ≤ ∑ p ∈ T, (C+1)*(b (f p))^2 := Finset.sum_le_sum ht
      _ = (C+1) * ∑ i ∈ T.image f, (b i)^2 := by rw [Finset.sum_image hi, Finset.mul_sum]
      _ ≤ (C+1)*C := mul_le_mul_of_nonneg_left (hsq _) (by linarith)
  have hE : ∑ p ∈ E, w p ≤ (C+1)*C := by
    refine diag_bound E Prod.fst ?_ ?_
    · intro p hp q hq he
      change p.1 = q.1 at he
      obtain ⟨hpD, hpE⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqD, hqE⟩ := Finset.mem_filter.mp hq
      have hpk := hD p hpD
      have hqk := hD q hqD
      exact Prod.ext he (Prod.ext (by omega) (by omega))
    · intro p hp
      have he := (Finset.mem_filter.mp hp).2
      have hx := mul_le_mul_of_nonneg_left (hbound p.2.2) (sq_nonneg (b p.1))
      dsimp [w]
      rw [← he]
      nlinarith only [hx]
  have hL : ∑ p ∈ L, w p ≤ (C+1)*C := by
    refine diag_bound L Prod.fst ?_ ?_
    · intro p hp q hq he
      change p.1 = q.1 at he
      obtain ⟨hpD, hpL⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqD, hqL⟩ := Finset.mem_filter.mp hq
      have hpk := hD p hpD
      have hqk := hD q hqD
      exact Prod.ext he (Prod.ext (by omega) (by omega))
    · intro p hp
      have he := (Finset.mem_filter.mp hp).2
      have hx := mul_le_mul_of_nonneg_left (hbound p.2.1) (sq_nonneg (b p.1))
      dsimp [w]
      rw [he]
      nlinarith only [hx]
  have hU : ∑ p ∈ U, w p ≤ (C+1)*C := by
    refine diag_bound U (fun p => p.2.1) ?_ ?_
    · intro p hp q hq he
      change p.2.1 = q.2.1 at he
      obtain ⟨hpD, hpU⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqD, hqU⟩ := Finset.mem_filter.mp hq
      have hpk := hD p hpD
      have hqk := hD q hqD
      exact Prod.ext (by omega) (Prod.ext he (by omega))
    · intro p hp
      have he := (Finset.mem_filter.mp hp).2
      have hx := mul_le_mul_of_nonneg_left (hbound p.1) (sq_nonneg (b p.2.1))
      dsimp [w]
      rw [he]
      nlinarith only [hx]
  have hcover : ∑ p ∈ D, w p ≤ (∑ p ∈ G, w p) + (∑ p ∈ R, w p) +
      (∑ p ∈ E, w p) + (∑ p ∈ L, w p) + (∑ p ∈ U, w p) := by
    dsimp [G, R, E, L, U]
    simp_rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hif (P : Prop) [Decidable P] : 0 ≤ (if P then w p else 0) := by
      split_ifs
      · exact hw p
      · exact le_rfl
    have h1 := hif (p.1 < p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1)
    have h2 := hif (p.2.1 < p.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1)
    have h3 := hif (p.1 = p.2.1)
    have h4 := hif (p.2.2 = p.1)
    have h5 := hif (p.2.2 = p.2.1)
    have hc : (p.1 < p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1) ∨
        (p.2.1 < p.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1) ∨
        p.1 = p.2.1 ∨ p.2.2 = p.1 ∨ p.2.2 = p.2.1 := by omega
    rcases hc with hx | hx | hx | hx | hx <;> simp only [if_pos hx] <;> linarith
  change (∑ p ∈ D, w p) ≤ _
  linarith



/-- A counterexample would give a nonnegative square-summable weighted sequence
with critical prefix growth and uniformly bounded mixed triple convolution.
All integer signed offsets and all repeated bin indices are included. -/
lemma failure_yields_weighted_sequence {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite)
    (hfail : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∃ b : ℕ → ℝ,
      (∀ i, 0 ≤ b i) ∧
      (∀ N : ℕ, ε * (N : ℝ)^(1/3 : ℝ) ≤ ∑ i ∈ Finset.range N, b i ∧
        (∑ i ∈ Finset.range N, b i) ≤ 5 * (N : ℝ)^(1/3 : ℝ)) ∧
      Summable (fun i => (b i)^2) ∧
      (∀ (K : ℤ) (D : Finset (ℕ × ℕ × ℕ)),
        (∀ p ∈ D, (p.1 : ℤ) + (p.2.1 : ℤ) - (p.2.2 : ℤ) = K) →
        ∑ p ∈ D, b p.1 * (b p.2.1 * b p.2.2) ≤ C) := by
  obtain ⟨ε, hε, M, hlow⟩ := (density_liminf_ne_zero_iff h).mp hfail
  obtain ⟨F, τ, hτ, hlim, hF0, hmono, hbound⟩ := exists_prefix_scaling_limit h M hlow
  have hF1 : 0 < F 1 := lt_of_lt_of_le hε (by simpa using (hbound 1).1)
  let b := fun i => F (i+1) - F i
  have hb : ∀ i, 0 ≤ b i := fun i => sub_nonneg.mpr (hmono (Nat.le_succ i))
  have hb0 : b 0 = F 1 := by simp [b, hF0]
  let Q := (F 1)^2 + 20 / F 1
  have hQ : 0 ≤ Q := by positivity
  have hsq : ∀ I : Finset ℕ, ∑ i ∈ I, (b i)^2 ≤ Q := by
    intro I
    have ht := scaling_limit_square_bound h hA hτ hlim (I.erase 0) (by
      intro m hm
      have hx := (Finset.mem_erase.mp hm).1
      omega)
    change F 1 * (∑ i ∈ I.erase 0, (b i)^2) ≤ 20 at ht
    have ht' : ∑ i ∈ I.erase 0, (b i)^2 ≤ 20 / F 1 := by
      apply (le_div_iff₀ hF1).mpr
      simpa [mul_comm] using ht
    by_cases h0 : 0 ∈ I
    · rw [← Finset.sum_erase_add I (fun i => (b i)^2) h0, hb0]
      dsimp [Q]
      linarith
    · rw [Finset.erase_eq_of_notMem h0] at ht'
      dsimp [Q]
      nlinarith [sq_nonneg (F 1)]
  refine ⟨ε, hε, 30 + 3 * (Q+1)*Q, by positivity, b, hb, ?_,
    summable_of_sum_le (fun i => sq_nonneg (b i)) hsq, ?_⟩
  · intro N
    dsimp [b]
    rw [Finset.sum_range_sub, hF0, sub_zero]
    exact hbound N
  · exact full_signed_weight_bound b hb Q hQ hsq
      (scaling_limit_signed_box_bound h hA hτ hlim)


lemma sorted_positive_triples_interval_card_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (L U : ℕ) (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 ∈ A ∧ p.2.1 ∈ A ∧ p.2.2 ∈ A ∧ p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
      L ≤ p.1 + p.2.1 + p.2.2 ∧ p.1 + p.2.1 + p.2.2 ≤ U) :
    T.card ≤ U+1-L := by
  let f : ℕ × ℕ × ℕ → ℕ := fun p => p.1 + p.2.1 + p.2.2
  have hmaps : Set.MapsTo f (T : Set (ℕ × ℕ × ℕ)) (Finset.Icc L U : Set ℕ) := by
    intro p hp
    exact Finset.mem_Icc.mpr (hT p hp).2.2.2.2.2
  have hinj : Set.InjOn f (T : Set (ℕ × ℕ × ℕ)) := by
    intro p hp q hq he
    obtain ⟨hpa, hpb, hpc, hpab, hpbc, _⟩ := hT p hp
    obtain ⟨hqa, hqb, hqc, hqab, hqbc, _⟩ := hT q hq
    have hpac := lt_trans hpab hpbc
    have hqac := lt_trans hqab hqbc
    have heq : ({p.1, p.2.1, p.2.2} : Finset ℕ) = {q.1, q.2.1, q.2.2} := by
      apply h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · simp [ne_of_lt hpab, ne_of_lt hpbc, ne_of_lt hpac]
      · simp [ne_of_lt hqab, ne_of_lt hqbc, ne_of_lt hqac]
      · simpa [f, ne_of_lt hpab, ne_of_lt hpbc, ne_of_lt hpac,
          ne_of_lt hqab, ne_of_lt hqbc, ne_of_lt hqac, add_assoc] using he
    have hpa' : p.1 = q.1 ∨ p.1 = q.2.1 ∨ p.1 = q.2.2 := by
      have hm : p.1 ∈ ({q.1, q.2.1, q.2.2} : Finset ℕ) := heq ▸ (by simp)
      simpa using hm
    have hqa' : q.1 = p.1 ∨ q.1 = p.2.1 ∨ q.1 = p.2.2 := by
      have hm : q.1 ∈ ({p.1, p.2.1, p.2.2} : Finset ℕ) := heq.symm ▸ (by simp)
      simpa using hm
    have hpc' : p.2.2 = q.1 ∨ p.2.2 = q.2.1 ∨ p.2.2 = q.2.2 := by
      have hm : p.2.2 ∈ ({q.1, q.2.1, q.2.2} : Finset ℕ) := heq ▸ (by simp)
      simpa using hm
    have hqc' : q.2.2 = p.1 ∨ q.2.2 = p.2.1 ∨ q.2.2 = p.2.2 := by
      have hm : q.2.2 ∈ ({p.1, p.2.1, p.2.2} : Finset ℕ) := heq.symm ▸ (by simp)
      simpa using hm
    have hpb' : p.2.1 = q.1 ∨ p.2.1 = q.2.1 ∨ p.2.1 = q.2.2 := by
      have hm : p.2.1 ∈ ({q.1, q.2.1, q.2.2} : Finset ℕ) := heq ▸ (by simp)
      simpa using hm
    exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))
  simpa using Finset.card_le_card_of_injOn f hmaps hinj

lemma positive_box_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (H : ℕ) (S : ℕ → Finset ℕ)
    (hS : ∀ m a, a ∈ S m → a ∈ A ∧ m * H + 1 ≤ a ∧ a ≤ (m + 1) * H)
    (K : ℕ) (D : Finset (ℕ × ℕ × ℕ))
    (hD : ∀ p ∈ D, p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.1 + p.2.1 + p.2.2 = K) :
    ∑ p ∈ D, (S p.1).card * ((S p.2.1).card * (S p.2.2).card) ≤ 3 * H + 1 := by
  classical
  let box : ℕ × ℕ × ℕ → Finset (ℕ × ℕ × ℕ) :=
    fun p => S p.1 ×ˢ (S p.2.1 ×ˢ S p.2.2)
  have hindex : ∀ {m n a}, a ∈ S m → a ∈ S n → m = n := by
    intro m n a ham han
    obtain ⟨_, hmlo, hmhi⟩ := hS m a ham
    obtain ⟨_, hnlo, hnhi⟩ := hS n a han
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx := Nat.mul_le_mul_right H (show m+1 ≤ n by omega)
      omega
    · have hx := Nat.mul_le_mul_right H (show n+1 ≤ m by omega)
      omega
  have hdisj : (D : Set (ℕ × ℕ × ℕ)).PairwiseDisjoint box := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro a hap haq
    obtain ⟨hpa, hpbc⟩ := Finset.mem_product.mp hap
    obtain ⟨hpb, hpc⟩ := Finset.mem_product.mp hpbc
    obtain ⟨hqa, hqbc⟩ := Finset.mem_product.mp haq
    obtain ⟨hqb, hqc⟩ := Finset.mem_product.mp hqbc
    exact hpq (Prod.ext (hindex hpa hqa) (Prod.ext (hindex hpb hqb) (hindex hpc hqc)))
  have hcard : (D.biUnion box).card =
      ∑ p ∈ D, (S p.1).card * ((S p.2.1).card * (S p.2.2).card) := by
    rw [Finset.card_biUnion hdisj]
    simp [box, Finset.card_product]
  rw [← hcard]
  have hb := sorted_positive_triples_interval_card_bound h (K*H) ((K+3)*H)
    (D.biUnion box) (by
      intro a ha
      obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨ham, hanc⟩ := Finset.mem_product.mp hap
      obtain ⟨han, hac⟩ := Finset.mem_product.mp hanc
      obtain ⟨hma, hmlo, hmhi⟩ := hS p.1 a.1 ham
      obtain ⟨hna, hnlo, hnhi⟩ := hS p.2.1 a.2.1 han
      obtain ⟨hca, hclo, hchi⟩ := hS p.2.2 a.2.2 hac
      obtain ⟨hmn, hnl, heq⟩ := hD p hp
      have hmn' := Nat.mul_le_mul_right H (show p.1+1 ≤ p.2.1 by omega)
      have hnl' := Nat.mul_le_mul_right H (show p.2.1+1 ≤ p.2.2 by omega)
      have heq' := congrArg (fun x : ℕ => x*H) heq
      exact ⟨hma, hna, hca, by omega, by omega, by nlinarith, by nlinarith⟩)
  have he : (K+3)*H+1-K*H = 3*H+1 := by rw [Nat.add_mul]; omega
  simpa only [he] using hb



lemma scaling_limit_positive_box_bound {A : Set ℕ} (h : NtupleCondition A 3)
    {F : ℕ → ℝ} {τ : ℕ → ℕ} (hτ : StrictMono τ)
    (hlim : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m)))
    (K : ℕ) (D : Finset (ℕ × ℕ × ℕ))
    (hD : ∀ p ∈ D, p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.1 + p.2.1 + p.2.2 = K) :
    ∑ p ∈ D, (F (p.1+1) - F p.1) *
      ((F (p.2.1+1) - F p.2.1) * (F (p.2.2+1) - F p.2.2)) ≤ 3 := by
  have ht := tendsto_finset_sum D (fun p _ => (scaling_limit_intervalBin hlim p.1).mul
    ((scaling_limit_intervalBin hlim p.2.1).mul (scaling_limit_intervalBin hlim p.2.2)))
  have hτlim : Tendsto (fun n => τ n + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hτ.tendsto_atTop
  have hu : Tendsto (fun n => (3 : ℝ) + ((τ n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 3) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hτlim)).const_mul (1 : ℝ))
  apply le_of_tendsto_of_tendsto ht hu
  filter_upwards [] with n
  let H := τ n + 1
  have hH : 0 < H := Nat.succ_pos _
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hroot : ((H : ℝ)^(1/3 : ℝ))^3 = H := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hb := positive_box_count_bound h H (intervalBin A H)
    (fun m a ha => mem_intervalBin.mp ha) K D hD
  have hb' : ∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) *
      (((intervalBin A H p.2.1).card : ℝ) * ((intervalBin A H p.2.2).card : ℝ)) ≤
      (3 * (H : ℝ) + 1) := by exact_mod_cast hb
  change (∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) / (H : ℝ)^(1/3 : ℝ) *
    (((intervalBin A H p.2.1).card : ℝ) / (H : ℝ)^(1/3 : ℝ) *
      (((intervalBin A H p.2.2).card : ℝ) / (H : ℝ)^(1/3 : ℝ)))) ≤ 3 + (H : ℝ)⁻¹
  calc
    _ = (∑ p ∈ D, ((intervalBin A H p.1).card : ℝ) *
      (((intervalBin A H p.2.1).card : ℝ) * ((intervalBin A H p.2.2).card : ℝ))) / H := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = (((intervalBin A H p.1).card : ℝ) *
          (((intervalBin A H p.2.1).card : ℝ) * ((intervalBin A H p.2.2).card : ℝ))) /
          ((H : ℝ)^(1/3 : ℝ))^3 := by ring
        _ = _ := by rw [hroot]
    _ ≤ ((3 * (H : ℝ) + 1)) / H := (div_le_div_iff_of_pos_right hHr).mpr hb'
    _ = 3 + (H : ℝ)⁻¹ := by field_simp


lemma bounded_sequence_liminf_subsequence (f : ℕ → ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hf5 : ∀ n, f n ≤ 5) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ Tendsto (f ∘ τ) atTop (nhds (atTop.liminf f)) := by
  have hl := isBoundedUnder_of_eventually_ge (f := atTop) (Eventually.of_forall hf0)
  have hu := isBoundedUnder_of_eventually_le (f := atTop) (Eventually.of_forall hf5)
  apply TopologicalSpace.FirstCountableTopology.tendsto_subseq
  rw [mapClusterPt_iff_frequently]
  intro s hs
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hup := frequently_lt_of_liminf_lt hu.isCoboundedUnder_ge
    (show atTop.liminf f < atTop.liminf f + δ by linarith)
  have hlo := eventually_lt_of_lt_liminf
    (show atTop.liminf f - δ < atTop.liminf f by linarith) hl
  apply (hup.and_eventually hlo).mono
  intro n hn
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hn.1, hn.2]

/-- A scaling profile can be chosen to attain the actual lower density at scale one.
This still does not assert that the profile is a power law. -/
lemma exists_minimal_prefix_scaling_limit {A : Set ℕ} (h : NtupleCondition A 3) :
    ∃ (F : ℕ → ℝ) (τ : ℕ → ℕ), StrictMono τ ∧
      (∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
        ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m))) ∧
      F 0 = 0 ∧ Monotone F ∧
      F 1 = Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ∧
      (∀ m : ℕ, F 1 * (m : ℝ)^(1/3 : ℝ) ≤ F m ∧ F m ≤ 5 * (m : ℝ)^(1/3 : ℝ)) := by
  let d : ℕ → ℝ := fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)
  obtain ⟨σ, hσ, hσlim⟩ := bounded_sequence_liminf_subsequence (fun n => d (n+1))
    (fun n => density_nonneg A (n+1)) (fun n => density_le_five h (by omega))
  rw [liminf_nat_add] at hσlim
  let f : ℕ → ℕ → ℝ := fun n m => ((initialSegment A (m * (σ n + 1))).card : ℝ) /
    ((σ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)
  let s : Set (ℕ → ℝ) := {F | ∀ m : ℕ, F m ∈ Icc 0 (5 * (m : ℝ)^(1/3 : ℝ))}
  have hs : IsCompact s := isCompact_pi_infinite (fun m => isCompact_Icc)
  have hf : ∀ n, f n ∈ s := by
    intro n m
    exact ⟨by positivity, normalized_prefix_le h (σ n+1) m (by omega)⟩
  obtain ⟨F, hFs, ρ, hρ, hlim⟩ := hs.tendsto_subseq hf
  let τ := σ ∘ ρ
  have hτ : StrictMono τ := hσ.comp hρ
  have hlim' : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m)) := fun m => hlim.apply_nhds m
  have hzero : F 0 = 0 := by
    have hz := hlim' 0
    simp only [zero_mul, initialSegment, Finset.Icc_eq_empty_of_lt (by decide : 0 < 1),
      Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_div] at hz
    exact tendsto_nhds_unique hz tendsto_const_nhds
  have hF1 : F 1 = atTop.liminf d := by
    have ht : Tendsto (fun n => d (τ n+1)) atTop (nhds (F 1)) := by
      simpa [d, card_initialSegment] using hlim' 1
    exact tendsto_nhds_unique ht (hσlim.comp hρ.tendsto_atTop)
  refine ⟨F, τ, hτ, hlim', hzero, ?_, hF1, ?_⟩
  · intro i j hij
    apply le_of_tendsto_of_tendsto (hlim' i) (hlim' j)
    filter_upwards [] with n
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (initialSegment_mono A (Nat.mul_le_mul_right _ hij))
  · intro m
    refine ⟨?_, (hFs m).2⟩
    by_cases hm : m = 0
    · subst m
      simp [hzero]
    have hmpos : (0 : ℝ) < (m : ℝ)^(1/3 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) _
    rw [hF1]
    apply (le_div_iff₀ hmpos).mp
    apply le_of_forall_lt_imp_le_of_dense
    intro x hx
    have hl := isBoundedUnder_of_eventually_ge (f := atTop) (Eventually.of_forall (density_nonneg A))
    have hlow : ∀ᶠ N in atTop, x < d N := eventually_lt_of_lt_liminf hx hl
    have hτlim : Tendsto (fun n => m * (τ n+1)) atTop atTop := by
      have hbase := (tendsto_add_atTop_nat 1).comp hτ.tendsto_atTop
      exact tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm)) hbase
    apply (le_div_iff₀ hmpos).mpr
    apply ge_of_tendsto (hlim' m)
    filter_upwards [hτlim.eventually hlow] with n hn
    rw [normalized_prefix_eq]
    exact mul_le_mul_of_nonneg_right (le_of_lt hn) hmpos.le


/-- The translates of the tail's two-sum set by distinct prefix elements are disjoint. -/
lemma disjoint_two_one_sum_injective {A : Set ℕ} (h : NtupleCondition A 3)
    (P S : Finset ℕ) (hP : (P : Set ℕ) ⊆ A) (hS : (S : Set ℕ) ⊆ A)
    (hPS : Disjoint P S) :
    Set.InjOn (fun p : Finset ℕ × ℕ => (∑ a ∈ p.1, a) + p.2)
      ((S.powersetCard 2 ×ˢ P : Finset (Finset ℕ × ℕ)) : Set (Finset ℕ × ℕ)) := by
  classical
  intro p hp q hq he
  obtain ⟨hpI, hpp⟩ := Finset.mem_product.mp hp
  obtain ⟨hqI, hqp⟩ := Finset.mem_product.mp hq
  obtain ⟨hpS, hpc⟩ := Finset.mem_powersetCard.mp hpI
  obtain ⟨hqS, hqc⟩ := Finset.mem_powersetCard.mp hqI
  have hpnot : p.2 ∉ S := fun hps => Finset.disjoint_left.mp hPS hpp hps
  have hqnot : q.2 ∉ S := fun hqs => Finset.disjoint_left.mp hPS hqp hqs
  have hpnotI : p.2 ∉ p.1 := fun hpi => hpnot (hpS hpi)
  have hqnotI : q.2 ∉ q.1 := fun hqi => hqnot (hqS hqi)
  have hI : insert p.2 p.1 = insert q.2 q.1 := by
    apply h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hP hpp
      · exact hS (hpS hx)
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hP hqp
      · exact hS (hqS hx)
    · simp [hpnotI, hpc]
    · simp [hqnotI, hqc]
    · simpa only [Finset.sum_insert hpnotI, Finset.sum_insert hqnotI, add_comm] using he
  have hpq : p.2 = q.2 := by
    have hm : p.2 ∈ insert q.2 q.1 := hI ▸ Finset.mem_insert_self _ _
    exact (Finset.mem_insert.mp hm).resolve_right (fun hx => hpnot (hqS hx))
  refine Prod.ext ?_ hpq
  ext x
  constructor
  · intro hx
    have hm : x ∈ insert q.2 q.1 := hI ▸ Finset.mem_insert_of_mem hx
    exact (Finset.mem_insert.mp hm).resolve_left
      (fun heq => hqnot (heq ▸ hpS hx))
  · intro hx
    have hm : x ∈ insert p.2 p.1 := hI.symm ▸ Finset.mem_insert_of_mem hx
    exact (Finset.mem_insert.mp hm).resolve_left
      (fun heq => hpnot (heq ▸ hqS hx))

/-- A nonzero prefix difference cannot be a difference of two tail two-sums. -/
lemma prefix_difference_not_tail_two_sum_difference {A : Set ℕ}
    (h : NtupleCondition A 3) (P S : Finset ℕ)
    (hP : (P : Set ℕ) ⊆ A) (hS : (S : Set ℕ) ⊆ A) (hPS : Disjoint P S)
    {a b : ℕ} (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b)
    {I J : Finset ℕ} (hI : I ∈ S.powersetCard 2) (hJ : J ∈ S.powersetCard 2) :
    (a : ℤ) - (b : ℤ) ≠ (↑(∑ x ∈ I, x) : ℤ) - (↑(∑ x ∈ J, x) : ℤ) := by
  intro he
  have hsum : (∑ x ∈ I, x) + b = (∑ x ∈ J, x) + a := by omega
  have heq : (I, b) = (J, a) := disjoint_two_one_sum_injective h P S hP hS hPS
    (Finset.mem_product.mpr ⟨hI, hb⟩) (Finset.mem_product.mpr ⟨hJ, ha⟩) hsum
  exact hab (congrArg Prod.snd heq).symm


/-- Two four-element representations of the same sum are identical if they meet. -/
lemma four_sum_eq_of_common_mem {A : Set ℕ} (h : NtupleCondition A 3)
    {I J : Finset ℕ} (hI : (I : Set ℕ) ⊆ A) (hJ : (J : Set ℕ) ⊆ A)
    (hIc : I.card = 4) (hJc : J.card = 4)
    (hs : ∑ a ∈ I, a = ∑ a ∈ J, a)
    {x : ℕ} (hxI : x ∈ I) (hxJ : x ∈ J) : I = J := by
  have he : I.erase x = J.erase x := by
    apply h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      exact hI (Finset.erase_subset _ _ ha)
    · intro a ha
      exact hJ (Finset.erase_subset _ _ ha)
    · rw [Finset.card_erase_of_mem hxI, hIc]
    · rw [Finset.card_erase_of_mem hxJ, hJc]
    · have hi := Finset.sum_erase_add I (fun a => a) hxI
      have hj := Finset.sum_erase_add J (fun a => a) hxJ
      dsimp only at hi hj
      omega
  calc
    I = insert x (I.erase x) := (Finset.insert_erase hxI).symm
    _ = insert x (J.erase x) := congrArg (insert x) he
    _ = J := Finset.insert_erase hxJ

/-- A family of four-element sets with the same sum is a matching. -/
lemma four_sum_fiber_pairwiseDisjoint {A : Set ℕ} (h : NtupleCondition A 3)
    (R : Finset (Finset ℕ)) (t : ℕ)
    (hR : ∀ I ∈ R, (I : Set ℕ) ⊆ A ∧ I.card = 4 ∧ ∑ a ∈ I, a = t) :
    (R : Set (Finset ℕ)).PairwiseDisjoint id := by
  intro I hIR J hJR hne
  apply Finset.disjoint_left.mpr
  intro a haI haJ
  obtain ⟨hI, hIc, hIs⟩ := hR I hIR
  obtain ⟨hJ, hJc, hJs⟩ := hR J hJR
  exact hne (four_sum_eq_of_common_mem h hI hJ hIc hJc (hIs.trans hJs.symm) haI haJ)

/-- Weighted packing for a single fiber of four-element sums. -/
lemma four_sum_fiber_weight_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (S : Finset ℕ) (R : Finset (Finset ℕ)) (t : ℕ)
    (hS : (S : Set ℕ) ⊆ A)
    (hR : ∀ I ∈ R, I ⊆ S ∧ I.card = 4 ∧ ∑ a ∈ I, a = t)
    (w : ℕ → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a) :
    ∑ I ∈ R, ∑ a ∈ I, w a ≤ ∑ a ∈ S, w a := by
  have hd := four_sum_fiber_pairwiseDisjoint h R t (by
    intro I hI
    obtain ⟨hIS, hIc, hIs⟩ := hR I hI
    exact ⟨fun a ha => hS (hIS ha), hIc, hIs⟩)
  have he : (∑ I ∈ R, ∑ a ∈ I, w a) = ∑ a ∈ R.biUnion id, w a :=
    (Finset.sum_biUnion hd).symm
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    obtain ⟨I, hI, haI⟩ := Finset.mem_biUnion.mp ha
    exact (hR I hI).1 haI
  · intro a ha _
    exact hw a ha

/-- Consequently, a four-sum fiber uses four new elements for every representation. -/
lemma four_sum_fiber_card_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (S : Finset ℕ) (R : Finset (Finset ℕ)) (t : ℕ)
    (hS : (S : Set ℕ) ⊆ A)
    (hR : ∀ I ∈ R, I ⊆ S ∧ I.card = 4 ∧ ∑ a ∈ I, a = t) :
    4 * R.card ≤ S.card := by
  have hb := four_sum_fiber_weight_bound h S R t hS hR (fun _ => 1) (by intros; positivity)
  have hc : ∀ I ∈ R, (I.card : ℝ) = 4 := by
    intro I hI
    exact_mod_cast (hR I hI).2.1
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hb
  have hs : ∑ I ∈ R, (I.card : ℝ) = (R.card : ℝ) * 4 := by
    calc
      ∑ I ∈ R, (I.card : ℝ) = ∑ _ ∈ R, (4 : ℝ) := Finset.sum_congr rfl hc
      _ = (R.card : ℝ) * 4 := by simp
  rw [hs] at hb
  exact_mod_cast (show (4 : ℝ) * (R.card : ℝ) ≤ (S.card : ℝ) by nlinarith)


/-- Every nonzero difference has boundedly many representations by two elements of `A`. -/
lemma nonzero_difference_fiber_card_le_five {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) {t : ℤ} (ht : t ≠ 0) (R : Finset (ℕ × ℕ))
    (hR : ∀ p ∈ R, p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = t) :
    R.card ≤ 5 := by
  classical
  obtain ⟨e, heA, he⟩ := hA.exists_notMem_finset (R.image Prod.fst ∪ R.image Prod.snd)
  have hfst : ∀ p ∈ R, p.1 ≠ e := by
    intro p hp hpe
    apply he
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨p, hp, hpe⟩
  have hsnd : ∀ p ∈ R, p.2 ≠ e := by
    intro p hp hpe
    apply he
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨p, hp, hpe⟩
  let f : ℕ × ℕ → Finset ℕ × ℕ := fun p => ({p.1, e}, p.2)
  have hf : Set.InjOn f (R : Set (ℕ × ℕ)) := by
    intro p hp q hq heq
    have h2 : p.2 = q.2 := congrArg (fun v : Finset ℕ × ℕ => v.2) heq
    have hp' := (hR p hp).2.2
    have hq' := (hR q hq).2.2
    exact Prod.ext (by omega) h2
  rw [← Finset.card_image_of_injOn hf]
  apply signed_sum_fiber_card_le_five h hA (t + e)
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hq1, hq2, hqt⟩ := hR q hq
  have hqne : q.1 ≠ q.2 := by intro heq; apply ht; omega
  refine ⟨?_, ?_, hq2, ?_, ?_⟩
  · intro a ha
    simp only [f, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hq1
    · exact heA
  · simp [f, hfst q hq]
  · simp only [f, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hqne.symm, hsnd q hq⟩
  · simp only [f, Finset.sum_pair (hfst q hq), Nat.cast_add]
    omega

/-- The freedom in repeated-entry triples gives only quadratically many collisions. -/
lemma double_single_collision_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A)
    (Q : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hQ : ∀ p ∈ Q, p.1.1 ∈ S ∧ p.1.2 ∈ S ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S ∧
      2 * p.1.1 + p.1.2 = 2 * p.2.1 + p.2.2) :
    Q.card ≤ 6 * S.card^2 := by
  classical
  let D := Q.filter (fun p => p.1.1 = p.2.1)
  let O := Q.filter (fun p => p.1.1 ≠ p.2.1)
  have hD : D.card ≤ S.card^2 := by
    calc
      D.card ≤ (S ×ˢ S).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1)
        · intro p hp
          obtain ⟨hpQ, _⟩ := Finset.mem_filter.mp hp
          have hp' := hQ p hpQ
          exact Finset.mem_product.mpr ⟨hp'.1, hp'.2.1⟩
        · intro p hp q hq he
          change p.1 = q.1 at he
          obtain ⟨hpQ, hpc⟩ := Finset.mem_filter.mp hp
          obtain ⟨hqQ, hqc⟩ := Finset.mem_filter.mp hq
          have hps := (hQ p hpQ).2.2.2.2
          have hqs := (hQ q hqQ).2.2.2.2
          have he1 : p.1.1 = q.1.1 := congrArg (fun v : ℕ × ℕ => v.1) he
          have he2 : p.1.2 = q.1.2 := congrArg (fun v : ℕ × ℕ => v.2) he
          exact Prod.ext he (Prod.ext (by omega) (by omega))
      _ = S.card^2 := by simp [pow_two]
  let f : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ := fun p => (p.1.1, p.2.1)
  have hmaps : Set.MapsTo f (O : Set ((ℕ × ℕ) × (ℕ × ℕ)))
      ((S ×ˢ S : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro p hp
    have hp' := hQ p (Finset.mem_filter.mp hp).1
    change (p.1.1, p.2.1) ∈ (S ×ˢ S : Finset (ℕ × ℕ))
    exact Finset.mem_product.mpr ⟨hp'.1, hp'.2.2.1⟩
  have hfib : ∀ x ∈ S ×ˢ S, (O.filter (fun p => f p = x)).card ≤ 5 := by
    intro x hx
    let R := O.filter (fun p => f p = x)
    by_cases hxe : x.1 = x.2
    · have hR : R = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hpO, hpx⟩ := Finset.mem_filter.mp hp
        have hpne := (Finset.mem_filter.mp hpO).2
        have hp1 : p.1.1 = x.1 := by simpa only [f] using congrArg (fun v : ℕ × ℕ => v.1) hpx
        have hp2 : p.2.1 = x.2 := by simpa only [f] using congrArg (fun v : ℕ × ℕ => v.2) hpx
        exact hpne (hp1.trans (hxe.trans hp2.symm))
      change R.card ≤ 5
      simp [hR]
    let g : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ := fun p => (p.1.2, p.2.2)
    have hg : Set.InjOn g (R : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
      intro p hp q hq he
      have hpx := (Finset.mem_filter.mp hp).2
      have hqx := (Finset.mem_filter.mp hq).2
      have hpfq : f p = f q := hpx.trans hqx.symm
      have ha : p.1.1 = q.1.1 := by simpa only [f] using congrArg (fun v : ℕ × ℕ => v.1) hpfq
      have hc : p.2.1 = q.2.1 := by simpa only [f] using congrArg (fun v : ℕ × ℕ => v.2) hpfq
      have hb : p.1.2 = q.1.2 := by simpa only [g] using congrArg (fun v : ℕ × ℕ => v.1) he
      have hd : p.2.2 = q.2.2 := by simpa only [g] using congrArg (fun v : ℕ × ℕ => v.2) he
      exact Prod.ext (Prod.ext ha hb) (Prod.ext hc hd)
    change R.card ≤ 5
    rw [← Finset.card_image_of_injOn hg]
    apply nonzero_difference_fiber_card_le_five h hA
      (t := 2 * (x.2 : ℤ) - 2 * (x.1 : ℤ)) (by intro he; apply hxe; omega)
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqO, hqx⟩ := Finset.mem_filter.mp hq
    obtain ⟨ha, hb, hc, hd, hs⟩ := hQ q (Finset.mem_filter.mp hqO).1
    have hx1 : q.1.1 = x.1 := by simpa only [f] using congrArg (fun v : ℕ × ℕ => v.1) hqx
    have hx2 : q.2.1 = x.2 := by simpa only [f] using congrArg (fun v : ℕ × ℕ => v.2) hqx
    exact ⟨hS hb, hS hd, by dsimp [g]; omega⟩
  have hO : O.card ≤ 5 * S.card^2 := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      ∑ x ∈ S ×ˢ S, (O.filter (fun p => f p = x)).card ≤ ∑ _ ∈ S ×ˢ S, 5 :=
        Finset.sum_le_sum hfib
      _ = 5 * S.card^2 := by simp [pow_two, mul_comm]
  have hcover : Q ⊆ D ∪ O := by
    intro p hp
    by_cases hpe : p.1.1 = p.2.1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hpe⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hpe⟩)
  calc
    Q.card ≤ (D ∪ O).card := Finset.card_le_card hcover
    _ ≤ D.card + O.card := Finset.card_union_le _ _
    _ ≤ 6 * S.card^2 := by omega


/-- A repeated-entry sum can coincide with at most one distinct-entry triple. -/
lemma repeated_distinct_collision_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A)
    (R : Finset ((ℕ × ℕ) × Finset ℕ))
    (hR : ∀ p ∈ R, p.1.1 ∈ S ∧ p.1.2 ∈ S ∧ p.2 ⊆ S ∧ p.2.card = 3 ∧
      2 * p.1.1 + p.1.2 = ∑ a ∈ p.2, a) : R.card ≤ S.card^2 := by
  classical
  calc
    R.card ≤ (S ×ˢ S).card := by
      apply Finset.card_le_card_of_injOn (fun p => p.1)
      · intro p hp
        have hp' := hR p hp
        exact Finset.mem_product.mpr ⟨hp'.1, hp'.2.1⟩
      · intro p hp q hq he
        change p.1 = q.1 at he
        obtain ⟨hp1, hp2, hpS, hpc, hps⟩ := hR p hp
        obtain ⟨hq1, hq2, hqS, hqc, hqs⟩ := hR q hq
        refine Prod.ext he (h p.2 q.2 ⟨?_, ?_, hpc, hqc, ?_⟩)
        · intro a ha
          exact hS (hpS ha)
        · intro a ha
          exact hS (hqS ha)
        · rw [← hps, ← hqs, he]
    _ = S.card^2 := by simp [pow_two]


abbrev NatTriple := ℕ × ℕ × ℕ

def tripleTotal (p : NatTriple) : ℕ := p.1 + p.2.1 + p.2.2

def tripleDistinct (p : NatTriple) : Prop :=
  p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2

instance (p : NatTriple) : Decidable (tripleDistinct p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def triplePermutations (p : NatTriple) : Finset NatTriple :=
  {(p.1, p.2.1, p.2.2), (p.1, p.2.2, p.2.1), (p.2.1, p.1, p.2.2),
   (p.2.1, p.2.2, p.1), (p.2.2, p.1, p.2.1), (p.2.2, p.2.1, p.1)}

lemma ordered_distinct_triple_fiber_card_le_six {A : Set ℕ} (h : NtupleCondition A 3)
    (R : Finset NatTriple) (t : ℕ)
    (hR : ∀ p ∈ R, p.1 ∈ A ∧ p.2.1 ∈ A ∧ p.2.2 ∈ A ∧
      tripleDistinct p ∧ tripleTotal p = t) : R.card ≤ 6 := by
  classical
  by_cases he : R = ∅
  · simp [he]
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨hp1, hp2, hp3, hpd, hpt⟩ := hR p hp
  obtain ⟨hp12, hp13, hp23⟩ := hpd
  have hsub : R ⊆ triplePermutations p := by
    intro q hq
    obtain ⟨hq1, hq2, hq3, hqd, hqt⟩ := hR q hq
    obtain ⟨hq12, hq13, hq23⟩ := hqd
    have hs : ({q.1, q.2.1, q.2.2} : Finset ℕ) = {p.1, p.2.1, p.2.2} := by
      apply h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · simp [hq12, hq13, hq23]
      · simp [hp12, hp13, hp23]
      · simpa [tripleTotal, hq12, hq13, hq23, hp12, hp13, hp23, add_assoc]
          using hqt.trans hpt.symm
    have hq1' : q.1 = p.1 ∨ q.1 = p.2.1 ∨ q.1 = p.2.2 := by
      have hm : q.1 ∈ ({p.1, p.2.1, p.2.2} : Finset ℕ) := hs ▸ (by simp)
      simpa using hm
    have hq2' : q.2.1 = p.1 ∨ q.2.1 = p.2.1 ∨ q.2.1 = p.2.2 := by
      have hm : q.2.1 ∈ ({p.1, p.2.1, p.2.2} : Finset ℕ) := hs ▸ (by simp)
      simpa using hm
    have hq3' : q.2.2 = p.1 ∨ q.2.2 = p.2.1 ∨ q.2.2 = p.2.2 := by
      have hm : q.2.2 ∈ ({p.1, p.2.1, p.2.2} : Finset ℕ) := hs ▸ (by simp)
      simpa using hm
    rcases hq1' with h1 | h1 | h1 <;>
      rcases hq2' with h2 | h2 | h2 <;>
      rcases hq3' with h3 | h3 | h3 <;>
      simp_all [triplePermutations, Prod.ext_iff]
  exact (Finset.card_le_card hsub).trans Finset.card_le_six

def repeatedTriples (p : ℕ × ℕ) : Finset NatTriple :=
  {(p.1, p.1, p.2), (p.1, p.2, p.1), (p.2, p.1, p.1)}

lemma repeatedTriple_encoding (S : Finset ℕ) {p : NatTriple}
    (hp : p ∈ S ×ˢ (S ×ˢ S)) (hd : ¬ tripleDistinct p) :
    ∃ q ∈ S ×ˢ S, p ∈ repeatedTriples q ∧ tripleTotal p = 2*q.1 + q.2 := by
  obtain ⟨hp1, hp23⟩ := Finset.mem_product.mp hp
  obtain ⟨hp2, hp3⟩ := Finset.mem_product.mp hp23
  simp only [tripleDistinct, not_and_or, not_not] at hd
  rcases hd with h12 | h13 | h23
  · refine ⟨(p.1, p.2.2), Finset.mem_product.mpr ⟨hp1, hp3⟩, ?_, ?_⟩
    · simp [repeatedTriples, Prod.ext_iff, h12]
    · dsimp [tripleTotal]; omega
  · refine ⟨(p.1, p.2.1), Finset.mem_product.mpr ⟨hp1, hp2⟩, ?_, ?_⟩
    · simp [repeatedTriples, Prod.ext_iff, h13]
    · dsimp [tripleTotal]; omega
  · refine ⟨(p.2.1, p.1), Finset.mem_product.mpr ⟨hp2, hp1⟩, ?_, ?_⟩
    · simp [repeatedTriples, Prod.ext_iff, h23]
    · dsimp [tripleTotal]; omega

lemma repeated_triple_card_bound (S : Finset ℕ) :
    ((S ×ˢ (S ×ˢ S)).filter (fun p => ¬ tripleDistinct p)).card ≤ 3*S.card^2 := by
  have hsub : (S ×ˢ (S ×ˢ S)).filter (fun p => ¬ tripleDistinct p) ⊆
      (S ×ˢ S).biUnion repeatedTriples := by
    intro p hp
    obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
    obtain ⟨q, hq, hpq, _⟩ := repeatedTriple_encoding S hpS hpd
    exact Finset.mem_biUnion.mpr ⟨q, hq, hpq⟩
  calc
    _ ≤ ((S ×ˢ S).biUnion repeatedTriples).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ S ×ˢ S, (repeatedTriples p).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ S ×ˢ S, 3 := Finset.sum_le_sum (fun _ _ => Finset.card_le_three)
    _ = 3*S.card^2 := by simp [pow_two, mul_comm]


lemma right_distinct_collision_card_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (T : Finset NatTriple) (Q : Finset (NatTriple × NatTriple))
    (hQ : ∀ p ∈ Q, p.1 ∈ T ∧ p.2.1 ∈ A ∧ p.2.2.1 ∈ A ∧ p.2.2.2 ∈ A ∧
      tripleDistinct p.2 ∧ tripleTotal p.1 = tripleTotal p.2) : Q.card ≤ 6*T.card := by
  classical
  apply Finset.card_le_mul_card_image_of_maps_to (fun p hp => (hQ p hp).1) 6
  intro t ht
  let R := Q.filter (fun p => p.1 = t)
  have hi : Set.InjOn Prod.snd (R : Set (NatTriple × NatTriple)) := by
    intro p hp q hq he
    have hp1 := (Finset.mem_filter.mp hp).2
    have hq1 := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hp1.trans hq1.symm) he
  change R.card ≤ 6
  rw [← Finset.card_image_of_injOn hi]
  apply ordered_distinct_triple_fiber_card_le_six h _ (tripleTotal t)
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hqQ, hqt⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, hq1, hq2, hq3, hqd, hqs⟩ := hQ q hqQ
  exact ⟨hq1, hq2, hq3, hqd, by rw [← hqs, hqt]⟩

/-- Sixth additive energy has the same leading cubic bound as for full `B₃` sets. -/
lemma ordered_triple_collision_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A)
    (Q : Finset (NatTriple × NatTriple))
    (hQ : ∀ p ∈ Q, p.1 ∈ S ×ˢ (S ×ˢ S) ∧ p.2 ∈ S ×ˢ (S ×ˢ S) ∧
      tripleTotal p.1 = tripleTotal p.2) :
    Q.card ≤ 6*S.card^3 + 72*S.card^2 := by
  classical
  let T := S ×ˢ (S ×ˢ S)
  let Bad := T.filter (fun p => ¬ tripleDistinct p)
  have hBad : Bad.card ≤ 3*S.card^2 := repeated_triple_card_bound S
  let G := Q.filter (fun p => tripleDistinct p.2)
  let H := Q.filter (fun p => ¬ tripleDistinct p.2 ∧ tripleDistinct p.1)
  let B := Q.filter (fun p => ¬ tripleDistinct p.1 ∧ ¬ tripleDistinct p.2)
  have hG : G.card ≤ 6*S.card^3 := by
    have hh := right_distinct_collision_card_bound h T G (by
      intro p hp
      obtain ⟨hpQ, hpd⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2, hps⟩ := hQ p hpQ
      obtain ⟨hp21, hp22⟩ := Finset.mem_product.mp hp2
      obtain ⟨hp221, hp222⟩ := Finset.mem_product.mp hp22
      exact ⟨hp1, hS hp21, hS hp221, hS hp222, hpd, hps⟩)
    simpa [T, pow_succ, pow_two, mul_assoc] using hh
  have hH : H.card ≤ 18*S.card^2 := by
    have hi : Set.InjOn Prod.swap (H : Set (NatTriple × NatTriple)) := by
      intro p hp q hq he
      have he' := congrArg Prod.swap he
      simpa using he'
    have hh := right_distinct_collision_card_bound h Bad (H.image Prod.swap) (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqQ, hqd2, hqd1⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq1, hq2, hqs⟩ := hQ q hqQ
      obtain ⟨hq11, hq12⟩ := Finset.mem_product.mp hq1
      obtain ⟨hq121, hq122⟩ := Finset.mem_product.mp hq12
      exact ⟨Finset.mem_filter.mpr ⟨hq2, hqd2⟩,
        hS hq11, hS hq121, hS hq122, hqd1, hqs.symm⟩)
    rw [Finset.card_image_of_injOn hi] at hh
    omega
  let D := ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
    (fun p => 2*p.1.1 + p.1.2 = 2*p.2.1 + p.2.2)
  have hD : D.card ≤ 6*S.card^2 := by
    apply double_single_collision_count_bound h hA S hS
    intro p hp
    obtain ⟨hpD, hps⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpD
    obtain ⟨hp11, hp12⟩ := Finset.mem_product.mp hp1
    obtain ⟨hp21, hp22⟩ := Finset.mem_product.mp hp2
    exact ⟨hp11, hp12, hp21, hp22, hps⟩
  let box := fun p : (ℕ × ℕ) × (ℕ × ℕ) => repeatedTriples p.1 ×ˢ repeatedTriples p.2
  have hBsub : B ⊆ D.biUnion box := by
    intro p hp
    obtain ⟨hpQ, hpd1, hpd2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2, hps⟩ := hQ p hpQ
    obtain ⟨u, hu, hpu, hsu⟩ := repeatedTriple_encoding S hp1 hpd1
    obtain ⟨v, hv, hpv, hsv⟩ := repeatedTriple_encoding S hp2 hpd2
    apply Finset.mem_biUnion.mpr
    refine ⟨(u,v), ?_, Finset.mem_product.mpr ⟨hpu, hpv⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu,hv⟩, by dsimp only; omega⟩
  have hbox : ∀ p, (box p).card ≤ 9 := by
    intro p
    have h1 : (repeatedTriples p.1).card ≤ 3 := Finset.card_le_three
    have h2 : (repeatedTriples p.2).card ≤ 3 := Finset.card_le_three
    simp only [box, Finset.card_product]
    nlinarith
  have hB : B.card ≤ 54*S.card^2 := by
    calc
      B.card ≤ (D.biUnion box).card := Finset.card_le_card hBsub
      _ ≤ ∑ p ∈ D, (box p).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ D, 9 := Finset.sum_le_sum (fun p _ => hbox p)
      _ = 9*D.card := by simp [mul_comm]
      _ ≤ 54*S.card^2 := by omega
  have hsub : Q ⊆ (G ∪ H) ∪ B := by
    intro p hp
    by_cases h2 : tripleDistinct p.2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h2⟩))
    by_cases h1 : tripleDistinct p.1
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h2, h1⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h1, h2⟩)
  calc
    Q.card ≤ ((G ∪ H) ∪ B).card := Finset.card_le_card hsub
    _ ≤ (G ∪ H).card + B.card := Finset.card_union_le _ _
    _ ≤ G.card + H.card + B.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 6*S.card^3 + 72*S.card^2 := by omega


lemma initialSegment_card_le_count (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) :
    (initialSegment A N).card ≤ Nat.count (· ∈ A) (N+1) := by
  classical
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨haA, ha1, haN⟩ := mem_initialSegment.mp ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), haA⟩

lemma failure_yields_cubic_enumeration {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite)
    (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0) :
    ∃ (a : ℕ → ℕ) (C : ℕ), 0 < C ∧ StrictMono a ∧ Set.range a = A ∧
      ∀ n, a n ≤ C*(n+1)^3 := by
  classical
  obtain ⟨ε, hε, M, hM⟩ := (density_liminf_ne_zero_iff h).mp hf
  obtain ⟨L, hL⟩ := exists_nat_gt (max ((M : ℝ)+1) (1/ε))
  have hLM : M+1 ≤ L := by
    have : (M : ℝ)+1 < L := (le_max_left _ _).trans_lt hL
    exact_mod_cast this.le
  have hLp : 0 < L := by omega
  have hεL : 1 ≤ ε*(L : ℝ) := by
    have : 1/ε < (L : ℝ) := (le_max_right _ _).trans_lt hL
    exact le_of_lt ((div_lt_iff₀ hε).mp this |>.trans_eq (mul_comm _ _))
  refine ⟨Nat.nth (· ∈ A), L^3, by positivity, Nat.nth_strictMono hA,
    Nat.range_nth_of_infinite hA, ?_⟩
  intro n
  let t := L*(n+1)
  have ht : 1 ≤ t := by dsimp [t]; nlinarith
  have hMt : M ≤ t^3 := by
    have hLt : L ≤ t := by dsimp [t]; nlinarith
    have : t ≤ t^3 := by nlinarith [sq_nonneg (t : ℤ)]
    omega
  have hroot : ((t^3 : ℕ) : ℝ)^(1/3 : ℝ) = (t : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
    norm_num
  have hcount : n+1 ≤ (initialSegment A (t^3)).card := by
    have hd := hM (t^3) hMt
    rw [hroot, ← card_initialSegment] at hd
    have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    have hεt := (le_div_iff₀ htR).mp hd
    have hnl : (n : ℝ)+1 ≤ ε*(t : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hεL (show (0 : ℝ) ≤ n+1 by positivity)
      simpa [t, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hmul
    exact_mod_cast hnl.trans hεt
  have hn : n < Nat.count (· ∈ A) (t^3+1) :=
    lt_of_lt_of_le (show n < (initialSegment A (t^3)).card by omega)
      (initialSegment_card_le_count A (t^3))
  have hnth := Nat.nth_lt_of_lt_count hn
  have : Nat.nth (· ∈ A) n ≤ t^3 := by omega
  simpa [t, mul_pow] using this


lemma cubic_enumeration_density_lower_bound {A : Set ℕ} {a : ℕ → ℕ} {C : ℕ}
    (hC : 0 < C) (ha : StrictMono a) (haA : Set.range a ⊆ A)
    (hbound : ∀ n, a n ≤ C*(n+1)^3) {N : ℕ} (hN : (4*C)^3 ≤ N) :
    1 / (2*(C : ℝ)) ≤ (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ) := by
  classical
  let k := (initialSegment A N).card
  have hNa : N < a (k+1) := by
    by_contra! hle
    have hsub : (Finset.Icc 1 (k+1)).image a ⊆ initialSegment A N := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hi1, hik⟩ := Finset.mem_Icc.mp hi
      exact mem_initialSegment.mpr ⟨haA (Set.mem_range_self i),
        hi1.trans (ha.id_le i), (ha.monotone hik).trans hle⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ ha.injective, Nat.card_Icc] at hc
    change k+1+1-1 ≤ k at hc
    omega
  have hNk : N ≤ (C*(k+2))^3 := by
    have hC3 : C ≤ C^3 := by nlinarith [Nat.zero_le (C^2)]
    have hm := Nat.mul_le_mul_right ((k+2)^3) hC3
    rw [← mul_pow] at hm
    have hh := hbound (k+1)
    have : k+1+1 = k+2 := by omega
    rw [this] at hh
    omega
  let r := (N : ℝ)^(1/3 : ℝ)
  have hr0 : 0 ≤ r := by positivity
  have hr3 : r^3 = (N : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hCr : 4*(C : ℝ) ≤ r := by
    apply (pow_le_pow_iff_left₀ (by positivity) hr0 (by decide : (3 : ℕ) ≠ 0)).mp
    rw [hr3]
    exact_mod_cast hN
  have hrk : r ≤ (C : ℝ)*((k : ℝ)+2) := by
    apply (pow_le_pow_iff_left₀ hr0 (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
    rw [hr3]
    exact_mod_cast hNk
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  have hrp : 0 < r := by linarith
  have hkr : r ≤ 2*(C : ℝ)*(k : ℝ) := by nlinarith
  rw [← card_initialSegment]
  change 1 / (2*(C : ℝ)) ≤ (k : ℝ) / r
  apply (div_le_div_iff₀ (by positivity) hrp).mpr
  nlinarith

lemma density_liminf_eq_zero_iff_no_cubic_enumeration {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite) :
    Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 ↔
    ¬ ∃ (a : ℕ → ℕ) (C : ℕ), 0 < C ∧ StrictMono a ∧ Set.range a ⊆ A ∧
      ∀ n, a n ≤ C*(n+1)^3 := by
  constructor
  · intro hz ⟨a, C, hC, ha, haA, hbound⟩
    have hn : Filter.atTop.liminf
        (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0 := by
      apply (density_liminf_ne_zero_iff h).mpr
      refine ⟨1/(2*(C : ℝ)), by positivity, (4*C)^3, ?_⟩
      intro N hN
      exact cubic_enumeration_density_lower_bound hC ha haA hbound hN
    exact hn hz
  · intro hn
    by_contra hz
    obtain ⟨a, C, hC, ha, haA, hbound⟩ := failure_yields_cubic_enumeration h hA hz
    exact hn ⟨a, C, hC, ha, haA.subset, hbound⟩


lemma NtupleCondition.mono {α : Type} [AddCommMonoid α] {A B : Set α} {n : ℕ}
    (h : NtupleCondition A n) (hBA : B ⊆ A) : NtupleCondition B n := by
  intro I J ⟨hI, hJ, hIc, hJc, hs⟩
  exact h I J ⟨hI.trans hBA, hJ.trans hBA, hIc, hJc, hs⟩

/-- A finite, cubically bounded, increasing configuration with distinct triple sums. -/
abbrev CubicConfiguration (C n : ℕ) :=
  {a : (i : Fin n) → Fin (C*((i : ℕ)+1)^3+1) //
    StrictMono (fun i => (a i : ℕ)) ∧
    NtupleCondition (Set.range (fun i => (a i : ℕ))) 3}

def CubicConfiguration.restrict {C m n : ℕ} (hmn : m ≤ n)
    (a : CubicConfiguration C n) : CubicConfiguration C m :=
  ⟨fun i => a.1 (i.castLE hmn),
    (a.2.1.comp (fun i j hij => hij)),
    a.2.2.mono (by rintro x ⟨i, rfl⟩; exact ⟨i.castLE hmn, rfl⟩)⟩

lemma CubicConfiguration.restrict_refl {C n : ℕ} (a : CubicConfiguration C n) :
    a.restrict (le_refl n) = a := by
  apply Subtype.ext
  funext i
  rfl

lemma CubicConfiguration.restrict_trans {C l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (a : CubicConfiguration C n) :
    (a.restrict hmn).restrict hlm = a.restrict (hlm.trans hmn) := by
  apply Subtype.ext
  funext i
  rfl

lemma exists_cubic_sequence_of_finite_configurations (C : ℕ)
    (h : ∀ n, Nonempty (CubicConfiguration C n)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ NtupleCondition (Set.range a) 3 ∧
      ∀ n, a n ≤ C*(n+1)^3 := by
  classical
  letI : ∀ n, Nonempty (CubicConfiguration C n) := h
  obtain ⟨q, hq⟩ := exists_seq_forall_proj_of_forall_finite
    (fun {_ _} hmn a => CubicConfiguration.restrict (C := C) hmn a)
    (fun _ a => a.restrict_refl)
    (fun _ _ _ hlm hmn a => a.restrict_trans hlm hmn)
    (fun _ _ => Set.toFinite _)
  let a : ℕ → ℕ := fun i => (q (i+1)).1 (Fin.last i)
  have he : ∀ n (i : Fin n), a i = ((q n).1 i : ℕ) := by
    intro n i
    have hp := hq (Nat.succ_le_of_lt i.isLt)
    have hh := congrArg (fun b : CubicConfiguration C (i+1) =>
      ((b.1 (Fin.last i)) : ℕ)) hp
    exact hh.symm
  have ha : StrictMono a := by
    intro i j hij
    have hh := (q (j+1)).2.1 (show (⟨i, by omega⟩ : Fin (j+1)) < Fin.last j from hij)
    simpa only [← he] using hh
  refine ⟨a, ha, ?_, ?_⟩
  · intro I J ⟨hI, hJ, hIc, hJc, hs⟩
    let M := (I ∪ J).sup id + 1
    have hsub : ∀ S : Finset ℕ, S ⊆ I ∪ J → (S : Set ℕ) ⊆ Set.range a →
        (S : Set ℕ) ⊆ Set.range (fun i => ((q M).1 i : ℕ)) := by
      intro S hS hSA x hx
      obtain ⟨i, rfl⟩ := hSA hx
      have hmax : a i ≤ (I ∪ J).sup id := Finset.le_sup (f := id) (hS hx)
      have hiM : i < M := by
        have hii : i ≤ a i := ha.id_le i
        dsimp [M]
        omega
      exact ⟨⟨i, hiM⟩, (he M ⟨i, hiM⟩).symm⟩
    exact (q M).2.2 I J ⟨hsub I Finset.subset_union_left hI,
      hsub J Finset.subset_union_right hJ, hIc, hJc, hs⟩
  · intro n
    exact Nat.le_of_lt_succ ((q (n+1)).1 (Fin.last n)).isLt



def CubicConfiguration.ofSequence {C : ℕ} (a : ℕ → ℕ) (ha : StrictMono a)
    (h3 : NtupleCondition (Set.range a) 3) (hbound : ∀ i, a i ≤ C*(i+1)^3)
    (n : ℕ) : CubicConfiguration C n :=
  ⟨fun i => ⟨a i, Nat.lt_succ_of_le (hbound i)⟩,
    (fun i j hij => ha hij),
    h3.mono (by rintro x ⟨i, rfl⟩; exact ⟨i, rfl⟩)⟩

lemma exists_cubic_sequence_iff_finite_configurations (C : ℕ) :
    (∃ a : ℕ → ℕ, StrictMono a ∧ NtupleCondition (Set.range a) 3 ∧
      ∀ n, a n ≤ C*(n+1)^3) ↔
    ∀ n, Nonempty (CubicConfiguration C n) := by
  constructor
  · rintro ⟨a, ha, h3, hbound⟩ n
    exact ⟨CubicConfiguration.ofSequence a ha h3 hbound n⟩
  · exact exists_cubic_sequence_of_finite_configurations C

/-- An exact finitary reformulation. It does not assert that the obstructions exist. -/
lemma conjecture_iff_finite_obstructions :
    (∀ A : Set ℕ, NtupleCondition A 3 → A.Infinite →
      Filter.atTop.liminf
        (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0) ↔
    ∀ C : ℕ, 0 < C → ∃ n : ℕ, ¬ Nonempty (CubicConfiguration C n) := by
  constructor
  · intro hall C hC
    by_contra! hn
    obtain ⟨a, ha, h3, hbound⟩ := exists_cubic_sequence_of_finite_configurations C hn
    have hA : (Set.range a).Infinite := Set.infinite_range_of_injective ha.injective
    have hz := hall (Set.range a) h3 hA
    have hnone := (density_liminf_eq_zero_iff_no_cubic_enumeration h3 hA).mp hz
    exact hnone ⟨a, C, hC, ha, Set.Subset.rfl, hbound⟩
  · intro hfinite A h3 hA
    by_contra hz
    obtain ⟨a, C, hC, ha, haA, hbound⟩ := failure_yields_cubic_enumeration h3 hA hz
    obtain ⟨n, hn⟩ := hfinite C hC
    have h3' : NtupleCondition (Set.range a) 3 := h3.mono haA.subset
    exact hn ⟨CubicConfiguration.ofSequence a ha h3' hbound n⟩


lemma count_le_initialSegment_card_add_one (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) :
    Nat.count (· ∈ A) (N+1) ≤ (initialSegment A N).card + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  have hsub : (Finset.range (N+1)).filter (· ∈ A) ⊆ insert 0 (initialSegment A N) := by
    intro x hx
    obtain ⟨hxN, hxA⟩ := Finset.mem_filter.mp hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · exact Finset.mem_insert_of_mem (mem_initialSegment.mpr
        ⟨hxA, by omega, by simpa using Finset.mem_range.mp hxN⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

lemma cubic_gap_sum_bound {a : ℕ → ℕ} {C : ℕ}
    (hgap : ∀ i, a (i+1) ≤ a i + C*(i+1)^2) {m n : ℕ} (hmn : m ≤ n) :
    a n ≤ a m + C*(n-m)*(n+1)^2 := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hsub : n+1-m = (n-m)+1 := by omega
    calc
      a (n+1) ≤ a n + C*(n+1)^2 := hgap n
      _ ≤ (a m + C*(n-m)*(n+1)^2) + C*(n+1)^2 := Nat.add_le_add_right ih _
      _ = a m + C*((n-m)+1)*(n+1)^2 := by ring
      _ ≤ a m + C*(n+1-m)*(n+1+1)^2 := by rw [hsub]; gcongr; omega

lemma intervalBin_lower_of_nth_gap_bound {A : Set ℕ} (hA : A.Infinite) {C : ℕ}
    (hgap : ∀ i, Nat.nth (· ∈ A) (i+1) ≤ Nat.nth (· ∈ A) i + C*(i+1)^2)
    {H m : ℕ} (hm : 1 ≤ m) (hH : Nat.nth (· ∈ A) 0 + 1 ≤ H) :
    H ≤ C*((intervalBin A H m).card + 2)*
      ((initialSegment A ((m+1)*H)).card + 2)^2 := by
  classical
  let X := m*H
  let Y := (m+1)*H
  let l := Nat.count (· ∈ A) (X+1)
  let n := Nat.count (· ∈ A) (Y+1)
  have hXY : X ≤ Y := Nat.mul_le_mul_right H (Nat.le_succ m)
  have hl : 1 ≤ l := by
    have haX : Nat.nth (· ∈ A) 0 + 1 ≤ X+1 := by
      have hmH : H ≤ m*H := Nat.le_mul_of_pos_left H hm
      dsimp [X]
      omega
    have hh := (Nat.count_monotone (· ∈ A)) haX
    rw [Nat.count_nth_succ_of_infinite (p := fun x => x ∈ A) hA 0] at hh
    exact hh
  have hln : l ≤ n := Nat.count_monotone _ (by omega)
  have hlow : Nat.nth (· ∈ A) (l-1) ≤ X := by
    have hh := Nat.nth_lt_of_lt_count (show l-1 < Nat.count (· ∈ A) (X+1) by change l-1 < l; omega)
    omega
  have hhigh : Y+1 ≤ Nat.nth (· ∈ A) n := Nat.le_nth_count hA (Y+1)
  have hstep := cubic_gap_sum_bound hgap (show l-1 ≤ n by omega)
  have hc : (intervalBin A H m).card + (initialSegment A X).card =
      (initialSegment A Y).card :=
    Finset.card_sdiff_add_card_eq_card (initialSegment_mono A hXY)
  have hn : n ≤ (initialSegment A Y).card + 1 := count_le_initialSegment_card_add_one A Y
  have hl' : (initialSegment A X).card ≤ l := initialSegment_card_le_count A X
  have hdiff : n-(l-1) ≤ (intervalBin A H m).card+2 := by omega
  have hn' : n+1 ≤ (initialSegment A Y).card+2 := by omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left C hdiff) (Nat.pow_le_pow_left hn' 2)
  have hYX : Y = X+H := by dsimp [X,Y]; ring
  change H ≤ C*((intervalBin A H m).card + 2)*
    ((initialSegment A Y).card + 2)^2
  omega



lemma normalized_bin_lower_of_nth_gap_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) {C : ℕ}
    (hgap : ∀ j, Nat.nth (· ∈ A) (j+1) ≤ Nat.nth (· ∈ A) j + C*(j+1)^2)
    {H m i : ℕ} (hm : 1 ≤ m) (hmi : m+1 ≤ 8^(i+1))
    (hH : Nat.nth (· ∈ A) 0 + 1 ≤ H) :
    (1 : ℝ) ≤ (144*(C : ℝ)*4^i) *
      (((intervalBin A H m).card : ℝ)/(H : ℝ)^(1/3 : ℝ) +
        2*((H : ℝ)^(1/3 : ℝ))⁻¹) := by
  have hH1 : 1 ≤ H := by omega
  let r := (H : ℝ)^(1/3 : ℝ)
  have hr1 : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast hH1) (by norm_num)
  have hr : 0 < r := by linarith
  have hr3 : r^3 = (H : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hmroot : ((m+1 : ℕ) : ℝ)^(1/3 : ℝ) ≤ (2 : ℝ)^(i+1) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
    rw [← Real.rpow_mul_natCast (by positivity), pow_right_comm]
    norm_num
    exact_mod_cast hmi
  have hpre := (normalized_prefix_le h H (m+1) hH1).trans (mul_le_mul_of_nonneg_left hmroot (by norm_num : (0 : ℝ) ≤ 5))
  have hpre' : ((initialSegment A ((m+1)*H)).card : ℝ) ≤ 5*(2 : ℝ)^(i+1)*r :=
    (div_le_iff₀ hr).mp hpre
  have hp1 : 1 ≤ (2 : ℝ)^i := one_le_pow₀ (by norm_num)
  have hprod : 1 ≤ (2 : ℝ)^i*r := one_le_mul_of_one_le_of_one_le hp1 hr1
  have hp2 : ((2 : ℝ)^i)^2 = (4 : ℝ)^i := by rw [pow_right_comm]; norm_num
  have hpre2 : ((initialSegment A ((m+1)*H)).card : ℝ) + 2 ≤ 12*(2 : ℝ)^i*r := by
    rw [pow_succ] at hpre'
    nlinarith
  have hnat := intervalBin_lower_of_nth_gap_bound hA hgap hm hH
  have hreal : (H : ℝ) ≤ (C : ℝ)*((intervalBin A H m).card+2)*
      (((initialSegment A ((m+1)*H)).card : ℝ)+2)^2 := by exact_mod_cast hnat
  have hineq : (H : ℝ) ≤ (C : ℝ)*((intervalBin A H m).card+2)*
      (12*(2 : ℝ)^i*r)^2 :=
    hreal.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpre2 2) (by positivity))
  have hrbound : r ≤ (144*(C : ℝ)*4^i)*((intervalBin A H m).card+2) := by
    apply (mul_le_mul_iff_right₀ (show 0 < r^2 by positivity)).mp
    calc
      r^2*r = (H : ℝ) := by nlinarith [hr3]
      _ ≤ (C : ℝ)*((intervalBin A H m).card+2)*(12*(2 : ℝ)^i*r)^2 := hineq
      _ = r^2*((144*(C : ℝ)*4^i)*((intervalBin A H m).card+2)) := by
        simp only [mul_pow, hp2]
        ring
  change 1 ≤ (144*(C : ℝ)*4^i)*(((intervalBin A H m).card : ℝ)/r + 2*r⁻¹)
  have hh : 1 ≤ ((144*(C : ℝ)*4^i)*((intervalBin A H m).card+2))/r :=
    (le_div_iff₀ hr).mpr (by simpa using hrbound)
  convert hh using 1; ring



lemma scaling_limit_bin_lower_of_nth_gap_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) {C : ℕ}
    (hgap : ∀ j, Nat.nth (· ∈ A) (j+1) ≤ Nat.nth (· ∈ A) j + C*(j+1)^2)
    {F : ℕ → ℝ} {τ : ℕ → ℕ} (hτ : StrictMono τ)
    (hlim : ∀ m, Tendsto (fun n => ((initialSegment A (m * (τ n + 1))).card : ℝ) /
      ((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (F m)))
    {m i : ℕ} (hm : 1 ≤ m) (hmi : m+1 ≤ 8^(i+1)) :
    (1 : ℝ) ≤ (144*(C : ℝ)*4^i)*(F (m+1)-F m) := by
  have hτlim : Tendsto (fun n => τ n + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hτ.tendsto_atTop
  have hroot : Tendsto (fun n => (((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp
      (tendsto_natCast_atTop_atTop.comp hτlim))
  have ht : Tendsto (fun n => (144*(C : ℝ)*4^i)*
      (((intervalBin A (τ n + 1) m).card : ℝ)/((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ) +
        2*((((τ n + 1 : ℕ) : ℝ)^(1/3 : ℝ))⁻¹)))
      atTop (nhds ((144*(C : ℝ)*4^i)*(F (m+1)-F m))) := by
    simpa using ((scaling_limit_intervalBin hlim m).add (hroot.const_mul 2)).const_mul
      (144*(C : ℝ)*4^i)
  apply ge_of_tendsto ht
  filter_upwards [hτlim.eventually (eventually_ge_atTop (Nat.nth (· ∈ A) 0 + 1))] with n hn
  exact normalized_bin_lower_of_nth_gap_bound h hA hgap hm hmi hn

/-- Cubic-scale bounded successive gaps are incompatible with distinct triple sums.
This is a conditional obstruction, not the liminf conjecture. -/
lemma not_bounded_quadratic_nth_gaps {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (C : ℕ) :
    ¬ (∀ j, Nat.nth (· ∈ A) (j+1) ≤ Nat.nth (· ∈ A) j + C*(j+1)^2) := by
  intro hgap
  obtain ⟨F, τ, hτ, hlim, hF0, hFmono, hFbounds⟩ :=
    exists_prefix_scaling_limit h (ε := 0) 0 (fun N _ => density_nonneg A N)
  let b := fun m => F (m+1)-F m
  let L := 144*(C : ℝ)
  have hb : ∀ i m, 1 ≤ m → m+1 ≤ 8^(i+1) → 1 ≤ (L*4^i)*b m := by
    intro i m hm hmi
    exact scaling_limit_bin_lower_of_nth_gap_bound h hA hgap hτ hlim hm hmi
  have hblock : ∀ i, 1 ≤ L^3 * ∑ p ∈ indexBlock i, b p.1*(b p.2*b (p.1+p.2)) := by
    intro i
    let w := (L*(4 : ℝ)^i)^3
    have hw : ∀ p ∈ indexBlock i, 1 ≤ w*(b p.1*(b p.2*b (p.1+p.2))) := by
      intro p hp
      obtain ⟨hmlo, hmhi, hnlo, hnhi⟩ := mem_indexBlock.mp hp
      have hpow : 1 ≤ 8^i := Nat.one_le_pow i 8 (by decide)
      have hx : 8^(i+1) = 8^i*8 := pow_succ _ _
      have h1 := hb i p.1 (by omega) (by omega)
      have h2 := hb i p.2 (by omega) (by omega)
      have h3 := hb i (p.1+p.2) (by omega) (by omega)
      have h123 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
      dsimp [w]
      nlinarith only [h123]
    have hh := Finset.sum_le_sum hw
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum, card_indexBlock,
      Nat.cast_pow, Nat.cast_ofNat] at hh
    have hpow : ((4 : ℝ)^i)^3 = ((8 : ℝ)^i)^2 := by
      rw [pow_right_comm 4 i 3, pow_right_comm 8 i 2]
      norm_num
    have he : w = L^3*((8 : ℝ)^i)^2 := by dsimp [w]; rw [mul_pow, hpow]
    rw [he] at hh
    apply (mul_le_mul_iff_right₀ (show 0 < ((8 : ℝ)^i)^2 by positivity)).mp
    nlinarith only [hh]
  have hK : ∀ K : ℕ, (K : ℝ) ≤ 15*L^3 := by
    intro K
    let D := (Finset.range K).biUnion indexBlock
    have hdisj : (Finset.range K : Set ℕ).PairwiseDisjoint indexBlock := by
      intro i hi j hj hij
      exact indexBlock_disjoint hij
    have hD : ∀ p ∈ D, 1 ≤ p.1 ∧ p.1 < p.2 := by
      intro p hp
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
      exact indexBlock_ordered hpi
    have hu : ∑ p ∈ D, b p.1*(b p.2*b (p.1+p.2)) ≤ 15 :=
      scaling_limit_box_bound h hA hτ hlim D hD
    have hl := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range K) => hblock i)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, ← Finset.mul_sum] at hl
    have heq : (∑ p ∈ D, b p.1*(b p.2*b (p.1+p.2))) =
        ∑ i ∈ Finset.range K, ∑ p ∈ indexBlock i, b p.1*(b p.2*b (p.1+p.2)) :=
      Finset.sum_biUnion hdisj
    rw [← heq] at hl
    have hh := mul_le_mul_of_nonneg_left hu (show 0 ≤ L^3 by dsimp [L]; positivity)
    nlinarith only [hl, hh]
  obtain ⟨K, hlt⟩ := exists_nat_gt (15*L^3)
  exact (not_lt_of_ge (hK K)) hlt



lemma quadratic_nth_gaps_unbounded {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (C M : ℕ) :
    ∃ j ≥ M, Nat.nth (· ∈ A) j + C*(j+1)^2 < Nat.nth (· ∈ A) (j+1) := by
  by_contra! hbound
  let D := C + (Finset.range M).sup (fun j => Nat.nth (· ∈ A) (j+1))
  apply not_bounded_quadratic_nth_gaps h hA D
  intro j
  have hCD : C ≤ D := by dsimp [D]; omega
  by_cases hj : j < M
  · have hle : Nat.nth (· ∈ A) (j+1) ≤ D := by
      have hh := Finset.le_sup (f := fun j => Nat.nth (· ∈ A) (j+1))
        (Finset.mem_range.mpr hj)
      dsimp only at hh
      dsimp [D]
      omega
    have hsq : 1 ≤ (j+1)^2 := by nlinarith
    have hh := Nat.mul_le_mul_left D hsq
    omega
  · exact (hbound j (by omega)).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hCD) _)


lemma exists_small_gap_after_of_cubic_bound {a : ℕ → ℕ} {C : ℕ}
    (hbound : ∀ n, a n ≤ C*(n+1)^3) (i : ℕ) :
    ∃ j, i+1 ≤ j ∧ j ≤ 2*i+1 ∧ a (j+1)-a j ≤ 27*C*(i+1)^2 := by
  by_contra! hbad
  let t := 27*C*(i+1)^2
  have hstep : ∀ j, i+1 ≤ j → j ≤ 2*i+1 → a j + (t+1) ≤ a (j+1) := by
    intro j hj hj'
    have hh := hbad j hj hj'
    change t < a (j+1)-a j at hh
    omega
  have htel : ∀ k, k ≤ i+1 → a (i+1) + k*(t+1) ≤ a (i+1+k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hh := ih (by omega)
      have hs := hstep (i+1+k) (by omega) (by omega)
      have he : i+1+(k+1) = (i+1+k)+1 := by omega
      rw [he]
      nlinarith
  have hl := htel (i+1) (le_refl _)
  have he : i+1+(i+1) = 2*i+2 := by omega
  rw [he] at hl
  have hu := hbound (2*i+2)
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (show 2*i+2+1 ≤ 3*(i+1) by omega) 3)
  have ht : C*(3*(i+1))^3 = (i+1)*t := by dsimp [t]; ring
  rw [ht] at hp
  nlinarith

/-- With a cubic enumeration bound, a triple-sum set must have arbitrarily
large downward ratios of successive gaps within a factor-two index interval. -/
lemma cubic_nth_gap_ratios_unbounded {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) {C : ℕ}
    (hbound : ∀ n, Nat.nth (· ∈ A) n ≤ C*(n+1)^3) (K M : ℕ) :
    ∃ i ≥ M, ∃ j, i+1 ≤ j ∧ j ≤ 2*i+1 ∧
      K*(Nat.nth (· ∈ A) (j+1)-Nat.nth (· ∈ A) j) <
        Nat.nth (· ∈ A) (i+1)-Nat.nth (· ∈ A) i := by
  obtain ⟨i, hi, hlarge⟩ := quadratic_nth_gaps_unbounded h hA (27*C*(K+1)) M
  obtain ⟨j, hj, hj', hsmall⟩ := exists_small_gap_after_of_cubic_bound hbound i
  refine ⟨i, hi, j, hj, hj', ?_⟩
  have hl : 27*C*(K+1)*(i+1)^2 <
      Nat.nth (· ∈ A) (i+1)-Nat.nth (· ∈ A) i := by omega
  calc
    K*(Nat.nth (· ∈ A) (j+1)-Nat.nth (· ∈ A) j)
        ≤ K*(27*C*(i+1)^2) := Nat.mul_le_mul_left K hsmall
    _ ≤ 27*C*(K+1)*(i+1)^2 := by nlinarith
    _ < _ := hl



lemma failure_yields_cubic_nth_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite)
    (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0) :
    ∃ C : ℕ, 0 < C ∧ ∀ n, Nat.nth (· ∈ A) n ≤ C*(n+1)^3 := by
  obtain ⟨a, C, hC, ha, haA, hbound⟩ := failure_yields_cubic_enumeration h hA hf
  refine ⟨C, hC, fun n => ?_⟩
  apply le_trans (Nat.nth_le_of_strictMonoOn_of_mapsTo (p := (· ∈ A)) a ?_ ?_)
    (hbound n)
  · intro i hi
    change a i ∈ A
    rw [← haA]
    exact Set.mem_range_self i
  · exact ha.strictMonoOn _

lemma failure_yields_unbounded_local_gap_ratios {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite)
    (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0)
    (K M : ℕ) :
    ∃ i ≥ M, ∃ j, i+1 ≤ j ∧ j ≤ 2*i+1 ∧
      K*(Nat.nth (· ∈ A) (j+1)-Nat.nth (· ∈ A) j) <
        Nat.nth (· ∈ A) (i+1)-Nat.nth (· ∈ A) i := by
  obtain ⟨C, hC, hbound⟩ := failure_yields_cubic_nth_bound h hA hf
  exact cubic_nth_gap_ratios_unbounded h hA hbound K M

/-- The density conjecture holds under a bounded local downward gap-ratio
hypothesis. No such regularity assumption is made in the original conjecture. -/
lemma density_liminf_eq_zero_of_bounded_local_gap_ratios {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (hreg : ∃ K M : ℕ, ∀ i ≥ M, ∀ j, i+1 ≤ j → j ≤ 2*i+1 →
      Nat.nth (· ∈ A) (i+1)-Nat.nth (· ∈ A) i ≤
        K*(Nat.nth (· ∈ A) (j+1)-Nat.nth (· ∈ A) j)) :
    Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 := by
  by_contra hf
  obtain ⟨K, M, hreg⟩ := hreg
  obtain ⟨i, hi, j, hj, hj', hlt⟩ := failure_yields_unbounded_local_gap_ratios h hA hf K M
  exact (not_lt_of_ge (hreg i hi j hj hj')) hlt

lemma density_liminf_eq_zero_of_eventually_monotone_gaps {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (hreg : ∃ M : ℕ, MonotoneOn
      (fun i => Nat.nth (· ∈ A) (i+1)-Nat.nth (· ∈ A) i) (Set.Ici M)) :
    Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 := by
  obtain ⟨M, hreg⟩ := hreg
  apply density_liminf_eq_zero_of_bounded_local_gap_ratios h hA
  refine ⟨1, M, fun i hi j hj hj' => ?_⟩
  simpa using hreg hi (show M ≤ j by omega) (show i ≤ j by omega)


lemma power_scaling_limit_eq_zero {A : Set ℕ} (h : NtupleCondition A 3) (hA : A.Infinite)
    {c : ℝ} {τ : ℕ → ℕ} (hτ : StrictMono τ)
    (hlim : ∀ m, Tendsto (fun n => ((initialSegment A (m*(τ n+1))).card : ℝ) /
      ((τ n+1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds (c*(m : ℝ)^(1/3 : ℝ)))) : c = 0 := by
  have hc0 : 0 ≤ c := by
    have ht : Tendsto (fun n => ((initialSegment A (τ n+1)).card : ℝ) /
        ((τ n+1 : ℕ) : ℝ)^(1/3 : ℝ)) atTop (nhds c) := by
      simpa using hlim 1
    exact ge_of_tendsto ht (Eventually.of_forall (fun n => by positivity))
  have hb : ∀ K : ℕ, (K : ℝ) * c^3 ≤ 25920 := by
    intro K
    let D := (Finset.range K).biUnion indexBlock
    have hdisj : (Finset.range K : Set ℕ).PairwiseDisjoint indexBlock := by
      intro i hi j hj hij
      exact indexBlock_disjoint hij
    have hD : ∀ p ∈ D, 1 ≤ p.1 ∧ p.1 < p.2 := by
      intro p hp
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
      exact indexBlock_ordered hpi
    have hupper := scaling_limit_box_bound h hA hτ hlim D hD
    simp_rw [← mul_sub] at hupper
    change ∑ p ∈ D, (c * cubeRootIncrement p.1) *
      ((c * cubeRootIncrement p.2) * (c * cubeRootIncrement (p.1 + p.2))) ≤ 15 at hupper
    have hsum : ∑ p ∈ D, (c * cubeRootIncrement p.1) *
        ((c * cubeRootIncrement p.2) * (c * cubeRootIncrement (p.1 + p.2))) =
        c^3 * ∑ i ∈ Finset.range K, ∑ p ∈ indexBlock i,
          cubeRootIncrement p.1 * (cubeRootIncrement p.2 * cubeRootIncrement (p.1 + p.2)) := by
      rw [Finset.mul_sum]
      change (∑ p ∈ (Finset.range K).biUnion indexBlock, _) = _
      rw [Finset.sum_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [hsum] at hupper
    have hlower : (K : ℝ) / 1728 ≤ ∑ i ∈ Finset.range K, ∑ p ∈ indexBlock i,
        cubeRootIncrement p.1 * (cubeRootIncrement p.2 * cubeRootIncrement (p.1 + p.2)) := by
      simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.range K) => indexBlock_increment_lower i)
    have hmul := mul_le_mul_of_nonneg_left hlower (show 0 ≤ c^3 by positivity)
    nlinarith
  by_contra hne
  have hpos : 0 < c^3 := pow_pos (lt_of_le_of_ne hc0 (Ne.symm hne)) _
  obtain ⟨K, hK⟩ := exists_nat_gt ((25920 : ℝ) / c^3)
  have hk' : 25920 < (K : ℝ) * c^3 := (div_lt_iff₀ hpos).mp hK
  exact (not_lt_of_ge (hb K)) hk'



/-- If the normalized counting function is asymptotically unchanged by each
fixed positive integer dilation, then it converges to zero. This allows the
hypothesis itself to hold without first assuming convergence. -/
lemma density_tendsto_zero_of_dilation_invariance {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (hreg : ∀ m : ℕ, 1 ≤ m → Tendsto
      (fun N => (A ∩ Icc 1 (m*N)).ncard / ((m*N : ℕ) : ℝ)^(1/3 : ℝ) -
        (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) atTop (nhds 0) := by
  let d := fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)
  change Tendsto d atTop (nhds 0)
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) 5)).tendsto_nhds_of_unique_mapClusterPt
  · exact Eventually.of_forall (fun n => ⟨density_nonneg A (n+1), density_le_five h (by omega)⟩)
  intro c hc hcluster
  obtain ⟨τ, hτ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hcluster
  have hbase : Tendsto (fun n => d (τ n+1)) atTop (nhds c) := hlim
  have hτlim : Tendsto (fun n => τ n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hτ.tendsto_atTop
  apply power_scaling_limit_eq_zero h hA hτ
  intro m
  by_cases hm : m = 0
  · subst m
    simpa [initialSegment] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hdiff : Tendsto (fun n => d (m*(τ n+1))-d (τ n+1)) atTop (nhds 0) :=
    (hreg m (Nat.pos_of_ne_zero hm)).comp hτlim
  have ht : Tendsto (fun n => d (m*(τ n+1))) atTop (nhds c) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add hbase
  simpa only [normalized_prefix_eq, d] using ht.mul_const ((m : ℝ)^(1/3 : ℝ))

lemma density_liminf_eq_zero_of_dilation_invariance {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (hreg : ∀ m : ℕ, 1 ≤ m → Tendsto
      (fun N => (A ∩ Icc 1 (m*N)).ncard / ((m*N : ℕ) : ℝ)^(1/3 : ℝ) -
        (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) atTop (nhds 0)) :
    Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 :=
  (density_tendsto_zero_of_dilation_invariance h hA hreg).liminf_eq



/-- Failure of the conjecture forces a persistent macroscopic change under at
least one fixed integer dilation. In particular, slow multiplicative oscillation
cannot be the source of a counterexample. -/
lemma failure_yields_persistent_dilation_oscillation {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ M : ℕ, ∃ N ≥ M,
      ε ≤ |(A ∩ Icc 1 (m*N)).ncard / ((m*N : ℕ) : ℝ)^(1/3 : ℝ) -
        (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)| := by
  by_contra! hbad
  apply hf
  apply density_liminf_eq_zero_of_dilation_invariance h hA
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := hbad m (by omega) ε hε
  refine ⟨M, fun N hN => ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hM N hN


/-- Distinct two-element sums imply that any fixed nonzero difference has at
most two representations. The two possible representations form a three-term
arithmetic progression. -/
lemma nonzero_difference_fiber_card_le_two_of_pair_condition {A : Set ℕ}
    (h : NtupleCondition A 2) {t : ℤ} (ht : t ≠ 0) (R : Finset (ℕ × ℕ))
    (hR : ∀ p ∈ R, p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = t) :
    R.card ≤ 2 := by
  have hchain : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → p.1 = q.2 ∨ q.1 = p.2 := by
    intro p hp q hq hpq
    obtain ⟨hp1, hp2, hpt⟩ := hR p hp
    obtain ⟨hq1, hq2, hqt⟩ := hR q hq
    by_contra! hc
    have heq : ({p.1, q.2} : Finset ℕ) = {q.1, p.2} := by
      apply h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · simp [hc.1]
      · simp [hc.2]
      · simp only [Finset.sum_pair hc.1, Finset.sum_pair hc.2]
        omega
    have hp1mem : p.1 ∈ ({q.1, p.2} : Finset ℕ) := heq ▸ (by simp)
    have hpe : p.1 = q.1 ∨ p.1 = p.2 := by simpa using hp1mem
    have hfst : p.1 = q.1 := by omega
    exact hpq (Prod.ext hfst (by omega))
  by_contra! hcard
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp hcard
  have hpt := (hR p hp).2.2
  have hqt := (hR q hq).2.2
  have hrt := (hR r hr).2.2
  have hpq' : p.1 ≠ q.1 := fun he => hpq (Prod.ext he (by omega))
  have hpr' : p.1 ≠ r.1 := fun he => hpr (Prod.ext he (by omega))
  have hqr' : q.1 ≠ r.1 := fun he => hqr (Prod.ext he (by omega))
  rcases hchain p hp q hq hpq with hpq'' | hpq'' <;>
    rcases hchain p hp r hr hpr with hpr'' | hpr'' <;>
      rcases hchain q hq r hr hqr with hqr'' | hqr'' <;> omega

lemma nonzero_difference_fiber_card_le_two {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite) {t : ℤ} (ht : t ≠ 0)
    (R : Finset (ℕ × ℕ))
    (hR : ∀ p ∈ R, p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = t) :
    R.card ≤ 2 :=
  nonzero_difference_fiber_card_le_two_of_pair_condition (h.pred hA) ht R hR



lemma NtupleCondition.zero (A : Set ℕ) : NtupleCondition A 0 := by
  intro I J ⟨_, _, hI, hJ, _⟩
  rw [Finset.card_eq_zero.mp hI, Finset.card_eq_zero.mp hJ]

lemma NtupleCondition.one (A : Set ℕ) : NtupleCondition A 1 := by
  intro I J ⟨_, _, hI, hJ, hs⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hI
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hJ
  simpa using hs

/-- A sufficiently large new element preserves both adjacent uniqueness conditions. -/
lemma NtupleCondition.insert_large {S : Finset ℕ} {n x : ℕ}
    (h : NtupleCondition (S : Set ℕ) (n+1))
    (hp : NtupleCondition (S : Set ℕ) n)
    (hx : (∑ a ∈ S, a) < x) :
    NtupleCondition (insert x (S : Set ℕ)) (n+1) := by
  intro I J ⟨hI, hJ, hIc, hJc, hs⟩
  have herase : ∀ T : Finset ℕ, (T : Set ℕ) ⊆ insert x (S : Set ℕ) →
      (T.erase x : Set ℕ) ⊆ S := by
    intro T hT a ha
    obtain ⟨hax, haT⟩ := Finset.mem_erase.mp ha
    exact (hT haT).resolve_left hax
  have hnot : ∀ T : Finset ℕ, (T : Set ℕ) ⊆ insert x (S : Set ℕ) →
      x ∉ T → (T : Set ℕ) ⊆ S := by
    intro T hT hxT a ha
    exact (hT ha).resolve_left (fun he => hxT (he ▸ ha))
  by_cases hxI : x ∈ I
  · by_cases hxJ : x ∈ J
    · have he : I.erase x = J.erase x := by
        apply hp
        refine ⟨herase I hI, herase J hJ, ?_, ?_, ?_⟩
        · rw [Finset.card_erase_of_mem hxI, hIc, Nat.add_sub_cancel]
        · rw [Finset.card_erase_of_mem hxJ, hJc, Nat.add_sub_cancel]
        · have hi := Finset.sum_erase_add I (fun a => a) hxI
          have hj := Finset.sum_erase_add J (fun a => a) hxJ
          dsimp only at hi hj
          omega
      calc
        I = insert x (I.erase x) := (Finset.insert_erase hxI).symm
        _ = insert x (J.erase x) := congrArg (insert x) he
        _ = J := Finset.insert_erase hxJ
    · have hlo : x ≤ ∑ a ∈ I, a := Finset.single_le_sum (f := fun a => a) (fun _ _ => Nat.zero_le _) hxI
      have hhi : (∑ a ∈ J, a) ≤ ∑ a ∈ S, a :=
        Finset.sum_le_sum_of_subset_of_nonneg (hnot J hJ hxJ) (fun _ _ _ => Nat.zero_le _)
      omega
  · by_cases hxJ : x ∈ J
    · have hlo : x ≤ ∑ a ∈ J, a := Finset.single_le_sum (f := fun a => a) (fun _ _ => Nat.zero_le _) hxJ
      have hhi : (∑ a ∈ I, a) ≤ ∑ a ∈ S, a :=
        Finset.sum_le_sum_of_subset_of_nonneg (hnot I hI hxI) (fun _ _ _ => Nat.zero_le _)
      omega
    · exact h I J ⟨hnot I hI hxI, hnot J hJ hxJ, hIc, hJc, hs⟩

def largeExtensionChain (S : Finset ℕ) : ℕ → Finset ℕ
  | 0 => S
  | n+1 => insert ((∑ a ∈ largeExtensionChain S n, a) + 1) (largeExtensionChain S n)

lemma largeExtensionChain_fresh (S : Finset ℕ) (n : ℕ) :
    (∑ a ∈ largeExtensionChain S n, a) + 1 ∉ largeExtensionChain S n := by
  intro hm
  have hh := Finset.single_le_sum (s := largeExtensionChain S n) (f := fun a => a)
    (fun _ _ => Nat.zero_le _) hm
  dsimp only at hh
  omega

lemma largeExtensionChain_mono (S : Finset ℕ) : Monotone (largeExtensionChain S) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_insert _ _

lemma largeExtensionChain_card (S : Finset ℕ) (n : ℕ) :
    (largeExtensionChain S n).card = S.card + n := by
  induction n with
  | zero => simp [largeExtensionChain]
  | succ n hn =>
      rw [largeExtensionChain, Finset.card_insert_of_notMem (largeExtensionChain_fresh S n), hn]
      omega

lemma largeExtensionChain_condition (S : Finset ℕ)
    (hS : ∀ k ≤ 3, NtupleCondition (S : Set ℕ) k) (n : ℕ) :
    ∀ k ≤ 3, NtupleCondition (largeExtensionChain S n : Set ℕ) k := by
  induction n with
  | zero => exact hS
  | succ n hn =>
      intro k hk
      cases k with
      | zero => exact NtupleCondition.zero _
      | succ k =>
          simpa only [largeExtensionChain, Finset.coe_insert] using
            NtupleCondition.insert_large (hn (k+1) hk) (hn k (by omega)) (Nat.lt_succ_self _)

/-- Every finite pair-and-triple-unique set extends to an infinite triple-unique set.
This extension deliberately makes no uniform polynomial-growth claim. -/
lemma finite_triple_set_extends_iff (S : Finset ℕ) :
    (∃ A : Set ℕ, (S : Set ℕ) ⊆ A ∧ A.Infinite ∧ NtupleCondition A 3) ↔
    NtupleCondition (S : Set ℕ) 2 ∧ NtupleCondition (S : Set ℕ) 3 := by
  constructor
  · rintro ⟨A, hSA, hA, h3⟩
    exact ⟨(h3.pred hA).mono hSA, h3.mono hSA⟩
  · rintro ⟨h2, h3⟩
    let A : Set ℕ := ⋃ n, (largeExtensionChain S n : Set ℕ)
    have hinc : ∀ n, (largeExtensionChain S n : Set ℕ) ⊆ A := fun n a ha => Set.mem_iUnion.mpr ⟨n, ha⟩
    have hSA : (S : Set ℕ) ⊆ A := hinc 0
    have hA : A.Infinite := by
      intro hfin
      let F := hfin.toFinset
      have hsub : largeExtensionChain S (F.card+1) ⊆ F := by
        intro a ha
        exact hfin.mem_toFinset.mpr (hinc _ ha)
      have hc := Finset.card_le_card hsub
      rw [largeExtensionChain_card] at hc
      omega
    refine ⟨A, hSA, hA, ?_⟩
    have hcover : ∀ T : Finset ℕ, (T : Set ℕ) ⊆ A →
        ∃ n, T ⊆ largeExtensionChain S n := by
      intro T
      induction T using Finset.induction_on with
      | empty => exact fun _ => ⟨0, Finset.empty_subset _⟩
      | @insert a T ha ih =>
          intro hT
          obtain ⟨n, hn⟩ := ih (fun x hx => hT (Finset.mem_insert_of_mem hx))
          obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (hT (Finset.mem_insert_self _ _))
          refine ⟨max n m, Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
          · exact largeExtensionChain_mono S (le_max_right n m) hm
          · exact hn.trans (largeExtensionChain_mono S (le_max_left n m))
    intro I J ⟨hI, hJ, hIc, hJc, hs⟩
    obtain ⟨n, hn⟩ := hcover (I ∪ J) (by
      intro a ha
      rcases Finset.mem_union.mp ha with hi | hj
      · exact hI hi
      · exact hJ hj)
    have hcond := largeExtensionChain_condition S (n := n) (by
      intro k hk
      interval_cases k
      · exact NtupleCondition.zero _
      · exact NtupleCondition.one _
      · exact h2
      · exact h3) 3 (le_refl 3)
    exact hcond I J ⟨fun a ha => hn (Finset.mem_union_left _ ha),
      fun a ha => hn (Finset.mem_union_right _ ha), hIc, hJc, hs⟩

/-- The fresh-element argument only needs a finite set larger than the two tuples. -/
lemma NtupleCondition.pred_of_card {S : Finset ℕ} {n : ℕ}
    (h : NtupleCondition (S : Set ℕ) (n+1)) (hS : 2*n < S.card) :
    NtupleCondition (S : Set ℕ) n := by
  intro I J ⟨hI, hJ, hIc, hJc, hs⟩
  have hcard : (I ∪ J).card < S.card := by
    have hu := Finset.card_union_le I J
    omega
  obtain ⟨a, haS, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have haI : a ∉ I := fun hm => ha (Finset.mem_union_left _ hm)
  have haJ : a ∉ J := fun hm => ha (Finset.mem_union_right _ hm)
  have he : insert a I = insert a J := by
    apply h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haS
      · exact hI hx
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haS
      · exact hJ hx
    · simp [haI, hIc]
    · simp [haJ, hJc]
    · simpa [haI, haJ] using congrArg (a + ·) hs
  simpa [haI, haJ] using congrArg (Finset.erase · a) he

lemma finite_triple_set_extends_of_five_le_card (S : Finset ℕ)
    (hS : 5 ≤ S.card) (h : NtupleCondition (S : Set ℕ) 3) :
    ∃ A : Set ℕ, (S : Set ℕ) ⊆ A ∧ A.Infinite ∧ NtupleCondition A 3 :=
  (finite_triple_set_extends_iff S).mpr ⟨h.pred_of_card (by omega), h⟩

/-- This elementary extension has exponential, not cubic, growth. -/
lemma largeExtensionChain_sum (S : Finset ℕ) (n : ℕ) :
    (∑ a ∈ largeExtensionChain S n, a) + 1 = 2^n * ((∑ a ∈ S, a) + 1) := by
  induction n with
  | zero => simp [largeExtensionChain]
  | succ n hn =>
      rw [largeExtensionChain, Finset.sum_insert (largeExtensionChain_fresh S n)]
      rw [pow_succ]
      nlinarith



lemma triple_set_eq_of_power_sums {K : Type*} [Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (a b c d e f : K)
    (hfirst : a+b+c = d+e+f)
    (hsecond : a^2+b^2+c^2 = d^2+e^2+f^2)
    (hthird : a^3+b^3+c^3 = d^3+e^3+f^3) :
    ({a,b,c} : Finset K) = {d,e,f} := by
  classical
  have hpair : a*b+a*c+b*c = d*e+d*f+e*f := by
    apply mul_left_cancel₀ h2
    linear_combination (a+b+c+d+e+f)*hfirst - hsecond
  have hprod : a*b*c = d*e*f := by
    apply mul_left_cancel₀ h3
    have hn (x y z : K) : x^3+y^3+z^3 =
        (x+y+z)^3 - 3*(x+y+z)*(x*y+x*z+y*z)+3*(x*y*z) := by ring
    rw [hn a b c, hn d e f, hfirst, hpair] at hthird
    linear_combination hthird
  have hroot : ∀ x : K, (x-a)*(x-b)*(x-c) = (x-d)*(x-e)*(x-f) := by
    intro x
    calc
      (x-a)*(x-b)*(x-c) = x^3-(a+b+c)*x^2+(a*b+a*c+b*c)*x-a*b*c := by ring
      _ = x^3-(d+e+f)*x^2+(d*e+d*f+e*f)*x-d*e*f := by rw [hfirst,hpair,hprod]
      _ = (x-d)*(x-e)*(x-f) := by ring
  ext x
  simpa only [Finset.mem_insert, Finset.mem_singleton, mul_eq_zero, sub_eq_zero, or_assoc] using
    Iff.of_eq (congrArg (· = 0) (hroot x))


lemma base_three_digits_eq {B u₀ u₁ u₂ v₀ v₁ v₂ : ℕ}
    (hB : 0 < B) (hu₀ : u₀ < B) (hu₁ : u₁ < B)
    (hv₀ : v₀ < B) (hv₁ : v₁ < B)
    (he : u₀+B*(u₁+B*u₂) = v₀+B*(v₁+B*v₂)) :
    u₀ = v₀ ∧ u₁ = v₁ ∧ u₂ = v₂ := by
  have h₀ : u₀ = v₀ := by
    have hh := congrArg (· % B) he
    simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu₀,
      Nat.mod_eq_of_lt hv₀] using hh
  have hm : u₁+B*u₂ = v₁+B*v₂ := by
    apply Nat.eq_of_mul_eq_mul_left hB
    omega
  have h₁ : u₁ = v₁ := by
    have hh := congrArg (· % B) hm
    simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu₁,
      Nat.mod_eq_of_lt hv₁] using hh
  have h₂ : u₂ = v₂ := by
    apply Nat.eq_of_mul_eq_mul_left hB
    omega
  exact ⟨h₀,h₁,h₂⟩

def momentCode (q : ℕ) (x : ZMod q) : ℕ :=
  (x^3).val + (3*q)*((x^2).val+(3*q)*x.val)

lemma momentCode_injective (q : ℕ) [NeZero q] : Function.Injective (momentCode q) := by
  have hq : 0 < q := NeZero.pos q
  intro x y he
  have hb (z : ZMod q) : z.val < 3*q := (ZMod.val_lt z).trans_le (by omega)
  have hh := base_three_digits_eq (by omega : 0 < 3*q)
    (hb (x^3)) (hb (x^2)) (hb (y^3)) (hb (y^2)) he
  exact ZMod.val_injective q hh.2.2

lemma sum_zmod_val_lt_three_mul {q : ℕ} [NeZero q]
    (S : Finset (ZMod q)) (hS : S.card = 3) (f : ZMod q → ZMod q) :
    (∑ x ∈ S, (f x).val) < 3*q := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hh := Finset.sum_lt_sum_of_nonempty hne (fun x (_ : x ∈ S) => ZMod.val_lt (f x))
  simpa only [Finset.sum_const, smul_eq_mul, hS] using hh

lemma momentCode_triple_sum_injective (q : ℕ) [Fact q.Prime] (hq : 3 < q)
    (I J : Finset (ZMod q)) (hI : I.card = 3) (hJ : J.card = 3)
    (hs : (∑ x ∈ I, momentCode q x) = ∑ x ∈ J, momentCode q x) : I = J := by
  have hd := base_three_digits_eq (by omega : 0 < 3*q)
    (sum_zmod_val_lt_three_mul I hI (·^3))
    (sum_zmod_val_lt_three_mul I hI (·^2))
    (sum_zmod_val_lt_three_mul J hJ (·^3))
    (sum_zmod_val_lt_three_mul J hJ (·^2))
    (by simpa only [momentCode, Finset.sum_add_distrib, ← Finset.mul_sum] using hs)
  have hfirst : (∑ x ∈ I, x) = ∑ x ∈ J, x := by
    have hh := congrArg (fun n : ℕ => (n : ZMod q)) hd.2.2
    simpa only [Nat.cast_sum, ZMod.natCast_zmod_val] using hh
  have hsecond : (∑ x ∈ I, x^2) = ∑ x ∈ J, x^2 := by
    have hh := congrArg (fun n : ℕ => (n : ZMod q)) hd.2.1
    simpa only [Nat.cast_sum, ZMod.natCast_zmod_val] using hh
  have hthird : (∑ x ∈ I, x^3) = ∑ x ∈ J, x^3 := by
    have hh := congrArg (fun n : ℕ => (n : ZMod q)) hd.1
    simpa only [Nat.cast_sum, ZMod.natCast_zmod_val] using hh
  have hn (n : ℕ) (hn : 0 < n) (hnq : n < q) : (n : ZMod q) ≠ 0 := by
    intro he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt hnq, ZMod.val_zero] at hv
    omega
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hI
  obtain ⟨d,e,f,hde,hdf,hef,rfl⟩ := Finset.card_eq_three.mp hJ
  apply triple_set_eq_of_power_sums (hn 2 (by omega) (by omega))
    (hn 3 (by omega) hq)
  · simpa [hab,hac,hbc,hde,hdf,hef,add_assoc] using hfirst
  · simpa [hab,hac,hbc,hde,hdf,hef,add_assoc] using hsecond
  · simpa [hab,hac,hbc,hde,hdf,hef,add_assoc] using hthird

noncomputable def momentBlock (q : ℕ) [NeZero q] : Finset ℕ :=
  Finset.univ.image (momentCode q)

lemma momentBlock_card (q : ℕ) [NeZero q] : (momentBlock q).card = q := by
  simp only [momentBlock, Finset.card_image_of_injective _ (momentCode_injective q),
    Finset.card_univ, ZMod.card]

lemma momentBlock_condition (q : ℕ) [Fact q.Prime] (hq : 3 < q) :
    NtupleCondition (momentBlock q : Set ℕ) 3 := by
  intro I J ⟨hI,hJ,hIc,hJc,hs⟩
  obtain ⟨U,hU⟩ := Finset.subset_univ_image_iff.mp hI
  obtain ⟨V,hV⟩ := Finset.subset_univ_image_iff.mp hJ
  subst I J
  have hu : U.card = 3 := by
    simpa only [Finset.card_image_of_injective _ (momentCode_injective q)] using hIc
  have hv : V.card = 3 := by
    simpa only [Finset.card_image_of_injective _ (momentCode_injective q)] using hJc
  have hi : ∀ a ∈ U, ∀ b ∈ U, momentCode q a = momentCode q b → a = b :=
    fun _ _ _ _ hh => momentCode_injective q hh
  have hj : ∀ a ∈ V, ∀ b ∈ V, momentCode q a = momentCode q b → a = b :=
    fun _ _ _ _ hh => momentCode_injective q hh
  rw [Finset.sum_image hi, Finset.sum_image hj] at hs
  exact congrArg (Finset.image (momentCode q)) (momentCode_triple_sum_injective q hq U V hu hv hs)

lemma momentCode_lt (q : ℕ) [NeZero q] (x : ZMod q) : momentCode q x < (3*q)^3 := by
  have hq : 0 < q := NeZero.pos q
  let B := 3*q
  have hB : 0 < B := by dsimp [B]; omega
  have hx (z : ZMod q) : z.val + 1 ≤ B := by
    have hh := ZMod.val_lt z
    dsimp [B]
    omega
  have hm : (x^2).val+B*x.val < B^2 := by
    have hp := Nat.mul_le_mul_left B (hx x)
    nlinarith [hx (x^2)]
  have hp := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hm)
  change (x^3).val+B*((x^2).val+B*x.val) < B^3
  nlinarith [hx (x^3)]

lemma momentBlock_bound (q : ℕ) [NeZero q] (x : ℕ) (hx : x ∈ momentBlock q) :
    x < (3*q)^3 := by
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  exact momentCode_lt q y


lemma pair_eq_of_power_sums {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (a b c d : K)
    (hfirst : a+b = c+d) (hsecond : a^2+b^2 = c^2+d^2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hprod : a*b = c*d := by
    apply mul_left_cancel₀ h2
    linear_combination (a+b+c+d)*hfirst - hsecond
  have hz : (a-c)*(a-d) = 0 := by
    calc
      (a-c)*(a-d) = a^2-(c+d)*a+c*d := by ring
      _ = a^2-(a+b)*a+a*b := by rw [← hfirst, ← hprod]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hz with hc | hd
  · have hac := sub_eq_zero.mp hc
    exact Or.inl ⟨hac, by linear_combination hfirst - hac⟩
  · have had := sub_eq_zero.mp hd
    exact Or.inr ⟨had, by linear_combination hfirst - had⟩

/-- A gap smaller than `q` determines the two leading digits when the lower digits
are sums of two residues and the base is `3*q`. -/
lemma base_three_digits_close {q u₀ u₁ u₂ v₀ v₁ v₂ : ℕ}
    (_hq : 0 < q) (hu₀ : u₀ < 2*q) (hu₁ : u₁ < 2*q)
    (hv₀ : v₀ < 2*q) (hv₁ : v₁ < 2*q)
    (huv : u₀+(3*q)*(u₁+(3*q)*u₂) < v₀+(3*q)*(v₁+(3*q)*v₂)+q)
    (hvu : v₀+(3*q)*(v₁+(3*q)*v₂) < u₀+(3*q)*(u₁+(3*q)*u₂)+q) :
    u₂ = v₂ ∧ u₁ = v₁ := by
  have hsmall (a b : ℕ) (ha : a < 2*q) (hb : b < 2*q) :
      a+(3*q)*b+q < (3*q)^2 := by
    have hh := Nat.mul_le_mul_left (3*q) (Nat.succ_le_of_lt hb)
    nlinarith
  have hu := hsmall u₀ u₁ hu₀ hu₁
  have hv := hsmall v₀ v₁ hv₀ hv₁
  have hhigh : u₂ = v₂ := by
    rcases lt_trichotomy u₂ v₂ with hlt | he | hgt
    · have hm := Nat.mul_le_mul_left ((3*q)^2) (Nat.succ_le_of_lt hlt)
      nlinarith
    · exact he
    · have hm := Nat.mul_le_mul_left ((3*q)^2) (Nat.succ_le_of_lt hgt)
      nlinarith
  refine ⟨hhigh, ?_⟩
  rw [hhigh] at huv hvu
  rcases lt_trichotomy u₁ v₁ with hlt | he | hgt
  · have hm := Nat.mul_le_mul_left (3*q) (Nat.succ_le_of_lt hlt)
    nlinarith
  · exact he
  · have hm := Nat.mul_le_mul_left (3*q) (Nat.succ_le_of_lt hgt)
    nlinarith

lemma momentCode_pair_close (q : ℕ) [Fact q.Prime] (hq : 3 < q)
    (a b c d : ZMod q)
    (hab : momentCode q a + momentCode q b < momentCode q c + momentCode q d + q)
    (hcd : momentCode q c + momentCode q d < momentCode q a + momentCode q b + q) :
    momentCode q a + momentCode q b = momentCode q c + momentCode q d := by
  have hb (x y : ZMod q) : x.val+y.val < 2*q := by
    have hx := ZMod.val_lt x
    have hy := ZMod.val_lt y
    omega
  have hh := base_three_digits_close (by omega : 0 < q)
    (hb (a^3) (b^3)) (hb (a^2) (b^2)) (hb (c^3) (d^3)) (hb (c^2) (d^2))
    (show (a^3).val+(b^3).val+(3*q)*((a^2).val+(b^2).val+(3*q)*(a.val+b.val)) <
      (c^3).val+(d^3).val+(3*q)*((c^2).val+(d^2).val+(3*q)*(c.val+d.val))+q by
      simpa only [momentCode, mul_add, add_assoc, add_left_comm, add_comm] using hab)
    (show (c^3).val+(d^3).val+(3*q)*((c^2).val+(d^2).val+(3*q)*(c.val+d.val)) <
      (a^3).val+(b^3).val+(3*q)*((a^2).val+(b^2).val+(3*q)*(a.val+b.val))+q by
      simpa only [momentCode, mul_add, add_assoc, add_left_comm, add_comm] using hcd)
  have hfirst : a+b = c+d := by
    have hx := congrArg (fun n : ℕ => (n : ZMod q)) hh.1
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hx
  have hsecond : a^2+b^2 = c^2+d^2 := by
    have hx := congrArg (fun n : ℕ => (n : ZMod q)) hh.2
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hx
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro he
    have hx := congrArg ZMod.val he
    have hv := ZMod.val_natCast_of_lt (n := q) (a := 2) (by omega)
    change (2 : ZMod q).val = 2 at hv
    rw [hv, ZMod.val_zero] at hx
    omega
  rcases pair_eq_of_power_sums htwo a b c d hfirst hsecond with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact add_comm _ _


lemma momentCode_zero (q : ℕ) : momentCode q 0 = 0 := by
  simp [momentCode]

lemma momentCode_lower_of_ne_zero (q : ℕ) [NeZero q] {x : ZMod q} (hx : x ≠ 0) :
    (3*q)^2 ≤ momentCode q x := by
  have hv : 1 ≤ x.val := Nat.one_le_iff_ne_zero.mpr (fun he => hx ((ZMod.val_eq_zero x).mp he))
  have hh := Nat.mul_le_mul_left ((3*q)^2) hv
  dsimp [momentCode]
  nlinarith

lemma momentBlock_initial_gap (q : ℕ) [NeZero q] {x : ℕ} (hx : x ∈ momentBlock q) :
    x = 0 ∨ (3*q)^2 ≤ x := by
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  by_cases hy : y = 0
  · exact Or.inl (hy ▸ momentCode_zero q)
  · exact Or.inr (momentCode_lower_of_ne_zero q hy)

/-- Dense finite examples exist at arbitrarily large cardinalities. This does not
supply a single fixed bound on every prefix of an increasing enumeration. -/
lemma exists_arbitrarily_large_finite_triple_sets (m : ℕ) :
    ∃ S : Finset ℕ, m ≤ S.card ∧ NtupleCondition (S : Set ℕ) 3 ∧
      ∀ x ∈ S, x < 27*S.card^3 := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (max m 5)
  letI : Fact q.Prime := ⟨hp⟩
  refine ⟨momentBlock q, ?_, momentBlock_condition q (by omega), ?_⟩
  · rw [momentBlock_card]
    omega
  · intro x hx
    rw [momentBlock_card]
    simpa [mul_pow] using momentBlock_bound q x hx

/-- At any fixed cutoff the finite-field blocks eventually retain only zero.
Thus their large total cardinality alone cannot be passed through compactness. -/
lemma momentBlock_small_elements (M q : ℕ) [NeZero q] (hq : M < q)
    {x : ℕ} (hx : x ∈ momentBlock q) (hxm : x ≤ M) : x = 0 := by
  rcases momentBlock_initial_gap q hx with hz | hh
  · exact hz
  · have hqp : 0 < q := NeZero.pos q
    nlinarith


lemma momentBlock_small_sum (q : ℕ) [NeZero q] (I : Finset ℕ)
    (hI : I ⊆ momentBlock q) (hc : I.card ≤ 2) :
    ∃ a b : ZMod q, (∑ x ∈ I, x) = momentCode q a + momentCode q b := by
  rcases Nat.le_total I.card 1 with hc1 | hc1
  · rcases Nat.eq_zero_or_pos I.card with hz | hp
    · rw [Finset.card_eq_zero.mp hz]
      exact ⟨0, 0, by simp [momentCode_zero]⟩
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (by omega : I.card = 1)
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hI (by simp : x ∈ {x}))
      exact ⟨a, 0, by simp [ha, momentCode_zero]⟩
  · by_cases hc2 : I.card = 2
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc2
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hI (by simp : x ∈ {x,y}))
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (hI (by simp : y ∈ {x,y}))
      exact ⟨a, b, by simp [hxy, ha, hb]⟩
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (by omega : I.card = 1)
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hI (by simp : x ∈ {x}))
      exact ⟨a, 0, by simp [ha, momentCode_zero]⟩

lemma momentBlock_small_sum_close (q : ℕ) [Fact q.Prime] (hq : 3 < q)
    (I J : Finset ℕ) (hI : I ⊆ momentBlock q) (hJ : J ⊆ momentBlock q)
    (hIc : I.card ≤ 2) (hJc : J.card ≤ 2)
    (hij : (∑ x ∈ I, x) < (∑ x ∈ J, x) + q)
    (hji : (∑ x ∈ J, x) < (∑ x ∈ I, x) + q) :
    (∑ x ∈ I, x) = ∑ x ∈ J, x := by
  obtain ⟨a,b,ha⟩ := momentBlock_small_sum q I hI hIc
  obtain ⟨c,d,hb⟩ := momentBlock_small_sum q J hJ hJc
  rw [ha, hb] at hij hji ⊢
  exact momentCode_pair_close q hq a b c d hij hji

lemma translated_union_decompose (S T I : Finset ℕ) (L : ℕ)
    (hi : I ⊆ S ∪ T.image (L + ·)) :
    ∃ U V : Finset ℕ, U ⊆ S ∧ V ⊆ T ∧
      I = U ∪ V.image (L + ·) ∧ Disjoint U (V.image (L + ·)) ∧
      I.card = U.card + V.card ∧
      (∑ x ∈ I, x) = (∑ x ∈ U, x) + L*V.card + ∑ x ∈ V, x := by
  let U := I ∩ S
  obtain ⟨V,hVT,hV⟩ := Finset.subset_image_iff.mp (show I \ S ⊆ T.image (L+·) from by
    intro x hx
    exact (Finset.mem_union.mp (hi (Finset.mem_sdiff.mp hx).1)).resolve_left
      (Finset.mem_sdiff.mp hx).2)
  have he : I = U ∪ V.image (L+·) := by
    rw [hV]
    ext x
    simp only [U, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hd : Disjoint U (V.image (L+·)) := by
    rw [hV]
    exact Finset.disjoint_left.mpr (by
      intro x hx hy
      exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hx).2)
  have hlin : Function.Injective (L + · : ℕ → ℕ) := fun _ _ hh => Nat.add_left_cancel hh
  refine ⟨U,V,Finset.inter_subset_right,hVT,he,hd,?_,?_⟩
  · rw [he, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hlin]
  · rw [he, Finset.sum_union hd, Finset.sum_image (fun _ _ _ _ hh => hlin hh)]
    rw [Finset.sum_add_distrib, Finset.sum_const]
    simp only [smul_eq_mul]
    ring

lemma translated_union_condition (S T : Finset ℕ) (M B L q : ℕ)
    (hS : ∀ n ≤ 3, NtupleCondition (S : Set ℕ) n)
    (hT : ∀ n ≤ 3, NtupleCondition (T : Set ℕ) n)
    (hSM : ∀ x ∈ S, x ≤ M) (hTB : ∀ x ∈ T, x ≤ B)
    (hL : 3*M+3*B < L) (hq : 2*M < q)
    (hclose : ∀ I J : Finset ℕ, I ⊆ T → J ⊆ T →
      I.card ≤ 2 → J.card ≤ 2 →
      (∑ x ∈ I, x) < (∑ x ∈ J, x)+q →
      (∑ x ∈ J, x) < (∑ x ∈ I, x)+q →
      (∑ x ∈ I, x) = ∑ x ∈ J, x) :
    ∀ n ≤ 3, NtupleCondition ((S ∪ T.image (L+·)) : Set ℕ) n := by
  intro n hn I J ⟨hi,hj,hic,hjc,hs⟩
  obtain ⟨U,V,hUS,hVT,hiuv,_,hic',his⟩ := translated_union_decompose S T I L (by intro x hx; exact Finset.mem_union.mpr (hi hx))
  obtain ⟨W,X,hWS,hXT,hjwx,_,hjc',hjs⟩ := translated_union_decompose S T J L (by intro x hx; exact Finset.mem_union.mpr (hj hx))
  have huc : U.card ≤ 3 := by omega
  have hvc : V.card ≤ 3 := by omega
  have hwc : W.card ≤ 3 := by omega
  have hxc : X.card ≤ 3 := by omega
  have hsum_bound (Y Z : Finset ℕ) (hYZ : Y ⊆ Z) (D : ℕ)
      (hZD : ∀ x ∈ Z, x ≤ D) : (∑ x ∈ Y, x) ≤ Y.card*D := by
    calc
      (∑ x ∈ Y, x) ≤ ∑ _ ∈ Y, D := Finset.sum_le_sum (fun x hx => hZD x (hYZ hx))
      _ = Y.card*D := by simp
  have hu := hsum_bound U S hUS M hSM
  have hv := hsum_bound V T hVT B hTB
  have hw := hsum_bound W S hWS M hSM
  have hx := hsum_bound X T hXT B hTB
  have he : V.card = X.card := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hvx | hxv
    · have hh := Nat.mul_le_mul_left L (Nat.succ_le_of_lt hvx)
      have hu' := (Nat.mul_le_mul_right M huc)
      have hv' := (Nat.mul_le_mul_right B hvc)
      rw [Nat.mul_succ] at hh
      omega
    · have hh := Nat.mul_le_mul_left L (Nat.succ_le_of_lt hxv)
      have hw' := (Nat.mul_le_mul_right M hwc)
      have hx' := (Nat.mul_le_mul_right B hxc)
      rw [Nat.mul_succ] at hh
      omega
  have he' : U.card = W.card := by omega
  have hs' : (∑ x ∈ U, x) + (∑ x ∈ V, x) =
      (∑ x ∈ W, x) + (∑ x ∈ X, x) := by rw [he] at his; omega
  have hVX : V = X := by
    apply hT V.card hvc V X
    refine ⟨hVT,hXT,rfl,he.symm,?_⟩
    by_cases hc3 : V.card = 3
    · have huz : U = ∅ := Finset.card_eq_zero.mp (by omega)
      have hwz : W = ∅ := Finset.card_eq_zero.mp (by omega)
      simpa [huz,hwz] using hs'
    · by_cases hvz : V.card = 0
      · have hv0 : V = ∅ := Finset.card_eq_zero.mp hvz
        have hx0 : X = ∅ := Finset.card_eq_zero.mp (by omega)
        simp [hv0,hx0]
      · have hu2 : U.card ≤ 2 := by omega
        have hw2 : W.card ≤ 2 := by omega
        have hu' := (Nat.mul_le_mul_right M hu2)
        have hw' := (Nat.mul_le_mul_right M hw2)
        exact hclose V X hVT hXT (by omega) (by omega) (by omega) (by omega)
  have hUW : U = W := hS U.card huc U W ⟨hUS,hWS,rfl,he'.symm,by rw [hVX] at hs'; omega⟩
  rw [hiuv,hjwx,hVX,hUW]

lemma momentBlock_conditions (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) :
    ∀ n ≤ 3, NtupleCondition (momentBlock q : Set ℕ) n := by
  intro n hn
  interval_cases n
  · exact NtupleCondition.zero _
  · exact NtupleCondition.one _
  · exact (momentBlock_condition q (by omega)).pred_of_card (by rw [momentBlock_card]; omega)
  · exact momentBlock_condition q (by omega)

abbrev GoodTripleFinset := {S : Finset ℕ //
  (∀ n ≤ 3, NtupleCondition (S : Set ℕ) n) ∧ ∀ x ∈ S, 0 < x}

lemma exists_dense_extension (S : GoodTripleFinset) (M : ℕ) :
    ∃ U : GoodTripleFinset, ∃ q : ℕ, M < q ∧ S.val ⊆ U.val ∧
      q ≤ U.val.card ∧ ∀ x ∈ U.val, x ≤ (6*q)^3 := by
  let D := ∑ x ∈ S.val, x
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (max (2*D+M+1) 5)
  letI : Fact q.Prime := ⟨hprime⟩
  have hq5 : 5 ≤ q := by omega
  have hqD : 2*D < q := by omega
  have hD : ∀ x ∈ S.val, x ≤ D := fun x hx =>
    Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hx
  let B := (3*q)^3
  let L := 4*B
  have hBq : 3*q ≤ B := Nat.le_pow (by omega : 0 < 3)
  have hBpos : 0 < B := lt_of_lt_of_le (by omega) hBq
  have hLB : 3*D+3*B < L := by dsimp [L]; omega
  let U := S.val ∪ (momentBlock q).image (L+·)
  have hgood : ∀ n ≤ 3, NtupleCondition (U : Set ℕ) n := by
    simpa only [U, Finset.coe_union] using translated_union_condition
      S.val (momentBlock q) D B L q S.property.1 (momentBlock_conditions q hq5)
      hD (fun x hx => Nat.le_of_lt (momentBlock_bound q x hx)) hLB hqD
      (momentBlock_small_sum_close q (by omega))
  have hpos : ∀ x ∈ U, 0 < x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hs | ht
    · exact S.property.2 x hs
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
      dsimp [L]
      omega
  refine ⟨⟨U,hgood,hpos⟩,q,by omega,Finset.subset_union_left,?_,?_⟩
  · calc
      q = ((momentBlock q).image (L+·)).card := by
        rw [Finset.card_image_of_injective _ (fun _ _ hh => Nat.add_left_cancel hh), momentBlock_card]
      _ ≤ U.card := Finset.card_le_card Finset.subset_union_right
  · intro x hx
    have hN : (6*q)^3 = 8*B := by dsimp [B]; ring
    rw [hN]
    rcases Finset.mem_union.mp hx with hs | ht
    · have hh := hD x hs
      omega
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
      have hh := momentBlock_bound q y hy
      change y < B at hh
      dsimp [L]
      omega

lemma exists_dense_extension_pair (S : GoodTripleFinset) (M : ℕ) :
    ∃ p : GoodTripleFinset × ℕ, M < p.2 ∧ S.val ⊆ p.1.val ∧
      p.2 ≤ p.1.val.card ∧ ∀ x ∈ p.1.val, x ≤ (6*p.2)^3 := by
  obtain ⟨U,q,hq,hs,hc,hb⟩ := exists_dense_extension S M
  exact ⟨(U,q),hq,hs,hc,hb⟩

noncomputable def denseSuccessor (S : GoodTripleFinset) (M : ℕ) : GoodTripleFinset × ℕ :=
  Classical.choose (exists_dense_extension_pair S M)

lemma denseSuccessor_spec (S : GoodTripleFinset) (M : ℕ) :
    M < (denseSuccessor S M).2 ∧ S.val ⊆ (denseSuccessor S M).1.val ∧
      (denseSuccessor S M).2 ≤ (denseSuccessor S M).1.val.card ∧
      ∀ x ∈ (denseSuccessor S M).1.val, x ≤ (6*(denseSuccessor S M).2)^3 :=
  Classical.choose_spec (exists_dense_extension_pair S M)

def emptyGoodTripleFinset : GoodTripleFinset := ⟨∅, by
  constructor
  · intro n _ I J ⟨hi,hj,_,_,_⟩
    have hi' : I = ∅ := Finset.subset_empty.mp hi
    have hj' : J = ∅ := Finset.subset_empty.mp hj
    rw [hi',hj']
  · simp⟩

noncomputable def denseChain : ℕ → GoodTripleFinset × ℕ
  | 0 => (emptyGoodTripleFinset, 0)
  | n+1 => denseSuccessor (denseChain n).1 n

lemma denseChain_mono : Monotone (fun n => (denseChain n).1.val) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (denseSuccessor_spec (denseChain n).1 n).2.1

lemma denseChain_spec (n : ℕ) :
    n < (denseChain (n+1)).2 ∧
      (denseChain (n+1)).2 ≤ (denseChain (n+1)).1.val.card ∧
      ∀ x ∈ (denseChain (n+1)).1.val, x ≤ (6*(denseChain (n+1)).2)^3 :=
  ⟨(denseSuccessor_spec (denseChain n).1 n).1,
    (denseSuccessor_spec (denseChain n).1 n).2.2⟩

noncomputable def denseUnion : Set ℕ := ⋃ n, ((denseChain n).1.val : Set ℕ)

lemma denseChain_subset (n : ℕ) : ((denseChain n).1.val : Set ℕ) ⊆ denseUnion :=
  fun _ hx => Set.mem_iUnion.mpr ⟨n,hx⟩

lemma denseUnion_infinite : denseUnion.Infinite := by
  intro hf
  have hs : (denseChain (hf.toFinset.card+1)).1.val ⊆ hf.toFinset := by
    intro x hx
    exact hf.mem_toFinset.mpr (denseChain_subset _ hx)
  have hc := Finset.card_le_card hs
  have hbound := denseChain_spec hf.toFinset.card
  omega

lemma denseUnion_condition : NtupleCondition denseUnion 3 := by
  have hcover : ∀ T : Finset ℕ, (T : Set ℕ) ⊆ denseUnion →
      ∃ n, T ⊆ (denseChain n).1.val := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨0,Finset.empty_subset _⟩
    | @insert a T ha ih =>
        intro hT
        obtain ⟨n,hn⟩ := ih (fun x hx => hT (Finset.mem_insert_of_mem hx))
        obtain ⟨m,hm⟩ := Set.mem_iUnion.mp (hT (Finset.mem_insert_self _ _))
        refine ⟨max n m,Finset.insert_subset_iff.mpr ⟨?_,?_⟩⟩
        · exact denseChain_mono (le_max_right n m) hm
        · exact hn.trans (denseChain_mono (le_max_left n m))
  intro I J ⟨hi,hj,hic,hjc,hs⟩
  obtain ⟨n,hn⟩ := hcover (I ∪ J) (by
    intro x hx
    exact (Finset.mem_union.mp hx).elim (fun hh => hi hh) (fun hh => hj hh))
  exact (denseChain n).1.property.1 3 (le_refl 3) I J
    ⟨fun x hx => hn (Finset.mem_union_left _ hx),
      fun x hx => hn (Finset.mem_union_right _ hx),hic,hjc,hs⟩

lemma denseUnion_density_large (n : ℕ) :
    (1/6 : ℝ) ≤ (denseUnion ∩ Icc 1 ((6*(denseChain (n+1)).2)^3)).ncard /
      (((6*(denseChain (n+1)).2)^3 : ℕ) : ℝ)^(1/3 : ℝ) := by
  let q := (denseChain (n+1)).2
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (denseChain_spec n).1
  have hcard : q ≤ (denseUnion ∩ Icc 1 ((6*q)^3)).ncard := by
    calc
      q ≤ (denseChain (n+1)).1.val.card := (denseChain_spec n).2.1
      _ ≤ (initialSegment denseUnion ((6*q)^3)).card := Finset.card_le_card (by
        intro x hx
        exact mem_initialSegment.mpr ⟨denseChain_subset _ hx,
          (denseChain (n+1)).1.property.2 x hx, (denseChain_spec n).2.2 x hx⟩)
      _ = _ := card_initialSegment _ _
  have hp : (((6*q)^3 : ℕ) : ℝ)^(1/3 : ℝ) = 6*(q : ℝ) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  change (1/6 : ℝ) ≤ (denseUnion ∩ Icc 1 ((6*q)^3)).ncard / _
  rw [hp]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 6*(q : ℝ))).mpr
  have hh : (q : ℝ) ≤ (denseUnion ∩ Icc 1 ((6*q)^3)).ncard := by exact_mod_cast hcard
  linarith

lemma denseUnion_density_frequently_large (M : ℕ) :
    ∃ N ≥ M, (1/6 : ℝ) ≤
      (denseUnion ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ) := by
  refine ⟨(6*(denseChain (M+1)).2)^3,?_,denseUnion_density_large M⟩
  have hq := (denseChain_spec M).1
  have hp : 6*(denseChain (M+1)).2 ≤ (6*(denseChain (M+1)).2)^3 :=
    Nat.le_pow (by omega)
  omega

lemma denseUnion_density_not_tendsto_zero : ¬ Tendsto
    (fun N => (denseUnion ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) atTop (nhds 0) := by
  intro h
  obtain ⟨M,hM⟩ := Metric.tendsto_atTop.mp h (1/6) (by norm_num)
  obtain ⟨N,hNM,hN⟩ := denseUnion_density_frequently_large M
  have hh := hM N hNM
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (density_nonneg denseUnion N)] at hh
  linarith

/-- Triple uniqueness does not imply that the normalized counting function converges.
This says nothing against the conjecture, whose conclusion only concerns the liminf. -/
lemma exists_triple_unique_set_with_nonconvergent_density :
    ∃ A : Set ℕ, A.Infinite ∧ NtupleCondition A 3 ∧
      ∀ c : ℝ, ¬ Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ))
        atTop (nhds c) := by
  refine ⟨denseUnion,denseUnion_infinite,denseUnion_condition,?_⟩
  intro c hc
  have hz := density_limit_eq_zero denseUnion_condition denseUnion_infinite hc
  subst c
  exact denseUnion_density_not_tendsto_zero hc


lemma positive_finset_sum_lower_bound (S : Finset ℕ) (hS : ∀ x ∈ S, 0 < x) :
    S.card*(S.card+1) ≤ 2*(∑ x ∈ S, x) := by
  induction S using Finset.induction_on_max with
  | h0 => simp
  | step a S hmax ih =>
      have ha : 0 < a := hS a (Finset.mem_insert_self _ _)
      have hpos : ∀ x ∈ S, 0 < x := fun x hx => hS x (Finset.mem_insert_of_mem hx)
      have hnot : a ∉ S := fun hh => Nat.lt_irrefl a (hmax a hh)
      have hs : S ⊆ Finset.Ico 1 a := by
        intro x hx
        exact Finset.mem_Ico.mpr ⟨hpos x hx, hmax x hx⟩
      have hc := Finset.card_le_card hs
      rw [Nat.card_Ico] at hc
      have ih' := ih hpos
      rw [Finset.card_insert_of_notMem hnot, Finset.sum_insert hnot]
      have hh : S.card+1 ≤ a := by omega
      nlinarith

noncomputable def translatedMomentBlock (S : Finset ℕ) (q : ℕ) [NeZero q] : Finset ℕ :=
  S ∪ (momentBlock q).image (4*(3*q)^3+·)

lemma translatedMomentBlock_prefix (S : Finset ℕ) (q : ℕ) [NeZero q]
    (hS : ∀ x ∈ S, 0 < x) (hq : 2*(∑ x ∈ S, x) < q) :
    initialSegment (translatedMomentBlock S q : Set ℕ) (q^3) = S := by
  have hqp : 0 < q := NeZero.pos q
  have hqpow : q ≤ q^3 := Nat.le_pow (by omega)
  have hgap : q^3 < 4*(3*q)^3 := by
    rw [mul_pow]
    norm_num
    nlinarith [pow_pos hqp 3]
  ext x
  constructor
  · intro hx
    obtain ⟨hxu,_,hxn⟩ := mem_initialSegment.mp hx
    rcases Finset.mem_union.mp hxu with hs | ht
    · exact hs
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
      omega
  · intro hx
    have hsum : x ≤ ∑ y ∈ S, y :=
      Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx
    exact mem_initialSegment.mpr ⟨Finset.mem_union_left _ hx,hS x hx,by omega⟩

/-- The gap before each new block is quantitatively sparse. A dense terminal
block therefore does not supply the uniform prefix bound needed for a disproof. -/
lemma translatedMomentBlock_sparse_cutoff (S : Finset ℕ) (q : ℕ) [NeZero q]
    (hS : ∀ x ∈ S, 0 < x) (hq : 2*(∑ x ∈ S, x) < q) :
    ((translatedMomentBlock S q : Set ℕ) ∩ Icc 1 (q^3)).ncard /
      ((q^3 : ℕ) : ℝ)^(1/3 : ℝ) ≤ 1/((S.card : ℝ)+1) := by
  have hcard : ((translatedMomentBlock S q : Set ℕ) ∩ Icc 1 (q^3)).ncard = S.card := by
    rw [← card_initialSegment,translatedMomentBlock_prefix S q hS hq]
  have hp : ((q^3 : ℕ) : ℝ)^(1/3 : ℝ) = (q : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
    norm_num
  have hbound : S.card*(S.card+1) ≤ q :=
    (positive_finset_sum_lower_bound S hS).trans (Nat.le_of_lt hq)
  rw [hcard,hp]
  apply (div_le_div_iff₀ (by exact_mod_cast NeZero.pos q) (by positivity)).mpr
  simpa only [one_mul] using (show (S.card : ℝ)*((S.card : ℝ)+1) ≤ (q : ℝ) by exact_mod_cast hbound)

/-- Once the old set is larger than `C`, a single translated-block extension
cannot itself provide even `|S|+1` points with the required uniform cubic bounds. -/
lemma no_cubic_configuration_from_translatedMomentBlock
    (S : Finset ℕ) (q C : ℕ) [NeZero q]
    (hS : ∀ x ∈ S, 0 < x) (hq : 2*(∑ x ∈ S, x) < q) (hC : C < S.card) :
    ¬ ∃ a : CubicConfiguration C (S.card+1),
      Set.range (fun i => (a.val i : ℕ)) ⊆ (translatedMomentBlock S q : Set ℕ) := by
  have hsum := positive_finset_sum_lower_bound S hS
  have hCq : C*(S.card+1) < q := by nlinarith
  have hmax : C*(S.card+1)^3 < q^3 := by
    calc
      C*(S.card+1)^3 ≤ C^3*(S.card+1)^3 :=
        Nat.mul_le_mul_right _ (Nat.le_pow (by omega : 0 < 3))
      _ = (C*(S.card+1))^3 := (mul_pow _ _ _).symm
      _ < q^3 := Nat.pow_lt_pow_left hCq (by decide)
  have hgap : q^3 < 4*(3*q)^3 := by
    have hp : 0 < q^3 := pow_pos (NeZero.pos q) 3
    rw [mul_pow]
    norm_num
    nlinarith
  rintro ⟨a,ha⟩
  have hsub : Finset.univ.image (fun i => (a.val i : ℕ)) ⊆ S := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    have hval : (a.val i : ℕ) ≤ C*((i : ℕ)+1)^3 := Nat.le_of_lt_succ (a.val i).isLt
    have hi : (i : ℕ)+1 ≤ S.card+1 := by omega
    have hb : (a.val i : ℕ) < q^3 :=
      hval.trans_lt ((Nat.mul_le_mul_left C (Nat.pow_le_pow_left hi 3)).trans_lt hmax)
    rcases Finset.mem_union.mp (ha (Set.mem_range_self i)) with hs | ht
    · exact hs
    · obtain ⟨y,hy,he⟩ := Finset.mem_image.mp ht
      omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ a.property.1.injective,Finset.card_univ,Fintype.card_fin] at hc
  omega


lemma initialSegment_cube_bound {A : Set ℕ} (h : NtupleCondition A 3)
    {H : ℕ} (hH : 1 ≤ H) : (initialSegment A H).card^3 ≤ 192*H := by
  let k := (initialSegment A H).card
  have hb : (k-2)^3 ≤ 18*H+6 := by
    simpa only [k, card_initialSegment] using cube_count_bound h H
  change k^3 ≤ 192*H
  by_cases hk : k ≤ 3
  · have hh := Nat.pow_le_pow_left hk 3
    norm_num at hh
    omega
  · have hh := Nat.pow_le_pow_left (show k ≤ 2*(k-2) by omega) 3
    rw [mul_pow] at hh
    norm_num at hh
    omega

lemma global_short_difference_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H : ℕ) (hH : 1 ≤ H) (R : Finset (ℕ × ℕ))
    (hR : ∀ p ∈ R, p.1 ∈ A ∧ p.2 ∈ A ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ p.1+H) :
    (initialSegment A H).card * R.card ≤ 400*H := by
  let P := R.filter (fun p => p.1 ≤ H)
  let T := R.filter (fun p => ¬ p.1 ≤ H)
  have hpart : P.card + T.card = R.card := Finset.card_filter_add_card_filter_not (s := R) (fun p => p.1 ≤ H)
  have hp : P ⊆ initialSegment A (2*H) ×ˢ initialSegment A (2*H) := by
    intro p hp
    obtain ⟨hpR,hpH⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpa,hpb,hp1,hp2,hp3⟩ := hR p hpR
    exact Finset.mem_product.mpr ⟨mem_initialSegment.mpr ⟨hpa,hp1,by omega⟩,
      mem_initialSegment.mpr ⟨hpb,by omega,by omega⟩⟩
  have hpc : P.card ≤ (initialSegment A (2*H)).card^2 := by
    simpa only [Finset.card_product, pow_two] using Finset.card_le_card hp
  have hmon : (initialSegment A H).card ≤ (initialSegment A (2*H)).card :=
    Finset.card_le_card (initialSegment_mono A (by omega))
  have hc := initialSegment_cube_bound h (show 1 ≤ 2*H by omega)
  have hprefix : (initialSegment A H).card * P.card ≤ 384*H := by
    calc
      (initialSegment A H).card * P.card ≤
          (initialSegment A (2*H)).card * (initialSegment A (2*H)).card^2 :=
        Nat.mul_le_mul hmon hpc
      _ = (initialSegment A (2*H)).card^3 := by ring
      _ ≤ 384*H := by omega
  have htail := short_difference_count_bound h hA H T (by
    intro p hp
    obtain ⟨hpR,hpH⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpa,hpb,hp1,hp2,hp3⟩ := hR p hpR
    exact ⟨hpa,hpb,by omega,hp2,hp3⟩)
  rw [← card_initialSegment] at htail
  rw [← hpart, Nat.mul_add]
  omega

def shortDifferencePairs (A : Set ℕ) (H : ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 ∈ A ∧ p.2 ∈ A ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ p.1+H}

lemma shortDifferencePairs_finite {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) {H : ℕ} (hH : 1 ≤ H) (hp : 1 ≤ (initialSegment A H).card) :
    (shortDifferencePairs A H).Finite := by
  by_contra hi
  have hinf : (shortDifferencePairs A H).Infinite := hi
  obtain ⟨R,hR,hRc⟩ := hinf.exists_subset_card_eq (400*H+1)
  have hb := global_short_difference_count_bound h hA H hH R (fun p hp => hR hp)
  have hm := Nat.mul_le_mul_right R.card hp
  omega

lemma global_short_difference_real_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) {ε : ℝ} (hε : 0 < ε) {H : ℕ} (hH : 1 ≤ H)
    (hlow : ε ≤ (A ∩ Icc 1 H).ncard / (H : ℝ)^(1/3 : ℝ))
    (R : Finset (ℕ × ℕ)) (hR : (R : Set (ℕ × ℕ)) ⊆ shortDifferencePairs A H) :
    (R.card : ℝ) ≤ (400/ε)*(H : ℝ)^(2/3 : ℝ) := by
  let x := (H : ℝ)^(1/3 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < H)) _
  have hx3 : x^3 = (H : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hx2 : x^2 = (H : ℝ)^(2/3 : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hlo : ε*x ≤ (initialSegment A H).card := by
    rw [card_initialSegment]
    exact (le_div_iff₀ hx).mp hlow
  have hg : ((initialSegment A H).card : ℝ) * (R.card : ℝ) ≤ 400*(H : ℝ) := by
    exact_mod_cast global_short_difference_count_bound h hA H hH R (fun p hp => hR hp)
  have hm := mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg R.card : (0 : ℝ) ≤ R.card)
  have he : x*(ε*(R.card : ℝ)) ≤ x*(400*x^2) := by nlinarith
  have hh := le_of_mul_le_mul_left he hx
  rw [← hx2]
  calc
    (R.card : ℝ) = (ε*(R.card : ℝ))/ε := by field_simp
    _ ≤ (400*x^2)/ε := div_le_div_of_nonneg_right hh hε.le
    _ = (400/ε)*x^2 := by ring

/-- Positive critical lower density would bound the number of short differences
throughout the whole infinite set, not merely inside a chosen cutoff. -/
lemma failure_yields_global_difference_growth {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, ∀ H ≥ M,
      (shortDifferencePairs A H).Finite ∧
      ((shortDifferencePairs A H).ncard : ℝ) ≤ K*(H : ℝ)^(2/3 : ℝ) := by
  obtain ⟨ε,hε,M,hM⟩ := (density_liminf_ne_zero_iff h).mp hf
  refine ⟨400/ε,by positivity,max M 1,?_⟩
  intro H hH
  have hH1 : 1 ≤ H := by omega
  have hlo := hM H (by omega)
  have hp : 1 ≤ (initialSegment A H).card := by
    have hroot : (0 : ℝ) < (H : ℝ)^(1/3 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < H)) _
    have hh := (le_div_iff₀ hroot).mp hlo
    have hpos : (0 : ℝ) < (A ∩ Icc 1 H).ncard := lt_of_lt_of_le (mul_pos hε hroot) hh
    rw [card_initialSegment]
    exact_mod_cast hpos
  have hfin := shortDifferencePairs_finite h hA hH1 hp
  refine ⟨hfin,?_⟩
  have hb := global_short_difference_real_bound h hA hε hH1 hlo hfin.toFinset
    (fun _ hh => hfin.mem_toFinset.mp hh)
  simpa only [Set.ncard_eq_toFinset_card _ hfin] using hb



lemma shifted_difference_count_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H : ℕ) (L : ℤ) (R : Finset (ℕ × ℕ))
    (hR : ∀ p ∈ R, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 ∧
      L ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 ≤ L + H) :
    ((initialSegment A H).card - 2) * R.card ≤ 10 * (2*H + 1) := by
  classical
  let P := initialSegment A H
  let Q := (R ×ˢ P).filter (fun q => q.2 ≠ q.1.1 ∧ q.2 ≠ q.1.2)
  have hQ : ∀ q ∈ Q, q.1 ∈ R ∧ q.2 ∈ P ∧ q.2 ≠ q.1.1 ∧ q.2 ≠ q.1.2 := by
    intro q hq
    simpa only [Q, Finset.mem_filter, Finset.mem_product, and_assoc] using hq
  have hlo : (P.card - 2)*R.card ≤ Q.card := by
    have he := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (s := Q) (t := R) (fun q hq => (hQ q hq).1)
    rw [he]
    calc
      (P.card - 2)*R.card = ∑ _p ∈ R, (P.card - 2) := by simp [mul_comm]
      _ ≤ ∑ p ∈ R, (Q.filter (fun q => q.1 = p)).card := by
        apply Finset.sum_le_sum
        intro p hp
        have heq : Q.filter (fun q => q.1 = p) =
            (P \ {p.1, p.2}).image (fun x => (p, x)) := by
          ext ⟨r,x⟩
          simp only [Q, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
            Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          aesop
        rw [heq, Finset.card_image_of_injective _ (by
          intro x y hxy
          exact congrArg Prod.snd hxy)]
        have hc := Finset.card_sdiff_add_card_inter P {p.1,p.2}
        have hi : (P ∩ {p.1,p.2}).card ≤ 2 :=
          (Finset.card_le_card Finset.inter_subset_right).trans (by simpa using Finset.card_insert_le p.1 ({p.2} : Finset ℕ))
        omega
  let f : (ℕ × ℕ) × ℕ → Finset ℕ × ℕ := fun q => ({q.2,q.1.2},q.1.1)
  have hfcard : ∀ v ∈ Q.image f, v.1.card = 2 := by
    intro v hv
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    simp only [f, Finset.card_pair (hQ q hq).2.2.2]
  have htwo : Q.card ≤ 2*(Q.image f).card := by
    apply Finset.card_le_mul_card_image Q 2
    intro v hv
    calc
      (Q.filter (fun q => f q = v)).card ≤ v.1.card := by
        apply Finset.card_le_card_of_injOn (fun q => q.2)
        · intro q hq
          obtain ⟨hqQ,hqv⟩ := Finset.mem_filter.mp hq
          have he : ({q.2,q.1.2} : Finset ℕ) = v.1 := congrArg Prod.fst hqv
          rw [← he]
          simp
        · intro q hq r hr hqr
          obtain ⟨hqQ,hqv⟩ := Finset.mem_filter.mp hq
          obtain ⟨hrQ,hrv⟩ := Finset.mem_filter.mp hr
          have he : f q = f r := hqv.trans hrv.symm
          have ha : q.1.1 = r.1.1 := congrArg Prod.snd he
          have hs := congrArg (fun v : Finset ℕ × ℕ => ∑ x ∈ v.1, x) he
          have hqn := (hQ q hqQ).2.2.2
          have hrn := (hQ r hrQ).2.2.2
          simp only [f, Finset.sum_pair hqn, Finset.sum_pair hrn] at hs
          change q.2 = r.2 at hqr
          exact Prod.ext (Prod.ext ha (by omega)) hqr
      _ = 2 := hfcard v hv
  have hb : (Q.image f).card ≤ 5*((L+(2*H : ℕ)+1-L).toNat) := by
    apply signed_sum_interval_card_bound h hA L (L+(2*H : ℕ))
    intro v hv
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hqR,hqP,hqa,hqb⟩ := hQ q hq
    obtain ⟨ha,hb,hab,hl,hu⟩ := hR q.1 hqR
    obtain ⟨hx,hx1,hxH⟩ := mem_initialSegment.mp hqP
    refine ⟨?_,by simp [f,hqb],ha,?_,?_,?_⟩
    · intro x hx'
      simp only [f, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · exact hx
      · exact hb
    · simp only [f, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hqa,hab⟩
    · simp only [f,Finset.sum_pair hqb,Nat.cast_add]
      omega
    · simp only [f,Finset.sum_pair hqb,Nat.cast_add]
      omega
  have he : (L+(2*H : ℕ)+1-L).toNat = 2*H+1 := by omega
  rw [he] at hb
  exact hlo.trans (htwo.trans (by omega))

/-- Nonzero differences with a specified window, retaining their representations. -/
def shiftedDifferencePairs (A : Set ℕ) (H : ℕ) (L : ℤ) : Set (ℕ × ℕ) :=
  {p | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 ∧
    L ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 ≤ L + H}

lemma initialSegment_card_eventually_large {A : Set ℕ} (hA : A.Infinite) (k : ℕ) :
    ∃ M : ℕ, ∀ H ≥ M, k ≤ (initialSegment A H).card := by
  classical
  have hpos : (A \ {0}).Infinite := hA.diff (Set.finite_singleton 0)
  obtain ⟨S,hS,hSc⟩ := hpos.exists_subset_card_eq k
  refine ⟨S.sup id,?_⟩
  intro H hH
  rw [← hSc]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxA,hx0⟩ := hS hx
  have hx0' : x ≠ 0 := by simpa using hx0
  have hxM : x ≤ S.sup id := Finset.le_sup (f := id) hx
  exact mem_initialSegment.mpr ⟨hxA,by omega,by omega⟩

lemma shiftedDifferencePairs_finite {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H : ℕ) (L : ℤ) : (shiftedDifferencePairs A H L).Finite := by
  obtain ⟨M,hM⟩ := initialSegment_card_eventually_large hA 3
  let W := max M H
  have hm : 3 ≤ (initialSegment A W).card := hM W (le_max_left _ _)
  by_contra hi
  have hinf : (shiftedDifferencePairs A H L).Infinite := hi
  obtain ⟨R,hR,hRc⟩ := hinf.exists_subset_card_eq (10*(2*W+1)+1)
  have hb := shifted_difference_count_bound h hA W L R (by
    intro p hp
    obtain ⟨ha,hb,hab,hl,hu⟩ := hR hp
    refine ⟨ha,hb,hab,hl,?_⟩
    have hHW : H ≤ W := le_max_right _ _
    exact hu.trans (by exact_mod_cast (show L+(H : ℤ) ≤ L+(W : ℤ) by omega)))
  have hmul := Nat.mul_le_mul_right R.card (show 1 ≤ (initialSegment A W).card-2 by omega)
  omega

lemma shifted_difference_ncard_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (H : ℕ) (L : ℤ) :
    ((initialSegment A H).card-2)*(shiftedDifferencePairs A H L).ncard ≤
      10*(2*H+1) := by
  have hf := shiftedDifferencePairs_finite h hA H L
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact shifted_difference_count_bound h hA H L hf.toFinset
    (fun p hp => hf.mem_toFinset.mp hp)

/-- Uniformly over the position of the difference window, the number of
representations is sublinear in its width. -/
lemma shifted_difference_ncard_uniform_sublinear {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ H ≥ M, ∀ L : ℤ,
      ((shiftedDifferencePairs A H L).ncard : ℝ) ≤ ε*(H : ℝ) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (30/ε)
  have hkpos : 0 < k := by
    have hx : (0 : ℝ) < (k : ℝ) := lt_trans (by positivity) hk
    exact_mod_cast hx
  have hke : (30 : ℝ) ≤ ε*k := le_of_lt (by
    have hb := (div_lt_iff₀ hε).mp hk
    simpa [mul_comm] using hb)
  obtain ⟨M,hM⟩ := initialSegment_card_eventually_large hA (k+2)
  refine ⟨max M 1,?_⟩
  intro H hH L
  have hH1 : 1 ≤ H := by omega
  have hm : k ≤ (initialSegment A H).card-2 := by
    have hh := hM H (by omega)
    omega
  have hb := (Nat.mul_le_mul_right (shiftedDifferencePairs A H L).ncard hm).trans
    (shifted_difference_ncard_bound h hA H L)
  have hb' : (k : ℝ)*((shiftedDifferencePairs A H L).ncard : ℝ) ≤ 30*(H : ℝ) := by
    exact_mod_cast (show k*(shiftedDifferencePairs A H L).ncard ≤ 30*H by omega)
  have hfin := mul_le_mul_of_nonneg_right hke (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
  apply le_of_mul_le_mul_left (a := (k : ℝ)) _ (by exact_mod_cast hkpos)
  nlinarith

lemma shifted_difference_real_bound {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) {ε : ℝ} (hε : 0 < ε) {H : ℕ} (hH : 1 ≤ H)
    (hm : 4 ≤ (initialSegment A H).card)
    (hlow : ε ≤ (A ∩ Icc 1 H).ncard / (H : ℝ)^(1/3 : ℝ)) (L : ℤ) :
    ((shiftedDifferencePairs A H L).ncard : ℝ) ≤
      (60/ε)*(H : ℝ)^(2/3 : ℝ) := by
  let x := (H : ℝ)^(1/3 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < H)) _
  have hx3 : x^3 = (H : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hx2 : x^2 = (H : ℝ)^(2/3 : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hlo : ε*x ≤ (initialSegment A H).card := by
    rw [card_initialSegment]
    exact (le_div_iff₀ hx).mp hlow
  have hg : ((initialSegment A H).card : ℝ)*
      ((shiftedDifferencePairs A H L).ncard : ℝ) ≤ 60*(H : ℝ) := by
    have hb := shifted_difference_ncard_bound h hA H L
    have hh : (initialSegment A H).card ≤ 2*((initialSegment A H).card-2) := by omega
    have hb' := Nat.mul_le_mul_right (shiftedDifferencePairs A H L).ncard hh
    have he : 2*((initialSegment A H).card-2)*(shiftedDifferencePairs A H L).ncard =
      2*(((initialSegment A H).card-2)*(shiftedDifferencePairs A H L).ncard) := by ring
    rw [he] at hb'
    exact_mod_cast (show (initialSegment A H).card*(shiftedDifferencePairs A H L).ncard ≤
      60*H by omega)
  have hmul := mul_le_mul_of_nonneg_right hlo
    (Nat.cast_nonneg (shiftedDifferencePairs A H L).ncard : (0 : ℝ) ≤ _)
  have he : x*(ε*((shiftedDifferencePairs A H L).ncard : ℝ)) ≤ x*(60*x^2) := by nlinarith
  have hh := le_of_mul_le_mul_left he hx
  rw [← hx2]
  calc
    ((shiftedDifferencePairs A H L).ncard : ℝ) =
        (ε*((shiftedDifferencePairs A H L).ncard : ℝ))/ε := by field_simp
    _ ≤ (60*x^2)/ε := div_le_div_of_nonneg_right hh hε.le
    _ = (60/ε)*x^2 := by ring

/-- A counterexample would have a uniform, translation-independent two-thirds
power bound for all of its nonzero difference representations. -/
lemma failure_yields_uniform_difference_growth {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, ∀ H ≥ M, ∀ L : ℤ,
      (shiftedDifferencePairs A H L).Finite ∧
      ((shiftedDifferencePairs A H L).ncard : ℝ) ≤ K*(H : ℝ)^(2/3 : ℝ) := by
  obtain ⟨ε,hε,M,hM⟩ := (density_liminf_ne_zero_iff h).mp hf
  obtain ⟨B,hB⟩ := initialSegment_card_eventually_large hA 4
  refine ⟨60/ε,by positivity,max (max M B) 1,?_⟩
  intro H hH L
  exact ⟨shiftedDifferencePairs_finite h hA H L,
    shifted_difference_real_bound h hA hε (by omega) (hB H (by omega))
      (hM H (by omega)) L⟩



lemma strictMono_bounded_tag {M B : ℕ} (hBM : B < M)
    (t : ℕ → ℕ) (ht : ∀ a, t a ≤ B) :
    StrictMono (fun a => M*a+t a) := by
  intro a b hab
  have hh := Nat.mul_le_mul_left M (show a+1 ≤ b by omega)
  have he : M*(a+1) = M*a+M := by ring
  rw [he] at hh
  have ha := ht a
  change M*a+t a < M*b+t b
  omega

lemma bounded_tag_sum_decode {M B n : ℕ} (hM : n*B < M)
    (t : ℕ → ℕ) (ht : ∀ a, t a ≤ B) (I J : Finset ℕ)
    (hI : I.card = n) (hJ : J.card = n)
    (hs : ∑ a ∈ I, (M*a+t a) = ∑ a ∈ J, (M*a+t a)) :
    ∑ a ∈ I, a = ∑ a ∈ J, a := by
  have hMpos : 0 < M := by omega
  have hTI : ∑ a ∈ I, t a < M := by
    calc
      ∑ a ∈ I, t a ≤ ∑ _a ∈ I, B := Finset.sum_le_sum (fun a _ => ht a)
      _ = n*B := by simp [hI]
      _ < M := hM
  have hTJ : ∑ a ∈ J, t a < M := by
    calc
      ∑ a ∈ J, t a ≤ ∑ _a ∈ J, B := Finset.sum_le_sum (fun a _ => ht a)
      _ = n*B := by simp [hJ]
      _ < M := hM
  simp only [Finset.sum_add_distrib] at hs
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hd := congrArg (fun x => x/M) hs
  simpa only [Nat.mul_add_div hMpos, Nat.div_eq_of_lt hTI,
    Nat.div_eq_of_lt hTJ, Nat.add_zero] using hd

lemma NtupleCondition.image_of_sum_decode {A : Set ℕ} {n : ℕ}
    (h : NtupleCondition A n) (f : ℕ → ℕ) (hf : Function.Injective f)
    (hdecode : ∀ I J : Finset ℕ, I.card = n → J.card = n →
      (∑ a ∈ I, f a = ∑ a ∈ J, f a) → ∑ a ∈ I, a = ∑ a ∈ J, a) :
    NtupleCondition (f '' A) n := by
  classical
  intro I J ⟨hIA,hJA,hIc,hJc,hs⟩
  let P := I.preimage f hf.injOn
  let Q := J.preimage f hf.injOn
  have hIP : P.image f = I := by
    rw [Finset.image_preimage]
    apply Finset.filter_true_of_mem
    intro x hx
    obtain ⟨a,ha,rfl⟩ := hIA hx
    exact Set.mem_range_self a
  have hJQ : Q.image f = J := by
    rw [Finset.image_preimage]
    apply Finset.filter_true_of_mem
    intro x hx
    obtain ⟨a,ha,rfl⟩ := hJA hx
    exact Set.mem_range_self a
  have hPA : (P : Set ℕ) ⊆ A := by
    intro x hx
    have hfx : f x ∈ I := by simpa only [P,Finset.mem_coe,Finset.mem_preimage] using hx
    obtain ⟨a,ha,he⟩ := hIA hfx
    exact hf he ▸ ha
  have hQA : (Q : Set ℕ) ⊆ A := by
    intro x hx
    have hfx : f x ∈ J := by simpa only [Q,Finset.mem_coe,Finset.mem_preimage] using hx
    obtain ⟨a,ha,he⟩ := hJA hfx
    exact hf he ▸ ha
  have hPc : P.card = n := by
    rw [← hIc,← hIP,Finset.card_image_of_injective _ hf]
  have hQc : Q.card = n := by
    rw [← hJc,← hJQ,Finset.card_image_of_injective _ hf]
  have hsf : ∑ a ∈ P, f a = ∑ a ∈ Q, f a := by
    rw [← hIP,← hJQ,Finset.sum_image hf.injOn,Finset.sum_image hf.injOn] at hs
    exact hs
  have hPQ : P = Q := h P Q ⟨hPA,hQA,hPc,hQc,hdecode P Q hPc hQc hsf⟩
  rw [← hIP,← hJQ,hPQ]

lemma NtupleCondition.bounded_tag_image {A : Set ℕ} {n M B : ℕ}
    (h : NtupleCondition A n) (hBM : B < M) (hM : n*B < M)
    (t : ℕ → ℕ) (ht : ∀ a, t a ≤ B) :
    NtupleCondition ((fun a => M*a+t a) '' A) n := by
  exact h.image_of_sum_decode _ (strictMono_bounded_tag hBM t ht).injective
    (bounded_tag_sum_decode hM t ht)

lemma bounded_tag_cubic_bound {a : ℕ → ℕ} {C M B : ℕ}
    (ha : ∀ n, a n ≤ C*(n+1)^3) (t : ℕ → ℕ) (ht : ∀ a, t a ≤ B) (n : ℕ) :
    M*a n+t (a n) ≤ (M*C+B)*(n+1)^3 := by
  have hn : 1 ≤ (n+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hmul := Nat.mul_le_mul_left M (ha n)
  have hb := Nat.mul_le_mul_left B hn
  have ht' := ht (a n)
  calc
    M*a n+t (a n) ≤ M*(C*(n+1)^3)+B*(n+1)^3 := by omega
    _ = (M*C+B)*(n+1)^3 := by ring

/-- Arbitrary bounded residue tags do not eliminate a hypothetical counterexample,
provided the dilation is larger than every possible three-tag sum. -/
lemma bounded_tag_preserves_failure {A : Set ℕ} (h : NtupleCondition A 3)
    (hA : A.Infinite) (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0)
    {M B : ℕ} (hM : 3*B < M) (t : ℕ → ℕ) (ht : ∀ a, t a ≤ B) :
    let T := (fun a => M*a+t a) '' A
    T.Infinite ∧ NtupleCondition T 3 ∧
      Filter.atTop.liminf
        (fun N => (T ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0 := by
  let f := fun a => M*a+t a
  have hBM : B < M := by omega
  have hmono : StrictMono f := strictMono_bounded_tag hBM t ht
  have hT : (f '' A).Infinite := hA.image hmono.injective.injOn
  have h3T : NtupleCondition (f '' A) 3 := h.bounded_tag_image hBM hM t ht
  refine ⟨hT,h3T,?_⟩
  intro hz
  obtain ⟨a,C,hC,ha,haA,hbound⟩ := failure_yields_cubic_enumeration h hA hf
  have hnone := (density_liminf_eq_zero_iff_no_cubic_enumeration h3T hT).mp hz
  apply hnone
  refine ⟨f ∘ a,M*C+B,?_,hmono.comp ha,?_,?_⟩
  · have hMpos : 0 < M := by omega
    have hp := Nat.mul_pos hMpos hC
    omega
  · intro x hx
    obtain ⟨n,rfl⟩ := hx
    exact ⟨a n,haA ▸ Set.mem_range_self n,rfl⟩
  · intro n
    exact bounded_tag_cubic_bound hbound t ht n


/- Large four-sum matchings forced by a hypothetical counterexample.
These are necessary consequences, not a settlement of the conjecture. -/

lemma exists_large_four_sum_matching {A : Set ℕ} (h : NtupleCondition A 3)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) (N k : ℕ)
    (hN : ∀ a ∈ S, a ≤ N)
    (hk : (4*N+1)*k < S.card.choose 4) :
    ∃ t : ℕ, ∃ R : Finset (Finset ℕ),
      k < R.card ∧ (R : Set (Finset ℕ)).PairwiseDisjoint id ∧
      ∀ I ∈ R, I ⊆ S ∧ I.card = 4 ∧ ∑ a ∈ I, a = t := by
  classical
  let f : Finset ℕ → ℕ := fun I => ∑ a ∈ I, a
  have hm : ∀ I ∈ S.powersetCard 4, f I ∈ Finset.range (4*N+1) := by
    intro I hI
    obtain ⟨hIS,hIc⟩ := Finset.mem_powersetCard.mp hI
    apply Finset.mem_range.mpr
    have hb : f I ≤ 4*N := by
      calc
        f I ≤ ∑ _a ∈ I, N := Finset.sum_le_sum (fun a ha => hN a (hIS ha))
        _ = 4*N := by simp [hIc]
    omega
  have hk' : (Finset.range (4*N+1)).card*k < (S.powersetCard 4).card := by
    simpa using hk
  obtain ⟨t,ht,hfiber⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hm hk'
  let R := (S.powersetCard 4).filter (fun I => f I = t)
  have hR : ∀ I ∈ R, I ⊆ S ∧ I.card = 4 ∧ ∑ a ∈ I, a = t := by
    intro I hI
    obtain ⟨hIS,hIt⟩ := Finset.mem_filter.mp hI
    obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hIS
    exact ⟨hsub,hcard,hIt⟩
  refine ⟨t,R,hfiber,?_,hR⟩
  apply four_sum_fiber_pairwiseDisjoint h R t
  intro I hI
  obtain ⟨hIS,hIc,hIt⟩ := hR I hI
  exact ⟨fun a ha => hS (hIS ha),hIc,hIt⟩

lemma choose_four_cubic_lower {n : ℕ} (hn : 6 ≤ n) :
    n^4 ≤ 384*n.choose 4 := by
  have hs : (n-3)^4 ≤ n.descFactorial 4 := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
    have h0 : n-3 ≤ n := by omega
    have h1 : n-3 ≤ n-1 := by omega
    have h2 : n-3 ≤ n-2 := by omega
    calc
      (n-3)^4 = (n-3)*((n-3)*((n-3)*(n-3))) := by ring
      _ ≤ (n-3)*((n-2)*((n-1)*n)) := by gcongr
      _ = _ := by simp
  have hn' : n ≤ 2*(n-3) := by omega
  have hp := Nat.pow_le_pow_left hn' 4
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hs
  norm_num at hs
  nlinarith [show (2*(n-3))^4 = 16*(n-3)^4 by ring]

lemma cubic_prefix_four_matching_threshold {n C k : ℕ} (hC : 0 < C)
    (hn : 1921*C*(k+1) ≤ n) :
    (4*(C*n^3)+1)*k < n.choose 4 := by
  have hn6 : 6 ≤ n := by nlinarith
  have hnpos : 0 < n := by omega
  have hn3 : 0 < n^3 := pow_pos hnpos _
  have hCn3 : 1 ≤ C*n^3 := Nat.mul_pos hC hn3
  have hb : 4*(C*n^3)+1 ≤ 5*C*n^3 := by nlinarith
  have hk : 1920*C*k < n := by nlinarith
  have hmain : 384*((4*(C*n^3)+1)*k) < n^4 := by
    calc
      384*((4*(C*n^3)+1)*k) ≤ 384*((5*C*n^3)*k) := by gcongr
      _ = (1920*C*k)*n^3 := by ring
      _ < n*n^3 := Nat.mul_lt_mul_of_pos_right hk hn3
      _ = n^4 := by ring
  have hlo := choose_four_cubic_lower hn6
  omega

lemma cubic_sequence_forces_large_tail_four_matching {a : ℕ → ℕ} {C : ℕ}
    (ha : StrictMono a) (h3 : NtupleCondition (Set.range a) 3)
    (hC : 0 < C) (hbound : ∀ i, a i ≤ C*(i+1)^3) (k L : ℕ) :
    ∃ t : ℕ, ∃ R : Finset (Finset ℕ),
      k < R.card ∧ (R : Set (Finset ℕ)).PairwiseDisjoint id ∧
      ∀ I ∈ R, (I : Set ℕ) ⊆ Set.range a ∧
        (∀ x ∈ I, L ≤ x) ∧ I.card = 4 ∧ ∑ x ∈ I, x = t := by
  classical
  let D := C*(L+1)^3
  have hD : 0 < D := by dsimp [D]; positivity
  let b : ℕ → ℕ := fun i => a (L+i)
  have hbmono : StrictMono b := by
    intro i j hij
    exact ha (by omega)
  have hb : ∀ i, b i ≤ D*(i+1)^3 := by
    intro i
    have hi : L+i+1 ≤ (L+1)*(i+1) := by nlinarith
    calc
      b i ≤ C*(L+i+1)^3 := hbound _
      _ ≤ C*((L+1)*(i+1))^3 := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hi 3)
      _ = D*(i+1)^3 := by dsimp [D]; ring
  let n := 1921*D*(k+1)
  let S := (Finset.range n).image b
  have hSc : S.card = n := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hbmono.injective, Finset.card_range]
  have hSA : (S : Set ℕ) ⊆ Set.range a := by
    intro x hx
    change x ∈ (Finset.range n).image b at hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact Set.mem_range_self _
  have hSN : ∀ x ∈ S, x ≤ D*n^3 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hin : i+1 ≤ n := Finset.mem_range.mp hi
    exact (hb i).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hin 3))
  have hk : (4*(D*n^3)+1)*k < S.card.choose 4 := by
    rw [hSc]
    exact cubic_prefix_four_matching_threshold hD (le_refl n)
  obtain ⟨t,R,hRk,hdisj,hR⟩ := exists_large_four_sum_matching h3 S hSA (D*n^3) k hSN hk
  refine ⟨t,R,hRk,hdisj,?_⟩
  intro I hI
  obtain ⟨hIS,hIc,hIt⟩ := hR I hI
  refine ⟨fun x hx => hSA (hIS hx),?_,hIc,hIt⟩
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (hIS hx)
  change L ≤ a (L+i)
  exact (Nat.le_add_right L i).trans (ha.id_le (L+i))

lemma failure_yields_large_tail_four_matching {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0)
    (k L : ℕ) :
    ∃ t : ℕ, ∃ R : Finset (Finset ℕ),
      k < R.card ∧ (R : Set (Finset ℕ)).PairwiseDisjoint id ∧
      ∀ I ∈ R, (I : Set ℕ) ⊆ A ∧
        (∀ x ∈ I, L ≤ x) ∧ I.card = 4 ∧ ∑ x ∈ I, x = t := by
  obtain ⟨a,C,hC,ha,haA,hbound⟩ := failure_yields_cubic_enumeration h hA hf
  have h3 : NtupleCondition (Set.range a) 3 := haA.symm ▸ h
  simpa only [haA] using
    cubic_sequence_forces_large_tail_four_matching ha h3 hC hbound k L


/- Pair-sum difference bounds. Cardinality bounds below are not claims of
interval coverage, and do not settle the conjecture. -/

lemma two_set_complement {P : Finset ℕ} (hP : P.card = 2) {x : ℕ} (hx : x ∈ P) :
    x ≠ (∑ a ∈ P, a)-x ∧ P = {x,(∑ a ∈ P, a)-x} ∧
      (∑ a ∈ P, a)-x ∈ P ∧ ∑ a ∈ P, a = x+((∑ a ∈ P, a)-x) := by
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp [huv,Finset.sum_pair huv]
  · simp [huv,huv.symm,Finset.sum_pair huv,Finset.pair_comm,Nat.add_comm]

lemma disjoint_pair_difference_fiber_bound {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) (t : ℤ)
    (R : Finset (Finset ℕ × Finset ℕ))
    (hR : ∀ p ∈ R, p.1 ⊆ S ∧ p.2 ⊆ S ∧ p.1.card = 2 ∧ p.2.card = 2 ∧
      Disjoint p.1 p.2 ∧ ((∑ a ∈ p.1, a : ℕ) : ℤ) - (∑ a ∈ p.2, a : ℕ) = t) :
    R.card ≤ 5*S.card := by
  classical
  let F := fun x => R.filter (fun p => x ∈ p.1)
  have hfiber : ∀ x ∈ S, (F x).card ≤ 5 := by
    intro x hx
    let f : Finset ℕ × Finset ℕ → Finset ℕ × ℕ :=
      fun p => (p.2,(∑ a ∈ p.1, a)-x)
    have hi : Set.InjOn f (F x : Set (Finset ℕ × Finset ℕ)) := by
      intro p hp q hq he
      obtain ⟨hpR,hxp⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqR,hxq⟩ := Finset.mem_filter.mp hq
      have hp' := two_set_complement (hR p hpR).2.2.1 hxp
      have hq' := two_set_complement (hR q hqR).2.2.1 hxq
      have h2 : p.2 = q.2 := congrArg Prod.fst he
      have hy : (∑ a ∈ p.1, a)-x = (∑ a ∈ q.1, a)-x := congrArg Prod.snd he
      exact Prod.ext (by rw [hp'.2.1,hq'.2.1,hy]) h2
    rw [← Finset.card_image_of_injOn hi]
    apply signed_sum_fiber_card_le_five h hA ((x : ℤ)-t)
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hpR,hxp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hP,hQ,hPc,hQc,hdisj,ht⟩ := hR p hpR
    obtain ⟨hne,hPeq,hyP,hsum⟩ := two_set_complement hPc hxp
    refine ⟨fun a ha => hS (hQ ha),hQc,hS (hP hyP),?_,?_⟩
    · exact fun hyQ => Finset.disjoint_left.mp hdisj hyP hyQ
    · change ((∑ a ∈ p.2, a : ℕ) : ℤ) - (((∑ a ∈ p.1, a)-x : ℕ) : ℤ) = (x : ℤ)-t
      have he : ((∑ a ∈ p.1, a : ℕ) : ℤ) =
          (x : ℤ)+(((∑ a ∈ p.1, a)-x : ℕ) : ℤ) := by exact_mod_cast hsum
      omega
  have hcover : R ⊆ S.biUnion F := by
    intro p hp
    have hPc := (hR p hp).2.2.1
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < p.1.card by omega)
    exact Finset.mem_biUnion.mpr ⟨x,(hR p hp).1 hx,Finset.mem_filter.mpr ⟨hp,hx⟩⟩
  calc
    R.card ≤ (S.biUnion F).card := Finset.card_le_card hcover
    _ ≤ ∑ x ∈ S, (F x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, 5 := Finset.sum_le_sum hfiber
    _ = 5*S.card := by simp [mul_comm]

lemma intersecting_pair_difference_fiber_bound {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) {t : ℤ} (ht : t ≠ 0)
    (R : Finset (Finset ℕ × Finset ℕ))
    (hR : ∀ p ∈ R, p.1 ⊆ S ∧ p.2 ⊆ S ∧ p.1.card = 2 ∧ p.2.card = 2 ∧
      ¬ Disjoint p.1 p.2 ∧ ((∑ a ∈ p.1, a : ℕ) : ℤ) - (∑ a ∈ p.2, a : ℕ) = t) :
    R.card ≤ 2*S.card := by
  classical
  let F := fun x => R.filter (fun p => x ∈ p.1 ∧ x ∈ p.2)
  have hfiber : ∀ x ∈ S, (F x).card ≤ 2 := by
    intro x hx
    let f : Finset ℕ × Finset ℕ → ℕ × ℕ :=
      fun p => ((∑ a ∈ p.1, a)-x,(∑ a ∈ p.2, a)-x)
    have hi : Set.InjOn f (F x : Set (Finset ℕ × Finset ℕ)) := by
      intro p hp q hq he
      obtain ⟨hpR,hxp,hxP⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqR,hxq,hxQ⟩ := Finset.mem_filter.mp hq
      have hp1 := (two_set_complement (hR p hpR).2.2.1 hxp).2.1
      have hq1 := (two_set_complement (hR q hqR).2.2.1 hxq).2.1
      have hp2 := (two_set_complement (hR p hpR).2.2.2.1 hxP).2.1
      have hq2 := (two_set_complement (hR q hqR).2.2.2.1 hxQ).2.1
      have hy1 : (∑ a ∈ p.1, a)-x = (∑ a ∈ q.1, a)-x := congrArg Prod.fst he
      have hy2 : (∑ a ∈ p.2, a)-x = (∑ a ∈ q.2, a)-x := congrArg Prod.snd he
      exact Prod.ext (by rw [hp1,hq1,hy1]) (by rw [hp2,hq2,hy2])
    rw [← Finset.card_image_of_injOn hi]
    apply nonzero_difference_fiber_card_le_two h hA ht
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hpR,hxp,hxq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hP,hQ,hPc,hQc,hnd,hs⟩ := hR p hpR
    have hp' := two_set_complement hPc hxp
    have hq' := two_set_complement hQc hxq
    refine ⟨hS (hP hp'.2.2.1),hS (hQ hq'.2.2.1),?_⟩
    have he1 : ((∑ a ∈ p.1, a : ℕ) : ℤ) =
        (x : ℤ)+(((∑ a ∈ p.1, a)-x : ℕ) : ℤ) := by exact_mod_cast hp'.2.2.2
    have he2 : ((∑ a ∈ p.2, a : ℕ) : ℤ) =
        (x : ℤ)+(((∑ a ∈ p.2, a)-x : ℕ) : ℤ) := by exact_mod_cast hq'.2.2.2
    dsimp [f]
    omega
  have hcover : R ⊆ S.biUnion F := by
    intro p hp
    obtain ⟨x,hxP,hxQ⟩ := Finset.not_disjoint_iff.mp (hR p hp).2.2.2.2.1
    exact Finset.mem_biUnion.mpr ⟨x,(hR p hp).1 hxP,Finset.mem_filter.mpr ⟨hp,hxP,hxQ⟩⟩
  calc
    R.card ≤ (S.biUnion F).card := Finset.card_le_card hcover
    _ ≤ ∑ x ∈ S, (F x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, 2 := Finset.sum_le_sum hfiber
    _ = 2*S.card := by simp [mul_comm]

lemma pair_difference_fiber_bound {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) {t : ℤ} (ht : t ≠ 0)
    (R : Finset (Finset ℕ × Finset ℕ))
    (hR : ∀ p ∈ R, p.1 ⊆ S ∧ p.2 ⊆ S ∧ p.1.card = 2 ∧ p.2.card = 2 ∧
      ((∑ a ∈ p.1, a : ℕ) : ℤ) - (∑ a ∈ p.2, a : ℕ) = t) :
    R.card ≤ 7*S.card := by
  classical
  let D := R.filter (fun p => Disjoint p.1 p.2)
  let I := R.filter (fun p => ¬ Disjoint p.1 p.2)
  have hD : D.card ≤ 5*S.card := by
    apply disjoint_pair_difference_fiber_bound h hA S hS t
    intro p hp
    obtain ⟨hpR,hpd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hP,hQ,hPc,hQc,hs⟩ := hR p hpR
    exact ⟨hP,hQ,hPc,hQc,hpd,hs⟩
  have hI : I.card ≤ 2*S.card := by
    apply intersecting_pair_difference_fiber_bound h hA S hS ht
    intro p hp
    obtain ⟨hpR,hpd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hP,hQ,hPc,hQc,hs⟩ := hR p hpR
    exact ⟨hP,hQ,hPc,hQc,hpd,hs⟩
  have he : D.card+I.card = R.card := Finset.card_filter_add_card_filter_not (s := R) _
  omega

noncomputable def offDiagonalPairSumDifferences (S : Finset ℕ) : Finset ℤ :=
  (S.powersetCard 2).offDiag.image
    (fun p => ((∑ a ∈ p.1, a : ℕ) : ℤ) - (∑ a ∈ p.2, a : ℕ))

lemma nonzero_pair_sum_difference_count {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) :
    S.card.choose 2 * S.card.choose 2 - S.card.choose 2 ≤
      7*S.card*(offDiagonalPairSumDifferences S).card := by
  classical
  let T := S.powersetCard 2
  let f : Finset ℕ × Finset ℕ → ℤ :=
    fun p => ((∑ a ∈ p.1, a : ℕ) : ℤ) - (∑ a ∈ p.2, a : ℕ)
  have htnz : ∀ p ∈ T.offDiag, f p ≠ 0 := by
    intro p hp ht
    obtain ⟨hP,hQ,hne⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨hPS,hPc⟩ := Finset.mem_powersetCard.mp hP
    obtain ⟨hQS,hQc⟩ := Finset.mem_powersetCard.mp hQ
    apply hne
    apply h.pred hA
    refine ⟨fun a ha => hS (hPS ha),fun a ha => hS (hQS ha),hPc,hQc,?_⟩
    dsimp [f] at ht
    omega
  have hb : T.offDiag.card ≤ (7*S.card)*(T.offDiag.image f).card := by
    apply Finset.card_le_mul_card_image T.offDiag (7*S.card)
    intro t ht
    obtain ⟨p,hp,hpt⟩ := Finset.mem_image.mp ht
    have htne : t ≠ 0 := hpt ▸ htnz p hp
    apply pair_difference_fiber_bound h hA S hS htne
    intro q hq
    obtain ⟨hqR,hqt⟩ := Finset.mem_filter.mp hq
    obtain ⟨hQ,hQ',hne⟩ := Finset.mem_offDiag.mp hqR
    obtain ⟨hQS,hQc⟩ := Finset.mem_powersetCard.mp hQ
    obtain ⟨hQ'S,hQ'c⟩ := Finset.mem_powersetCard.mp hQ'
    exact ⟨hQS,hQ'S,hQc,hQ'c,hqt⟩
  simpa only [Finset.offDiag_card,T,Finset.card_powersetCard,
    offDiagonalPairSumDifferences,f] using hb

lemma nonzero_pair_sum_difference_cubic_lower {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) (hSc : 4 ≤ S.card) :
    S.card^3 ≤ 224*(offDiagonalPairSumDifferences S).card := by
  let m := S.card
  let b := m.choose 2
  let d := (offDiagonalPairSumDifferences S).card
  have hm : 4 ≤ m := hSc
  have hchoose : 2*b = m*(m-1) := by
    have he := Nat.descFactorial_eq_factorial_mul_choose m 2
    norm_num [Nat.descFactorial_succ,b] at he ⊢
    nlinarith
  have hm1 : m-1+1=m := Nat.sub_add_cancel (by omega)
  have hb2 : 2 ≤ b := by nlinarith
  have hb1 : b-1+1=b := Nat.sub_add_cancel (by omega)
  have hsq : m^2 ≤ 4*b := by nlinarith
  have hsq' : m^2 ≤ 8*(b-1) := by nlinarith
  have hp := Nat.mul_le_mul hsq hsq'
  have hcount := nonzero_pair_sum_difference_count h hA S hS
  change b*b-b ≤ 7*m*d at hcount
  have hbmul : b*b-b+b=b*b := Nat.sub_add_cancel (by nlinarith)
  have hfour : m*m^3 ≤ m*(224*d) := by nlinarith
  exact le_of_mul_le_mul_left hfour (show 0 < m by omega)

lemma failure_yields_many_pair_sum_differences {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∃ M : ℕ, ∀ N ≥ M,
      η*(N : ℝ) ≤ (offDiagonalPairSumDifferences (initialSegment A N)).card := by
  obtain ⟨ε,hε,M,hM⟩ := (density_liminf_ne_zero_iff h).mp hf
  obtain ⟨B,hB⟩ := initialSegment_card_eventually_large hA 4
  refine ⟨ε^3/224,by positivity,max (max M B) 1,?_⟩
  intro N hN
  have hNpos : 0 < N := by omega
  have hroot : 0 < (N : ℝ)^(1/3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _
  have hlow : ε*(N : ℝ)^(1/3 : ℝ) ≤ (initialSegment A N).card := by
    rw [card_initialSegment]
    exact (le_div_iff₀ hroot).mp (hM N (by omega))
  have hcub := pow_le_pow_left₀ (by positivity : 0 ≤ ε*(N : ℝ)^(1/3 : ℝ)) hlow 3
  have he : ((N : ℝ)^(1/3 : ℝ))^3 = N := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  rw [mul_pow,he] at hcub
  have hbound := nonzero_pair_sum_difference_cubic_lower h hA (initialSegment A N)
    (fun x hx => (mem_initialSegment.mp hx).1) (hB N (by omega))
  have hbound' : ((initialSegment A N).card : ℝ)^3 ≤
      224*(offDiagonalPairSumDifferences (initialSegment A N)).card := by exact_mod_cast hbound
  nlinarith


lemma card_sq_le_bins_mul_collision_card {β : Type*} [DecidableEq β]
    (T : Finset β) (f : β → ℕ) (K : ℕ) (hf : ∀ x ∈ T, f x < K) :
    T.card^2 ≤ K * ((T ×ˢ T).filter (fun p => f p.1 = f p.2)).card := by
  classical
  let F := fun i => T.filter (fun x => f x = i)
  let R := (T ×ˢ T).filter (fun p => f p.1 = f p.2)
  have hT : T.card = ∑ i ∈ Finset.range K, (F i).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_range.mpr (hf x hx))
  have hR : R.card = ∑ i ∈ Finset.range K, (F i).card^2 := by
    have he := Finset.card_eq_sum_card_fiberwise
      (s := R) (t := Finset.range K) (f := fun p => f p.1) (by
        intro p hp
        exact Finset.mem_range.mpr (hf p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1))
    rw [he]
    apply Finset.sum_congr rfl
    intro i hi
    have heq : R.filter (fun p => f p.1 = i) = F i ×ˢ F i := by
      ext p
      simp only [R,F,Finset.mem_filter,Finset.mem_product]
      aesop
    rw [heq,Finset.card_product,pow_two]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range K)
    (fun _ => (1 : ℕ)) (fun i => (F i).card)
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_range,smul_eq_mul,
    mul_one,← hT,← hR] using hc

noncomputable def shortPairSumDifferences (S : Finset ℕ) (H : ℕ) : Finset ℤ :=
  (offDiagonalPairSumDifferences S).filter (fun d => -(H : ℤ) ≤ d ∧ d ≤ H)

lemma short_pair_sum_difference_count {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) (N H : ℕ)
    (hN : ∀ a ∈ S, a ≤ N) (hH : 0 < H) :
    (S.card.choose 2)^2 ≤ (2*N/H+1) *
      (S.card.choose 2 + 7*S.card*(shortPairSumDifferences S H).card) := by
  classical
  let T := S.powersetCard 2
  let σ := fun P : Finset ℕ => ∑ a ∈ P, a
  let f := fun P : Finset ℕ => σ P / H
  let R := (T ×ˢ T).filter (fun p => f p.1 = f p.2)
  let E := R.filter (fun p => p.1 = p.2)
  let D := R.filter (fun p => p.1 ≠ p.2)
  let g := fun p : Finset ℕ × Finset ℕ => (σ p.1 : ℤ) - σ p.2
  have hbound : ∀ P ∈ T, σ P ≤ 2*N := by
    intro P hP
    obtain ⟨hPS,hPc⟩ := Finset.mem_powersetCard.mp hP
    calc
      σ P ≤ ∑ _a ∈ P, N := Finset.sum_le_sum (fun a ha => hN a (hPS ha))
      _ = 2*N := by simp [hPc]
  have hf : ∀ P ∈ T, f P < 2*N/H+1 := by
    intro P hP
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (hbound P hP))
  have hc : T.card^2 ≤ (2*N/H+1)*R.card :=
    card_sq_le_bins_mul_collision_card T f _ hf
  have hE : E.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
    · intro p hp q hq he
      have hpq := (Finset.mem_filter.mp hp).2
      have hqq := (Finset.mem_filter.mp hq).2
      exact Prod.ext he (by simpa only [← hpq,← hqq] using he)
  have hDmem : ∀ p ∈ D, p.1 ⊆ S ∧ p.2 ⊆ S ∧
      p.1.card = 2 ∧ p.2.card = 2 ∧ p.1 ≠ p.2 := by
    intro p hp
    obtain ⟨hpR,hne⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpT,he⟩ := Finset.mem_filter.mp hpR
    obtain ⟨hP,hQ⟩ := Finset.mem_product.mp hpT
    obtain ⟨hPS,hPc⟩ := Finset.mem_powersetCard.mp hP
    obtain ⟨hQS,hQc⟩ := Finset.mem_powersetCard.mp hQ
    exact ⟨hPS,hQS,hPc,hQc,hne⟩
  have hgnz : ∀ p ∈ D, g p ≠ 0 := by
    intro p hp hg
    obtain ⟨hP,hQ,hPc,hQc,hne⟩ := hDmem p hp
    apply hne
    apply h.pred hA
    refine ⟨fun a ha => hS (hP ha),fun a ha => hS (hQ ha),hPc,hQc,?_⟩
    dsimp [g,σ] at hg
    omega
  have himage : D.image g ⊆ shortPairSumDifferences S H := by
    intro d hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hP,hQ,hPc,hQc,hne⟩ := hDmem p hp
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨p,Finset.mem_offDiag.mpr ⟨?_,?_,hne⟩,rfl⟩
      · exact Finset.mem_powersetCard.mpr ⟨hP,hPc⟩
      · exact Finset.mem_powersetCard.mpr ⟨hQ,hQc⟩
    · have he : σ p.1 / H = σ p.2 / H :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have h1 := Nat.mod_add_div (σ p.1) H
      have h2 := Nat.mod_add_div (σ p.2) H
      have hr1 := Nat.mod_lt (σ p.1) hH
      have hr2 := Nat.mod_lt (σ p.2) hH
      rw [he] at h1
      dsimp [g]
      omega
  have hD : D.card ≤ 7*S.card*(shortPairSumDifferences S H).card := by
    have hi : D.card ≤ (7*S.card)*(D.image g).card := by
      apply Finset.card_le_mul_card_image
      intro d hd
      obtain ⟨p,hp,hpd⟩ := Finset.mem_image.mp hd
      have hdnz : d ≠ 0 := hpd ▸ hgnz p hp
      apply pair_difference_fiber_bound h hA S hS hdnz
      intro q hq
      obtain ⟨hqD,hqd⟩ := Finset.mem_filter.mp hq
      obtain ⟨hQ,hQ',hQc,hQ'c,hne⟩ := hDmem q hqD
      exact ⟨hQ,hQ',hQc,hQ'c,hqd⟩
    exact hi.trans (Nat.mul_le_mul_left _ (Finset.card_le_card himage))
  have hpart : E.card+D.card=R.card :=
    Finset.card_filter_add_card_filter_not (s := R) (fun p => p.1 = p.2)
  have hR : R.card ≤ T.card+7*S.card*(shortPairSumDifferences S H).card := by omega
  have hh := hc.trans (Nat.mul_le_mul_left (2*N/H+1) hR)
  simpa only [T,Finset.card_powersetCard] using hh


lemma short_pair_sum_difference_linear_lower {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) {C t : ℕ}
    (hC : 0 < C) (ht : 0 < t) (hcard : S.card = 8*t)
    (hbound : ∀ a ∈ S, a ≤ 4096*C*t^3) :
    t ≤ 2*(shortPairSumDifferences S (4096*C*t)).card := by
  let b := S.card.choose 2
  let d := (shortPairSumDifferences S (4096*C*t)).card
  have hb : 2*b = (8*t)*(8*t-1) := by
    have he := Nat.descFactorial_eq_factorial_mul_choose S.card 2
    norm_num [Nat.descFactorial_succ,hcard,b] at he ⊢
    nlinarith
  have ht1 : 8*t-1+1=8*t := Nat.sub_add_cancel (by omega)
  have hbl : 16*t^2 ≤ b := by nlinarith
  have hbu : b ≤ 32*t^2 := by nlinarith
  have hH : 0 < 4096*C*t := by positivity
  have hdiv : 2*(4096*C*t^3)/(4096*C*t)+1 = 2*t^2+1 := by
    have he : 2*(4096*C*t^3) = (2*t^2)*(4096*C*t) := by ring
    rw [he,Nat.mul_div_left _ hH]
  have hc := short_pair_sum_difference_count h hA S hS (4096*C*t^3)
    (4096*C*t) hbound hH
  rw [hdiv] at hc
  change b^2 ≤ (2*t^2+1)*(b+7*S.card*d) at hc
  rw [hcard] at hc
  have hh : (16*t^2)^2 ≤ (3*t^2)*(32*t^2+56*t*d) := by
    calc
      (16*t^2)^2 ≤ b^2 := Nat.pow_le_pow_left hbl 2
      _ ≤ (2*t^2+1)*(b+7*(8*t)*d) := hc
      _ ≤ (3*t^2)*(32*t^2+56*t*d) := by
        apply Nat.mul_le_mul
        · nlinarith
        · nlinarith
  have hcanc : t^3*(160*t) ≤ t^3*(168*d) := by nlinarith only [hh]
  have hh' : 160*t ≤ 168*d := le_of_mul_le_mul_left hcanc (by positivity)
  change t ≤ 2*d
  omega

lemma cubic_sequence_remote_pair_differences {a : ℕ → ℕ} {C : ℕ}
    (hC : 0 < C) (ha : StrictMono a)
    (h : NtupleCondition (Set.range a) 3)
    (hbound : ∀ i, a i ≤ C*(i+1)^3) {t : ℕ} (ht : 0 < t) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ Set.range a ∧ S.card = 8*t ∧
      (∀ x ∈ S, t^3 ≤ x ∧ x ≤ 4096*C*t^3) ∧
      t ≤ 2*(shortPairSumDifferences S (4096*C*t)).card := by
  classical
  have hA : (Set.range a).Infinite := Set.infinite_range_of_injective ha.injective
  let S := (Finset.range (8*t)).image (fun i => a (8*t+i))
  have hS : (S : Set ℕ) ⊆ Set.range a := by
    intro x hx
    change x ∈ (Finset.range (8*t)).image (fun i => a (8*t+i)) at hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact Set.mem_range_self _
  have hcard : S.card = 8*t := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range _
    · intro i j he
      have he' := ha.injective he
      omega
  have hhigh : ∀ x ∈ S, x ≤ 4096*C*t^3 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hi' := Finset.mem_range.mp hi
    calc
      a (8*t+i) ≤ C*(8*t+i+1)^3 := hbound _
      _ ≤ C*(16*t)^3 := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 3)
      _ = 4096*C*t^3 := by ring
  have halow : t^3 ≤ a (8*t) := by
    let P := (Finset.range (8*t)).image (fun i => a (i+1))
    have hP : P ⊆ initialSegment (Set.range a) (a (8*t)) := by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      have hi' := Finset.mem_range.mp hi
      refine mem_initialSegment.mpr ⟨Set.mem_range_self _,?_,?_⟩
      · have hh : i+1 ≤ a (i+1) := ha.id_le (i+1)
        omega
      · exact ha.monotone (by omega)
    have hPc : P.card = 8*t := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro i j he
        have he' := ha.injective he
        omega
    have hcardlow := Finset.card_le_card hP
    rw [hPc] at hcardlow
    have hapos : 1 ≤ a (8*t) := by
      have hh : 8*t ≤ a (8*t) := ha.id_le (8*t)
      omega
    have hh := (Nat.pow_le_pow_left hcardlow 3).trans (initialSegment_cube_bound h hapos)
    nlinarith
  refine ⟨S,hS,hcard,?_,?_⟩
  · intro x hx
    refine ⟨?_,hhigh x hx⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact halow.trans (ha.monotone (by omega))
  · exact short_pair_sum_difference_linear_lower h hA S hS hC ht hcard hhigh


lemma failure_yields_remote_pair_differences {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite)
    (hf : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) ≠ 0) :
    ∃ C : ℕ, 0 < C ∧ ∀ t : ℕ, 0 < t →
      ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ S.card = 8*t ∧
        (∀ x ∈ S, t^3 ≤ x ∧ x ≤ 4096*C*t^3) ∧
        t ≤ 2*(shortPairSumDifferences S (4096*C*t)).card := by
  obtain ⟨a,C,hC,ha,haA,hbound⟩ := failure_yields_cubic_enumeration h hA hf
  have hcond : NtupleCondition (Set.range a) 3 := haA.symm ▸ h
  refine ⟨C,hC,fun t ht => ?_⟩
  obtain ⟨S,hS,hSc,hSb,hSd⟩ :=
    cubic_sequence_remote_pair_differences hC ha hcond hbound ht
  exact ⟨S,haA ▸ hS,hSc,hSb,hSd⟩


/--
Let `A ⊆ ℕ` be an infinite set such that the triple sums `a + b + c` are all distinct for
`a, b, c` in `A` (aside from the trivial coincidences). Is it true that
`liminf n → ∞ |A ∩ {1, …, N}| / N^(1/3) = 0`?
-/
theorem erdos_41 (A : Set ℕ) (h_triple : NtupleCondition A 3) (h_infinite : A.Infinite) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 := by
  sorry

end Erdos41
