import FormalConjectures.Util.ProblemImports

open scoped Real

/--
A364173: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))


/- Flattened helper code from TempProductExpansion.lean -/

open scoped BigOperators

namespace TempProductExpansion

lemma prod_eq_zero_of_three_le_card
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    {s t : Finset ι} {y : ι → R}
    (hsub : t ⊆ s) (hcard : 3 ≤ t.card)
    (h3 : ∀ a b c, a ∈ s → b ∈ s → c ∈ s →
      a ≠ b → a ≠ c → b ≠ c → y a * y b * y c = 0) :
    ∏ i ∈ t, y i = 0 := by
  obtain ⟨u, hut, hucard⟩ := Finset.exists_subset_card_eq hcard
  rw [← Finset.prod_sdiff hut]
  suffices ∏ i ∈ u, y i = 0 by simp [this]
  rcases Finset.card_eq_three.mp hucard with ⟨a, b, c, hab, hac, hbc, rfl⟩
  have ha : a ∈ s := hsub (hut (by simp))
  have hb : b ∈ s := hsub (hut (by simp))
  have hc : c ∈ s := hsub (hut (by simp))
  simpa [hab, hac, hbc, mul_assoc] using h3 a b c ha hb hc hab hac hbc

theorem prod_one_add_eq_truncated_of_triple_zero
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (y : ι → R)
    (h3 : ∀ a b c, a ∈ s → b ∈ s → c ∈ s →
      a ≠ b → a ≠ c → b ≠ c → y a * y b * y c = 0) :
    ∏ i ∈ s, (1 + y i) =
      1 + ∑ i ∈ s, y i + ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i := by
  let F : ℕ → R := fun j => ∑ t ∈ s.powersetCard j, ∏ i ∈ t, y i
  have hzero_ge_three : ∀ j, 3 ≤ j → F j = 0 := by
    intro j hj
    dsimp [F]
    refine Finset.sum_eq_zero fun t ht => ?_
    exact prod_eq_zero_of_three_le_card (Finset.mem_powersetCard.mp ht).1
      (by simpa [Finset.mem_powersetCard.mp ht] using hj) h3
  have hzero_gt_card : ∀ j, s.card < j → F j = 0 := by
    intro j hj
    dsimp [F]
    have hp : s.powersetCard j = ∅ := by
      rw [Finset.powersetCard_eq_empty]
      exact hj
    simp [hp]
  have hrange : (∑ j ∈ Finset.range (s.card + 1), F j) = ∑ j ∈ Finset.range 3, F j := by
    let u := Finset.range (s.card + 1) ∪ Finset.range 3
    have h₁ : (∑ j ∈ Finset.range (s.card + 1), F j) = ∑ j ∈ u, F j := by
      refine Finset.sum_subset (by intro x hx; exact Finset.mem_union_left _ hx) ?_
      intro x hx hxrange
      have hx3 : x ∈ Finset.range 3 := by
        simpa [u, hxrange] using hx
      exact hzero_gt_card x (by
        rw [Finset.mem_range] at hxrange hx3
        exact Nat.lt_of_succ_le (not_lt.mp hxrange))
    have h₂ : (∑ j ∈ Finset.range 3, F j) = ∑ j ∈ u, F j := by
      refine Finset.sum_subset (by intro x hx; exact Finset.mem_union_right _ hx) ?_
      intro x hx hxrange3
      have hxorig : x ∈ Finset.range (s.card + 1) := by
        simpa [u, hxrange3] using hx
      exact hzero_ge_three x (by
        rw [Finset.mem_range] at hxrange3
        exact not_lt.mp hxrange3)
    exact h₁.trans h₂.symm
  have hF0 : F 0 = 1 := by
    dsimp [F]
    simp
  have hF1 : F 1 = ∑ i ∈ s, y i := by
    dsimp [F]
    rw [Finset.powersetCard_one]
    simp
  calc
    ∏ i ∈ s, (1 + y i) = ∑ t ∈ s.powerset, ∏ i ∈ t, y i := Finset.prod_one_add s
    _ = ∑ j ∈ Finset.range (s.card + 1), F j := by
      dsimp [F]
      exact Finset.sum_powerset s (fun t => ∏ i ∈ t, y i)
    _ = ∑ j ∈ Finset.range 3, F j := hrange
    _ = F 0 + F 1 + F 2 := by norm_num [Finset.sum_range_succ]
    _ = 1 + ∑ i ∈ s, y i + ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i := by
      dsimp [F] at hF0 hF1 ⊢
      rw [hF0, hF1]


theorem prod_one_add_eq_truncated_of_cube_zero
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (P : R) (z : ι → R) (hP : P ^ 3 = 0) :
    ∏ i ∈ s, (1 + P * z i) =
      1 + ∑ i ∈ s, P * z i + ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, P * z i := by
  apply prod_one_add_eq_truncated_of_triple_zero
  intro a b c _ha _hb _hc _hab _hac _hbc
  calc
    (P * z a) * (P * z b) * (P * z c) = P ^ 3 * (z a * z b * z c) := by ring
    _ = 0 := by simp [hP]



end TempProductExpansion


/- Flattened helper code from TempPairInvSum.lean -/

open scoped BigOperators

namespace TempPairInvSum

lemma elemSymTwo_insert
    {α R : Type*} [DecidableEq α] [CommRing R]
    (a : α) (s : Finset α) (ha : a ∉ s) (y : α → R) :
    (∑ t ∈ (insert a s).powersetCard 2, ∏ i ∈ t, y i) =
      (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i) + y a * (∑ i ∈ s, y i) := by
  rw [show (2:ℕ) = Nat.succ 1 by norm_num, Finset.powersetCard_succ_insert ha 1]
  rw [Finset.sum_union]
  · congr 1
    rw [Finset.powersetCard_one]
    rw [Finset.sum_image]
    · rw [Finset.sum_map]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hba : b ≠ a := by
        intro h; subst h; exact ha hb
      rw [Finset.prod_insert]
      · simp
      · simpa [eq_comm] using hba
    · intro u hu v hv huv
      rcases Finset.mem_map.mp hu with ⟨b, hb, rfl⟩
      rcases Finset.mem_map.mp hv with ⟨c, hc, rfl⟩
      have hab : a ≠ b := by intro h; subst h; exact ha hb
      have hac : a ≠ c := by intro h; subst h; exact ha hc
      have h₁ : a ∉ ({b} : Finset α) := by simp [hab]
      have h₂ : a ∉ ({c} : Finset α) := by simp [hac]
      have h := congrArg (fun T : Finset α => T.erase a) huv
      change (insert a ({b} : Finset α)).erase a = (insert a ({c} : Finset α)).erase a at h
      rw [Finset.erase_insert h₁, Finset.erase_insert h₂] at h
      change ({b} : Finset α) = ({c} : Finset α)
      exact h
  · rw [Finset.disjoint_left]
    intro t ht him
    rcases Finset.mem_image.mp him with ⟨u, hu, rfl⟩
    have hsub : insert a u ⊆ s := (Finset.mem_powersetCard.mp ht).1
    exact ha (hsub (Finset.mem_insert_self a u))

lemma elemSymTwo_square_identity
    {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (y : α → R) :
    (∑ i ∈ s, y i)^2 =
      (∑ i ∈ s, (y i)^2) +
        (2 : R) * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i) := by
  refine Finset.induction_on s ?empty ?insert
  · have h : (∅ : Finset α).powersetCard 2 = ∅ := by
      rw [Finset.powersetCard_eq_empty]
      norm_num
    simp [h]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, elemSymTwo_insert a s ha y]
    calc
      (y a + ∑ x ∈ s, y x) ^ 2
          = y a ^ 2 + 2 * y a * (∑ x ∈ s, y x) + (∑ x ∈ s, y x) ^ 2 := by ring
      _ = y a ^ 2 + 2 * y a * (∑ x ∈ s, y x) +
            ((∑ x ∈ s, y x ^ 2) + 2 * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i) := by rw [ih]
      _ = y a ^ 2 + ∑ x ∈ s, y x ^ 2 +
            2 * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i + y a * ∑ i ∈ s, y i) := by ring

lemma elemSymTwo_eq_zero_of_sum_and_sum_sq_zero
    {α R : Type*} [DecidableEq α] [CommRing R] [NoZeroDivisors R]
    (s : Finset α) (y : α → R)
    (h2 : (2 : R) ≠ 0)
    (hsum : (∑ i ∈ s, y i) = 0)
    (hsq : (∑ i ∈ s, (y i)^2) = 0) :
    (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i) = 0 := by
  have h := elemSymTwo_square_identity s y
  rw [hsum, zero_pow (by norm_num : (2:ℕ) ≠ 0), hsq, zero_add] at h
  exact (mul_eq_zero.mp h.symm).resolve_left h2

lemma zmod_units_sum_pow_eq_zero {p k : ℕ} [NeZero p] (hp : Nat.Prime p) (hk0 : k ≠ 0)
    (hklt : k < p - 1) :
    (∑ x : (ZMod p)ˣ, ((x : (ZMod p)ˣ) : ZMod p) ^ k) = 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h := FiniteField.sum_pow_units (K := ZMod p) k
  rw [h]
  rw [ZMod.card]
  have hndvd : ¬ p - 1 ∣ k := by
    exact fun hd => Nat.not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hd) hklt
  simp [hndvd]

noncomputable def IcoOnePEquivUnits (p : ℕ) (hp : Nat.Prime p) :
    {i : ℕ // i ∈ Finset.Ico 1 p} ≃ (ZMod p)ˣ where
  toFun i := by
    have hi0 : ¬ p ∣ i.1 := by
      intro hd
      have hlt : i.1 < p := (Finset.mem_Ico.mp i.2).2
      have hpos : 0 < i.1 := lt_of_lt_of_le zero_lt_one (Finset.mem_Ico.mp i.2).1
      exact Nat.not_lt_of_ge (Nat.le_of_dvd hpos hd) hlt
    exact ZMod.unitOfCoprime i.1 (((hp.coprime_iff_not_dvd).2 hi0).symm)
  invFun u := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    refine ⟨(u : ZMod p).val, ?_⟩
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.succ_le_of_lt (ZMod.val_pos.mpr (Units.ne_zero u))
    · exact ZMod.val_lt (u : ZMod p)
  left_inv i := by
    apply Subtype.ext
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    simp [ZMod.unitOfCoprime]
    exact Nat.mod_eq_of_lt (Finset.mem_Ico.mp i.2).2
  right_inv u := by
    ext
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    change ((ZMod.unitOfCoprime (u : ZMod p).val _ : (ZMod p)ˣ) : ZMod p) = (u : ZMod p)
    exact ZMod.natCast_zmod_val (u : ZMod p)

lemma zmod_units_sum_eq_zero {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ x : (ZMod p)ˣ, ((x : (ZMod p)ˣ) : ZMod p)) = 0 := by
  simpa using zmod_units_sum_pow_eq_zero (p := p) (k := 1) hp (by norm_num) (by omega)

lemma zmod_units_sum_sq_eq_zero {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ x : (ZMod p)ˣ, ((x : (ZMod p)ˣ) : ZMod p) ^ 2) = 0 := by
  simpa using zmod_units_sum_pow_eq_zero (p := p) (k := 2) hp (by norm_num) (by omega)

lemma zmod_units_sum_inv_eq_zero {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ x : (ZMod p)ˣ, (((x : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)) = 0 := by
  have hperm : (∑ x : (ZMod p)ˣ, (((x : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)) =
      (∑ x : (ZMod p)ˣ, ((x : (ZMod p)ˣ) : ZMod p)) := by
    exact Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ)
      (fun x => (((x : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p))
      (fun x => ((x : (ZMod p)ˣ) : ZMod p)) (by intro x; simp)
  rw [hperm, zmod_units_sum_eq_zero hp hp5]

lemma zmod_units_sum_inv_sq_eq_zero {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ x : (ZMod p)ˣ, (((x : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 2) = 0 := by
  have hperm : (∑ x : (ZMod p)ˣ, (((x : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 2) =
      (∑ x : (ZMod p)ˣ, ((x : (ZMod p)ˣ) : ZMod p) ^ 2) := by
    exact Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ)
      (fun x => (((x : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 2)
      (fun x => ((x : (ZMod p)ˣ) : ZMod p) ^ 2) (by intro x; simp)
  rw [hperm, zmod_units_sum_sq_eq_zero hp hp5]

lemma zmod_sum_Ico_inv_mod_p_zero {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹)) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Finset.sum_subtype (Finset.Ico 1 p) (by intro x; rfl) (fun i => ((i : ZMod p)⁻¹))]
  let e := IcoOnePEquivUnits p hp
  calc
    (∑ a : { i // i ∈ Finset.Ico 1 p}, ((a : ℕ) : ZMod p)⁻¹)
        = ∑ u : (ZMod p)ˣ, ((((u : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)) := by
          exact Fintype.sum_equiv e (fun a : { i // i ∈ Finset.Ico 1 p} => (((a : ℕ) : ZMod p)⁻¹))
            (fun u : (ZMod p)ˣ => ((((u : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p))) (by
              intro a
              change (((a : ℕ) : ZMod p)⁻¹) = ((((e a)⁻¹ : (ZMod p)ˣ) : ZMod p))
              have hea : ((e a : (ZMod p)ˣ) : ZMod p) = ((a : ℕ) : ZMod p) := by
                simp [e, IcoOnePEquivUnits, ZMod.unitOfCoprime]
              rw [← ZMod.inv_coe_unit (e a)]
              rw [hea])
    _ = 0 := zmod_units_sum_inv_eq_zero hp hp5

lemma zmod_sum_Ico_inv_sq_mod_p_zero {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹)^2) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Finset.sum_subtype (Finset.Ico 1 p) (by intro x; rfl) (fun i => ((i : ZMod p)⁻¹)^2)]
  let e := IcoOnePEquivUnits p hp
  calc
    (∑ a : { i // i ∈ Finset.Ico 1 p}, ((a : ℕ) : ZMod p)⁻¹ ^ 2)
        = ∑ u : (ZMod p)ˣ, ((((u : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 2) := by
          exact Fintype.sum_equiv e (fun a : { i // i ∈ Finset.Ico 1 p} => (((a : ℕ) : ZMod p)⁻¹)^2)
            (fun u : (ZMod p)ˣ => ((((u : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)^2)) (by
              intro a
              change (((a : ℕ) : ZMod p)⁻¹)^2 = ((((e a)⁻¹ : (ZMod p)ˣ) : ZMod p)^2)
              have hea : ((e a : (ZMod p)ˣ) : ZMod p) = ((a : ℕ) : ZMod p) := by
                simp [e, IcoOnePEquivUnits, ZMod.unitOfCoprime]
              rw [← ZMod.inv_coe_unit (e a)]
              rw [hea])
    _ = 0 := zmod_units_sum_inv_sq_eq_zero hp hp5

/-- The requested statement. -/
theorem zmod_pair_inv_sum_eq_zero {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ t ∈ (Finset.Ico 1 p).powersetCard 2, ∏ i ∈ t, ((i : ZMod p)⁻¹)) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    omega
  exact elemSymTwo_eq_zero_of_sum_and_sum_sq_zero (s := Finset.Ico 1 p)
    (y := fun i : ℕ => ((i : ZMod p)⁻¹)) h2
    (zmod_sum_Ico_inv_mod_p_zero hp hp5)
    (zmod_sum_Ico_inv_sq_mod_p_zero hp hp5)

end TempPairInvSum


/- Flattened helper code from TempGeneralHarmonic.lean -/

open scoped BigOperators

namespace TempShiftedProductGeneralHarmonic

/-- The finite set of positive representatives less than `p^r` and prime to `p`. -/
def unitRange (p r : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (p^r)).filter (fun i => ¬ p ∣ i)

lemma elemSymTwo_insert
    {α R : Type*} [DecidableEq α] [CommRing R]
    (a : α) (s : Finset α) (ha : a ∉ s) (y : α → R) :
    (∑ t ∈ (insert a s).powersetCard 2, ∏ i ∈ t, y i) =
      (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i) + y a * (∑ i ∈ s, y i) := by
  rw [show (2:ℕ) = Nat.succ 1 by norm_num, Finset.powersetCard_succ_insert ha 1]
  rw [Finset.sum_union]
  · congr 1
    rw [Finset.powersetCard_one]
    rw [Finset.sum_image]
    · rw [Finset.sum_map]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hba : b ≠ a := by
        intro h; subst h; exact ha hb
      rw [Finset.prod_insert]
      · simp
      · simpa [eq_comm] using hba
    · intro u hu v hv huv
      rcases Finset.mem_map.mp hu with ⟨b, hb, rfl⟩
      rcases Finset.mem_map.mp hv with ⟨c, hc, rfl⟩
      have hab : a ≠ b := by intro h; subst h; exact ha hb
      have hac : a ≠ c := by intro h; subst h; exact ha hc
      have h₁ : a ∉ ({b} : Finset α) := by simp [hab]
      have h₂ : a ∉ ({c} : Finset α) := by simp [hac]
      have h := congrArg (fun T : Finset α => T.erase a) huv
      change (insert a ({b} : Finset α)).erase a = (insert a ({c} : Finset α)).erase a at h
      rw [Finset.erase_insert h₁, Finset.erase_insert h₂] at h
      change ({b} : Finset α) = ({c} : Finset α)
      exact h
  · rw [Finset.disjoint_left]
    intro t ht him
    rcases Finset.mem_image.mp him with ⟨u, hu, rfl⟩
    have hsub : insert a u ⊆ s := (Finset.mem_powersetCard.mp ht).1
    exact ha (hsub (Finset.mem_insert_self a u))

lemma elemSymTwo_square_identity
    {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (y : α → R) :
    (∑ i ∈ s, y i)^2 =
      (∑ i ∈ s, (y i)^2) +
        (2 : R) * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i) := by
  refine Finset.induction_on s ?empty ?insert
  · have h : (∅ : Finset α).powersetCard 2 = ∅ := by
      rw [Finset.powersetCard_eq_empty]
      norm_num
    simp [h]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, elemSymTwo_insert a s ha y]
    calc
      (y a + ∑ x ∈ s, y x) ^ 2
          = y a ^ 2 + 2 * y a * (∑ x ∈ s, y x) + (∑ x ∈ s, y x) ^ 2 := by ring
      _ = y a ^ 2 + 2 * y a * (∑ x ∈ s, y x) +
            ((∑ x ∈ s, y x ^ 2) + 2 * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i) := by rw [ih]
      _ = y a ^ 2 + ∑ x ∈ s, y x ^ 2 +
            2 * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i + y a * ∑ i ∈ s, y i) := by ring

lemma elemSymTwo_eq_zero_of_sum_and_sum_sq_zero_of_two_unit
    {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (y : α → R)
    (h2 : IsUnit (2 : R))
    (hsum : (∑ i ∈ s, y i) = 0)
    (hsq : (∑ i ∈ s, (y i)^2) = 0) :
    (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i) = 0 := by
  have h := elemSymTwo_square_identity s y
  rw [hsum, zero_pow (by norm_num : (2:ℕ) ≠ 0), hsq, zero_add] at h
  exact (IsUnit.mul_right_eq_zero h2).mp h.symm

lemma pow_pos_of_prime {p r : ℕ} (hp : Nat.Prime p) : 0 < p ^ r :=
  pow_pos hp.pos r

lemma pow_ne_zero_of_prime {p r : ℕ} (hp : Nat.Prime p) : p ^ r ≠ 0 :=
  ne_of_gt (pow_pos_of_prime (p := p) (r := r) hp)

lemma not_dvd_two_of_five_le {p : ℕ} (hp5 : 5 ≤ p) : ¬ p ∣ 2 := by
  intro h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) h
  omega

lemma not_dvd_three_of_five_le {p : ℕ} (hp5 : 5 ≤ p) : ¬ p ∣ 3 := by
  intro h
  have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num : 0 < 3) h
  omega

lemma one_lt_pow_of_prime_pos {p r : ℕ} (hp : Nat.Prime p) (hr : 0 < r) : 1 < p ^ r := by
  have hp2 : 2 ≤ p := hp.two_le
  have hle : p ≤ p ^ r := le_self_pow (by omega : 1 ≤ p) hr.ne'
  omega


lemma prime_dvd_pow_self_of_pos (p r : ℕ) (hr : 0 < r) : p ∣ p ^ r := by
  cases r with
  | zero => omega
  | succ k =>
      use p^k
      rw [pow_succ]
      exact Nat.mul_comm (p^k) p


noncomputable def unitRangeEquivUnits (p r : ℕ) (hp : Nat.Prime p) (hr : 0 < r) :
    {i : ℕ // i ∈ unitRange p r} ≃ (ZMod (p^r))ˣ where
  toFun i := by
    have hnot : ¬ p ∣ i.1 := (Finset.mem_filter.mp i.2).2
    exact ZMod.unitOfCoprime i.1 (hp.coprime_pow_of_not_dvd hnot)
  invFun u := by
    haveI : NeZero (p^r) := ⟨pow_ne_zero_of_prime (p := p) (r := r) hp⟩
    haveI : Fact (1 < p^r) := ⟨one_lt_pow_of_prime_pos (p := p) (r := r) hp hr⟩
    refine ⟨(u : ZMod (p^r)).val, ?_⟩
    rw [unitRange, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · constructor
      · exact Nat.succ_le_of_lt (ZMod.val_pos.mpr (Units.ne_zero u))
      · exact ZMod.val_lt (u : ZMod (p^r))
    · have hunit : IsUnit (((u : ZMod (p^r)).val : ℕ) : ZMod (p^r)) := by
        rw [ZMod.natCast_zmod_val]
        exact u.isUnit
      have hcop : Nat.Coprime ((u : ZMod (p^r)).val) (p^r) :=
        (ZMod.isUnit_iff_coprime ((u : ZMod (p^r)).val) (p^r)).mp hunit
      have hcop_p : Nat.Coprime ((u : ZMod (p^r)).val) p :=
        (Nat.coprime_pow_right_iff hr ((u : ZMod (p^r)).val) p).mp hcop
      exact (hp.coprime_iff_not_dvd).mp hcop_p.symm
  left_inv i := by
    apply Subtype.ext
    haveI : NeZero (p^r) := ⟨pow_ne_zero_of_prime (p := p) (r := r) hp⟩
    simp [ZMod.unitOfCoprime]
    exact Nat.mod_eq_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp i.2).1).2
  right_inv u := by
    ext
    haveI : NeZero (p^r) := ⟨pow_ne_zero_of_prime (p := p) (r := r) hp⟩
    change ((ZMod.unitOfCoprime (u : ZMod (p^r)).val _ : (ZMod (p^r))ˣ) : ZMod (p^r)) = (u : ZMod (p^r))
    exact ZMod.natCast_zmod_val (u : ZMod (p^r))

lemma zmod_two_unit_pow {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    IsUnit (2 : ZMod (p^r)) := by
  exact (ZMod.unitOfCoprime 2 (hp.coprime_pow_of_not_dvd (not_dvd_two_of_five_le hp5))).isUnit

lemma zmod_three_unit_pow {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    IsUnit (3 : ZMod (p^r)) := by
  exact (ZMod.unitOfCoprime 3 (hp.coprime_pow_of_not_dvd (not_dvd_three_of_five_le hp5))).isUnit

lemma zmod_units_sum_eq_zero_pow {p r : ℕ} [NeZero (p^r)] [Fintype (ZMod (p^r))]
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ x : (ZMod (p^r))ˣ, ((x : (ZMod (p^r))ˣ) : ZMod (p^r))) = 0 := by
  let R := ZMod (p^r)
  let a : Rˣ := ZMod.unitOfCoprime 2 (hp.coprime_pow_of_not_dvd (not_dvd_two_of_five_le hp5))
  let S : R := ∑ x : Rˣ, ((x : Rˣ) : R)
  have hperm : (∑ x : Rˣ, (((a * x : Rˣ) : R))) = S := by
    dsimp [S]
    exact Fintype.sum_equiv (Equiv.mulLeft a)
      (fun x : Rˣ => (((a * x : Rˣ) : R)))
      (fun x : Rˣ => ((x : Rˣ) : R)) (by intro x; rfl)
  have hmul : ((a : R) - 1) * S = 0 := by
    have hcalc : (a : R) * S = S := by
      calc
        (a : R) * S = ∑ x : Rˣ, (a : R) * ((x : Rˣ) : R) := by rw [Finset.mul_sum]
        _ = ∑ x : Rˣ, (((a * x : Rˣ) : R)) := by simp
        _ = S := hperm
    calc
      ((a : R) - 1) * S = (a : R) * S - S := by ring
      _ = 0 := by rw [hcalc, sub_self]
  have ha1 : ((a : R) - 1) = (1 : R) := by
    dsimp [a]
    norm_num
  change S = 0
  simpa [ha1] using hmul

lemma zmod_units_sum_sq_eq_zero_pow {p r : ℕ} [NeZero (p^r)] [Fintype (ZMod (p^r))]
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ x : (ZMod (p^r))ˣ, ((x : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 2) = 0 := by
  let R := ZMod (p^r)
  let a : Rˣ := ZMod.unitOfCoprime 2 (hp.coprime_pow_of_not_dvd (not_dvd_two_of_five_le hp5))
  let S : R := ∑ x : Rˣ, ((x : Rˣ) : R) ^ 2
  have hperm : (∑ x : Rˣ, (((a * x : Rˣ) : R)) ^ 2) = S := by
    dsimp [S]
    exact Fintype.sum_equiv (Equiv.mulLeft a)
      (fun x : Rˣ => (((a * x : Rˣ) : R)) ^ 2)
      (fun x : Rˣ => ((x : Rˣ) : R) ^ 2) (by intro x; rfl)
  have hmul : (((a : R)^2) - 1) * S = 0 := by
    have hcalc : ((a : R)^2) * S = S := by
      calc
        ((a : R)^2) * S = ∑ x : Rˣ, ((a : R)^2) * (((x : Rˣ) : R) ^ 2) := by rw [Finset.mul_sum]
        _ = ∑ x : Rˣ, (((a * x : Rˣ) : R)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
        _ = S := hperm
    calc
      (((a : R)^2) - 1) * S = ((a : R)^2) * S - S := by ring
      _ = 0 := by rw [hcalc, sub_self]
  have ha : (((a : R)^2) - 1) = (3 : R) := by
    dsimp [a]
    norm_num
  have h3 : IsUnit ((((a : R)^2) - 1)) := by
    rw [ha]
    exact zmod_three_unit_pow hp hp5
  change S = 0
  exact (IsUnit.mul_right_eq_zero h3).mp hmul

lemma zmod_units_sum_inv_eq_zero_pow {p r : ℕ} [NeZero (p^r)] [Fintype (ZMod (p^r))]
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ x : (ZMod (p^r))ˣ, (((x : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))) = 0 := by
  have hperm : (∑ x : (ZMod (p^r))ˣ, (((x : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))) =
      (∑ x : (ZMod (p^r))ˣ, ((x : (ZMod (p^r))ˣ) : ZMod (p^r))) := by
    exact Fintype.sum_equiv (Equiv.inv (ZMod (p^r))ˣ)
      (fun x => (((x : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)))
      (fun x => ((x : (ZMod (p^r))ˣ) : ZMod (p^r))) (by intro x; simp)
  rw [hperm, zmod_units_sum_eq_zero_pow hp hp5]

lemma zmod_units_sum_inv_sq_eq_zero_pow {p r : ℕ} [NeZero (p^r)] [Fintype (ZMod (p^r))]
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ x : (ZMod (p^r))ˣ, (((x : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 2) = 0 := by
  have hperm : (∑ x : (ZMod (p^r))ˣ, (((x : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 2) =
      (∑ x : (ZMod (p^r))ˣ, ((x : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 2) := by
    exact Fintype.sum_equiv (Equiv.inv (ZMod (p^r))ˣ)
      (fun x => (((x : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 2)
      (fun x => ((x : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 2) (by intro x; simp)
  rw [hperm, zmod_units_sum_sq_eq_zero_pow hp hp5]

/-- In `ZMod (p^r)`, the inverse-square harmonic sum over `unitRange p r` is zero. -/
theorem zmod_unitRange_inv_sq_sum_zero {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∑ i ∈ unitRange p r, ((i : ZMod (p^r))⁻¹)^2) = 0 := by
  haveI : NeZero (p^r) := ⟨pow_ne_zero_of_prime (p := p) (r := r) hp⟩
  haveI : Fintype (ZMod (p^r)) := ZMod.fintype (p^r)
  rw [Finset.sum_subtype (unitRange p r) (by intro x; rfl) (fun i => ((i : ZMod (p^r))⁻¹)^2)]
  let e := unitRangeEquivUnits p r hp hr
  calc
    (∑ a : { i // i ∈ unitRange p r}, ((a : ℕ) : ZMod (p^r))⁻¹ ^ 2)
        = ∑ u : (ZMod (p^r))ˣ, ((((u : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 2) := by
          exact Fintype.sum_equiv e
            (fun a : { i // i ∈ unitRange p r} => (((a : ℕ) : ZMod (p^r))⁻¹)^2)
            (fun u : (ZMod (p^r))ˣ => ((((u : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2)) (by
              intro a
              change (((a : ℕ) : ZMod (p^r))⁻¹)^2 = ((((e a)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2)
              have hea : ((e a : (ZMod (p^r))ˣ) : ZMod (p^r)) = ((a : ℕ) : ZMod (p^r)) := by
                simp [e, unitRangeEquivUnits, ZMod.unitOfCoprime]
              rw [← ZMod.inv_coe_unit (e a)]
              rw [hea])
    _ = 0 := zmod_units_sum_inv_sq_eq_zero_pow hp hp5

/-- In `ZMod (p^r)`, the inverse harmonic sum over `unitRange p r` is zero. -/
theorem zmod_unitRange_inv_sum_zero_mod_pr {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∑ i ∈ unitRange p r, ((i : ZMod (p^r))⁻¹)) = 0 := by
  haveI : NeZero (p^r) := ⟨pow_ne_zero_of_prime (p := p) (r := r) hp⟩
  haveI : Fintype (ZMod (p^r)) := ZMod.fintype (p^r)
  rw [Finset.sum_subtype (unitRange p r) (by intro x; rfl) (fun i => ((i : ZMod (p^r))⁻¹))]
  let e := unitRangeEquivUnits p r hp hr
  calc
    (∑ a : { i // i ∈ unitRange p r}, ((a : ℕ) : ZMod (p^r))⁻¹)
        = ∑ u : (ZMod (p^r))ˣ, ((((u : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))) := by
          exact Fintype.sum_equiv e
            (fun a : { i // i ∈ unitRange p r} => (((a : ℕ) : ZMod (p^r))⁻¹))
            (fun u : (ZMod (p^r))ˣ => ((((u : (ZMod (p^r))ˣ)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)))) (by
              intro a
              change (((a : ℕ) : ZMod (p^r))⁻¹) = ((((e a)⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)))
              have hea : ((e a : (ZMod (p^r))ˣ) : ZMod (p^r)) = ((a : ℕ) : ZMod (p^r)) := by
                simp [e, unitRangeEquivUnits, ZMod.unitOfCoprime]
              rw [← ZMod.inv_coe_unit (e a)]
              rw [hea])
    _ = 0 := zmod_units_sum_inv_eq_zero_pow hp hp5

/-- Elementary symmetric pair inverse sum in `ZMod (p^r)` is zero. -/
theorem zmod_unitRange_pair_inv_sum_zero {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∑ t ∈ (unitRange p r).powersetCard 2, ∏ i ∈ t, ((i : ZMod (p^r))⁻¹)) = 0 := by
  exact elemSymTwo_eq_zero_of_sum_and_sum_sq_zero_of_two_unit (s := unitRange p r)
    (y := fun i : ℕ => ((i : ZMod (p^r))⁻¹))
    (zmod_two_unit_pow hp hp5)
    (zmod_unitRange_inv_sum_zero_mod_pr hp hp5 hr)
    (zmod_unitRange_inv_sq_sum_zero hp hp5 hr)

lemma zmod_square_base_mul_zero_of_cast_zero {m : ℕ} [NeZero m]
    (x : ZMod (m^2))
    (hx : ZMod.castHom (show m ∣ m^2 by rw [pow_two]; exact dvd_mul_right m m) (ZMod m) x = 0) :
    (m : ZMod (m^2)) * x = 0 := by
  haveI : NeZero (m^2) := ⟨pow_ne_zero 2 (NeZero.ne m)⟩
  have hxval : ((x.val : ℕ) : ZMod m) = 0 := by
    rw [← ZMod.natCast_zmod_val x] at hx
    simpa using hx
  have hdvd_nat : m ∣ x.val := by
    rw [← Nat.modEq_zero_iff_dvd]
    rw [← ZMod.natCast_eq_natCast_iff (x.val) 0 m]
    simpa using hxval
  obtain ⟨t, ht⟩ := hdvd_nat
  rw [← ZMod.natCast_zmod_val x]
  rw [← Nat.cast_mul]
  rw [ht]
  rw [show m * (m * t) = m^2 * t by ring]
  rw [Nat.cast_mul, CharP.cast_eq_zero, zero_mul]

lemma zmod_map_inv_nat_of_coprime {m i : ℕ} [NeZero m] (hcop : Nat.Coprime i m) :
    ZMod.castHom (show m ∣ m^2 by rw [pow_two]; exact dvd_mul_right m m) (ZMod m)
      (((i : ZMod (m^2))⁻¹)) = ((i : ZMod m)⁻¹) := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  have hunit2 : IsUnit (i : ZMod (m^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hcop.pow_right 2
  have hmul2 : (i : ZMod (m^2)) * ((i : ZMod (m^2))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hunit2
  have hmap := congrArg (ZMod.castHom (show m ∣ m^2 by rw [pow_two]; exact dvd_mul_right m m) (ZMod m)) hmul2
  simp only [map_mul, map_one] at hmap
  simpa using hmap

lemma zmod_base_square_zero (m : ℕ) : ((m : ZMod (m^2)) ^ 2) = 0 := by
  rw [← Nat.cast_pow]
  exact CharP.cast_eq_zero (ZMod (m^2)) (m^2)

lemma zmod_inv_add_square_zero {n : ℕ} (u : (ZMod n)ˣ) {e : ZMod n} (he : e ^ 2 = 0) :
    ((u : ZMod n) + e)⁻¹ = ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (1 - e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) := by
  apply ZMod.inv_eq_of_mul_eq_one
  have hu : (u : ZMod n) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by simp
  have hsq : (e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 2 = 0 := by
    rw [show (e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 2 = e^2 * (((u⁻¹ : (ZMod n)ˣ) : ZMod n)^2) by ring]
    rw [he, zero_mul]
  calc
    ((u : ZMod n) + e) * (((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (1 - e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)))
        = ((u : ZMod n) + e) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (1 - e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) := by ring
    _ = (1 + e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) * (1 - e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) := by rw [add_mul, hu]
    _ = 1 := by
      rw [show (1 + e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) * (1 - e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) = 1 - (e * ((u⁻¹ : (ZMod n)ˣ) : ZMod n))^2 by ring]
      rw [hsq, sub_zero]

lemma zmod_inv_neg_add_square_zero {n : ℕ} (u : (ZMod n)ˣ) {e : ZMod n} (he : e ^ 2 = 0) :
    (-(u : ZMod n) + e)⁻¹ = -(((u⁻¹ : (ZMod n)ˣ) : ZMod n)) - e * (((u⁻¹ : (ZMod n)ˣ) : ZMod n)^2) := by
  rw [show (-(u : ZMod n) + e) = (((-u : (ZMod n)ˣ) : ZMod n) + e) by simp]
  rw [zmod_inv_add_square_zero (-u : (ZMod n)ˣ) (e := e) he]
  simp
  ring

lemma zmod_inv_pair_formula {n : ℕ} (u : (ZMod n)ˣ) {e : ZMod n} (he : e ^ 2 = 0) :
    ((u : ZMod n)⁻¹) + (-(u : ZMod n) + e)⁻¹ = - e * (((u⁻¹ : (ZMod n)ˣ) : ZMod n)^2) := by
  rw [zmod_inv_neg_add_square_zero u he]
  rw [ZMod.inv_coe_unit]
  ring

lemma zmod_inv_pair_nat_square {m i : ℕ} (hcop : Nat.Coprime i m) (him : i ≤ m) :
    ((i : ZMod (m^2))⁻¹) + (((m - i : ℕ) : ZMod (m^2))⁻¹) =
      - (m : ZMod (m^2)) * (((i : ZMod (m^2))⁻¹)^2) := by
  let u : (ZMod (m^2))ˣ := ZMod.unitOfCoprime i (hcop.pow_right 2)
  have huval : (u : ZMod (m^2)) = (i : ZMod (m^2)) := rfl
  have hsub : ((m - i : ℕ) : ZMod (m^2)) = - (i : ZMod (m^2)) + (m : ZMod (m^2)) := by
    rw [Nat.cast_sub him]
    ring
  rw [hsub]
  rw [← huval]
  have h := zmod_inv_pair_formula (n:=m^2) u (e := (m : ZMod (m^2))) (zmod_base_square_zero m)
  rw [ZMod.inv_coe_unit]
  simpa [pow_two] using h

lemma zmod_unitRange_lift_inv_sq_mul_pr_zero {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    ((p^r : ℕ) : ZMod ((p^r)^2)) *
      (∑ i ∈ unitRange p r, ((i : ZMod ((p^r)^2))⁻¹)^2) = 0 := by
  haveI : NeZero (p^r) := ⟨pow_ne_zero_of_prime (p := p) (r := r) hp⟩
  apply zmod_square_base_mul_zero_of_cast_zero (m := p^r)
  simp only [map_sum, map_pow]
  rw [show (∑ x ∈ unitRange p r,
      (ZMod.castHom (show p ^ r ∣ (p ^ r) ^ 2 by rw [pow_two]; exact dvd_mul_right (p^r) (p^r)) (ZMod (p^r))) (↑x)⁻¹ ^ 2) =
      (∑ i ∈ unitRange p r, ((i : ZMod (p^r))⁻¹)^2) by
    apply Finset.sum_congr rfl
    intro i hi
    have hnot : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
    have hcop : Nat.Coprime i (p^r) := hp.coprime_pow_of_not_dvd hnot
    rw [zmod_map_inv_nat_of_coprime (m := p^r) (i := i) hcop]]
  exact zmod_unitRange_inv_sq_sum_zero hp hp5 hr

noncomputable def unitRangeNegEquiv (p r : ℕ) (hp : Nat.Prime p) (hr : 0 < r) :
    {i : ℕ // i ∈ unitRange p r} ≃ {i : ℕ // i ∈ unitRange p r} where
  toFun a := by
    let m := p^r
    have haI := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
    have hnot : ¬ p ∣ a.1 := (Finset.mem_filter.mp a.2).2
    refine ⟨m - a.1, ?_⟩
    change m - a.1 ∈ (Finset.Ico 1 (p^r)).filter (fun i => ¬ p ∣ i)
    rw [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · constructor
      · omega
      · omega
    · intro hd
      have hpm : p ∣ m := by
        dsimp [m]
        exact prime_dvd_pow_self_of_pos p r hr
      have hpa : p ∣ a.1 := by
        have hsub : p ∣ m - (m - a.1) := Nat.dvd_sub hpm hd
        have hmma : m - (m - a.1) = a.1 := Nat.sub_sub_self (le_of_lt haI.2)
        rwa [hmma] at hsub
      exact hnot hpa
  invFun a := by
    let m := p^r
    have haI := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
    have hnot : ¬ p ∣ a.1 := (Finset.mem_filter.mp a.2).2
    refine ⟨m - a.1, ?_⟩
    change m - a.1 ∈ (Finset.Ico 1 (p^r)).filter (fun i => ¬ p ∣ i)
    rw [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · constructor
      · omega
      · omega
    · intro hd
      have hpm : p ∣ m := by
        dsimp [m]
        exact prime_dvd_pow_self_of_pos p r hr
      have hpa : p ∣ a.1 := by
        have hsub : p ∣ m - (m - a.1) := Nat.dvd_sub hpm hd
        have hmma : m - (m - a.1) = a.1 := Nat.sub_sub_self (le_of_lt haI.2)
        rwa [hmma] at hsub
      exact hnot hpa
  left_inv a := by
    apply Subtype.ext
    let m := p^r
    have haI := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
    change m - (m - a.1) = a.1
    exact Nat.sub_sub_self (le_of_lt haI.2)
  right_inv a := by
    apply Subtype.ext
    let m := p^r
    have haI := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
    change m - (m - a.1) = a.1
    exact Nat.sub_sub_self (le_of_lt haI.2)

/-- In `ZMod (p^(2*r))`, the inverse harmonic sum over `unitRange p r` is zero. -/
theorem zmod_unitRange_inv_sum_zero_mod_p2r {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∑ i ∈ unitRange p r, ((i : ZMod (p^(2*r)))⁻¹)) = 0 := by
  let m := p^r
  have hm2 : m^2 = p^(2*r) := by
    dsimp [m]
    rw [← pow_mul]
    congr 1
    omega
  haveI : NeZero m := ⟨by dsimp [m]; exact pow_ne_zero_of_prime (p := p) (r := r) hp⟩
  haveI : NeZero (m^2) := ⟨pow_ne_zero 2 (NeZero.ne m)⟩
  let R := ZMod (m^2)
  let S : R := ∑ i ∈ unitRange p r, ((i : R)⁻¹)
  have hreflect : (∑ i ∈ unitRange p r, (((m - i : ℕ) : R)⁻¹)) = S := by
    dsimp [S]
    rw [Finset.sum_subtype (unitRange p r) (by intro x; rfl) (fun i => (((m - i : ℕ) : R)⁻¹))]
    rw [Finset.sum_subtype (unitRange p r) (by intro x; rfl) (fun i => ((i : R)⁻¹))]
    let e := unitRangeNegEquiv p r hp hr
    calc
      (∑ a : { i // i ∈ unitRange p r}, (((m - (a : ℕ) : ℕ) : R)⁻¹))
          = ∑ a : { i // i ∈ unitRange p r}, (((e a : ℕ) : R)⁻¹) := by rfl
      _ = ∑ a : { i // i ∈ unitRange p r}, (((a : ℕ) : R)⁻¹) := by
          exact Fintype.sum_equiv e
            (fun a : { i // i ∈ unitRange p r} => (((e a : ℕ) : R)⁻¹))
            (fun a : { i // i ∈ unitRange p r} => (((a : ℕ) : R)⁻¹)) (by intro a; rfl)
  have htwoS : (2 : R) * S = 0 := by
    have hpair : S + S = - (m : R) * (∑ i ∈ unitRange p r, ((i : R)⁻¹)^2) := by
      calc
        S + S = (∑ i ∈ unitRange p r, ((i : R)⁻¹)) +
              (∑ i ∈ unitRange p r, (((m - i : ℕ) : R)⁻¹)) := by rw [hreflect]
        _ = ∑ i ∈ unitRange p r, (((i : R)⁻¹) + (((m - i : ℕ) : R)⁻¹)) := by rw [Finset.sum_add_distrib]
        _ = ∑ i ∈ unitRange p r, (- (m : R) * (((i : R)⁻¹)^2)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hnot : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
          have hcop : Nat.Coprime i m := by
            dsimp [m]
            exact hp.coprime_pow_of_not_dvd hnot
          have hi_le : i ≤ m := le_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).2
          exact zmod_inv_pair_nat_square (m := m) (i := i) hcop hi_le
        _ = - (m : R) * (∑ i ∈ unitRange p r, ((i : R)⁻¹)^2) := by rw [Finset.mul_sum]
    have hmsq : (m : R) * (∑ i ∈ unitRange p r, ((i : R)⁻¹)^2) = 0 := by
      dsimp [R, m]
      exact zmod_unitRange_lift_inv_sq_mul_pr_zero hp hp5 hr
    calc
      (2 : R) * S = S + S := by ring
      _ = - (m : R) * (∑ i ∈ unitRange p r, ((i : R)⁻¹)^2) := hpair
      _ = 0 := by
        rw [show - (m : R) * (∑ i ∈ unitRange p r, ((i : R)⁻¹)^2) =
          - ((m : R) * (∑ i ∈ unitRange p r, ((i : R)⁻¹)^2)) by ring]
        rw [hmsq, neg_zero]
  have h2unit : IsUnit (2 : R) := by
    dsimp [R, m]
    have hcop : Nat.Coprime 2 p := ((hp.coprime_iff_not_dvd).2 (not_dvd_two_of_five_le hp5)).symm
    exact (ZMod.unitOfCoprime 2 ((hcop.pow_right r).pow_right 2)).isUnit
  have hS : S = 0 := (IsUnit.mul_right_eq_zero h2unit).mp htwoS
  change (∑ i ∈ unitRange p r, ((i : ZMod (p^(2*r)))⁻¹)) = 0
  rw [← hm2]
  exact hS

end TempShiftedProductGeneralHarmonic


/- Flattened helper code from TempHalfBlockR.lean -/

open scoped BigOperators

namespace TempHalfBlockR

/-- Positive reduced residues in the lower half of the interval modulo `p^r`. -/
def halfUnitRange (p r : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (((p^r - 1) / 2) + 1)).filter (fun i => ¬ p ∣ i)

/-- The generalized shifted half-block in `ZMod (p^(3*r))`. -/
def halfBlockR (p r q : ℕ) : ZMod (p^(3*r)) :=
  ∏ i ∈ halfUnitRange p r,
    ((i : ZMod (p^(3*r))) + (q : ZMod (p^(3*r))) * (p^r : ZMod (p^(3*r))))

lemma pow_odd_decomp {m : ℕ} (hm : Odd m) : m = 2 * ((m - 1) / 2) + 1 := by
  obtain ⟨k, hk⟩ := hm
  have : (m - 1) / 2 = k := by omega
  omega

lemma prime_pow_odd {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) : Odd (p^r) := by
  exact (hp.odd_of_ne_two (by omega)).pow

lemma prime_dvd_pow_self_of_pos (p r : ℕ) (hr : 0 < r) : p ∣ p ^ r := by
  cases r with
  | zero => omega
  | succ k =>
      use p^k
      rw [pow_succ]
      exact Nat.mul_comm (p^k) p

lemma halfUnitRange_subset_unitRange {p r i : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hi : i ∈ halfUnitRange p r) :
    i ∈ TempShiftedProductGeneralHarmonic.unitRange p r := by
  rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hi
  rw [TempShiftedProductGeneralHarmonic.unitRange, Finset.mem_filter, Finset.mem_Ico]
  rcases hi with ⟨⟨hi1, hih⟩, hnot⟩
  refine ⟨⟨hi1, ?_⟩, hnot⟩
  have hmpos : 0 < p^r := pow_pos hp.pos r
  omega

noncomputable def halfUnitRangeNegEquiv (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    {i : ℕ // i ∈ halfUnitRange p r} ≃
      {i : ℕ // i ∈ (Finset.Ico (((p^r - 1) / 2) + 1) (p^r)).filter (fun i => ¬ p ∣ i)} where
  toFun a := by
    let m := p^r
    let h := (m - 1) / 2
    have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
    have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
    have ha := Finset.mem_filter.mp a.2
    have haI := Finset.mem_Ico.mp ha.1
    have hnot : ¬ p ∣ a.1 := ha.2
    refine ⟨m - a.1, ?_⟩
    rw [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · constructor
      · omega
      · omega
    · intro hd
      have hpm : p ∣ m := by dsimp [m]; exact prime_dvd_pow_self_of_pos p r hr
      have hpa : p ∣ a.1 := by
        have ham : a.1 < m := by dsimp [m, h] at hm haI ⊢; omega
        have hsub : p ∣ m - (m - a.1) := Nat.dvd_sub hpm hd
        have hmma : m - (m - a.1) = a.1 := Nat.sub_sub_self (le_of_lt ham)
        rwa [hmma] at hsub
      exact hnot hpa
  invFun a := by
    let m := p^r
    let h := (m - 1) / 2
    have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
    have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
    have ha := Finset.mem_filter.mp a.2
    have haI := Finset.mem_Ico.mp ha.1
    have hnot : ¬ p ∣ a.1 := ha.2
    refine ⟨m - a.1, ?_⟩
    rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · constructor
      · omega
      · omega
    · intro hd
      have hpm : p ∣ m := by dsimp [m]; exact prime_dvd_pow_self_of_pos p r hr
      have hpa : p ∣ a.1 := by
        have hsub : p ∣ m - (m - a.1) := Nat.dvd_sub hpm hd
        have hmma : m - (m - a.1) = a.1 := Nat.sub_sub_self (le_of_lt haI.2)
        rwa [hmma] at hsub
      exact hnot hpa
  left_inv a := by
    apply Subtype.ext
    let m := p^r
    let h := (m - 1) / 2
    have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
    have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
    have haI := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
    have ham : a.1 < m := by dsimp [m, h] at hm haI ⊢; omega
    change m - (m - a.1) = a.1
    exact Nat.sub_sub_self (le_of_lt ham)
  right_inv a := by
    apply Subtype.ext
    let m := p^r
    have haI := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
    change m - (m - a.1) = a.1
    exact Nat.sub_sub_self (le_of_lt haI.2)

/-- The half inverse-square sum over the lower reduced residues vanishes modulo `p^r`. -/
theorem zmod_halfUnitRange_inv_sq_sum_zero {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∑ i ∈ halfUnitRange p r, ((i : ZMod (p^r))⁻¹)^2) = 0 := by
  let m := p^r
  let h := (m - 1) / 2
  let R := ZMod m
  have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
  have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
  haveI : NeZero m := ⟨by dsimp [m]; exact TempShiftedProductGeneralHarmonic.pow_ne_zero_of_prime (p := p) (r := r) hp⟩
  have hsplit : TempShiftedProductGeneralHarmonic.unitRange p r =
      halfUnitRange p r ∪ (Finset.Ico (((p^r - 1) / 2) + 1) (p^r)).filter (fun i => ¬ p ∣ i) := by
    ext i
    rw [TempShiftedProductGeneralHarmonic.unitRange, halfUnitRange]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    dsimp [m, h] at hm ⊢
    constructor
    · intro hfull
      rcases hfull with ⟨⟨hi1, him⟩, hnot⟩
      by_cases hih : i < (p ^ r - 1) / 2 + 1
      · exact Or.inl ⟨⟨hi1, hih⟩, hnot⟩
      · exact Or.inr ⟨⟨by omega, him⟩, hnot⟩
    · intro hmem
      rcases hmem with hmem | hmem
      · rcases hmem with ⟨⟨hi1, hih⟩, hnot⟩
        exact ⟨⟨hi1, by omega⟩, hnot⟩
      · rcases hmem with ⟨⟨hlo, him⟩, hnot⟩
        exact ⟨⟨by omega, him⟩, hnot⟩
  have hdisj : Disjoint (halfUnitRange p r) ((Finset.Ico (((p^r - 1) / 2) + 1) (p^r)).filter (fun i => ¬ p ∣ i)) := by
    rw [Finset.disjoint_left]
    intro i hi hu
    rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hi
    rw [Finset.mem_filter, Finset.mem_Ico] at hu
    omega
  let S : R := ∑ i ∈ halfUnitRange p r, ((i : R)⁻¹)^2
  have hupper : (∑ i ∈ (Finset.Ico (((p^r - 1) / 2) + 1) (p^r)).filter (fun i => ¬ p ∣ i), ((i : R)⁻¹)^2) = S := by
    dsimp [S]
    rw [Finset.sum_subtype ((Finset.Ico (((p^r - 1) / 2) + 1) (p^r)).filter (fun i => ¬ p ∣ i)) (by intro x; rfl)
      (fun i => ((i : R)⁻¹)^2)]
    rw [Finset.sum_subtype (halfUnitRange p r) (by intro x; rfl) (fun i => ((i : R)⁻¹)^2)]
    let e := halfUnitRangeNegEquiv p r hp hp5 hr
    calc
      (∑ a : { i // i ∈ (Finset.Ico (((p^r - 1) / 2) + 1) (p^r)).filter (fun i => ¬ p ∣ i)}, (((a : ℕ) : R)⁻¹)^2)
          = ∑ a : { i // i ∈ halfUnitRange p r}, ((((e a : ℕ) : R)⁻¹)^2) := by
            exact (Fintype.sum_equiv e
              (fun a : { i // i ∈ halfUnitRange p r} => ((((e a : ℕ) : R)⁻¹)^2))
              (fun a : { i // i ∈ (Finset.Ico (((p^r - 1) / 2) + 1) (p^r)).filter (fun i => ¬ p ∣ i)} => (((a : ℕ) : R)⁻¹)^2)
              (by intro a; rfl)).symm
      _ = ∑ a : { i // i ∈ halfUnitRange p r}, (((a : ℕ) : R)⁻¹)^2 := by
            apply Finset.sum_congr rfl
            intro a _
            change ((((m - (a : ℕ) : ℕ) : R)⁻¹)^2) = ((((a : ℕ) : R)⁻¹)^2)
            have haI := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
            have hle : (a : ℕ) ≤ m := le_trans (le_of_lt haI.2) (by dsimp [m, h] at hm ⊢; omega)
            have hcast : ((m - (a : ℕ) : ℕ) : R) = - ((a : ℕ) : R) := by
              rw [Nat.cast_sub hle]
              dsimp [R, m]
              simp
            rw [hcast]
            have hnot : ¬ p ∣ (a : ℕ) := (Finset.mem_filter.mp a.2).2
            have hunit : IsUnit (((a : ℕ) : R)) := by
              dsimp [R, m]
              rw [ZMod.isUnit_iff_coprime]
              exact hp.coprime_pow_of_not_dvd hnot
            have hxinv : (((a : ℕ) : R)) * (((a : ℕ) : R)⁻¹) = 1 :=
              ZMod.mul_inv_of_unit _ hunit
            have hneg : (-((a : ℕ) : R))⁻¹ = -(((a : ℕ) : R)⁻¹) := by
              apply ZMod.inv_eq_of_mul_eq_one
              rw [show (-((a : ℕ) : R)) * (-(((a : ℕ) : R)⁻¹)) =
                    (((a : ℕ) : R)) * (((a : ℕ) : R)⁻¹) by ring, hxinv]
            rw [hneg]
            ring
  have hfull := TempShiftedProductGeneralHarmonic.zmod_unitRange_inv_sq_sum_zero (p := p) (r := r) hp hp5 hr
  change (∑ i ∈ TempShiftedProductGeneralHarmonic.unitRange p r, ((i : R)⁻¹)^2) = 0 at hfull
  have hfull_two : (∑ i ∈ TempShiftedProductGeneralHarmonic.unitRange p r, ((i : R)⁻¹)^2) = (2 : R) * S := by
    rw [hsplit, Finset.sum_union hdisj, hupper]
    ring
  have h2S : (2 : R) * S = 0 := by rwa [hfull_two] at hfull
  have h2unit : IsUnit (2 : R) := by
    dsimp [R, m]
    exact TempShiftedProductGeneralHarmonic.zmod_two_unit_pow hp hp5
  have hS : S = 0 := (IsUnit.mul_right_eq_zero h2unit).mp h2S
  exact hS

end TempHalfBlockR


namespace TempHalfBlockR

lemma prod_one_add_eq_one_add_sum_of_pairwise_mul_zero
    {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (y : ι → R)
    (hmul : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → y a * y b = 0) :
    ∏ i ∈ s, (1 + y i) = 1 + ∑ i ∈ s, y i := by
  revert hmul
  refine Finset.induction_on s ?empty ?insert
  · intro hmul
    simp
  · intro a s ha ih hmul
    have hmul_s : ∀ x ∈ s, ∀ z ∈ s, x ≠ z → y x * y z = 0 := by
      intro x hx z hz hxz
      exact hmul x (Finset.mem_insert_of_mem hx) z (Finset.mem_insert_of_mem hz) hxz
    have ih' := ih hmul_s
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih']
    have hay_sum : y a * (∑ x ∈ s, y x) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro x hx
      exact hmul a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx) (by
        intro h; exact ha (h.symm ▸ hx))
    ring_nf
    rw [hay_sum]
    ring

lemma prod_one_add_eq_one_of_sum_and_pairwise_mul_zero
    {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (y : ι → R)
    (hsum : (∑ i ∈ s, y i) = 0)
    (hmul : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → y a * y b = 0) :
    ∏ i ∈ s, (1 + y i) = 1 := by
  rw [prod_one_add_eq_one_add_sum_of_pairwise_mul_zero s y hmul, hsum, add_zero]

lemma zmod_p3r_base_pow_four_eq_zero (p r : ℕ) (hr : 0 < r) :
    ((p^r : ZMod (p^(3*r))) ^ 4) = 0 := by
  rw [show ((p^r : ZMod (p^(3*r))) ^ 4) = ((p ^ (4*r) : ℕ) : ZMod (p^(3*r))) by
    norm_num [Nat.cast_pow]
    rw [← pow_mul]
    congr 1
    omega]
  have hfac : p ^ (4*r) = p ^ (3*r) * p^r := by
    rw [← pow_add]
    congr 1
    omega
  rw [hfac, Nat.cast_mul, CharP.cast_eq_zero, zero_mul]

lemma zmod_p3r_base_sq_mul_zero_of_cast_zero {p r : ℕ} (hp : Nat.Prime p) (hr : 0 < r)
    (x : ZMod (p^(3*r)))
    (hx : ZMod.castHom (by
        show p^r ∣ p^(3*r)
        use p^(2*r)
        rw [← pow_add]
        congr 1
        omega) (ZMod (p^r)) x = 0) :
    ((p^r : ZMod (p^(3*r)))^2) * x = 0 := by
  haveI : NeZero (p^(3*r)) := ⟨by exact pow_ne_zero (3*r) hp.ne_zero⟩
  have hxval : ((x.val : ℕ) : ZMod (p^r)) = 0 := by
    rw [← ZMod.natCast_zmod_val x] at hx
    simpa using hx
  have hdvd_nat : p^r ∣ x.val := by
    rw [← Nat.modEq_zero_iff_dvd]
    rw [← ZMod.natCast_eq_natCast_iff (x.val) 0 (p^r)]
    simpa using hxval
  obtain ⟨t, ht⟩ := hdvd_nat
  rw [← ZMod.natCast_zmod_val x]
  rw [show ((p^r : ZMod (p^(3*r)))^2) = (((p^r)^2 : ℕ) : ZMod (p^(3*r))) by
    norm_num [Nat.cast_pow]]
  rw [← Nat.cast_mul]
  rw [ht]
  rw [show (p^r)^2 * (p^r * t) = p^(3*r) * t by
    ring_nf]
  rw [Nat.cast_mul, CharP.cast_eq_zero, zero_mul]

lemma shifted_factor_isUnit {p r q i : ℕ} (hp : Nat.Prime p) (hr : 0 < r)
    (hi : i ∈ halfUnitRange p r) :
    IsUnit ((i : ZMod (p^(3*r))) + (q : ZMod (p^(3*r))) * (p^r : ZMod (p^(3*r)))) := by
  rw [halfUnitRange, Finset.mem_filter] at hi
  have hnoti : ¬ p ∣ i := hi.2
  have hpdm : p ∣ p^r := prime_dvd_pow_self_of_pos p r hr
  have hnot : ¬ p ∣ i + q * p^r := by
    intro hd
    have hq : p ∣ q * p^r := dvd_mul_of_dvd_right hpdm q
    have hsub : p ∣ (i + q * p^r) - q * p^r := Nat.dvd_sub hd hq
    have hi' : p ∣ i := by simpa using hsub
    exact hnoti hi'
  have hcop : Nat.Coprime (i + q * p^r) (p^(3*r)) := hp.coprime_pow_of_not_dvd hnot
  convert (ZMod.unitOfCoprime (i + q * p^r) hcop).isUnit using 1
  norm_num [Nat.cast_add, Nat.cast_mul]

lemma shifted_C_isUnit {p r q i : ℕ} (hp : Nat.Prime p) (hr : 0 < r)
    (hi : i ∈ halfUnitRange p r) :
    IsUnit (((i : ZMod (p^(3*r))) + (q : ZMod (p^(3*r))) * (p^r : ZMod (p^(3*r)))) *
      ((i : ZMod (p^(3*r))) + (p^r : ZMod (p^(3*r))))) := by
  exact IsUnit.mul (shifted_factor_isUnit (p := p) (r := r) (q := q) (i := i) hp hr hi)
    (by simpa using shifted_factor_isUnit (p := p) (r := r) (q := 1) (i := i) hp hr hi)


lemma zmod_cast_Cinv_eq_inv_sq {p r q i : ℕ} (hp : Nat.Prime p) (hr : 0 < r)
    (hi : i ∈ halfUnitRange p r) :
    ZMod.castHom (by
        show p^r ∣ p^(3*r)
        use p^(2*r)
        rw [← pow_add]
        congr 1
        omega) (ZMod (p^r))
      ((((i : ZMod (p^(3*r))) + (q : ZMod (p^(3*r))) * (p^r : ZMod (p^(3*r)))) *
        ((i : ZMod (p^(3*r))) + (p^r : ZMod (p^(3*r)))))⁻¹) =
      ((i : ZMod (p^r))⁻¹)^2 := by
  let φ := ZMod.castHom (by
        show p^r ∣ p^(3*r)
        use p^(2*r)
        rw [← pow_add]
        congr 1
        omega) (ZMod (p^r))
  let C : ZMod (p^(3*r)) := (((i : ZMod (p^(3*r))) + (q : ZMod (p^(3*r))) * (p^r : ZMod (p^(3*r)))) *
        ((i : ZMod (p^(3*r))) + (p^r : ZMod (p^(3*r)))))
  have hunitC : IsUnit C := by
    dsimp [C]
    exact shifted_C_isUnit (p := p) (r := r) (q := q) (i := i) hp hr hi
  have hφC : φ C = ((i : ZMod (p^r))^2) := by
    dsimp [C]
    rw [map_mul, map_add, map_mul, map_add]
    simp only [map_natCast]
    have hbase : φ ((p : ZMod (p^(3*r))) ^ r) = 0 := by
      rw [map_pow, map_natCast]
      rw [← Nat.cast_pow]
      exact CharP.cast_eq_zero (ZMod (p^r)) (p^r)
    rw [hbase]
    ring
  have hmul : φ C * φ (C⁻¹) = 1 := by
    have hc := congrArg φ (ZMod.mul_inv_of_unit C hunitC)
    simpa only [map_mul, map_one] using hc
  have hinvC : φ (C⁻¹) = (φ C)⁻¹ := by
    exact (ZMod.inv_eq_of_mul_eq_one (p^r) (φ C) (φ (C⁻¹)) hmul).symm
  rw [show ZMod.castHom (by
        show p^r ∣ p^(3*r)
        use p^(2*r)
        rw [← pow_add]
        congr 1
        omega) (ZMod (p^r))
      ((((i : ZMod (p^(3*r))) + (q : ZMod (p^(3*r))) * (p^r : ZMod (p^(3*r)))) *
        ((i : ZMod (p^(3*r))) + (p^r : ZMod (p^(3*r)))))⁻¹) = φ (C⁻¹) by rfl]
  rw [hinvC, hφC]
  have hnot : ¬ p ∣ i := by
    have hi' := hi
    rw [halfUnitRange, Finset.mem_filter] at hi'
    exact hi'.2
  have hunit : IsUnit (i : ZMod (p^r)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hp.coprime_pow_of_not_dvd hnot
  apply ZMod.inv_eq_of_mul_eq_one
  rw [show ((i : ZMod (p^r))^2) * ((i : ZMod (p^r))⁻¹)^2 =
        ((i : ZMod (p^r)) * ((i : ZMod (p^r))⁻¹))^2 by ring]
  rw [ZMod.mul_inv_of_unit _ hunit]
  norm_num

lemma shifted_Cinv_sum_base_sq_zero {p r q : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    ((p^r : ZMod (p^(3*r)))^2) *
      (∑ i ∈ halfUnitRange p r,
        ((((i : ZMod (p^(3*r))) + (q : ZMod (p^(3*r))) * (p^r : ZMod (p^(3*r)))) *
          ((i : ZMod (p^(3*r))) + (p^r : ZMod (p^(3*r)))))⁻¹)) = 0 := by
  apply zmod_p3r_base_sq_mul_zero_of_cast_zero (p := p) (r := r) hp hr
  simp only [map_sum]
  rw [show (∑ x ∈ halfUnitRange p r,
      (ZMod.castHom (by
        show p^r ∣ p^(3*r)
        use p^(2*r)
        rw [← pow_add]
        congr 1
        omega) (ZMod (p^r)))
      ((((x : ZMod (p^(3*r))) + (q : ZMod (p^(3*r))) * (p^r : ZMod (p^(3*r)))) *
          ((x : ZMod (p^(3*r))) + (p^r : ZMod (p^(3*r)))))⁻¹)) =
      (∑ i ∈ halfUnitRange p r, ((i : ZMod (p^r))⁻¹)^2) by
    apply Finset.sum_congr rfl
    intro i hi
    exact zmod_cast_Cinv_eq_inv_sq (p := p) (r := r) (q := q) (i := i) hp hr hi]
  exact zmod_halfUnitRange_inv_sq_sum_zero hp hp5 hr

end TempHalfBlockR

namespace TempHalfBlockR

/-- Cross-multiplication identity for generalized shifted half-blocks. -/
theorem halfBlockR_q_independent {p r q : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    halfBlockR p r (q+1) * halfBlockR p r 0 = halfBlockR p r q * halfBlockR p r 1 := by
  let R := ZMod (p^(3*r))
  let P : R := (p^r : R)
  let s := halfUnitRange p r
  let d : R := -(q : R) * P^2
  let C : ℕ → R := fun i => ((i : R) + (q : R) * P) * ((i : R) + P)
  let A : ℕ → R := fun i => ((i : R) + ((q+1 : ℕ) : R) * P) * (i : R)
  let y : ℕ → R := fun i => d * (C i)⁻¹
  have hA : ∀ i ∈ s, A i = C i * (1 + y i) := by
    intro i hi
    have hunit : IsUnit (C i) := by
      dsimp [C, R, P]
      exact shifted_C_isUnit (p := p) (r := r) (q := q) (i := i) hp hr hi
    have hmul_inv : C i * (C i)⁻¹ = 1 := ZMod.mul_inv_of_unit (C i) hunit
    dsimp [A, C, y, d, P, R]
    rw [show ((q + 1 : ℕ) : ZMod (p ^ (3*r))) = (q : ZMod (p ^ (3*r))) + 1 by norm_num]
    calc
      (((i : ZMod (p ^ (3*r))) + ((q : ZMod (p ^ (3*r))) + 1) * (p^r : ZMod (p ^ (3*r)))) * (i : ZMod (p ^ (3*r))))
          = (((i : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
              ((i : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r))))) -
                (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))^2 := by ring
      _ = (((i : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
              ((i : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r))))) *
            (1 + (-(q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))^2) *
              ((((i : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
                ((i : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r)))))⁻¹)) := by
        rw [show (((i : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
              ((i : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r))))) *
            (1 + (-(q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))^2) *
              ((((i : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
                ((i : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r)))))⁻¹)) =
            (((i : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
              ((i : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r))))) +
              (-(q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))^2) *
              ((((i : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
                ((i : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r))))) *
              ((((i : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
                ((i : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r)))))⁻¹)) by ring]
        rw [hmul_inv]
        ring
  have hprodA : (∏ i ∈ s, A i) = (∏ i ∈ s, C i) * (∏ i ∈ s, (1 + y i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact hA i hi
  have hsum_y : (∑ i ∈ s, y i) = 0 := by
    dsimp [y, d, C, P, R, s]
    rw [← Finset.mul_sum]
    rw [show (-(q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r))) ^ 2) *
        (∑ x ∈ halfUnitRange p r,
          ((((x : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
            ((x : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r)))))⁻¹)) =
        -(q : ZMod (p ^ (3*r))) * (((p^r : ZMod (p ^ (3*r))) ^ 2) *
        (∑ x ∈ halfUnitRange p r,
          ((((x : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r)))) *
            ((x : ZMod (p ^ (3*r))) + (p^r : ZMod (p ^ (3*r)))))⁻¹))) by ring]
    rw [shifted_Cinv_sum_base_sq_zero (p := p) (r := r) (q := q) hp hp5 hr, mul_zero]
  have hdsq : d^2 = 0 := by
    dsimp [d, P, R]
    rw [show (-(q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r))) ^ 2) ^ 2 =
      (q : ZMod (p ^ (3*r)))^2 * (p^r : ZMod (p ^ (3*r)))^4 by ring]
    rw [zmod_p3r_base_pow_four_eq_zero p r hr, mul_zero]
  have hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → y a * y b = 0 := by
    intro a ha b hb hab
    dsimp [y]
    rw [show (d * (C a)⁻¹) * (d * (C b)⁻¹) = d^2 * ((C a)⁻¹ * (C b)⁻¹) by ring]
    rw [hdsq, zero_mul]
  have hyprod : (∏ i ∈ s, (1 + y i)) = 1 :=
    prod_one_add_eq_one_of_sum_and_pairwise_mul_zero s y hsum_y hpair
  calc
    halfBlockR p r (q+1) * halfBlockR p r 0
        = (∏ i ∈ s, A i) := by
          dsimp [halfBlockR, A, s, R, P]
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i hi
          ring
    _ = (∏ i ∈ s, C i) * (∏ i ∈ s, (1 + y i)) := hprodA
    _ = ∏ i ∈ s, C i := by rw [hyprod, mul_one]
    _ = halfBlockR p r q * halfBlockR p r 1 := by
          dsimp [halfBlockR, C, s, R, P]
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i hi
          ring

end TempHalfBlockR

namespace TempHalfBlockR

/-- The negative shifted half-block in `ZMod (p^(3*r))`. -/
def halfBlockRMinus (p r : ℕ) : ZMod (p^(3*r)) :=
  ∏ i ∈ halfUnitRange p r,
    ((i : ZMod (p^(3*r))) - (p^r : ZMod (p^(3*r))))

/-- The unshifted half-block is a unit. -/
theorem halfBlockR_zero_isUnit {p r : ℕ} (hp : Nat.Prime p) (hr : 0 < r) :
    IsUnit (halfBlockR p r 0) := by
  dsimp [halfBlockR]
  apply Finset.prod_induction
  · intro a b ha hb
    exact IsUnit.mul ha hb
  · exact isUnit_one
  · intro i hi
    simpa using shifted_factor_isUnit (p := p) (r := r) (q := 0) (i := i) hp hr hi

lemma zmod_cast_inv_nat_eq_inv {p r i : ℕ} (hp : Nat.Prime p) (hr : 0 < r)
    (hi : i ∈ halfUnitRange p r) :
    ZMod.castHom (by
        show p^r ∣ p^(3*r)
        use p^(2*r)
        rw [← pow_add]
        congr 1
        omega) (ZMod (p^r))
      ((i : ZMod (p^(3*r)))⁻¹) = ((i : ZMod (p^r))⁻¹) := by
  let φ := ZMod.castHom (by
        show p^r ∣ p^(3*r)
        use p^(2*r)
        rw [← pow_add]
        congr 1
        omega) (ZMod (p^r))
  have hunit : IsUnit (i : ZMod (p^(3*r))) := by
    simpa using shifted_factor_isUnit (p := p) (r := r) (q := 0) (i := i) hp hr hi
  have hmul : φ (i : ZMod (p^(3*r))) * φ ((i : ZMod (p^(3*r)))⁻¹) = 1 := by
    have hc := congrArg φ (ZMod.mul_inv_of_unit (i : ZMod (p^(3*r))) hunit)
    simpa only [map_mul, map_one] using hc
  have hinv : φ ((i : ZMod (p^(3*r)))⁻¹) = (φ (i : ZMod (p^(3*r))))⁻¹ := by
    exact (ZMod.inv_eq_of_mul_eq_one (p^r) (φ (i : ZMod (p^(3*r))))
      (φ ((i : ZMod (p^(3*r)))⁻¹)) hmul).symm
  rw [show ZMod.castHom (by
        show p^r ∣ p^(3*r)
        use p^(2*r)
        rw [← pow_add]
        congr 1
        omega) (ZMod (p^r))
      ((i : ZMod (p^(3*r)))⁻¹) = φ ((i : ZMod (p^(3*r)))⁻¹) by rfl]
  rw [hinv]
  simp only [map_natCast]

/-- Lift of the half inverse-square vanishing: after multiplying by `p^(2r)`, the
sum vanishes in `ZMod (p^(3*r))`. -/
theorem zmod_p3r_halfUnitRange_inv_sq_sum_base_sq_zero {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    ((p^r : ZMod (p^(3*r)))^2) *
      (∑ i ∈ halfUnitRange p r, ((i : ZMod (p^(3*r)))⁻¹)^2) = 0 := by
  apply zmod_p3r_base_sq_mul_zero_of_cast_zero (p := p) (r := r) hp hr
  simp only [map_sum, map_pow]
  rw [show (∑ x ∈ halfUnitRange p r,
      (ZMod.castHom (by
        show p^r ∣ p^(3*r)
        use p^(2*r)
        rw [← pow_add]
        congr 1
        omega) (ZMod (p^r))) ((x : ZMod (p^(3*r)))⁻¹) ^ 2) =
      (∑ i ∈ halfUnitRange p r, ((i : ZMod (p^r))⁻¹)^2) by
    apply Finset.sum_congr rfl
    intro i hi
    rw [zmod_cast_inv_nat_eq_inv (p := p) (r := r) (i := i) hp hr hi]]
  exact zmod_halfUnitRange_inv_sq_sum_zero hp hp5 hr

/-- The plus and minus half-blocks multiply to the square of the unshifted
half-block. -/
theorem halfBlockR_one_mul_minus_eq_zero_sq {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (halfBlockR p r 1) * halfBlockRMinus p r = (halfBlockR p r 0)^2 := by
  let R := ZMod (p^(3*r))
  let P : R := (p^r : R)
  let s := halfUnitRange p r
  let A : ℕ → R := fun i => ((i : R) + P) * ((i : R) - P)
  let B : ℕ → R := fun i => (i : R) * (i : R)
  let y : ℕ → R := fun i => -P^2 * (((i : R)⁻¹)^2)
  have hA : ∀ i ∈ s, A i = B i * (1 + y i) := by
    intro i hi
    have hunit : IsUnit (i : R) := by
      dsimp [R]
      simpa using shifted_factor_isUnit (p := p) (r := r) (q := 0) (i := i) hp hr hi
    have hmul_inv : (i : R) * (i : R)⁻¹ = 1 := ZMod.mul_inv_of_unit (i : R) hunit
    dsimp [A, B, y]
    rw [show (i : R) * (i : R) * (1 + -P ^ 2 * ((i : R)⁻¹ ^ 2)) =
        (i : R) * (i : R) - P^2 * (((i : R) * (i : R)⁻¹)^2) by ring]
    rw [hmul_inv]
    ring
  have hprodA : (∏ i ∈ s, A i) = (∏ i ∈ s, B i) * (∏ i ∈ s, (1 + y i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact hA i hi
  have hsum_y : (∑ i ∈ s, y i) = 0 := by
    dsimp [y, P, R, s]
    rw [← Finset.mul_sum]
    have hbase := zmod_p3r_halfUnitRange_inv_sq_sum_base_sq_zero (p := p) (r := r) hp hp5 hr
    calc
      -(p^r : ZMod (p ^ (3*r))) ^ 2 *
          (∑ i ∈ halfUnitRange p r, (i : ZMod (p ^ (3*r)))⁻¹ ^ 2)
          = -(((p^r : ZMod (p ^ (3*r))) ^ 2) *
          (∑ i ∈ halfUnitRange p r, (i : ZMod (p ^ (3*r)))⁻¹ ^ 2)) := by ring_nf
      _ = 0 := by rw [hbase, neg_zero]
  have hdsq : (-P^2)^2 = 0 := by
    dsimp [P, R]
    rw [show (-(p^r : ZMod (p ^ (3*r))) ^ 2) ^ 2 =
      (p^r : ZMod (p ^ (3*r))) ^ 4 by ring_nf]
    exact zmod_p3r_base_pow_four_eq_zero p r hr
  have hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → y a * y b = 0 := by
    intro a ha b hb hab
    dsimp [y]
    rw [show (-P ^ 2 * ((a : R)⁻¹ ^ 2)) * (-P ^ 2 * ((b : R)⁻¹ ^ 2)) =
      (-P^2)^2 * (((a : R)⁻¹ ^ 2) * ((b : R)⁻¹ ^ 2)) by ring]
    rw [hdsq, zero_mul]
  have hyprod : (∏ i ∈ s, (1 + y i)) = 1 :=
    prod_one_add_eq_one_of_sum_and_pairwise_mul_zero s y hsum_y hpair
  calc
    halfBlockR p r 1 * halfBlockRMinus p r
        = (∏ i ∈ s, A i) := by
          dsimp [halfBlockR, halfBlockRMinus, A, s, R, P]
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i hi
          ring_nf
    _ = (∏ i ∈ s, B i) * (∏ i ∈ s, (1 + y i)) := hprodA
    _ = ∏ i ∈ s, B i := by rw [hyprod, mul_one]
    _ = (halfBlockR p r 0)^2 := by
          dsimp [halfBlockR, B, s, R, P]
          rw [show (∏ i ∈ halfUnitRange p r, (i : ZMod (p ^ (3*r))) * (i : ZMod (p ^ (3*r)))) =
              (∏ i ∈ halfUnitRange p r, (i : ZMod (p ^ (3*r)))) *
              (∏ i ∈ halfUnitRange p r, (i : ZMod (p ^ (3*r)))) by
            rw [← Finset.prod_mul_distrib]]
          ring_nf

/-- If the Morley product gives the minus block as the stated power of four times
`halfBlockR p r 0`, then the base half-block congruence follows by cancelling
the unit `halfBlockR p r 0`. -/
theorem halfBlockR_base_of_morley_product {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r)
    (hminus : halfBlockRMinus p r =
      (4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1)) * halfBlockR p r 0) :
    (4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1)) * halfBlockR p r 1 = halfBlockR p r 0 := by
  let c : ZMod (p^(3*r)) := (4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1))
  let h0 : ZMod (p^(3*r)) := halfBlockR p r 0
  let h1 : ZMod (p^(3*r)) := halfBlockR p r 1
  have hprod := halfBlockR_one_mul_minus_eq_zero_sq (p := p) (r := r) hp hp5 hr
  have hprod' : h1 * (c * h0) = h0 ^ 2 := by
    dsimp [h1, h0, c]
    rwa [hminus] at hprod
  have hcancel : (c * h1) * h0 = h0 * h0 := by
    rw [show (c * h1) * h0 = h1 * (c * h0) by ring_nf]
    rw [hprod']
    ring_nf
  have hunit0 : IsUnit h0 := by
    dsimp [h0]
    exact halfBlockR_zero_isUnit (p := p) (r := r) hp hr
  have hmain : c * h1 = h0 := by
    exact IsUnit.mul_right_cancel hunit0 hcancel
  simpa [c, h1, h0] using hmain

end TempHalfBlockR



/- Flattened helper code from TempPrimePowerLehmerProduct.lean -/

open scoped BigOperators

namespace TempPrimePowerLehmerProduct

open TempHalfBlockR

/-- The base `P = p^r` cubed vanishes in `ZMod (p^(3*r))`. -/
lemma zmod_p3r_base_pow_three_eq_zero (p r : ℕ) (hr : 0 < r) :
    ((p^r : ZMod (p^(3*r))) ^ 3) = 0 := by
  have hnat : (p^r)^3 = p^(3*r) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [show ((p^r : ZMod (p^(3*r))) ^ 3) = (((p^r)^3 : ℕ) : ZMod (p^(3*r))) by
    norm_num [Nat.cast_pow]]
  rw [hnat]
  exact CharP.cast_eq_zero (ZMod (p^(3*r))) (p^(3*r))

/-- A second-order product expansion specialized to the prime-power Lehmer half range.

This is the algebraic expansion of
`∏ (1 - (p^r/i)/2 - (p^r/i)^2/4)` in `ZMod ((p^r)^3)`.  The constants are
written as powers of `(2 : R)⁻¹`; equivalently the quadratic term is
`(p^r)^2 * (A^2/8 - 3*H2/8)` when `2` is a unit. -/
theorem primePowerLehmer_truncated_expansion {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    let R := ZMod (p^(3*r))
    let P : R := (p^r : R)
    let s := halfUnitRange p r
    let u : ℕ → R := fun i => ((i : R)⁻¹)
    let c : R := (2 : R)⁻¹
    ∏ i ∈ s, (1 + (-P * c * u i - P^2 * c^2 * (u i)^2)) =
      1 - P * c * (∑ i ∈ s, u i) +
        P^2 * c^3 * ((∑ i ∈ s, u i)^2 - (3 : R) * (∑ i ∈ s, (u i)^2)) := by
  intro R P s u c
  have hP3 : P ^ 3 = 0 := by
    dsimp [P, R]
    exact zmod_p3r_base_pow_three_eq_zero p r hr
  have hP4 : P ^ 4 = 0 := by
    calc
      P ^ 4 = P * P ^ 3 := by ring
      _ = 0 := by rw [hP3, mul_zero]
  have h2unit : IsUnit (2 : R) := by
    dsimp [R]
    exact TempShiftedProductGeneralHarmonic.zmod_two_unit_pow hp hp5
  have hc2 : c * (2 : R) = 1 := by
    dsimp [c]
    rw [mul_comm]
    exact ZMod.mul_inv_of_unit (2 : R) h2unit
  have hc2' : (2 : R) * c = 1 := by
    rw [mul_comm]
    exact hc2
  have hc_sq : c^2 = (2 : R) * c^3 := by
    calc
      c^2 = 1 * c^2 := by ring
      _ = ((2 : R) * c) * c^2 := by rw [hc2']
      _ = (2 : R) * c^3 := by ring
  let y : ℕ → R := fun i => -P * c * u i - P^2 * c^2 * (u i)^2
  have htrunc := TempProductExpansion.prod_one_add_eq_truncated_of_cube_zero
      (s := s) (P := P) (z := fun i => -c * u i - P * c^2 * (u i)^2) hP3
  have hy_eq : ∀ i, P * (-c * u i - P * c^2 * (u i)^2) = y i := by
    intro i
    dsimp [y]
    ring
  have hprod_trunc : ∏ i ∈ s, (1 + y i) =
      1 + ∑ i ∈ s, y i + ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i := by
    simpa [hy_eq] using htrunc
  have hsum_y : (∑ i ∈ s, y i) = -P * c * (∑ i ∈ s, u i) - P^2 * c^2 * (∑ i ∈ s, (u i)^2) := by
    dsimp [y]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  let E2 : R := ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, u i
  have hpair_y : (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i) = P^2 * c^2 * E2 := by
    dsimp [E2]
    calc
      (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i)
          = ∑ t ∈ s.powersetCard 2, P^2 * c^2 * (∏ i ∈ t, u i) := by
            apply Finset.sum_congr rfl
            intro t ht
            have hcard : t.card = 2 := (Finset.mem_powersetCard.mp ht).2
            rcases Finset.card_eq_two.mp hcard with ⟨a, b, hab, rfl⟩
            simp [hab, y]
            rw [show (-P * c * u a - P ^ 2 * c ^ 2 * u a ^ 2) *
                (-P * c * u b - P ^ 2 * c ^ 2 * u b ^ 2) =
                P^2 * c^2 * (u a * u b) +
                  P^3 * (c^3 * (u a * u b^2 + u a^2 * u b)) +
                  P^4 * (c^4 * (u a^2 * u b^2)) by ring]
            rw [hP3, hP4]
            ring
      _ = P^2 * c^2 * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, u i) := by
            rw [Finset.mul_sum]
  have hsym := TempPairInvSum.elemSymTwo_square_identity s u
  have htwoE : (2 : R) * E2 = (∑ i ∈ s, u i)^2 - (∑ i ∈ s, (u i)^2) := by
    dsimp [E2]
    rw [hsym]
    ring
  have hE2 : E2 = c * ((∑ i ∈ s, u i)^2 - (∑ i ∈ s, (u i)^2)) := by
    calc
      E2 = (c * (2 : R)) * E2 := by rw [hc2]; ring
      _ = c * ((2 : R) * E2) := by ring
      _ = c * ((∑ i ∈ s, u i)^2 - (∑ i ∈ s, (u i)^2)) := by rw [htwoE]
  calc
    ∏ i ∈ s, (1 + (-P * c * u i - P^2 * c^2 * (u i)^2))
        = ∏ i ∈ s, (1 + y i) := by rfl
    _ = 1 + ∑ i ∈ s, y i + ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i := hprod_trunc
    _ = 1 - P * c * (∑ i ∈ s, u i) +
        P^2 * c^3 * ((∑ i ∈ s, u i)^2 - (3 : R) * (∑ i ∈ s, (u i)^2)) := by
          rw [hsum_y, hpair_y, hE2]
          let A : R := ∑ i ∈ s, u i
          let H : R := ∑ i ∈ s, (u i)^2
          change 1 + (-P * c * A - P^2 * c^2 * H) + P^2 * c^2 * (c * (A^2 - H)) =
            1 - P * c * A + P^2 * c^3 * (A^2 - (3 : R) * H)
          rw [show P^2 * c^2 * (c * (A^2 - H)) = P^2 * c^3 * (A^2 - H) by ring]
          rw [hc_sq]
          ring


/-- The same expansion for the actual Lehmer product
`∏ (1 - x_i) * (1 - x_i/2)⁻¹`, with `x_i = p^r/i`, in `ZMod (p^(3*r))`.
Here `x_i/2` is represented as `(p^r) * (2⁻¹) * i⁻¹`. -/
theorem primePowerLehmer_product_expansion {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    let R := ZMod (p^(3*r))
    let P : R := (p^r : R)
    let s := halfUnitRange p r
    let u : ℕ → R := fun i => ((i : R)⁻¹)
    let c : R := (2 : R)⁻¹
    ∏ i ∈ s, ((1 - P * u i) * (1 - P * c * u i)⁻¹) =
      1 - P * c * (∑ i ∈ s, u i) +
        P^2 * c^3 * ((∑ i ∈ s, u i)^2 - (3 : R) * (∑ i ∈ s, (u i)^2)) := by
  intro R P s u c
  have hP3 : P ^ 3 = 0 := by
    dsimp [P, R]
    exact zmod_p3r_base_pow_three_eq_zero p r hr
  have h2unit : IsUnit (2 : R) := by
    dsimp [R]
    exact TempShiftedProductGeneralHarmonic.zmod_two_unit_pow hp hp5
  have hc2 : c * (2 : R) = 1 := by
    dsimp [c]
    rw [mul_comm]
    exact ZMod.mul_inv_of_unit (2 : R) h2unit
  have hc2' : (2 : R) * c = 1 := by
    rw [mul_comm]
    exact hc2
  have hc_lin : c = (2 : R) * c^2 := by
    calc
      c = 1 * c := by ring
      _ = ((2 : R) * c) * c := by rw [hc2']
      _ = (2 : R) * c^2 := by ring
  have hfac : ∀ i ∈ s,
      (1 - P * u i) * (1 - P * c * u i)⁻¹ =
        1 + (-P * c * u i - P^2 * c^2 * (u i)^2) := by
    intro i hi
    let z : R := P * c * u i
    have hz3 : z^3 = 0 := by
      dsimp [z]
      rw [show (P * c * u i)^3 = P^3 * (c^3 * (u i)^3) by ring]
      rw [hP3, zero_mul]
    have hinv : (1 - z)⁻¹ = 1 + z + z^2 := by
      apply ZMod.inv_eq_of_mul_eq_one
      rw [show (1 - z) * (1 + z + z^2) = 1 - z^3 by ring]
      rw [hz3, sub_zero]
    dsimp [z] at hinv
    rw [hinv]
    have hc_minus : c - 1 = -c := by
      rw [← hc2']
      ring
    have hc2_minus : c^2 - c = -c^2 := by
      rw [show c^2 - c = c * (c - 1) by ring, hc_minus]
      ring
    rw [show (1 - P * u i) * (1 + P * c * u i + (P * c * u i)^2) =
        1 + P * (c - 1) * u i + P^2 * (c^2 - c) * (u i)^2 - P^3 * c^2 * (u i)^3 by ring]
    rw [hc_minus, hc2_minus, hP3]
    ring
  calc
    ∏ i ∈ s, ((1 - P * u i) * (1 - P * c * u i)⁻¹)
        = ∏ i ∈ s, (1 + (-P * c * u i - P^2 * c^2 * (u i)^2)) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hfac i hi
    _ = 1 - P * c * (∑ i ∈ s, u i) +
        P^2 * c^3 * ((∑ i ∈ s, u i)^2 - (3 : R) * (∑ i ∈ s, (u i)^2)) := by
          dsimp [R, P, s, u, c]
          simpa using primePowerLehmer_truncated_expansion (p := p) (r := r) hp hp5 hr

end TempPrimePowerLehmerProduct


/- Flattened helper code from TempPrimePowerLehmerExact.lean -/

open scoped BigOperators

namespace TempPrimePowerLehmerExact

open TempHalfBlockR TempShiftedProductGeneralHarmonic

/-- Upper-half reduced residues modulo `p^r`. -/
def upperHalfUnitRange (p r : ℕ) : Finset ℕ :=
  (Finset.Ico (((p^r - 1) / 2) + 1) (p^r)).filter (fun i => ¬ p ∣ i)

lemma unitRange_eq_half_union_upper {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    unitRange p r = halfUnitRange p r ∪ upperHalfUnitRange p r := by
  let m := p^r
  let h := (m - 1) / 2
  have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
  have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
  ext i
  rw [unitRange, halfUnitRange, upperHalfUnitRange]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
  dsimp [m, h] at hm ⊢
  constructor
  · intro hi
    rcases hi with ⟨⟨hi1, him⟩, hnot⟩
    by_cases hih : i < (p ^ r - 1) / 2 + 1
    · exact Or.inl ⟨⟨hi1, hih⟩, hnot⟩
    · exact Or.inr ⟨⟨by omega, him⟩, hnot⟩
  · intro hi
    rcases hi with hi | hi
    · rcases hi with ⟨⟨hi1, hih⟩, hnot⟩
      exact ⟨⟨hi1, by omega⟩, hnot⟩
    · rcases hi with ⟨⟨hlo, him⟩, hnot⟩
      exact ⟨⟨by omega, him⟩, hnot⟩

lemma half_disjoint_upper (p r : ℕ) :
    Disjoint (halfUnitRange p r) (upperHalfUnitRange p r) := by
  rw [Finset.disjoint_left]
  intro i hi hu
  rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hi
  rw [upperHalfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hu
  omega

lemma upper_product_eq_neg_half_product {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ x ∈ upperHalfUnitRange p r, x) =
      ∏ i ∈ halfUnitRange p r, (p^r - i) := by
  classical
  rw [Finset.prod_subtype (upperHalfUnitRange p r) (by intro x; rfl) (fun x => x)]
  rw [Finset.prod_subtype (halfUnitRange p r) (by intro x; rfl) (fun i => p^r - i)]
  let e := halfUnitRangeNegEquiv p r hp hp5 hr
  exact (Fintype.prod_equiv e
    (fun a : {i // i ∈ halfUnitRange p r} => p^r - (a : ℕ))
    (fun a : {i // i ∈ upperHalfUnitRange p r} => (a : ℕ))
    (by intro a; rfl)).symm

lemma two_mul_half_mem_unitRange {p r i : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hi : i ∈ halfUnitRange p r) : 2 * i ∈ unitRange p r := by
  let m := p^r
  let h := (m - 1) / 2
  have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
  have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
  rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hi
  rw [unitRange, Finset.mem_filter, Finset.mem_Ico]
  rcases hi with ⟨⟨hi1, hih⟩, hnot⟩
  constructor
  · constructor
    · omega
    · dsimp [m, h] at hm hih ⊢; omega
  · intro hd
    exact hnot ((hp.dvd_or_dvd hd).resolve_left (TempShiftedProductGeneralHarmonic.not_dvd_two_of_five_le hp5))

lemma n_sub_two_mul_half_mem_unitRange {p r i : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r)
    (hi : i ∈ halfUnitRange p r) : p^r - 2 * i ∈ unitRange p r := by
  let m := p^r
  let h := (m - 1) / 2
  have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
  have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
  rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hi
  rw [unitRange, Finset.mem_filter, Finset.mem_Ico]
  rcases hi with ⟨⟨hi1, hih⟩, hnot⟩
  constructor
  · constructor
    · dsimp [m, h] at hm hih ⊢; omega
    · dsimp [m, h] at hm hih ⊢; omega
  · intro hd
    have hpm : p ∣ p^r := TempHalfBlockR.prime_dvd_pow_self_of_pos p r hr
    have hle : 2 * i ≤ p^r := by dsimp [m, h] at hm hih ⊢; omega
    have hsub : p ∣ p^r - (p^r - 2 * i) := Nat.dvd_sub hpm hd
    have hsubeq : p^r - (p^r - 2 * i) = 2 * i := Nat.sub_sub_self hle
    have hpi2 : p ∣ 2 * i := by rwa [hsubeq] at hsub
    have hpi : p ∣ i := (hp.dvd_or_dvd hpi2).resolve_left (TempShiftedProductGeneralHarmonic.not_dvd_two_of_five_le hp5)
    exact hnot hpi

lemma unitRange_eq_evenOdd_images {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    unitRange p r =
      (halfUnitRange p r).image (fun i => 2 * i) ∪
      (halfUnitRange p r).image (fun i => p^r - 2 * i) := by
  classical
  let m := p^r
  let h := (m - 1) / 2
  have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
  have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
  ext x
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · intro hx
    have hx' := hx
    rw [unitRange, Finset.mem_filter, Finset.mem_Ico] at hx'
    rcases hx' with ⟨⟨hx1, hxm⟩, hxnotp⟩
    by_cases heven : Even x
    · rcases heven with ⟨i, hi_even⟩
      have hx_eq : x = 2 * i := by omega
      left
      refine ⟨i, ?_, hx_eq.symm⟩
      rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico]
      constructor
      · constructor
        · omega
        · dsimp [m, h] at hm hxm hx_eq ⊢; omega
      · intro hd
        exact hxnotp (by rw [hx_eq]; exact dvd_mul_of_dvd_right hd 2)
    · have hoddx : Odd x := Nat.not_even_iff_odd.mp heven
      have hEvenSub : Even (m - x) := by
        apply Nat.not_odd_iff_even.mp
        intro hbad
        have hsumeven : Even ((m - x) + x) := hbad.add_odd hoddx
        have hxle : x ≤ m := le_of_lt hxm
        have hmx : (m - x) + x = m := Nat.sub_add_cancel hxle
        rw [hmx] at hsumeven
        exact (Nat.not_even_iff_odd.mpr hodd) hsumeven
      rcases hEvenSub with ⟨i, hi⟩
      right
      refine ⟨i, ?_, ?_⟩
      · rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico]
        have hi_eq : 2 * i = m - x := by simpa [two_mul] using hi.symm
        constructor
        · constructor
          · dsimp [m, h] at hm hi_eq hx1 hxm ⊢; omega
          · dsimp [m, h] at hm hi_eq hx1 hxm ⊢; omega
        · intro hd
          have hpm : p ∣ m := by dsimp [m]; exact TempHalfBlockR.prime_dvd_pow_self_of_pos p r hr
          have hp2i : p ∣ 2 * i := dvd_mul_of_dvd_right hd 2
          have hpx : p ∣ m - 2 * i := Nat.dvd_sub hpm hp2i
          have hx_eq : m - 2 * i = x := by omega
          exact hxnotp (by rwa [hx_eq] at hpx)
      · dsimp [m] at hi ⊢
        omega
  · intro hx
    rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact two_mul_half_mem_unitRange (p := p) (r := r) (i := i) hp hp5 hi
    · exact n_sub_two_mul_half_mem_unitRange (p := p) (r := r) (i := i) hp hp5 hr hi


lemma evenOdd_images_disjoint {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    Disjoint ((halfUnitRange p r).image (fun i => 2 * i))
      ((halfUnitRange p r).image (fun i => p^r - 2 * i)) := by
  classical
  let m := p^r
  let h := (m - 1) / 2
  have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
  have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_image] at hx hy
  rcases hx with ⟨a, ha, hxa⟩
  rcases hy with ⟨b, hb, hxb⟩
  have haI := ha
  have hbI := hb
  simp [halfUnitRange] at haI hbI
  dsimp [m, h] at hm haI hbI hxa hxb
  omega

lemma prod_even_image {p r : ℕ} :
    (∏ x ∈ (halfUnitRange p r).image (fun i => 2 * i), x) =
      ∏ i ∈ halfUnitRange p r, 2 * i := by
  classical
  rw [Finset.prod_image]
  intro a ha b hb hab
  dsimp at hab
  omega

lemma prod_odd_image {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∏ x ∈ (halfUnitRange p r).image (fun i => p^r - 2 * i), x) =
      ∏ i ∈ halfUnitRange p r, (p^r - 2 * i) := by
  classical
  rw [Finset.prod_image]
  intro a ha b hb hab
  let m := p^r
  let h := (m - 1) / 2
  have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
  have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
  have haI := ha
  have hbI := hb
  simp [halfUnitRange] at haI hbI
  dsimp [m, h] at hm haI hbI hab
  omega

lemma prod_two_mul_half (p r : ℕ) :
    (∏ i ∈ halfUnitRange p r, 2 * i) =
      2 ^ (halfUnitRange p r).card * (∏ i ∈ halfUnitRange p r, i) := by
  calc
    (∏ i ∈ halfUnitRange p r, 2 * i) = (∏ i ∈ halfUnitRange p r, 2) * (∏ i ∈ halfUnitRange p r, i) := by
      rw [← Finset.prod_mul_distrib]
    _ = 2 ^ (halfUnitRange p r).card * (∏ i ∈ halfUnitRange p r, i) := by simp

/-- Exact natural-number product identity behind the prime-power Lehmer product. -/
theorem upper_product_eq_two_pow_card_mul_odd_product {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ i ∈ halfUnitRange p r, (p^r - i)) =
      2 ^ (halfUnitRange p r).card * (∏ i ∈ halfUnitRange p r, (p^r - 2 * i)) := by
  classical
  let L := ∏ i ∈ halfUnitRange p r, i
  let U := ∏ i ∈ halfUnitRange p r, (p^r - i)
  let O := ∏ i ∈ halfUnitRange p r, (p^r - 2 * i)
  have hfull₁ : (∏ x ∈ unitRange p r, x) = L * U := by
    dsimp [L, U]
    rw [unitRange_eq_half_union_upper (p := p) (r := r) hp hp5]
    rw [Finset.prod_union (half_disjoint_upper p r)]
    rw [upper_product_eq_neg_half_product (p := p) (r := r) hp hp5 hr]
  have hfull₂ : (∏ x ∈ unitRange p r, x) = (2 ^ (halfUnitRange p r).card * L) * O := by
    dsimp [L, O]
    rw [unitRange_eq_evenOdd_images (p := p) (r := r) hp hp5 hr]
    rw [Finset.prod_union (evenOdd_images_disjoint (p := p) (r := r) hp hp5)]
    rw [prod_even_image (p := p) (r := r)]
    rw [prod_odd_image (p := p) (r := r) hp hp5]
    rw [prod_two_mul_half]
  have hLpos : 0 < L := by
    dsimp [L]
    apply Finset.prod_pos
    intro i hi
    rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hi
    omega
  apply Nat.mul_left_cancel hLpos
  calc
    L * U = ∏ x ∈ unitRange p r, x := hfull₁.symm
    _ = (2 ^ (halfUnitRange p r).card * L) * O := hfull₂
    _ = L * (2 ^ (halfUnitRange p r).card * O) := by ring

/-- The lower half of the reduced residues has half of Euler's totient cardinality. -/
theorem two_mul_card_halfUnitRange {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    2 * (halfUnitRange p r).card = p^(r-1) * (p-1) := by
  classical
  haveI : NeZero (p^r) := ⟨pow_ne_zero r hp.ne_zero⟩

  have hupper_card : (upperHalfUnitRange p r).card = (halfUnitRange p r).card := by
    have h := Fintype.card_congr (halfUnitRangeNegEquiv p r hp hp5 hr)
    simpa [upperHalfUnitRange] using h.symm
  have hsplit : (unitRange p r).card = 2 * (halfUnitRange p r).card := by
    rw [unitRange_eq_half_union_upper (p := p) (r := r) hp hp5]
    rw [Finset.card_union_of_disjoint (half_disjoint_upper p r)]
    rw [hupper_card]
    ring
  have hunit_card : (unitRange p r).card = Fintype.card (ZMod (p^r))ˣ := by
    have h := Fintype.card_congr (unitRangeEquivUnits p r hp hr)
    simpa using h
  have htot : Fintype.card (ZMod (p^r))ˣ = p^(r-1) * (p-1) := by
    rw [ZMod.card_units_eq_totient]
    exact Nat.totient_prime_pow hp hr
  rw [← hsplit, hunit_card, htot]


lemma unitRange_natCast_isUnit_p3r {p r j : ℕ} (hp : Nat.Prime p) (hj : j ∈ unitRange p r) :
    IsUnit (j : ZMod (p^(3*r))) := by
  rw [ZMod.isUnit_iff_coprime]
  have hnot : ¬ p ∣ j := (Finset.mem_filter.mp hj).2
  exact hp.coprime_pow_of_not_dvd hnot

lemma odd_factor_isUnit_p3r {p r i : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r)
    (hi : i ∈ halfUnitRange p r) :
    IsUnit ((p^r : ZMod (p^(3*r))) - (2 * i : ZMod (p^(3*r)))) := by
  have hj := n_sub_two_mul_half_mem_unitRange (p := p) (r := r) (i := i) hp hp5 hr hi
  have hunit : IsUnit ((p^r - 2 * i : ℕ) : ZMod (p^(3*r))) :=
    unitRange_natCast_isUnit_p3r (p := p) (r := r) hp hj
  convert hunit using 1
  have hi' := hi
  rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hi'
  have hle : 2 * i ≤ p^r := by
    let m := p^r
    let h := (m - 1) / 2
    have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
    have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
    dsimp [m, h] at hm hi' ⊢
    omega
  rw [Nat.cast_sub hle]
  norm_num [Nat.cast_mul]

lemma halfUnitRange_le_base {p r i : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hi : i ∈ halfUnitRange p r) : i ≤ p^r := by
  let m := p^r
  let h := (m - 1) / 2
  have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
  have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
  have hi' := hi
  rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hi'
  dsimp [m, h] at hm hi' ⊢
  omega

lemma two_mul_halfUnitRange_le_base {p r i : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hi : i ∈ halfUnitRange p r) : 2 * i ≤ p^r := by
  let m := p^r
  let h := (m - 1) / 2
  have hodd : Odd m := by dsimp [m]; exact prime_pow_odd hp hp5
  have hm : m = 2 * h + 1 := by dsimp [h]; exact pow_odd_decomp hodd
  have hi' := hi
  rw [halfUnitRange, Finset.mem_filter, Finset.mem_Ico] at hi'
  dsimp [m, h] at hm hi' ⊢
  omega

lemma zmod_inv_two_mul_natCast {p r i : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r)
    (hi : i ∈ halfUnitRange p r) :
    let R := ZMod (p^(3*r))
    (((2 * i : ℕ) : R)⁻¹) = (2 : R)⁻¹ * ((i : R)⁻¹) := by
  intro R
  let c : R := (2 : R)⁻¹
  have h2unit : IsUnit (2 : R) := by
    dsimp [R]
    exact zmod_two_unit_pow hp hp5
  have hiunit : IsUnit (i : R) := by
    dsimp [R]
    simpa using TempHalfBlockR.shifted_factor_isUnit (p := p) (r := r) (q := 0) (i := i) hp hr hi
  have h2c : (2 : R) * c = 1 := by
    dsimp [c]
    exact ZMod.mul_inv_of_unit (2 : R) h2unit
  have hic : (i : R) * (i : R)⁻¹ = 1 := ZMod.mul_inv_of_unit (i : R) hiunit
  apply ZMod.inv_eq_of_mul_eq_one
  dsimp [R, c]
  rw [show ((2 * i : ℕ) : R) = (2 : R) * (i : R) by norm_num [Nat.cast_mul]]
  rw [show ((2 : R) * (i : R)) * ((2 : R)⁻¹ * (i : R)⁻¹) =
      ((2 : R) * (2 : R)⁻¹) * ((i : R) * (i : R)⁻¹) by ring]
  rw [ZMod.mul_inv_of_unit (2 : R) h2unit, hic]
  ring

/-- Per-factor bridge from the expanded Lehmer factor to the exact product factor. -/
theorem primePowerLehmer_factor_bridge {p r i : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r)
    (hi : i ∈ halfUnitRange p r) :
    let R := ZMod (p^(3*r))
    let P : R := (p^r : R)
    (1 - P * ((i : R)⁻¹)) * (1 - P * (((2 * i : ℕ) : R)⁻¹))⁻¹ =
      (2 : R) * (((p^r - i : ℕ) : R)) * ((((p^r - 2 * i : ℕ) : R))⁻¹) := by
  intro R P
  let a : R := (i : R)
  let b : R := ((2 * i : ℕ) : R)
  let N : R := ((p^r - i : ℕ) : R)
  let D : R := ((p^r - 2 * i : ℕ) : R)
  have haunit : IsUnit a := by
    dsimp [a, R]
    simpa using TempHalfBlockR.shifted_factor_isUnit (p := p) (r := r) (q := 0) (i := i) hp hr hi
  have hbunit : IsUnit b := by
    dsimp [b, R]
    have hj := two_mul_half_mem_unitRange (p := p) (r := r) (i := i) hp hp5 hi
    exact unitRange_natCast_isUnit_p3r (p := p) (r := r) hp hj
  have hDunit : IsUnit D := by
    dsimp [D, R]
    have hj := n_sub_two_mul_half_mem_unitRange (p := p) (r := r) (i := i) hp hp5 hr hi
    exact unitRange_natCast_isUnit_p3r (p := p) (r := r) hp hj
  have hle_i : i ≤ p^r := halfUnitRange_le_base (p := p) (r := r) (i := i) hp hp5 hi
  have hle_2i : 2 * i ≤ p^r := two_mul_halfUnitRange_le_base (p := p) (r := r) (i := i) hp hp5 hi
  have hN : N = P - a := by
    dsimp [N, P, a, R]
    rw [Nat.cast_sub hle_i]
    simp [Nat.cast_pow]
  have hD : D = P - b := by
    dsimp [D, P, b, R]
    rw [Nat.cast_sub hle_2i]
    simp [Nat.cast_pow, Nat.cast_mul]
  have h_ai : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a haunit
  have h_bi : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit b hbunit
  have h_Di : D * D⁻¹ = 1 := ZMod.mul_inv_of_unit D hDunit
  have hnum : 1 - P * a⁻¹ = -N * a⁻¹ := by
    rw [hN]
    rw [show -(P - a) * a⁻¹ = -P * a⁻¹ + a * a⁻¹ by ring]
    rw [h_ai]
    ring
  have hden : 1 - P * b⁻¹ = -D * b⁻¹ := by
    rw [hD]
    rw [show -(P - b) * b⁻¹ = -P * b⁻¹ + b * b⁻¹ by ring]
    rw [h_bi]
    ring
  have hden_inv : (1 - P * b⁻¹)⁻¹ = -b * D⁻¹ := by
    rw [hden]
    apply ZMod.inv_eq_of_mul_eq_one
    have h_b_left : b⁻¹ * b = 1 := by rw [mul_comm, h_bi]
    calc
      (-D * b⁻¹) * (-b * D⁻¹)
          = (D * D⁻¹) * (b⁻¹ * b) := by ring
      _ = 1 := by rw [h_Di, h_b_left]; ring
  have hb_cast : b = (2 : R) * a := by
    dsimp [b, a, R]
    norm_num [Nat.cast_mul]
  have h_a_left : a⁻¹ * a = 1 := by rw [mul_comm, h_ai]
  calc
    (1 - P * ((i : R)⁻¹)) * (1 - P * (((2 * i : ℕ) : R)⁻¹))⁻¹
        = (1 - P * a⁻¹) * (1 - P * b⁻¹)⁻¹ := by rfl
    _ = (-N * a⁻¹) * (-b * D⁻¹) := by rw [hnum, hden_inv]
    _ = (2 : R) * N * D⁻¹ := by
      rw [hb_cast]
      rw [show (-N * a⁻¹) * (-((2 : R) * a) * D⁻¹) =
          (2 : R) * N * D⁻¹ * (a⁻¹ * a) by ring]
      rw [h_a_left]
      ring
    _ = (2 : R) * (((p^r - i : ℕ) : R)) * ((((p^r - 2 * i : ℕ) : R))⁻¹) := by rfl


/-- A compile-tested ZMod product form of the exact identity.  This is the
post-algebraic form of the requested Lehmer product. -/
theorem primePowerLehmer_simplified_product_identity {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    let R := ZMod (p^(3*r))
    ∏ i ∈ halfUnitRange p r,
      ((2 : R) * ((p^r - i : ℕ) : R) * ((p^r - 2 * i : ℕ) : R)⁻¹) =
        (2 : R)^(p^(r-1) * (p-1)) := by
  intro R
  let S := halfUnitRange p r
  let U : R := ∏ i ∈ S, ((p^r - i : ℕ) : R)
  let O : R := ∏ i ∈ S, ((p^r - 2 * i : ℕ) : R)
  have hU : U = (2 : R) ^ S.card * O := by
    dsimp [U, O, R, S]
    rw [← Nat.cast_prod, ← Nat.cast_prod]
    simpa [Nat.cast_mul, Nat.cast_pow] using congrArg (fun n : ℕ => (n : R))
      (upper_product_eq_two_pow_card_mul_odd_product (p := p) (r := r) hp hp5 hr)
  have hOunit : IsUnit O := by
    dsimp [O]
    apply Finset.prod_induction
    · intro a b ha hb; exact ha.mul hb
    · exact isUnit_one
    · intro i hi
      have hj := n_sub_two_mul_half_mem_unitRange (p := p) (r := r) (i := i) hp hp5 hr hi
      exact unitRange_natCast_isUnit_p3r (p := p) (r := r) hp hj
  let OinvProd : R := ∏ i ∈ S, (((p^r - 2 * i : ℕ) : R)⁻¹)
  have hprod : (∏ i ∈ S, ((2 : R) * ((p^r - i : ℕ) : R) * ((p^r - 2 * i : ℕ) : R)⁻¹)) =
      (2 : R)^S.card * U * OinvProd := by
    dsimp [U, OinvProd]
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_mul_distrib]
    simp [Nat.mul_comm]
  have hOcancel : O * OinvProd = 1 := by
    dsimp [O, OinvProd]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    have hj := n_sub_two_mul_half_mem_unitRange (p := p) (r := r) (i := i) hp hp5 hr hi
    have hu := unitRange_natCast_isUnit_p3r (p := p) (r := r) hp hj
    exact ZMod.mul_inv_of_unit _ hu
  calc
    (∏ i ∈ S, ((2 : R) * ((p^r - i : ℕ) : R) * ((p^r - 2 * i : ℕ) : R)⁻¹))
        = (2 : R)^S.card * U * OinvProd := hprod
    _ = (2 : R)^S.card * ((2 : R)^S.card * O) * OinvProd := by rw [hU]
    _ = (2 : R)^(2 * S.card) := by
      rw [show (2 : R)^S.card * ((2 : R)^S.card * O) * OinvProd =
          ((2 : R)^S.card * (2 : R)^S.card) * (O * OinvProd) by ring]
      rw [hOcancel]
      rw [mul_one, ← pow_add]
      congr 1
      omega
    _ = (2 : R)^(p^(r-1) * (p-1)) := by
      rw [two_mul_card_halfUnitRange (p := p) (r := r) hp hp5 hr]





/-- Exact identity for the original Lehmer product, after the per-factor bridge. -/
theorem primePowerLehmer_product_identity {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    let R := ZMod (p^(3*r))
    let P : R := (p^r : R)
    ∏ i ∈ halfUnitRange p r,
      ((1 - P * ((i : R)⁻¹)) * (1 - P * (((2 * i : ℕ) : R)⁻¹))⁻¹) =
        (2 : R)^(p^(r-1) * (p-1)) := by
  intro R P
  calc
    ∏ i ∈ halfUnitRange p r,
      ((1 - P * ((i : R)⁻¹)) * (1 - P * (((2 * i : ℕ) : R)⁻¹))⁻¹)
        = ∏ i ∈ halfUnitRange p r,
          ((2 : R) * (((p^r - i : ℕ) : R)) * ((((p^r - 2 * i : ℕ) : R))⁻¹)) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact primePowerLehmer_factor_bridge (p := p) (r := r) (i := i) hp hp5 hr hi
    _ = (2 : R)^(p^(r-1) * (p-1)) := by
      simpa using primePowerLehmer_simplified_product_identity (p := p) (r := r) hp hp5 hr

/-- The expansion side from `TempPrimePowerLehmerProduct` evaluates to the same
power of two, using the exact product identity above. -/
theorem primePowerLehmer_expansion_eq_two_pow {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    let R := ZMod (p^(3*r))
    let P : R := (p^r : R)
    let s := halfUnitRange p r
    let u : ℕ → R := fun i => ((i : R)⁻¹)
    let c : R := (2 : R)⁻¹
    1 - P * c * (∑ i ∈ s, u i) +
        P^2 * c^3 * ((∑ i ∈ s, u i)^2 - (3 : R) * (∑ i ∈ s, (u i)^2)) =
      (2 : R)^(p^(r-1) * (p-1)) := by
  intro R P s u c
  have hprod_exp := TempPrimePowerLehmerProduct.primePowerLehmer_product_expansion
      (p := p) (r := r) hp hp5 hr
  have hprod_id := primePowerLehmer_product_identity (p := p) (r := r) hp hp5 hr
  have hprod_same :
      (∏ i ∈ s, ((1 - P * u i) * (1 - P * c * u i)⁻¹)) =
      (∏ i ∈ halfUnitRange p r,
        ((1 - P * ((i : R)⁻¹)) * (1 - P * (((2 * i : ℕ) : R)⁻¹))⁻¹)) := by
    dsimp [s, u, c]
    apply Finset.prod_congr rfl
    intro i hi
    have hinv2 := zmod_inv_two_mul_natCast (p := p) (r := r) (i := i) hp hp5 hr hi
    dsimp [R] at hinv2
    rw [hinv2]
    rw [show 1 - P * (2 : R)⁻¹ * ((i : R)⁻¹) =
        1 - P * ((2 : R)⁻¹ * ((i : R)⁻¹)) by ring]
  calc
    1 - P * c * (∑ i ∈ s, u i) +
        P^2 * c^3 * ((∑ i ∈ s, u i)^2 - (3 : R) * (∑ i ∈ s, (u i)^2))
        = ∏ i ∈ s, ((1 - P * u i) * (1 - P * c * u i)⁻¹) := by
          exact hprod_exp.symm
    _ = ∏ i ∈ halfUnitRange p r,
        ((1 - P * ((i : R)⁻¹)) * (1 - P * (((2 * i : ℕ) : R)⁻¹))⁻¹) := hprod_same
    _ = (2 : R)^(p^(r-1) * (p-1)) := hprod_id


end TempPrimePowerLehmerExact


/- Flattened helper code from TempPrimePowerMorleyProductInput.lean -/

open scoped BigOperators

namespace TempPrimePowerMorleyProductInput

open TempHalfBlockR

/-- The direct second-order expansion of `∏ (1 - P/i)` on the prime-power half range. -/
theorem primePowerMorley_T_expansion {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    let R := ZMod (p^(3*r))
    let P : R := (p^r : R)
    let s := halfUnitRange p r
    let u : ℕ → R := fun i => ((i : R)⁻¹)
    let c : R := (2 : R)⁻¹
    ∏ i ∈ s, (1 - P * u i) =
      1 - P * (∑ i ∈ s, u i) +
        P^2 * c * ((∑ i ∈ s, u i)^2 - (∑ i ∈ s, (u i)^2)) := by
  intro R P s u c
  have hP3 : P ^ 3 = 0 := by
    dsimp [P, R]
    exact TempPrimePowerLehmerProduct.zmod_p3r_base_pow_three_eq_zero p r hr
  have h2unit : IsUnit (2 : R) := by
    dsimp [R]
    exact TempShiftedProductGeneralHarmonic.zmod_two_unit_pow hp hp5
  have hc2 : c * (2 : R) = 1 := by
    dsimp [c]
    rw [mul_comm]
    exact ZMod.mul_inv_of_unit (2 : R) h2unit
  let A : R := ∑ i ∈ s, u i
  let S2 : R := ∑ i ∈ s, (u i)^2
  let E2 : R := ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, u i
  have htrunc := TempProductExpansion.prod_one_add_eq_truncated_of_cube_zero
      (s := s) (P := -P) (z := u) (hP := by
        rw [show (-P)^3 = -(P^3) by ring, hP3, neg_zero])
  have hleft : (∏ i ∈ s, (1 - P * u i)) = ∏ i ∈ s, (1 + (-P) * u i) := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  have hlin : (∑ i ∈ s, (-P) * u i) = -P * A := by
    dsimp [A]
    rw [← Finset.mul_sum]
  have hquad : (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, (-P) * u i) = P^2 * E2 := by
    dsimp [E2]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have htcard : t.card = 2 := (Finset.mem_powersetCard.mp ht).2
    calc
      (∏ i ∈ t, (-P) * u i) = (∏ _i ∈ t, (-P)) * (∏ i ∈ t, u i) := by
        rw [← Finset.prod_mul_distrib]
      _ = (-P) ^ t.card * (∏ i ∈ t, u i) := by
        rw [Finset.prod_const]
      _ = P^2 * (∏ i ∈ t, u i) := by
        rw [htcard]
        ring
  have hsym := TempPairInvSum.elemSymTwo_square_identity s u
  have htwoE : (2 : R) * E2 = A^2 - S2 := by
    dsimp [A, S2, E2]
    rw [hsym]
    ring
  have hE2 : E2 = c * (A^2 - S2) := by
    calc
      E2 = (c * (2 : R)) * E2 := by rw [hc2]; ring
      _ = c * ((2 : R) * E2) := by ring
      _ = c * (A^2 - S2) := by rw [htwoE]
  calc
    ∏ i ∈ s, (1 - P * u i)
        = ∏ i ∈ s, (1 + (-P) * u i) := hleft
    _ = 1 + ∑ i ∈ s, (-P) * u i +
          ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, (-P) * u i := htrunc
    _ = 1 - P * A + P^2 * c * (A^2 - S2) := by
      rw [hlin, hquad, hE2]
      ring

/-- The Morley product `T = ∏ (1 - P/i)` is the square of the Lehmer product expansion. -/
theorem primePowerMorley_T_eq_lehmer_expansion_sq {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    let R := ZMod (p^(3*r))
    let P : R := (p^r : R)
    let s := halfUnitRange p r
    let u : ℕ → R := fun i => ((i : R)⁻¹)
    let c : R := (2 : R)⁻¹
    ∏ i ∈ s, (1 - P * u i) =
      (1 - P * c * (∑ i ∈ s, u i) +
        P^2 * c^3 * ((∑ i ∈ s, u i)^2 - (3 : R) * (∑ i ∈ s, (u i)^2)))^2 := by
  intro R P s u c
  let A : R := ∑ i ∈ s, u i
  let S2 : R := ∑ i ∈ s, (u i)^2
  have hP3 : P ^ 3 = 0 := by
    dsimp [P, R]
    exact TempPrimePowerLehmerProduct.zmod_p3r_base_pow_three_eq_zero p r hr
  have hP4 : P ^ 4 = 0 := by
    calc
      P^4 = P * P^3 := by ring
      _ = 0 := by rw [hP3, mul_zero]
  have h2unit : IsUnit (2 : R) := by
    dsimp [R]
    exact TempShiftedProductGeneralHarmonic.zmod_two_unit_pow hp hp5
  have h2c : (2 : R) * c = 1 := by
    dsimp [c]
    exact ZMod.mul_inv_of_unit (2 : R) h2unit
  have hquadc : c^2 + (2 : R) * c^3 = c := by
    calc
      c^2 + (2 : R) * c^3 = c^2 + ((2 : R) * c) * c^2 := by ring
      _ = c^2 + 1 * c^2 := by rw [h2c]
      _ = ((2 : R) * c) * c := by ring
      _ = c := by rw [h2c]; ring
  have hS2zero : P^2 * S2 = 0 := by
    dsimp [P, S2, s, u, R]
    exact zmod_p3r_halfUnitRange_inv_sq_sum_base_sq_zero (p := p) (r := r) hp hp5 hr
  have hT := primePowerMorley_T_expansion (p := p) (r := r) hp hp5 hr
  dsimp [R, P, s, u, c] at hT
  change (∏ i ∈ s, (1 - P * u i)) =
      (1 - P * c * A + P^2 * c^3 * (A^2 - (3 : R) * S2))^2
  calc
    ∏ i ∈ s, (1 - P * u i)
        = 1 - P * A + P^2 * c * (A^2 - S2) := by
          simpa [A, S2] using hT
    _ = 1 - P * A + P^2 * c * A^2 := by
          rw [show P^2 * c * (A^2 - S2) = P^2 * c * A^2 - c * (P^2 * S2) by ring]
          rw [hS2zero]
          ring
    _ = (1 - P * c * A + P^2 * c^3 * A^2)^2 := by
          rw [show (1 - P * c * A + P^2 * c^3 * A^2)^2 =
            1 - ((2 : R) * c) * P * A + P^2 * (c^2 + (2 : R) * c^3) * A^2 +
              P^3 * (-((2 : R) * c^4 * A^3)) + P^4 * (c^6 * A^4) by ring]
          rw [hP3, hP4, h2c, hquadc]
          ring
    _ = (1 - P * c * A + P^2 * c^3 * (A^2 - (3 : R) * S2))^2 := by
          have hinside : 1 - P * c * A + P^2 * c^3 * (A^2 - (3 : R) * S2) =
              1 - P * c * A + P^2 * c^3 * A^2 := by
            rw [show P^2 * c^3 * (A^2 - (3 : R) * S2) =
              P^2 * c^3 * A^2 - ((3 : R) * c^3) * (P^2 * S2) by ring]
            rw [hS2zero]
            ring
          rw [hinside]

/-- The prime-power Morley product in normalized form. -/
theorem primePowerMorley_T_eq_four_pow {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    let R := ZMod (p^(3*r))
    let P : R := (p^r : R)
    let s := halfUnitRange p r
    let u : ℕ → R := fun i => ((i : R)⁻¹)
    ∏ i ∈ s, (1 - P * u i) = (4 : R)^(p^(r-1) * (p-1)) := by
  intro R P s u
  let c : R := (2 : R)⁻¹
  let A : R := ∑ i ∈ s, u i
  let S2 : R := ∑ i ∈ s, (u i)^2
  let phi := p^(r-1) * (p-1)
  have hTE := primePowerMorley_T_eq_lehmer_expansion_sq (p := p) (r := r) hp hp5 hr
  -- Use the requested Lehmer product expansion together with the exact identity `E = 2^phi`.
  have hprod_exp := TempPrimePowerLehmerProduct.primePowerLehmer_product_expansion
      (p := p) (r := r) hp hp5 hr
  have hprod_id := TempPrimePowerLehmerExact.primePowerLehmer_product_identity
      (p := p) (r := r) hp hp5 hr
  dsimp [R, P, s, u, c] at hTE hprod_exp hprod_id
  have hprod_same :
      (∏ i ∈ s, ((1 - P * u i) * (1 - P * c * u i)⁻¹)) =
      (∏ i ∈ halfUnitRange p r,
        ((1 - P * ((i : R)⁻¹)) * (1 - P * (((2 * i : ℕ) : R)⁻¹))⁻¹)) := by
    dsimp [s, u, c]
    apply Finset.prod_congr rfl
    intro i hi
    have hinv2 := TempPrimePowerLehmerExact.zmod_inv_two_mul_natCast
      (p := p) (r := r) (i := i) hp hp5 hr hi
    dsimp [R] at hinv2
    rw [hinv2]
    rw [show 1 - P * (2 : R)⁻¹ * ((i : R)⁻¹) =
        1 - P * ((2 : R)⁻¹ * ((i : R)⁻¹)) by ring]
  have hE : 1 - P * c * A + P^2 * c^3 * (A^2 - (3 : R) * S2) = (2 : R)^phi := by
    calc
      1 - P * c * A + P^2 * c^3 * (A^2 - (3 : R) * S2)
          = ∏ i ∈ s, ((1 - P * u i) * (1 - P * c * u i)⁻¹) := by
            simpa [A, S2, phi] using hprod_exp.symm
      _ = ∏ i ∈ halfUnitRange p r,
          ((1 - P * ((i : R)⁻¹)) * (1 - P * (((2 * i : ℕ) : R)⁻¹))⁻¹) := hprod_same
      _ = (2 : R)^phi := by
            simpa [phi] using hprod_id
  change (∏ i ∈ s, (1 - P * u i)) = (4 : R)^phi
  calc
    ∏ i ∈ s, (1 - P * u i)
        = (1 - P * c * A + P^2 * c^3 * (A^2 - (3 : R) * S2))^2 := by
          simpa [A, S2, phi] using hTE
    _ = ((2 : R)^phi)^2 := by rw [hE]
    _ = (4 : R)^phi := by
          rw [pow_two]
          rw [show (4 : R) = (2 : R) * (2 : R) by norm_num]
          rw [mul_pow]

/-- The requested prime-power Morley product input for `halfBlockR_base_of_morley_product`. -/
theorem halfBlockRMinus_eq_four_pow_mul_halfBlockR_zero {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    halfBlockRMinus p r =
      (4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1)) * halfBlockR p r 0 := by
  let R := ZMod (p^(3*r))
  let P : R := (p^r : R)
  let s := halfUnitRange p r
  let u : ℕ → R := fun i => ((i : R)⁻¹)
  let phi := p^(r-1) * (p-1)
  have hT := primePowerMorley_T_eq_four_pow (p := p) (r := r) hp hp5 hr
  dsimp [R, P, s, u] at hT
  have hfac : ∀ i ∈ s, ((i : R) - P) = (i : R) * (1 - P * u i) := by
    intro i hi
    have hunit : IsUnit (i : R) := by
      dsimp [R]
      simpa using shifted_factor_isUnit (p := p) (r := r) (q := 0) (i := i) hp hr hi
    have hmul_inv : (i : R) * (i : R)⁻¹ = 1 := ZMod.mul_inv_of_unit (i : R) hunit
    dsimp [u]
    rw [show (i : R) * (1 - P * (i : R)⁻¹) = (i : R) - P * ((i : R) * (i : R)⁻¹) by ring]
    rw [hmul_inv]
    ring
  calc
    halfBlockRMinus p r
        = (∏ i ∈ s, ((i : R) - P)) := by rfl
    _ = (∏ i ∈ s, (i : R)) * (∏ i ∈ s, (1 - P * u i)) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i hi
          exact hfac i hi
    _ = (∏ i ∈ s, (i : R)) * (4 : R)^phi := by
          rw [hT]
    _ = (4 : R)^phi * halfBlockR p r 0 := by
          dsimp [halfBlockR, R, s, P, phi]
          ring


/-- Alias with the requested product-input wording. -/
theorem primePowerMorley_product_input {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    halfBlockRMinus p r =
      (4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1)) * halfBlockR p r 0 := by
  exact halfBlockRMinus_eq_four_pow_mul_halfBlockR_zero (p := p) (r := r) hp hp5 hr

/-- The base half-block congruence, with the Morley-product input discharged. -/
theorem halfBlockR_base_from_primePowerLehmer {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1)) * halfBlockR p r 1 = halfBlockR p r 0 := by
  exact halfBlockR_base_of_morley_product (p := p) (r := r) hp hp5 hr
    (halfBlockRMinus_eq_four_pow_mul_halfBlockR_zero (p := p) (r := r) hp hp5 hr)

end TempPrimePowerMorleyProductInput


/- Flattened helper code from TempPrimePowerHalfBlockRIteration.lean -/

open scoped BigOperators

namespace TempHalfBlockR

/-- Every shifted prime-power half-block is a unit. -/
theorem halfBlockR_isUnit {p r q : ℕ} (hp : Nat.Prime p) (hr : 0 < r) :
    IsUnit (halfBlockR p r q) := by
  dsimp [halfBlockR]
  apply Finset.prod_induction
  · intro a b ha hb
    exact IsUnit.mul ha hb
  · exact isUnit_one
  · intro i hi
    simpa using shifted_factor_isUnit (p := p) (r := r) (q := q) (i := i) hp hr hi

/-- One-step prime-power shifted half-block congruence. -/
theorem halfBlockR_step {p r : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (q : ℕ) :
    (4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1)) * halfBlockR p r (q+1) =
      halfBlockR p r q := by
  let M : ZMod (p^(3*r)) := (4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1))
  let B : ℕ → ZMod (p^(3*r)) := fun n => halfBlockR p r n
  have hbase : M * B 1 = B 0 := by
    dsimp [M, B]
    exact TempPrimePowerMorleyProductInput.halfBlockR_base_from_primePowerLehmer
      (p := p) (r := r) hp hp5 hr
  have hshift : B (q+1) * B 0 = B q * B 1 := by
    dsimp [B]
    exact halfBlockR_q_independent (p := p) (r := r) (q := q) hp hp5 hr
  have hmul : (M * B (q+1)) * B 1 = B q * B 1 := by
    calc
      (M * B (q+1)) * B 1 = B (q+1) * (M * B 1) := by ring
      _ = B (q+1) * B 0 := by rw [hbase]
      _ = B q * B 1 := hshift
  have hunitB1 : IsUnit (B 1) := by
    dsimp [B]
    exact halfBlockR_isUnit (p := p) (r := r) (q := 1) hp hr
  have hcancel := hunitB1.mul_left_inj.mp hmul
  simpa [M, B] using hcancel

/-- Division-free iteration theorem for prime-power shifted half-blocks. -/
theorem halfBlockR_iterate_division_free {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (N q : ℕ) :
    ((4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1)))^N * halfBlockR p r (q+N) =
      halfBlockR p r q := by
  let M : ZMod (p^(3*r)) := (4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1))
  let B : ℕ → ZMod (p^(3*r)) := fun n => halfBlockR p r n
  change M^N * B (q+N) = B q
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hstep : M * B (q + N + 1) = B (q + N) := by
        dsimp [M, B]
        exact halfBlockR_step (p := p) (r := r) hp hp5 hr (q + N)
      calc
        M^(N+1) * B (q + (N+1))
            = M^N * (M * B (q + N + 1)) := by
                rw [pow_succ]
                ring_nf
        _ = M^N * B (q + N) := by rw [hstep]
        _ = B q := ih

/-- Iteration theorem for prime-power shifted half-blocks, with the power of `4`
stated as `N * (p^(r-1)*(p-1))`. -/
theorem halfBlockR_iterate_division_free_four_pow {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (N q : ℕ) :
    (4 : ZMod (p^(3*r)))^(N * (p^(r-1) * (p-1))) * halfBlockR p r (q+N) =
      halfBlockR p r q := by
  have h := halfBlockR_iterate_division_free (p := p) (r := r) hp hp5 hr N q
  rw [Nat.mul_comm N (p^(r-1) * (p-1))]

  change (4 : ZMod (p^(3*r)))^((p^(r-1) * (p-1)) * N) * halfBlockR p r (q+N) =
      halfBlockR p r q
  have hpow : (4 : ZMod (p^(3*r)))^((p^(r-1) * (p-1)) * N) =
      ((4 : ZMod (p^(3*r)))^(p^(r-1) * (p-1)))^N := by
    exact pow_mul (4 : ZMod (p^(3*r))) (p^(r-1) * (p-1)) N
  rw [hpow]
  exact h

/-- Ratio form of the prime-power half-block iteration theorem. -/
theorem halfBlockR_iterate_ratio {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (N q : ℕ) :
    (4 : ZMod (p^(3*r)))^(N * (p^(r-1) * (p-1))) * halfBlockR p r (q+N) *
        (halfBlockR p r q)⁻¹ = 1 := by
  have h := halfBlockR_iterate_division_free_four_pow (p := p) (r := r) hp hp5 hr N q
  rw [h]
  exact ZMod.mul_inv_of_unit (halfBlockR p r q)
    (halfBlockR_isUnit (p := p) (r := r) (q := q) hp hr)

/-- The especially useful shift by `3*n`, in division-free form. -/
theorem halfBlockR_shift_three_mul_division_free {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (n q : ℕ) :
    (4 : ZMod (p^(3*r)))^((3*n) * (p^(r-1) * (p-1))) * halfBlockR p r (q+3*n) =
      halfBlockR p r q := by
  exact halfBlockR_iterate_division_free_four_pow (p := p) (r := r) hp hp5 hr (3*n) q

/-- The especially useful shift by `3*n`, in ratio form. -/
theorem halfBlockR_shift_three_mul_ratio {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (n q : ℕ) :
    (4 : ZMod (p^(3*r)))^((3*n) * (p^(r-1) * (p-1))) * halfBlockR p r (q+3*n) *
        (halfBlockR p r q)⁻¹ = 1 := by
  exact halfBlockR_iterate_ratio (p := p) (r := r) hp hp5 hr (3*n) q

end TempHalfBlockR


/- Flattened helper code from TempOddChosen.lean -/

open scoped BigOperators Real

namespace TempOddChosen

open TempShiftedProductGeneralHarmonic

/-- In the final file, the temporary sequence is definitionally the submitted sequence. -/
noncomputable abbrev aTemp (n : ℕ) : ℝ := a n

/-- The numerator in the odd-index factorial formula. -/
def OddNum (n : ℕ) : ℕ :=
  4 ^ (3 * n) * Nat.factorial ((9 * n - 1) / 2) * Nat.factorial (2 * n)

/-- The denominator in the odd-index factorial formula. -/
def OddDen (n : ℕ) : ℕ :=
  Nat.factorial ((3 * n - 1) / 2) * Nat.factorial (4 * n) * Nat.factorial n

lemma OddDen_pos (n : ℕ) : 0 < OddDen n := by
  unfold OddDen
  positivity

/-- Complete unit-block product, in the namespace/import chain compatible with `TempHalfBlockR`. -/
def U (C m p r : ℕ) : ℕ :=
  ∏ q ∈ Finset.range (C * m), ∏ i ∈ unitRange p r, (q * p^r + i)

/-- Base complete unit-block product. -/
def W (p r : ℕ) : ℕ :=
  ∏ i ∈ unitRange p r, i

lemma odd_q9_eq_q3_add (n : ℕ) (hn : Odd n) :
    (9 * n - 1) / 2 = (3 * n - 1) / 2 + 3 * n := by
  rcases hn with ⟨k, rfl⟩
  omega

/-- The p-free odd-branch balance after the exact factorial decompositions are reduced to
complete unit blocks and the two half-blocks.  The hypotheses `hU...` are precisely the
complete-block shifted-product facts (proved in the even standalone development, but not
import-compatible with the current half-block iteration files because both are standalone copies).
The nontrivial odd-only part is the `halfBlockR` shift by `3*n`, which is discharged here by
`TempHalfBlockR.halfBlockR_shift_three_mul_division_free`. -/
lemma odd_pfree_balance_from_complete_blocks {p r n : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n)
    (hU1q9 : (U 1 ((9 * n - 1) / 2) p r : ZMod (p^(3*r))) =
      (W p r : ZMod (p^(3*r))) ^ (1 * ((9 * n - 1) / 2)))
    (hU2n : (U 2 n p r : ZMod (p^(3*r))) =
      (W p r : ZMod (p^(3*r))) ^ (2 * n))
    (hU1q3 : (U 1 ((3 * n - 1) / 2) p r : ZMod (p^(3*r))) =
      (W p r : ZMod (p^(3*r))) ^ (1 * ((3 * n - 1) / 2)))
    (hU4n : (U 4 n p r : ZMod (p^(3*r))) =
      (W p r : ZMod (p^(3*r))) ^ (4 * n))
    (hU1n : (U 1 n p r : ZMod (p^(3*r))) =
      (W p r : ZMod (p^(3*r))) ^ (1 * n)) :
    let R := ZMod (p^(3*r))
    let q3 := (3 * n - 1) / 2
    let q9 := (9 * n - 1) / 2
    ((4 : R) ^ ((3*n) * (p^(r-1) * (p-1)))) *
        (U 1 q9 p r : R) *
        (U 2 n p r : R) *
        TempHalfBlockR.halfBlockR p r q9 =
      (U 1 q3 p r : R) *
        (U 4 n p r : R) *
        (U 1 n p r : R) *
        TempHalfBlockR.halfBlockR p r q3 := by
  classical
  dsimp only
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let R := ZMod (p^(3*r))
  let w : R := (W p r : R)
  have hq : (9 * n - 1) / 2 = (3 * n - 1) / 2 + 3 * n := odd_q9_eq_q3_add n hn
  have hshift :
      (4 : R)^((3*n) * (p^(r-1) * (p-1))) *
          TempHalfBlockR.halfBlockR p r (((3*n - 1) / 2) + 3*n) =
        TempHalfBlockR.halfBlockR p r ((3*n - 1) / 2) := by
    dsimp [R]
    exact TempHalfBlockR.halfBlockR_shift_three_mul_division_free
      (p := p) (r := r) hp hp5 hr n ((3*n - 1) / 2)
  rw [hU1q9, hU2n, hU1q3, hU4n, hU1n]
  rw [hq]
  change (4 : R)^((3*n) * (p^(r-1) * (p-1))) *
          w ^ (1 * (((3*n - 1) / 2 + 3*n))) * w ^ (2 * n) *
          TempHalfBlockR.halfBlockR p r (((3*n - 1) / 2) + 3*n) =
        w ^ (1 * ((3*n - 1) / 2)) * w ^ (4 * n) * w ^ (1 * n) *
          TempHalfBlockR.halfBlockR p r ((3*n - 1) / 2)
  have hw : w ^ (1 * (((3*n - 1) / 2 + 3*n))) * w ^ (2 * n) =
      w ^ (1 * ((3*n - 1) / 2)) * w ^ (4 * n) * w ^ (1 * n) := by
    rw [← pow_add, ← pow_add]
    ring
  calc
    (4 : R)^((3*n) * (p^(r-1) * (p-1))) *
          w ^ (1 * (((3*n - 1) / 2 + 3*n))) * w ^ (2 * n) *
          TempHalfBlockR.halfBlockR p r (((3*n - 1) / 2) + 3*n)
        = (w ^ (1 * (((3*n - 1) / 2 + 3*n))) * w ^ (2 * n)) *
            ((4 : R)^((3*n) * (p^(r-1) * (p-1))) *
              TempHalfBlockR.halfBlockR p r (((3*n - 1) / 2) + 3*n)) := by ring
    _ = (w ^ (1 * ((3*n - 1) / 2)) * w ^ (4 * n) * w ^ (1 * n)) *
            TempHalfBlockR.halfBlockR p r ((3*n - 1) / 2) := by rw [hshift, hw]
    _ = w ^ (1 * ((3*n - 1) / 2)) * w ^ (4 * n) * w ^ (1 * n) *
          TempHalfBlockR.halfBlockR p r ((3*n - 1) / 2) := by ring

end TempOddChosen


/- Flattened helper code from TempOddHalfExact.lean -/

open scoped BigOperators

namespace TempOddHalfExact

/-- The unit representatives modulo `p^r`: positive integers below `p^r` not divisible by `p`. -/
def unitRange (p r : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (p^r)).filter (fun i => ¬ p ∣ i)

def U (C m p r : ℕ) : ℕ :=
  ∏ q ∈ Finset.range (C * m), ∏ i ∈ unitRange p r, (q * p^r + i)

def halfUnitRange (p r : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (((p^r - 1) / 2) + 1)).filter (fun i => ¬ p ∣ i)

def halfShiftBlock (M p r : ℕ) : ℕ :=
  ∏ i ∈ halfUnitRange p r, (M * p^r + i)


lemma pow_pred_mul_self (p r : ℕ) (hr : 0 < r) : p ^ (r - 1) * p = p ^ r := by
  rw [← Nat.pow_succ]
  congr 1
  omega

lemma factorial_block_product_aux (N p : ℕ) (hp0 : 0 < p) :
    Nat.factorial (N * p) = p ^ N * Nat.factorial N * (∏ q ∈ Finset.range N, ∏ i ∈ Finset.Ico 1 p, (q * p + i)) := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
      have hfac := Nat.factorial_mul_ascFactorial (N * p) p
      have hNp : N * p + p = (N + 1) * p := by ring
      rw [hNp] at hfac
      rw [← hfac]
      rw [ih]
      rw [Nat.ascFactorial_eq_prod_range]
      have hblock :
          (∏ x ∈ Finset.range p, (N * p + 1 + x)) =
            (∏ i ∈ Finset.Ico 1 p, (N * p + i)) * ((N + 1) * p) := by
        calc
          (∏ x ∈ Finset.range p, (N * p + 1 + x))
              = ∏ i ∈ Finset.Ico 1 (p + 1), (N * p + i) := by
                  rw [Finset.range_eq_Ico]
                  rw [← Finset.prod_Ico_add' (fun y : ℕ => N * p + y) 0 p 1]
                  apply Finset.prod_congr rfl
                  intro x hx
                  ring
          _ = (∏ i ∈ Finset.Ico 1 p, (N * p + i)) * (N * p + p) := by
                  rw [Finset.prod_Ico_succ_top]
                  omega
          _ = (∏ i ∈ Finset.Ico 1 p, (N * p + i)) * ((N + 1) * p) := by
                  rw [hNp]
      rw [hblock]
      rw [Finset.prod_range_succ]
      rw [Nat.factorial_succ]
      ring_nf

lemma prod_range_mul_decomp {α : Type*} [CommMonoid α]
    (N M : ℕ) (hM : 0 < M) (F : ℕ → α) :
    (∏ a ∈ Finset.range (N * M), F a) =
      ∏ q ∈ Finset.range N, ∏ b ∈ Finset.range M, F (q * M + b) := by
  classical
  calc
    (∏ a ∈ Finset.range (N * M), F a)
        = ∏ x ∈ (Finset.range N).product (Finset.range M), F (x.1 * M + x.2) := by
          symm
          refine Finset.prod_bij'
            (s := (Finset.range N).product (Finset.range M))
            (t := Finset.range (N * M))
            (f := fun x : ℕ × ℕ => F (x.1 * M + x.2))
            (g := F)
            (fun x _ => x.1 * M + x.2)
            (fun a _ => (a / M, a % M)) ?hi ?hj ?left ?right ?val
          · intro x hx
            rcases Finset.mem_product.mp hx with ⟨hq, hb⟩
            rw [Finset.mem_range] at hq hb ⊢
            have hlt1 : x.1 * M + x.2 < x.1 * M + M := Nat.add_lt_add_left hb _
            have hlt2 : x.1 * M + M = (x.1 + 1) * M := by ring
            have hle : (x.1 + 1) * M ≤ N * M := Nat.mul_le_mul_right M (Nat.succ_le_of_lt hq)
            exact lt_of_lt_of_le (by simpa [hlt2] using hlt1) hle
          · intro a ha
            rw [Finset.mem_range] at ha
            exact Finset.mem_product.mpr ⟨by simpa using (Nat.div_lt_iff_lt_mul hM).mpr ha, by simpa using Nat.mod_lt a hM⟩
          · intro x hx
            rcases Finset.mem_product.mp hx with ⟨hq, hb⟩
            rw [Finset.mem_range] at hq hb
            ext <;> simp only
            · rw [show (x.1 * M + x.2) / M = (x.2 + M * x.1) / M by rw [Nat.mul_comm, Nat.add_comm]]
              rw [Nat.add_mul_div_left _ _ hM]
              rw [Nat.div_eq_of_lt hb]
              simp
            · rw [show (x.1 * M + x.2) % M = (x.2 + M * x.1) % M by rw [Nat.mul_comm, Nat.add_comm]]
              rw [Nat.add_mul_mod_self_left]
              exact Nat.mod_eq_of_lt hb
          · intro a ha
            rw [Finset.mem_range] at ha
            simp only
            rw [Nat.mul_comm]
            simpa [Nat.add_comm] using Nat.mod_add_div a M
          · intro x hx
            rfl
    _ = ∏ q ∈ Finset.range N, ∏ b ∈ Finset.range M, F (q * M + b) := by
          exact Finset.prod_product (Finset.range N) (Finset.range M) (fun x : ℕ × ℕ => F (x.1 * M + x.2))

lemma unitRange_prod_decomp {α : Type*} [CommMonoid α]
    (p r : ℕ) (hp0 : 0 < p) (hr : 0 < r) (F : ℕ → α) :
    (∏ a ∈ Finset.range (p ^ (r - 1)), ∏ i ∈ Finset.Ico 1 p, F (a * p + i)) =
      ∏ i ∈ unitRange p r, F i := by
  classical
  let M := p ^ (r - 1)
  have hpow : M * p = p ^ r := by
    dsimp [M]
    exact pow_pred_mul_self p r hr
  calc
    (∏ a ∈ Finset.range (p ^ (r - 1)), ∏ i ∈ Finset.Ico 1 p, F (a * p + i))
        = ∏ x ∈ (Finset.range M).product (Finset.Ico 1 p), F (x.1 * p + x.2) := by
          dsimp [M]
          symm
          exact Finset.prod_product (Finset.range (p ^ (r - 1))) (Finset.Ico 1 p)
            (fun x : ℕ × ℕ => F (x.1 * p + x.2))
    _ = ∏ i ∈ unitRange p r, F i := by
        refine Finset.prod_bij'
          (s := (Finset.range M).product (Finset.Ico 1 p))
          (t := unitRange p r)
          (f := fun x : ℕ × ℕ => F (x.1 * p + x.2))
          (g := F)
          (fun x _ => x.1 * p + x.2)
          (fun b _ => (b / p, b % p)) ?hi ?hj ?left ?right ?val
        · intro x hx
          rcases Finset.mem_product.mp hx with ⟨ha, hi⟩
          rw [Finset.mem_range] at ha
          rw [Finset.mem_Ico] at hi
          rw [unitRange, Finset.mem_filter, Finset.mem_Ico]
          constructor
          · constructor
            · exact le_trans hi.1 (Nat.le_add_left x.2 (x.1 * p))
            · have hlt1 : x.1 * p + x.2 < x.1 * p + p := Nat.add_lt_add_left hi.2 _
              have hlt2 : x.1 * p + p = (x.1 + 1) * p := by ring
              have hle : (x.1 + 1) * p ≤ M * p := Nat.mul_le_mul_right p (Nat.succ_le_of_lt ha)
              have : x.1 * p + x.2 < M * p := lt_of_lt_of_le (by simpa [hlt2] using hlt1) hle
              simpa [hpow] using this
          · intro hdvd
            have hap : p ∣ x.1 * p := by exact ⟨x.1, by rw [Nat.mul_comm]⟩
            have hpi : p ∣ x.2 := (Nat.dvd_add_iff_right hap).mpr hdvd
            have hz : x.2 = 0 := Nat.eq_zero_of_dvd_of_lt hpi hi.2
            omega
        · intro b hb
          rw [unitRange, Finset.mem_filter, Finset.mem_Ico] at hb
          rcases hb with ⟨⟨hb1, hb2⟩, hbndvd⟩
          refine Finset.mem_product.mpr ⟨?_, ?_⟩
          · rw [Finset.mem_range]
            rw [Nat.div_lt_iff_lt_mul hp0]
            simpa [M, hpow] using hb2
          · rw [Finset.mem_Ico]
            constructor
            · have hne : b % p ≠ 0 := by
                intro hz
                exact hbndvd (Nat.dvd_of_mod_eq_zero hz)
              exact Nat.pos_of_ne_zero hne
            · exact Nat.mod_lt b hp0
        · intro x hx
          rcases Finset.mem_product.mp hx with ⟨ha, hi⟩
          rw [Finset.mem_Ico] at hi
          ext <;> simp only
          · rw [show (x.1 * p + x.2) / p = (x.2 + p * x.1) / p by rw [Nat.mul_comm, Nat.add_comm]]
            rw [Nat.add_mul_div_left _ _ hp0]
            rw [Nat.div_eq_of_lt hi.2]
            simp
          · rw [show (x.1 * p + x.2) % p = (x.2 + p * x.1) % p by rw [Nat.mul_comm, Nat.add_comm]]
            rw [Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt hi.2
        · intro b hb
          rw [unitRange, Finset.mem_filter, Finset.mem_Ico] at hb
          simp only
          rw [Nat.mul_comm]
          simpa [Nat.add_comm] using Nat.mod_add_div b p
        · intro x hx
          rfl

theorem factorial_block_decomposition (N p r : ℕ) (hp0 : 0 < p) (hr : 0 < r) :
    Nat.factorial (N * p^r) =
      p^(N * p^(r-1)) * Nat.factorial (N * p^(r-1)) *
        (∏ q ∈ Finset.range N, ∏ i ∈ unitRange p r, (q*p^r + i)) := by
  classical
  let M := p ^ (r - 1)
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos hp0
  have hpow : M * p = p ^ r := by
    dsimp [M]
    exact pow_pred_mul_self p r hr
  have haux := factorial_block_product_aux (N * M) p hp0
  have hprod :
      (∏ a ∈ Finset.range (N * M), ∏ i ∈ Finset.Ico 1 p, (a * p + i)) =
        (∏ q ∈ Finset.range N, ∏ i ∈ unitRange p r, (q * p^r + i)) := by
    calc
      (∏ a ∈ Finset.range (N * M), ∏ i ∈ Finset.Ico 1 p, (a * p + i))
          = ∏ q ∈ Finset.range N, ∏ b ∈ Finset.range M,
              ∏ i ∈ Finset.Ico 1 p, ((q * M + b) * p + i) := by
              exact prod_range_mul_decomp N M hMpos (fun a => ∏ i ∈ Finset.Ico 1 p, (a * p + i))
      _ = ∏ q ∈ Finset.range N, ∏ b ∈ Finset.range M,
              ∏ i ∈ Finset.Ico 1 p, (q * p^r + (b * p + i)) := by
              apply Finset.prod_congr rfl
              intro q hq
              apply Finset.prod_congr rfl
              intro b hb
              apply Finset.prod_congr rfl
              intro i hi
              rw [← hpow]
              ring
      _ = ∏ q ∈ Finset.range N, ∏ i ∈ unitRange p r, (q * p^r + i) := by
              apply Finset.prod_congr rfl
              intro q hq
              exact unitRange_prod_decomp p r hp0 hr (fun i => q * p^r + i)
  calc
    Nat.factorial (N * p^r)
        = Nat.factorial ((N * M) * p) := by
            congr 1
            rw [← hpow]
            ring
    _ = p ^ (N * M) * Nat.factorial (N * M) *
          (∏ a ∈ Finset.range (N * M), ∏ i ∈ Finset.Ico 1 p, (a * p + i)) := haux
    _ = p^(N * p^(r-1)) * Nat.factorial (N * p^(r-1)) *
          (∏ q ∈ Finset.range N, ∏ i ∈ unitRange p r, (q*p^r + i)) := by
            dsimp [M] at hprod ⊢
            rw [hprod]


/-- Arithmetic identity for odd factors. -/
lemma odd_mul_pred_div_two_decomp {A p : ℕ} (hA : Odd A) (hp : Odd p) :
    (A * p - 1) / 2 = ((A - 1) / 2) * p + (p - 1) / 2 := by
  rcases hA with ⟨a, rfl⟩
  rcases hp with ⟨b, rfl⟩
  have hprod : (2 * a + 1) * (2 * b + 1) = 2 * (a * (2 * b + 1) + b) + 1 := by ring
  have hnum : (2 * a + 1) * (2 * b + 1) - 1 = 2 * (a * (2 * b + 1) + b) := by
    rw [hprod]
    exact Nat.add_sub_cancel _ _
  calc
    (((2 * a + 1) * (2 * b + 1) - 1) / 2)
        = a * (2 * b + 1) + b := by
            rw [hnum]
            exact Nat.mul_div_right _ (by norm_num : 0 < 2)
    _ = ((2 * a + 1 - 1) / 2) * (2 * b + 1) + (2 * b + 1 - 1) / 2 := by
            rw [show 2 * a + 1 - 1 = 2 * a by omega]
            rw [show 2 * b + 1 - 1 = 2 * b by omega]
            rw [Nat.mul_div_right a (by norm_num : 0 < 2)]
            rw [Nat.mul_div_right b (by norm_num : 0 < 2)]

/-- Shifted product version of the usual one-step block decomposition. -/
lemma shifted_block_product_aux (K N p : ℕ) (hp0 : 0 < p) :
    (∏ x ∈ Finset.range (N * p), (K * p + 1 + x)) =
      p ^ N * (∏ a ∈ Finset.range N, (K + 1 + a)) *
        (∏ a ∈ Finset.range N, ∏ i ∈ Finset.Ico 1 p, ((K + a) * p + i)) := by
  classical
  calc
    (∏ x ∈ Finset.range (N * p), (K * p + 1 + x))
        = ∏ a ∈ Finset.range N, ∏ b ∈ Finset.range p, (K * p + 1 + (a * p + b)) := by
            exact prod_range_mul_decomp N p hp0 (fun x => K * p + 1 + x)
    _ = ∏ a ∈ Finset.range N,
          ((∏ i ∈ Finset.Ico 1 p, ((K + a) * p + i)) * (p * (K + 1 + a))) := by
          apply Finset.prod_congr rfl
          intro a ha
          calc
            (∏ b ∈ Finset.range p, (K * p + 1 + (a * p + b)))
                = ∏ i ∈ Finset.Ico 1 (p + 1), ((K + a) * p + i) := by
                    rw [Finset.range_eq_Ico]
                    rw [← Finset.prod_Ico_add' (fun y : ℕ => (K + a) * p + y) 0 p 1]
                    apply Finset.prod_congr rfl
                    intro x hx
                    ring
            _ = (∏ i ∈ Finset.Ico 1 p, ((K + a) * p + i)) * ((K + a) * p + p) := by
                    rw [Finset.prod_Ico_succ_top]
                    omega
            _ = (∏ i ∈ Finset.Ico 1 p, ((K + a) * p + i)) * (p * (K + 1 + a)) := by
                    congr 1
                    ring
    _ = (∏ a ∈ Finset.range N, p * (K + 1 + a)) *
          (∏ a ∈ Finset.range N, ∏ i ∈ Finset.Ico 1 p, ((K + a) * p + i)) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro a ha
          ring
    _ = p ^ N * (∏ a ∈ Finset.range N, (K + 1 + a)) *
          (∏ a ∈ Finset.range N, ∏ i ∈ Finset.Ico 1 p, ((K + a) * p + i)) := by
          rw [show (∏ a ∈ Finset.range N, p * (K + 1 + a)) =
              (∏ a ∈ Finset.range N, p) * (∏ a ∈ Finset.range N, (K + 1 + a)) by
                rw [Finset.prod_mul_distrib]]
          rw [Finset.prod_const]
          simp

/-- The leftover half-block product in a form obtained by one more ordinary `p`-block split. -/
def halfShiftBlockStep (M p r : ℕ) : ℕ :=
  (∏ a ∈ Finset.range ((p^(r-1) - 1) / 2),
      ∏ i ∈ Finset.Ico 1 p, (M * p^r + (a * p + i))) *
    (∏ i ∈ Finset.Ico 1 (((p - 1) / 2) + 1),
      (M * p^r + (((p^(r-1) - 1) / 2) * p + i)))


lemma block_prod_filter_decomp {α : Type*} [CommMonoid α]
    (J p : ℕ) (hp0 : 0 < p) (F : ℕ → α) :
    (∏ a ∈ Finset.range J, ∏ i ∈ Finset.Ico 1 p, F (a * p + i)) =
      ∏ n ∈ (Finset.Ico 1 (J * p + 1)).filter (fun n => ¬ p ∣ n), F n := by
  classical
  calc
    (∏ a ∈ Finset.range J, ∏ i ∈ Finset.Ico 1 p, F (a * p + i))
        = ∏ x ∈ (Finset.range J).product (Finset.Ico 1 p), F (x.1 * p + x.2) := by
            symm
            exact Finset.prod_product (Finset.range J) (Finset.Ico 1 p)
              (fun x : ℕ × ℕ => F (x.1 * p + x.2))
    _ = ∏ n ∈ (Finset.Ico 1 (J * p + 1)).filter (fun n => ¬ p ∣ n), F n := by
        refine Finset.prod_bij'
          (s := (Finset.range J).product (Finset.Ico 1 p))
          (t := (Finset.Ico 1 (J * p + 1)).filter (fun n => ¬ p ∣ n))
          (f := fun x : ℕ × ℕ => F (x.1 * p + x.2))
          (g := F)
          (fun x _ => x.1 * p + x.2)
          (fun n _ => (n / p, n % p)) ?hi ?hj ?left ?right ?val
        · intro x hx
          rcases Finset.mem_product.mp hx with ⟨ha, hi⟩
          rw [Finset.mem_range] at ha
          rw [Finset.mem_Ico] at hi
          rw [Finset.mem_filter, Finset.mem_Ico]
          constructor
          · constructor
            · exact le_trans hi.1 (Nat.le_add_left x.2 (x.1 * p))
            · have hlt1 : x.1 * p + x.2 < x.1 * p + p := Nat.add_lt_add_left hi.2 _
              have hlt2 : x.1 * p + p = (x.1 + 1) * p := by ring
              have hle : (x.1 + 1) * p ≤ J * p := Nat.mul_le_mul_right p (Nat.succ_le_of_lt ha)
              have : x.1 * p + x.2 < J * p := lt_of_lt_of_le (by simpa [hlt2] using hlt1) hle
              exact Nat.lt_succ_of_lt this
          · intro hdvd
            have hap : p ∣ x.1 * p := ⟨x.1, by rw [Nat.mul_comm]⟩
            have hpi : p ∣ x.2 := (Nat.dvd_add_iff_right hap).mpr hdvd
            have hz : x.2 = 0 := Nat.eq_zero_of_dvd_of_lt hpi hi.2
            omega
        · intro n hn
          rw [Finset.mem_filter, Finset.mem_Ico] at hn
          rcases hn with ⟨⟨hn1, hn2⟩, hnndvd⟩
          refine Finset.mem_product.mpr ⟨?_, ?_⟩
          · rw [Finset.mem_range]
            have hle : n ≤ J * p := Nat.lt_succ_iff.mp hn2
            have hne : n ≠ J * p := by
              intro hEq
              apply hnndvd
              rw [hEq]
              exact ⟨J, by rw [Nat.mul_comm]⟩
            have hnlt : n < J * p := by omega
            exact (Nat.div_lt_iff_lt_mul hp0).mpr hnlt
          · rw [Finset.mem_Ico]
            constructor
            · have hne : n % p ≠ 0 := by
                intro hz
                exact hnndvd (Nat.dvd_of_mod_eq_zero hz)
              exact Nat.pos_of_ne_zero hne
            · exact Nat.mod_lt n hp0
        · intro x hx
          rcases Finset.mem_product.mp hx with ⟨ha, hi⟩
          rw [Finset.mem_Ico] at hi
          ext <;> simp only
          · rw [show (x.1 * p + x.2) / p = (x.2 + p * x.1) / p by rw [Nat.mul_comm, Nat.add_comm]]
            rw [Nat.add_mul_div_left _ _ hp0]
            rw [Nat.div_eq_of_lt hi.2]
            simp
          · rw [show (x.1 * p + x.2) % p = (x.2 + p * x.1) % p by rw [Nat.mul_comm, Nat.add_comm]]
            rw [Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt hi.2
        · intro n hn
          rw [Finset.mem_filter, Finset.mem_Ico] at hn
          simp only
          rw [Nat.mul_comm]
          simpa [Nat.add_comm] using Nat.mod_add_div n p
        · intro x hx
          rfl

lemma tail_prod_filter_decomp {α : Type*} [CommMonoid α]
    (J p h : ℕ) (hhp : h < p) (F : ℕ → α) :
    (∏ i ∈ Finset.Ico 1 (h + 1), F (J * p + i)) =
      ∏ n ∈ (Finset.Ico (J * p + 1) (J * p + h + 1)).filter (fun n => ¬ p ∣ n), F n := by
  classical
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.zero_le h) hhp
  refine Finset.prod_bij'
    (s := Finset.Ico 1 (h + 1))
    (t := (Finset.Ico (J * p + 1) (J * p + h + 1)).filter (fun n => ¬ p ∣ n))
    (f := fun i : ℕ => F (J * p + i))
    (g := F)
    (fun i _ => J * p + i)
    (fun n _ => n - J * p) ?hi ?hj ?left ?right ?val
  · intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · constructor
      · change J * p + 1 ≤ J * p + i
        omega
      · change J * p + i < J * p + h + 1
        omega
    · intro hdvd
      have hJ : p ∣ J * p := ⟨J, by rw [Nat.mul_comm]⟩
      have hpi : p ∣ i := (Nat.dvd_add_iff_right hJ).mpr hdvd
      have hip : i < p := by omega
      have hz : i = 0 := Nat.eq_zero_of_dvd_of_lt hpi hip
      omega
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    rcases hn with ⟨⟨hn1, hn2⟩, hnndvd⟩
    rw [Finset.mem_Ico]
    have hleJ : J * p ≤ n := by omega
    constructor
    · exact Nat.le_sub_of_add_le (a := 1) (b := J * p) (c := n) (by simpa [Nat.add_comm] using hn1)
    · exact (Nat.sub_lt_iff_lt_add' hleJ).mpr (by simpa [Nat.add_assoc] using hn2)
  · intro i hi
    rw [Finset.mem_Ico] at hi
    change (J * p + i) - J * p = i
    exact Nat.add_sub_cancel_left _ _
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    rcases hn with ⟨⟨hn1, hn2⟩, hnndvd⟩
    have hleJ : J * p ≤ n := by omega
    change J * p + (n - J * p) = n
    exact Nat.add_sub_of_le hleJ
  · intro i hi
    rfl

/-- The one-step half block is exactly the filtered half unit block. -/
theorem halfShiftBlockStep_eq_halfShiftBlock
    (M p r : ℕ) (hpOdd : Odd p) (hr : 0 < r) :
    halfShiftBlockStep M p r = halfShiftBlock M p r := by
  classical
  let B := p^(r-1)
  let J := (B - 1) / 2
  let h := (p - 1) / 2
  have hBodd : Odd B := by
    dsimp [B]
    exact hpOdd.pow
  have hpow : B * p = p^r := by
    dsimp [B]
    exact pow_pred_mul_self p r hr
  have hH : (p^r - 1) / 2 = J * p + h := by
    dsimp [J, h, B]
    rw [← hpow]
    exact odd_mul_pred_div_two_decomp hBodd hpOdd
  have hp0 : 0 < p := by
    rcases hpOdd with ⟨k, rfl⟩
    omega
  have hhp : h < p := by
    dsimp [h]
    rcases hpOdd with ⟨k, rfl⟩
    omega
  let F : ℕ → ℕ := fun n => M * p^r + n
  have hfirst := block_prod_filter_decomp J p hp0 F
  have htail := tail_prod_filter_decomp J p h hhp F
  have hdisj : Disjoint
      ((Finset.Ico 1 (J * p + 1)).filter (fun n => ¬ p ∣ n))
      ((Finset.Ico (J * p + 1) (J * p + h + 1)).filter (fun n => ¬ p ∣ n)) := by
    rw [Finset.disjoint_left]
    intro n hnA hnB
    rw [Finset.mem_filter, Finset.mem_Ico] at hnA hnB
    omega
  have hunion : Finset.Ico 1 (J * p + h + 1) =
      Finset.Ico 1 (J * p + 1) ∪ Finset.Ico (J * p + 1) (J * p + h + 1) := by
    rw [Finset.Ico_union_Ico_eq_Ico]
    · exact Nat.succ_pos (J * p)
    · exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le h)) (J * p)
  calc
    halfShiftBlockStep M p r
        = (∏ n ∈ (Finset.Ico 1 (J * p + 1)).filter (fun n => ¬ p ∣ n), F n) *
          (∏ n ∈ (Finset.Ico (J * p + 1) (J * p + h + 1)).filter (fun n => ¬ p ∣ n), F n) := by
            dsimp [halfShiftBlockStep, F, J, h, B] at hfirst htail ⊢
            rw [hfirst, htail]
    _ = ∏ n ∈ ((Finset.Ico 1 (J * p + 1)).filter (fun n => ¬ p ∣ n)) ∪
            ((Finset.Ico (J * p + 1) (J * p + h + 1)).filter (fun n => ¬ p ∣ n)), F n := by
            rw [Finset.prod_union hdisj]
    _ = ∏ n ∈ (Finset.Ico 1 (J * p + h + 1)).filter (fun n => ¬ p ∣ n), F n := by
            rw [← Finset.filter_union]
            rw [← hunion]
    _ = halfShiftBlock M p r := by
            dsimp [halfShiftBlock, halfUnitRange, F]
            rw [hH]

lemma shifted_half_step (M p r : ℕ) (hpOdd : Odd p) (hr : 0 < r) :
    (∏ x ∈ Finset.range ((p^r - 1) / 2), (M * p^r + 1 + x)) =
      p ^ ((p^(r-1) - 1) / 2) *
        (∏ a ∈ Finset.range ((p^(r-1) - 1) / 2), (M * p^(r-1) + 1 + a)) *
          halfShiftBlockStep M p r := by
  classical
  let B := p^(r-1)
  let J := (B - 1) / 2
  let h := (p - 1) / 2
  have hBodd : Odd B := by
    dsimp [B]
    exact hpOdd.pow
  have hpow : B * p = p^r := by
    dsimp [B]
    exact pow_pred_mul_self p r hr
  have hp0 : 0 < p := by
    rcases hpOdd with ⟨k, rfl⟩
    omega
  have hH : (p^r - 1) / 2 = J * p + h := by
    dsimp [J, h, B]
    rw [← hpow]
    exact odd_mul_pred_div_two_decomp hBodd hpOdd
  calc
    (∏ x ∈ Finset.range ((p^r - 1) / 2), (M * p^r + 1 + x))
        = (∏ x ∈ Finset.range (J * p + h), (M * p^r + 1 + x)) := by rw [hH]
    _ = (∏ x ∈ Finset.range (J * p), (M * p^r + 1 + x)) *
          (∏ x ∈ Finset.range h, (M * p^r + 1 + (J * p + x))) := by
            rw [Finset.prod_range_add]
    _ = (p ^ J * (∏ a ∈ Finset.range J, (M * B + 1 + a)) *
          (∏ a ∈ Finset.range J, ∏ i ∈ Finset.Ico 1 p, ((M * B + a) * p + i))) *
          (∏ x ∈ Finset.range h, (M * p^r + 1 + (J * p + x))) := by
            rw [show M * p^r = (M * B) * p by rw [← hpow]; ring]
            rw [shifted_block_product_aux (K := M * B) (N := J) (p := p) hp0]
    _ = p ^ J * (∏ a ∈ Finset.range J, (M * B + 1 + a)) *
          ((∏ a ∈ Finset.range J, ∏ i ∈ Finset.Ico 1 p, (M * p^r + (a * p + i))) *
            (∏ i ∈ Finset.Ico 1 (h + 1), (M * p^r + (J * p + i)))) := by
            have hC :
                (∏ a ∈ Finset.range J, ∏ i ∈ Finset.Ico 1 p, ((M * B + a) * p + i)) =
                  (∏ a ∈ Finset.range J, ∏ i ∈ Finset.Ico 1 p, (M * p^r + (a * p + i))) := by
              apply Finset.prod_congr rfl
              intro a ha
              apply Finset.prod_congr rfl
              intro i hi
              rw [← hpow]
              ring
            have hD :
                (∏ x ∈ Finset.range h, (M * p^r + 1 + (J * p + x))) =
                  (∏ i ∈ Finset.Ico 1 (h + 1), (M * p^r + (J * p + i))) := by
              rw [Finset.range_eq_Ico]
              rw [← Finset.prod_Ico_add' (fun y : ℕ => M * p^r + (J * p + y)) 0 h 1]
              apply Finset.prod_congr rfl
              intro x hx
              ring
            rw [hC, hD]
            ring
    _ = p ^ ((p^(r-1) - 1) / 2) *
        (∏ a ∈ Finset.range ((p^(r-1) - 1) / 2), (M * p^(r-1) + 1 + a)) *
          halfShiftBlockStep M p r := by
          dsimp [B, J, h, halfShiftBlockStep]


/-- Exact odd half-factorial decomposition, with the final half block written in the
one-step form `halfShiftBlockStep`.  This is equivalent to the filtered
`halfUnitRange` product: it consists of the nonmultiples of `p` in the initial
half of the residue interval modulo `p^r`. -/
theorem odd_half_factorial_decomposition_step
    (C n p r : ℕ) (hpOdd : Odd p) (hr : 0 < r) (hCn : Odd (C * n)) :
    Nat.factorial ((C * n * p^r - 1) / 2) =
      p ^ ((C * n * p^(r-1) - 1) / 2) *
        Nat.factorial ((C * n * p^(r-1) - 1) / 2) *
          U 1 ((C * n - 1) / 2) p r *
            halfShiftBlockStep ((C * n - 1) / 2) p r := by
  classical
  let A := C * n
  let M := (A - 1) / 2
  let B := p^(r-1)
  let J := (B - 1) / 2
  let H := (p^r - 1) / 2
  have hp0 : 0 < p := by
    rcases hpOdd with ⟨k, rfl⟩
    omega
  have hBodd : Odd B := by
    dsimp [B]
    exact hpOdd.pow
  have hprodd : Odd (p^r) := hpOdd.pow
  have hpow : B * p = p^r := by
    dsimp [B]
    exact pow_pred_mul_self p r hr
  have htop : (A * p^r - 1) / 2 = M * p^r + H := by
    dsimp [M, H]
    exact odd_mul_pred_div_two_decomp hCn hprodd
  have hold : (A * B - 1) / 2 = M * B + J := by
    dsimp [M, J]
    exact odd_mul_pred_div_two_decomp hCn hBodd
  have harg_top : (C * n * p^r - 1) / 2 = M * p^r + H := by
    dsimp [A] at htop
    simpa [A, mul_assoc] using htop
  have harg_old : (C * n * p^(r-1) - 1) / 2 = M * B + J := by
    dsimp [A, B] at hold
    simpa [A, B, mul_assoc] using hold
  have hfac_top := Nat.factorial_mul_ascFactorial (M * p^r) H
  have hfac_old := Nat.factorial_mul_ascFactorial (M * B) J
  calc
    Nat.factorial ((C * n * p^r - 1) / 2)
        = Nat.factorial (M * p^r + H) := by rw [harg_top]
    _ = Nat.factorial (M * p^r) * (∏ x ∈ Finset.range H, (M * p^r + 1 + x)) := by
          rw [← hfac_top]
          rw [Nat.ascFactorial_eq_prod_range]
    _ = (p ^ (M * B) * Nat.factorial (M * B) *
          (∏ q ∈ Finset.range M, ∏ i ∈ unitRange p r, (q * p^r + i))) *
          (p ^ J * (∏ a ∈ Finset.range J, (M * B + 1 + a)) * halfShiftBlockStep M p r) := by
          rw [show M * p^r = M * p^r by rfl]
          rw [factorial_block_decomposition M p r hp0 hr]
          rw [show B = p^(r-1) by rfl]
          rw [shifted_half_step M p r hpOdd hr]
    _ = p ^ (M * B + J) * Nat.factorial (M * B + J) *
          (∏ q ∈ Finset.range M, ∏ i ∈ unitRange p r, (q * p^r + i)) *
            halfShiftBlockStep M p r := by
          rw [← hfac_old]
          rw [Nat.ascFactorial_eq_prod_range]
          rw [pow_add]
          ring
    _ = p ^ ((C * n * p^(r-1) - 1) / 2) *
        Nat.factorial ((C * n * p^(r-1) - 1) / 2) *
          U 1 ((C * n - 1) / 2) p r *
            halfShiftBlockStep ((C * n - 1) / 2) p r := by
          rw [harg_old]
          dsimp [M, A, U]
          simp [one_mul]

/-- Prime/`p ≥ 5` wrapper, matching the supercongruence context. -/
theorem odd_half_factorial_decomposition_step_prime_ge5
    (C n p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hCn : Odd (C * n)) :
    Nat.factorial ((C * n * p^r - 1) / 2) =
      p ^ ((C * n * p^(r-1) - 1) / 2) *
        Nat.factorial ((C * n * p^(r-1) - 1) / 2) *
          U 1 ((C * n - 1) / 2) p r *
            halfShiftBlockStep ((C * n - 1) / 2) p r := by
  exact odd_half_factorial_decomposition_step C n p r (hp.odd_of_ne_two (by omega)) hr hCn


/-- Prime/`p ≥ 5` wrapper for the half-block identification. -/
theorem halfShiftBlockStep_eq_halfShiftBlock_prime_ge5
    (M p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    halfShiftBlockStep M p r = halfShiftBlock M p r := by
  exact halfShiftBlockStep_eq_halfShiftBlock M p r (hp.odd_of_ne_two (by omega)) hr

/-- Exact odd half-factorial decomposition with the final half block in filtered
`halfUnitRange`/`halfShiftBlock` form. -/
theorem odd_half_factorial_decomposition
    (C n p r : ℕ) (hpOdd : Odd p) (hr : 0 < r) (hCn : Odd (C * n)) :
    Nat.factorial ((C * n * p^r - 1) / 2) =
      p ^ ((C * n * p^(r-1) - 1) / 2) *
        Nat.factorial ((C * n * p^(r-1) - 1) / 2) *
          U 1 ((C * n - 1) / 2) p r *
            halfShiftBlock ((C * n - 1) / 2) p r := by
  rw [← halfShiftBlockStep_eq_halfShiftBlock ((C * n - 1) / 2) p r hpOdd hr]
  exact odd_half_factorial_decomposition_step C n p r hpOdd hr hCn

/-- Prime/`p ≥ 5` wrapper for the filtered-half-block odd decomposition. -/
theorem odd_half_factorial_decomposition_prime_ge5
    (C n p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hCn : Odd (C * n)) :
    Nat.factorial ((C * n * p^r - 1) / 2) =
      p ^ ((C * n * p^(r-1) - 1) / 2) *
        Nat.factorial ((C * n * p^(r-1) - 1) / 2) *
          U 1 ((C * n - 1) / 2) p r *
            halfShiftBlock ((C * n - 1) / 2) p r := by
  exact odd_half_factorial_decomposition C n p r (hp.odd_of_ne_two (by omega)) hr hCn


lemma prod_filter_mul_not {α : Type*} [DecidableEq α] [CommMonoid α]
    (s : Finset α) (P : α → Prop) [DecidablePred P] [∀ x, Decidable (¬ P x)] (F : α → α) :
    (∏ x ∈ s, F x) = (∏ x ∈ s.filter P, F x) * (∏ x ∈ s.filter (fun x => ¬ P x), F x) := by
  rw [← Finset.prod_union]
  · rw [Finset.filter_union_filter_not_eq]
  · exact Finset.disjoint_filter_filter_not s s P

end TempOddHalfExact


/- Flattened helper code from TempShiftedProductGeneralClean.lean -/

open scoped BigOperators

-- Clean, non-conflicting copy of only the product-expansion and kernel bridge
-- lemmas needed to combine `TempGeneralHarmonic` with the full shifted product.
namespace TempShiftedProductGeneralClean

open TempShiftedProductGeneralHarmonic


lemma prod_eq_zero_of_three_le_card
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    {s t : Finset ι} {y : ι → R}
    (hsub : t ⊆ s) (hcard : 3 ≤ t.card)
    (h3 : ∀ a b c, a ∈ s → b ∈ s → c ∈ s →
      a ≠ b → a ≠ c → b ≠ c → y a * y b * y c = 0) :
    ∏ i ∈ t, y i = 0 := by
  obtain ⟨u, hut, hucard⟩ := Finset.exists_subset_card_eq hcard
  rw [← Finset.prod_sdiff hut]
  suffices ∏ i ∈ u, y i = 0 by simp [this]
  rcases Finset.card_eq_three.mp hucard with ⟨a, b, c, hab, hac, hbc, rfl⟩
  have ha : a ∈ s := hsub (hut (by simp))
  have hb : b ∈ s := hsub (hut (by simp))
  have hc : c ∈ s := hsub (hut (by simp))
  simpa [hab, hac, hbc, mul_assoc] using h3 a b c ha hb hc hab hac hbc

theorem prod_one_add_eq_truncated_of_triple_zero
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (y : ι → R)
    (h3 : ∀ a b c, a ∈ s → b ∈ s → c ∈ s →
      a ≠ b → a ≠ c → b ≠ c → y a * y b * y c = 0) :
    ∏ i ∈ s, (1 + y i) =
      1 + ∑ i ∈ s, y i + ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i := by
  let F : ℕ → R := fun j => ∑ t ∈ s.powersetCard j, ∏ i ∈ t, y i
  have hzero_ge_three : ∀ j, 3 ≤ j → F j = 0 := by
    intro j hj
    dsimp [F]
    refine Finset.sum_eq_zero fun t ht => ?_
    exact prod_eq_zero_of_three_le_card (Finset.mem_powersetCard.mp ht).1
      (by simpa [Finset.mem_powersetCard.mp ht] using hj) h3
  have hzero_gt_card : ∀ j, s.card < j → F j = 0 := by
    intro j hj
    dsimp [F]
    have hp : s.powersetCard j = ∅ := by
      rw [Finset.powersetCard_eq_empty]
      exact hj
    simp [hp]
  have hrange : (∑ j ∈ Finset.range (s.card + 1), F j) = ∑ j ∈ Finset.range 3, F j := by
    let u := Finset.range (s.card + 1) ∪ Finset.range 3
    have h₁ : (∑ j ∈ Finset.range (s.card + 1), F j) = ∑ j ∈ u, F j := by
      refine Finset.sum_subset (by intro x hx; exact Finset.mem_union_left _ hx) ?_
      intro x hx hxrange
      have hx3 : x ∈ Finset.range 3 := by
        simpa [u, hxrange] using hx
      exact hzero_gt_card x (by
        rw [Finset.mem_range] at hxrange hx3
        exact Nat.lt_of_succ_le (not_lt.mp hxrange))
    have h₂ : (∑ j ∈ Finset.range 3, F j) = ∑ j ∈ u, F j := by
      refine Finset.sum_subset (by intro x hx; exact Finset.mem_union_right _ hx) ?_
      intro x hx hxrange3
      have hxorig : x ∈ Finset.range (s.card + 1) := by
        simpa [u, hxrange3] using hx
      exact hzero_ge_three x (by
        rw [Finset.mem_range] at hxrange3
        exact not_lt.mp hxrange3)
    exact h₁.trans h₂.symm
  have hF0 : F 0 = 1 := by
    dsimp [F]
    simp
  have hF1 : F 1 = ∑ i ∈ s, y i := by
    dsimp [F]
    rw [Finset.powersetCard_one]
    simp
  calc
    ∏ i ∈ s, (1 + y i) = ∑ t ∈ s.powerset, ∏ i ∈ t, y i := Finset.prod_one_add s
    _ = ∑ j ∈ Finset.range (s.card + 1), F j := by
      dsimp [F]
      exact Finset.sum_powerset s (fun t => ∏ i ∈ t, y i)
    _ = ∑ j ∈ Finset.range 3, F j := hrange
    _ = F 0 + F 1 + F 2 := by norm_num [Finset.sum_range_succ]
    _ = 1 + ∑ i ∈ s, y i + ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i := by
      dsimp [F] at hF0 hF1 ⊢
      rw [hF0, hF1]


theorem prod_one_add_eq_truncated_of_cube_zero
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (P : R) (z : ι → R) (hP : P ^ 3 = 0) :
    ∏ i ∈ s, (1 + P * z i) =
      1 + ∑ i ∈ s, P * z i + ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, P * z i := by
  apply prod_one_add_eq_truncated_of_triple_zero
  intro a b c _ha _hb _hc _hab _hac _hbc
  calc
    (P * z a) * (P * z b) * (P * z c) = P ^ 3 * (z a * z b * z c) := by ring
    _ = 0 := by simp [hP]




lemma zmod_shift_cube_zero (p r q : ℕ) :
    (((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r)))) ^ 3) = 0 := by
  have hpzero : (p^r : ZMod (p ^ (3 * r))) ^ 3 = 0 := by
    rw [← pow_mul]
    rw [show r * 3 = 3 * r by omega]
    rw [← Nat.cast_pow]
    exact CharP.cast_eq_zero (ZMod (p ^ (3 * r))) (p ^ (3 * r))
  rw [show ((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r)))) ^ 3 =
      (q : ZMod (p ^ (3 * r))) ^ 3 * (p^r : ZMod (p ^ (3 * r))) ^ 3 by ring]
  rw [hpzero, mul_zero]

lemma zmod_nat_unit_mul_inv_general {p r i : ℕ} (hp : Nat.Prime p)
    (hi : i ∈ unitRange p r) :
    (i : ZMod (p ^ (3 * r))) * ((i : ZMod (p ^ (3 * r)))⁻¹) = 1 := by
  have hnot : ¬ p ∣ i := by
    exact (Finset.mem_filter.mp hi).2
  have hunit : IsUnit (i : ZMod (p ^ (3 * r))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hp.coprime_pow_of_not_dvd hnot
  exact ZMod.mul_inv_of_unit _ hunit

/-- General shifted-product reduction to the two harmonic congruences.

For `R = ZMod (p^(3*r))` and `P = q*p^r`, the product identity follows from
`P * sum i⁻¹ = 0` and `P^2 * sum_{i<j} (ij)⁻¹ = 0`.  The cubic and higher
terms vanish because `P^3 = 0`. -/
theorem shifted_product_general_of_harmonic
    (p r q : ℕ) (hp : Nat.Prime p)
    (hlin : ((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r)))) *
        (∑ i ∈ unitRange p r, ((i : ZMod (p ^ (3 * r)))⁻¹)) = 0)
    (hquad : (((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r)))) ^ 2) *
        (∑ t ∈ (unitRange p r).powersetCard 2,
          ∏ i ∈ t, ((i : ZMod (p ^ (3 * r)))⁻¹)) = 0) :
    (∏ i ∈ unitRange p r,
        ((i : ZMod (p ^ (3 * r))) +
          (q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r))))) =
      ∏ i ∈ unitRange p r, (i : ZMod (p ^ (3 * r))) := by
  let R := ZMod (p ^ (3 * r))
  let P : R := (q : R) * (p^r : R)
  let s := unitRange p r
  let z : ℕ → R := fun i => ((i : R)⁻¹)
  have hprod_one : (∏ i ∈ s, (1 + P * z i)) = 1 := by
    have hexp := prod_one_add_eq_truncated_of_cube_zero
      (s := s) (P := P) (z := z) (hP := by
        dsimp [P, R]
        exact zmod_shift_cube_zero p r q)
    dsimp [P, z, R, s] at hexp
    rw [hexp]
    have hlin' : (∑ i ∈ unitRange p r,
        (q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r))) *
          (↑i)⁻¹) = 0 := by
      rw [← Finset.mul_sum]
      exact hlin
    have hquad' : (∑ t ∈ (unitRange p r).powersetCard 2,
        ∏ i ∈ t,
          (q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r))) * (↑i)⁻¹) = 0 := by
      rw [show (∑ t ∈ (unitRange p r).powersetCard 2,
          ∏ i ∈ t,
            (q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r))) * (↑i)⁻¹) =
          (((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r)))) ^ 2) *
            (∑ t ∈ (unitRange p r).powersetCard 2,
              ∏ i ∈ t, (↑i)⁻¹) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have htcard : t.card = 2 := (Finset.mem_powersetCard.mp ht).2
        calc
          ∏ x ∈ t,
              ((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r))) * (↑x)⁻¹)
              = (∏ _x ∈ t,
                  ((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r))))) *
                    ∏ x ∈ t, (↑x)⁻¹ := by
                rw [← Finset.prod_mul_distrib]
          _ = (((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r)))) ^ t.card) *
                    ∏ x ∈ t, (↑x)⁻¹ := by
                rw [Finset.prod_const]
          _ = (((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r)))) ^ 2) *
                    ∏ x ∈ t, (↑x)⁻¹ := by
                rw [htcard]]
      exact hquad
    simp [hlin', hquad']
  calc
    (∏ i ∈ unitRange p r,
        ((i : ZMod (p ^ (3 * r))) +
          (q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r)))))
        = ∏ i ∈ s, ((i : R) * (1 + P * z i)) := by
          dsimp [s, P, z, R]
          apply Finset.prod_congr rfl
          intro i hi
          rw [mul_add, mul_one]
          rw [show (i : ZMod (p ^ (3 * r))) *
                (((q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r)))) *
                  ((i : ZMod (p ^ (3 * r)))⁻¹)) =
              (q : ZMod (p ^ (3 * r))) * (p^r : ZMod (p ^ (3 * r))) *
                ((i : ZMod (p ^ (3 * r))) * ((i : ZMod (p ^ (3 * r)))⁻¹)) by ring]
          rw [zmod_nat_unit_mul_inv_general hp hi]
          ring
    _ = (∏ i ∈ s, (i : R)) * (∏ i ∈ s, (1 + P * z i)) := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ i ∈ unitRange p r, (i : ZMod (p ^ (3 * r))) := by
          dsimp [s, R] at hprod_one ⊢
          rw [hprod_one, mul_one]



/-- Divisibility `p^(2r) ∣ p^(3r)`. -/
lemma dvd_p2r_p3r (p r : ℕ) : p ^ (2 * r) ∣ p ^ (3 * r) := by
  exact Nat.pow_dvd_pow p (by omega)

/-- Divisibility `p^r ∣ p^(3r)`. -/
lemma dvd_pr_p3r (p r : ℕ) : p ^ r ∣ p ^ (3 * r) := by
  exact Nat.pow_dvd_pow p (by omega)

/-- If an element of `ZMod (p^(3r))` maps to zero modulo `p^(2r)`, then multiplying
by `p^r` kills it.  This is the kernel statement used for the linear term. -/
lemma zmod_p3r_cast_p2r_eq_zero_mul_pr {p r : ℕ} [NeZero (p ^ (3 * r))]
    (x : ZMod (p ^ (3 * r)))
    (hx : ZMod.castHom (dvd_p2r_p3r p r) (ZMod (p ^ (2 * r))) x = 0) :
    (p ^ r : ZMod (p ^ (3 * r))) * x = 0 := by
  have hxval : ((x.val : ℕ) : ZMod (p ^ (2 * r))) = 0 := by
    rw [← ZMod.natCast_zmod_val x] at hx
    simpa using hx
  have hdvd_nat : p ^ (2 * r) ∣ x.val := by
    rw [← Nat.modEq_zero_iff_dvd]
    rw [← ZMod.natCast_eq_natCast_iff (x.val) 0 (p ^ (2 * r))]
    simpa using hxval
  obtain ⟨t, ht⟩ := hdvd_nat
  rw [← ZMod.natCast_zmod_val x]
  rw [← Nat.cast_pow p r]
  rw [← Nat.cast_mul]
  rw [ht]
  rw [show p ^ r * (p ^ (2 * r) * t) = p ^ (3 * r) * t by
    rw [← mul_assoc]
    congr 1
    rw [← pow_add]
    congr 1
    omega]
  rw [Nat.cast_mul, CharP.cast_eq_zero, zero_mul]

/-- If an element of `ZMod (p^(3r))` maps to zero modulo `p^r`, then multiplying
by `(p^r)^2` kills it.  This is the kernel statement used for the quadratic term. -/
lemma zmod_p3r_cast_pr_eq_zero_mul_pr_sq {p r : ℕ} [NeZero (p ^ (3 * r))]
    (x : ZMod (p ^ (3 * r)))
    (hx : ZMod.castHom (dvd_pr_p3r p r) (ZMod (p ^ r)) x = 0) :
    ((p ^ r : ZMod (p ^ (3 * r))) ^ 2) * x = 0 := by
  have hxval : ((x.val : ℕ) : ZMod (p ^ r)) = 0 := by
    rw [← ZMod.natCast_zmod_val x] at hx
    simpa using hx
  have hdvd_nat : p ^ r ∣ x.val := by
    rw [← Nat.modEq_zero_iff_dvd]
    rw [← ZMod.natCast_eq_natCast_iff (x.val) 0 (p ^ r)]
    simpa using hxval
  obtain ⟨t, ht⟩ := hdvd_nat
  rw [← ZMod.natCast_zmod_val x]
  rw [← Nat.cast_pow p r]

  rw [← Nat.cast_pow (p ^ r) 2]
  rw [← Nat.cast_mul]
  rw [ht]
  rw [show (p ^ r) ^ 2 * (p ^ r * t) = p ^ (3 * r) * t by
    ring_nf]
  rw [Nat.cast_mul, CharP.cast_eq_zero, zero_mul]

lemma zmod_map_inv_nat_p3r_to_p2r {p r i : ℕ} [NeZero (p ^ (2 * r))]
    (hp : Nat.Prime p) (hi : i ∈ unitRange p r) :
    ZMod.castHom (dvd_p2r_p3r p r) (ZMod (p ^ (2 * r)))
      (((i : ZMod (p ^ (3 * r)))⁻¹)) = ((i : ZMod (p ^ (2 * r)))⁻¹) := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  have hnot : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
  have hunit3 : IsUnit (i : ZMod (p ^ (3 * r))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hp.coprime_pow_of_not_dvd hnot
  have hmul3 : (i : ZMod (p ^ (3 * r))) * ((i : ZMod (p ^ (3 * r)))⁻¹) = 1 :=
    ZMod.mul_inv_of_unit _ hunit3
  have hmap := congrArg (ZMod.castHom (dvd_p2r_p3r p r) (ZMod (p ^ (2 * r)))) hmul3
  simp only [map_mul, map_one] at hmap
  simpa using hmap

lemma zmod_map_inv_nat_p3r_to_pr {p r i : ℕ} [NeZero (p ^ r)]
    (hp : Nat.Prime p) (hi : i ∈ unitRange p r) :
    ZMod.castHom (dvd_pr_p3r p r) (ZMod (p ^ r))
      (((i : ZMod (p ^ (3 * r)))⁻¹)) = ((i : ZMod (p ^ r))⁻¹) := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  have hnot : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
  have hunit3 : IsUnit (i : ZMod (p ^ (3 * r))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hp.coprime_pow_of_not_dvd hnot
  have hmul3 : (i : ZMod (p ^ (3 * r))) * ((i : ZMod (p ^ (3 * r)))⁻¹) = 1 :=
    ZMod.mul_inv_of_unit _ hunit3
  have hmap := congrArg (ZMod.castHom (dvd_pr_p3r p r) (ZMod (p ^ r))) hmul3
  simp only [map_mul, map_one] at hmap
  simpa using hmap

/-- The linear harmonic sum over `unitRange p r`, lifted to `ZMod (p^(3r))`, is
annihilated by `p^r`. -/
lemma zmod_unitRange_inv_sum_p3r_mul_pr_zero {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (p ^ r : ZMod (p ^ (3 * r))) *
      (∑ i ∈ unitRange p r, ((i : ZMod (p ^ (3 * r)))⁻¹)) = 0 := by
  haveI : NeZero (p ^ (3 * r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ (2 * r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply zmod_p3r_cast_p2r_eq_zero_mul_pr
  rw [show ZMod.castHom (dvd_p2r_p3r p r) (ZMod (p ^ (2 * r)))
        (∑ i ∈ unitRange p r, ((i : ZMod (p ^ (3 * r)))⁻¹)) =
      (∑ i ∈ unitRange p r,
        ZMod.castHom (dvd_p2r_p3r p r) (ZMod (p ^ (2 * r)))
          ((i : ZMod (p ^ (3 * r)))⁻¹)) by simp]
  rw [show (∑ i ∈ unitRange p r,
        ZMod.castHom (dvd_p2r_p3r p r) (ZMod (p ^ (2 * r)))
          ((i : ZMod (p ^ (3 * r)))⁻¹)) =
      (∑ i ∈ unitRange p r, ((i : ZMod (p ^ (2 * r)))⁻¹)) by
    apply Finset.sum_congr rfl
    intro i hi
    exact zmod_map_inv_nat_p3r_to_p2r hp hi]
  exact zmod_unitRange_inv_sum_zero_mod_p2r hp hp5 hr

/-- The elementary pair inverse sum over `unitRange p r`, lifted to `ZMod (p^(3r))`,
is annihilated by `(p^r)^2`. -/
lemma zmod_unitRange_pair_inv_sum_p3r_mul_pr_sq_zero {p r : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    ((p ^ r : ZMod (p ^ (3 * r))) ^ 2) *
      (∑ t ∈ (unitRange p r).powersetCard 2,
        ∏ i ∈ t, ((i : ZMod (p ^ (3 * r)))⁻¹)) = 0 := by
  haveI : NeZero (p ^ (3 * r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply zmod_p3r_cast_pr_eq_zero_mul_pr_sq
  rw [show ZMod.castHom (dvd_pr_p3r p r) (ZMod (p ^ r))
        (∑ t ∈ (unitRange p r).powersetCard 2,
          ∏ i ∈ t, ((i : ZMod (p ^ (3 * r)))⁻¹)) =
      (∑ t ∈ (unitRange p r).powersetCard 2,
        ZMod.castHom (dvd_pr_p3r p r) (ZMod (p ^ r))
          (∏ i ∈ t, ((i : ZMod (p ^ (3 * r)))⁻¹))) by simp]
  rw [show (∑ t ∈ (unitRange p r).powersetCard 2,
        ZMod.castHom (dvd_pr_p3r p r) (ZMod (p ^ r))
          (∏ i ∈ t, ((i : ZMod (p ^ (3 * r)))⁻¹))) =
      (∑ t ∈ (unitRange p r).powersetCard 2,
        ∏ i ∈ t, ((i : ZMod (p ^ r))⁻¹)) by
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i hit
    have hsub : t ⊆ unitRange p r := (Finset.mem_powersetCard.mp ht).1
    exact zmod_map_inv_nat_p3r_to_pr hp (hsub hit)]
  exact zmod_unitRange_pair_inv_sum_zero hp hp5 hr

/-- Full generalized shifted-product theorem. -/
theorem shifted_product_general
  (p r q : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ i ∈ unitRange p r,
        ((i : ZMod (p ^ (3*r))) + (q : ZMod (p ^ (3*r))) * (p^r : ZMod (p ^ (3*r))))) =
      ∏ i ∈ unitRange p r, (i : ZMod (p ^ (3*r))) := by
  rw [show 3 * r = 3*r by rfl]
  apply shifted_product_general_of_harmonic p r q hp
  · have h := zmod_unitRange_inv_sum_p3r_mul_pr_zero hp hp5 hr
    rw [show (q : ZMod (p ^ (3 * r))) * (p ^ r : ZMod (p ^ (3 * r))) *
        (∑ i ∈ unitRange p r, (↑i)⁻¹) =
        (q : ZMod (p ^ (3 * r))) *
          ((p ^ r : ZMod (p ^ (3 * r))) * (∑ i ∈ unitRange p r, (↑i)⁻¹)) by ring]
    rw [h, mul_zero]
  · have h := zmod_unitRange_pair_inv_sum_p3r_mul_pr_sq_zero hp hp5 hr
    rw [show ((q : ZMod (p ^ (3 * r))) * (p ^ r : ZMod (p ^ (3 * r)))) ^ 2 *
        (∑ t ∈ (unitRange p r).powersetCard 2, ∏ i ∈ t, (↑i)⁻¹) =
        ((q : ZMod (p ^ (3 * r))) ^ 2) *
          (((p ^ r : ZMod (p ^ (3 * r))) ^ 2) *
            (∑ t ∈ (unitRange p r).powersetCard 2, ∏ i ∈ t, (↑i)⁻¹)) by ring]
    rw [h, mul_zero]



/-- `TempOddChosen.U` is a product of full unit blocks; the clean shifted-product theorem
identifies every shifted full block with the base block `TempOddChosen.W`. -/
lemma oddChosen_U_cast_eq_pow_W {p r C m : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (TempOddChosen.U C m p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (C * m) := by
  classical
  rw [TempOddChosen.U, TempOddChosen.W]
  calc
    (↑(∏ q ∈ Finset.range (C * m),
          ∏ i ∈ TempShiftedProductGeneralHarmonic.unitRange p r, (q * p ^ r + i)) : ZMod (p ^ (3 * r)))
        = ∏ q ∈ Finset.range (C * m),
            (∏ i ∈ TempShiftedProductGeneralHarmonic.unitRange p r,
              ((q * p ^ r + i : ℕ) : ZMod (p^(3*r)))) := by
          simp
    _ = ∏ q ∈ Finset.range (C * m),
            (∏ i ∈ TempShiftedProductGeneralHarmonic.unitRange p r,
              (i : ZMod (p^(3*r)))) := by
          apply Finset.prod_congr rfl
          intro q hq
          have hshift := shifted_product_general p r q hp hp5 hr
          simpa [Nat.cast_add, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc,
            add_comm, add_left_comm, add_assoc] using hshift
    _ = (∏ i ∈ TempShiftedProductGeneralHarmonic.unitRange p r,
            (i : ZMod (p^(3*r)))) ^ (C * m) := by
          rw [Finset.prod_const]
          simp
    _ = (↑(∏ i ∈ TempShiftedProductGeneralHarmonic.unitRange p r, i) :
            ZMod (p^(3*r))) ^ (C * m) := by
          simp

/-- Alias with the requested conventional name, inside the fresh clean namespace. -/
lemma U_cast_eq_pow_W {p r C m : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (TempOddChosen.U C m p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (C * m) :=
  oddChosen_U_cast_eq_pow_W hp hp5 hr

end TempShiftedProductGeneralClean


/- Flattened helper code from TempOddChosenRepresentativeCongruence.lean -/

open scoped BigOperators Real

namespace TempOddChosenRepresentativeCongruence

open TempOddChosen

/-- The p-free numerator multiplier in the odd branch when passing from
`n*p^(r-1)` to `n*p^r`.  This is the exact non-`p` factor left after the
factorial decompositions; the exponent of `4` is written in the form needed by
`halfBlockR_shift_three_mul_division_free`. -/
def OddUnum (n p r : ℕ) : ℕ :=
  4 ^ (3 * n * (p^(r-1) * (p-1))) *
    TempOddChosen.U 1 ((9 * n - 1) / 2) p r *
    TempOddChosen.U 2 n p r *
    TempOddHalfExact.halfShiftBlock ((9 * n - 1) / 2) p r

/-- The p-free denominator multiplier in the odd branch when passing from
`n*p^(r-1)` to `n*p^r`. -/
def OddUden (n p r : ℕ) : ℕ :=
  TempOddChosen.U 1 ((3 * n - 1) / 2) p r *
    TempOddChosen.U 4 n p r *
    TempOddChosen.U 1 n p r *
    TempOddHalfExact.halfShiftBlock ((3 * n - 1) / 2) p r

lemma cast_halfShiftBlock_eq_halfBlockR (M p r : ℕ) :
    (TempOddHalfExact.halfShiftBlock M p r : ZMod (p^(3*r))) =
      TempHalfBlockR.halfBlockR p r M := by
  classical
  rw [TempOddHalfExact.halfShiftBlock, TempHalfBlockR.halfBlockR]
  simp only [Nat.cast_prod]
  apply Finset.prod_congr
  · ext i
    simp [TempOddHalfExact.halfUnitRange, TempHalfBlockR.halfUnitRange]
  · intro i hi
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring_nf

/-- The central p-free modular equality for the odd branch.  The only hypotheses
not discharged here are the complete-block shifted-product congruences for the
five `U` factors.  They are stated explicitly to avoid importing the standalone
even complete-block development, whose copied auxiliary names conflict with the
prime-power half-block files.

This theorem is the useful modular integer statement for the `OddNum/OddDen`
ratio after the exact factorial decompositions have reduced the problem to
p-free factors. -/
theorem odd_pfree_multipliers_congruent {p r n : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n)
    (hU1q9 : (TempOddChosen.U 1 ((9 * n - 1) / 2) p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (1 * ((9 * n - 1) / 2)))
    (hU2n : (TempOddChosen.U 2 n p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (2 * n))
    (hU1q3 : (TempOddChosen.U 1 ((3 * n - 1) / 2) p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (1 * ((3 * n - 1) / 2)))
    (hU4n : (TempOddChosen.U 4 n p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (4 * n))
    (hU1n : (TempOddChosen.U 1 n p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (1 * n)) :
    (OddUnum n p r : ZMod (p^(3*r))) = (OddUden n p r : ZMod (p^(3*r))) := by
  classical
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hbal := TempOddChosen.odd_pfree_balance_from_complete_blocks
    (p := p) (r := r) (n := n) hp hp5 hr hn hU1q9 hU2n hU1q3 hU4n hU1n
  dsimp [OddUnum, OddUden]
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [cast_halfShiftBlock_eq_halfBlockR ((9 * n - 1) / 2) p r]
  rw [cast_halfShiftBlock_eq_halfBlockR ((3 * n - 1) / 2) p r]
  exact hbal

/-- A cancellation wrapper converting the p-free multiplier equality into the
chosen-representative congruence.  The hypothesis `hchosen_exact` is precisely
what the exact odd full/half factorial decompositions give after cancelling the
common nonzero old denominator and the balanced power of `p` over the integers.
The hypothesis `hunit` records that the denominator p-free multiplier is a unit
modulo `p^(3r)` (it follows directly from the fact that all its factors are
prime to `p`). -/
theorem odd_branch_chosen_representative_congruence_from_exact_pfree
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    {p r n : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n)
    (hU1q9 : (TempOddChosen.U 1 ((9 * n - 1) / 2) p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (1 * ((9 * n - 1) / 2)))
    (hU2n : (TempOddChosen.U 2 n p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (2 * n))
    (hU1q3 : (TempOddChosen.U 1 ((3 * n - 1) / 2) p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (1 * ((3 * n - 1) / 2)))
    (hU4n : (TempOddChosen.U 4 n p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (4 * n))
    (hU1n : (TempOddChosen.U 1 n p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (1 * n))
    (hchosen_exact :
      (Classical.choose (h_int (n * p^r)) : ℤ) * (OddUden n p r : ℤ) =
        (Classical.choose (h_int (n * p^(r-1))) : ℤ) * (OddUnum n p r : ℤ))
    (hunit : IsUnit (OddUden n p r : ZMod (p^(3*r)))) :
    (Classical.choose (h_int (n * p^r)) : ℤ)
      ≡ (Classical.choose (h_int (n * p^(r-1))) : ℤ)
      [ZMOD ((p : ℤ) ^ (3*r))] := by
  classical
  let R := ZMod (p^(3*r))
  let Anew : ℤ := Classical.choose (h_int (n * p^r))
  let Aold : ℤ := Classical.choose (h_int (n * p^(r-1)))
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hrelR : (Anew : R) * (OddUden n p r : R) =
      (Aold : R) * (OddUnum n p r : R) := by
    have := congrArg (fun z : ℤ => (z : R)) hchosen_exact
    simpa [Anew, Aold, R] using this
  have hpfree := odd_pfree_multipliers_congruent
    (p := p) (r := r) (n := n) hp hp5 hr hn hU1q9 hU2n hU1q3 hU4n hU1n
  change (OddUnum n p r : R) = (OddUden n p r : R) at hpfree
  rw [hpfree] at hrelR
  change IsUnit (OddUden n p r : R) at hunit
  have hEqR : (Anew : R) = (Aold : R) := hunit.mul_right_cancel hrelR
  have hmod : Anew ≡ Aold [ZMOD (p^(3*r) : ℕ)] :=
    (ZMod.intCast_eq_intCast_iff Anew Aold (p^(3*r))).mp hEqR
  simpa [Anew, Aold, Int.natCast_pow] using hmod

end TempOddChosenRepresentativeCongruence


/- Flattened helper code from TempOddPFreeUnconditional.lean -/

open scoped BigOperators Real

namespace TempOddPFreeUnconditional

open TempOddChosenRepresentativeCongruence

/-- Unconditional odd-branch p-free multiplier congruence.  The five complete-block
`U` congruences required by `TempOddChosenRepresentativeCongruence` are supplied
by `TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W`. -/
theorem odd_pfree_multipliers_congruent_unconditional {p r n : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n) :
    (OddUnum n p r : ZMod (p^(3*r))) = (OddUden n p r : ZMod (p^(3*r))) := by
  exact odd_pfree_multipliers_congruent
    (p := p) (r := r) (n := n) hp hp5 hr hn
    (TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 1) (m := ((9 * n - 1) / 2)) hp hp5 hr)
    (TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 2) (m := n) hp hp5 hr)
    (TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 1) (m := ((3 * n - 1) / 2)) hp hp5 hr)
    (TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 4) (m := n) hp hp5 hr)
    (TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 1) (m := n) hp hp5 hr)

/-- The base complete unit block `W` is a unit modulo `p^(3*r)`. -/
lemma oddChosen_W_isUnit {p r : ℕ} (hp : Nat.Prime p) :
    IsUnit (TempOddChosen.W p r : ZMod (p^(3*r))) := by
  classical
  rw [TempOddChosen.W]
  simp only [Nat.cast_prod]
  apply Finset.prod_induction
  · intro a b ha hb
    exact IsUnit.mul ha hb
  · exact isUnit_one
  · intro i hi
    exact TempPrimePowerLehmerExact.unitRange_natCast_isUnit_p3r (p := p) (r := r) hp hi

/-- Every complete shifted unit-block product `U` is a unit modulo `p^(3*r)`. -/
lemma oddChosen_U_isUnit {p r C m : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    IsUnit (TempOddChosen.U C m p r : ZMod (p^(3*r))) := by
  have hWpow : IsUnit ((TempOddChosen.W p r : ZMod (p^(3*r))) ^ (C * m)) :=
    (oddChosen_W_isUnit (p := p) (r := r) hp).pow (C * m)
  rw [TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
    (p := p) (r := r) (C := C) (m := m) hp hp5 hr]
  exact hWpow

/-- The shifted half block appearing in the odd denominator is a unit modulo `p^(3*r)`. -/
lemma halfShiftBlock_isUnit {M p r : ℕ} (hp : Nat.Prime p) (hr : 0 < r) :
    IsUnit (TempOddHalfExact.halfShiftBlock M p r : ZMod (p^(3*r))) := by
  rw [TempOddChosenRepresentativeCongruence.cast_halfShiftBlock_eq_halfBlockR M p r]
  exact TempHalfBlockR.halfBlockR_isUnit (p := p) (r := r) (q := M) hp hr

/-- The odd-branch p-free denominator multiplier is a unit modulo `p^(3*r)`. -/
theorem OddUden_isUnit {p r n : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    IsUnit (OddUden n p r : ZMod (p^(3*r))) := by
  rw [OddUden]
  simp only [Nat.cast_mul]
  exact IsUnit.mul
    (IsUnit.mul
      (IsUnit.mul
        (oddChosen_U_isUnit (p := p) (r := r) (C := 1) (m := ((3 * n - 1) / 2)) hp hp5 hr)
        (oddChosen_U_isUnit (p := p) (r := r) (C := 4) (m := n) hp hp5 hr))
      (oddChosen_U_isUnit (p := p) (r := r) (C := 1) (m := n) hp hp5 hr))
    (halfShiftBlock_isUnit (M := ((3 * n - 1) / 2)) (p := p) (r := r) hp hr)

end TempOddPFreeUnconditional


/- Flattened helper code from TempOddFormulaFinal.lean -/

open scoped BigOperators Real

namespace TempOddChosen

lemma gamma_nat_add_one (n : ℕ) : Real.Gamma ((n : ℝ) + 1) = (Nat.factorial n : ℝ) := by
  simpa using Real.Gamma_nat_eq_factorial n

lemma sqrt_pi_ne_zero : Real.sqrt Real.pi ≠ 0 := by
  exact Real.sqrt_ne_zero'.mpr Real.pi_pos

lemma a_odd_factorial_df (k : ℕ) :
    aTemp (2*k+1) =
      ((Nat.factorial (18*k+9) : ℝ) * (Nat.factorial (4*k+2) : ℝ) *
          (((Nat.doubleFactorial (6*k+3) : ℝ) * Real.sqrt Real.pi) / (2 : ℝ)^(3*k+2))) /
        ((((Nat.doubleFactorial (18*k+9) : ℝ) * Real.sqrt Real.pi) / (2 : ℝ)^(9*k+5)) *
          (Nat.factorial (8*k+4) : ℝ) * (Nat.factorial (6*k+3) : ℝ) *
          (Nat.factorial (2*k+1) : ℝ)) := by
  unfold aTemp
  change
    (Real.Gamma (9 * (((2 * k + 1 : ℕ) : ℝ)) + 1) *
        Real.Gamma (2 * (((2 * k + 1 : ℕ) : ℝ)) + 1) *
        Real.Gamma ((3 / 2 : ℝ) * (((2 * k + 1 : ℕ) : ℝ)) + 1)) /
      (Real.Gamma ((9 / 2 : ℝ) * (((2 * k + 1 : ℕ) : ℝ)) + 1) *
        Real.Gamma (4 * (((2 * k + 1 : ℕ) : ℝ)) + 1) *
        Real.Gamma (3 * (((2 * k + 1 : ℕ) : ℝ)) + 1) *
        Real.Gamma ((((2 * k + 1 : ℕ) : ℝ)) + 1)) = _
  have h9 : 9 * (((2 * k + 1 : ℕ) : ℝ)) + 1 = ((18*k+9 : ℕ) : ℝ) + 1 := by norm_num; ring
  have h2 : 2 * (((2 * k + 1 : ℕ) : ℝ)) + 1 = ((4*k+2 : ℕ) : ℝ) + 1 := by norm_num; ring
  have h32 : (3 / 2 : ℝ) * (((2 * k + 1 : ℕ) : ℝ)) + 1 = ((3*k+2 : ℕ) : ℝ) + 1 / 2 := by norm_num; ring
  have h92 : (9 / 2 : ℝ) * (((2 * k + 1 : ℕ) : ℝ)) + 1 = ((9*k+5 : ℕ) : ℝ) + 1 / 2 := by norm_num; ring
  have h4 : 4 * (((2 * k + 1 : ℕ) : ℝ)) + 1 = ((8*k+4 : ℕ) : ℝ) + 1 := by norm_num; ring
  have h3 : 3 * (((2 * k + 1 : ℕ) : ℝ)) + 1 = ((6*k+3 : ℕ) : ℝ) + 1 := by norm_num; ring
  have h1 : (((2 * k + 1 : ℕ) : ℝ)) + 1 = ((2*k+1 : ℕ) : ℝ) + 1 := rfl
  rw [h9, h2, h32, h92, h4, h3, h1]
  simp only [gamma_nat_add_one, Real.Gamma_nat_add_half]
  rw [show 2 * (3 * k + 2) - 1 = 6 * k + 3 by omega]
  rw [show 2 * (9 * k + 5) - 1 = 18 * k + 9 by omega]


lemma a_odd_factorial_real (k : ℕ) :
    aTemp (2*k+1) =
      ((4 : ℕ)^(6*k+3) * Nat.factorial (9*k+4) * Nat.factorial (4*k+2) : ℝ) /
        (Nat.factorial (3*k+1) * Nat.factorial (8*k+4) * Nat.factorial (2*k+1) : ℝ) := by
  rw [a_odd_factorial_df]
  have h18 : (Nat.factorial (18*k+9) : ℝ) =
      (Nat.doubleFactorial (18*k+9) : ℝ) * (Nat.doubleFactorial (18*k+8) : ℝ) := by
    have h := Nat.factorial_eq_mul_doubleFactorial (18*k+8)
    rw [show 18*k+8+1 = 18*k+9 by omega] at h
    exact_mod_cast h
  have h6 : (Nat.factorial (6*k+3) : ℝ) =
      (Nat.doubleFactorial (6*k+3) : ℝ) * (Nat.doubleFactorial (6*k+2) : ℝ) := by
    have h := Nat.factorial_eq_mul_doubleFactorial (6*k+2)
    rw [show 6*k+2+1 = 6*k+3 by omega] at h
    exact_mod_cast h
  have h18even : (Nat.doubleFactorial (18*k+8) : ℝ) =
      ((2 : ℕ)^(9*k+4) * Nat.factorial (9*k+4) : ℕ) := by
    have h := Nat.doubleFactorial_two_mul (9*k+4)
    rw [show 2*(9*k+4) = 18*k+8 by omega] at h
    exact_mod_cast h
  have h6even : (Nat.doubleFactorial (6*k+2) : ℝ) =
      ((2 : ℕ)^(3*k+1) * Nat.factorial (3*k+1) : ℕ) := by
    have h := Nat.doubleFactorial_two_mul (3*k+1)
    rw [show 2*(3*k+1) = 6*k+2 by omega] at h
    exact_mod_cast h
  rw [h18, h6, h18even, h6even]
  field_simp [sqrt_pi_ne_zero]
  norm_num
  ring_nf
  rw [show (4 : ℝ) ^ (k * 6) = (2 : ℝ) ^ (k * 12) by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [← pow_mul]
    congr 1
    ring]
  have hpow : (2 : ℝ) ^ (k * 18) = (2 : ℝ) ^ (k * 6) * (2 : ℝ) ^ (k * 12) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow]
  ring


theorem aTemp_odd_eq_OddNum_div_OddDen :
    ∀ m, Odd m → aTemp m = (OddNum m : ℝ) / (OddDen m : ℝ) := by
  intro m hm
  rcases hm with ⟨k, rfl⟩
  rw [a_odd_factorial_real]
  unfold OddNum OddDen
  rw [show 3 * (2 * k + 1) = 6 * k + 3 by omega]
  rw [show (9 * (2 * k + 1) - 1) / 2 = 9 * k + 4 by omega]
  rw [show 2 * (2 * k + 1) = 4 * k + 2 by omega]
  rw [show (6 * k + 3 - 1) / 2 = 3 * k + 1 by omega]
  rw [show 4 * (2 * k + 1) = 8 * k + 4 by omega]
  norm_num

end TempOddChosen


theorem tempOddChosen_remaining_formula :
    ∀ m, Odd m → TempOddChosen.aTemp m =
      (TempOddChosen.OddNum m : ℝ) / (TempOddChosen.OddDen m : ℝ) :=
  TempOddChosen.aTemp_odd_eq_OddNum_div_OddDen


/- Flattened helper code from TempOddExactRelation.lean -/

open scoped BigOperators Real

namespace TempOddExactRelation

open TempOddChosenRepresentativeCongruence

lemma unitRange_eq (p r : ℕ) :
    TempOddHalfExact.unitRange p r = TempShiftedProductGeneralHarmonic.unitRange p r := by
  ext i
  simp [TempOddHalfExact.unitRange, TempShiftedProductGeneralHarmonic.unitRange]

lemma U_half_eq_chosen (C m p r : ℕ) :
    TempOddHalfExact.U C m p r = TempOddChosen.U C m p r := by
  classical
  simp [TempOddHalfExact.U, TempOddChosen.U, unitRange_eq]

lemma full_factorial_decomposition_chosenU
    (C n p r : ℕ) (hp0 : 0 < p) (hr : 0 < r) :
    Nat.factorial (C * (n * p^r)) =
      p^(C * n * p^(r-1)) * Nat.factorial (C * (n * p^(r-1))) *
        TempOddChosen.U C n p r := by
  classical
  have h := TempOddHalfExact.factorial_block_decomposition (C * n) p r hp0 hr
  calc
    Nat.factorial (C * (n * p^r)) = Nat.factorial ((C * n) * p^r) := by ring_nf
    _ = p^((C * n) * p^(r-1)) * Nat.factorial ((C * n) * p^(r-1)) *
          TempOddChosen.U C n p r := by
            simpa [TempOddHalfExact.U, TempOddChosen.U, unitRange_eq] using h
    _ = p^(C * n * p^(r-1)) * Nat.factorial (C * (n * p^(r-1))) *
          TempOddChosen.U C n p r := by ring_nf

lemma odd_pow_mul (n p r : ℕ) (hn : Odd n) (hpOdd : Odd p) : Odd (n * p^r) := by
  exact hn.mul hpOdd.pow

lemma odd_pow_pred_mul (n p r : ℕ) (hn : Odd n) (hpOdd : Odd p) : Odd (n * p^(r-1)) := by
  exact hn.mul hpOdd.pow

lemma odd_q9_eq_q3_add' (x : ℕ) (hx : Odd x) :
    (9 * x - 1) / 2 = (3 * x - 1) / 2 + 3 * x := by
  rcases hx with ⟨k, rfl⟩
  omega

lemma odd_p_exponent_balance (x : ℕ) (hx : Odd x) :
    (9 * x - 1) / 2 + 2 * x = (3 * x - 1) / 2 + 4 * x + x := by
  have h := odd_q9_eq_q3_add' x hx
  omega

lemma four_exponent_split (n p r : ℕ) (hp0 : 0 < p) (hr : 0 < r) :
    3 * (n * p^r) = 3 * (n * p^(r-1)) + 3 * n * (p^(r-1) * (p - 1)) := by
  have hpow : p^r = p^(r-1) * p := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hpS : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.succ_le_of_lt hp0)
  have hsplit : p^r = p^(r-1) + p^(r-1) * (p - 1) := by
    rw [hpow]
    calc
      p^(r-1) * p = p^(r-1) * ((p - 1) + 1) := by rw [hpS]
      _ = p^(r-1) + p^(r-1) * (p - 1) := by rw [Nat.mul_add]; ring
  rw [hsplit]
  ring

lemma half9_decomposition_chosenU
    {p r n : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n) :
    Nat.factorial ((9 * (n * p^r) - 1) / 2) =
      p ^ ((9 * (n * p^(r-1)) - 1) / 2) *
        Nat.factorial ((9 * (n * p^(r-1)) - 1) / 2) *
          TempOddChosen.U 1 ((9 * n - 1) / 2) p r *
            TempOddHalfExact.halfShiftBlock ((9 * n - 1) / 2) p r := by
  classical
  have hCn : Odd (9 * n) := by
    exact (by norm_num : Odd 9).mul hn
  have h := TempOddHalfExact.odd_half_factorial_decomposition_prime_ge5
    (C := 9) (n := n) (p := p) (r := r) hp hp5 hr hCn
  rw [U_half_eq_chosen] at h
  convert h using 1 <;> ring_nf

lemma half3_decomposition_chosenU
    {p r n : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n) :
    Nat.factorial ((3 * (n * p^r) - 1) / 2) =
      p ^ ((3 * (n * p^(r-1)) - 1) / 2) *
        Nat.factorial ((3 * (n * p^(r-1)) - 1) / 2) *
          TempOddChosen.U 1 ((3 * n - 1) / 2) p r *
            TempOddHalfExact.halfShiftBlock ((3 * n - 1) / 2) p r := by
  classical
  have hCn : Odd (3 * n) := by
    exact (by norm_num : Odd 3).mul hn
  have h := TempOddHalfExact.odd_half_factorial_decomposition_prime_ge5
    (C := 3) (n := n) (p := p) (r := r) hp hp5 hr hCn
  rw [U_half_eq_chosen] at h
  convert h using 1 <;> ring_nf

lemma OddNum_decomposition
    {p r n : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n) :
    TempOddChosen.OddNum (n * p^r) =
      p ^ ((9 * (n * p^(r-1)) - 1) / 2 + 2 * (n * p^(r-1))) *
        TempOddChosen.OddNum (n * p^(r-1)) *
          OddUnum n p r := by
  classical
  have hp0 : 0 < p := hp.pos
  have hhalf := half9_decomposition_chosenU (p := p) (r := r) (n := n) hp hp5 hr hn
  have hfull := full_factorial_decomposition_chosenU (C := 2) (n := n) (p := p) (r := r) hp0 hr
  have h4 := four_exponent_split n p r hp0 hr
  unfold TempOddChosen.OddNum OddUnum
  rw [hhalf, hfull, h4, pow_add, pow_add]
  ring

lemma OddDen_decomposition
    {p r n : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n) :
    TempOddChosen.OddDen (n * p^r) =
      p ^ ((3 * (n * p^(r-1)) - 1) / 2 + 4 * (n * p^(r-1)) + (n * p^(r-1))) *
        TempOddChosen.OddDen (n * p^(r-1)) *
          OddUden n p r := by
  classical
  have hp0 : 0 < p := hp.pos
  have hhalf := half3_decomposition_chosenU (p := p) (r := r) (n := n) hp hp5 hr hn
  have hfull4 := full_factorial_decomposition_chosenU (C := 4) (n := n) (p := p) (r := r) hp0 hr
  have hfull1 := full_factorial_decomposition_chosenU (C := 1) (n := n) (p := p) (r := r) hp0 hr
  have hfull1' : Nat.factorial (n * p^r) =
      p ^ (n * p^(r-1)) * Nat.factorial (n * p^(r-1)) * TempOddChosen.U 1 n p r := by
    simpa [one_mul] using hfull1
  unfold TempOddChosen.OddDen OddUden
  rw [hhalf, hfull4, hfull1']
  ring

/-- The requested exact integer relation, reduced to the chosen-representative
odd factorial equation.  The remaining hypothesis `hchoose_odd` is exactly the
Gamma/factorial formula for odd indices, cleared of denominators. -/
theorem odd_branch_exact_integer_relation_from_chosen_equation
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    {p r n : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n)
    (hchoose_odd : ∀ m : ℕ, Odd m →
      (Classical.choose (h_int m) : ℤ) * (TempOddChosen.OddDen m : ℤ) =
        (TempOddChosen.OddNum m : ℤ)) :
    (Classical.choose (h_int (n*p^r)) : ℤ) * (OddUden n p r : ℤ) =
      (Classical.choose (h_int (n*p^(r-1))) : ℤ) * (OddUnum n p r : ℤ) := by
  classical
  let x := n * p^(r-1)
  let E := (9 * x - 1) / 2 + 2 * x
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hxnew : Odd (n * p^r) := odd_pow_mul n p r hn hpOdd
  have hxold : Odd x := by
    dsimp [x]
    exact odd_pow_pred_mul n p r hn hpOdd
  have hEbal : (3 * x - 1) / 2 + 4 * x + x = E := by
    dsimp [E]
    exact (odd_p_exponent_balance x hxold).symm
  have hnum_nat : TempOddChosen.OddNum (n * p^r) =
      p ^ E * TempOddChosen.OddNum x * OddUnum n p r := by
    dsimp [E, x]
    exact OddNum_decomposition (p := p) (r := r) (n := n) hp hp5 hr hn
  have hden_nat : TempOddChosen.OddDen (n * p^r) =
      p ^ E * TempOddChosen.OddDen x * OddUden n p r := by
    have h := OddDen_decomposition (p := p) (r := r) (n := n) hp hp5 hr hn
    have hEbalN : (3 * (n * p^(r-1)) - 1) / 2 + 4 * (n * p^(r-1)) + (n * p^(r-1)) = E := by
      simpa [x, E] using hEbal
    simpa [x, hEbalN] using h
  have hnum_int : (TempOddChosen.OddNum (n * p^r) : ℤ) =
      (p ^ E : ℕ) * (TempOddChosen.OddNum x : ℤ) * (OddUnum n p r : ℤ) := by
    exact_mod_cast hnum_nat
  have hden_int : (TempOddChosen.OddDen (n * p^r) : ℤ) =
      (p ^ E : ℕ) * (TempOddChosen.OddDen x : ℤ) * (OddUden n p r : ℤ) := by
    exact_mod_cast hden_nat
  let Anew : ℤ := Classical.choose (h_int (n * p^r))
  let Aold : ℤ := Classical.choose (h_int x)
  let Dold : ℤ := (TempOddChosen.OddDen x : ℤ)
  let Nold : ℤ := (TempOddChosen.OddNum x : ℤ)
  let pe : ℤ := (p ^ E : ℕ)
  have hnew := hchoose_odd (n * p^r) hxnew
  have hold := hchoose_odd x hxold
  have hnew' : Anew * (pe * Dold * (OddUden n p r : ℤ)) =
      pe * Nold * (OddUnum n p r : ℤ) := by
    dsimp [Anew, pe, Dold, Nold]
    simpa [hden_int, hnum_int] using hnew
  have hold' : Aold * Dold = Nold := by
    dsimp [Aold, Dold, Nold]
    exact hold
  have hfactor : pe * Dold ≠ 0 := by
    have hpe_pos_nat : 0 < p ^ E := Nat.pow_pos hp.pos
    have hD_pos_nat : 0 < TempOddChosen.OddDen x := TempOddChosen.OddDen_pos x
    have hprod_pos_nat : 0 < p ^ E * TempOddChosen.OddDen x := Nat.mul_pos hpe_pos_nat hD_pos_nat
    have hprod_pos_int : 0 < (p ^ E * TempOddChosen.OddDen x : ℤ) := by exact_mod_cast hprod_pos_nat
    have : 0 < pe * Dold := by
      dsimp [pe, Dold]
      norm_num at hprod_pos_int ⊢
      exact hprod_pos_int
    exact ne_of_gt this
  have hcancel : (pe * Dold) * (Anew * (OddUden n p r : ℤ)) =
      (pe * Dold) * (Aold * (OddUnum n p r : ℤ)) := by
    calc
      (pe * Dold) * (Anew * (OddUden n p r : ℤ))
          = Anew * (pe * Dold * (OddUden n p r : ℤ)) := by ring
      _ = pe * Nold * (OddUnum n p r : ℤ) := hnew'
      _ = pe * (Aold * Dold) * (OddUnum n p r : ℤ) := by rw [hold']
      _ = (pe * Dold) * (Aold * (OddUnum n p r : ℤ)) := by ring
  have hres := mul_left_cancel₀ hfactor hcancel
  dsimp [Anew, Aold, x] at hres
  simpa [mul_assoc] using hres

/-- Version using the odd Gamma/factorial formula for `aTemp`.  This packages the
standard cleared-denominator chosen equation and then applies the exact
factorial-decomposition/cancellation theorem above. -/
theorem odd_branch_exact_integer_relation_from_odd_gamma_formula
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    (ha_odd : ∀ m : ℕ, Odd m →
      TempOddChosen.aTemp m = (TempOddChosen.OddNum m : ℝ) / (TempOddChosen.OddDen m : ℝ))
    {p r n : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hn : Odd n) :
    (Classical.choose (h_int (n*p^r)) : ℤ) * (OddUden n p r : ℤ) =
      (Classical.choose (h_int (n*p^(r-1))) : ℤ) * (OddUnum n p r : ℤ) := by
  classical
  refine odd_branch_exact_integer_relation_from_chosen_equation h_int hp hp5 hr hn ?_
  intro m hm
  have hchoose : ((Classical.choose (h_int m) : ℤ) : ℝ) = TempOddChosen.aTemp m := by
    exact Classical.choose_spec (h_int m)
  have hreal : ((Classical.choose (h_int m) : ℤ) : ℝ) * (TempOddChosen.OddDen m : ℝ) =
      (TempOddChosen.OddNum m : ℝ) := by
    rw [hchoose, ha_odd m hm]
    have hden : (TempOddChosen.OddDen m : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (TempOddChosen.OddDen_pos m))
    field_simp [hden]
  exact_mod_cast hreal


end TempOddExactRelation


/- Flattened helper code from TempOddFull.lean -/

open scoped BigOperators Real

/-- Full odd-branch chosen-representative congruence for the temporary copy
`TempOddChosen.aTemp`. -/
theorem odd_branch_chosen_representative_congruence
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    {p r n : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) (hnodd : Odd n) :
    (Classical.choose (h_int (n * p^r)) : ℤ)
      ≡ (Classical.choose (h_int (n * p^(r-1))) : ℤ)
      [ZMOD ((p : ℤ) ^ (3*r))] := by
  classical
  have hU1q9 :
      (TempOddChosen.U 1 ((9 * n - 1) / 2) p r : ZMod (p^(3*r))) =
        (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (1 * ((9 * n - 1) / 2)) :=
    TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 1) (m := ((9 * n - 1) / 2)) hp hp5 hr
  have hU2n :
      (TempOddChosen.U 2 n p r : ZMod (p^(3*r))) =
        (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (2 * n) :=
    TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 2) (m := n) hp hp5 hr
  have hU1q3 :
      (TempOddChosen.U 1 ((3 * n - 1) / 2) p r : ZMod (p^(3*r))) =
        (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (1 * ((3 * n - 1) / 2)) :=
    TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 1) (m := ((3 * n - 1) / 2)) hp hp5 hr
  have hU4n :
      (TempOddChosen.U 4 n p r : ZMod (p^(3*r))) =
        (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (4 * n) :=
    TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 4) (m := n) hp hp5 hr
  have hU1n :
      (TempOddChosen.U 1 n p r : ZMod (p^(3*r))) =
        (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (1 * n) :=
    TempShiftedProductGeneralClean.oddChosen_U_cast_eq_pow_W
      (p := p) (r := r) (C := 1) (m := n) hp hp5 hr
  have hchosen_exact :
      (Classical.choose (h_int (n * p^r)) : ℤ) *
          (TempOddChosenRepresentativeCongruence.OddUden n p r : ℤ) =
        (Classical.choose (h_int (n * p^(r-1))) : ℤ) *
          (TempOddChosenRepresentativeCongruence.OddUnum n p r : ℤ) :=
    TempOddExactRelation.odd_branch_exact_integer_relation_from_odd_gamma_formula
      (h_int := h_int)
      (ha_odd := tempOddChosen_remaining_formula)
      (p := p) (r := r) (n := n) hp hp5 hr hnodd
  have hunit :
      IsUnit (TempOddChosenRepresentativeCongruence.OddUden n p r : ZMod (p^(3*r))) :=
    TempOddPFreeUnconditional.OddUden_isUnit (p := p) (r := r) (n := n) hp hp5 hr
  have hpfree :
      (TempOddChosenRepresentativeCongruence.OddUnum n p r : ZMod (p^(3*r))) =
        (TempOddChosenRepresentativeCongruence.OddUden n p r : ZMod (p^(3*r))) :=
    TempOddPFreeUnconditional.odd_pfree_multipliers_congruent_unconditional
      (p := p) (r := r) (n := n) hp hp5 hr hnodd
  have hfrom_unconditional_pfree :
      (Classical.choose (h_int (n * p^r)) : ℤ)
        ≡ (Classical.choose (h_int (n * p^(r-1))) : ℤ)
        [ZMOD ((p : ℤ) ^ (3*r))] := by
    let R := ZMod (p^(3*r))
    let Anew : ℤ := Classical.choose (h_int (n * p^r))
    let Aold : ℤ := Classical.choose (h_int (n * p^(r-1)))
    haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hrelR : (Anew : R) *
          (TempOddChosenRepresentativeCongruence.OddUden n p r : R) =
        (Aold : R) *
          (TempOddChosenRepresentativeCongruence.OddUnum n p r : R) := by
      have := congrArg (fun z : ℤ => (z : R)) hchosen_exact
      simpa [Anew, Aold, R] using this
    change (TempOddChosenRepresentativeCongruence.OddUnum n p r : R) =
      (TempOddChosenRepresentativeCongruence.OddUden n p r : R) at hpfree
    rw [hpfree] at hrelR
    change IsUnit (TempOddChosenRepresentativeCongruence.OddUden n p r : R) at hunit
    have hEqR : (Anew : R) = (Aold : R) := hunit.mul_right_cancel hrelR
    have hmod : Anew ≡ Aold [ZMOD (p^(3*r) : ℕ)] :=
      (ZMod.intCast_eq_intCast_iff Anew Aold (p^(3*r))).mp hEqR
    simpa [Anew, Aold, Int.natCast_pow] using hmod
  have hfrom_cancellation_wrapper :
      (Classical.choose (h_int (n * p^r)) : ℤ)
        ≡ (Classical.choose (h_int (n * p^(r-1))) : ℤ)
        [ZMOD ((p : ℤ) ^ (3*r))] :=
    TempOddChosenRepresentativeCongruence.odd_branch_chosen_representative_congruence_from_exact_pfree
      (h_int := h_int) (p := p) (r := r) (n := n) hp hp5 hr hnodd
      hU1q9 hU2n hU1q3 hU4n hU1n hchosen_exact hunit
  exact hfrom_unconditional_pfree


/- Flattened helper code from TempEvenFullClean.lean -/

open scoped BigOperators Real

namespace TempEvenFullClean

/-- The numerator in the even-index factorial formula. -/
def Bnum (k : ℕ) : ℕ :=
  Nat.factorial (18*k) * Nat.factorial (4*k) * Nat.factorial (3*k)

/-- The denominator in the even-index factorial formula. -/
def Bden (k : ℕ) : ℕ :=
  Nat.factorial (9*k) * Nat.factorial (8*k) * Nat.factorial (6*k) * Nat.factorial (2*k)

lemma Bden_pos (k : ℕ) : 0 < Bden k := by
  unfold Bden
  positivity

lemma gamma_nat_add_one (n : ℕ) : Real.Gamma ((n : ℝ) + 1) = (Nat.factorial n : ℝ) := by
  simpa using Real.Gamma_nat_eq_factorial n

/-- Even-index Gamma formula for the clean temp representative `TempOddChosen.aTemp`. -/
lemma aTemp_even_eq (k : ℕ) :
    TempOddChosen.aTemp (2*k) = (Bnum k : ℝ) / (Bden k : ℝ) := by
  unfold TempOddChosen.aTemp
  change
    (Real.Gamma (9 * ((2 * k : ℕ) : ℝ) + 1) * Real.Gamma (2 * ((2 * k : ℕ) : ℝ) + 1) * Real.Gamma ((3 / 2 : ℝ) * ((2 * k : ℕ) : ℝ) + 1)) /
      (Real.Gamma ((9 / 2 : ℝ) * ((2 * k : ℕ) : ℝ) + 1) * Real.Gamma (4 * ((2 * k : ℕ) : ℝ) + 1) * Real.Gamma (3 * ((2 * k : ℕ) : ℝ) + 1) * Real.Gamma (((2 * k : ℕ) : ℝ) + 1)) =
      (Bnum k : ℝ) / (Bden k : ℝ)
  have h9 : 9 * ((2 * k : ℕ) : ℝ) + 1 = ((18 * k : ℕ) : ℝ) + 1 := by norm_num; ring
  have h2 : 2 * ((2 * k : ℕ) : ℝ) + 1 = ((4 * k : ℕ) : ℝ) + 1 := by norm_num; ring
  have h32 : (3 / 2 : ℝ) * ((2 * k : ℕ) : ℝ) + 1 = ((3 * k : ℕ) : ℝ) + 1 := by norm_num; ring
  have h92 : (9 / 2 : ℝ) * ((2 * k : ℕ) : ℝ) + 1 = ((9 * k : ℕ) : ℝ) + 1 := by norm_num; ring
  have h4 : 4 * ((2 * k : ℕ) : ℝ) + 1 = ((8 * k : ℕ) : ℝ) + 1 := by norm_num; ring
  have h3 : 3 * ((2 * k : ℕ) : ℝ) + 1 = ((6 * k : ℕ) : ℝ) + 1 := by norm_num; ring
  rw [h9, h2, h32, h92, h4, h3]
  simp only [gamma_nat_add_one]
  rw [Bnum, Bden]
  norm_num

lemma choose_even_mul_Bden_eq_Bnum
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (k : ℕ) :
    (Classical.choose (h_int (2*k)) : ℤ) * (Bden k : ℤ) = (Bnum k : ℤ) := by
  have hchoose : ((Classical.choose (h_int (2*k)) : ℤ) : ℝ) = TempOddChosen.aTemp (2*k) := by
    exact Classical.choose_spec (h_int (2*k))
  have hreal : ((Classical.choose (h_int (2*k)) : ℤ) : ℝ) * (Bden k : ℝ) =
      (Bnum k : ℝ) := by
    rw [hchoose, aTemp_even_eq]
    have hden : (Bden k : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Bden_pos k))
    field_simp [hden]
  exact_mod_cast hreal

lemma even_index_rewrite (k p r : ℕ) : (2*k) * p^r = 2 * (k * p^r) := by
  ring

lemma choose_even_pow_mul_Bden_eq_Bnum
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (k p r : ℕ) :
    (Classical.choose (h_int ((2*k) * p^r)) : ℤ) * (Bden (k * p^r) : ℤ) =
      (Bnum (k * p^r) : ℤ) := by
  rw [even_index_rewrite]
  exact choose_even_mul_Bden_eq_Bnum h_int (k * p^r)

/-- The pure numerator unit factor `U18*U4*U3`. -/
def Unum (k p r : ℕ) : ℕ :=
  TempOddChosen.U 18 k p r * TempOddChosen.U 4 k p r * TempOddChosen.U 3 k p r

/-- The pure denominator unit factor `U9*U8*U6*U2`. -/
def Uden (k p r : ℕ) : ℕ :=
  TempOddChosen.U 9 k p r * TempOddChosen.U 8 k p r * TempOddChosen.U 6 k p r * TempOddChosen.U 2 k p r

/-- Common explicit power of `p` in the even-branch factorial block decompositions. -/
def Ppow (k p r : ℕ) : ℕ := p^(25*k*p^(r-1))

lemma factorial_scaled_decomposition (C k p r : ℕ) (hp0 : 0 < p) (hr : 0 < r) :
    Nat.factorial (C * (k * p^r)) =
      p^(C*k*p^(r-1)) * Nat.factorial (C * (k * p^(r-1))) * TempOddChosen.U C k p r := by
  have h := TempOddHalfExact.factorial_block_decomposition (N := C*k) (p := p) (r := r) hp0 hr
  calc
    Nat.factorial (C * (k * p^r)) = Nat.factorial ((C*k) * p^r) := by
      congr 1
      ring
    _ = p^((C*k) * p^(r-1)) * Nat.factorial ((C*k) * p^(r-1)) * TempOddChosen.U C k p r := by
      simpa [TempOddChosen.U, TempOddHalfExact.unitRange, TempShiftedProductGeneralHarmonic.unitRange] using h
    _ = p^(C*k*p^(r-1)) * Nat.factorial (C * (k * p^(r-1))) * TempOddChosen.U C k p r := by
      ring_nf

lemma Bnum_exact_decomposition (k p r : ℕ) (hp0 : 0 < p) (hr : 0 < r) :
    Bnum (k * p^r) =
      Ppow k p r * Bnum (k * p^(r-1)) * Unum k p r := by
  rw [Bnum, Unum, Ppow]
  rw [factorial_scaled_decomposition (C := 18) (k := k) (p := p) (r := r) hp0 hr]
  rw [factorial_scaled_decomposition (C := 4) (k := k) (p := p) (r := r) hp0 hr]
  rw [factorial_scaled_decomposition (C := 3) (k := k) (p := p) (r := r) hp0 hr]
  have hpows : p ^ (18 * k * p ^ (r - 1)) * p ^ (4 * k * p ^ (r - 1)) * p ^ (3 * k * p ^ (r - 1)) =
      p ^ (25 * k * p ^ (r - 1)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  calc
    (p ^ (18 * k * p ^ (r - 1)) * Nat.factorial (18 * (k * p ^ (r - 1))) * TempOddChosen.U 18 k p r) *
        (p ^ (4 * k * p ^ (r - 1)) * Nat.factorial (4 * (k * p ^ (r - 1))) * TempOddChosen.U 4 k p r) *
          (p ^ (3 * k * p ^ (r - 1)) * Nat.factorial (3 * (k * p ^ (r - 1))) * TempOddChosen.U 3 k p r)
        = (p ^ (18 * k * p ^ (r - 1)) * p ^ (4 * k * p ^ (r - 1)) * p ^ (3 * k * p ^ (r - 1))) *
            (Nat.factorial (18 * (k * p ^ (r - 1))) * Nat.factorial (4 * (k * p ^ (r - 1))) * Nat.factorial (3 * (k * p ^ (r - 1)))) *
              (TempOddChosen.U 18 k p r * TempOddChosen.U 4 k p r * TempOddChosen.U 3 k p r) := by ring
    _ = p ^ (25 * k * p ^ (r - 1)) *
            (Nat.factorial (18 * (k * p ^ (r - 1))) * Nat.factorial (4 * (k * p ^ (r - 1))) * Nat.factorial (3 * (k * p ^ (r - 1)))) *
              (TempOddChosen.U 18 k p r * TempOddChosen.U 4 k p r * TempOddChosen.U 3 k p r) := by rw [hpows]

lemma Bden_exact_decomposition (k p r : ℕ) (hp0 : 0 < p) (hr : 0 < r) :
    Bden (k * p^r) =
      Ppow k p r * Bden (k * p^(r-1)) * Uden k p r := by
  rw [Bden, Uden, Ppow]
  rw [factorial_scaled_decomposition (C := 9) (k := k) (p := p) (r := r) hp0 hr]
  rw [factorial_scaled_decomposition (C := 8) (k := k) (p := p) (r := r) hp0 hr]
  rw [factorial_scaled_decomposition (C := 6) (k := k) (p := p) (r := r) hp0 hr]
  rw [factorial_scaled_decomposition (C := 2) (k := k) (p := p) (r := r) hp0 hr]
  have hpows : p ^ (9 * k * p ^ (r - 1)) * p ^ (8 * k * p ^ (r - 1)) * p ^ (6 * k * p ^ (r - 1)) * p ^ (2 * k * p ^ (r - 1)) =
      p ^ (25 * k * p ^ (r - 1)) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  calc
    (p ^ (9 * k * p ^ (r - 1)) * Nat.factorial (9 * (k * p ^ (r - 1))) * TempOddChosen.U 9 k p r) *
        (p ^ (8 * k * p ^ (r - 1)) * Nat.factorial (8 * (k * p ^ (r - 1))) * TempOddChosen.U 8 k p r) *
          (p ^ (6 * k * p ^ (r - 1)) * Nat.factorial (6 * (k * p ^ (r - 1))) * TempOddChosen.U 6 k p r) *
            (p ^ (2 * k * p ^ (r - 1)) * Nat.factorial (2 * (k * p ^ (r - 1))) * TempOddChosen.U 2 k p r)
        = (p ^ (9 * k * p ^ (r - 1)) * p ^ (8 * k * p ^ (r - 1)) * p ^ (6 * k * p ^ (r - 1)) * p ^ (2 * k * p ^ (r - 1))) *
            (Nat.factorial (9 * (k * p ^ (r - 1))) * Nat.factorial (8 * (k * p ^ (r - 1))) * Nat.factorial (6 * (k * p ^ (r - 1))) * Nat.factorial (2 * (k * p ^ (r - 1)))) *
              (TempOddChosen.U 9 k p r * TempOddChosen.U 8 k p r * TempOddChosen.U 6 k p r * TempOddChosen.U 2 k p r) := by ring
    _ = p ^ (25 * k * p ^ (r - 1)) *
            (Nat.factorial (9 * (k * p ^ (r - 1))) * Nat.factorial (8 * (k * p ^ (r - 1))) * Nat.factorial (6 * (k * p ^ (r - 1))) * Nat.factorial (2 * (k * p ^ (r - 1)))) *
              (TempOddChosen.U 9 k p r * TempOddChosen.U 8 k p r * TempOddChosen.U 6 k p r * TempOddChosen.U 2 k p r) := by rw [hpows]

lemma chosen_exact_U_relation
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    {p r k : ℕ} (hp : Nat.Prime p) (hr : 0 < r) :
    (Classical.choose (h_int ((2*k) * p^r)) : ℤ) * (Uden k p r : ℤ) =
      (Classical.choose (h_int ((2*k) * p^(r-1))) : ℤ) * (Unum k p r : ℤ) := by
  let Anew : ℤ := Classical.choose (h_int ((2*k) * p^r))
  let Aold : ℤ := Classical.choose (h_int ((2*k) * p^(r-1)))
  let P : ℤ := (Ppow k p r : ℤ)
  let Bold : ℤ := (Bden (k * p^(r-1)) : ℤ)
  have hp0 : 0 < p := hp.pos
  have hnew := choose_even_pow_mul_Bden_eq_Bnum h_int k p r
  have hold := choose_even_pow_mul_Bden_eq_Bnum h_int k p (r-1)
  have hnumZ : (Bnum (k * p^r) : ℤ) =
      (Ppow k p r : ℤ) * (Bnum (k * p^(r-1)) : ℤ) * (Unum k p r : ℤ) := by
    exact_mod_cast (Bnum_exact_decomposition k p r hp0 hr)
  have hdenZ : (Bden (k * p^r) : ℤ) =
      (Ppow k p r : ℤ) * (Bden (k * p^(r-1)) : ℤ) * (Uden k p r : ℤ) := by
    exact_mod_cast (Bden_exact_decomposition k p r hp0 hr)
  change Anew * (Bden (k * p^r : ℕ) : ℤ) = (Bnum (k * p^r : ℕ) : ℤ) at hnew
  change Aold * (Bden (k * p^(r-1) : ℕ) : ℤ) = (Bnum (k * p^(r-1) : ℕ) : ℤ) at hold
  rw [hdenZ, hnumZ] at hnew
  rw [← hold] at hnew
  have hCne : P * Bold ≠ 0 := by
    have hPpos : 0 < P := by
      dsimp [P, Ppow]
      exact_mod_cast (Nat.pow_pos hp0)
    have hBpos : 0 < Bold := by
      dsimp [Bold]
      exact_mod_cast (Bden_pos (k * p^(r-1)))
    exact mul_ne_zero (ne_of_gt hPpos) (ne_of_gt hBpos)
  have hcancel : (P * Bold) * (Anew * (Uden k p r : ℤ)) = (P * Bold) * (Aold * (Unum k p r : ℤ)) := by
    dsimp [P, Bold] at hnew ⊢
    calc
      ((Ppow k p r : ℤ) * (Bden (k * p ^ (r - 1)) : ℤ)) * (Anew * (Uden k p r : ℤ))
          = Anew * ((Ppow k p r : ℤ) * (Bden (k * p ^ (r - 1)) : ℤ) * (Uden k p r : ℤ)) := by ring
      _ = (Ppow k p r : ℤ) * (Aold * (Bden (k * p ^ (r - 1)) : ℤ)) * (Unum k p r : ℤ) := hnew
      _ = ((Ppow k p r : ℤ) * (Bden (k * p ^ (r - 1)) : ℤ)) * (Aold * (Unum k p r : ℤ)) := by ring
  exact mul_left_cancel₀ hCne hcancel

lemma Unum_cast_eq_Uden {p r k : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (Unum k p r : ZMod (p^(3*r))) = (Uden k p r : ZMod (p^(3*r))) := by
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [Unum, Uden]
  simp only [Nat.cast_mul]
  rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 18) (m := k) hp hp5 hr]
  rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 4) (m := k) hp hp5 hr]
  rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 3) (m := k) hp hp5 hr]
  rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 9) (m := k) hp hp5 hr]
  rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 8) (m := k) hp hp5 hr]
  rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 6) (m := k) hp hp5 hr]
  rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 2) (m := k) hp hp5 hr]
  let w : ZMod (p^(3*r)) := (TempOddChosen.W p r : ZMod (p^(3*r)))
  change w ^ (18 * k) * w ^ (4 * k) * w ^ (3 * k) = w ^ (9 * k) * w ^ (8 * k) * w ^ (6 * k) * w ^ (2 * k)
  rw [← pow_add, ← pow_add]
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

lemma W_isUnit {p r : ℕ} (hp : Nat.Prime p) :
    IsUnit (TempOddChosen.W p r : ZMod (p^(3*r))) := by
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [TempOddChosen.W]
  simp only [Nat.cast_prod]
  rw [IsUnit.prod_iff]
  intro i hi
  have hnot : ¬ p ∣ i := by
    simpa [TempShiftedProductGeneralHarmonic.unitRange] using (Finset.mem_filter.mp hi).2
  exact (ZMod.unitOfCoprime i (hp.coprime_pow_of_not_dvd hnot)).isUnit

lemma Uden_isUnit {p r k : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    IsUnit (Uden k p r : ZMod (p^(3*r))) := by
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcast : (Uden k p r : ZMod (p^(3*r))) =
      (TempOddChosen.W p r : ZMod (p^(3*r))) ^ (25 * k) := by
    rw [Uden]
    simp only [Nat.cast_mul]
    rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 9) (m := k) hp hp5 hr]
    rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 8) (m := k) hp hp5 hr]
    rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 6) (m := k) hp hp5 hr]
    rw [TempShiftedProductGeneralClean.U_cast_eq_pow_W (C := 2) (m := k) hp hp5 hr]
    let w : ZMod (p^(3*r)) := (TempOddChosen.W p r : ZMod (p^(3*r)))
    change w ^ (9 * k) * w ^ (8 * k) * w ^ (6 * k) * w ^ (2 * k) = w ^ (25 * k)
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hcast]
  exact (W_isUnit (p := p) (r := r) hp).pow (25*k)

/-- Even-branch arbitrary-`r` congruence for the chosen integer representatives of
`TempOddChosen.aTemp`, proved from the clean shifted-product theorem. -/
theorem even_branch_chosen_representative_congruence
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    {p r k : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (Classical.choose (h_int ((2*k) * p^r)) : ℤ)
      ≡ (Classical.choose (h_int ((2*k) * p^(r-1))) : ℤ)
      [ZMOD ((p : ℤ) ^ (3*r))] := by
  let R := ZMod (p^(3*r))
  let Anew : ℤ := Classical.choose (h_int ((2*k) * p^r))
  let Aold : ℤ := Classical.choose (h_int ((2*k) * p^(r-1)))
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hrel := chosen_exact_U_relation h_int hp hr (k := k)
  change Anew * (Uden k p r : ℤ) = Aold * (Unum k p r : ℤ) at hrel
  have hrelR : (Anew : R) * (Uden k p r : R) = (Aold : R) * (Unum k p r : R) := by
    have := congrArg (fun z : ℤ => (z : R)) hrel
    simpa using this
  have hU := Unum_cast_eq_Uden (p := p) (r := r) (k := k) hp hp5 hr
  change (Unum k p r : R) = (Uden k p r : R) at hU
  rw [hU] at hrelR
  have hunit := Uden_isUnit (p := p) (r := r) (k := k) hp hp5 hr
  change IsUnit (Uden k p r : R) at hunit
  have hEqR : (Anew : R) = (Aold : R) := hunit.mul_right_cancel hrelR
  have hmod : Anew ≡ Aold [ZMOD (p^(3*r) : ℕ)] :=
    (ZMod.intCast_eq_intCast_iff Anew Aold (p^(3*r))).mp hEqR
  simpa [Anew, Aold, Int.natCast_pow] using hmod

end TempEvenFullClean

/-- Top-level version of the clean even-branch chosen-representative congruence for
`TempOddChosen.aTemp`. -/
theorem even_branch_chosen_representative_congruence
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    {p r k : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (Classical.choose (h_int ((2*k) * p^r)) : ℤ)
      ≡ (Classical.choose (h_int ((2*k) * p^(r-1))) : ℤ)
      [ZMOD ((p : ℤ) ^ (3*r))] :=
  TempEvenFullClean.even_branch_chosen_representative_congruence h_int hp hp5 hr


/- Flattened helper code from TempFullCombinedClean.lean -/

open scoped BigOperators Real

/-- Full temporary OEIS 364173 congruence for `TempOddChosen.aTemp`, obtained by
splitting on the parity of the base index and applying the even/odd branch
congruences. -/
theorem temp_oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, TempOddChosen.aTemp m ∈ Set.range (fun x : ℤ => (x : ℝ))) :
    ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∀ (n r : ℕ), n > 0 → r > 0 →
      (Classical.choose (h_int (n * p^r)) : ℤ)
        ≡ (Classical.choose (h_int (n * p^(r-1))) : ℤ)
        [ZMOD ((p : ℤ) ^ (3*r))] := by
  intro p hp hp5 n r hn hr
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · rcases hn_even with ⟨k, hk⟩
    simpa [hk, two_mul] using
      (even_branch_chosen_representative_congruence
        (h_int := h_int) (p := p) (r := r) (k := k) hp hp5 hr)
  · exact odd_branch_chosen_representative_congruence
      (h_int := h_int) (p := p) (r := r) (n := n) hp hp5 hr hn_odd

/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.
-/
theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  exact temp_oeis_364173_conjecture_0 h_int
