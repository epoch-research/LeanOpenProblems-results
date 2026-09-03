import FormalConjecturesUtil

/-!
# Erdős Problem 1020

*Reference:* [erdosproblems.com/1020](https://www.erdosproblems.com/1020)
-/

namespace Erdos1020

/-- The maximum number of edges in an `r`-uniform hypergraph on `n` vertices containing no
matching of size `k` (i.e. no `k` pairwise vertex-disjoint edges). -/
noncomputable def f (n r k : ℕ) : ℕ :=
  open scoped Classical in
  let candidates :=
    (((Finset.univ : Finset (Fin n)).powersetCard r).powerset).filter fun H ↦
      ¬ ∃ M : Finset (Finset (Fin n)),
          M ⊆ H ∧ M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id
  candidates.sup Finset.card

lemma f_le_choose (n r k : ℕ) : f n r k ≤ n.choose r := by
  classical
  unfold f
  apply Finset.sup_le
  intro H hH
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hH).1
  simpa using Finset.card_le_card hsub

lemma f_eq_choose_of_lt (n r k : ℕ) (hn : n < r * k) : f n r k = n.choose r := by
  classical
  apply le_antisymm (f_le_choose n r k)
  unfold f
  have hno : ¬ ∃ M : Finset (Finset (Fin n)),
      M ⊆ (Finset.univ : Finset (Fin n)).powersetCard r ∧
      M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id := by
    rintro ⟨M, hM, hcard, hdisj⟩
    have hsize : ∀ E ∈ M, E.card = r := by
      intro E hE
      exact (Finset.mem_powersetCard.mp (hM hE)).2
    have hcount : (M.biUnion id).card = r * k := by
      rw [Finset.card_biUnion hdisj]
      simp only [id_eq, Finset.sum_congr rfl hsize, Finset.sum_const,
        smul_eq_mul, hcard, Nat.mul_comm k r]
    have hle : (M.biUnion id).card ≤ n := by
      simpa using (M.biUnion id).card_le_univ
    omega
  apply Finset.le_sup_of_le (b := (Finset.univ : Finset (Fin n)).powersetCard r)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), hno⟩
  · simp

lemma f_one (n r : ℕ) : f n r 1 = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  unfold f
  apply Finset.sup_le
  intro H hH
  have hno := (Finset.mem_filter.mp hH).2
  have hHempty : H = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro E hE
    apply hno
    refine ⟨{E}, ?_, by simp, ?_⟩
    · simpa using hE
    · simpa using Set.pairwiseDisjoint_singleton E id
  simp [hHempty]

lemma erdos_1020_boundary (r k : ℕ) (hr : 3 ≤ r) (hk : 0 < k) :
    f (r * k - 1) r k =
      max ((r * k - 1).choose r)
        ((r * k - 1).choose r - (r * k - 1 - k + 1).choose r) := by
  rw [f_eq_choose_of_lt]
  · exact (max_eq_left (Nat.sub_le _ _)).symm
  · have : 0 < r * k := Nat.mul_pos (by omega) hk
    omega

lemma choose_le_f_of_lt (n r k t : ℕ) (htn : t ≤ n) (htk : t < r * k) :
    t.choose r ≤ f n r k := by
  classical
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simpa using htn)
  unfold f
  apply Finset.le_sup_of_le (b := S.powersetCard r)
  · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.powersetCard_mono hS), ?_⟩
    rintro ⟨M, hM, hcard, hdisj⟩
    have hsize : ∀ E ∈ M, E.card = r := by
      intro E hE
      exact (Finset.mem_powersetCard.mp (hM hE)).2
    have hcount : (M.biUnion id).card = r * k := by
      rw [Finset.card_biUnion hdisj]
      simp only [id_eq, Finset.sum_congr rfl hsize, Finset.sum_const,
        smul_eq_mul, hcard, Nat.mul_comm k r]
    have hsub : M.biUnion id ⊆ S := by
      intro x hx
      obtain ⟨E, hE, hx⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_powersetCard.mp (hM hE)).1 hx
    have := Finset.card_le_card hsub
    omega
  · simp [hScard]

lemma star_le_f (n r k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    n.choose r - (n - k + 1).choose r ≤ f n r k := by
  classical
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq
    (n := k - 1) (s := (Finset.univ : Finset (Fin n))) (by simp; omega)
  let U : Finset (Fin n) := Finset.univ
  let H := U.powersetCard r \ (U \ S).powersetCard r
  have hHsub : H ⊆ U.powersetCard r := Finset.sdiff_subset
  have hmeet : ∀ E ∈ H, 0 < (E ∩ S).card := by
    intro E hE
    obtain ⟨hEr, hES⟩ := Finset.mem_sdiff.mp hE
    apply Finset.card_pos.mpr
    by_contra hempty
    apply hES
    refine Finset.mem_powersetCard.mpr ⟨?_, (Finset.mem_powersetCard.mp hEr).2⟩
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_powersetCard.mp hEr).1 hx, ?_⟩
    intro hxS
    exact hempty ⟨x, Finset.mem_inter.mpr ⟨hx, hxS⟩⟩
  have hno : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      (M : Set (Finset (Fin n))).PairwiseDisjoint id := by
    rintro ⟨M, hM, hcard, hdisj⟩
    have hdisj' : (M : Set (Finset (Fin n))).PairwiseDisjoint (fun E ↦ E ∩ S) :=
      hdisj.mono (fun E ↦ Finset.inter_subset_left)
    have hsub : M.biUnion (fun E ↦ E ∩ S) ⊆ S := by
      intro x hx
      obtain ⟨E, hE, hx⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hx).2
    have hbound := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj'] at hbound
    have hsum : M.card ≤ ∑ E ∈ M, (E ∩ S).card := by
      calc
        M.card = ∑ E ∈ M, 1 := by simp
        _ ≤ ∑ E ∈ M, (E ∩ S).card :=
          Finset.sum_le_sum (fun E hE ↦ hmeet E (hM hE))
    omega
  unfold f
  apply Finset.le_sup_of_le (b := H)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hHsub, hno⟩
  · dsimp [H]
    rw [Finset.card_sdiff_of_subset
      (Finset.powersetCard_mono (Finset.sdiff_subset))]
    simp only [Finset.card_powersetCard, Finset.card_sdiff_of_subset hS,
      Finset.card_univ, Fintype.card_fin, hScard, U]
    have : n - (k - 1) = n - k + 1 := by omega
    simp [this]

lemma erdos_1020_lower (r n k : ℕ) (hr : 3 ≤ r) (hk : 0 < k)
    (hn : r * k - 1 ≤ n) :
    max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r) ≤ f n r k := by
  apply max_le
  · apply choose_le_f_of_lt n r k (r * k - 1) hn
    have : 0 < r * k := Nat.mul_pos (by omega) hk
    omega
  · apply star_le_f n r k hk
    have : 2 * k ≤ r * k := Nat.mul_le_mul_right k (by omega)
    omega

lemma f_two_le (n r : ℕ) (hr : 0 < r) (hn : 2 * r ≤ n) :
    f n r 2 ≤ (n - 1).choose (r - 1) := by
  classical
  unfold f
  apply Finset.sup_le
  intro H hH
  obtain ⟨hH, hno⟩ := Finset.mem_filter.mp hH
  have hsub := Finset.mem_powerset.mp hH
  have hsized : (H : Set (Finset (Fin n))).Sized r := by
    intro E hE
    exact (Finset.mem_powersetCard.mp (hsub hE)).2
  apply Finset.erdos_ko_rado _ hsized (by omega)
  intro E hE F hF hdisj
  have hne : E ≠ F := by
    intro h
    subst F
    have hempty := disjoint_self.mp hdisj
    have := hsized hE
    simp [hempty] at this
    omega
  apply hno
  refine ⟨{E, F}, ?_, ?_, ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hE, hF⟩
  · simp [hne]
  · simpa [Set.pairwiseDisjoint_insert, hne] using hdisj

lemma erdos_1020_two (r n : ℕ) (hr : 3 ≤ r) (hn : r * 2 - 1 ≤ n) :
    f n r 2 = max ((r * 2 - 1).choose r) (n.choose r - (n - 2 + 1).choose r) := by
  by_cases heq : n = r * 2 - 1
  · subst n
    exact erdos_1020_boundary r 2 hr (by omega)
  have hn' : 2 * r ≤ n := by omega
  apply le_antisymm _ (erdos_1020_lower r n 2 hr (by omega) hn)
  apply (f_two_le n r (by omega) hn').trans
  have heq' : (n - 1).choose (r - 1) = n.choose r - (n - 2 + 1).choose r := by
    rw [Nat.choose_eq_choose_pred_add (n := n) (k := r) (by omega) (by omega)]
    have : n - 2 + 1 = n - 1 := by omega
    simp [this]
  rw [heq']
  exact le_max_right _ _

lemma exists_perm_image_eq {α : Type*} [Fintype α] [DecidableEq α]
    (S T : Finset α) (hcard : S.card = T.card) :
    ∃ p : Equiv.Perm α, S.image p = T := by
  classical
  let e : S ≃ T := Fintype.equivOfCardEq (by simpa using hcard)
  let e' : {a : α // a ∉ S} ≃ {a : α // a ∉ T} :=
    Fintype.equivOfCardEq (by simpa using congrArg (fun m ↦ Fintype.card α - m) hcard)
  let p := Equiv.subtypeCongr e e'
  refine ⟨p, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    change p a ∈ T
    simpa [p, Equiv.subtypeCongr, ha] using (e ⟨a, ha⟩).prop
  · simpa [Finset.card_image_of_injective _ p.injective] using hcard.ge

lemma uniform_perm_sum {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset (Finset α)) (S T : Finset α) (hcard : S.card = T.card) :
    (∑ p : Equiv.Perm α, if S.image p ∈ H then 1 else 0 : ℕ) =
      ∑ p : Equiv.Perm α, if T.image p ∈ H then 1 else 0 := by
  classical
  obtain ⟨q, rfl⟩ := exists_perm_image_eq S T hcard
  symm
  simpa only [Finset.image_image, Equiv.mulRight, Equiv.Perm.coe_mul]
    using Equiv.sum_comp (Equiv.mulRight q)
      (fun p : Equiv.Perm α ↦ if S.image p ∈ H then (1 : ℕ) else 0)

lemma sum_perm_image_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (H : Finset (Finset α))
    (hH : H ⊆ (Finset.univ : Finset α).powersetCard r) (p : Equiv.Perm α) :
    (∑ E ∈ (Finset.univ : Finset α).powersetCard r,
      if E.image p ∈ H then 1 else 0 : ℕ) = H.card := by
  classical
  rw [Finset.sum_boole, Nat.cast_id]
  let A := ((Finset.univ : Finset α).powersetCard r).filter (fun E ↦ E.image p ∈ H)
  have himage : A.image (Finset.image p) = H := by
    ext E
    constructor
    · intro hE
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
      exact (Finset.mem_filter.mp hF).2
    · intro hE
      have hF : E.image p.symm ∈ A := by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_powersetCard.mpr
          refine ⟨Finset.subset_univ _, ?_⟩
          rw [Finset.card_image_of_injective _ p.symm.injective]
          exact (Finset.mem_powersetCard.mp (hH hE)).2
        · simpa [Finset.image_image, Function.comp_def] using hE
      exact Finset.mem_image.mpr
        ⟨E.image p.symm, hF, by simp [Finset.image_image, Function.comp_def]⟩
  have := congrArg Finset.card himage
  rwa [Finset.card_image_of_injective _ (Finset.image_injective p.injective)] at this

lemma matching_image_sum_le {α : Type*} [DecidableEq α]
    (H M : Finset (Finset α)) (k : ℕ)
    (hM : (M : Set (Finset α)).PairwiseDisjoint id)
    (hno : ¬ ∃ N : Finset (Finset α), N ⊆ H ∧ N.card = k ∧
      (N : Set (Finset α)).PairwiseDisjoint id) (p : Equiv.Perm α) :
    (∑ E ∈ M, if E.image p ∈ H then 1 else 0 : ℕ) ≤ k - 1 := by
  classical
  rw [Finset.sum_boole, Nat.cast_id]
  let A := M.filter (fun E ↦ E.image p ∈ H)
  let B := A.image (Finset.image p)
  have hB : B ⊆ H := by
    intro E hE
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
    exact (Finset.mem_filter.mp hF).2
  have hBd : (B : Set (Finset α)).PairwiseDisjoint id := by
    intro E hE F hF hne
    obtain ⟨E', hE', rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
    apply (Finset.disjoint_image p.injective).mpr
    apply hM (Finset.mem_filter.mp hE').1 (Finset.mem_filter.mp hF').1
    exact fun heq ↦ hne (congrArg (Finset.image p) heq)
  have hcard : B.card < k := by
    by_contra h
    obtain ⟨N, hNB, hNc⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
    exact hno ⟨N, hNB.trans hB, hNc, hBd.subset hNB⟩
  dsimp [B] at hcard
  rw [Finset.card_image_of_injective _ (Finset.image_injective p.injective)] at hcard
  exact Nat.le_sub_one_of_lt hcard

lemma matching_averaging_bound {α : Type*} [Fintype α] [DecidableEq α]
    (r k : ℕ) (H M : Finset (Finset α))
    (hH : H ⊆ (Finset.univ : Finset α).powersetCard r)
    (hM : M ⊆ (Finset.univ : Finset α).powersetCard r)
    (hMd : (M : Set (Finset α)).PairwiseDisjoint id)
    (hno : ¬ ∃ N : Finset (Finset α), N ⊆ H ∧ N.card = k ∧
      (N : Set (Finset α)).PairwiseDisjoint id) :
    M.card * H.card ≤ (k - 1) * (Fintype.card α).choose r := by
  classical
  obtain hMempty | ⟨E₀, hE₀⟩ := M.eq_empty_or_nonempty
  · simp [hMempty]
  let U := (Finset.univ : Finset α).powersetCard r
  let d : Finset α → ℕ := fun E ↦ ∑ p : Equiv.Perm α, if E.image p ∈ H then 1 else 0
  have hd : ∀ E ∈ U, d E = d E₀ := by
    intro E hE
    apply uniform_perm_sum
    exact (Finset.mem_powersetCard.mp hE).2.trans
      (Finset.mem_powersetCard.mp (hM hE₀)).2.symm
  have htotal : U.card * d E₀ = Fintype.card (Equiv.Perm α) * H.card := by
    calc
      U.card * d E₀ = ∑ E ∈ U, d E := by
        rw [Finset.sum_congr rfl hd]
        simp
      _ = ∑ p : Equiv.Perm α, ∑ E ∈ U, if E.image p ∈ H then 1 else 0 :=
        Finset.sum_comm
      _ = Fintype.card (Equiv.Perm α) * H.card := by
        simp [U, sum_perm_image_indicator r H hH]
  have hpartial : M.card * d E₀ ≤ Fintype.card (Equiv.Perm α) * (k - 1) := by
    calc
      M.card * d E₀ = ∑ E ∈ M, d E := by
        rw [Finset.sum_congr rfl (fun E hE ↦ hd E (hM hE))]
        simp
      _ = ∑ p : Equiv.Perm α, ∑ E ∈ M, if E.image p ∈ H then 1 else 0 :=
        Finset.sum_comm
      _ ≤ ∑ _p : Equiv.Perm α, (k - 1) :=
        Finset.sum_le_sum (fun p _ ↦ matching_image_sum_le H M k hMd hno p)
      _ = Fintype.card (Equiv.Perm α) * (k - 1) := by simp
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card (Equiv.Perm α)) _ Fintype.card_pos
  calc
    Fintype.card (Equiv.Perm α) * (M.card * H.card) = M.card * (U.card * d E₀) := by
      rw [htotal]; ring
    _ = U.card * (M.card * d E₀) := by ring
    _ ≤ U.card * (Fintype.card (Equiv.Perm α) * (k - 1)) :=
      Nat.mul_le_mul_left _ hpartial
    _ = Fintype.card (Equiv.Perm α) * ((k - 1) * (Fintype.card α).choose r) := by
      simp [U, Finset.card_powersetCard]; ring

lemma exists_uniform_matching {α : Type*} [Fintype α] [DecidableEq α]
    (r q : ℕ) (hr : 0 < r) (hn : r * q ≤ Fintype.card α) :
    ∃ M : Finset (Finset α), M ⊆ (Finset.univ : Finset α).powersetCard r ∧
      M.card = q ∧ (M : Set (Finset α)).PairwiseDisjoint id := by
  classical
  induction q with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ q ih =>
    obtain ⟨M, hM, hMc, hMd⟩ := ih (by nlinarith)
    have hsize : ∀ E ∈ M, E.card = r := by
      intro E hE
      exact (Finset.mem_powersetCard.mp (hM hE)).2
    have hcount : (M.biUnion id).card = r * q := by
      rw [Finset.card_biUnion hMd]
      simp only [id_eq, Finset.sum_congr rfl hsize, Finset.sum_const,
        smul_eq_mul, hMc, Nat.mul_comm q r]
    have hcompl : r ≤ ((Finset.univ : Finset α) \ M.biUnion id).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcount]
      rw [Nat.mul_succ] at hn
      omega
    obtain ⟨E, hE, hEc⟩ := Finset.exists_subset_card_eq hcompl
    have hdisj : Disjoint E (M.biUnion id) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.mem_sdiff.mp (hE ha)).2 hb
    have hEm : E ∉ M := by
      intro hEm
      have hh := (Finset.disjoint_biUnion_right E M id).mp hdisj E hEm
      have : E = ∅ := disjoint_self.mp hh
      simp [this] at hEc
      omega
    refine ⟨insert E M, ?_, by simp [hEm, hMc], ?_⟩
    · apply Finset.insert_subset_iff.mpr
      exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hEc⟩, hM⟩
    · rw [Finset.coe_insert]
      apply (Set.pairwiseDisjoint_insert_of_notMem (show E ∉ (M : Set (Finset α)) from hEm)).mpr
      exact ⟨hMd, (Finset.disjoint_biUnion_right E M id).mp hdisj⟩

lemma f_packing_bound (n r k q : ℕ) (hr : 0 < r) (hn : r * q ≤ n) :
    q * f n r k ≤ (k - 1) * n.choose r := by
  classical
  obtain ⟨M, hM, hMc, hMd⟩ := exists_uniform_matching (α := Fin n) r q hr (by simpa using hn)
  obtain rfl | hq := Nat.eq_zero_or_pos q
  · simp
  suffices f n r k ≤ (k - 1) * n.choose r / q by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp this
  unfold f
  apply Finset.sup_le
  intro H hH
  obtain ⟨hH, hno⟩ := Finset.mem_filter.mp hH
  apply (Nat.le_div_iff_mul_le hq).mpr
  simpa [hMc, Nat.mul_comm] using
    matching_averaging_bound r k H M (Finset.mem_powerset.mp hH) hM hMd hno

lemma f_mul_le (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    f (r * k) r k ≤ (r * k - 1).choose r := by
  have hbound := f_packing_bound (r * k) r k k hr le_rfl
  have hn : 0 < r * k := Nat.mul_pos hr hk
  have hid := Nat.choose_mul_succ_eq (r * k - 1) r
  have hsucc : r * k - 1 + 1 = r * k := by omega
  rw [hsucc] at hid
  have hsub : r * k - r = r * (k - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hsub] at hid
  have heq : (k - 1) * (r * k).choose r = k * (r * k - 1).choose r := by
    apply Nat.eq_of_mul_eq_mul_left hr
    nlinarith [hid]
  rw [heq] at hbound
  exact Nat.le_of_mul_le_mul_left hbound hk

lemma erdos_1020_at_mul (r k : ℕ) (hr : 3 ≤ r) (hk : 0 < k) :
    f (r * k) r k = max ((r * k - 1).choose r)
      ((r * k).choose r - (r * k - k + 1).choose r) := by
  apply le_antisymm
  · exact (f_mul_le r k (by omega) hk).trans (le_max_left _ _)
  · exact erdos_1020_lower r (r * k) k hr hk (Nat.sub_le _ _)

lemma cover_card_bound {α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (H : Finset (Finset α)) (S : Finset α)
    (hH : H ⊆ (Finset.univ : Finset α).powersetCard r)
    (hcover : ∀ E ∈ H, ¬ Disjoint E S) :
    H.card ≤ (Fintype.card α).choose r - (Fintype.card α - S.card).choose r := by
  classical
  have hsub : H ⊆ (Finset.univ : Finset α).powersetCard r \
      ((Finset.univ : Finset α) \ S).powersetCard r := by
    intro E hE
    refine Finset.mem_sdiff.mpr ⟨hH hE, ?_⟩
    intro he
    apply hcover E hE
    apply Finset.disjoint_left.mpr
    intro a ha haS
    exact (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp he).1 ha)).2 haS
  have hb := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.powersetCard_mono Finset.sdiff_subset)] at hb
  simpa [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ S)] using hb

lemma cover_star_bound (n r k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (H : Finset (Finset (Fin n))) (S : Finset (Fin n))
    (hH : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r)
    (hcover : ∀ E ∈ H, ¬ Disjoint E S) (hSc : S.card ≤ k - 1) :
    H.card ≤ n.choose r - (n - k + 1).choose r := by
  have hbound : H.card ≤ n.choose r - (n - S.card).choose r := by
    simpa using cover_card_bound r H S hH hcover
  apply hbound.trans
  apply Nat.sub_le_sub_left
  exact Nat.choose_le_choose r (by omega)

lemma erdos_1020_one (r n : ℕ) (hr : 3 ≤ r) (hn : r * 1 - 1 ≤ n) :
    f n r 1 = max ((r * 1 - 1).choose r) (n.choose r - (n - 1 + 1).choose r) := by
  rw [f_one]
  have hnp : 0 < n := by omega
  have hrp : 0 < r := by omega
  simp [Nat.sub_add_cancel hnp, Nat.choose_eq_zero_of_lt (show r - 1 < r by omega)]

end Erdos1020
