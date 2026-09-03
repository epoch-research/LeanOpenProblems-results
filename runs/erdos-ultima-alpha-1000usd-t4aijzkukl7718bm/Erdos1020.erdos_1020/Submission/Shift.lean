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

private def NoMatching {α : Type*} (H : Finset (Finset α)) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = k ∧
    (M : Set (Finset α)).PairwiseDisjoint id

private lemma matching_card_lt {α : Type*} (H M : Finset (Finset α)) (k : ℕ)
    (hno : NoMatching H k) (hMH : M ⊆ H)
    (hMd : (M : Set (Finset α)).PairwiseDisjoint id) : M.card < k := by
  classical
  by_contra h
  obtain ⟨N, hNM, hNc⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
  exact hno ⟨N, hNM.trans hMH, hNc, hMd.subset hNM⟩

private lemma maximal_matching_cover {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (k : ℕ) (hno : NoMatching H k)
    (hne : ∀ E ∈ H, E.Nonempty) :
    ∃ M : Finset (Finset α), M ⊆ H ∧ M.card < k ∧
      (M : Set (Finset α)).PairwiseDisjoint id ∧
      ∀ E ∈ H, ¬ Disjoint E (M.biUnion id) := by
  classical
  let P : Finset (Finset (Finset α)) := H.powerset.filter
    (fun M : Finset (Finset α) ↦ (M : Set (Finset α)).PairwiseDisjoint id)
  have hP : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image P Finset.card hP
  have hMH : M ⊆ H := Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
  have hMd : (M : Set (Finset α)).PairwiseDisjoint id := (Finset.mem_filter.mp hM).2
  refine ⟨M, hMH, matching_card_lt H M k hno hMH hMd, hMd, ?_⟩
  intro E hE hdisj
  have hEm : E ∉ M := by
    intro hEm
    have hh := (Finset.disjoint_biUnion_right E M id).mp hdisj E hEm
    exact (hne E hE).ne_empty (disjoint_self.mp hh)
  have hnew : insert E M ∈ P := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨hE, hMH⟩), ?_⟩
    rw [Finset.coe_insert]
    exact hMd.insert_of_notMem hEm ((Finset.disjoint_biUnion_right E M id).mp hdisj)
  have hbound := hmax (insert E M) hnew
  simp [hEm] at hbound

private lemma family_card_le_sum_degrees {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (S : Finset α) (hcover : ∀ E ∈ H, ¬ Disjoint E S) :
    H.card ≤ ∑ x ∈ S, (H.filter (fun E ↦ x ∈ E)).card := by
  classical
  have hsub : H ⊆ S.biUnion (fun x ↦ H.filter (fun E ↦ x ∈ E)) := by
    intro E hE
    obtain ⟨x, hxE, hxS⟩ := Finset.not_disjoint_iff.mp (hcover E hE)
    exact Finset.mem_biUnion.mpr ⟨x, hxS, Finset.mem_filter.mpr ⟨hE, hxE⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

private lemma uniform_family_containing_bound {α : Type*} [DecidableEq α]
    (U S : Finset α) (r : ℕ) (H : Finset (Finset α))
    (hSU : S ⊆ U) (hH : H ⊆ U.powersetCard r) (hS : ∀ E ∈ H, S ⊆ E) :
    H.card ≤ (U.card - S.card).choose (r - S.card) := by
  classical
  have hinj : (H : Set (Finset α)).InjOn (fun E ↦ E \ S) := by
    intro E hE F hF heq
    calc
      E = (E \ S) ∪ S := (Finset.sdiff_union_of_subset (hS E hE)).symm
      _ = (F \ S) ∪ S := congrArg (fun T ↦ T ∪ S) heq
      _ = F := Finset.sdiff_union_of_subset (hS F hF)
  have hsub : H.image (fun E ↦ E \ S) ⊆ (U \ S).powersetCard (r - S.card) := by
    intro E hE
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨hxF, hxS⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powersetCard.mp (hH hF)).1 hxF, hxS⟩
    · rw [Finset.card_sdiff_of_subset (hS F hF), (Finset.mem_powersetCard.mp (hH hF)).2]
  calc
    H.card = (H.image (fun E ↦ E \ S)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((U \ S).powersetCard (r - S.card)).card := Finset.card_le_card hsub
    _ = (U.card - S.card).choose (r - S.card) := by
      rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hSU]

private lemma uniform_matching_union {α : Type*} [DecidableEq α]
    (r : ℕ) (M : Finset (Finset α))
    (hsize : ∀ E ∈ M, E.card = r)
    (hdisj : (M : Set (Finset α)).PairwiseDisjoint id) :
    (M.biUnion id).card = r * M.card := by
  rw [Finset.card_biUnion hdisj]
  simp only [id_eq, Finset.sum_congr rfl hsize, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

private lemma low_degree_bound {α : Type*} [DecidableEq α]
    (U : Finset α) (r k D : ℕ) (H : Finset (Finset α))
    (hr : 0 < r) (hH : H ⊆ U.powersetCard r) (hno : NoMatching H k)
    (hdeg : ∀ x ∈ U, (H.filter (fun E ↦ x ∈ E)).card ≤ D) :
    H.card ≤ r * (k - 1) * D := by
  classical
  have hne : ∀ E ∈ H, E.Nonempty := by
    intro E hE
    apply Finset.card_pos.mp
    rwa [(Finset.mem_powersetCard.mp (hH hE)).2]
  obtain ⟨M, hMH, hMk, hMd, hcover⟩ := maximal_matching_cover H k hno hne
  have hsub : M.biUnion id ⊆ U := by
    apply Finset.biUnion_subset.mpr
    intro E hE
    exact (Finset.mem_powersetCard.mp (hH (hMH hE))).1
  have hsize : ∀ E ∈ M, E.card = r := by
    intro E hE
    exact (Finset.mem_powersetCard.mp (hH (hMH hE))).2
  calc
    H.card ≤ ∑ x ∈ M.biUnion id, (H.filter (fun E ↦ x ∈ E)).card :=
      family_card_le_sum_degrees H (M.biUnion id) hcover
    _ ≤ ∑ _x ∈ M.biUnion id, D := Finset.sum_le_sum (fun x hx ↦ hdeg x (hsub hx))
    _ = r * M.card * D := by simp [uniform_matching_union r M hsize hMd]
    _ ≤ r * (k - 1) * D := Nat.mul_le_mul_right D
      (Nat.mul_le_mul_left r (Nat.le_sub_one_of_lt hMk))

private lemma high_degree_drop {α : Type*} [DecidableEq α]
    (U : Finset α) (r k : ℕ) (H : Finset (Finset α)) (v : α)
    (hvU : v ∈ U) (hH : H ⊆ U.powersetCard r) (hno : NoMatching H (k + 1))
    (hdeg : r * k * (U.card - 2).choose (r - 2) < (H.filter (fun E ↦ v ∈ E)).card) :
    NoMatching (H.filter (fun E ↦ v ∉ E)) k := by
  classical
  rintro ⟨M, hM, hMc, hMd⟩
  let S := M.biUnion id
  let A := H.filter (fun E ↦ v ∈ E)
  have hMH : M ⊆ H := hM.trans (Finset.filter_subset _ _)
  have hsize : ∀ E ∈ M, E.card = r := by
    intro E hE
    exact (Finset.mem_powersetCard.mp (hH (hMH hE))).2
  have hSc : S.card = r * k := by
    dsimp [S]
    rw [uniform_matching_union r M hsize hMd, hMc]
  have hSU : S ⊆ U := by
    apply Finset.biUnion_subset.mpr
    intro E hE
    exact (Finset.mem_powersetCard.mp (hH (hMH hE))).1
  have hvS : v ∉ S := by
    intro hv
    obtain ⟨E, hE, hvE⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp (hM hE)).2 hvE
  have hcover : ∀ E ∈ A, ¬ Disjoint E S := by
    intro E hE hd
    obtain ⟨hEH, hvE⟩ := Finset.mem_filter.mp hE
    have hEm : E ∉ M := by
      intro hEm
      exact (Finset.mem_filter.mp (hM hEm)).2 hvE
    apply hno
    refine ⟨insert E M, Finset.insert_subset_iff.mpr ⟨hEH, hMH⟩, by simp [hEm, hMc], ?_⟩
    rw [Finset.coe_insert]
    exact hMd.insert_of_notMem hEm ((Finset.disjoint_biUnion_right E M id).mp hd)
  have hpair : ∀ x ∈ S, (A.filter (fun E ↦ x ∈ E)).card ≤
      (U.card - 2).choose (r - 2) := by
    intro x hx
    have hvx : v ≠ x := by rintro rfl; exact hvS hx
    have hpairU : ({v, x} : Finset α) ⊆ U :=
      Finset.insert_subset_iff.mpr ⟨hvU, Finset.singleton_subset_iff.mpr (hSU hx)⟩
    have hpairH : A.filter (fun E ↦ x ∈ E) ⊆ U.powersetCard r :=
      (Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans hH)
    have hcontain : ∀ E ∈ A.filter (fun E ↦ x ∈ E), ({v, x} : Finset α) ⊆ E := by
      intro E hE
      obtain ⟨hEA, hxE⟩ := Finset.mem_filter.mp hE
      have hvE := (Finset.mem_filter.mp hEA).2
      exact Finset.insert_subset_iff.mpr ⟨hvE, Finset.singleton_subset_iff.mpr hxE⟩
    simpa [hvx] using uniform_family_containing_bound U {v, x} r
      (A.filter (fun E ↦ x ∈ E)) hpairU hpairH hcontain
  have hbound : A.card ≤ r * k * (U.card - 2).choose (r - 2) := by
    calc
      A.card ≤ ∑ x ∈ S, (A.filter (fun E ↦ x ∈ E)).card :=
        family_card_le_sum_degrees A S hcover
      _ ≤ ∑ _x ∈ S, (U.card - 2).choose (r - 2) :=
        Finset.sum_le_sum hpair
      _ = r * k * (U.card - 2).choose (r - 2) := by simp [hSc]
  exact Nat.not_lt_of_ge hbound hdeg

private lemma large_n_upper {α : Type*} [DecidableEq α]
    (r k : ℕ) (hr : 2 ≤ r) (U : Finset α) (H : Finset (Finset α))
    (hH : H ⊆ U.powersetCard r) (hno : NoMatching H k) (hk : 0 < k)
    (hn : r ^ 3 * k ^ 2 + 1 ≤ U.card) :
    H.card + (U.card - k + 1).choose r ≤ U.card.choose r := by
  classical
  induction k generalizing U H with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      have he : H = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro E hE
        apply hno
        exact ⟨{E}, by simpa using hE, by simp, by simp⟩
      have hp : 0 < r ^ 3 := pow_pos (by omega) 3
      have hn0 : 0 < U.card := by omega
      simp [he, Nat.sub_add_cancel hn0]
    have hkpos : 0 < k := by omega
    have hp : 0 < r ^ 3 := pow_pos (by omega) 3
    have hkpow : k + 1 ≤ (k + 1) ^ 2 := by nlinarith
    have hpkn : (k + 1) ^ 2 ≤ r ^ 3 * (k + 1) ^ 2 :=
      Nat.le_mul_of_pos_left _ hp
    have hnkn : k + 2 ≤ U.card := by omega
    have hn2 : 2 ≤ U.card := by omega
    have hindsize : r ^ 3 * k ^ 2 + 1 ≤ U.card - 1 := by
      have hsq : k ^ 2 + 1 ≤ (k + 1) ^ 2 := by nlinarith
      have hm := Nat.mul_le_mul_left (r ^ 3) hsq
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    by_cases hhigh : ∃ v ∈ U,
        r * k * (U.card - 2).choose (r - 2) < (H.filter (fun E ↦ v ∈ E)).card
    · obtain ⟨v, hvU, hdeg⟩ := hhigh
      let A := H.filter (fun E ↦ v ∉ E)
      have hAU : A ⊆ (U.erase v).powersetCard r := by
        intro E hE
        obtain ⟨hEH, hvE⟩ := Finset.mem_filter.mp hE
        refine Finset.mem_powersetCard.mpr ⟨?_, (Finset.mem_powersetCard.mp (hH hEH)).2⟩
        intro x hx
        apply Finset.mem_erase.mpr
        refine ⟨?_, (Finset.mem_powersetCard.mp (hH hEH)).1 hx⟩
        intro heq
        subst x
        exact hvE hx
      have hAno : NoMatching A k := high_degree_drop U r k H v hvU hH hno hdeg
      have hAsize : r ^ 3 * k ^ 2 + 1 ≤ (U.erase v).card := by
        rwa [Finset.card_erase_of_mem hvU]
      have hi := ih (U.erase v) A hAU hAno hkpos hAsize
      rw [Finset.card_erase_of_mem hvU] at hi
      have hdeg_bound : (H.filter (fun E ↦ v ∈ E)).card ≤
          (U.card - 1).choose (r - 1) := by
        simpa using uniform_family_containing_bound U {v} r
          (H.filter (fun E ↦ v ∈ E)) (Finset.singleton_subset_iff.mpr hvU)
          ((Finset.filter_subset _ _).trans hH)
          (fun E hE ↦ Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hE).2)
      have hsplit := Finset.card_filter_add_card_filter_not (s := H) (fun E : Finset α ↦ v ∈ E)
      have hid := Nat.choose_eq_choose_pred_add (n := U.card) (k := r) (by omega) (by omega)
      have hidx : U.card - 1 - k + 1 = U.card - (k + 1) + 1 := by omega
      rw [hidx] at hi
      dsimp [A] at hi
      omega
    · push_neg at hhigh
      have hb := low_degree_bound U r (k + 1)
        (r * k * (U.card - 2).choose (r - 2)) H (by omega) hH hno hhigh
      simp only [Nat.add_sub_cancel] at hb
      have hcoef : (r * k) ^ 2 * (r - 1) ≤ U.card - 1 := by
        calc
          (r * k) ^ 2 * (r - 1) ≤ (r * k) ^ 2 * r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = r ^ 3 * k ^ 2 := by ring
          _ ≤ U.card - 1 := by omega
      have hid := Nat.add_one_mul_choose_eq (U.card - 2) (r - 2)
      have hnidx : U.card - 2 + 1 = U.card - 1 := by omega
      have hridx : r - 2 + 1 = r - 1 := by omega
      rw [hnidx, hridx] at hid
      have hlow : (r * k) ^ 2 * (U.card - 2).choose (r - 2) ≤
          (U.card - 1).choose (r - 1) := by
        apply Nat.le_of_mul_le_mul_left (c := r - 1) _ (by omega)
        calc
          (r - 1) * ((r * k) ^ 2 * (U.card - 2).choose (r - 2)) =
              ((r * k) ^ 2 * (r - 1)) * (U.card - 2).choose (r - 2) := by ring
          _ ≤ (U.card - 1) * (U.card - 2).choose (r - 2) := Nat.mul_le_mul_right _ hcoef
          _ = (r - 1) * (U.card - 1).choose (r - 1) := by rw [hid]; ring
      have hHcard : H.card ≤ (U.card - 1).choose (r - 1) := by
        apply le_trans hb
        convert hlow using 1 <;> ring
      have hchoose : (U.card - (k + 1) + 1).choose r ≤ (U.card - 1).choose r :=
        Nat.choose_le_choose r (by omega)
      have hPascal := Nat.choose_eq_choose_pred_add (n := U.card) (k := r) (by omega) (by omega)
      omega

lemma f_large_le (n r k : ℕ) (hr : 2 ≤ r) (hk : 0 < k)
    (hn : r ^ 3 * k ^ 2 + 1 ≤ n) :
    f n r k ≤ n.choose r - (n - k + 1).choose r := by
  classical
  unfold f
  apply Finset.sup_le
  intro H hH
  obtain ⟨hH, hno⟩ := Finset.mem_filter.mp hH
  have hb := large_n_upper r k hr (Finset.univ : Finset (Fin n)) H
    (Finset.mem_powerset.mp hH) hno hk (by simpa using hn)
  simpa using Nat.le_sub_of_add_le hb

lemma erdos_1020_large (r n k : ℕ) (hr : 3 ≤ r) (hk : 0 < k)
    (hn : r ^ 3 * k ^ 2 + 1 ≤ n) :
    f n r k = max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r) := by
  have hrpow : r ≤ r ^ 3 := le_self_pow (by omega) (by decide)
  have hkpow : k ≤ k ^ 2 := le_self_pow hk (by decide)
  have hmul := Nat.mul_le_mul hrpow hkpow
  apply le_antisymm
  · exact (f_large_le n r k (by omega) hk hn).trans (le_max_right _ _)
  · exact erdos_1020_lower r n k hr hk (by omega)

lemma erdos_1020_of_middle
    (hmiddle : ∀ r n k : ℕ, 3 ≤ r → 3 ≤ k → r * k < n → n ≤ r ^ 3 * k ^ 2 →
      f n r k ≤ max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r)) :
    ∀ r : ℕ, 3 ≤ r → ∀ n k : ℕ, 0 < k → r * k - 1 ≤ n →
      f n r k = max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r) := by
  intro r hr n k hk hn
  by_cases hk1 : k = 1
  · subst k
    exact erdos_1020_one r n hr hn
  by_cases hk2 : k = 2
  · subst k
    exact erdos_1020_two r n hr hn
  by_cases hn1 : n = r * k - 1
  · subst n
    exact erdos_1020_boundary r k hr hk
  by_cases hn2 : n = r * k
  · subst n
    exact erdos_1020_at_mul r k hr hk
  by_cases hlarge : r ^ 3 * k ^ 2 + 1 ≤ n
  · exact erdos_1020_large r n k hr hk hlarge
  apply le_antisymm
  · exact hmiddle r n k hr (by omega) (by omega) (by omega)
  · exact erdos_1020_lower r n k hr hk hn

private lemma swap_image_mem_notMem {α : Type*} [DecidableEq α]
    (E : Finset α) (a b : α) (ha : a ∈ E) (hb : b ∉ E) :
    E.image (Equiv.swap a b) = (E ∪ {b}) \ {a} := by
  apply Finset.coe_injective
  simpa [Finset.coe_image, Finset.coe_sdiff, Finset.coe_union, Finset.coe_singleton,
    Set.union_singleton] using Equiv.image_swap_of_mem_of_notMem
      (s := (E : Set α)) ha hb

private lemma swap_image_notMem {α : Type*} [DecidableEq α]
    (E : Finset α) (a b : α) (ha : a ∉ E) (hb : b ∉ E) :
    E.image (Equiv.swap a b) = E := by
  calc
    E.image (Equiv.swap a b) = E.image id := by
      apply Finset.image_congr
      intro x hx
      exact Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hx ha)
        (ne_of_mem_of_not_mem hx hb)
    _ = E := Finset.image_id

private lemma compression_no_matching {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (k : ℕ) (a b : α) (hno : NoMatching H k) :
    NoMatching (UV.compression {a} {b} H) k := by
  classical
  rintro ⟨M, hM, hMc, hMd⟩
  by_cases hMH : M ⊆ H
  · exact hno ⟨M, hMH, hMc, hMd⟩
  simp only [Finset.subset_iff, not_forall, _root_.not_imp] at hMH
  obtain ⟨E, hEM, hEH⟩ := hMH
  have hEC := hM hEM
  have haE : a ∈ E := Finset.singleton_subset_iff.mp
    (UV.le_of_mem_compression_of_notMem hEC hEH)
  have hbE : b ∉ E := Finset.disjoint_singleton_left.mp
    (UV.disjoint_of_mem_compression_of_notMem hEC hEH)
  have hswap : ∀ G ∈ M, G.image (Equiv.swap a b) ∈ H := by
    intro G hGM
    by_cases hGE : G = E
    · subst G
      rw [swap_image_mem_notMem E a b haE hbE]
      exact UV.sup_sdiff_mem_of_mem_compression_of_notMem hEC hEH
    have haG : a ∉ G := by
      intro haG
      exact Finset.disjoint_left.mp (hMd hEM hGM (Ne.symm hGE)) haE haG
    have hGH : G ∈ H := by
      by_contra hnot
      exact haG (Finset.singleton_subset_iff.mp
        (UV.le_of_mem_compression_of_notMem (hM hGM) hnot))
    by_cases hbG : b ∈ G
    · rw [Equiv.swap_comm a b, swap_image_mem_notMem G b a hbG haG]
      exact UV.sup_sdiff_mem_of_mem_compression (hM hGM)
        (Finset.singleton_subset_iff.mpr hbG) (Finset.disjoint_singleton_left.mpr haG)
    · rwa [swap_image_notMem G a b haG hbG]
  apply hno
  refine ⟨M.image (Finset.image (Equiv.swap a b)), ?_, ?_, ?_⟩
  · intro G hG
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hG
    exact hswap F hF
  · rw [Finset.card_image_of_injective _ (Finset.image_injective (Equiv.swap a b).injective), hMc]
  · intro G hG F hF hne
    obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
    obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
    apply (Finset.disjoint_image (Equiv.swap a b).injective).mpr
    exact hMd hG' hF' (fun hh ↦ hne (congrArg (Finset.image (Equiv.swap a b)) hh))

private def shiftMeasure {n : ℕ} (H : Finset (Finset (Fin n))) : ℕ :=
  ∑ E ∈ H, ∑ x ∈ E, 2 ^ (x : ℕ)

open Finset UV Finset.Colex in
private lemma shiftMeasure_compression_lt {n : ℕ} {U V : Finset (Fin n)}
    {hU : U.Nonempty} {hV : V.Nonempty} (h : max' U hU < max' V hV)
    {H : Finset (Finset (Fin n))} (hc : UV.compression U V H ≠ H) :
    shiftMeasure (UV.compression U V H) < shiftMeasure H := by
  rw [compression] at hc ⊢
  have q : ∀ Q ∈ {E ∈ H | compress U V E ∉ H}, compress U V Q ≠ Q := by grind
  have uA : {E ∈ H | compress U V E ∈ H} ∪ {E ∈ H | compress U V E ∉ H} = H :=
    filter_union_filter_not_eq _ _
  have ne₂ : {E ∈ H | compress U V E ∉ H}.Nonempty := by
    contrapose! hc
    rw [filter_image, hc, image_empty, union_empty]
    rwa [hc, union_empty] at uA
  rw [shiftMeasure, shiftMeasure, sum_union compress_disjoint]
  conv_rhs => rw [← uA]
  rw [sum_union (disjoint_filter_filter_not _ _ _), add_lt_add_iff_left, filter_image,
    sum_image compress_injOn]
  refine sum_lt_sum_of_nonempty ne₂ fun E hE ↦ ?_
  simp_rw [← sum_image Fin.val_injective.injOn]
  rw [geomSum_lt_geomSum_iff_toColex_lt_toColex le_rfl,
    toColex_image_lt_toColex_image Fin.val_strictMono]
  exact Finset.UV.toColex_compress_lt_toColex h (q E hE)

private lemma exists_shifted_family (n r k : ℕ) (H : Finset (Finset (Fin n)))
    (hsize : (H : Set (Finset (Fin n))).Sized r) (hno : NoMatching H k) :
    ∃ B : Finset (Finset (Fin n)), B.card = H.card ∧
      (B : Set (Finset (Fin n))).Sized r ∧ NoMatching B k ∧
      ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} B := by
  classical
  let C : Finset (Finset (Finset (Fin n))) := Finset.univ.filter
    (fun B : Finset (Finset (Fin n)) ↦ (B : Set (Finset (Fin n))).Sized r ∧
      NoMatching B k ∧ B.card = H.card)
  have hCne : C.Nonempty := ⟨H, by simp [C, hsize, hno]⟩
  obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image C shiftMeasure hCne
  obtain ⟨hBs, hBn, hBc⟩ := (Finset.mem_filter.mp hB).2
  refine ⟨B, hBc, hBs, hBn, ?_⟩
  intro i j hij
  by_contra hc
  change UV.compression {i} {j} B ≠ B at hc
  have hlt := shiftMeasure_compression_lt
    (U := {i}) (V := {j}) (hU := Finset.singleton_nonempty _)
    (hV := Finset.singleton_nonempty _) (by simpa using hij) hc
  have hcomp : UV.compression {i} {j} B ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hBs.uvCompression (by simp),
      compression_no_matching B k i j hBn, ?_⟩
    simpa using hBc
  exact Nat.not_lt_of_ge (hmin _ hcomp) hlt

private lemma extension_no_matching {α : Type*} [Fintype α] [DecidableEq α]
    (r k : ℕ) (H L : Finset (Finset α)) (hno : NoMatching H k)
    (hsize : (L : Set (Finset α)).Sized r)
    (hn : (r + 1) * k ≤ Fintype.card α)
    (hext : ∀ E ∈ L, ∀ x : α, x ∉ E → insert x E ∈ H) : NoMatching L k := by
  classical
  rintro ⟨M, hML, hMc, hMd⟩
  let S := M.biUnion id
  let T := (Finset.univ : Finset α) \ S
  have hSc : S.card = r * k := by
    dsimp [S]
    rw [uniform_matching_union r M (fun E hE ↦ hsize (hML hE)) hMd, hMc]
  have hcard : Fintype.card M ≤ Fintype.card T := by
    simp only [Fintype.card_coe, T,
      Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, hSc, hMc]
    rw [Nat.add_mul, Nat.one_mul] at hn
    omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  let G : M → Finset α := fun E ↦ insert (g E).val E.val
  have hout : ∀ E F : M, (g E).val ∉ F.val := by
    intro E F hx
    have hh : (g E).val ∈ S := Finset.mem_biUnion.mpr ⟨F.val, F.prop, hx⟩
    exact (Finset.mem_sdiff.mp (g E).prop).2 hh
  have hGd : Pairwise (fun E F : M ↦ Disjoint (G E) (G F)) := by
    intro E F hEF
    have hEF' : E.val ≠ F.val := fun hh ↦ hEF (Subtype.ext hh)
    have hgEF : (g E).val ≠ (g F).val := fun hh ↦ hEF (g.injective (Subtype.ext hh))
    dsimp [G]
    simp only [Finset.disjoint_insert_left, Finset.disjoint_insert_right, Finset.mem_insert,
      not_or]
    exact ⟨⟨hgEF.symm, hout F E⟩, hout E F, hMd E.prop F.prop hEF'⟩
  have hGi : Function.Injective G := by
    intro E F hEF
    by_contra hne
    have he : (g E).val ∈ G E := Finset.mem_insert_self _ _
    have hf : (g E).val ∈ G F := hEF ▸ he
    exact Finset.disjoint_left.mp (hGd hne) he hf
  apply hno
  refine ⟨Finset.univ.image G, ?_, ?_, ?_⟩
  · intro E hE
    obtain ⟨F, _, rfl⟩ := Finset.mem_image.mp hE
    exact hext F.val (hML F.prop) (g F).val (hout F F)
  · rw [Finset.card_image_of_injective _ hGi, Finset.card_univ, Fintype.card_coe, hMc]
  · intro E hE F hF hne
    obtain ⟨E', _, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨F', _, rfl⟩ := Finset.mem_image.mp hF
    exact hGd (fun hh ↦ hne (congrArg G hh))

private lemma shifted_replace {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (E : Finset α) (a b : α)
    (hc : UV.IsCompressed {a} {b} H) (hE : E ∈ H) (ha : a ∉ E) (hb : b ∈ E) :
    insert a (E.erase b) ∈ H := by
  classical
  have hmem := UV.compress_mem_compression (u := ({a} : Finset α)) (v := {b}) hE
  rw [hc.eq, UV.compress_of_disjoint_of_le (Finset.disjoint_singleton_left.mpr ha)
    (Finset.singleton_subset_iff.mpr hb)] at hmem
  have hab : a ≠ b := ne_of_mem_of_not_mem hb ha |>.symm
  convert hmem using 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_union,
    Finset.mem_singleton, Finset.sup_eq_union]
  aesop

private lemma shifted_link_no_matching (n r k : ℕ)
    (H : Finset (Finset (Fin (n + 1))))
    (hsize : (H : Set (Finset (Fin (n + 1)))).Sized (r + 1)) (hno : NoMatching H k)
    (hn : (r + 1) * k ≤ n + 1)
    (hshift : ∀ i j : Fin (n + 1), i < j → UV.IsCompressed {i} {j} H) :
    NoMatching ((H.filter (fun E ↦ Fin.last n ∈ E)).image
      (fun E ↦ E.erase (Fin.last n))) k := by
  classical
  let L := (H.filter (fun E ↦ Fin.last n ∈ E)).image (fun E ↦ E.erase (Fin.last n))
  have hLsize : (L : Set (Finset (Fin (n + 1)))).Sized r := by
    intro E hE
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hFH, hvF⟩ := Finset.mem_filter.mp hF
    rw [Finset.card_erase_of_mem hvF, hsize hFH, Nat.add_sub_cancel]
  apply extension_no_matching r k H L hno hLsize (by simpa using hn)
  intro E hE x hx
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨hFH, hvF⟩ := Finset.mem_filter.mp hF
  by_cases hxv : x = Fin.last n
  · subst x
    simpa only [Finset.insert_erase hvF] using hFH
  have hxlt : x < Fin.last n := lt_of_le_of_ne (Fin.le_last x) hxv
  have hxF : x ∉ F := by
    intro h
    exact hx (Finset.mem_erase.mpr ⟨hxv, h⟩)
  exact shifted_replace H F x (Fin.last n) (hshift x (Fin.last n) hxlt) hFH hxF hvF

private lemma family_card_le_f {α : Type*} [DecidableEq α]
    (U : Finset α) (r k : ℕ) (H : Finset (Finset α))
    (hH : H ⊆ U.powersetCard r) (hno : NoMatching H k) : H.card ≤ f U.card r k := by
  classical
  let e : Fin U.card ↪ α :=
    ⟨fun i ↦ (U.equivFin.symm i).val, fun i j hh ↦ U.equivFin.symm.injective (Subtype.ext hh)⟩
  let φ : Finset α → Finset (Fin U.card) := fun E ↦ Finset.univ.filter (fun i ↦ e i ∈ E)
  have himage : ∀ E ⊆ U, (φ E).image e = E := by
    intro E hEU
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro hx
      let i := U.equivFin ⟨x, hEU hx⟩
      have hei : e i = x := by simp [e, i]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hei.symm ▸ hx⟩, hei⟩
  have hφinj : (H : Set (Finset α)).InjOn φ := by
    intro E hE F hF hEF
    have hh := congrArg (Finset.image e) hEF
    rwa [himage E (Finset.mem_powersetCard.mp (hH hE)).1,
      himage F (Finset.mem_powersetCard.mp (hH hF)).1] at hh
  have hφcard : ∀ E ∈ H, (φ E).card = r := by
    intro E hE
    have hh := congrArg Finset.card (himage E (Finset.mem_powersetCard.mp (hH hE)).1)
    rw [Finset.card_image_of_injective _ e.injective,
      (Finset.mem_powersetCard.mp (hH hE)).2] at hh
    exact hh
  have hφno : NoMatching (H.image φ) k := by
    rintro ⟨M, hM, hMc, hMd⟩
    apply hno
    refine ⟨M.image (Finset.image e), ?_, ?_, ?_⟩
    · intro E hE
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
      obtain ⟨G, hGH, hGF⟩ := Finset.mem_image.mp (hM hF)
      rw [← hGF, himage G (Finset.mem_powersetCard.mp (hH hGH)).1]
      exact hGH
    · rw [Finset.card_image_of_injective _ (Finset.image_injective e.injective), hMc]
    · intro E hE F hF hne
      obtain ⟨E', hE', rfl⟩ := Finset.mem_image.mp hE
      obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
      apply (Finset.disjoint_image e.injective).mpr
      exact hMd hE' hF' (fun hh ↦ hne (congrArg (Finset.image e) hh))
  unfold f
  apply Finset.le_sup_of_le (b := H.image φ)
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, hφno⟩
    intro E hE
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hφcard F hF⟩
  · exact (Finset.card_image_of_injOn hφinj).ge

lemma f_shifting_recurrence (n r k : ℕ) (hn : (r + 1) * k ≤ n + 1) :
    f (n + 1) (r + 1) k ≤ f n (r + 1) k + f n r k := by
  classical
  conv_lhs => unfold f
  apply Finset.sup_le
  intro H hH
  obtain ⟨hH, hno⟩ := Finset.mem_filter.mp hH
  have hHsize : (H : Set (Finset (Fin (n + 1)))).Sized (r + 1) := by
    intro E hE
    exact (Finset.mem_powersetCard.mp (Finset.mem_powerset.mp hH hE)).2
  obtain ⟨B, hBc, hBs, hBn, hBshift⟩ := exists_shifted_family (n + 1) (r + 1) k H hHsize hno
  let v := Fin.last n
  let U := (Finset.univ : Finset (Fin (n + 1))).erase v
  let A := B.filter (fun E ↦ v ∉ E)
  let C := B.filter (fun E ↦ v ∈ E)
  let L := C.image (fun E ↦ E.erase v)
  have hUc : U.card = n := by simp [U]
  have hAU : A ⊆ U.powersetCard (r + 1) := by
    intro E hE
    obtain ⟨hEB, hvE⟩ := Finset.mem_filter.mp hE
    refine Finset.mem_powersetCard.mpr ⟨?_, hBs hEB⟩
    intro x hx
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hx hvE, Finset.mem_univ _⟩
  have hAno : NoMatching A k := by
    rintro ⟨M, hM, hMc, hMd⟩
    exact hBn ⟨M, hM.trans (Finset.filter_subset _ _), hMc, hMd⟩
  have hLU : L ⊆ U.powersetCard r := by
    intro E hE
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hFB, hvF⟩ := Finset.mem_filter.mp hF
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
    · rw [Finset.card_erase_of_mem hvF, hBs hFB, Nat.add_sub_cancel]
  have hLno : NoMatching L k := shifted_link_no_matching n r k B hBs hBn hn hBshift
  have hLC : L.card = C.card := by
    apply Finset.card_image_of_injOn
    intro E hE F hF hh
    have hh' := congrArg (insert v) hh
    rwa [Finset.insert_erase (Finset.mem_filter.mp hE).2,
      Finset.insert_erase (Finset.mem_filter.mp hF).2] at hh'
  have hAcard := family_card_le_f U (r + 1) k A hAU hAno
  have hLcard := family_card_le_f U r k L hLU hLno
  rw [hUc] at hAcard hLcard
  rw [hLC] at hLcard
  have hsplit := Finset.card_filter_add_card_filter_not (s := B) (fun E : Finset (Fin (n + 1)) ↦ v ∈ E)
  change C.card + A.card = B.card at hsplit
  omega

private lemma weighted_no_matching {α : Type*} [DecidableEq α]
    (U : Finset α) (H : Finset (Finset α)) (k : ℕ) (w : α → ℚ)
    (hw : ∀ x ∈ U, 0 ≤ w x) (htotal : ∑ x ∈ U, w x < (k : ℚ))
    (hH : ∀ E ∈ H, E ⊆ U) (hedge : ∀ E ∈ H, (1 : ℚ) ≤ ∑ x ∈ E, w x) :
    NoMatching H k := by
  classical
  rintro ⟨M, hM, hMc, hMd⟩
  have hsub : M.biUnion id ⊆ U := by
    apply Finset.biUnion_subset.mpr
    intro E hE
    exact hH E (hM hE)
  have hupper : (∑ x ∈ M.biUnion id, w x) ≤ ∑ x ∈ U, w x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ ↦ hw x hx)
  have hlower : (k : ℚ) ≤ ∑ x ∈ M.biUnion id, w x := by
    calc
      (k : ℚ) = ∑ _E ∈ M, (1 : ℚ) := by simp [hMc]
      _ ≤ ∑ E ∈ M, ∑ x ∈ E, w x := Finset.sum_le_sum (fun E hE ↦ hedge E (hM hE))
      _ = ∑ x ∈ M.biUnion id, w x := (Finset.sum_biUnion hMd).symm
  exact (not_le_of_gt htotal) (hlower.trans hupper)

end Erdos1020
