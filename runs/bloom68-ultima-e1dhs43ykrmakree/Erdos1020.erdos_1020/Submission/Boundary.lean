import Submission.Bounds

/-!
# Two proved special cases of the Erdős matching problem

This file proves the full displayed formula when `k = 2`, using the
Erdős–Ko–Rado theorem, and the boundary `n = r * k`, using finite
permutation averaging. These results do not settle the general conjecture.
-/

namespace Erdos1020

/-- A family of nonempty sets with no two-edge matching is intersecting. -/
theorem intersecting_of_matching_free_two {α : Type*} [DecidableEq α]
    {H : Finset (Finset α)} (hne : ∀ e ∈ H, e.Nonempty)
    (hfree : ¬ ∃ M : Finset (Finset α),
      M ⊆ H ∧ M.card = 2 ∧ (M : Set (Finset α)).PairwiseDisjoint id) :
    (H : Set (Finset α)).Intersecting := by
  classical
  intro a ha b hb hab
  have hneab : a ≠ b := by
    intro h
    subst b
    exact (hne a ha).ne_empty ((Finset.disjoint_self_iff_empty a).mp hab)
  apply hfree
  refine ⟨{a, b}, ?_, by simp [hneab], ?_⟩
  · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro ha hb
  · simpa only [Finset.coe_insert, Finset.coe_singleton,
      Set.pairwiseDisjoint_insert, Set.pairwiseDisjoint_singleton, Set.mem_singleton_iff,
      true_and, forall_eq] using (fun _ : a ≠ b ↦ hab)

/-- EKR bounds every positive-uniform family with no matching of size two. -/
theorem matching_free_two_card_le {n r : ℕ} {H : Finset (Finset (Fin n))}
    (hr : 0 < r) (hn : r * 2 ≤ n)
    (hH : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)),
      M ⊆ H ∧ M.card = 2 ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id) :
    H.card ≤ (n - 1).choose (r - 1) := by
  have hsized : (H : Set (Finset (Fin n))).Sized r :=
    fun e he ↦ (Finset.mem_powersetCard.mp (hH he)).2
  exact Finset.erdos_ko_rado
    (intersecting_of_matching_free_two
      (fun e he ↦ Finset.card_pos.mp (by rw [hsized he]; exact hr)) hfree)
    hsized ((Nat.le_div_iff_mul_le (by decide)).mpr hn)

/-- The EKR upper bound for the extremal function when `n ≥ 2*r`. -/
theorem f_two_le {n r : ℕ} (hr : 0 < r) (hn : r * 2 ≤ n) :
    f n r 2 ≤ (n - 1).choose (r - 1) := by
  classical
  unfold f
  refine Finset.sup_le fun H hH ↦ ?_
  have hc := Finset.mem_filter.mp hH
  exact matching_free_two_card_le hr hn (Finset.mem_powerset.mp hc.1) hc.2

/-- The exact EKR value of the matching extremal function. -/
theorem f_two {n r : ℕ} (hr : 0 < r) (hn : r * 2 ≤ n) :
    f n r 2 = (n - 1).choose (r - 1) := by
  apply le_antisymm (f_two_le hr hn)
  have hlow := cover_lower_bound (n := n) (r := r) (k := 2) (by decide) (by omega)
  have hpred : n - 2 + 1 = n - 1 := by omega
  rw [hpred, Nat.choose_eq_choose_pred_add (by omega) hr, Nat.add_sub_cancel] at hlow
  exact hlow

/-- The full displayed EMC formula for `k = 2`, throughout its standard range. -/
theorem emc_eq_two (r : ℕ) (hr : 3 ≤ r) (n : ℕ) (hn : r * 2 - 1 ≤ n) :
    f n r 2 = max ((r * 2 - 1).choose r)
      (n.choose r - (n - 2 + 1).choose r) := by
  apply le_antisymm
  · by_cases h : n < r * 2
    · have heq : n = r * 2 - 1 := by omega
      rw [f_eq_choose_of_lt h, heq]
      exact le_max_left _ _
    · have hpred : n - 2 + 1 = n - 1 := by omega
      calc
        f n r 2 = (n - 1).choose (r - 1) := f_two (by omega) (by omega)
        _ = n.choose r - (n - 2 + 1).choose r := by
          rw [hpred, Nat.choose_eq_choose_pred_add (n := n) (k := r) (by omega) (by omega),
            Nat.add_sub_cancel]
        _ ≤ max _ _ := le_max_right _ _
  · exact emc_lower_bound r hr n 2 (by decide) hn

/-- Relabel all the edges of a family by a permutation of the vertices. -/
def permuteFamily {α : Type*} (σ : Equiv.Perm α) (P : Finset (Finset α)) :
    Finset (Finset α) :=
  P.map σ.finsetCongr.toEmbedding

@[simp]
theorem card_permuteFamily {α : Type*} (σ : Equiv.Perm α) (P : Finset (Finset α)) :
    (permuteFamily σ P).card = P.card := by
  simp [permuteFamily]

@[simp]
theorem permuteFamily_refl {α : Type*} (P : Finset (Finset α)) :
    permuteFamily (Equiv.refl α) P = P := by
  simp [permuteFamily]

/-- Relabeling twice is relabeling by the composite permutation. -/
theorem permuteFamily_trans {α : Type*} (σ τ : Equiv.Perm α)
    (P : Finset (Finset α)) :
    permuteFamily (σ.trans τ) P = permuteFamily τ (permuteFamily σ P) := by
  simp [permuteFamily, Finset.map_map, ← Equiv.finsetCongr_trans]

/-- Equal-sized subsets of a finite type are related by a vertex permutation. -/
theorem exists_perm_map_eq_of_card_eq {α : Type*} [Fintype α]
    {a b : Finset α} (hab : a.card = b.card) :
    ∃ τ : Equiv.Perm α, a.map τ.toEmbedding = b := by
  classical
  let e : a ≃ b := Finset.equivOfCardEq hab
  refine ⟨e.extendSubtype, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact e.extendSubtype_mem y hy
  · simpa using hab.ge

/-- Every edge of a given size occurs equally often among all permuted copies
of any fixed family. The bijection is composition with a vertex permutation. -/
theorem card_permutations_mem_family_eq {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset (Finset α)) {a b : Finset α} (hab : a.card = b.card) :
    ((Finset.univ : Finset (Equiv.Perm α)).filter
      (fun σ ↦ a ∈ permuteFamily σ P)).card =
    ((Finset.univ : Finset (Equiv.Perm α)).filter
      (fun σ ↦ b ∈ permuteFamily σ P)).card := by
  classical
  obtain ⟨τ, hτ⟩ := exists_perm_map_eq_of_card_eq hab
  apply Finset.card_equiv ((Equiv.refl α).equivCongr τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (a ∈ permuteFamily σ P) ↔ b ∈ permuteFamily (σ.trans τ) P
  rw [permuteFamily_trans, ← hτ]
  change (a ∈ permuteFamily σ P) ↔
    τ.finsetCongr a ∈ (permuteFamily σ P).map τ.finsetCongr.toEmbedding
  simp [Finset.map_map]

/-- Relabeling preserves uniformity. -/
theorem permuteFamily_uniform {α : Type*} {P : Finset (Finset α)} {r : ℕ}
    (hP : ∀ e ∈ P, e.card = r) (σ : Equiv.Perm α) :
    ∀ e ∈ permuteFamily σ P, e.card = r := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
  simpa using hP a ha

/-- Relabeling preserves the property of being a matching. -/
theorem permuteFamily_pairwiseDisjoint {α : Type*} [DecidableEq α]
    {P : Finset (Finset α)} (hP : (P : Set (Finset α)).PairwiseDisjoint id)
    (σ : Equiv.Perm α) :
    (permuteFamily σ P : Set (Finset α)).PairwiseDisjoint id := by
  intro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
  exact (Finset.disjoint_map σ.toEmbedding).mpr
    (hP ha' hb' (fun h ↦ hab (congrArg σ.finsetCongr h)))

/-- Finite permutation averaging for uniform set families.

If every relabeling of an `r`-uniform test family `P` contains at most `b`
edges of `H`, then `|P| * |H| ≤ b * C(|α|, r)`. This is a double count of
incidences between edges and permutations; no probability or division is needed. -/
theorem uniform_permutation_average {α : Type*} [Fintype α] [DecidableEq α]
    {P H : Finset (Finset α)} {r b : ℕ}
    (hP : ∀ e ∈ P, e.card = r) (hH : ∀ e ∈ H, e.card = r)
    (hbound : ∀ σ : Equiv.Perm α, ((permuteFamily σ P) ∩ H).card ≤ b) :
    P.card * H.card ≤ b * (Fintype.card α).choose r := by
  classical
  by_cases hempty : P = ∅
  · simp [hempty]
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let U := (Finset.univ : Finset α).powersetCard r
  let T := (Finset.univ : Finset (Equiv.Perm α))
  let R : Finset α → Equiv.Perm α → Prop := fun e σ ↦ e ∈ permuteFamily σ P
  let d := (T.bipartiteAbove R a).card
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    exact ⟨Equiv.refl α, by simp [T, R, Finset.bipartiteAbove, ha]⟩
  have hdegree : ∀ e : Finset α, e.card = r → (T.bipartiteAbove R e).card = d := by
    intro e he
    exact card_permutations_mem_family_eq P (he.trans (hP a ha).symm)
  have hfull : ∀ σ : Equiv.Perm α, (U.bipartiteBelow R σ).card = P.card := by
    intro σ
    have heq : U.bipartiteBelow R σ = permuteFamily σ P := by
      ext e
      simp only [Finset.mem_bipartiteBelow]
      exact and_iff_right_of_imp (fun he ↦ Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, permuteFamily_uniform hP σ e he⟩)
    rw [heq, card_permuteFamily]
  have hcount : U.card * d = T.card * P.card :=
    Finset.card_mul_eq_card_mul R
      (fun e he ↦ hdegree e (Finset.mem_powersetCard.mp he).2) (fun σ _ ↦ hfull σ)
  have hrestricted : H.card * d ≤ T.card * b := by
    apply Finset.card_mul_le_card_mul R (fun e he ↦ (hdegree e (hH e he)).ge)
    intro σ _
    have heq : H.bipartiteBelow R σ = (permuteFamily σ P) ∩ H := by
      ext e
      simp [Finset.bipartiteBelow, R, and_comm]
    rw [heq]
    exact hbound σ
  have hmul : (P.card * H.card) * d ≤ (b * U.card) * d := by
    calc
      (P.card * H.card) * d = P.card * (H.card * d) := by ring
      _ ≤ P.card * (T.card * b) := Nat.mul_le_mul_left _ hrestricted
      _ = b * (T.card * P.card) := by ring
      _ = b * (U.card * d) := by rw [hcount]
      _ = (b * U.card) * d := by ring
  simpa [U] using Nat.le_of_mul_le_mul_right hmul hd

/-- A finite type of size `r*k` can be partitioned into `k` disjoint `r`-sets
when `r > 0`. The blocks are the images of `{i} × Fin r` under a bijection. -/
theorem exists_uniform_partition {α : Type*} [Fintype α] [DecidableEq α]
    {r k : ℕ} (hr : 0 < r) (hcard : Fintype.card α = r * k) :
    ∃ P : Finset (Finset α), P.card = k ∧ (∀ e ∈ P, e.card = r) ∧
      (P : Set (Finset α)).PairwiseDisjoint id ∧ P.biUnion id = Finset.univ := by
  classical
  let e : Fin k × Fin r ≃ α := Fintype.equivOfCardEq (by simp [hcard, Nat.mul_comm])
  let B : Fin k → Finset α := fun i ↦ (Finset.univ : Finset (Fin r)).map
    ⟨fun j ↦ e (i, j), fun x y h ↦ congrArg Prod.snd (e.injective h)⟩
  have hBcard : ∀ i, (B i).card = r := by
    intro i
    simp [B]
  have hBdisj : ∀ {i j : Fin k}, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, _, hab⟩ := Finset.mem_map.mp hy
    exact hij (congrArg Prod.fst (e.injective hab)).symm
  have hBinj : Function.Injective B := by
    intro i j hij
    by_contra hne
    have hdisj := hBdisj hne
    rw [hij, Finset.disjoint_self_iff_empty] at hdisj
    have hc := hBcard j
    rw [hdisj, Finset.card_empty] at hc
    omega
  refine ⟨Finset.univ.image B, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hBinj]
    simp
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hBcard i
  · intro a ha b hb hab
    change a ∈ Finset.univ.image B at ha
    change b ∈ Finset.univ.image B at hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact hBdisj (fun hij ↦ hab (congrArg B hij))
  · apply Finset.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective x
    exact Finset.mem_biUnion.mpr
      ⟨B i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
        Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

/-- Every matching inside a family with no `k`-matching has fewer than `k` edges. -/
theorem matching_card_lt_of_matching_free {α : Type*} [DecidableEq α]
    {H M : Finset (Finset α)} {k : ℕ}
    (hfree : ¬ ∃ N : Finset (Finset α),
      N ⊆ H ∧ N.card = k ∧ (N : Set (Finset α)).PairwiseDisjoint id)
    (hM : M ⊆ H) (hdisj : (M : Set (Finset α)).PairwiseDisjoint id) :
    M.card < k := by
  by_contra h
  obtain ⟨N, hNM, hcard⟩ := Finset.exists_subset_card_eq (s := M) (Nat.le_of_not_gt h)
  exact hfree ⟨N, hNM.trans hM, hcard, hdisj.subset hNM⟩

/-- Test a matching-free family against every relabeling of any fixed uniform
matching. This is the matching version of `uniform_permutation_average`. -/
theorem matching_free_card_mul_le_of_matching {α : Type*} [Fintype α] [DecidableEq α]
    {P H : Finset (Finset α)} {r k : ℕ}
    (hP : ∀ e ∈ P, e.card = r) (hdisj : (P : Set (Finset α)).PairwiseDisjoint id)
    (hH : ∀ e ∈ H, e.card = r)
    (hfree : ¬ ∃ M : Finset (Finset α),
      M ⊆ H ∧ M.card = k ∧ (M : Set (Finset α)).PairwiseDisjoint id) :
    P.card * H.card ≤ (k - 1) * (Fintype.card α).choose r := by
  apply uniform_permutation_average hP hH
  intro σ
  have hlt := matching_card_lt_of_matching_free hfree
    (Finset.inter_subset_right (s₁ := permuteFamily σ P) (s₂ := H))
    ((permuteFamily_pairwiseDisjoint hdisj σ).subset Finset.inter_subset_left)
  omega

/-- The random-partition inequality at `|α| = r*k`:
`k * |H| ≤ (k-1) * C(r*k,r)`. -/
theorem matching_free_mul_card_at_multiple {α : Type*} [Fintype α] [DecidableEq α]
    {H : Finset (Finset α)} {r k : ℕ} (hr : 0 < r)
    (hcard : Fintype.card α = r * k) (hH : ∀ e ∈ H, e.card = r)
    (hfree : ¬ ∃ M : Finset (Finset α),
      M ⊆ H ∧ M.card = k ∧ (M : Set (Finset α)).PairwiseDisjoint id) :
    k * H.card ≤ (k - 1) * (r * k).choose r := by
  obtain ⟨P, hPcard, hP, hdisj, _⟩ := exists_uniform_partition hr hcard
  simpa [hPcard, hcard] using matching_free_card_mul_le_of_matching hP hdisj hH hfree

/-- The binomial identity converting the partition inequality into the sharp
boundary bound. -/
theorem choose_multiple_boundary_identity {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    k * (r * k - 1).choose r = (k - 1) * (r * k).choose r := by
  have hmul : (r * k).choose r = k * (r * k - 1).choose (r - 1) := by
    simpa only [Nat.mul_comm k r] using
      (Nat.choose_mul_right (m := k) (n := r) (Nat.ne_of_gt hr))
  have hpred : (r * k - 1).choose r = (k - 1) * (r * k - 1).choose (r - 1) := by
    calc
      (r * k - 1).choose r = (r * k).choose r - (r * k - 1).choose (r - 1) := by
        rw [Nat.choose_eq_choose_pred_add (Nat.mul_pos hr hk) hr,
          Nat.add_sub_cancel_left]
      _ = (k - 1) * (r * k - 1).choose (r - 1) := by
        rw [hmul, Nat.sub_mul, Nat.one_mul]
  rw [hpred, hmul]
  ring

/-- Sharp upper bound for a matching-free uniform family on `r*k` vertices. -/
theorem matching_free_card_le_at_multiple {α : Type*} [Fintype α] [DecidableEq α]
    {H : Finset (Finset α)} {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (hcard : Fintype.card α = r * k) (hH : ∀ e ∈ H, e.card = r)
    (hfree : ¬ ∃ M : Finset (Finset α),
      M ⊆ H ∧ M.card = k ∧ (M : Set (Finset α)).PairwiseDisjoint id) :
    H.card ≤ (r * k - 1).choose r := by
  have hbound := matching_free_mul_card_at_multiple hr hcard hH hfree
  rw [← choose_multiple_boundary_identity hr hk] at hbound
  exact Nat.le_of_mul_le_mul_left hbound hk

/-- The exact value at `n = r*k`. Only `r > 0` and `k > 0` are needed. -/
theorem f_at_multiple (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    f (r * k) r k = (r * k - 1).choose r := by
  classical
  apply le_antisymm
  · unfold f
    refine Finset.sup_le fun H hH ↦ ?_
    have hc := Finset.mem_filter.mp hH
    have hsub := Finset.mem_powerset.mp hc.1
    exact matching_free_card_le_at_multiple hr hk (by simp)
      (fun e he ↦ (Finset.mem_powersetCard.mp (hsub he)).2) hc.2
  · exact clique_lower_bound hr hk (Nat.sub_le _ _)

/-- The full displayed EMC formula at `n = r*k`. This is a boundary case,
not a proof for general `n`. -/
theorem emc_eq_at_multiple (r k : ℕ) (hr : 3 ≤ r) (hk : 0 < k) :
    f (r * k) r k = max ((r * k - 1).choose r)
      ((r * k).choose r - (r * k - k + 1).choose r) := by
  apply le_antisymm
  · rw [f_at_multiple r k (by omega) hk]
    exact le_max_left _ _
  · exact emc_lower_bound r hr (r * k) k hk (Nat.sub_le _ _)

end Erdos1020
-- Axiom audit for every declaration introduced in this module.
#print axioms Erdos1020.intersecting_of_matching_free_two
#print axioms Erdos1020.matching_free_two_card_le
#print axioms Erdos1020.f_two_le
#print axioms Erdos1020.f_two
#print axioms Erdos1020.emc_eq_two
#print axioms Erdos1020.permuteFamily
#print axioms Erdos1020.card_permuteFamily
#print axioms Erdos1020.permuteFamily_refl
#print axioms Erdos1020.permuteFamily_trans
#print axioms Erdos1020.exists_perm_map_eq_of_card_eq
#print axioms Erdos1020.card_permutations_mem_family_eq
#print axioms Erdos1020.permuteFamily_uniform
#print axioms Erdos1020.permuteFamily_pairwiseDisjoint
#print axioms Erdos1020.uniform_permutation_average
#print axioms Erdos1020.exists_uniform_partition
#print axioms Erdos1020.matching_card_lt_of_matching_free
#print axioms Erdos1020.matching_free_card_mul_le_of_matching
#print axioms Erdos1020.matching_free_mul_card_at_multiple
#print axioms Erdos1020.choose_multiple_boundary_identity
#print axioms Erdos1020.matching_free_card_le_at_multiple
#print axioms Erdos1020.f_at_multiple
#print axioms Erdos1020.emc_eq_at_multiple
