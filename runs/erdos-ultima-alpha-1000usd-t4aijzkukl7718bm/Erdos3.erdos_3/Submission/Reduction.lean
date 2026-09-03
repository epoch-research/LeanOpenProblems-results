import FormalConjecturesUtil

/-! Verified reductions for the conjecture; these do not prove it. -/

namespace Erdos3Reduction

theorem nonsummable_infinite (A : Set ℕ)
    (h : ¬ Summable fun a : A ↦ 1 / (a : ℝ)) : A.Infinite := by
  intro hfin
  letI := hfin.fintype
  exact h (hasSum_fintype _).summable

theorem nonsummable_contains_pair (A : Set ℕ)
    (h : ¬ Summable fun a : A ↦ 1 / (a : ℝ)) :
    ∃ S ⊆ A, S.IsAPOfLength 2 := by
  have hinf := nonsummable_infinite A h
  obtain ⟨a, ha⟩ := hinf.nonempty
  obtain ⟨b, hb, hab⟩ := hinf.exists_gt a
  refine ⟨{a, b}, ?_, Nat.isAPOfLength_pair hab⟩
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl
  · exact ha
  · exact hb

theorem conjecture_iff_bounded_ap_summable :
    (∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    (∀ A : Set ℕ,
      (∃ N : ℕ, ∀ k ≥ N, ¬ ∃ S ⊆ A, S.IsAPOfLength k) →
      Summable fun a : A ↦ 1 / (a : ℝ)) := by
  classical
  simp only [Filter.frequently_atTop]
  constructor
  · intro h A ⟨N, hN⟩
    by_contra hs
    obtain ⟨k, hk, S, hSA, hAP⟩ := h A hs N
    exact hN k hk ⟨S, hSA, hAP⟩
  · intro h A hs N
    by_contra hN
    apply hs
    apply h A
    exact ⟨N, fun k hk hAP ↦ hN ⟨k, hk, hAP⟩⟩

theorem nat_ap_image (a d k : ℕ) (hd : 0 < d) :
    ((fun i : ℕ ↦ a + i * d) '' Set.Iio k).IsAPOfLengthWith k a d := by
  have hinj : Function.Injective (fun i : ℕ ↦ a + i * d) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  constructor
  · change ((fun i : ℕ ↦ a + i * d) '' Set.Iio k).encard = (k : ℕ∞)
    rw [hinj.encard_image]
    exact Set.Nat.encard_range k
  · ext x
    simp [Set.mem_image]

theorem ap_difference_pos {S : Set ℕ} {m a d : ℕ}
    (hm : 2 ≤ m) (hS : S.IsAPOfLengthWith m a d) : 0 < d := by
  by_contra hd
  have hd0 : d = 0 := by omega
  have hsub : S ⊆ {a} := by
    rw [hS.eq]
    rintro x ⟨i, hi, rfl⟩
    simp [hd0]
  have hle : ENat.card S ≤ 1 := by
    change S.encard ≤ 1
    exact (Set.encard_le_encard hsub).trans (by simp)
  rw [hS.card] at hle
  have : m ≤ 1 := by exact_mod_cast hle
  omega

theorem ap_truncate {S : Set ℕ} {m k : ℕ}
    (hS : S.IsAPOfLength m) (hkm : k ≤ m) :
    ∃ T ⊆ S, T.IsAPOfLength k := by
  by_cases heq : k = m
  · exact ⟨S, Set.Subset.rfl, heq ▸ hS⟩
  by_cases hk : k = 0
  · subst k
    exact ⟨∅, Set.empty_subset _, by simp⟩
  have hm : 2 ≤ m := by omega
  obtain ⟨a, d, hS⟩ := hS
  have hd := ap_difference_pos hm hS
  refine ⟨(fun i : ℕ ↦ a + i * d) '' Set.Iio k, ?_, a, d,
    nat_ap_image a d k hd⟩
  rintro x ⟨i, hi, rfl⟩
  rw [hS.eq]
  refine ⟨i, ?_, ?_⟩
  · exact_mod_cast lt_of_lt_of_le hi hkm
  · simp

theorem frequently_ap_iff_all_lengths (A : Set ℕ) :
    (∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    (∀ k : ℕ, ∃ S ⊆ A, S.IsAPOfLength k) := by
  rw [Filter.frequently_atTop]
  constructor
  · intro h k
    obtain ⟨m, hm, S, hSA, hS⟩ := h k
    obtain ⟨T, hTS, hT⟩ := ap_truncate hS hm
    exact ⟨T, hTS.trans hSA, hT⟩
  · intro h k
    exact ⟨k, le_rfl, h k⟩

theorem conjecture_iff_fixed_length_ap_free_summable :
    (∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    (∀ k : ℕ, 3 ≤ k → ∀ A : Set ℕ,
      A.IsAPOfLengthFree k → Summable fun a : A ↦ 1 / (a : ℝ)) := by
  classical
  constructor
  · intro h k hk A hfree
    by_contra hs
    obtain ⟨S, hSA, hS⟩ := (frequently_ap_iff_all_lengths A).mp (h A hs) k
    have hle : (k : ℕ∞) ≤ 1 := hfree S hSA hS
    have : k ≤ 1 := by exact_mod_cast hle
    omega
  · intro h A hs
    apply Filter.frequently_atTop.mpr
    intro N
    let k := max N 3
    have hk : 3 ≤ k := le_max_right _ _
    refine ⟨k, le_max_left _ _, ?_⟩
    by_contra hno
    apply hs
    apply h k hk A
    intro S hSA hS
    exact (hno ⟨S, hSA, hS⟩).elim

/-- A sufficient finite extremal estimate; the estimate itself is not assumed to be known. -/
theorem conjecture_of_uniform_finite_harmonic_bound
    (hbound : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ,
      ∀ S : Finset ℕ, (S : Set ℕ).IsAPOfLengthFree k →
        ∑ n ∈ S, 1 / (n : ℝ) ≤ C) :
    ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  apply conjecture_iff_fixed_length_ap_free_summable.mpr
  intro k hk A hA
  obtain ⟨C, hC⟩ := hbound k hk
  apply summable_of_sum_le (c := C) (fun a ↦ by positivity)
  intro F
  let e : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : (F.map e : Set ℕ) ⊆ A := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
    exact a.property
  have hfree : (F.map e : Set ℕ).IsAPOfLengthFree k := by
    intro S hSF hS
    exact hA S (hSF.trans hsub) hS
  simpa [e] using hC (F.map e) hfree

/-- An explicit nondegenerate progression, used for the gluing argument. -/
def HasNatAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

theorem hasNatAP_iff {A : Set ℕ} {k : ℕ} (hk : 2 ≤ k) :
    HasNatAP A k ↔ ∃ S ⊆ A, S.IsAPOfLength k := by
  constructor
  · rintro ⟨a, d, hd, hmem⟩
    refine ⟨(fun i : ℕ ↦ a + i * d) '' Set.Iio k, ?_, a, d,
      nat_ap_image a d k hd⟩
    rintro x ⟨i, hi, rfl⟩
    exact hmem i hi
  · rintro ⟨S, hSA, a, d, hS⟩
    refine ⟨a, d, ap_difference_pos hk hS, ?_⟩
    intro i hi
    apply hSA
    rw [hS.eq]
    exact ⟨i, by exact_mod_cast hi, by simp⟩

theorem free_iff_not_hasNatAP {A : Set ℕ} {k : ℕ} (hk : 2 ≤ k) :
    A.IsAPOfLengthFree k ↔ ¬ HasNatAP A k := by
  rw [hasNatAP_iff hk]
  constructor
  · intro h ⟨S, hSA, hS⟩
    have hle : (k : ℕ∞) ≤ 1 := h S hSA hS
    have : k ≤ 1 := by exact_mod_cast hle
    omega
  · intro h S hSA hS
    exact (h ⟨S, hSA, hS⟩).elim

theorem hasNatAP_of_affine_image {A : Set ℕ} {k q r : ℕ}
    (hk : 2 ≤ k) (hq : 0 < q)
    (h : HasNatAP ((fun n : ℕ ↦ q * n + r) '' A) k) : HasNatAP A k := by
  obtain ⟨a, d, hd, hmem⟩ := h
  obtain ⟨u, hu, hueq⟩ := hmem 0 (by omega)
  obtain ⟨v, hv, hveq⟩ := hmem 1 (by omega)
  simp only [zero_mul, add_zero] at hueq
  simp only [one_mul] at hveq
  have huv : u ≤ v := by nlinarith
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le huv
  have hdc : d = q * c := by nlinarith
  have hc : 0 < c := by nlinarith
  refine ⟨u, c, hc, ?_⟩
  intro i hi
  obtain ⟨w, hw, hweq⟩ := hmem i hi
  have heq : q * w + r = q * (u + i * c) + r := by
    calc
      q * w + r = a + i * d := hweq
      _ = q * (u + i * c) + r := by rw [← hueq, hdc]; ring
  have hw' : w = u + i * c := by nlinarith
  rwa [hw'] at hw

theorem free_affine_image {A : Set ℕ} {k q r : ℕ}
    (hk : 2 ≤ k) (hq : 0 < q) (hA : A.IsAPOfLengthFree k) :
    ((fun n : ℕ ↦ q * n + r) '' A).IsAPOfLengthFree k := by
  rw [free_iff_not_hasNatAP hk] at hA ⊢
  exact fun h ↦ hA (hasNatAP_of_affine_image hk hq h)

/-- An AP cannot cross a large gap into a suitably chosen residue class. -/
theorem hasNatAP_union_separated {F G : Set ℕ} {k L q r : ℕ}
    (hk : 3 ≤ k) (hF : ∀ x ∈ F, x ≤ L)
    (hG : ∀ x ∈ G, 2 * L < x)
    (hmod : ∀ x ∈ G, Nat.ModEq q x r)
    (hLr : L < r) (hrq : 2 * r < q)
    (h : HasNatAP (F ∪ G) k) : HasNatAP F k ∨ HasNatAP G k := by
  obtain ⟨a, d, hd, hmem⟩ := h
  have hzero := hmem 0 (by omega)
  simp only [zero_mul, add_zero, Set.mem_union] at hzero
  rcases hzero with ha | ha
  · have hapos := hF a ha
    have hone := hmem 1 (by omega)
    simp only [one_mul, Set.mem_union] at hone
    rcases hone with hb | hb
    · have hdL : d ≤ L := by have := hF _ hb; omega
      left
      refine ⟨a, d, hd, ?_⟩
      intro i
      induction i with
      | zero => simpa using (fun _ : 0 < k ↦ ha)
      | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have hprevL := hF _ hprev
        have hnext := hmem (i + 1) hi
        rcases hnext with hnext | hnext
        · exact hnext
        · have hnextG := hG _ hnext
          simp only [Nat.add_mul, one_mul] at hnextG
          omega
    · have hc := hmem 2 (by omega)
      have hbG := hG _ hb
      have hcG : a + 2 * d ∈ G := by
        rcases hc with hc | hc
        · have := hF _ hc
          omega
        · exact hc
      have hm1 := hmod _ hb
      have hm2 := hmod _ hcG
      have hma : Nat.ModEq q (r + a) (r + r) := by
        apply (hm2.add_right a).symm.trans
        convert hm1.add hm1 using 1; omega
      have heq : r + a = r + r := hma.eq_of_lt_of_lt (by omega) (by omega)
      omega
  · right
    refine ⟨a, d, hd, ?_⟩
    intro i hi
    have haG := hG _ ha
    rcases hmem i hi with hx | hx
    · have hxF := hF _ hx
      omega
    · exact hx

theorem free_union_separated {F G : Set ℕ} {k L q r : ℕ}
    (hk : 3 ≤ k) (hF : ∀ x ∈ F, x ≤ L)
    (hG : ∀ x ∈ G, 2 * L < x)
    (hmod : ∀ x ∈ G, Nat.ModEq q x r)
    (hLr : L < r) (hrq : 2 * r < q)
    (hfreeF : F.IsAPOfLengthFree k) (hfreeG : G.IsAPOfLengthFree k) :
    (F ∪ G).IsAPOfLengthFree k := by
  have hk2 : 2 ≤ k := by omega
  rw [free_iff_not_hasNatAP hk2] at hfreeF hfreeG ⊢
  intro h
  exact (hasNatAP_union_separated hk hF hG hmod hLr hrq h).elim hfreeF hfreeG

noncomputable def recipWeight (S : Finset ℕ) : ℝ := ∑ n ∈ S, 1 / (n : ℝ)

def affineEmbedding (q r : ℕ) (hq : 0 < q) : ℕ ↪ ℕ :=
  ⟨fun n ↦ q * n + r, by intro a b hab; dsimp at hab; nlinarith⟩

theorem recipWeight_mono {S T : Finset ℕ} (h : S ⊆ T) :
    recipWeight S ≤ recipWeight T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ ↦ by positivity)

theorem recipWeight_erase_zero (S : Finset ℕ) :
    recipWeight (S.erase 0) = recipWeight S := by
  apply Finset.sum_subset (Finset.erase_subset _ _)
  intro n hn hnot
  have : n = 0 := by simpa [hn] using hnot
  simp [this]

theorem recipWeight_affine_lower {S : Finset ℕ} {q r : ℕ}
    (hq : 0 < q) (hS : 0 ∉ S) :
    (1 / ((q + r : ℕ) : ℝ)) * recipWeight S ≤
      recipWeight (S.map (affineEmbedding q r hq)) := by
  simp only [recipWeight, Finset.sum_map, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := by
    have : n ≠ 0 := fun hn0 ↦ hS (hn0 ▸ hn)
    omega
  have hpos : 0 < q * n + r := by nlinarith
  have hle : q * n + r ≤ (q + r) * n := by nlinarith
  change 1 / ((q + r : ℕ) : ℝ) * (1 / (n : ℝ)) ≤ 1 / ((q * n + r : ℕ) : ℝ)
  rw [one_div_mul_one_div]
  apply one_div_le_one_div_of_le (by exact_mod_cast hpos)
  exact_mod_cast hle

theorem finite_extension_of_unbounded {k : ℕ} (hk : 3 ≤ k)
    (hunbounded : ∀ C : ℝ, ∃ S : Finset ℕ,
      (S : Set ℕ).IsAPOfLengthFree k ∧ C < recipWeight S)
    (F : Finset ℕ) (hF : (F : Set ℕ).IsAPOfLengthFree k) (M : ℝ) :
    ∃ T : Finset ℕ, F ⊆ T ∧ (T : Set ℕ).IsAPOfLengthFree k ∧ M < recipWeight T := by
  classical
  let L := F.sup id
  let r := L + 1
  let q := 4 * r
  have hq : 0 < q := by dsimp [q, r]; omega
  have hqr : (0 : ℝ) < ((q + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q + r)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨S, hS, hSw⟩ := hunbounded (((q + r : ℕ) : ℝ) * M)
  let S' := S.erase 0
  have hS' : (S' : Set ℕ).IsAPOfLengthFree k := by
    intro T hTS hT
    exact hS T (hTS.trans (by exact Finset.erase_subset _ _)) hT
  let G := S'.map (affineEmbedding q r hq)
  have hGfree : (G : Set ℕ).IsAPOfLengthFree k := by
    simpa [G, Finset.coe_map, affineEmbedding] using
      (free_affine_image (r := r) hk2 hq hS')
  have hweight : 1 / ((q + r : ℕ) : ℝ) * recipWeight S ≤ recipWeight G := by
    simpa [G, S', recipWeight_erase_zero] using
      (recipWeight_affine_lower (S := S') (r := r) hq (by simp [S']))
  have hMG : M < recipWeight G := by
    calc
      M = (1 / ((q + r : ℕ) : ℝ)) * (((q + r : ℕ) : ℝ) * M) := by
        field_simp
      _ < (1 / ((q + r : ℕ) : ℝ)) * recipWeight S :=
        mul_lt_mul_of_pos_left hSw (by positivity)
      _ ≤ recipWeight G := hweight
  have hFb : ∀ x ∈ (F : Set ℕ), x ≤ L := by
    intro x hx
    exact Finset.le_sup (f := id) hx
  have hGb : ∀ x ∈ (G : Set ℕ), 2 * L < x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hx
    have hn1 : 1 ≤ n := by have := (Finset.mem_erase.mp hn).1; omega
    change 2 * L < q * n + r
    dsimp [q, r]
    nlinarith
  have hGmod : ∀ x ∈ (G : Set ℕ), Nat.ModEq q x r := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hx
    change (q * n + r) % q = r % q
    simp
  refine ⟨F ∪ G, Finset.subset_union_left, ?_,
    hMG.trans_le (recipWeight_mono Finset.subset_union_right)⟩
  have hunion := free_union_separated hk hFb hGb hGmod
    (by dsimp [r]; omega) (by dsimp [q, r]; omega) hF hGfree
  simpa using hunion

/-- Unbounded finite reciprocal weights give a genuine infinite counterexample at a fixed length. -/
theorem infinite_counterexample_of_unbounded {k : ℕ} (hk : 3 ≤ k)
    (hunbounded : ∀ C : ℝ, ∃ S : Finset ℕ,
      (S : Set ℕ).IsAPOfLengthFree k ∧ C < recipWeight S) :
    ∃ A : Set ℕ, A.IsAPOfLengthFree k ∧
      ¬ Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  classical
  have hk2 : 2 ≤ k := by omega
  have hempty : (∅ : Set ℕ).IsAPOfLengthFree k := by
    rw [free_iff_not_hasNatAP hk2]
    rintro ⟨a, d, hd, hmem⟩
    simpa using hmem 0 (by omega)
  let B := {F : Finset ℕ // (F : Set ℕ).IsAPOfLengthFree k}
  have hext : ∀ F : B, ∀ n : ℕ, ∃ T : B,
      F.val ⊆ T.val ∧ (n : ℝ) < recipWeight T.val := by
    intro F n
    obtain ⟨T, hFT, hT, hw⟩ := finite_extension_of_unbounded hk hunbounded F.val F.property n
    exact ⟨⟨T, hT⟩, hFT, hw⟩
  choose next hnext using hext
  let chain : ℕ → B := Nat.rec ⟨∅, by simpa using hempty⟩ (fun n F ↦ next F (n + 1))
  have hstep (n : ℕ) : (chain n).val ⊆ (chain (n + 1)).val ∧
      ((n + 1 : ℕ) : ℝ) < recipWeight (chain (n + 1)).val :=
    hnext (chain n) (n + 1)
  have hmono : Monotone (fun n ↦ (chain n).val) :=
    monotone_nat_of_le_succ (fun n ↦ (hstep n).1)
  let A : Set ℕ := ⋃ n : ℕ, ((chain n).val : Set ℕ)
  have hA : A.IsAPOfLengthFree k := by
    rw [free_iff_not_hasNatAP hk2]
    rintro ⟨a, d, hd, hmem⟩
    have hstages : ∀ i : Fin k, ∃ n : ℕ, a + i.val * d ∈ (chain n).val := by
      intro i
      exact Set.mem_iUnion.mp (hmem i.val i.isLt)
    choose stage hstage using hstages
    let N := Finset.univ.sup stage
    have hNmem : ∀ i < k, a + i * d ∈ (chain N).val := by
      intro i hi
      have hle : stage ⟨i, hi⟩ ≤ N := Finset.le_sup (Finset.mem_univ _)
      exact hmono hle (hstage ⟨i, hi⟩)
    exact (free_iff_not_hasNatAP hk2).mp (chain N).property ⟨a, d, hd, hNmem⟩
  refine ⟨A, hA, ?_⟩
  intro hs
  have hsI : Summable (A.indicator (fun n : ℕ ↦ 1 / (n : ℝ))) :=
    summable_subtype_iff_indicator.mp hs
  obtain ⟨m, hm⟩ := exists_nat_gt (∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n)
  have hbound : recipWeight (chain (m + 1)).val ≤
      ∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n := by
    calc
      recipWeight (chain (m + 1)).val =
          ∑ x ∈ (chain (m + 1)).val, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxA : x ∈ A := Set.mem_iUnion.mpr ⟨m + 1, hx⟩
        exact (Set.indicator_of_mem hxA (fun n : ℕ ↦ 1 / (n : ℝ))).symm
      _ ≤ ∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n :=
        Summable.sum_le_tsum _ (fun n _ ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) n) hsI
  have hlarge := (hstep m).2
  norm_num only [Nat.cast_add, Nat.cast_one] at hlarge
  linarith

/-- The original conjecture is equivalent to a uniform finite harmonic-weight bound. -/
theorem conjecture_iff_uniform_finite_harmonic_bound :
    (∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    (∀ k : ℕ, 3 ≤ k → ∃ C : ℝ,
      ∀ S : Finset ℕ, (S : Set ℕ).IsAPOfLengthFree k → recipWeight S ≤ C) := by
  classical
  constructor
  · intro h k hk
    by_contra hno
    push_neg at hno
    obtain ⟨A, hA, hs⟩ := infinite_counterexample_of_unbounded hk hno
    exact hs (conjecture_iff_fixed_length_ap_free_summable.mp h k hk A hA)
  · intro h
    apply conjecture_of_uniform_finite_harmonic_bound
    simpa [recipWeight] using h

theorem card_le_maxCard {k N : ℕ} {S : Finset ℕ}
    (hSN : S ⊆ Finset.Icc 1 N) (hS : (S : Set ℕ).IsAPOfLengthFree k) :
    S.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  unfold Set.IsAPOfLengthFree.maxCard
  refine le_csSup ?_ ⟨S, hSN, hS, rfl⟩
  refine ⟨N, ?_⟩
  rintro n ⟨T, hT, hfree, rfl⟩
  exact (Finset.card_le_card hT).trans_eq (Nat.card_Icc _ _)

/-- Dyadic counts give an upper bound for every finite reciprocal sum. -/
theorem recipWeight_le_extremal_series {k b : ℕ} (hb : 1 < b)
    (hg : Summable (fun j : ℕ ↦
      (Set.IsAPOfLengthFree.maxCard k (b ^ (j + 1)) : ℝ) / ((b ^ j : ℕ) : ℝ)))
    (S : Finset ℕ) (hS : (S : Set ℕ).IsAPOfLengthFree k) :
    recipWeight S ≤ ∑' j : ℕ,
      (Set.IsAPOfLengthFree.maxCard k (b ^ (j + 1)) : ℝ) / ((b ^ j : ℕ) : ℝ) := by
  classical
  let S' := S.erase 0
  let J := S'.image (Nat.log b)
  have hfiber (j : ℕ) :
      (∑ n ∈ S'.filter (fun n ↦ Nat.log b n = j), 1 / (n : ℝ)) ≤
      (Set.IsAPOfLengthFree.maxCard k (b ^ (j + 1)) : ℝ) / ((b ^ j : ℕ) : ℝ) := by
    let T := S'.filter (fun n ↦ Nat.log b n = j)
    have hTsub : T ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hTfree : (T : Set ℕ).IsAPOfLengthFree k := by
      intro U hUT hU
      exact hS U (hUT.trans (by exact hTsub)) hU
    have hTinterval : T ⊆ Finset.Icc 1 (b ^ (j + 1)) := by
      intro n hn
      obtain ⟨hnS, hnj⟩ := Finset.mem_filter.mp hn
      have hn0 := (Finset.mem_erase.mp hnS).1
      apply Finset.mem_Icc.mpr
      constructor
      · omega
      · simpa [hnj] using (Nat.lt_pow_succ_log_self hb n).le
    have hTcard := card_le_maxCard hTinterval hTfree
    calc
      (∑ n ∈ T, 1 / (n : ℝ)) ≤ ∑ n ∈ T, 1 / ((b ^ j : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnS, hnj⟩ := Finset.mem_filter.mp hn
        have hn0 := (Finset.mem_erase.mp hnS).1
        have hpow : b ^ j ≤ n := by simpa [hnj] using Nat.pow_log_le_self b hn0
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast hpow
      _ = (T.card : ℝ) / ((b ^ j : ℕ) : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ (Set.IsAPOfLengthFree.maxCard k (b ^ (j + 1)) : ℝ) /
          ((b ^ j : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hTcard
  calc
    recipWeight S = recipWeight S' := (recipWeight_erase_zero S).symm
    _ = ∑ j ∈ J, ∑ n ∈ S'.filter (fun n ↦ Nat.log b n = j), 1 / (n : ℝ) := by
      exact (Finset.sum_fiberwise_of_maps_to
        (fun n hn ↦ Finset.mem_image_of_mem (Nat.log b) hn) (fun n : ℕ ↦ 1 / (n : ℝ))).symm
    _ ≤ ∑ j ∈ J,
        (Set.IsAPOfLengthFree.maxCard k (b ^ (j + 1)) : ℝ) / ((b ^ j : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun j _ ↦ hfiber j)
    _ ≤ ∑' j : ℕ,
        (Set.IsAPOfLengthFree.maxCard k (b ^ (j + 1)) : ℝ) / ((b ^ j : ℕ) : ℝ) :=
      Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) hg

/-- A precise quantitative sufficient condition, rather than merely density tending to zero. -/
theorem conjecture_of_extremal_series
    (hseries : ∀ k : ℕ, 3 ≤ k → Summable (fun j : ℕ ↦
      (Set.IsAPOfLengthFree.maxCard k (2 ^ (j + 1)) : ℝ) / ((2 ^ j : ℕ) : ℝ))) :
    ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  apply conjecture_iff_uniform_finite_harmonic_bound.mpr
  intro k hk
  refine ⟨∑' j : ℕ,
    (Set.IsAPOfLengthFree.maxCard k (2 ^ (j + 1)) : ℝ) / ((2 ^ j : ℕ) : ℝ), ?_⟩
  intro S hS
  exact recipWeight_le_extremal_series (by norm_num : 1 < 2) (hseries k hk) S hS

theorem maxCard_spec {k N : ℕ} (hk : 2 ≤ k) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
      (S : Set ℕ).IsAPOfLengthFree k ∧ S.card = Set.IsAPOfLengthFree.maxCard k N := by
  classical
  let E : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hbound : E ⊆ Set.Iic N := by
    rintro n ⟨S, hS, hfree, rfl⟩
    exact (Finset.card_le_card hS).trans_eq (Nat.card_Icc _ _)
  have hfinite : E.Finite := (Set.finite_Iic N).subset hbound
  have hempty : (∅ : Set ℕ).IsAPOfLengthFree k := by
    rw [free_iff_not_hasNatAP hk]
    rintro ⟨a, d, hd, hmem⟩
    simpa using hmem 0 (by omega)
  have hnonempty : E.Nonempty :=
    ⟨0, ∅, Finset.empty_subset _, by simpa using hempty, rfl⟩
  obtain ⟨S, hSN, hfree, hcard⟩ := hnonempty.csSup_mem hfinite
  exact ⟨S, hSN, hfree, hcard⟩

theorem hasNatAP_union_gap {F G : Set ℕ} {k L B U : ℕ}
    (hk : 3 ≤ k) (hF : ∀ x ∈ F, x ≤ L)
    (hG : ∀ x ∈ G, B ≤ x ∧ x ≤ U)
    (hgap : 2 * L < B) (hshort : L + U < 2 * B)
    (h : HasNatAP (F ∪ G) k) : HasNatAP F k ∨ HasNatAP G k := by
  obtain ⟨a, d, hd, hmem⟩ := h
  have hzero := hmem 0 (by omega)
  simp only [zero_mul, add_zero, Set.mem_union] at hzero
  rcases hzero with ha | ha
  · have hapos := hF a ha
    have hone := hmem 1 (by omega)
    simp only [one_mul, Set.mem_union] at hone
    rcases hone with hb | hb
    · have hdL : d ≤ L := by have := hF _ hb; omega
      left
      refine ⟨a, d, hd, ?_⟩
      intro i
      induction i with
      | zero => simpa using (fun _ : 0 < k ↦ ha)
      | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have hprevL := hF _ hprev
        rcases hmem (i + 1) hi with hnext | hnext
        · exact hnext
        · have hnextG := (hG _ hnext).1
          simp only [Nat.add_mul, one_mul] at hnextG
          omega
    · have hc := hmem 2 (by omega)
      have hbG := hG _ hb
      rcases hc with hc | hc
      · have := hF _ hc
        omega
      · have := (hG _ hc).2
        omega
  · right
    refine ⟨a, d, hd, ?_⟩
    intro i hi
    have haG := (hG _ ha).1
    rcases hmem i hi with hx | hx
    · have hxF := hF _ hx
      omega
    · exact hx

theorem free_union_gap {F G : Set ℕ} {k L B U : ℕ}
    (hk : 3 ≤ k) (hF : ∀ x ∈ F, x ≤ L)
    (hG : ∀ x ∈ G, B ≤ x ∧ x ≤ U)
    (hgap : 2 * L < B) (hshort : L + U < 2 * B)
    (hfreeF : F.IsAPOfLengthFree k) (hfreeG : G.IsAPOfLengthFree k) :
    (F ∪ G).IsAPOfLengthFree k := by
  have hk2 : 2 ≤ k := by omega
  rw [free_iff_not_hasNatAP hk2] at hfreeF hfreeG ⊢
  intro h
  exact (hasNatAP_union_gap hk hF hG hgap hshort h).elim hfreeF hfreeG

/-- Uniform harmonic bounds force summability of the extremal densities on geometric scales. -/
theorem extremal_series_of_uniform_bound {k : ℕ} (hk : 3 ≤ k) {C : ℝ}
    (hbound : ∀ S : Finset ℕ, (S : Set ℕ).IsAPOfLengthFree k → recipWeight S ≤ C) :
    Summable (fun j : ℕ ↦ (Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) /
      ((4 ^ j : ℕ) : ℝ)) := by
  classical
  have hk2 : 2 ≤ k := by omega
  choose S hSsub hSfree hScard using
    (fun j : ℕ ↦ maxCard_spec (N := 4 ^ j) hk2)
  let G (j : ℕ) := (S j).map (affineEmbedding 1 (2 * 4 ^ j) (by decide))
  have hGfree (j : ℕ) : (G j : Set ℕ).IsAPOfLengthFree k := by
    simpa [G, Finset.coe_map, affineEmbedding] using
      (free_affine_image (q := 1) (r := 2 * 4 ^ j) hk2 (by decide) (hSfree j))
  have hGb (j : ℕ) : ∀ x ∈ (G j : Set ℕ), 2 * 4 ^ j + 1 ≤ x ∧ x ≤ 3 * 4 ^ j := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hx
    have hnI := Finset.mem_Icc.mp (hSsub j hn)
    change 2 * 4 ^ j + 1 ≤ 1 * n + 2 * 4 ^ j ∧ 1 * n + 2 * 4 ^ j ≤ 3 * 4 ^ j
    omega
  have hGw (j : ℕ) :
      (Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) / ((3 * 4 ^ j : ℕ) : ℝ) ≤
      recipWeight (G j) := by
    simp only [G, recipWeight, Finset.sum_map]
    calc
      (Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) / ((3 * 4 ^ j : ℕ) : ℝ) =
          ∑ n ∈ S j, 1 / ((3 * 4 ^ j : ℕ) : ℝ) := by
        simp [hScard, div_eq_mul_inv]
      _ ≤ ∑ n ∈ S j, 1 / ((affineEmbedding 1 (2 * 4 ^ j) (by decide) n : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnI := Finset.mem_Icc.mp (hSsub j hn)
        have hpos : 0 < 1 * n + 2 * 4 ^ j := by omega
        have hle : 1 * n + 2 * 4 ^ j ≤ 3 * 4 ^ j := by omega
        change 1 / ((3 * 4 ^ j : ℕ) : ℝ) ≤ 1 / ((1 * n + 2 * 4 ^ j : ℕ) : ℝ)
        exact one_div_le_one_div_of_le (by exact_mod_cast hpos) (by exact_mod_cast hle)
  let T : ℕ → Finset ℕ := Nat.rec ∅ (fun n F ↦ F ∪ G n)
  have hT : ∀ n : ℕ,
      ({x : ℕ | x ∈ T n}).IsAPOfLengthFree k ∧
      (∀ x ∈ T n, x ≤ 4 ^ n) ∧
      (∑ j ∈ Finset.range n,
        (Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) / ((3 * 4 ^ j : ℕ) : ℝ)) ≤
        recipWeight (T n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [free_iff_not_hasNatAP hk2]
        rintro ⟨a, d, hd, hmem⟩
        simpa [T] using hmem 0 (by omega)
      · simp [T]
      · simp [T, recipWeight]
    | succ n ih =>
      have hdisj : Disjoint (T n) (G n) := by
        apply Finset.disjoint_left.mpr
        intro x hxT hxG
        have := ih.2.1 x hxT
        have := (hGb n x hxG).1
        omega
      have hfree := free_union_gap hk ih.2.1 (hGb n)
        (by omega : 2 * 4 ^ n < 2 * 4 ^ n + 1)
        (by omega : 4 ^ n + 3 * 4 ^ n < 2 * (2 * 4 ^ n + 1)) ih.1 (hGfree n)
      refine ⟨by simpa [T] using hfree, ?_, ?_⟩
      · intro x hx
        change x ∈ T n ∪ G n at hx
        simp only [Finset.mem_union] at hx
        rw [pow_succ]
        rcases hx with hx | hx
        · have := ih.2.1 x hx
          omega
        · have := (hGb n x hx).2
          omega
      · rw [Finset.sum_range_succ]
        change _ ≤ recipWeight (T n ∪ G n)
        change _ ≤ ∑ x ∈ T n ∪ G n, 1 / (x : ℝ)
        rw [Finset.sum_union hdisj]
        exact add_le_add ih.2.2 (hGw n)
  have hs : Summable (fun j : ℕ ↦
      (Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) / ((3 * 4 ^ j : ℕ) : ℝ)) := by
    apply summable_of_sum_range_le (c := C) (fun _ ↦ by positivity)
    intro n
    exact (hT n).2.2.trans (hbound (T n) (hT n).1)
  convert hs.mul_left (3 : ℝ) using 1
  funext j
  push_cast
  field_simp

/-- An exact analytic formulation of the original conjecture. -/
theorem conjecture_iff_extremal_series :
    (∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    (∀ k : ℕ, 3 ≤ k → Summable (fun j : ℕ ↦
      (Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ))) := by
  constructor
  · intro h k hk
    obtain ⟨C, hC⟩ := conjecture_iff_uniform_finite_harmonic_bound.mp h k hk
    exact extremal_series_of_uniform_bound hk hC
  · intro h
    apply conjecture_iff_uniform_finite_harmonic_bound.mpr
    intro k hk
    have hs : Summable (fun j : ℕ ↦
        (Set.IsAPOfLengthFree.maxCard k (4 ^ (j + 1)) : ℝ) /
          ((4 ^ (j + 1) : ℕ) : ℝ)) :=
      (h k hk).comp_injective (by intro a b hab; change a + 1 = b + 1 at hab; omega)
    have hg : Summable (fun j : ℕ ↦
        (Set.IsAPOfLengthFree.maxCard k (4 ^ (j + 1)) : ℝ) / ((4 ^ j : ℕ) : ℝ)) := by
      convert hs.mul_left (4 : ℝ) using 1
      funext j
      simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      field_simp
    refine ⟨∑' j : ℕ,
      (Set.IsAPOfLengthFree.maxCard k (4 ^ (j + 1)) : ℝ) / ((4 ^ j : ℕ) : ℝ), ?_⟩
    intro S hS
    exact recipWeight_le_extremal_series (by norm_num : 1 < 4) hg S hS

/-- The extremal cardinality is subadditive, by splitting an interval into two pieces. -/
theorem maxCard_add_le {k : ℕ} (hk : 2 ≤ k) (m n : ℕ) :
    Set.IsAPOfLengthFree.maxCard k (m + n) ≤
      Set.IsAPOfLengthFree.maxCard k m + Set.IsAPOfLengthFree.maxCard k n := by
  classical
  obtain ⟨S, hS, hfree, hcard⟩ := maxCard_spec (N := m + n) hk
  let T := S.filter (fun x ↦ x ≤ m)
  let V := S.filter (fun x ↦ ¬ x ≤ m)
  let U := V.image (fun x ↦ x - m)
  have hT : T ⊆ Finset.Icc 1 m := by
    intro x hx
    obtain ⟨hxS, hxm⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hS hxS)).1, hxm⟩
  have hTf : (T : Set ℕ).IsAPOfLengthFree k := by
    intro W hWT hW
    exact hfree W (hWT.trans (by exact Finset.filter_subset _ _)) hW
  have hU : U ⊆ Finset.Icc 1 n := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxS, hxm⟩ := Finset.mem_filter.mp hx
    have hxb := Finset.mem_Icc.mp (hS hxS)
    apply Finset.mem_Icc.mpr
    omega
  have hUf : (U : Set ℕ).IsAPOfLengthFree k := by
    rw [free_iff_not_hasNatAP hk]
    rintro ⟨a, d, hd, hmem⟩
    apply (free_iff_not_hasNatAP hk).mp hfree
    refine ⟨m + a, d, hd, ?_⟩
    intro i hi
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp (hmem i hi)
    obtain ⟨hxS, hxm⟩ := Finset.mem_filter.mp hx
    have heq : m + a + i * d = x := by omega
    simpa only [heq] using hxS
  have hUc : U.card = V.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    change x - m = y - m at hxy
    omega
  have hsplit : T.card + V.card = S.card :=
    Finset.card_filter_add_card_filter_not _
  rw [← hcard, ← hsplit, ← hUc]
  exact Nat.add_le_add (card_le_maxCard hT hTf) (card_le_maxCard hU hUf)

/-- Tiling an interval gives a linear, not a submultiplicative, extremal bound. -/
theorem maxCard_mul_le {k : ℕ} (hk : 2 ≤ k) (m n : ℕ) :
    Set.IsAPOfLengthFree.maxCard k (m * n) ≤ m * Set.IsAPOfLengthFree.maxCard k n := by
  induction m with
  | zero =>
    obtain ⟨S, hS, _, hcard⟩ := maxCard_spec (N := 0) hk
    have : S = ∅ := Finset.subset_empty.mp (by simpa using hS)
    simp [← hcard, this]
  | succ m ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact (maxCard_add_le hk (m * n) n).trans (Nat.add_le_add_right ih _)

/-- Extremal densities at powers of four form a decreasing sequence. -/
theorem extremal_density_antitone {k : ℕ} (hk : 2 ≤ k) :
    Antitone (fun j : ℕ ↦
      (Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro j
  have hbound := maxCard_mul_le hk 4 (4 ^ j)
  rw [pow_succ']
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hc : (Set.IsAPOfLengthFree.maxCard k (4 * 4 ^ j) : ℝ) ≤
      4 * (Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) := by exact_mod_cast hbound
  nlinarith [mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ 4 ^ j by positivity)]

/-- Summable decreasing nonnegative sequences satisfy the stronger necessary condition `n f(n) → 0`. -/
theorem tendsto_nat_mul_of_summable_antitone {f : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ f n) (hmono : Antitone f) (hs : Summable f) :
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * f n) Filter.atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n ↦ ha.trans_le (mul_nonneg (by positivity) (hnonneg n)))
  · intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      ((tendsto_sum_nat_add f).eventually_lt_const (show (0 : ℝ) < ε / 2 by positivity))
    refine Filter.eventually_atTop.mpr ⟨2 * N, fun n hn ↦ ?_⟩
    have hsub : N ≤ n := by omega
    have hsum : ((n - N : ℕ) : ℝ) * f n ≤ ∑' i : ℕ, f (i + N) := by
      calc
        ((n - N : ℕ) : ℝ) * f n = ∑ i ∈ Finset.range (n - N), f n := by simp
        _ ≤ ∑ i ∈ Finset.range (n - N), f (i + N) := by
          apply Finset.sum_le_sum
          intro i hi
          apply hmono
          have := Finset.mem_range.mp hi
          omega
        _ ≤ ∑' i : ℕ, f (i + N) :=
          Summable.sum_le_tsum _ (fun i _ ↦ hnonneg (i + N)) ((summable_nat_add_iff N).mpr hs)
    have hc : (n : ℝ) ≤ 2 * ((n - N : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 2 * (n - N) by omega)
    have := mul_le_mul_of_nonneg_right hc (hnonneg n)
    have htail := hN N le_rfl
    nlinarith

/-- The conjecture would force logarithmic decay of the extremal density at geometric scales. -/
theorem conjecture_implies_logarithmic_decay
    (h : ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k)
    {k : ℕ} (hk : 3 ≤ k) :
    Filter.Tendsto (fun j : ℕ ↦ (j : ℝ) *
      ((Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := by
  exact tendsto_nat_mul_of_summable_antitone (fun _ ↦ by positivity)
    (extremal_density_antitone (by omega)) (conjecture_iff_extremal_series.mp h k hk)

/-- Finite extension can also introduce no new pairs at distance at most D. -/
theorem finite_extension_of_unbounded_with_gap {k : ℕ} (hk : 3 ≤ k)
    (hunbounded : ∀ C : ℝ, ∃ S : Finset ℕ,
      (S : Set ℕ).IsAPOfLengthFree k ∧ C < recipWeight S)
    (F : Finset ℕ) (hF : (F : Set ℕ).IsAPOfLengthFree k) (M : ℝ) (D : ℕ) :
    ∃ T : Finset ℕ, F ⊆ T ∧ (T : Set ℕ).IsAPOfLengthFree k ∧ M < recipWeight T ∧
      ∀ x ∈ T, ∀ y ∈ T, x < y → y ≤ x + D → x ∈ F ∧ y ∈ F := by
  classical
  let L := max (F.sup id) D
  have hDL : D ≤ L := le_max_right _ _
  let r := L + 1
  let q := 4 * r
  have hq : 0 < q := by dsimp [q, r]; omega
  have hqr : (0 : ℝ) < ((q + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q + r)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨S, hS, hSw⟩ := hunbounded (((q + r : ℕ) : ℝ) * M)
  let S' := S.erase 0
  have hS' : (S' : Set ℕ).IsAPOfLengthFree k := by
    intro T hTS hT
    exact hS T (hTS.trans (by exact Finset.erase_subset _ _)) hT
  let G := S'.map (affineEmbedding q r hq)
  have hGfree : (G : Set ℕ).IsAPOfLengthFree k := by
    simpa [G, Finset.coe_map, affineEmbedding] using
      (free_affine_image (r := r) hk2 hq hS')
  have hweight : 1 / ((q + r : ℕ) : ℝ) * recipWeight S ≤ recipWeight G := by
    simpa [G, S', recipWeight_erase_zero] using
      (recipWeight_affine_lower (S := S') (r := r) hq (by simp [S']))
  have hMG : M < recipWeight G := by
    calc
      M = (1 / ((q + r : ℕ) : ℝ)) * (((q + r : ℕ) : ℝ) * M) := by
        field_simp
      _ < (1 / ((q + r : ℕ) : ℝ)) * recipWeight S :=
        mul_lt_mul_of_pos_left hSw (by positivity)
      _ ≤ recipWeight G := hweight
  have hFb : ∀ x ∈ (F : Set ℕ), x ≤ L := by
    intro x hx
    exact (Finset.le_sup (f := id) hx).trans (le_max_left _ _)
  have hGb : ∀ x ∈ (G : Set ℕ), 2 * L < x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hx
    have hn1 : 1 ≤ n := by have := (Finset.mem_erase.mp hn).1; omega
    change 2 * L < q * n + r
    dsimp [q, r]
    nlinarith
  have hGmod : ∀ x ∈ (G : Set ℕ), Nat.ModEq q x r := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hx
    change (q * n + r) % q = r % q
    simp
  have hgap : ∀ x ∈ F ∪ G, ∀ y ∈ F ∪ G, x < y → y ≤ x + D → x ∈ F ∧ y ∈ F := by
    intro x hx y hy hxy hclose
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact ⟨hx, hy⟩
    · have := hFb x hx
      have := hGb y hy
      omega
    · have := hGb x hx
      have := hFb y hy
      omega
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
      change q * u + r < q * v + r at hxy
      change q * v + r ≤ q * u + r + D at hclose
      have huv : u < v := (Nat.mul_lt_mul_left hq).mp (by omega)
      have hmul := Nat.mul_le_mul_left q (show u + 1 ≤ v by omega)
      have hqD : D < q := by dsimp [q, r]; omega
      nlinarith
  refine ⟨F ∪ G, Finset.subset_union_left, ?_,
    hMG.trans_le (recipWeight_mono Finset.subset_union_right), hgap⟩
  have hunion := free_union_separated hk hFb hGb hGmod
    (by dsimp [r]; omega) (by dsimp [q, r]; omega) hF hGfree
  simpa using hunion

/-- If the finite weights are unbounded, a counterexample can additionally have
finite intersections with every fixed positive shift. -/
theorem gapped_counterexample_of_unbounded {k : ℕ} (hk : 3 ≤ k)
    (hunbounded : ∀ C : ℝ, ∃ S : Finset ℕ,
      (S : Set ℕ).IsAPOfLengthFree k ∧ C < recipWeight S) :
    ∃ A : Set ℕ, A.IsAPOfLengthFree k ∧
      (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) ∧
      ∀ d : ℕ, 0 < d → {x : ℕ | x ∈ A ∧ x + d ∈ A}.Finite := by
  classical
  have hk2 : 2 ≤ k := by omega
  have hempty : (∅ : Set ℕ).IsAPOfLengthFree k := by
    rw [free_iff_not_hasNatAP hk2]
    rintro ⟨a, d, hd, hmem⟩
    simpa using hmem 0 (by omega)
  let B := {F : Finset ℕ // (F : Set ℕ).IsAPOfLengthFree k}
  have hext : ∀ F : B, ∀ n : ℕ, ∃ T : B,
      F.val ⊆ T.val ∧ (n : ℝ) < recipWeight T.val ∧
      ∀ x ∈ T.val, ∀ y ∈ T.val, x < y → y ≤ x + n → x ∈ F.val ∧ y ∈ F.val := by
    intro F n
    obtain ⟨T, hFT, hT, hw, hgap⟩ :=
      finite_extension_of_unbounded_with_gap hk hunbounded F.val F.property n n
    exact ⟨⟨T, hT⟩, hFT, hw, hgap⟩
  choose next hnext using hext
  let chain : ℕ → B := Nat.rec ⟨∅, by simpa using hempty⟩ (fun n F ↦ next F (n + 1))
  have hstep (n : ℕ) : (chain n).val ⊆ (chain (n + 1)).val ∧
      ((n + 1 : ℕ) : ℝ) < recipWeight (chain (n + 1)).val ∧
      ∀ x ∈ (chain (n + 1)).val, ∀ y ∈ (chain (n + 1)).val,
        x < y → y ≤ x + (n + 1) → x ∈ (chain n).val ∧ y ∈ (chain n).val :=
    hnext (chain n) (n + 1)
  have hmono : Monotone (fun n ↦ (chain n).val) :=
    monotone_nat_of_le_succ (fun n ↦ (hstep n).1)
  let A : Set ℕ := ⋃ n : ℕ, ((chain n).val : Set ℕ)
  have hA : A.IsAPOfLengthFree k := by
    rw [free_iff_not_hasNatAP hk2]
    rintro ⟨a, d, hd, hmem⟩
    have hstages : ∀ i : Fin k, ∃ n : ℕ, a + i.val * d ∈ (chain n).val := by
      intro i
      exact Set.mem_iUnion.mp (hmem i.val i.isLt)
    choose stage hstage using hstages
    let N := Finset.univ.sup stage
    have hNmem : ∀ i < k, a + i * d ∈ (chain N).val := by
      intro i hi
      have hle : stage ⟨i, hi⟩ ≤ N := Finset.le_sup (Finset.mem_univ _)
      exact hmono hle (hstage ⟨i, hi⟩)
    exact (free_iff_not_hasNatAP hk2).mp (chain N).property ⟨a, d, hd, hNmem⟩
  have hstabilize (d n : ℕ) (hdn : d ≤ n) :
      ∀ x ∈ (chain n).val, ∀ y ∈ (chain n).val,
        x < y → y ≤ x + d → x ∈ (chain d).val := by
    induction n, hdn using Nat.le_induction with
    | base => intro x hx y hy hxy hclose; exact hx
    | succ n hdn ih =>
      intro x hx y hy hxy hclose
      obtain ⟨hx', hy'⟩ := (hstep n).2.2 x hx y hy hxy (by omega)
      exact ih x hx' y hy' hxy hclose
  have hfinite (d : ℕ) (hd : 0 < d) : {x : ℕ | x ∈ A ∧ x + d ∈ A}.Finite := by
    apply (chain d).val.finite_toSet.subset
    rintro x ⟨hx, hy⟩
    obtain ⟨nx, hnx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ny, hny⟩ := Set.mem_iUnion.mp hy
    let M := max (max nx ny) d
    have hdM : d ≤ M := le_max_right _ _
    have hxM : nx ≤ M := (le_max_left _ _).trans (le_max_left _ _)
    have hyM : ny ≤ M := (le_max_right _ _).trans (le_max_left _ _)
    exact hstabilize d M hdM x (hmono hxM hnx) (x + d) (hmono hyM hny) (by omega) le_rfl
  refine ⟨A, hA, ?_, hfinite⟩
  intro hs
  have hsI : Summable (A.indicator (fun n : ℕ ↦ 1 / (n : ℝ))) :=
    summable_subtype_iff_indicator.mp hs
  obtain ⟨m, hm⟩ := exists_nat_gt (∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n)
  have hbound : recipWeight (chain (m + 1)).val ≤
      ∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n := by
    calc
      recipWeight (chain (m + 1)).val =
          ∑ x ∈ (chain (m + 1)).val, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxA : x ∈ A := Set.mem_iUnion.mpr ⟨m + 1, hx⟩
        exact (Set.indicator_of_mem hxA (fun n : ℕ ↦ 1 / (n : ℝ))).symm
      _ ≤ ∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n :=
        Summable.sum_le_tsum _ (fun n _ ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) n) hsI
  have hlarge := (hstep m).2.1
  norm_num only [Nat.cast_add, Nat.cast_one] at hlarge
  linarith

/-- Restricting to sets with only finitely many pairs at each fixed positive distance
does not make the conjecture weaker: any failure can be glued into that class. -/
theorem conjecture_iff_finite_shift_case :
    (∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    (∀ A : Set ℕ,
      (∀ d : ℕ, 0 < d → {x : ℕ | x ∈ A ∧ x + d ∈ A}.Finite) →
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) := by
  classical
  constructor
  · intro h A _
    exact h A
  · intro h
    apply conjecture_iff_uniform_finite_harmonic_bound.mpr
    intro k hk
    by_contra! hno
    obtain ⟨A, hfree, hs, hfinite⟩ := gapped_counterexample_of_unbounded hk hno
    obtain ⟨S, hSA, hS⟩ := (frequently_ap_iff_all_lengths A).mp (h A hfinite hs) k
    have hsmall : k ≤ 1 := by exact_mod_cast hfree S hSA hS
    omega

#print axioms conjecture_iff_finite_shift_case

#print axioms gapped_counterexample_of_unbounded

/-- Extensions can protect all nonidentity affine equations with bounded coefficients. -/
theorem finite_extension_of_unbounded_affine_thin {k : ℕ} (hk : 3 ≤ k)
    (hunbounded : ∀ C : ℝ, ∃ S : Finset ℕ,
      (S : Set ℕ).IsAPOfLengthFree k ∧ C < recipWeight S)
    (F : Finset ℕ) (hF : (F : Set ℕ).IsAPOfLengthFree k) (M : ℝ) (D : ℕ) :
    ∃ T : Finset ℕ, F ⊆ T ∧ (T : Set ℕ).IsAPOfLengthFree k ∧ M < recipWeight T ∧
      ∀ a b c d : ℕ, 0 < a → a ≤ D → b ≤ D → 0 < c → c ≤ D → d ≤ D →
        (a ≠ c ∨ b ≠ d) → ∀ x ∈ T, ∀ y ∈ T,
          a * x + b = c * y + d → x ∈ F ∧ y ∈ F := by
  classical
  let L := max (F.sup id) D
  have hDL : D ≤ L := le_max_right _ _
  let r := L + 1
  let q := 4 * (D + 1) * r
  have hr : 0 < r := by dsimp [r]; omega
  have hDr : D < r := by dsimp [r]; omega
  have hq : 0 < q := by dsimp [q]; positivity
  have hqbase : 4 * r ≤ q := by dsimp [q]; nlinarith [Nat.zero_le (D * r)]
  have hqDL : D * L + D < q := by dsimp [q, r]; nlinarith [Nat.zero_le (D * L)]
  have hqDr : D * r + D < q := by dsimp [q]; nlinarith [Nat.zero_le (D * r)]
  have hqr : (0 : ℝ) < ((q + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q + r)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨S, hS, hSw⟩ := hunbounded (((q + r : ℕ) : ℝ) * M)
  let S' := S.erase 0
  have hS' : (S' : Set ℕ).IsAPOfLengthFree k := by
    intro T hTS hT
    exact hS T (hTS.trans (by exact Finset.erase_subset _ _)) hT
  let G := S'.map (affineEmbedding q r hq)
  have hGfree : (G : Set ℕ).IsAPOfLengthFree k := by
    simpa [G, Finset.coe_map, affineEmbedding] using
      (free_affine_image (r := r) hk2 hq hS')
  have hweight : 1 / ((q + r : ℕ) : ℝ) * recipWeight S ≤ recipWeight G := by
    simpa [G, S', recipWeight_erase_zero] using
      (recipWeight_affine_lower (S := S') (r := r) hq (by simp [S']))
  have hMG : M < recipWeight G := by
    calc
      M = (1 / ((q + r : ℕ) : ℝ)) * (((q + r : ℕ) : ℝ) * M) := by
        field_simp
      _ < (1 / ((q + r : ℕ) : ℝ)) * recipWeight S :=
        mul_lt_mul_of_pos_left hSw (by positivity)
      _ ≤ recipWeight G := hweight
  have hFb : ∀ x ∈ (F : Set ℕ), x ≤ L := by
    intro x hx
    exact (Finset.le_sup (f := id) hx).trans (le_max_left _ _)
  have hGlarge : ∀ x ∈ (G : Set ℕ), q < x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hx
    have hn1 : 1 ≤ n := by have := (Finset.mem_erase.mp hn).1; omega
    change q < q * n + r
    nlinarith [Nat.mul_le_mul_left q hn1]
  have hGb : ∀ x ∈ (G : Set ℕ), 2 * L < x := by
    intro x hx
    have := hGlarge x hx
    dsimp [r] at hqbase
    omega
  have hGmod : ∀ x ∈ (G : Set ℕ), Nat.ModEq q x r := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hx
    change (q * n + r) % q = r % q
    simp
  have hbound (a b : ℕ) (ha : a ≤ D) (hb : b ≤ D) : a * r + b < q :=
    (Nat.add_le_add (Nat.mul_le_mul_right r ha) hb).trans_lt hqDr
  have hsmall (a b x : ℕ) (ha : a ≤ D) (hb : b ≤ D) (hx : x ∈ F) :
      a * x + b < q :=
    (Nat.add_le_add (Nat.mul_le_mul ha (hFb x hx)) hb).trans_lt hqDL
  have hlarge (a b x : ℕ) (ha : 0 < a) (hx : x ∈ G) : q < a * x + b := by
    have hmul : x ≤ a * x := by
      simpa using Nat.mul_le_mul_right x (show 1 ≤ a by omega)
    have := hGlarge x hx
    omega
  have hpreserve : ∀ a b c d : ℕ,
      0 < a → a ≤ D → b ≤ D → 0 < c → c ≤ D → d ≤ D → (a ≠ c ∨ b ≠ d) →
      ∀ x ∈ F ∪ G, ∀ y ∈ F ∪ G,
        a * x + b = c * y + d → x ∈ F ∧ y ∈ F := by
    intro a b c d ha haD hbD hc hcD hdD hneq x hx y hy heq
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact ⟨hx, hy⟩
    · have := hsmall a b x haD hbD hx
      have := hlarge c d y hc hy
      omega
    · have := hlarge a b x ha hx
      have := hsmall c d y hcD hdD hy
      omega
    · have hm1 := ((hGmod x hx).mul_left a).add_right b
      have hm2 := ((hGmod y hy).mul_left c).add_right d
      rw [heq] at hm1
      have heq' : a * r + b = c * r + d :=
        (hm1.symm.trans hm2).eq_of_lt_of_lt (hbound a b haD hbD) (hbound c d hcD hdD)
      have hbd : b = d := by
        have hm := congrArg (fun z : ℕ ↦ z % r) heq'
        simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (hbD.trans_lt hDr),
          Nat.mod_eq_of_lt (hdD.trans_lt hDr)] using hm
      have hac : a = c := by
        rw [hbd] at heq'
        exact Nat.eq_of_mul_eq_mul_right hr (Nat.add_right_cancel heq')
      exact (hneq.elim (fun h ↦ h hac) (fun h ↦ h hbd)).elim
  refine ⟨F ∪ G, Finset.subset_union_left, ?_,
    hMG.trans_le (recipWeight_mono Finset.subset_union_right), hpreserve⟩
  have hunion := free_union_separated hk hFb hGb hGmod
    (by dsimp [r]; omega) (by omega) hF hGfree
  simpa using hunion

#print axioms finite_extension_of_unbounded_affine_thin

/-- Every fixed nonidentity positive-slope rational affine relation has finitely
many solutions inside A. -/
def AffineThin (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < c → (a ≠ c ∨ b ≠ d) →
    {x : ℕ | x ∈ A ∧ ∃ y ∈ A, a * x + b = c * y + d}.Finite

/-- A failure of a finite harmonic bound can be glued into an affine-thin counterexample. -/
theorem affine_thin_counterexample_of_unbounded {k : ℕ} (hk : 3 ≤ k)
    (hunbounded : ∀ C : ℝ, ∃ S : Finset ℕ,
      (S : Set ℕ).IsAPOfLengthFree k ∧ C < recipWeight S) :
    ∃ A : Set ℕ, A.IsAPOfLengthFree k ∧
      (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) ∧
      AffineThin A := by
  classical
  have hk2 : 2 ≤ k := by omega
  have hempty : (∅ : Set ℕ).IsAPOfLengthFree k := by
    rw [free_iff_not_hasNatAP hk2]
    rintro ⟨a, d, hd, hmem⟩
    simpa using hmem 0 (by omega)
  let B := {F : Finset ℕ // (F : Set ℕ).IsAPOfLengthFree k}
  have hext : ∀ F : B, ∀ n : ℕ, ∃ T : B,
      F.val ⊆ T.val ∧ (n : ℝ) < recipWeight T.val ∧
      ∀ a b c d : ℕ, 0 < a → a ≤ n → b ≤ n → 0 < c → c ≤ n → d ≤ n →
        (a ≠ c ∨ b ≠ d) → ∀ x ∈ T.val, ∀ y ∈ T.val,
          a * x + b = c * y + d → x ∈ F.val ∧ y ∈ F.val := by
    intro F n
    obtain ⟨T, hFT, hT, hw, hgap⟩ :=
      finite_extension_of_unbounded_affine_thin hk hunbounded F.val F.property n n
    exact ⟨⟨T, hT⟩, hFT, hw, hgap⟩
  choose next hnext using hext
  let chain : ℕ → B := Nat.rec ⟨∅, by simpa using hempty⟩ (fun n F ↦ next F (n + 1))
  have hstep (n : ℕ) : (chain n).val ⊆ (chain (n + 1)).val ∧
      ((n + 1 : ℕ) : ℝ) < recipWeight (chain (n + 1)).val ∧
      ∀ a b c d : ℕ, 0 < a → a ≤ n + 1 → b ≤ n + 1 → 0 < c → c ≤ n + 1 →
        d ≤ n + 1 → (a ≠ c ∨ b ≠ d) →
        ∀ x ∈ (chain (n + 1)).val, ∀ y ∈ (chain (n + 1)).val,
          a * x + b = c * y + d → x ∈ (chain n).val ∧ y ∈ (chain n).val :=
    hnext (chain n) (n + 1)
  have hmono : Monotone (fun n ↦ (chain n).val) :=
    monotone_nat_of_le_succ (fun n ↦ (hstep n).1)
  let A : Set ℕ := ⋃ n : ℕ, ((chain n).val : Set ℕ)
  have hA : A.IsAPOfLengthFree k := by
    rw [free_iff_not_hasNatAP hk2]
    rintro ⟨a, d, hd, hmem⟩
    have hstages : ∀ i : Fin k, ∃ n : ℕ, a + i.val * d ∈ (chain n).val := by
      intro i
      exact Set.mem_iUnion.mp (hmem i.val i.isLt)
    choose stage hstage using hstages
    let N := Finset.univ.sup stage
    have hNmem : ∀ i < k, a + i * d ∈ (chain N).val := by
      intro i hi
      have hle : stage ⟨i, hi⟩ ≤ N := Finset.le_sup (Finset.mem_univ _)
      exact hmono hle (hstage ⟨i, hi⟩)
    exact (free_iff_not_hasNatAP hk2).mp (chain N).property ⟨a, d, hd, hNmem⟩
  have hstabilize (a b c d D n : ℕ)
      (ha : 0 < a) (haD : a ≤ D) (hbD : b ≤ D)
      (hc : 0 < c) (hcD : c ≤ D) (hdD : d ≤ D) (hneq : a ≠ c ∨ b ≠ d) (hDn : D ≤ n) :
      ∀ x ∈ (chain n).val, ∀ y ∈ (chain n).val,
        a * x + b = c * y + d → x ∈ (chain D).val := by
    induction n, hDn using Nat.le_induction with
    | base => intro x hx y hy heq; exact hx
    | succ n hDn ih =>
      intro x hx y hy heq
      obtain ⟨hx', hy'⟩ := (hstep n).2.2 a b c d ha (by omega) (by omega)
        hc (by omega) (by omega) hneq x hx y hy heq
      exact ih x hx' y hy' heq
  have hfinite : AffineThin A := by
    intro a b c d ha hc hneq
    let D := max (max a b) (max c d)
    have haD : a ≤ D := (le_max_left _ _).trans (le_max_left _ _)
    have hbD : b ≤ D := (le_max_right _ _).trans (le_max_left _ _)
    have hcD : c ≤ D := (le_max_left _ _).trans (le_max_right _ _)
    have hdD : d ≤ D := (le_max_right _ _).trans (le_max_right _ _)
    apply (chain D).val.finite_toSet.subset
    rintro x ⟨hx, y, hy, heq⟩
    obtain ⟨nx, hnx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ny, hny⟩ := Set.mem_iUnion.mp hy
    let M := max (max nx ny) D
    have hDM : D ≤ M := le_max_right _ _
    have hxM : nx ≤ M := (le_max_left _ _).trans (le_max_left _ _)
    have hyM : ny ≤ M := (le_max_right _ _).trans (le_max_left _ _)
    exact hstabilize a b c d D M ha haD hbD hc hcD hdD hneq hDM
      x (hmono hxM hnx) y (hmono hyM hny) heq
  refine ⟨A, hA, ?_, hfinite⟩
  intro hs
  have hsI : Summable (A.indicator (fun n : ℕ ↦ 1 / (n : ℝ))) :=
    summable_subtype_iff_indicator.mp hs
  obtain ⟨m, hm⟩ := exists_nat_gt (∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n)
  have hbound : recipWeight (chain (m + 1)).val ≤
      ∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n := by
    calc
      recipWeight (chain (m + 1)).val =
          ∑ x ∈ (chain (m + 1)).val, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxA : x ∈ A := Set.mem_iUnion.mpr ⟨m + 1, hx⟩
        exact (Set.indicator_of_mem hxA (fun n : ℕ ↦ 1 / (n : ℝ))).symm
      _ ≤ ∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n :=
        Summable.sum_le_tsum _ (fun n _ ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) n) hsI
  have hlarge := (hstep m).2.1
  norm_num only [Nat.cast_add, Nat.cast_one] at hlarge
  linarith

/-- Fixed-shift intersections are a special case of affine thinness. -/
theorem AffineThin.finite_shift_intersection {A : Set ℕ} (hA : AffineThin A)
    {d : ℕ} (hd : 0 < d) : {x : ℕ | x ∈ A ∧ x + d ∈ A}.Finite := by
  apply (hA 1 d 1 0 (by omega) (by omega) (Or.inr (by omega))).subset
  rintro x ⟨hx, hy⟩
  exact ⟨hx, x + d, hy, by omega⟩

/-- The conjecture is unchanged if it is restricted to affine-thin sets. -/
theorem conjecture_iff_affine_thin_case :
    (∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔
    (∀ A : Set ℕ,
      AffineThin A →
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) := by
  classical
  constructor
  · intro h A _
    exact h A
  · intro h
    apply conjecture_iff_uniform_finite_harmonic_bound.mpr
    intro k hk
    by_contra! hno
    obtain ⟨A, hfree, hs, hfinite⟩ := affine_thin_counterexample_of_unbounded hk hno
    obtain ⟨S, hSA, hS⟩ := (frequently_ap_iff_all_lengths A).mp (h A hfinite hs) k
    have hsmall : k ≤ 1 := by exact_mod_cast hfree S hSA hS
    omega

#print axioms conjecture_iff_affine_thin_case

#print axioms affine_thin_counterexample_of_unbounded

/-- A logarithmic power saving with exponent strictly greater than one would be enough.
This lemma does not assert the existence of that saving. -/
theorem extremal_series_of_log_power_bound {k : ℕ} {C p : ℝ} (hp : 1 < p)
    (hbound : ∀ᶠ N : ℕ in Filter.atTop,
      (Set.IsAPOfLengthFree.maxCard k N : ℝ) ≤ C * N / (Real.log N) ^ p) :
    Summable (fun j : ℕ ↦
      (Set.IsAPOfLengthFree.maxCard k (2 ^ (j + 1)) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by
  have hs : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1) ^ p) := by
    apply ((Real.summable_one_div_nat_add_rpow 1 p).mpr hp).congr
    intro j
    rw [abs_of_nonneg (by positivity)]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : Filter.Tendsto (fun j : ℕ ↦ 2 ^ (j + 1)) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (Filter.tendsto_add_atTop_nat 1)
  apply (hs.mul_left (2 * C / (Real.log 2) ^ p)).of_norm_bounded_eventually_nat
  filter_upwards [ht.eventually hbound] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (C * ((2 ^ (j + 1) : ℕ) : ℝ) /
        (Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) ^ p) / ((2 ^ j : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hj (by positivity)
    _ = (2 * C / (Real.log 2) ^ p) * (1 / ((j : ℝ) + 1) ^ p) := by
      push_cast
      rw [Real.log_pow, Real.mul_rpow (by positivity) hlog.le]
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      field_simp

/-- Conditional completion from a uniform-in-N logarithmic power bound for each fixed length. -/
theorem conjecture_of_log_power_bound
    (hbound : ∀ k : ℕ, 3 ≤ k → ∃ C p : ℝ, 1 < p ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (Set.IsAPOfLengthFree.maxCard k N : ℝ) ≤ C * N / (Real.log N) ^ p) :
    ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  apply conjecture_of_extremal_series
  intro k hk
  obtain ⟨C, p, hp, h⟩ := hbound k hk
  exact extremal_series_of_log_power_bound hp h

#print axioms conjecture_of_log_power_bound

#print axioms conjecture_implies_logarithmic_decay

#print axioms conjecture_iff_extremal_series

#print axioms free_union_gap

#print axioms conjecture_of_extremal_series

#print axioms conjecture_iff_uniform_finite_harmonic_bound

#print axioms finite_extension_of_unbounded

#print axioms free_union_separated

#print axioms conjecture_of_uniform_finite_harmonic_bound

#print axioms ap_truncate
#print axioms conjecture_iff_fixed_length_ap_free_summable
#print axioms nonsummable_contains_pair
#print axioms nonsummable_infinite
#print axioms conjecture_iff_bounded_ap_summable

end Erdos3Reduction
