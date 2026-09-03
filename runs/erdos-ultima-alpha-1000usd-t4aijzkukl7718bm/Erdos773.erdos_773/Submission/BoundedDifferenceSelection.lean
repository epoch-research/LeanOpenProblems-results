import Submission.Hypergraph
import Submission.FractionalSquareSidon

/-!
Actual near-linear subsets with a constant bound on positive square-difference
multiplicity. The constant depends on the exponent loss. This is not a proof
of the Sidon conjecture, which requires the constant to be one.
-/
namespace Erdos773.BoundedDifferenceSelection
open Finset Filter
set_option maxHeartbeats 1000000

private def root {N : ℕ} (a : Fin N) : ℕ := a.val + 1

private lemma root_injective (N : ℕ) : Function.Injective (@root N) := by
  intro a b h
  apply Fin.ext
  dsimp [root] at h
  omega

private def reps (N D : ℕ) : Finset (Fin N × Fin N) :=
  univ.filter (fun ab => ab.1 < ab.2 ∧ root ab.2 ^ 2 = root ab.1 ^ 2 + D)

private def support {N : ℕ} (E : Finset (Fin N × Fin N)) : Finset (Fin N) :=
  E.image Prod.fst ∪ E.image Prod.snd

private lemma mem_reps {N D : ℕ} {ab : Fin N × Fin N} :
    ab ∈ reps N D ↔ ab.1 < ab.2 ∧ root ab.2 ^ 2 = root ab.1 ^ 2 + D := by
  simp [reps]

private lemma reps_card_le (N D : ℕ) :
    (reps N D).card ≤ (squareDifferenceReps N D).card := by
  apply card_le_card_of_injOn (fun ab => (root ab.1, root ab.2))
  · intro ab hab
    obtain ⟨hlt, he⟩ := mem_reps.mp hab
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ?_, mem_Icc.mpr ?_⟩, ?_⟩
    · dsimp [root]; omega
    · dsimp [root]; omega
    · exact ⟨by simpa [root] using hlt, he⟩
  · intro ab hab cd hcd he
    apply Prod.ext
    · exact root_injective N (congrArg Prod.fst he)
    · exact root_injective N (congrArg Prod.snd he)

private lemma snd_injective {N D : ℕ} :
    Set.InjOn Prod.snd (reps N D : Set (Fin N × Fin N)) := by
  intro ab hab cd hcd he
  obtain ⟨_, hab⟩ := mem_reps.mp hab
  obtain ⟨_, hcd⟩ := mem_reps.mp hcd
  apply Prod.ext
  · apply root_injective N
    have hh : root ab.1 ^ 2 = root cd.1 ^ 2 := by rw [he] at hab; omega
    exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh
  · exact he

private lemma support_card {N D : ℕ} {E : Finset (Fin N × Fin N)}
    (hE : E ⊆ reps N D) (hne : E.Nonempty) : E.card + 1 ≤ (support E).card := by
  let T := E.image Prod.fst
  have hT : T.Nonempty := hne.image Prod.fst
  let a := T.min' hT
  have ha : a ∈ T := min'_mem T hT
  have hnot : a ∉ E.image Prod.snd := by
    intro h
    obtain ⟨ab, hab, he⟩ := mem_image.mp h
    have hle : a ≤ ab.1 := min'_le T _ (mem_image.mpr ⟨ab, hab, rfl⟩)
    have hlt := (mem_reps.mp (hE hab)).1
    rw [he] at hlt
    exact (not_lt_of_ge hle) hlt
  have hi : insert a (E.image Prod.snd) ⊆ support E := by
    intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact mem_union_left _ ha
    · exact mem_union_right _ hb
  have hc : (E.image Prod.snd).card = E.card :=
    card_image_of_injOn (fun p hp q hq he => snd_injective (hE hp) (hE hq) he)
  have hh := card_le_card hi
  rw [card_insert_of_notMem hnot, hc] at hh
  exact hh

private def badSupports (N g : ℕ) : Finset (Finset (Fin N)) :=
  (Icc 1 (N ^ 2)).biUnion (fun D => ((reps N D).powersetCard (g + 1)).image support)

private lemma badSupports_size {N g : ℕ} {e : Finset (Fin N)}
    (he : e ∈ badSupports N g) : g + 2 ≤ e.card := by
  obtain ⟨D, hD, he⟩ := mem_biUnion.mp he
  obtain ⟨E, hE, rfl⟩ := mem_image.mp he
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hE
  have hn : E.Nonempty := card_pos.mp (by omega)
  have hh := support_card hsub hn
  omega

private lemma badSupports_count (N g : ℕ) :
    (badSupports N g).card ≤ ∑ D ∈ Icc 1 (N ^ 2), (reps N D).card ^ (g + 1) := by
  calc
    _ ≤ ∑ D ∈ Icc 1 (N ^ 2), (((reps N D).powersetCard (g + 1)).image support).card :=
      card_biUnion_le
    _ ≤ _ := by
      apply sum_le_sum
      intro D hD
      exact (card_image_le).trans (by rw [card_powersetCard]; exact Nat.choose_le_pow _ _)

private lemma avoids_bounded {N g : ℕ} {B : Finset (Fin N)}
    (hB : ∀ e ∈ badSupports N g, ¬ e ⊆ B) :
    ∀ D : ℕ, 0 < D → ((reps N D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card ≤ g := by
  intro D hD
  by_cases hDN : D ≤ N ^ 2
  · by_contra! hlarge
    obtain ⟨E, hE, hcard⟩ := exists_subset_card_eq (show g + 1 ≤
      ((reps N D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card by omega)
    have hsub : E ⊆ reps N D := hE.trans (filter_subset _ _)
    apply hB (support E)
    · apply mem_biUnion.mpr
      exact ⟨D, mem_Icc.mpr ⟨hD, hDN⟩,
        mem_image.mpr ⟨E, mem_powersetCard.mpr ⟨hsub, hcard⟩, rfl⟩⟩
    · intro a ha
      rcases mem_union.mp ha with ha | ha
      · obtain ⟨ab, hab, rfl⟩ := mem_image.mp ha
        exact (mem_filter.mp (hE hab)).2.1
      · obtain ⟨ab, hab, rfl⟩ := mem_image.mp ha
        exact (mem_filter.mp (hE hab)).2.2
  · have he : reps N D = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ab hab
      have hh := (mem_reps.mp hab).2
      have hb : root ab.2 ≤ N := by dsimp [root]; omega
      have hb2 := Nat.pow_le_pow_left hb 2
      omega
    simp [he]

private lemma finite_selection (N g : ℕ) (p K : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hrep : ∀ D ∈ Icc 1 (N ^ 2), ((reps N D).card : ℝ) ≤ K) :
    ∃ B : Finset (Fin N),
      (∀ D : ℕ, 0 < D → ((reps N D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card ≤ g) ∧
      p * N - (N : ℝ) ^ 2 * K ^ (g + 1) * p ^ (g + 2) ≤ B.card := by
  have hnonempty : ∀ e ∈ badSupports N g, e.Nonempty := by
    intro e he
    have hh := badSupports_size he
    exact card_pos.mp (by omega)
  obtain ⟨B, hB, hcard⟩ := alteration_bound (badSupports N g) hnonempty p hp hp1
  have hcount : ((badSupports N g).card : ℝ) ≤ (N : ℝ) ^ 2 * K ^ (g + 1) := by
    calc
      _ ≤ ∑ D ∈ Icc 1 (N ^ 2), ((reps N D).card : ℝ) ^ (g + 1) := by
        exact_mod_cast badSupports_count N g
      _ ≤ ∑ D ∈ Icc 1 (N ^ 2), K ^ (g + 1) := by
        apply sum_le_sum
        intro D hD
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hrep D hD) _
      _ = _ := by simp
  have hcost : (∑ e ∈ badSupports N g, p ^ e.card) ≤
      (N : ℝ) ^ 2 * K ^ (g + 1) * p ^ (g + 2) := by
    calc
      _ ≤ ∑ e ∈ badSupports N g, p ^ (g + 2) := by
        apply sum_le_sum
        intro e he
        exact pow_le_pow_of_le_one hp hp1 (badSupports_size he)
      _ = ((badSupports N g).card : ℝ) * p ^ (g + 2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount (pow_nonneg hp _)
  refine ⟨B, avoids_bounded hB, ?_⟩
  simp only [Fintype.card_fin] at hcard
  linarith

private lemma image_selection {N g : ℕ} {B : Finset (Fin N)}
    (hB : ∀ D : ℕ, 0 < D →
      ((reps N D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card ≤ g) :
    ∃ A ⊆ Icc 1 N, A.card = B.card ∧
      ∀ D : ℕ, 0 < D →
        ((squareDifferenceReps N D).filter (fun ab => ab.1 ∈ A ∧ ab.2 ∈ A)).card ≤ g := by
  let A := B.image root
  have hA : A ⊆ Icc 1 N := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    apply mem_Icc.mpr
    dsimp [root]
    omega
  refine ⟨A, hA, card_image_of_injective B (root_injective N), ?_⟩
  intro D hD
  have he : (squareDifferenceReps N D).filter (fun ab => ab.1 ∈ A ∧ ab.2 ∈ A) =
      ((reps N D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).image
        (fun ab => (root ab.1, root ab.2)) := by
    ext ab
    constructor
    · intro hab
      obtain ⟨hab, ha, hb⟩ := mem_filter.mp hab
      obtain ⟨a, ha, hea⟩ := mem_image.mp ha
      obtain ⟨b, hb, heb⟩ := mem_image.mp hb
      refine mem_image.mpr ⟨(a, b), ?_, Prod.ext hea heb⟩
      apply mem_filter.mpr
      refine ⟨mem_reps.mpr ?_, ha, hb⟩
      have hh := (mem_filter.mp hab).2
      rw [← hea, ← heb] at hh
      exact ⟨by simpa [root] using hh.1, hh.2⟩
    · intro hab
      obtain ⟨cd, hcd, rfl⟩ := mem_image.mp hab
      obtain ⟨hcd, hc, hd⟩ := mem_filter.mp hcd
      obtain ⟨hlt, he⟩ := mem_reps.mp hcd
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_product.mpr ?_, ?_⟩,
        mem_image.mpr ⟨cd.1, hc, rfl⟩, mem_image.mpr ⟨cd.2, hd, rfl⟩⟩
      · exact ⟨hA (mem_image.mpr ⟨cd.1, hc, rfl⟩), hA (mem_image.mpr ⟨cd.2, hd, rfl⟩)⟩
      · exact ⟨by simpa [root] using hlt, he⟩
  rw [he]
  exact card_image_le.trans (hB D hD)

/-- For a prescribed positive exponent loss, an actual near-linear root subset
has uniformly bounded positive square-difference multiplicities. The bound is
constant in N, but is not asserted to be one. -/
theorem near_linear_bounded_differences (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℕ, ∀ᶠ N : ℕ in atTop, ∃ A ⊆ Icc 1 N,
      (N : ℝ) ^ (1 - ε) ≤ A.card ∧
      ∀ D : ℕ, 0 < D →
        ((squareDifferenceReps N D).filter (fun ab => ab.1 ∈ A ∧ ab.2 ∈ A)).card ≤ g := by
  obtain ⟨g, hg⟩ := exists_nat_gt (4 / ε)
  have hg' : (4 : ℝ) < ε * g := by
    have hh := (div_lt_iff₀ hε).mp hg
    nlinarith
  let ρ : ℝ := ε / 4 * (g + 1) - 1
  have hρ : 0 < ρ := by dsimp [ρ]; nlinarith
  have hrep := Fractional.eventually_representation_bound (ε / 8) (by positivity)
  have ht (r : ℝ) (hr : 0 < r) :
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-r)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) (ht ρ hρ)
  have hslack := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
    (ht (ε / 2) (by positivity))
  refine ⟨g, ?_⟩
  filter_upwards [hrep, hsmall, hslack, eventually_ge_atTop 1] with N hrep hsmall hslack hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  let p : ℝ := (N : ℝ) ^ (-(ε / 2))
  let K : ℝ := (N : ℝ) ^ (ε / 4)
  let S : ℝ := (N : ℝ) ^ (1 - ε / 2)
  have hp : 0 ≤ p := Real.rpow_nonneg hNpos.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hS : 0 ≤ S := Real.rpow_nonneg hNpos.le _
  have hK (D : ℕ) (hD : D ∈ Icc 1 (N ^ 2)) : ((reps N D).card : ℝ) ≤ K := by
    calc
      _ ≤ ((squareDifferenceReps N D).card : ℝ) := by exact_mod_cast reps_card_le N D
      _ ≤ K := by
        simpa only [K, show 2 * (ε / 8) = ε / 4 by ring] using
          hrep D (mem_Icc.mp hD).1
  obtain ⟨B, hB, hcard⟩ := finite_selection N g p K hp hp1 hK
  have hPN : p * N = S := by
    dsimp [p, S]
    calc
      _ = (N : ℝ) ^ (-(ε / 2)) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring
  have hcost : (N : ℝ) ^ 2 * K ^ (g + 1) * p ^ (g + 2) =
      S * (N : ℝ) ^ (-ρ) := by
    dsimp [K, p, S, ρ]
    rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_mul_natCast hNpos.le,
      ← Real.rpow_natCast (N : ℝ) 2]
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have htarget : (N : ℝ) ^ (1 - ε) = S * (N : ℝ) ^ (-(ε / 2)) := by
    dsimp [S]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have herror := mul_le_mul_of_nonneg_left hsmall hS
  have htargetle := mul_le_mul_of_nonneg_left hslack hS
  rw [hPN, hcost] at hcard
  obtain ⟨A, hA, hc, hdiff⟩ := image_selection hB
  refine ⟨A, hA, ?_, hdiff⟩
  rw [hc, htarget]
  nlinarith only [hcard, herror, htargetle]

#print axioms near_linear_bounded_differences

end Erdos773.BoundedDifferenceSelection
