import FormalConjecturesUtil

/-!
# Repeated patterns in a dense finite interval

A purely combinatorial block-counting and pigeonhole argument. The block width,
the pattern-count bound, and the density loss depend only on the pattern size.
-/

namespace SquarefreePatternExtraction

open scoped BigOperators

/-- Positions occupied by `S` in block `j`, with positions numbered from `1` to `B`. -/
def blockOffsets (S : Finset ℕ) (B j : ℕ) : Finset ℕ :=
  (S.filter (fun v => (v - 1) / B = j)).image (fun v => (v - 1) % B + 1)

lemma blockOffsets_subset (S : Finset ℕ) {B : ℕ} (hB : 0 < B) (j : ℕ) :
    blockOffsets S B j ⊆ Finset.Icc 1 B := by
  intro i hi
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hi
  have hm := Nat.mod_lt (v - 1) hB
  simp only [Finset.mem_Icc]
  omega

lemma blockOffsets_card (S : Finset ℕ) (B j : ℕ)
    (hS : ∀ v ∈ S, 1 ≤ v) :
    (blockOffsets S B j).card = (S.filter (fun v => (v - 1) / B = j)).card := by
  unfold blockOffsets
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  change (a - 1) % B + 1 = (b - 1) % B + 1 at hab
  obtain ⟨haS, haQ⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbS, hbQ⟩ := Finset.mem_filter.mp hb
  have ha1 := hS a haS
  have hb1 := hS b hbS
  have hda := Nat.div_add_mod (a - 1) B
  have hdb := Nat.div_add_mod (b - 1) B
  rw [haQ] at hda
  rw [hbQ] at hdb
  omega

lemma blockOffsets_mem (S : Finset ℕ) (B j : ℕ)
    (hS : ∀ v ∈ S, 1 ≤ v) {i : ℕ} (hi : i ∈ blockOffsets S B j) :
    j * B + i ∈ S := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨hvS, hvQ⟩ := Finset.mem_filter.mp hv
  have hv1 := hS v hvS
  have hd := Nat.div_add_mod (v - 1) B
  rw [hvQ, Nat.mul_comm B j] at hd
  have heq : j * B + ((v - 1) % B + 1) = v := by omega
  rw [heq]
  exact hvS

lemma card_eq_sum_blockOffsets (S : Finset ℕ) (B H : ℕ)
    (hS : S ⊆ Finset.Icc 1 H) :
    S.card = ∑ j ∈ Finset.range (H / B + 1), (blockOffsets S B j).card := by
  have hpos : ∀ v ∈ S, 1 ≤ v := fun v hv => (Finset.mem_Icc.mp (hS hv)).1
  calc
    S.card = ∑ j ∈ Finset.range (H / B + 1),
        (S.filter (fun v => (v - 1) / B = j)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro v hv
      apply Finset.mem_range.mpr
      change (v - 1) / B < H / B + 1
      have hvH := (Finset.mem_Icc.mp (hS hv)).2
      have hdiv : (v - 1) / B ≤ H / B :=
        Nat.div_le_div_right (by omega)
      omega
    _ = ∑ j ∈ Finset.range (H / B + 1), (blockOffsets S B j).card := by
      apply Finset.sum_congr rfl
      intro j _
      exact (blockOffsets_card S B j hpos).symm

/-- A division-free multiplicative form of the finite pigeonhole principle. -/
lemma exists_large_fiber {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β)
    (ht : t.Nonempty) (hf : ∀ x ∈ s, f x ∈ t) :
    ∃ y ∈ t, s.card ≤ t.card * (s.filter (fun x => f x = y)).card := by
  classical
  obtain ⟨y, hy, hmax⟩ :=
    t.exists_max_image (fun y => (s.filter (fun x => f x = y)).card) ht
  refine ⟨y, hy, ?_⟩
  calc
    s.card = ∑ z ∈ t, (s.filter (fun x => f x = z)).card :=
      Finset.card_eq_sum_card_fiberwise hf
    _ ≤ ∑ _ ∈ t, (s.filter (fun x => f x = y)).card :=
      Finset.sum_le_sum hmax
    _ = t.card * (s.filter (fun x => f x = y)).card := by simp

/-- The density and rounding estimates used to count rich blocks. -/
lemma rich_block_bound (k H n r : ℕ)
    (hH : 48 * k ≤ H) (hdensity : H ≤ 12 * n)
    (hcount : n ≤ (H / (24 * k) + 1) * k + r * (24 * k)) :
    H ≤ 48 * (24 * k) * r := by
  have hdiv := Nat.div_mul_le_self H (24 * k)
  nlinarith only [hH, hdensity, hcount, hdiv]

/-- A dense subset of `[1,H]` has a fixed `k`-element pattern occurring in many
blocks of width `24*k`. No arithmetic or prime hypotheses are used. -/
theorem exists_repeated_pattern (k H : ℕ) (S : Finset ℕ)
    (hk : 0 < k) (hH : 48 * k ≤ H)
    (hS : S ⊆ Finset.Icc 1 H) (hdensity : H ≤ 12 * S.card) :
    ∃ I : Finset ℕ, I ⊆ Finset.Icc 1 (24 * k) ∧ I.card = k ∧
      H ≤ 48 * (24 * k) * 2 ^ (24 * k) *
        ((Finset.range (H / (24 * k) + 1)).filter
          (fun j => ∀ i ∈ I, j * (24 * k) + i ∈ S)).card := by
  classical
  let B := 24 * k
  let J := Finset.range (H / B + 1)
  let A := blockOffsets S B
  let R := J.filter (fun j => k ≤ (A j).card)
  have hB : 0 < B := by dsimp [B]; omega
  have hpos : ∀ v ∈ S, 1 ≤ v := fun v hv => (Finset.mem_Icc.mp (hS hv)).1
  have hA : ∀ j, A j ⊆ Finset.Icc 1 B := fun j => blockOffsets_subset S hB j
  have hAsize : ∀ j, (A j).card ≤ B := by
    intro j
    simpa using Finset.card_le_card (hA j)
  have hsum : S.card = ∑ j ∈ J, (A j).card :=
    card_eq_sum_blockOffsets S B H hS
  have hcount : S.card ≤ J.card * k + R.card * B := by
    rw [hsum]
    calc
      (∑ j ∈ J, (A j).card) ≤
          ∑ j ∈ J, (k + if k ≤ (A j).card then B else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : k ≤ (A j).card
        · simp only [if_pos hj]
          exact (hAsize j).trans (Nat.le_add_left B k)
        · simp only [if_neg hj, Nat.add_zero]
          omega
      _ = J.card * k + R.card * B := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [R]
  have hR : H ≤ 48 * B * R.card := by
    have hJ : J.card = H / B + 1 := by simp [J]
    rw [hJ] at hcount
    exact rich_block_bound k H S.card R.card hH hdensity hcount
  have hchoose : ∀ j ∈ R, ∃ I : Finset ℕ, I ⊆ A j ∧ I.card = k := by
    intro j hj
    exact Finset.exists_subset_card_eq (Finset.mem_filter.mp hj).2
  choose! P hPsub hPcard using hchoose
  let T := (Finset.Icc 1 B).powersetCard k
  have hT : T.Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    dsimp [B]
    omega
  have hPmap : ∀ j ∈ R, P j ∈ T := by
    intro j hj
    exact Finset.mem_powersetCard.mpr ⟨(hPsub j hj).trans (hA j), hPcard j hj⟩
  have hTcard : T.card ≤ 2 ^ B := by
    calc
      T.card ≤ (Finset.Icc 1 B).powerset.card := by
        apply Finset.card_le_card
        intro I hI
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hI).1
      _ = 2 ^ B := by simp
  obtain ⟨I, hIT, hfiber⟩ := exists_large_fiber R T P hT hPmap
  obtain ⟨hI, hIcard⟩ := Finset.mem_powersetCard.mp hIT
  let F := R.filter (fun j => P j = I)
  let M := J.filter (fun j => ∀ i ∈ I, j * B + i ∈ S)
  have hFM : F ⊆ M := by
    intro j hj
    obtain ⟨hjR, hjP⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hjR).1, ?_⟩
    intro i hi
    apply blockOffsets_mem S B j hpos
    apply hPsub j hjR
    simpa only [hjP] using hi
  have hRcard : R.card ≤ 2 ^ B * M.card := by
    calc
      R.card ≤ T.card * F.card := hfiber
      _ ≤ 2 ^ B * M.card := Nat.mul_le_mul hTcard (Finset.card_le_card hFM)
  have hfinal : H ≤ 48 * B * 2 ^ B * M.card := by
    calc
      H ≤ 48 * B * R.card := hR
      _ ≤ 48 * B * (2 ^ B * M.card) := Nat.mul_le_mul_left (48 * B) hRcard
      _ = 48 * B * 2 ^ B * M.card := by ring
  refine ⟨I, hI, hIcard, ?_⟩
  simpa only [M, J, B] using hfinal

end SquarefreePatternExtraction

#check SquarefreePatternExtraction.exists_repeated_pattern
#print axioms SquarefreePatternExtraction.exists_repeated_pattern
