import FormalConjecturesUtil

/-! An infinite cube-Sidon root set containing arbitrarily long intervals.
This auxiliary construction does not establish positive lower natural density. -/

namespace Erdos1206

private lemma cube_sum_lt_of_offset_sum_lt (L M x y z w : ℕ)
    (hM : 2 * L ^ 2 + 2 * L ^ 3 + 1 ≤ M)
    (hx : x ≤ L) (hy : y ≤ L) (hs : x + y < z + w) :
    (M + x) ^ 3 + (M + y) ^ 3 < (M + z) ^ 3 + (M + w) ^ 3 := by
  have hx2 : x ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hx 2
  have hy2 : y ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hy 2
  have hx3 : x ^ 3 ≤ L ^ 3 := Nat.pow_le_pow_left hx 3
  have hy3 : y ^ 3 ≤ L ^ 3 := Nat.pow_le_pow_left hy 3
  have hM2 : 2 * L ^ 2 + 1 ≤ M := by omega
  have hM3 : 2 * L ^ 3 < M := by omega
  have hmul := Nat.mul_le_mul_left (3 * M) hM2
  have hbound : 6 * M * L ^ 2 + 2 * L ^ 3 < 3 * M ^ 2 := by
    nlinarith
  have hquad : x ^ 2 + y ^ 2 ≤ 2 * L ^ 2 := by omega
  have hquad' := Nat.mul_le_mul_left (3 * M) hquad
  have htail : 3 * M * (x ^ 2 + y ^ 2) + (x ^ 3 + y ^ 3) < 3 * M ^ 2 := by
    nlinarith
  have hsum : x + y + 1 ≤ z + w := hs
  have hsum' := Nat.mul_le_mul_left (3 * M ^ 2) hsum
  have hother := Nat.zero_le (3 * M * (z ^ 2 + w ^ 2) + (z ^ 3 + w ^ 3))
  nlinarith only [htail, hsum', hother]

lemma cubes_sidon_on_sufficiently_far_interval (L M : ℕ)
    (hMlarge : 2 * L ^ 2 + 2 * L ^ 3 + 1 ≤ M) :
    IsSidon ((fun a : ℕ => a ^ 3) '' Set.Icc M (M + L)) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ heq
  change M ≤ a ∧ a ≤ M + L at ha
  change M ≤ b ∧ b ≤ M + L at hb
  change M ≤ c ∧ c ≤ M + L at hc
  change M ≤ d ∧ d ≤ M + L at hd
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha.1
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb.1
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hc.1
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hd.1
  have hx : x ≤ L := by omega
  have hy : y ≤ L := by omega
  have hz : z ≤ L := by omega
  have hw : w ≤ L := by omega
  have hs : x + y = z + w := by
    rcases lt_trichotomy (x + y) (z + w) with h | h | h
    · exact False.elim ((ne_of_lt (cube_sum_lt_of_offset_sum_lt L M x y z w hMlarge hx hy h)) heq)
    · exact h
    · exact False.elim ((ne_of_lt (cube_sum_lt_of_offset_sum_lt L M z w x y hMlarge hz hw h)) heq.symm)
  have hsum : M + x + (M + y) = M + z + (M + w) := by omega
  have hM : 0 < M := by omega
  have hp : (M + x) * (M + y) = (M + z) * (M + w) := by
    have hid :
        3 * (M + x + (M + y)) * ((M + x) * (M + y)) +
          ((M + x) ^ 3 + (M + y) ^ 3) = (M + x + (M + y)) ^ 3 := by ring
    have hid' :
        3 * (M + z + (M + w)) * ((M + z) * (M + w)) +
          ((M + z) ^ 3 + (M + w) ^ 3) = (M + z + (M + w)) ^ 3 := by ring
    rw [hsum, heq] at hid
    have hm : 3 * (M + z + (M + w)) * ((M + x) * (M + y)) =
        3 * (M + z + (M + w)) * ((M + z) * (M + w)) :=
      Nat.add_right_cancel (hid.trans hid'.symm)
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3 * (M + z + (M + w))) hm
  have hp' : (x : ℤ) * y = (z : ℤ) * w := by
    have hpZ : ((M : ℤ) + x) * (M + y) = (M + z) * (M + w) := by exact_mod_cast hp
    have hsZ : (x : ℤ) + y = z + w := by exact_mod_cast hs
    nlinarith
  have hz0 : ((x : ℤ) - z) * (x - w) = 0 := by
    have hsZ : (x : ℤ) + y = z + w := by exact_mod_cast hs
    nlinarith
  rcases mul_eq_zero.mp hz0 with h | h
  · have hxz : x = z := by omega
    have hyw : y = w := by omega
    subst z
    subst w
    exact Or.inl ⟨rfl, rfl⟩
  · have hxw : x = w := by omega
    have hyz : y = z := by omega
    subst w
    subst z
    exact Or.inr ⟨rfl, rfl⟩

private lemma sidon_union_separated {S T : Set ℕ} {B M U : ℕ}
    (hS : IsSidon S) (hT : IsSidon T)
    (hSB : ∀ a ∈ S, a ≤ B) (hTB : ∀ a ∈ T, M ≤ a ∧ a ≤ U)
    (hBM : 2 * B < M) (hBU : U + B < 2 * M)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → B < a - b ∨ B < b - a) :
    IsSidon (S ∪ T) := by
  have hmix (a b c d : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ T)
      (hd : d ∈ T) (heq : a + c = b + d) : a = b ∧ c = d := by
    have haB := hSB a ha
    have hbB := hSB b hb
    by_cases hcd : c = d
    · exact ⟨by omega, hcd⟩
    · rcases hsep c hc d hd hcd with h | h <;> omega
  rintro a ha c hc b hb d hd heq
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc <;> rcases hd with hd | hd
  · exact hS a ha c hc b hb d hd heq
  · have h₁ := hSB a ha
    have h₂ := hSB b hb
    have h₃ := hSB c hc
    have h₄ := hTB d hd
    omega
  · have h₁ := hSB a ha
    have h₂ := hSB b hb
    have h₃ := hTB c hc
    have h₄ := hSB d hd
    omega
  · have h₁ := hSB a ha
    have h₂ := hSB b hb
    have h₃ := hTB c hc
    have h₄ := hTB d hd
    omega
  · have h₁ := hSB a ha
    have h₂ := hTB b hb
    have h₃ := hSB c hc
    have h₄ := hSB d hd
    omega
  · have h := hmix a c b d ha hc hb hd heq
    exact Or.inl h
  · have h := hmix a d b c ha hd hb hc (by omega)
    exact Or.inr h
  · have h₁ := hSB a ha
    have h₂ := hTB b hb
    have h₃ := hTB c hc
    have h₄ := hTB d hd
    omega
  · have h₁ := hTB a ha
    have h₂ := hSB b hb
    have h₃ := hSB c hc
    have h₄ := hSB d hd
    omega
  · have h := hmix b c a d hb hc ha hd (by omega)
    exact Or.inr ⟨h.2, h.1⟩
  · have h := hmix b d a c hb hd ha hc (by omega)
    exact Or.inl ⟨h.2, h.1⟩
  · have h₁ := hTB a ha
    have h₂ := hSB b hb
    have h₃ := hTB c hc
    have h₄ := hTB d hd
    omega
  · have h₁ := hTB a ha
    have h₂ := hTB b hb
    have h₃ := hSB c hc
    have h₄ := hSB d hd
    omega
  · have h₁ := hTB a ha
    have h₂ := hTB b hb
    have h₃ := hSB c hc
    have h₄ := hTB d hd
    omega
  · have h₁ := hTB a ha
    have h₂ := hTB b hb
    have h₃ := hTB c hc
    have h₄ := hSB d hd
    omega
  · exact hT a ha c hc b hb d hd heq

lemma cube_sidon_finset_extend_interval (S : Finset ℕ)
    (hS : IsSidon ((fun a : ℕ => a ^ 3) '' (S : Set ℕ))) (L K : ℕ) :
    ∃ M : ℕ, K ≤ M ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' ((S : Set ℕ) ∪ Set.Icc M (M + L))) := by
  let B := S.sup id
  have hB (a : ℕ) (ha : a ∈ S) : a ≤ B := Finset.le_sup (f := id) ha
  let M := 2 * L ^ 2 + 2 * L ^ 3 + 1 + 8 * L + 2 * B + B ^ 3 + K
  have hMlarge : 2 * L ^ 2 + 2 * L ^ 3 + 1 ≤ M := by dsimp [M]; omega
  have hMpos : 0 < M := by omega
  have hMK : K ≤ M := by dsimp [M]; omega
  have hMB : 2 * B ≤ M := by dsimp [M]; omega
  have hML : 8 * L ≤ M := by dsimp [M]; omega
  have hMB3 : B ^ 3 ≤ M := by dsimp [M]; omega
  refine ⟨M, hMK, ?_⟩
  rw [Set.image_union]
  apply sidon_union_separated (B := B ^ 3) (M := M ^ 3) (U := (M + L) ^ 3)
    hS (cubes_sidon_on_sufficiently_far_interval L M hMlarge)
  · rintro _ ⟨a, ha, rfl⟩
    exact Nat.pow_le_pow_left (hB a ha) _
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨Nat.pow_le_pow_left ha.1 _, Nat.pow_le_pow_left ha.2 _⟩
  · have hpow := Nat.pow_le_pow_left hMB 3
    have hpos := pow_pos hMpos 3
    nlinarith
  · have hpow := Nat.pow_le_pow_left hMB 3
    have hwidth : 8 * (M + L) ≤ 9 * M := by omega
    have hpow' := Nat.pow_le_pow_left hwidth 3
    have hpos := pow_pos hMpos 3
    nlinarith
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
    rcases lt_trichotomy a b with h | h | h
    · have hg := Nat.pow_le_pow_left (show a + 1 ≤ b by omega) 3
      have hba : a ^ 3 + B ^ 3 < b ^ 3 := by nlinarith [ha.1]
      exact Or.inr (show B ^ 3 < b ^ 3 - a ^ 3 from by omega)
    · exact (hne (congrArg (fun a : ℕ => a ^ 3) h)).elim
    · have hg := Nat.pow_le_pow_left (show b + 1 ≤ a by omega) 3
      have hba : b ^ 3 + B ^ 3 < a ^ 3 := by nlinarith [hb.1]
      exact Or.inl (show B ^ 3 < a ^ 3 - b ^ 3 from by omega)


private abbrev GoodFiniteCubeRoots :=
  {S : Finset ℕ // IsSidon ((fun a : ℕ => a ^ 3) '' (S : Set ℕ))}

private def blockLowerBound (S : GoodFiniteCubeRoots) (n : ℕ) : ℕ :=
  max n ((n + 1) * (S.1.card + 1) + S.1.sup id + 1)

private noncomputable def nextBlockStart (S : GoodFiniteCubeRoots) (n : ℕ) : ℕ :=
  Classical.choose (cube_sidon_finset_extend_interval S.1 S.2 n (blockLowerBound S n))

private lemma nextBlockStart_spec (S : GoodFiniteCubeRoots) (n : ℕ) :
    blockLowerBound S n ≤ nextBlockStart S n ∧
    IsSidon ((fun a : ℕ => a ^ 3) '' ((S.1 : Set ℕ) ∪
      Set.Icc (nextBlockStart S n) (nextBlockStart S n + n))) :=
  Classical.choose_spec (cube_sidon_finset_extend_interval S.1 S.2 n (blockLowerBound S n))

private noncomputable def nextCubeBlock (S : GoodFiniteCubeRoots) (n : ℕ) :
    GoodFiniteCubeRoots :=
  ⟨S.1 ∪ Finset.Icc (nextBlockStart S n) (nextBlockStart S n + n), by
    simpa only [Finset.coe_union, Finset.coe_Icc] using (nextBlockStart_spec S n).2⟩

private noncomputable def cubeBlockChain : ℕ → GoodFiniteCubeRoots
  | 0 => ⟨∅, by simp [IsSidon]⟩
  | n + 1 => nextCubeBlock (cubeBlockChain n) n

private noncomputable def cubeBlockStart (n : ℕ) : ℕ :=
  nextBlockStart (cubeBlockChain n) n

private lemma cubeBlockStart_large (n : ℕ) :
    n ≤ cubeBlockStart n ∧
    (n + 1) * ((cubeBlockChain n).1.card + 1) < cubeBlockStart n ∧
    (cubeBlockChain n).1.sup id < cubeBlockStart n := by
  have h := (nextBlockStart_spec (cubeBlockChain n) n).1
  change blockLowerBound (cubeBlockChain n) n ≤ cubeBlockStart n at h
  dsimp only [blockLowerBound] at h
  omega

private lemma cubeBlockChain_monotone : Monotone (fun n => (cubeBlockChain n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_union_left

private lemma cubeBlock_mem_next (n : ℕ) {a : ℕ}
    (ha : a ∈ Set.Icc (cubeBlockStart n) (cubeBlockStart n + n)) :
    a ∈ (cubeBlockChain (n + 1)).1 := by
  apply Finset.mem_union.mpr
  exact Or.inr (Finset.mem_Icc.mpr ha)

private lemma cubeBlockStart_strictMono : StrictMono cubeBlockStart := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hm : cubeBlockStart n ∈ (cubeBlockChain (n + 1)).1 :=
    cubeBlock_mem_next n ⟨le_refl _, Nat.le_add_right _ _⟩
  exact (Finset.le_sup (f := id) hm).trans_lt (cubeBlockStart_large (n + 1)).2.2

/-- This set has arbitrarily long intervals but lower natural density zero. -/
noncomputable def thickCubeSidonRoots : Set ℕ :=
  ⋃ n : ℕ, Set.Icc (cubeBlockStart n) (cubeBlockStart n + n)

lemma thickCubeSidonRoots_intervals (n : ℕ) :
    ∃ M ≥ n, Set.Icc M (M + n) ⊆ thickCubeSidonRoots := by
  refine ⟨cubeBlockStart n, (cubeBlockStart_large n).1, ?_⟩
  exact Set.subset_iUnion_of_subset n (Set.Subset.refl _)

lemma thickCubeSidonRoots_infinite : thickCubeSidonRoots.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨M, hM, hsub⟩ := thickCubeSidonRoots_intervals (N + 1)
  exact ⟨M, hsub ⟨le_refl _, Nat.le_add_right _ _⟩, by omega⟩

lemma thickCubeSidonRoots_sidon :
    IsSidon ((fun a : ℕ => a ^ 3) '' thickCubeSidonRoots) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ heq
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hc
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hd
  let N := i + j + k + l + 1
  have haN : a ∈ (cubeBlockChain N).1 :=
    cubeBlockChain_monotone (by dsimp [N]; omega) (cubeBlock_mem_next i hi)
  have hbN : b ∈ (cubeBlockChain N).1 :=
    cubeBlockChain_monotone (by dsimp [N]; omega) (cubeBlock_mem_next j hj)
  have hcN : c ∈ (cubeBlockChain N).1 :=
    cubeBlockChain_monotone (by dsimp [N]; omega) (cubeBlock_mem_next k hk)
  have hdN : d ∈ (cubeBlockChain N).1 :=
    cubeBlockChain_monotone (by dsimp [N]; omega) (cubeBlock_mem_next l hl)
  exact (cubeBlockChain N).2 _ ⟨a, haN, rfl⟩ _ ⟨c, hcN, rfl⟩
    _ ⟨b, hbN, rfl⟩ _ ⟨d, hdN, rfl⟩ heq

private lemma thickCubeSidonRoots_count (n : ℕ) :
    (thickCubeSidonRoots ∩ Set.Iio (cubeBlockStart n)).ncard ≤
      (cubeBlockChain n).1.card := by
  have hsub : thickCubeSidonRoots ∩ Set.Iio (cubeBlockStart n) ⊆
      ((cubeBlockChain n).1 : Set ℕ) := by
    rintro a ⟨ha, hlt⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ha
    have hjn : j < n := by
      by_contra! h
      have hM := cubeBlockStart_strictMono.monotone h
      exact (not_lt_of_ge (hM.trans hj.1)) hlt
    exact cubeBlockChain_monotone (by omega : j + 1 ≤ n) (cubeBlock_mem_next j hj)
  simpa only [Set.ncard_coe_finset] using
    Set.ncard_le_ncard hsub (cubeBlockChain n).1.finite_toSet

lemma thickCubeSidonRoots_lowerDensity : thickCubeSidonRoots.lowerDensity = 0 := by
  apply le_antisymm _ (Set.lowerDensity_nonneg _)
  by_contra! hpos
  obtain ⟨c, hc, hcD⟩ := exists_between hpos
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      c < thickCubeSidonRoots.partialDensity Set.univ N :=
    Filter.eventually_lt_of_lt_liminf hcD
      (Filter.isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / c)
  let n := max B m + 1
  have hnB : B ≤ n := by dsimp [n]; omega
  have hmn : m < n := by dsimp [n]; omega
  have hnc : 1 < c * ((n : ℝ) + 1) := by
    have hmc : 1 < (m : ℝ) * c := (div_lt_iff₀ hc).mp hm
    have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
    nlinarith
  have hn := cubeBlockStart_large n
  have hMpos : 0 < cubeBlockStart n := by omega
  have hd := hB (cubeBlockStart n) (hnB.trans hn.1)
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio] at hd
  have hd' := (lt_div_iff₀ (show (0 : ℝ) < cubeBlockStart n by exact_mod_cast hMpos)).mp hd
  have hcount : ((thickCubeSidonRoots ∩ Set.Iio (cubeBlockStart n)).ncard : ℝ) ≤
      (cubeBlockChain n).1.card := by exact_mod_cast thickCubeSidonRoots_count n
  have hlarge : ((n : ℝ) + 1) * ((cubeBlockChain n).1.card + 1) < cubeBlockStart n := by
    exact_mod_cast hn.2.1
  have hmul := mul_lt_mul_of_pos_left hlarge hc
  have hmul' := mul_le_mul_of_nonneg_right hnc.le
    (show (0 : ℝ) ≤ (cubeBlockChain n).1.card + 1 by positivity)
  nlinarith

/-- Even the existence of arbitrarily long intervals is compatible with Sidon
cubes. The constructed set has zero lower density, so it is not a witness for
`erdos_1206.parts.ii`. -/
lemma infinite_thick_cube_sidon_with_zero_lowerDensity :
    ∃ A : Set ℕ, A.Infinite ∧ IsSidon ((fun a : ℕ => a ^ 3) '' A) ∧
      A.lowerDensity = 0 ∧ ∀ L : ℕ, ∃ M ≥ L, Set.Icc M (M + L) ⊆ A :=
  ⟨thickCubeSidonRoots, thickCubeSidonRoots_infinite, thickCubeSidonRoots_sidon,
    thickCubeSidonRoots_lowerDensity, thickCubeSidonRoots_intervals⟩

end Erdos1206
