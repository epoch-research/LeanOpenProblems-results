import Submission.SummableDivisorCover

/-!
A canonical divisor-closed greedy set of cube-Sidon roots and its exclusion
certificates. Its positive lower density and the summability of its minimal
excluded divisors are NOT proved here.
-/

namespace Erdos1206
open scoped Classical

private def greedyCubeStep (n : ℕ) (G : ∀ m : ℕ, m < n → Prop) : Prop :=
  0 < n ∧
  (∀ d (hd : d < n), 0 < d → d ∣ n → G d hd) ∧
  ∀ a (ha : a < n) b (hb : b < n) c (hc : c < n),
    G a ha → G b hb → G c hc → n ^ 3 + a ^ 3 ≠ b ^ 3 + c ^ 3

/-- Accept a positive integer if its proper positive divisors were accepted
and adding it does not complete a collision with earlier accepted roots. -/
def greedyCubeRoots : Set ℕ := fun n => Nat.strongRec greedyCubeStep n

lemma mem_greedyCubeRoots_iff (n : ℕ) : n ∈ greedyCubeRoots ↔
    0 < n ∧
    (∀ d, d < n → 0 < d → d ∣ n → d ∈ greedyCubeRoots) ∧
    ∀ a, a < n → ∀ b, b < n → ∀ c, c < n →
      a ∈ greedyCubeRoots → b ∈ greedyCubeRoots → c ∈ greedyCubeRoots →
      n ^ 3 + a ^ 3 ≠ b ^ 3 + c ^ 3 := by
  change Nat.strongRec greedyCubeStep n ↔ _
  rw [Nat.strongRec_eq]
  rfl

lemma greedyCubeRoots_pos {n : ℕ} (hn : n ∈ greedyCubeRoots) : 0 < n :=
  (mem_greedyCubeRoots_iff n).mp hn |>.1

lemma one_mem_greedyCubeRoots : 1 ∈ greedyCubeRoots := by
  rw [mem_greedyCubeRoots_iff]
  refine ⟨by omega, ?_, ?_⟩
  · intro d hd hd0; omega
  · intro a ha b hb c hc hA
    have := greedyCubeRoots_pos hA
    omega

lemma greedyCubeRoots_divisorClosed : PositiveDivisorClosed greedyCubeRoots := by
  intro n hn d hdn hd0
  have hdn' := Nat.le_of_dvd (greedyCubeRoots_pos hn) hdn
  rcases hdn'.eq_or_lt with rfl | hlt
  · exact hn
  · exact (mem_greedyCubeRoots_iff n).mp hn |>.2.1 d hlt hd0 hdn

private lemma greedyCube_no_collision_at_max
    {n a b c : ℕ} (hn : n ∈ greedyCubeRoots)
    (ha : a ∈ greedyCubeRoots) (hb : b ∈ greedyCubeRoots) (hc : c ∈ greedyCubeRoots)
    (han : a ≤ n) (hbn : b ≤ n) (hcn : c ≤ n) (hnb : n ≠ b) (hnc : n ≠ c)
    (he : n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3) : False := by
  have hbn' : b < n := lt_of_le_of_ne hbn hnb.symm
  have hcn' : c < n := lt_of_le_of_ne hcn hnc.symm
  have han' : a < n := by
    have hb3 := Nat.pow_lt_pow_left hbn' (by decide : 3 ≠ 0)
    have hc3 := Nat.pow_lt_pow_left hcn' (by decide : 3 ≠ 0)
    by_contra h
    have : a = n := by omega
    subst a
    omega
  exact (mem_greedyCubeRoots_iff n).mp hn |>.2.2 a han' b hbn' c hcn' ha hb hc he

lemma greedyCubeRoots_cube_sidon :
    IsSidon ((fun a : ℕ => a ^ 3) '' greedyCubeRoots) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ he
  change a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 at he
  dsimp only at ⊢
  by_cases hac : a = c
  · subst c
    exact Or.inl ⟨rfl, Nat.add_left_cancel he⟩
  by_cases had : a = d
  · subst d
    exact Or.inr ⟨rfl, by omega⟩
  have hbc : b ≠ c := by
    intro h
    subst c
    have : a ^ 3 = d ^ 3 := by omega
    exact had (Nat.pow_left_injective (by decide : 3 ≠ 0) this)
  have hbd : b ≠ d := by
    intro h
    subst d
    have : a ^ 3 = c ^ 3 := by omega
    exact hac (Nat.pow_left_injective (by decide : 3 ≠ 0) this)
  exfalso
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · rcases le_total b d with hbd' | hdb
    · apply greedyCube_no_collision_at_max hd hc ha hb hcd (hab.trans hbd') hbd'
        (Ne.symm had) hbd.symm
      omega
    · apply greedyCube_no_collision_at_max hb ha hc hd hab (hcd.trans hdb) hdb hbc hbd
      omega
  · rcases le_total b c with hbc' | hcb
    · apply greedyCube_no_collision_at_max hc hd ha hb hdc (hab.trans hbc') hbc'
        (Ne.symm hac) hbc.symm
      omega
    · apply greedyCube_no_collision_at_max hb ha hc hd hab hcb (hdc.trans hcb) hbc hbd
      omega
  · rcases le_total a d with had' | hda
    · apply greedyCube_no_collision_at_max hd hc ha hb hcd had' (hba.trans had')
        (Ne.symm had) hbd.symm
      omega
    · exact greedyCube_no_collision_at_max ha hb hc hd hba (hcd.trans hda) hda hac had he
  · rcases le_total a c with hac' | hca
    · apply greedyCube_no_collision_at_max hc hd ha hb hdc hac' (hba.trans hac')
        (Ne.symm hac) hbc.symm
      omega
    · exact greedyCube_no_collision_at_max ha hb hc hd hba hca (hdc.trans hca) hac had he

/-- The minimal positive excluded integers, ordered by divisibility. -/
def greedyCubeGenerators : Set ℕ :=
  {n | 0 < n ∧ n ∉ greedyCubeRoots ∧
    ∀ d, d < n → 0 < d → d ∣ n → d ∈ greedyCubeRoots}

lemma one_not_mem_greedyCubeGenerators : 1 ∉ greedyCubeGenerators := by
  intro h
  exact h.2.1 one_mem_greedyCubeRoots

/-- Every rejected positive integer is divisible by a minimal rejected one. -/
lemma greedyCube_generator_dvd {n : ℕ} (hn : 0 < n) (hnG : n ∉ greedyCubeRoots) :
    ∃ d ∈ greedyCubeGenerators, d ∣ n := by
  classical
  let P := fun d : ℕ => 0 < d ∧ d ∣ n ∧ d ∉ greedyCubeRoots
  have hex : ∃ d, P d := ⟨n, hn, dvd_refl n, hnG⟩
  let d := Nat.find hex
  have hd : P d := Nat.find_spec hex
  refine ⟨d, ⟨hd.1, hd.2.2, ?_⟩, hd.2.1⟩
  intro m hmd hm hmdvd
  by_contra hmG
  have hmp : P m := ⟨hm, hmdvd.trans hd.2.1, hmG⟩
  have := Nat.find_min' hex hmp
  change d ≤ m at this
  omega

lemma greedyCubeRoots_eq_divisorAvoider :
    greedyCubeRoots = divisorAvoider greedyCubeGenerators := by
  ext n
  constructor
  · intro hn
    refine ⟨greedyCubeRoots_pos hn, ?_⟩
    intro d hd hdn
    exact hd.2.1 (greedyCubeRoots_divisorClosed n hn d hdn hd.1)
  · rintro ⟨hn, hnB⟩
    by_contra hnG
    obtain ⟨d, hd, hdn⟩ := greedyCube_generator_dvd hn hnG
    exact hnB d hd hdn

lemma greedyCubeGenerators_primitive {m n : ℕ}
    (hm : m ∈ greedyCubeGenerators) (hn : n ∈ greedyCubeGenerators)
    (hmn : m ∣ n) : m = n := by
  have hle := Nat.le_of_dvd hn.1 hmn
  by_contra hne
  exact hm.2.1 (hn.2.2 m (lt_of_le_of_ne hle hne) hm.1 hmn)

/-- Exclusion witnesses consist of three strictly earlier accepted roots. -/
lemma greedyCubeGenerator_witness {n : ℕ} (hn : n ∈ greedyCubeGenerators) :
    ∃ a ∈ greedyCubeRoots, ∃ b ∈ greedyCubeRoots, ∃ c ∈ greedyCubeRoots,
      a < n ∧ b < n ∧ c < n ∧ n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3 := by
  classical
  have hnot : ¬ (∀ a, a < n → ∀ b, b < n → ∀ c, c < n →
      a ∈ greedyCubeRoots → b ∈ greedyCubeRoots → c ∈ greedyCubeRoots →
      n ^ 3 + a ^ 3 ≠ b ^ 3 + c ^ 3) := by
    intro h
    exact hn.2.1 ((mem_greedyCubeRoots_iff n).mpr ⟨hn.1, hn.2.2, h⟩)
  push_neg at hnot
  obtain ⟨a, han, b, hbn, c, hcn, ha, hb, hc, he⟩ := hnot
  exact ⟨a, ha, b, hb, c, hc, han, hbn, hcn, he⟩

lemma greedyCubeGenerators_cover : IsCubeDivisorCover greedyCubeGenerators := by
  intro a b c d ha hb hc hd he hac had
  by_cases hA : a ∈ greedyCubeRoots
  · by_cases hB : b ∈ greedyCubeRoots
    · by_cases hC : c ∈ greedyCubeRoots
      · by_cases hD : d ∈ greedyCubeRoots
        · have hs := greedyCubeRoots_cube_sidon _ ⟨a, hA, rfl⟩ _ ⟨c, hC, rfl⟩
            _ ⟨b, hB, rfl⟩ _ ⟨d, hD, rfl⟩ he
          rcases hs with hs | hs
          · exact (hac (Nat.pow_left_injective (by decide : 3 ≠ 0) hs.1)).elim
          · exact (had (Nat.pow_left_injective (by decide : 3 ≠ 0) hs.1)).elim
        · obtain ⟨p, hp, hpd⟩ := greedyCube_generator_dvd hd hD
          exact ⟨p, hp, Or.inr (Or.inr (Or.inr hpd))⟩
      · obtain ⟨p, hp, hpc⟩ := greedyCube_generator_dvd hc hC
        exact ⟨p, hp, Or.inr (Or.inr (Or.inl hpc))⟩
    · obtain ⟨p, hp, hpb⟩ := greedyCube_generator_dvd hb hB
      exact ⟨p, hp, Or.inr (Or.inl hpb)⟩
  · obtain ⟨p, hp, hpa⟩ := greedyCube_generator_dvd ha hA
    exact ⟨p, hp, Or.inl hpa⟩

/-- Each greedy exclusion has a primitive collision witness: its four roots
have no common divisor other than one. -/
lemma greedyCubeGenerator_primitive_witness {n : ℕ} (hn : n ∈ greedyCubeGenerators) :
    ∃ a ∈ greedyCubeRoots, ∃ b ∈ greedyCubeRoots, ∃ c ∈ greedyCubeRoots,
      a < n ∧ b < n ∧ c < n ∧ n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3 ∧
      ∀ k : ℕ, k ∣ n → k ∣ a → k ∣ b → k ∣ c → k = 1 := by
  obtain ⟨a, ha, b, hb, c, hc, han, hbn, hcn, he⟩ := greedyCubeGenerator_witness hn
  refine ⟨a, ha, b, hb, c, hc, han, hbn, hcn, he, ?_⟩
  intro k hkn hka hkb hkc
  have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hkn hn.1
  by_contra hk1
  have hk2 : 1 < k := by omega
  obtain ⟨m, hm⟩ := hkn
  obtain ⟨x, hx⟩ := hka
  obtain ⟨y, hy⟩ := hkb
  obtain ⟨z, hz⟩ := hkc
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left (hm ▸ hn.1)
  have hx0 : 0 < x := Nat.pos_of_mul_pos_left (hx ▸ greedyCubeRoots_pos ha)
  have hy0 : 0 < y := Nat.pos_of_mul_pos_left (hy ▸ greedyCubeRoots_pos hb)
  have hz0 : 0 < z := Nat.pos_of_mul_pos_left (hz ▸ greedyCubeRoots_pos hc)
  have hmn : m < n := by rw [hm]; nlinarith
  have hmG : m ∈ greedyCubeRoots := hn.2.2 m hmn hm0 (by rw [hm]; exact dvd_mul_left _ _)
  have hxG : x ∈ greedyCubeRoots := greedyCubeRoots_divisorClosed a ha x
    (by rw [hx]; exact dvd_mul_left _ _) hx0
  have hyG : y ∈ greedyCubeRoots := greedyCubeRoots_divisorClosed b hb y
    (by rw [hy]; exact dvd_mul_left _ _) hy0
  have hzG : z ∈ greedyCubeRoots := greedyCubeRoots_divisorClosed c hc z
    (by rw [hz]; exact dvd_mul_left _ _) hz0
  have he' : m ^ 3 + x ^ 3 = y ^ 3 + z ^ 3 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hk0 3)
    simpa only [hm, hx, hy, hz, mul_pow, mul_add] using he
  have hs := greedyCubeRoots_cube_sidon _ ⟨m, hmG, rfl⟩ _ ⟨y, hyG, rfl⟩
    _ ⟨x, hxG, rfl⟩ _ ⟨z, hzG, rfl⟩ he'
  rcases hs with hs | hs
  · have hmy := Nat.pow_left_injective (by decide : 3 ≠ 0) hs.1
    have : n = b := by rw [hm, hy, hmy]
    omega
  · have hmz := Nat.pow_left_injective (by decide : 3 ≠ 0) hs.1
    have : n = c := by rw [hm, hz, hmz]
    omega

/-- The greedy construction is maximal among divisor-closed cube-Sidon sets. -/
lemma greedyCubeRoots_maximal {A : Set ℕ} (hclosed : PositiveDivisorClosed A)
    (hs : IsSidon ((fun a : ℕ => a ^ 3) '' A))
    (hG : greedyCubeRoots ⊆ A) : A ∩ Set.Ioi 0 = greedyCubeRoots := by
  apply Set.Subset.antisymm
  · rintro n ⟨hn, hn0⟩
    by_contra hnG
    obtain ⟨d, hd, hdn⟩ := greedyCube_generator_dvd hn0 hnG
    have hdA : d ∈ A := hclosed n hn d hdn hd.1
    obtain ⟨a, ha, b, hb, c, hc, _, hbd, hcd, he⟩ := greedyCubeGenerator_witness hd
    have h := hs _ ⟨d, hdA, rfl⟩ _ ⟨b, hG hb, rfl⟩
      _ ⟨a, hG ha, rfl⟩ _ ⟨c, hG hc, rfl⟩ he
    rcases h with h | h
    · have := Nat.pow_left_injective (by decide : 3 ≠ 0) h.1
      omega
    · have := Nat.pow_left_injective (by decide : 3 ≠ 0) h.1
      omega
  · intro n hn
    exact ⟨hG hn, greedyCubeRoots_pos hn⟩

lemma greedyCubeRoots_infinite : greedyCubeRoots.Infinite := by
  by_contra h
  obtain ⟨M, hM⟩ := (Set.not_infinite.mp h).bddAbove
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (2 * M + 2)
  have hpG : p ∉ greedyCubeRoots := by
    intro h
    have := hM h
    omega
  have hpB : p ∈ greedyCubeGenerators := by
    refine ⟨hp.pos, hpG, ?_⟩
    intro d hdp _ hdiv
    rcases hp.eq_one_or_self_of_dvd d hdiv with rfl | h
    · exact one_mem_greedyCubeRoots
    · omega
  obtain ⟨a, _, b, hb, c, hc, _, _, _, he⟩ := greedyCubeGenerator_witness hpB
  have hb3 := Nat.pow_le_pow_left (hM hb) 3
  have hc3 := Nat.pow_le_pow_left (hM hc) 3
  have hp3 := Nat.pow_lt_pow_left (show 2 * M < p by omega) (by decide : 3 ≠ 0)
  norm_num [mul_pow] at hp3
  omega

/-- This explicit reciprocal summability assertion would suffice. It is not
established by the greedy construction itself. -/
lemma summable_greedyCubeGenerators_suffices
    (h : Summable (fun n : ℕ => if n ∈ greedyCubeGenerators then (1 : ℝ) / n else 0)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  refine ⟨greedyCubeRoots, greedyCubeRoots_infinite, ?_, greedyCubeRoots_cube_sidon⟩
  rw [greedyCubeRoots_eq_divisorAvoider]
  exact divisorAvoider_positive_density_of_summable one_not_mem_greedyCubeGenerators h

#print axioms greedyCubeRoots_cube_sidon
#print axioms greedyCubeGenerator_primitive_witness
#print axioms greedyCubeRoots_infinite
#print axioms summable_greedyCubeGenerators_suffices

end Erdos1206
