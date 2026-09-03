import Submission.UniversalCompleteCyclicExplore

/-! A fixed complete fine partition gives an ordinary natural-number operator.
Both carry levels are included. The coarse profile is an input, not a result. -/
namespace Erdos66UniversalCompleteNatural
open Erdos66UniversalCompleteCyclic Erdos66TranslatedGraphPartition
  Erdos66OriginRepair Erdos66CyclicThickening Erdos66MixedCyclicThickening
  Erdos66OuterCarryProfile Erdos66DisjointBlockOperator Erdos66ColoredBlockTransfer
  AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 3000000
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
variable (p K : ℕ) [NeZero p] [NeZero K]

noncomputable def fineColor (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) (z : ZMod ((p*K)^2)) : α :=
  let xy := (cyclicDigitEquiv (p*K)).symm z
  ω (ρ.symm (reduceDigit p K xy.2-f (reduceDigit p K xy.1)))

section Prime
variable [Fact p.Prime]

noncomputable def cyclicColors (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) (a : α) : Finset (ZMod ((p*K)^2)) :=
  thickenedSet p K (colorClass f ρ ω a)

lemma mem_cyclicColors (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) (a : α) (z : ZMod ((p*K)^2)) :
    z∈cyclicColors p K f ρ ω a ↔ fineColor p K f ρ ω z=a := by
  simp only [cyclicColors,thickenedSet,Finset.mem_filter,Finset.mem_univ,true_and,
    mem_colorClass,graphColor,fineColor]

lemma cyclicColors_disjoint (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) :
    Pairwise (fun a b ↦ Disjoint (cyclicColors p K f ρ ω a) (cyclicColors p K f ρ ω b)) := by
  intro a b hab
  exact thickened_disjoint p K (colorClass_disjoint f ρ ω hab)

lemma cyclicColors_cover (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) : Finset.univ.biUnion (cyclicColors p K f ρ ω)=Finset.univ :=
  thickened_cover p K _ (colorClass_cover f ρ ω)

noncomputable def cyclicMean : ℝ := (K:ℝ)^2*(p:ℝ)^2/(Fintype.card α:ℝ)^2
noncomputable def carryRelative (ε : ℝ) : ℝ := ε+2*(1+ε)/(K:ℝ)

omit [DecidableEq α] [Fact p.Prime] in
lemma cyclicMean_pos : 0 < cyclicMean (α := α) p K := by
  unfold cyclicMean
  have hp : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
  have hK : (0:ℝ)<K := by exact_mod_cast NeZero.pos K
  have ha : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  positivity

omit [NeZero K] in
lemma carryRelative_nonneg (ε : ℝ) (hε : 0≤ε) : 0≤carryRelative K ε := by
  unfold carryRelative
  positivity

lemma cyclicColors_error (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) (ε : ℝ)
    (hω : ∀ a b : α, ∀ t s : ZMod p,
      |(pairCount (colorClass f ρ ω a) (colorClass f ρ ω b) (t,s):ℝ)-
        (p:ℝ)^2/(Fintype.card α:ℝ)^2|≤ε*((p:ℝ)^2/(Fintype.card α:ℝ)^2))
    (a b : α) (z : ZMod ((p*K)^2)) :
    |(cyclicCount ((p*K)^2) (cyclicColors p K f ρ ω a) (cyclicColors p K f ρ ω b) z:ℝ)-
      cyclicMean (α := α) p K|≤carryRelative K ε*cyclicMean (α := α) p K := by
  have hm (t s : ZMod p) :
      |((mixedFiber p (colorClass f ρ ω a) (colorClass f ρ ω b) t s).card:ℝ)-
        (p:ℝ)^2/(Fintype.card α:ℝ)^2|≤ε*((p:ℝ)^2/(Fintype.card α:ℝ)^2) := hω a b t s
  have he := Erdos66MixedCyclicThickening.thickenedSet_error p K
    (colorClass f ρ ω a) (colorClass f ρ ω b)
    ((p:ℝ)^2/(Fintype.card α:ℝ)^2) (ε*((p:ℝ)^2/(Fintype.card α:ℝ)^2)) hm z
  change |(cyclicCount ((p*K)^2) (cyclicColors p K f ρ ω a) (cyclicColors p K f ρ ω b) z:ℝ)-
    (K:ℝ)^2*((p:ℝ)^2/(Fintype.card α:ℝ)^2)|≤_ at he
  convert he using 1
  · unfold cyclicMean
    congr 1
    ring
  · unfold cyclicMean carryRelative
    have hK : (K:ℝ)≠0 := by exact_mod_cast NeZero.ne K
    field_simp

variable (L : ℕ) [NeZero L]

noncomputable def naturalSet (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) (B : α → Set ℕ) : Set ℕ :=
  naturalOperator ((p*K)^2) L (cyclicColors p K f ρ ω) B

lemma naturalSet_mem (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) (B : α → Set ℕ) (a : ℕ) :
    a∈naturalSet p K L f ρ ω B ↔
      a/(((p*K)^2)*L)∈B (fineColor p K f ρ ω
        (reduceDigit ((p*K)^2) L (a : ZMod (((p*K)^2)*L)))) := by
  simp only [naturalSet,naturalOperator_mem,mem_cyclicColors]
  constructor
  · rintro ⟨i,hi,he⟩
    rwa [he]
  · intro ha
    exact ⟨_,ha,rfl⟩

omit [Nonempty α] in
lemma naturalSet_prefix_congr (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) (B C : α → Set ℕ) (N : ℕ)
    (hBC : ∀ i k, k≤N → (k∈B i ↔ k∈C i))
    (a : ℕ) (ha : a<(N+1)*(((p*K)^2)*L)) :
    a∈naturalSet p K L f ρ ω B ↔ a∈naturalSet p K L f ρ ω C :=
  naturalOperator_prefix_congr ((p*K)^2) L _ B C N hBC a ha

/-- Every fine residue is actually attained if all coarse colors are nonempty.
This is a full-projection statement, not an asymptotic equidistribution claim. -/
lemma naturalSet_full_projection (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) (B : α → Set ℕ) (hB : ∀ i, (B i).Nonempty)
    (z : ZMod (((p*K)^2)*L)) :
    ∃ a∈naturalSet p K L f ρ ω B, (a : ZMod (((p*K)^2)*L))=z := by
  obtain ⟨q,hq⟩ := hB (fineColor p K f ρ ω (reduceDigit ((p*K)^2) L z))
  have hc : ((z.val+(((p*K)^2)*L)*q : ℕ) : ZMod (((p*K)^2)*L))=z := by
    rw [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,
      add_zero,ZMod.natCast_zmod_val]
  refine ⟨z.val+(((p*K)^2)*L)*q,?_,hc⟩
  rw [naturalSet_mem,hc]
  have hz : (z.val+(((p*K)^2)*L)*q)/(((p*K)^2)*L)=q := by
    rw [Nat.add_mul_div_left _ _ (NeZero.pos (((p*K)^2)*L)),
      Nat.div_eq_of_lt (ZMod.val_lt z),Nat.zero_add]
  rwa [hz]

/-- Conditional all-target natural carry formula for a complete fine palette.
The scalar convolution of coarse color multiplicities is not assumed flat. -/
theorem naturalSet_profile_error (f : ZMod p → ZMod p) (ρ : Fin p ≃ ZMod p)
    (ω : Fin p → α) (ε : ℝ) (hε : 0≤ε)
    (hω : ∀ a b : α, ∀ t s : ZMod p,
      |(pairCount (colorClass f ρ ω a) (colorClass f ρ ω b) (t,s):ℝ)-
        (p:ℝ)^2/(Fintype.card α:ℝ)^2|≤ε*((p:ℝ)^2/(Fintype.card α:ℝ)^2))
    (B : α → Set ℕ) (n : ℕ) (hn : 0<n) (z : ZMod ((p*K)^2)) (r : Fin L) :
    |(sumRep (naturalSet p K L f ρ ω B)
        (n*(((p*K)^2)*L)+(blockDigit ((p*K)^2) L z r).val):ℝ)-
      cyclicMean (α := α) p K*(r.val*profileConv (colorWeight B) n+
        ((L:ℝ)-r.val)*profileConv (colorWeight B) (n-1))|≤
      cyclicMean (α := α) p K*(L*carryRelative K ε+1+carryRelative K ε)*
        (profileConv (colorWeight B) n+profileConv (colorWeight B) (n-1)) := by
  exact natural_operator_profile_error ((p*K)^2) L (cyclicColors p K f ρ ω)
    (cyclicColors_disjoint p K f ρ ω) _ _ (cyclicMean_pos p K).le
    (carryRelative_nonneg K ε hε) (cyclicColors_error p K f ρ ω ε hω) B n hn z r

/-- One coloring precedes all repetition counts, graphs, infinite coarse
families, and natural targets. The fourth-power color condition and both
carry errors are explicit. This is a fixed-field theorem. -/
theorem exists_universal_complete_natural (ρ : Fin p ≃ ZMod p) (hp : p≠2) :
    ∃ ω : Fin p → α, ∀ (K L : ℕ), ∀ _hK : NeZero K, ∀ _hL : NeZero L,
      ∀ (f : ZMod p → ZMod p) (D : ℕ), HasBoundedSums f D →
      ∀ ε : ℝ, 0≤ε → 10*(D:ℝ)^2*(Fintype.card α:ℝ)^4≤ε^2*p →
      ∀ (B : α → Set ℕ) (n : ℕ), 0<n →
      ∀ (z : ZMod ((p*K)^2)) (r : Fin L),
        |(sumRep (naturalSet p K L f ρ ω B)
            (n*(((p*K)^2)*L)+(blockDigit ((p*K)^2) L z r).val):ℝ)-
          cyclicMean (α := α) p K*(r.val*profileConv (colorWeight B) n+
            ((L:ℝ)-r.val)*profileConv (colorWeight B) (n-1))|≤
          cyclicMean (α := α) p K*(L*carryRelative K ε+1+carryRelative K ε)*
            (profileConv (colorWeight B) n+profileConv (colorWeight B) (n-1)) := by
  obtain ⟨ω,hω⟩ := exists_complete_plane_colors (α := α) ρ
    (by simpa only [ZMod.ringChar_zmod_n] using hp)
  refine ⟨ω,fun K L hK hL f D hf ε hε hsize B n hn z r ↦ ?_⟩
  letI := hK
  letI := hL
  exact naturalSet_profile_error p K L f ρ ω ε hε
    (hω f D hf ε hε hsize) B n hn z r

end Prime
end Erdos66UniversalCompleteNatural
