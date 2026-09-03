import Submission.CyclicAsymptoticExplore

/-! Cyclic flatness survives arbitrary changes on a sub-mean-size set.
In particular it permits independently specified short integer prefixes.
This is not the uniform integer-prefix conclusion needed in Spec.lean. -/
namespace Erdos66CyclicPrefixPatch
open Filter Erdos66CyclicAsymptotic
open scoped Classical Topology

section Group
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma count_le_of_agree_off (B C S : Finset G)
    (h : ∀ x, x ∉ S → (x ∈ B ↔ x ∈ C)) (z : G) :
    (B.filter (fun x ↦ z-x ∈ B)).card ≤
      (C.filter (fun x ↦ z-x ∈ C)).card + 2*S.card := by
  have hs : B.filter (fun x ↦ z-x ∈ B) ⊆
      (C.filter (fun x ↦ z-x ∈ C)) ∪ (S ∪ S.image (fun x ↦ z-x)) := by
    intro x hx
    obtain ⟨hx,hzx⟩ := Finset.mem_filter.mp hx
    by_cases hxs : x ∈ S
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxs)
    by_cases hzs : z-x ∈ S
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨z-x,hzs,by abel⟩))
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨(h x hxs).mp hx,(h (z-x) hzs).mp hzx⟩)
  have h₁ := Finset.card_le_card hs
  have h₂ := Finset.card_union_le (C.filter (fun x ↦ z-x ∈ C))
    (S ∪ S.image (fun x ↦ z-x))
  have h₃ := Finset.card_union_le S (S.image (fun x ↦ z-x))
  have h₄ := Finset.card_image_le (s := S) (f := fun x ↦ z-x)
  omega

lemma count_error_of_agree_off (B C S : Finset G)
    (h : ∀ x, x ∉ S → (x ∈ B ↔ x ∈ C)) (z : G) :
    |((B.filter (fun x ↦ z-x ∈ B)).card : ℝ)-
      ((C.filter (fun x ↦ z-x ∈ C)).card : ℝ)| ≤ 2*(S.card : ℝ) := by
  have h₁ : ((B.filter (fun x ↦ z-x ∈ B)).card : ℝ) ≤
      ((C.filter (fun x ↦ z-x ∈ C)).card : ℝ)+2*(S.card : ℝ) := by
    exact_mod_cast count_le_of_agree_off B C S h z
  have h₂ : ((C.filter (fun x ↦ z-x ∈ C)).card : ℝ) ≤
      ((B.filter (fun x ↦ z-x ∈ B)).card : ℝ)+2*(S.card : ℝ) := by
    exact_mod_cast count_le_of_agree_off C B S (fun x hx ↦ (h x hx).symm) z
  rw [abs_le]
  constructor <;> linarith
end Group

variable (N : ℕ) [NeZero N]

noncomputable def shortPrefix (L : ℕ) : Finset (ZMod N) :=
  Finset.univ.filter (fun z ↦ z.val < L)

noncomputable def patch (B : Finset (ZMod N)) (A : Set ℕ) (L : ℕ) : Finset (ZMod N) :=
  B.filter (fun z ↦ L ≤ z.val) ∪ (shortPrefix N L).filter (fun z ↦ z.val ∈ A)

lemma card_shortPrefix_le (L : ℕ) : (shortPrefix N L).card ≤ L := by
  have h : (shortPrefix N L).image ZMod.val ⊆ Finset.range L := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2
  have hval : Function.Injective (ZMod.val : ZMod N → ℕ) := ZMod.val_injective N
  simpa only [Finset.card_image_of_injective _ hval, Finset.card_range] using
    Finset.card_le_card h

lemma patch_agree (B : Finset (ZMod N)) (A : Set ℕ) (L : ℕ) (z : ZMod N) :
    z ∈ patch N B A L ↔ if z.val < L then z.val ∈ A else z ∈ B := by
  simp only [patch,shortPrefix,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs with h
  · simp [h,show ¬ L ≤ z.val by omega]
  · simp [h,show L ≤ z.val by omega]

lemma patch_error (B : Finset (ZMod N)) (A : Set ℕ) (L : ℕ) (z : ZMod N) :
    |cyclicCount N (patch N B A L) z-cyclicCount N B z| ≤ 2*(L : ℝ) := by
  have h := count_error_of_agree_off (patch N B A L) B (shortPrefix N L)
    (fun x hx ↦ by
      have hx' : ¬x.val < L := by simpa [shortPrefix] using hx
      simpa [hx'] using patch_agree N B A L x) z
  have hc : ((shortPrefix N L).card : ℝ) ≤ L := by exact_mod_cast card_shortPrefix_le N L
  exact h.trans (by gcongr)

noncomputable def patchedSequence (B : (N : ℕ) → Finset (ZMod N))
    (A : Set ℕ) (L : ℕ → ℕ) (N : ℕ) : Finset (ZMod N) :=
  if h : N = 0 then B N else @patch N ⟨h⟩ (B N) A (L N)

lemma patchedSequence_eq (B : (N : ℕ) → Finset (ZMod N))
    (A : Set ℕ) (L : ℕ → ℕ) :
    patchedSequence B A L N = patch N (B N) A (L N) := by
  simp [patchedSequence,NeZero.ne N]

variable {N}

/-- An arbitrary prescribed prefix of length o(f(N)) can be imposed on
uniformly self-flat cyclic templates at every large modulus. -/
theorem exists_flat_with_prescribed_prefix (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop)
    (hsub : Tendsto (fun N ↦ f N/(N : ℝ)) atTop (𝓝 0))
    (L : ℕ → ℕ) (hL : Tendsto (fun N ↦ (L N : ℝ)/f N) atTop (𝓝 0))
    (A : Set ℕ) :
    ∃ C : (N : ℕ) → Finset (ZMod N),
      (∀ N : ℕ, 0 < N → ∀ n : ℕ, n < L N → n < N →
        ((n : ZMod N) ∈ C N ↔ n ∈ A)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ z : ZMod N,
        |cyclicCount N (C N) z/f N-1| ≤ ε := by
  obtain ⟨B,hB⟩ := exists_uniformly_flat_sequence f hf hsub
  refine ⟨patchedSequence B A L,?_,?_⟩
  · intro N hN n hn hnN
    letI : NeZero N := ⟨by omega⟩
    rw [patchedSequence_eq N B A L,patch_agree]
    simp [ZMod.val_natCast_of_lt hnN,hn]
  · intro ε hε
    have hzero : Tendsto (fun N ↦ 2*((L N : ℝ)/f N)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hL.const_mul 2
    have hsmall := hzero.eventually_le_const (show 0 < ε/2 by positivity)
    filter_upwards [hB (ε/2) (by positivity),hsmall,
      (tendsto_atTop.1 hf) 1,eventually_ge_atTop 1] with N hBN hLN hfN hN
    letI : NeZero N := ⟨by omega⟩
    have hfp : 0 < f N := by linarith
    intro z
    rw [patchedSequence_eq N B A L]
    have hpatch : |cyclicCount N (patch N (B N) A (L N)) z/f N-
        cyclicCount N (B N) z/f N| ≤ ε/2 := by
      rw [← sub_div,abs_div,abs_of_pos hfp]
      calc
        _ ≤ (2*(L N : ℝ))/f N :=
          div_le_div_of_nonneg_right (patch_error N (B N) A (L N) z) hfp.le
        _ = 2*((L N : ℝ)/f N) := by ring
        _ ≤ _ := hLN
    exact (abs_sub_le _ (cyclicCount N (B N) z/f N) 1).trans
      (by linarith [hBN z])

lemma slow_prefix (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧
      Tendsto (fun N ↦ (L N : ℝ)/f N) atTop (𝓝 0) := by
  let L : ℕ → ℕ := fun N ↦ ⌊Real.sqrt (f N)⌋₊
  have hs := Real.tendsto_sqrt_atTop.comp hf
  refine ⟨L,?_,?_⟩
  · apply tendsto_atTop.2
    intro m
    filter_upwards [(tendsto_atTop.1 hs) ((m : ℝ)+1)] with N hN
    dsimp only [Function.comp_apply] at hN
    have hh := Nat.lt_floor_add_one (Real.sqrt (f N))
    have hm : (m : ℝ) < L N := by dsimp [L]; linarith
    exact (Nat.cast_lt.mp hm).le
  · have hz := tendsto_inv_atTop_zero.comp hs
    apply squeeze_zero' ?_ ?_ hz
    · filter_upwards [(tendsto_atTop.1 hf) 1] with N hN
      positivity
    · filter_upwards [(tendsto_atTop.1 hf) 1] with N hN
      have hp : 0 < f N := by linarith
      have hspos := Real.sqrt_pos.mpr hp
      have hsne := ne_of_gt hspos
      have hsq := Real.sq_sqrt hp.le
      have hfloor : (L N : ℝ) ≤ Real.sqrt (f N) := Nat.floor_le (Real.sqrt_nonneg _)
      change (L N : ℝ)/f N ≤ (Real.sqrt (f N))⁻¹
      apply (div_le_iff₀ hp).mpr
      have he : (Real.sqrt (f N))⁻¹*f N=Real.sqrt (f N) := by
        field_simp
        nlinarith
      simpa only [he] using hfloor

/-- Even pointwise convergence of prefixes adds no restriction: every set A
is the eventual prefix limit of uniformly flat cyclic templates. -/
theorem every_set_is_a_cyclic_prefix_limit (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop)
    (hsub : Tendsto (fun N ↦ f N/(N : ℝ)) atTop (𝓝 0)) (A : Set ℕ) :
    ∃ C : (N : ℕ) → Finset (ZMod N),
      (∀ n : ℕ, ∀ᶠ N : ℕ in atTop, (n : ZMod N) ∈ C N ↔ n ∈ A) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ z : ZMod N,
        |cyclicCount N (C N) z/f N-1| ≤ ε := by
  obtain ⟨L,hLt,hL⟩ := slow_prefix f hf
  obtain ⟨C,hC,hflat⟩ := exists_flat_with_prescribed_prefix f hf hsub L hL A
  refine ⟨C,?_,hflat⟩
  intro n
  filter_upwards [(tendsto_atTop.1 hLt) (n+1),eventually_ge_atTop (n+1)] with N hLN hN
  exact hC N (by omega) n (by omega) (by omega)

/-- At any positive logarithmic coefficient, every subset of the naturals
can be the pointwise prefix limit of finite cyclic sets satisfying the
cyclic logarithmic analogue. This is deliberately not an integer limit. -/
theorem logarithmic_templates_with_arbitrary_prefix_limit
    (c : ℝ) (hc : 0 < c) (A : Set ℕ) :
    ∃ C : (N : ℕ) → Finset (ZMod N),
      (∀ n : ℕ, ∀ᶠ N : ℕ in atTop, (n : ZMod N) ∈ C N ↔ n ∈ A) ∧
      ∀ z : (N : ℕ) → ZMod N,
        Tendsto (fun N ↦ cyclicCount N (C N) (z N)/Real.log N) atTop (𝓝 c) := by
  have hf : Tendsto (fun N : ℕ ↦ c*Real.log N) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have hsub : Tendsto (fun N : ℕ ↦ (c*Real.log N)/(N : ℝ)) atTop (𝓝 0) := by
    have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul c
    simpa only [Function.comp_apply,id_eq,mul_zero,mul_div_assoc] using hh
  obtain ⟨C,hprefix,hflat⟩ := every_set_is_a_cyclic_prefix_limit
    (fun N : ℕ ↦ c*Real.log N) hf hsub A
  refine ⟨C,hprefix,fun z ↦ ?_⟩
  have hlim : Tendsto (fun N ↦ cyclicCount N (C N) (z N)/(c*Real.log N))
      atTop (𝓝 1) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.1 (hflat (ε/2) (by positivity))
    refine ⟨N,fun n hn ↦ ?_⟩
    rw [Real.dist_eq]
    exact (hN n hn (z n)).trans_lt (by linarith)
  have hh := hlim.const_mul c
  convert hh using 1
  · funext N
    field_simp
  · ring

end Erdos66CyclicPrefixPatch
