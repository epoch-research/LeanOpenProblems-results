import Submission.ClippedModulusTuningExplore

/-! Logarithmically tuned finite cyclic palettes on unbounded powers of two.
The finite period need not retain a large prime factor. Different dyadic
palettes are not claimed to agree on any prescribed natural prefix. -/
namespace Erdos66DyadicCyclicPalette
open Filter Erdos66ClippedModulus Erdos66ClippedModulusTuning
  Erdos66PrefixBalancedPalette Erdos66OuterMixedPrefix Erdos66OuterCarryProfile
  Erdos66SaturatingCyclicFamily
open scoped Topology Classical
set_option maxHeartbeats 2600000

lemma half_scale_log_bound (M L : ℕ) (hM : 2 ≤ M) (hML : M ≤ L) (hLM : L ≤ 2*M) :
    0<Real.log (M:ℝ) ∧ Real.log (L:ℝ) ≤ 2*Real.log M := by
  have hm : (1:ℝ)<M := by exact_mod_cast (show 1<M by omega)
  have hl : (0:ℝ)<L := by exact_mod_cast (show 0<L by omega)
  refine ⟨Real.log_pos hm,?_⟩
  have hs : (L:ℝ) ≤ (M:ℝ)^2 := by
    have hh : L ≤ M^2 := by nlinarith
    exact_mod_cast hh
  have hh := Real.log_le_log hl hs
  simpa only [Real.log_pow,Nat.cast_ofNat] using hh

/-- A complete joint prefix-balanced palette and a precisely tuned sparse
member exist on arbitrarily large DYADIC cyclic groups. -/
theorem exists_dyadic_logarithmic_palette (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) (N₀ : ℕ) :
    ∃ k : ℕ, N₀<k ∧ ∃ B : Finset (ZMod (2^k)),
      ∃ P : Finset (Finset (ZMod (2^k))), B∈P ∧ Finset.univ∈P ∧
        (∀ C∈P, ∀ D∈P, C ⊆ D ∨ D ⊆ C) ∧
        (∀ z : ZMod (2^k), ∀ u : ℕ, u ≤ 2^k →
          |(prefixCount (2^k) B B z u:ℝ)/Real.log (2^k:ℕ)-
            (u:ℝ)/(2^k:ℕ)*c| ≤ δ) ∧
        (∀ C∈P, ∀ D∈P, ∀ z u, u ≤ 2^k →
          |(prefixCount (2^k) C D z u:ℝ)-(u:ℝ)/(2^k:ℕ)*actualMean (2^k) C D| ≤
            δ*actualMean (2^k) C D) := by
  let t := min (1/16) (δ/(100*(c+1)))
  have ht : 0<t := by dsimp [t]; positivity
  have ht16 : t ≤ 1/16 := min_le_left _ _
  have ht1 : t ≤ 1 := by linarith
  have htbudget : 100*t*(c+1) ≤ δ := by
    have hh := (le_div_iff₀ (by positivity : 0<100*(c+1))).mp
      (min_le_right (1/16) (δ/(100*(c+1))))
    change t*(100*(c+1)) ≤ δ at hh
    nlinarith only [hh]
  have hlim : Tendsto (fun M : ℕ ↦ c*Real.log M/(M:ℝ)) atTop (𝓝 0) := by
    have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul c
    simpa only [Function.comp_apply,id_eq,mul_zero,mul_div_assoc] using hh
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hlim.eventually_le_const (by norm_num : (0:ℝ)<1))
  let R := max 2 (max T (2^(N₀+1)))
  obtain ⟨L,hLR,hodd,hL,B₀,P,hBpos,hBmem,htune,hBsub,hnest,hflat,hprefix,hfull,hPcard,hcover⟩ :=
    exists_prefix_balanced_complete_palette (c/8) (c/8) t t
      (by positivity) (by positivity) ht ht1 ht ht1 (2*R)
  letI := hL
  let k := Nat.log 2 L
  let M := 2^k
  have hMpos : 0<M := by dsimp [M]; positivity
  letI : NeZero M := ⟨hMpos.ne'⟩
  have hML : M ≤ L := Nat.pow_log_le_self 2 (NeZero.ne L)
  have hLM : L<2*M := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1<2) L
    simpa only [Nat.pow_succ, Nat.mul_comm, M, k] using hh
  have hRM : R<M := by omega
  have hM2 : 2 ≤ M := by dsimp [R] at hRM; omega
  have hMT : T ≤ M := by dsimp [R] at hRM; omega
  have hk : N₀<k := by
    have hpow : 2^(N₀+1) ≤ 2^k := by change 2^(N₀+1) ≤ M; dsimp [R] at hRM; omega
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hpow
    omega
  obtain ⟨hlogM,hlogLM⟩ := half_scale_log_bound M L hM2 hML hLM.le
  have hlogL : 0<Real.log (L:ℝ) := Real.log_pos (by exact_mod_cast (show 1<L by omega))
  have hm : (0:ℝ)<M := by exact_mod_cast hMpos
  have hl : (0:ℝ)<L := by exact_mod_cast NeZero.pos L
  have hbaseμ : actualMean L B₀ B₀ ≤ c*Real.log M := by
    have htune' := (abs_lt.mp htune).2
    have hquarter : actualMean L B₀ B₀/Real.log L ≤ c/4 := by linarith
    have hh := (div_le_iff₀ hlogL).mp hquarter
    have hh' := mul_le_mul_of_nonneg_left hlogLM (show 0 ≤ c/4 by positivity)
    have hp := mul_pos hc hlogM
    nlinarith only [hh,hh',hp]
  have hbase : actualMean L B₀ B₀ ≤ (c*Real.log M)*L/M := by
    have hfac : (1:ℝ) ≤ (L:ℝ)/M := (one_le_div hm).mpr (by exact_mod_cast hML)
    have hh := mul_le_mul_of_nonneg_left hfac (show 0 ≤ c*Real.log M by positivity)
    exact hbaseμ.trans (by simpa only [mul_one, mul_div_assoc] using hh)
  have hcap : c*Real.log M ≤ M := by
    have hh := (div_le_iff₀ hm).mp (hT M hMT)
    simpa only [one_mul] using hh
  obtain ⟨C,hCP,hC⟩ := exists_clipped_tuned_member M L hML hLM.le B₀ P
    (c*Real.log M) t t (by positivity) ht.le ht1 ht.le
    (fun C hCP ↦ hprefix C hCP C hCP) hcover hbase hcap
  let Q := P.image (rebase M L)
  refine ⟨k,hk,rebase M L C,Q,Finset.mem_image.mpr ⟨C,hCP,rfl⟩,
    Finset.mem_image.mpr ⟨Finset.univ,hfull,rebase_univ M L⟩,?_,?_,?_⟩
  · intro C hC D hD
    obtain ⟨C,hCP,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D,hDP,rfl⟩ := Finset.mem_image.mp hD
    rcases hnest C hCP D hDP with hh | hh
    · exact Or.inl (rebase_mono M L hh)
    · exact Or.inr (rebase_mono M L hh)
  · intro z u hu
    have hh := div_le_div_of_nonneg_right (hC z u hu) hlogM.le
    have he : ((prefixCount M (rebase M L C) (rebase M L C) z u:ℝ)-
        (u:ℝ)/M*(c*Real.log M))/Real.log M=
        (prefixCount M (rebase M L C) (rebase M L C) z u:ℝ)/Real.log M-(u:ℝ)/M*c := by
      field_simp
    have hh' : |((prefixCount M (rebase M L C) (rebase M L C) z u:ℝ)-
        (u:ℝ)/M*(c*Real.log M))/Real.log M| ≤
        (32*t+3*t)*(c*Real.log M)/Real.log M := by
      simpa only [abs_div, abs_of_pos hlogM] using hh
    rw [he] at hh'
    have hright : ((32*t+3*t)*(c*Real.log M))/Real.log M=(32*t+3*t)*c := by field_simp
    rw [hright] at hh'
    change |(prefixCount M (rebase M L C) (rebase M L C) z u:ℝ)/Real.log M-(u:ℝ)/M*c| ≤ δ
    have hp : 0 ≤ t*c := mul_nonneg ht.le hc.le
    exact hh'.trans (by nlinarith only [htbudget,hp,ht])
  · intro C hC D hD z u hu
    obtain ⟨C,hCP,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D,hDP,rfl⟩ := Finset.mem_image.mp hD
    have hh := rebase_prefix_actual_error M L hML hLM.le C D t ht.le ht16
      (hprefix C hCP D hDP) z u hu
    have hsmall : 32*t ≤ δ := by nlinarith [mul_nonneg ht.le hc.le]
    exact hh.trans (mul_le_mul_of_nonneg_right hsmall (actualMean_nonneg M _ _))

end Erdos66DyadicCyclicPalette
