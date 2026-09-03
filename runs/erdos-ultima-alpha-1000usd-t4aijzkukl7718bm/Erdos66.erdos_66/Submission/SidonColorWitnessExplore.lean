import Submission.SidonColorAnnuliExplore
import Submission.TauberianProfileExplore

/-! A hypothetical logarithmic witness requires linearly many Sidon colors
in its logarithmic scale, not merely its square root. This is a necessary
condition on component constructions and does not negate the conjecture. -/
namespace Erdos66SidonColorWitness
open Erdos66SidonColorBlockEnergy Erdos66SidonColorAnnuli Erdos66Counting
  Erdos66TauberianProfile Erdos66Explore Filter AdditiveCombinatorics
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma geometric_normalizer (k : ℕ) :
    Real.sqrt (((4^k : ℕ) : ℝ)*Real.log (4^k : ℕ)) =
      (2 : ℝ)^k*Real.sqrt k*Real.sqrt (Real.log 4) := by
  have hpow : (4 : ℝ)^k=((2 : ℝ)^k)^2 := by
    rw [show (4 : ℝ)=2*2 by norm_num,mul_pow,pow_two]
  push_cast
  rw [Real.log_pow,hpow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity),
    Real.sqrt_mul (Nat.cast_nonneg k)]
  ring

lemma geometric_count_limit {A : Set ℕ} {L : ℝ}
    (h : Tendsto (fun N ↦ (count A N : ℝ)/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 L)) :
    Tendsto (fun k : ℕ ↦ (count A (4^k) : ℝ)/((2 : ℝ)^k*Real.sqrt k)) atTop
      (𝓝 (L*Real.sqrt (Real.log 4))) := by
  have ht := h.comp (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(4 : ℕ)))
  have hs : Real.sqrt (Real.log 4) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos (by norm_num)))
  have he := ht.mul_const (Real.sqrt (Real.log 4))
  apply he.congr
  intro k
  simp only [Function.comp_apply]
  rw [geometric_normalizer]
  field_simp

lemma geometric_count_bounds {A : Set ℕ} {D : ℝ} (hD : 0<D)
    (h : Tendsto (fun k : ℕ ↦ (count A (4^k) : ℝ)/((2 : ℝ)^k*Real.sqrt k)) atTop (𝓝 D)) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ k, K ≤ k →
      (3*D/4)*((2 : ℝ)^k*Real.sqrt k) ≤ count A (4^k) ∧
      (count A (4^k) : ℝ) ≤ (5*D/4)*((2 : ℝ)^k*Real.sqrt k) := by
  have hlo := h.eventually_const_lt (show 3*D/4<D by linarith)
  have hhi := h.eventually_lt_const (show D<5*D/4 by linarith)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hlo.and hhi)
  refine ⟨max K 1,le_max_right _ _,fun k hk ↦ ?_⟩
  have hk1 : 1 ≤ k := (le_max_right K 1).trans hk
  have hp : (0 : ℝ)<(2 : ℝ)^k*Real.sqrt k := by positivity
  obtain ⟨hlo,hhi⟩ := hK k ((le_max_left _ _).trans hk)
  exact ⟨((lt_div_iff₀ hp).mp hlo).le,((div_lt_iff₀ hp).mp hhi).le⟩

lemma cutoff_mono' (A : Set ℕ) {N M : ℕ} (hNM : N ≤ M) : cutoff A N ⊆ cutoff A M := by
  intro n hn
  obtain ⟨hn,hA⟩ := mem_cutoff.mp hn
  exact mem_cutoff.mpr ⟨hn.trans_le hNM,hA⟩

lemma cutoff_shell_card (A : Set ℕ) {j L : ℕ} (hj : j+1 ≤ L) :
    shellMass (cutoff A (4^L)) j=count A (4^(j+1))-count A (4^j) := by
  have hpow : 4^(j+1) ≤ 4^L := Nat.pow_le_pow_right (by decide) hj
  have hsub : cutoff A (4^j) ⊆ cutoff A (4^(j+1)) :=
    cutoff_mono' A (Nat.pow_le_pow_right (by decide) (by omega))
  have he : (cutoff A (4^L)).filter (fun n ↦ 4^j ≤ n ∧ n<4^(j+1)) =
      cutoff A (4^(j+1)) \ cutoff A (4^j) := by
    ext n
    simp only [Finset.mem_filter,mem_cutoff,Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hn,hA⟩,hl,hh⟩
      exact ⟨⟨hh,hA⟩,fun he ↦ by omega⟩
    · rintro ⟨⟨hh,hA⟩,hnot⟩
      exact ⟨⟨hh.trans_le hpow,hA⟩,by by_contra hn; exact hnot ⟨by omega,hA⟩,hh⟩
  rw [shellMass,he,Finset.card_sdiff_of_subset hsub]
  rfl

lemma annulus_profile_of_bounds (A : Set ℕ) (D : ℝ) (hD : 0<D) (K : ℕ)
    (hbounds : ∀ k, K ≤ k →
      (3*D/4)*((2 : ℝ)^k*Real.sqrt k) ≤ count A (4^k) ∧
      (count A (4^k) : ℝ) ≤ (5*D/4)*((2 : ℝ)^k*Real.sqrt k))
    (J : ℕ) (hJ : K ≤ J) (j : ℕ) (hj : j∈Finset.Ico J (2*J)) :
    (D/4)^2*(4 : ℝ)^j*J ≤ (shellMass (cutoff A (4^(2*J))) j : ℝ)^2 := by
  obtain ⟨hJj,hjJ⟩ := Finset.mem_Ico.mp hj
  have hjK := hJ.trans hJj
  have hlo := (hbounds (j+1) (by omega)).1
  have hhi := (hbounds j hjK).2
  have hsqrt : Real.sqrt (j : ℝ) ≤ Real.sqrt (j+1 : ℕ) := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ j)
  have hp : (0 : ℝ) ≤ (2 : ℝ)^j := by positivity
  have hD0 : 0 ≤ D := hD.le
  have hlow : (D/4)*((2 : ℝ)^j*Real.sqrt j) ≤
      (count A (4^(j+1)) : ℝ)-count A (4^j) := by
    rw [pow_succ] at hlo
    have hh := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ (3*D/2)*(2 : ℝ)^j)
    nlinarith
  have hcardle : count A (4^j) ≤ count A (4^(j+1)) :=
    Finset.card_le_card (cutoff_mono' A (Nat.pow_le_pow_right (by decide) (by omega)))
  have hmass : (D/4)*((2 : ℝ)^j*Real.sqrt j) ≤
      (shellMass (cutoff A (4^(2*J))) j : ℝ) := by
    rw [cutoff_shell_card A (by omega : j+1 ≤ 2*J),Nat.cast_sub hcardle]
    exact hlow
  have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (D/4)*((2 : ℝ)^j*Real.sqrt j))
    (Nat.cast_nonneg _)).mpr hmass
  have hpow : ((2 : ℝ)^j)^2=(4 : ℝ)^j := by
    rw [pow_two,← mul_pow]; norm_num
  rw [mul_pow,mul_pow,hpow,Real.sq_sqrt (Nat.cast_nonneg j)] at hsq
  have hjR : (J : ℝ) ≤ j := by exact_mod_cast hJj
  exact (mul_le_mul_of_nonneg_left hjR (by positivity : 0 ≤ (D/4)^2*(4 : ℝ)^j)).trans (by simpa only [mul_assoc] using hsq)

lemma cutoff_size_of_bounds (A : Set ℕ) (D : ℝ) (hD : 0<D) (K : ℕ)
    (hbounds : ∀ k, K ≤ k →
      (3*D/4)*((2 : ℝ)^k*Real.sqrt k) ≤ count A (4^k) ∧
      (count A (4^k) : ℝ) ≤ (5*D/4)*((2 : ℝ)^k*Real.sqrt k))
    (J : ℕ) (hJ : K ≤ J) (hJ1 : 1 ≤ J) :
    ((cutoff A (4^(2*J))).card : ℝ) ≤ (5*D/2)*(4 : ℝ)^J*J := by
  have hhi := (hbounds (2*J) (by omega)).2
  have hpow : (2 : ℝ)^(2*J)=(4 : ℝ)^J := by rw [pow_mul]; norm_num
  rw [hpow] at hhi
  have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have hsqrt : Real.sqrt (2*J : ℕ) ≤ 2*(J : ℝ) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    push_cast
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ (5*D/4)*(4 : ℝ)^J)
  change (count A (4^(2*J)) : ℝ) ≤ _
  nlinarith

/-- Every hypothetical witness needs at least delta*J distinct-difference
colors on its prefix below 4^(2J), for one fixed delta>0. The coloring may
be selected afresh for every prefix. -/
theorem witness_requires_logarithmically_many_colors {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ δ : ℝ, 0<δ ∧ ∃ K : ℕ, ∀ J, K ≤ J → ∀ m : ℕ, ∀ col : ℕ → Fin m,
      DistinctColorDifferences (cutoff A (4^(2*J))) col → δ*J ≤ m := by
  let L := 2*Real.sqrt (c/Real.pi)
  let D := L*Real.sqrt (Real.log 4)
  have hcpos := limit_pos hc h
  have hL : 0<L := by dsimp [L]; positivity
  have hD : 0<D := mul_pos hL (Real.sqrt_pos.mpr (Real.log_pos (by norm_num)))
  have hgeo : Tendsto (fun k : ℕ ↦ (count A (4^k) : ℝ)/((2 : ℝ)^k*Real.sqrt k)) atTop (𝓝 D) :=
    geometric_count_limit (witness_counting_profile hc h)
  obtain ⟨K,hK1,hbounds⟩ := geometric_count_bounds hD hgeo
  let a := D/4
  let b := 5*D/2
  let δ := min 1 (a^2/(3*b+6))
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hδ : 0<δ := lt_min (by norm_num) (div_pos (sq_pos_of_pos ha) (by positivity))
  refine ⟨δ,hδ,K,fun J hJ m col hcol ↦ ?_⟩
  have hJ1 : 1 ≤ J := hK1.trans hJ
  have he := color_quadratic_bound (cutoff A (4^(2*J))) col hcol J a b
    (annulus_profile_of_bounds A D hD K hbounds J hJ)
    (cutoff_size_of_bounds A D hD K hbounds J hJ hJ1)
  simp only [Fintype.card_fin] at he
  exact linear_bound_of_quadratic a b m J ha hb.le (Nat.cast_nonneg _)
    (by exact_mod_cast (show 0<J by omega)) he

/-- In particular, an o(J)-color decomposition of these prefixes cannot
occur for a nonzero logarithmic witness. -/
theorem sublog_colors_exclude_witness (A : Set ℕ) (m : ℕ → ℕ)
    (col : (J : ℕ) → ℕ → Fin (m J))
    (hcol : ∀ J, DistinctColorDifferences (cutoff A (4^(2*J))) (col J))
    (hm : Tendsto (fun J : ℕ ↦ (m J : ℝ)/J) atTop (𝓝 0))
    (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro h
  obtain ⟨δ,hδ,K,hK⟩ := witness_requires_logarithmically_many_colors hc h
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hm.eventually_lt_const hδ)
  let J := max (max K L) 1
  have hJK : K ≤ J := (le_max_left K L).trans (le_max_left _ _)
  have hJL : L ≤ J := (le_max_right K L).trans (le_max_left _ _)
  have hJ1 : 1 ≤ J := le_max_right _ _
  have hJpos : (0 : ℝ)<J := by exact_mod_cast (show 0<J by omega)
  have hlo := hK J hJK (m J) (col J) (hcol J)
  have hhi := (div_lt_iff₀ hJpos).mp (hL J hJL)
  linarith

end Erdos66SidonColorWitness
