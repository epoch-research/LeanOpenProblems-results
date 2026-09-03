import FormalConjecturesUtil

/-! A finite coloring excluding strict cubic collisions in a compact range of
reduced gap ratios. This does not settle the positive-density conjecture. -/

namespace Erdos1206.CompactGapRatioColoring

/-- Multiplicative bins, periodically colored: equal colors on a bounded
multiplicative interval force two positive integers into the same bin. -/
theorem multiplicative_bins (q R : ℝ) (hq : 1 < q) (hR : 1 ≤ R) :
    ∃ m : ℕ, 0 < m ∧ ∃ color : ℕ → Fin m,
      ∀ a b : ℕ, 0 < a → a ≤ b → (b : ℝ) ≤ R*a →
        color a = color b → (b : ℝ) < q*a := by
  classical
  have hq0 : 0 < q := by linarith
  have hex (n : ℕ) : ∃ k : ℕ, q^k ≤ max 1 (n : ℝ) ∧
      max 1 (n : ℝ) < q^(k+1) :=
    exists_nat_pow_near (le_max_left _ _) hq
  choose index hindex using hex
  have hbound (n : ℕ) (hn : 0 < n) :
      q^(index n) ≤ (n : ℝ) ∧ (n : ℝ) < q^(index n+1) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa only [max_eq_right hnR] using hindex n
  obtain ⟨l,_,hl⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ R*q by nlinarith) hq
  let m := l+1
  have hm : 0 < m := by dsimp [m]; omega
  let color : ℕ → Fin m := fun n => ⟨index n % m, Nat.mod_lt _ hm⟩
  refine ⟨m,hm,color,?_⟩
  intro a b ha hab hba hc
  have hb : 0 < b := by omega
  obtain ⟨ha₁,ha₂⟩ := hbound a ha
  obtain ⟨hb₁,hb₂⟩ := hbound b hb
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hind : index a ≤ index b := by
    by_contra hh
    have hpow := pow_le_pow_right₀ hq.le (show index b+1 ≤ index a by omega)
    linarith
  have hfar : (b : ℝ) < q^(index a+m) := by
    calc
      (b : ℝ) ≤ R*a := hba
      _ < R*q^(index a+1) := mul_lt_mul_of_pos_left ha₂ (by linarith)
      _ = (R*q)*q^(index a) := by rw [pow_succ]; ring
      _ < q^m*q^(index a) := mul_lt_mul_of_pos_right hl (pow_pos hq0 _)
      _ = q^(index a+m) := by rw [pow_add]; ring
  have hnear : index b < index a+m := by
    by_contra hh
    have hpow := pow_le_pow_right₀ hq.le (show index a+m ≤ index b by omega)
    linarith
  have he : index a = index b := by
    have hemod : Nat.ModEq m (index a) (index b) := congrArg Fin.val hc
    apply hemod.eq_of_abs_lt
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (index b : ℤ) - index a)]
    omega
  calc
    (b : ℝ) < q^(index b+1) := hb₂
    _ = q*q^(index a) := by rw [← he,pow_succ]; ring
    _ ≤ q*a := mul_le_mul_of_nonneg_left ha₁ hq0.le

private lemma cofactor_bounds {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    3*x^2 ≤ x^2+x*y+y^2 ∧ x^2+x*y+y^2 ≤ 3*y^2 ∧
      y^2 ≤ x^2+x*y+y^2 := by
  have hy : 0 ≤ y := hx.trans hxy
  have h₁ := mul_nonneg (sub_nonneg.mpr hxy) hx
  have h₂ := mul_nonneg (sub_nonneg.mpr hxy) hy
  have h₃ := sq_nonneg x
  have h₄ := mul_nonneg hx hy
  constructor
  · nlinarith
  constructor <;> nlinarith

private lemma gap_upper_implies_size_bound {a b c d H : ℝ}
    (hH : 1 ≤ H) (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) (hgap : b-a ≤ H*(d-c)) : d ≤ 2*H*b := by
  have hb : 0 < b := ha.trans_lt hab
  have hc : 0 ≤ c := (hb.trans_le hbc).le
  have hd : 0 ≤ d := hc.trans hcd.le
  have hQ₀ := cofactor_bounds ha hab.le
  have hQ₁ := cofactor_bounds hc hcd.le
  have hfactor : (b-a)*(a^2+a*b+b^2)=(d-c)*(c^2+c*d+d^2) := by
    nlinarith only [he]
  have hQ : c^2+c*d+d^2 ≤ H*(a^2+a*b+b^2) := by
    have hmul := mul_le_mul_of_nonneg_right hgap (show 0 ≤ a^2+a*b+b^2 by positivity)
    apply (mul_le_mul_iff_right₀ (sub_pos.mpr hcd)).mp
    nlinarith only [hmul,hfactor]
  have hsq : d^2 ≤ 3*H*b^2 := by
    have hm := mul_le_mul_of_nonneg_left hQ₀.2.1 (show 0 ≤ H by linarith)
    nlinarith
  have hcoef : 3*H ≤ (2*H)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
  have hs : d^2 ≤ (2*H*b)^2 := by nlinarith
  exact (sq_le_sq₀ hd (by positivity)).mp hs

/-- A cubic collision with sufficiently close upper and lower middle roots
has gap ratio strictly less than `1+1/H`. -/
private lemma close_middle_roots {a b c d H : ℝ}
    (hH : 1 ≤ H) (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) (hclose : 100*H*d < (100*H+1)*b) :
    H*(b-a) < (H+1)*(d-c) := by
  have hb : 0 < b := ha.trans_lt hab
  have hc : 0 ≤ c := (hb.trans_le hbc).le
  have hd : 0 ≤ d := hc.trans hcd.le
  have hQ₀ := cofactor_bounds ha hab.le
  have hQ₁ := cofactor_bounds hc hcd.le
  have hfactor : (b-a)*(a^2+a*b+b^2)=(d-c)*(c^2+c*d+d^2) := by
    nlinarith only [he]
  have hd₂ : d ≤ 2*b := by nlinarith
  have hd₂sq : d^2 ≤ 4*b^2 := by nlinarith [sq_nonneg (2*b-d),mul_nonneg (by positivity : 0 ≤ 2*b+d) (sub_nonneg.mpr hd₂)]
  have hgap : b-a ≤ 12*(d-b) := by
    have hm₀ := mul_le_mul_of_nonneg_left hQ₀.2.2 (sub_pos.mpr hab).le
    have hm₁ := mul_le_mul_of_nonneg_left hQ₁.2.1 (sub_pos.mpr hcd).le
    have hm₂ := mul_le_mul_of_nonneg_left hd₂sq (show 0 ≤ 3*(d-c) by linarith)
    have hm₃ := mul_le_mul_of_nonneg_right (show d-c ≤ d-b by linarith) (show 0 ≤ 12*b^2 by positivity)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hb)).mp
    nlinarith only [hm₀,hm₁,hm₂,hm₃,hfactor]
  have ha_close : (100*H-12)*b < 100*H*a := by
    have hm := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 100*H by linarith)
    nlinarith only [hm,hclose]
  have ha_pos : 0 < a := by nlinarith
  by_contra hnot
  push_neg at hnot
  have hQ : (H+1)*(a^2+a*b+b^2) ≤ H*(c^2+c*d+d^2) := by
    have hm := mul_le_mul_of_nonneg_right hnot (show 0 ≤ a^2+a*b+b^2 by positivity)
    apply (mul_le_mul_iff_right₀ (sub_pos.mpr hcd)).mp
    have hf := congrArg (fun x : ℝ => H*x) hfactor
    dsimp only at hf
    nlinarith only [hm,hf]
  have had : (H+1)*a^2 ≤ H*d^2 := by
    have hm₀ := mul_le_mul_of_nonneg_left hQ₀.1 (show 0 ≤ H+1 by linarith)
    have hm₁ := mul_le_mul_of_nonneg_left hQ₁.2.1 (show 0 ≤ H by linarith)
    nlinarith only [hQ,hm₀,hm₁]
  have hspos : 0 < 100*H-12 := by linarith
  have ha_sq : ((100*H-12)*b)^2 < (100*H*a)^2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mpr ha_close
  have hd_sq : (100*H*d)^2 < ((100*H+1)*b)^2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mpr hclose
  have hm₀ := mul_lt_mul_of_pos_left ha_sq (show 0 < H+1 by linarith)
  have hm₁ := mul_le_mul_of_nonneg_left had (show 0 ≤ (100*H)^2 by positivity)
  have hm₂ := mul_lt_mul_of_pos_left hd_sq (show 0 < H by linarith)
  have hcoef : H*(100*H+1)^2 < (H+1)*(100*H-12)^2 := by
    have hh : 0 ≤ H*(H-1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hm₃ := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hb)
  nlinarith only [hm₀,hm₁,hm₂,hm₃]

/-- One fixed finite coloring excludes every strict cubic collision whose gap
ratio lies in `[1+1/H,H]`. In fact its second and fourth roots have different
colors. The common denominator of the gap ratio is unrestricted. -/
theorem compact_gap_ratio_coloring (H : ℕ) (hH : 1 ≤ H) :
    ∃ m : ℕ, 0 < m ∧ ∃ color : ℕ → Fin m,
      ∀ a b c d : ℕ, a < b → b ≤ c → c < d →
        a^3+d^3=b^3+c^3 →
        (H+1)*(d-c) ≤ H*(b-a) → b-a ≤ H*(d-c) →
        color b ≠ color d := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hs : (0 : ℝ) < 100*H := by positivity
  let q : ℝ := (100*H+1)/(100*H)
  have hq : 1 < q := by
    dsimp [q]
    apply (lt_div_iff₀ hs).mpr
    linarith
  obtain ⟨m,hm,color,hcolor⟩ := multiplicative_bins q (2*H) hq (by linarith)
  refine ⟨m,hm,color,?_⟩
  intro a b c d hab hbc hcd he hlow hupp hc
  have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hbcR : (b : ℝ) ≤ c := by exact_mod_cast hbc
  have hcdR : (c : ℝ) < d := by exact_mod_cast hcd
  have heR : (a : ℝ)^3+d^3=(b : ℝ)^3+c^3 := by exact_mod_cast he
  have hlowR : ((H : ℝ)+1)*((d : ℝ)-c) ≤ H*((b : ℝ)-a) := by
    have hh := (show (((H+1)*(d-c) : ℕ) : ℝ) ≤ ((H*(b-a) : ℕ) : ℝ) by exact_mod_cast hlow)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,
      Nat.cast_sub hcd.le,Nat.cast_sub hab.le] using hh
  have huppR : (b : ℝ)-a ≤ H*((d : ℝ)-c) := by
    have hh := (show ((b-a : ℕ) : ℝ) ≤ ((H*(d-c) : ℕ) : ℝ) by exact_mod_cast hupp)
    simpa only [Nat.cast_mul,Nat.cast_sub hcd.le,Nat.cast_sub hab.le] using hh
  have hbound := gap_upper_implies_size_bound hHR haR habR hbcR hcdR heR huppR
  have hnear := hcolor b d (by omega) (by omega) hbound hc
  have hclose : (100 : ℝ)*H*d < (100*H+1)*b := by
    have hh := mul_lt_mul_of_pos_right hnear hs
    dsimp only [q] at hh
    have heq : ((100*(H : ℝ)+1)/(100*H)*b)*(100*H)=(100*H+1)*b := by
      field_simp
    rw [heq] at hh
    nlinarith only [hh]
  have hlt := close_middle_roots hHR haR habR hbcR hcdR heR hclose
  linarith

/-- Repeated multiplicative intervals, with fixed geometric spacing. -/
def geometricBand (q r : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ, r^k ≤ (n : ℝ) ∧ (n : ℝ) < q*r^k}

open Filter
open scoped Topology

/-- The bands have positive lower density, not just positive upper density. -/
theorem geometricBand_lowerDensity_pos {q r : ℝ} (hq : 1 < q) (hr : 1 < r) :
    0 < (geometricBand q r).lowerDensity := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  let δ := (q-1)/(q*r)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hq) (mul_pos hq0 hr0)
  have hδeq : δ*(q*r)=q-1 := by dsimp [δ]; field_simp
  have hcount (N : ℕ) (hN : q ≤ (N : ℝ)) :
      δ*N-2 ≤ (((geometricBand q r ∩ Set.Iio N).ncard : ℕ) : ℝ) := by
    have hdiv : 1 ≤ (N : ℝ)/q := (le_div_iff₀ hq0).mpr (by simpa using hN)
    obtain ⟨k,hk₀,hk₁⟩ := exists_nat_pow_near hdiv hr
    let t := r^k
    have ht : 0 < t := pow_pos hr0 k
    have htN : q*t ≤ (N : ℝ) := by
      have hh := (le_div_iff₀ hq0).mp hk₀
      dsimp only [t]
      nlinarith only [hh]
    have hNt : (N : ℝ) < q*r*t := by
      have hh := (div_lt_iff₀ hq0).mp hk₁
      rw [pow_succ] at hh
      dsimp only [t]
      nlinarith only [hh]
    let lo := Nat.ceil t
    let hi := Nat.floor (q*t)
    have hsub : (↑(Finset.Ico lo hi) : Set ℕ) ⊆ geometricBand q r ∩ Set.Iio N := by
      intro n hn
      change n ∈ Finset.Ico lo hi at hn
      obtain ⟨hnlo,hnhi⟩ := Finset.mem_Ico.mp hn
      have hnl : (lo : ℝ) ≤ n := by exact_mod_cast hnlo
      have hnh : (n : ℝ) < hi := by exact_mod_cast hnhi
      have hhi : (hi : ℝ) ≤ q*t := Nat.floor_le (by positivity)
      have hlo : t ≤ (lo : ℝ) := Nat.le_ceil t
      refine ⟨⟨k,hlo.trans hnl,hnh.trans_le hhi⟩,?_⟩
      change n < N
      exact_mod_cast hnh.trans_le (hhi.trans htN)
    have hcard := Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset,Nat.card_Ico] at hcard
    have hcardR : ((hi-lo : ℕ) : ℝ) ≤ (geometricBand q r ∩ Set.Iio N).ncard := by
      exact_mod_cast hcard
    have hlo : (lo : ℝ) < t+1 := Nat.ceil_lt_add_one ht.le
    have hhi : q*t < (hi : ℝ)+1 := Nat.lt_floor_add_one (q*t)
    have hdiff : (hi : ℝ)-(lo : ℝ) ≤ ((hi-lo : ℕ) : ℝ) := by
      by_cases hle : lo ≤ hi
      · rw [Nat.cast_sub hle]
      · have hh : hi ≤ lo := by omega
        have hhR : (hi : ℝ) ≤ lo := by exact_mod_cast hh
        rw [Nat.sub_eq_zero_of_le hh]
        simp only [Nat.cast_zero]
        linarith
    have hmass := mul_lt_mul_of_pos_left hNt hδ
    have hm : δ*((q*r)*t)=(q-1)*t := by rw [← mul_assoc,hδeq]
    rw [mul_assoc q r t,← mul_assoc q r t] at hmass
    rw [hm] at hmass
    linarith
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (max q (4/δ))
  have hevent : ∀ᶠ N : ℕ in atTop,
      δ/2 ≤ (geometricBand q r).partialDensity Set.univ N := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hNN : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    have hNq : q ≤ (N : ℝ) := by linarith [le_max_left q (4/δ)]
    have hNδ : 4/δ < (N : ℝ) := by linarith [le_max_right q (4/δ)]
    have hNpos : (0 : ℝ) < N := hq0.trans_le hNq
    have hmass := (div_lt_iff₀ hδ).mp hNδ
    have hc := hcount N hNq
    simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Nat.ncard_Iio]
    apply (le_div_iff₀ hNpos).mpr
    nlinarith
  have hl : δ/2 ≤ (geometricBand q r).lowerDensity :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le atTop
      (fun N => Set.partialDensity_le_one (geometricBand q r) Set.univ N)) hevent
  exact (half_pos hδ).trans_le hl

private lemma geometricBand_close {q r R : ℝ}
    (hq : 0 < q) (hr : 1 < r) (hR : 0 < R) (hsep : R*q < r)
    {a b : ℕ} (ha : a ∈ geometricBand q r) (hb : b ∈ geometricBand q r)
    (hbound : (b : ℝ) ≤ R*a) : (b : ℝ) < q*a := by
  obtain ⟨i,hi₀,hi₁⟩ := ha
  obtain ⟨j,hj₀,hj₁⟩ := hb
  have hji : j ≤ i := by
    by_contra hh
    have hij : i+1 ≤ j := by omega
    have hp := pow_le_pow_right₀ hr.le hij
    have ht : 0 < r^i := pow_pos (by linarith) i
    have hsep' := mul_lt_mul_of_pos_right hsep ht
    have hupper := mul_lt_mul_of_pos_left hi₁ hR
    rw [pow_succ] at hp
    nlinarith only [hbound,hp,hsep',hupper,hj₀]
  have hp := pow_le_pow_right₀ hr.le hji
  exact hj₁.trans_le (mul_le_mul_of_nonneg_left (hp.trans hi₀) hq.le)

/-- Explicit positive-lower-density avoidance of every gap ratio in a compact
subinterval of `(1,∞)`. This does NOT assert full cube-Sidonness. -/
theorem positive_density_avoids_compact_gap_ratios (H : ℕ) (hH : 1 ≤ H) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ a b c d : ℕ, a < b → b ≤ c → c < d →
        a^3+d^3=b^3+c^3 →
        (H+1)*(d-c) ≤ H*(b-a) → b-a ≤ H*(d-c) →
        ¬ (b ∈ A ∧ d ∈ A) := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hs : (0 : ℝ) < 100*H := by positivity
  let q : ℝ := (100*H+1)/(100*H)
  let r : ℝ := 2*H*q+1
  have hq : 1 < q := by
    dsimp [q]
    apply (lt_div_iff₀ hs).mpr
    linarith
  have hq0 : 0 < q := by linarith
  have hr : 1 < r := by dsimp [r]; nlinarith
  let A := geometricBand q r
  have hden : 0 < A.lowerDensity := geometricBand_lowerDensity_pos hq hr
  refine ⟨A,?_,hden,?_⟩
  · by_contra hfin
    have hz := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
    change A.lowerDensity=0 at hz
    linarith
  · intro a b c d hab hbc hcd he hlow hupp hmem
    have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    have hbcR : (b : ℝ) ≤ c := by exact_mod_cast hbc
    have hcdR : (c : ℝ) < d := by exact_mod_cast hcd
    have heR : (a : ℝ)^3+d^3=(b : ℝ)^3+c^3 := by exact_mod_cast he
    have hlowR : ((H : ℝ)+1)*((d : ℝ)-c) ≤ H*((b : ℝ)-a) := by
      have hh := (show (((H+1)*(d-c) : ℕ) : ℝ) ≤ ((H*(b-a) : ℕ) : ℝ) by exact_mod_cast hlow)
      simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,
        Nat.cast_sub hcd.le,Nat.cast_sub hab.le] using hh
    have huppR : (b : ℝ)-a ≤ H*((d : ℝ)-c) := by
      have hh := (show ((b-a : ℕ) : ℝ) ≤ ((H*(d-c) : ℕ) : ℝ) by exact_mod_cast hupp)
      simpa only [Nat.cast_mul,Nat.cast_sub hcd.le,Nat.cast_sub hab.le] using hh
    have hbound := gap_upper_implies_size_bound hHR haR habR hbcR hcdR heR huppR
    have hnear := geometricBand_close hq0 hr (show (0 : ℝ) < 2*H by positivity)
      (show (2*(H : ℝ))*q < r by dsimp [r]; linarith) hmem.1 hmem.2 hbound
    have hclose : (100 : ℝ)*H*d < (100*H+1)*b := by
      have hh := mul_lt_mul_of_pos_right hnear hs
      dsimp only [q] at hh
      have heq : ((100*(H : ℝ)+1)/(100*H)*b)*(100*H)=(100*H+1)*b := by
        field_simp
      rw [heq] at hh
      nlinarith only [hh]
    have hlt := close_middle_roots hHR haR habR hbcR hcdR heR hclose
    linarith

/-- The real root-ratio interval behind the compact-gap coloring. This form
can be applied to a positive-density subset of an arbitrary source. -/
lemma compact_gap_root_ratio {a b c d H : ℝ}
    (hH : 1 ≤ H) (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3)
    (hlow : (H+1)*(d-c) ≤ H*(b-a)) (hupp : b-a ≤ H*(d-c)) :
    ((100*H+1)/(100*H))*b ≤ d ∧ d ≤ (2*H)*b := by
  have hs : 0 < 100*H := by linarith
  have hnot : (100*H+1)*b ≤ 100*H*d := by
    by_contra hh
    have hclose : 100*H*d < (100*H+1)*b := lt_of_not_ge hh
    have hh := close_middle_roots hH ha hab hbc hcd he hclose
    linarith
  constructor
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hs).mpr
    simpa only [mul_comm] using hnot
  · exact gap_upper_implies_size_bound hH ha hab hbc hcd he hupp

#print axioms compact_gap_root_ratio

#print axioms multiplicative_bins
#print axioms compact_gap_ratio_coloring
#print axioms geometricBand_lowerDensity_pos
#print axioms positive_density_avoids_compact_gap_ratios

end Erdos1206.CompactGapRatioColoring
