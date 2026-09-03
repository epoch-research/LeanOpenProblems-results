import Submission.PrimitiveSquareCollisions

/-!
Elementary parity-sensitive lattice counts for triangular parameter regions.
These estimates are auxiliary to square-collision counting.
-/
noncomputable section
namespace Erdos773.ParityTriangleCount
open Finset
set_option maxHeartbeats 1000000

lemma interval_card_bound (S : Finset ℕ) (L U : ℝ) (hLU : L ≤ U)
    (h : ∀ n ∈ S, L ≤ n ∧ (n : ℝ) ≤ U) : (S.card : ℝ) ≤ U-L+1 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [card_empty,Nat.cast_zero]
    linarith
  · let a := S.min' hS
    let b := S.max' hS
    have ha : a ∈ S := min'_mem _ hS
    have hb : b ∈ S := max'_mem _ hS
    have hab : a ≤ b := min'_le _ _ hb
    have hsub : S ⊆ Icc a b := fun n hn => mem_Icc.mpr
      ⟨min'_le _ _ hn,le_max' _ _ hn⟩
    have hc := card_le_card hsub
    have hcard : (Icc a b).card = b-a+1 := by simp; omega
    rw [hcard] at hc
    have hcast : (S.card : ℝ) ≤ (b : ℝ)-a+1 := by
      exact_mod_cast (show S.card ≤ b-a+1 from hc)
    have hal := (h a ha).1
    have hbu := (h b hb).2
    linarith

lemma residue_interval_card_bound (S : Finset ℕ) (L U : ℝ) (q s : ℕ)
    (hq : 0 < q) (hLU : L ≤ U)
    (h : ∀ n ∈ S, n%q=s ∧ L ≤ n ∧ (n : ℝ) ≤ U) :
    (S.card : ℝ) ≤ (U-L)/q+1 := by
  let T := S.image (fun n => n/q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hinj : Set.InjOn (fun n : ℕ => n/q) S := by
    intro n hn m hm he
    have hn' := (h n hn).1
    have hm' := (h m hm).1
    dsimp only at he
    have hnq := Nat.mod_add_div n q
    have hmq := Nat.mod_add_div m q
    rw [hn',he] at hnq
    rw [hm'] at hmq
    omega
  have hcard : T.card = S.card := card_image_iff.mpr hinj
  have hT : ∀ n ∈ T, (L-s)/q ≤ n ∧ (n : ℝ) ≤ (U-s)/q := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    obtain ⟨hmod,hl,hu⟩ := h m hm
    have he : m = q*(m/q)+s := by have hh := Nat.mod_add_div m q; omega
    have heR : (m : ℝ) = q*(m/q : ℕ)+s := by exact_mod_cast he
    constructor
    · apply (div_le_iff₀ hqR).mpr
      nlinarith only [heR,hl]
    · apply (le_div_iff₀ hqR).mpr
      nlinarith only [heR,hu]
  have hh := interval_card_bound T ((L-s)/q) ((U-s)/q)
    (div_le_div_of_nonneg_right (by linarith) hqR.le) hT
  rw [hcard] at hh
  have heq : (U-s)/q-(L-s)/q+1 = (U-L)/q+1 := by ring
  rwa [heq] at hh

lemma parity_interval_card_bound (S : Finset ℕ) (L U : ℝ) (s : ℕ)
    (_hs : s < 2) (hLU : L ≤ U)
    (h : ∀ n ∈ S, n%2=s ∧ L ≤ n ∧ (n : ℝ) ≤ U) :
    (S.card : ℝ) ≤ (U-L)/2+1 := by
  let T := S.image (fun n => n/2)
  have hinj : Set.InjOn (fun n : ℕ => n/2) S := by
    intro n hn m hm he
    have hn' := (h n hn).1
    have hm' := (h m hm).1
    dsimp only at he
    omega
  have hcard : T.card = S.card := card_image_iff.mpr hinj
  have hT : ∀ n ∈ T, (L-s)/2 ≤ n ∧ (n : ℝ) ≤ (U-s)/2 := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    obtain ⟨hmod,hl,hu⟩ := h m hm
    have he : m = 2*(m/2)+s := by omega
    have heR : (m : ℝ) = 2*(m/2 : ℕ)+s := by exact_mod_cast he
    constructor <;> linarith
  have hh := interval_card_bound T ((L-s)/2) ((U-s)/2) (by linarith) hT
  rw [hcard] at hh
  linarith

lemma sum_Icc_cast (K : ℕ) :
    ∑ k ∈ Icc 1 K, (k : ℝ) = (K : ℝ)*(K+1)/2 := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega),ih]
    push_cast
    ring

lemma sum_range_cast (K : ℕ) :
    ∑ k ∈ range K, (k : ℝ) = (K : ℝ)*(K-1)/2 := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [sum_range_succ,ih]
    push_cast
    ring

/-- Possible positive even first coordinates. -/
def evenG (A D : ℝ) : Finset ℕ := (Icc 1 (⌊A/D⌋₊/2)).image (fun k => 2*k)

/-- Possible positive odd first coordinates. -/
def oddG (A D : ℝ) : Finset ℕ := (range ((⌊A/D⌋₊+1)/2)).image (fun k => 2*k+1)

lemma mem_evenG {A D : ℝ} {g : ℕ} :
    g ∈ evenG A D ↔ 0 < g ∧ g ≤ ⌊A/D⌋₊ ∧ g%2=0 := by
  simp only [evenG,mem_image,mem_Icc]
  constructor
  · rintro ⟨k,⟨hk,hK⟩,rfl⟩
    omega
  · rintro ⟨hg,hG,hpar⟩
    exact ⟨g/2,by omega,by omega⟩

lemma mem_oddG {A D : ℝ} {g : ℕ} :
    g ∈ oddG A D ↔ 0 < g ∧ g ≤ ⌊A/D⌋₊ ∧ g%2=1 := by
  simp only [oddG,mem_image,mem_range]
  constructor
  · rintro ⟨k,hK,rfl⟩
    omega
  · rintro ⟨hg,hG,hpar⟩
    exact ⟨g/2,by omega,by omega⟩

lemma evenG_linear_sum (A D : ℝ) :
    ∑ g ∈ evenG A D, ((A-D*g)/2+1) =
      let K : ℝ := (⌊A/D⌋₊/2 : ℕ)
      K*(A/2+1)-D*K*(K+1)/2 := by
  unfold evenG
  rw [sum_image (by intro a ha b hb hh; dsimp only at hh; omega)]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  calc
    _ = ∑ k ∈ Icc 1 (⌊A/D⌋₊/2), ((A/2+1)-D*k) := by
      apply sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      rw [sum_sub_distrib,sum_const,← mul_sum,sum_Icc_cast]
      simp only [Nat.card_Icc,nsmul_eq_mul]
      norm_num
      ring

lemma oddG_linear_sum (A D : ℝ) :
    ∑ g ∈ oddG A D, ((A-D*g)/2+1) =
      let K : ℝ := ((⌊A/D⌋₊+1)/2 : ℕ)
      K*(A/2+1)-D*K^2/2 := by
  unfold oddG
  rw [sum_image (by intro a ha b hb hh; dsimp only at hh; omega)]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  calc
    _ = ∑ k ∈ range ((⌊A/D⌋₊+1)/2), ((A/2+1-D/2)-D*k) := by
      apply sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      rw [sum_sub_distrib,sum_const,← mul_sum,sum_range_cast]
      simp only [card_range,nsmul_eq_mul]
      ring

/-- Counting by first-coordinate fibers; no probabilistic input is used. -/
lemma fiber_count (H : Finset (ℕ × ℕ)) (G : Finset ℕ) (A C r : ℝ) (s : ℕ)
    (hs : s < 2)
    (hG : ∀ g ∈ G, (C+r)*g ≤ A)
    (hH : ∀ t ∈ H, t.1 ∈ G ∧ t.2%2=s ∧ C*t.1 ≤ t.2 ∧
      (t.2 : ℝ)+r*t.1 ≤ A) :
    (H.card : ℝ) ≤ ∑ g ∈ G, ((A-(C+r)*g)/2+1) := by
  have hc : H.card = ∑ g ∈ G, (H.filter (fun t => t.1=g)).card :=
    card_eq_sum_card_fiberwise (fun t ht => (hH t ht).1)
  rw [hc,Nat.cast_sum]
  apply sum_le_sum
  intro g hg
  let T := (H.filter (fun t => t.1=g)).image Prod.snd
  have hTi : Set.InjOn (Prod.snd : ℕ × ℕ → ℕ) (H.filter (fun t => t.1=g)) := by
    intro t ht u hu he
    have ht' := (mem_filter.mp ht).2
    have hu' := (mem_filter.mp hu).2
    exact Prod.ext (by omega) he
  have hTc : T.card = (H.filter (fun t => t.1=g)).card := card_image_iff.mpr hTi
  have hT : ∀ n ∈ T, n%2=s ∧ C*g ≤ n ∧ (n : ℝ) ≤ A-r*g := by
    intro n hn
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hn
    obtain ⟨ht,htg⟩ := mem_filter.mp ht
    obtain ⟨_,hpar,hl,hu⟩ := hH t ht
    rw [htg] at hl hu
    exact ⟨hpar,hl,by linarith⟩
  have hgg := hG g hg
  have hb := parity_interval_card_bound T (C*g) (A-r*g) s hs (by nlinarith) hT
  rw [hTc] at hb
  nlinarith only [hb]

/-- A triangular region with both coordinates even. -/
theorem even_triangle_count (H : Finset (ℕ × ℕ)) (A C r : ℝ)
    (hA : 0 ≤ A) (hD : 1 ≤ C+r)
    (hH : ∀ t ∈ H, 0 < t.1 ∧ t.1%2=0 ∧ t.2%2=0 ∧
      C*t.1 ≤ t.2 ∧ (t.2 : ℝ)+r*t.1 ≤ A) :
    (H.card : ℝ) ≤ A^2/(8*(C+r))+A/2 := by
  let D := C+r
  have hD0 : 0 < D := by dsimp [D]; linarith
  have hAD : 0 ≤ A/D := div_nonneg hA hD0.le
  have hf := Nat.floor_le hAD
  have hG : ∀ g ∈ evenG A D, D*g ≤ A := by
    intro g hg
    have hg' := (mem_evenG.mp hg).2.1
    have hgf : (g : ℝ) ≤ (⌊A/D⌋₊ : ℝ) := by exact_mod_cast hg'
    have hgR : (g : ℝ) ≤ A/D := hgf.trans hf
    nlinarith only [(le_div_iff₀ hD0).mp hgR]
  have hH' : ∀ t ∈ H, t.1 ∈ evenG A D ∧ t.2%2=0 ∧ C*t.1 ≤ t.2 ∧
      (t.2 : ℝ)+r*t.1 ≤ A := by
    intro t ht
    obtain ⟨hg,hpar,hpar',hl,hu⟩ := hH t ht
    have htD : D*t.1 ≤ A := by dsimp [D]; nlinarith
    have htR : (t.1 : ℝ) ≤ A/D := (le_div_iff₀ hD0).mpr (by nlinarith only [htD])
    exact ⟨mem_evenG.mpr ⟨hg,Nat.le_floor htR,hpar⟩,hpar',hl,hu⟩
  have hb := fiber_count H (evenG A D) A C r 0 (by omega) hG hH'
  change (H.card : ℝ) ≤ ∑ g ∈ evenG A D, ((A-D*g)/2+1) at hb
  rw [evenG_linear_sum] at hb
  let K : ℝ := (⌊A/D⌋₊/2 : ℕ)
  change (H.card : ℝ) ≤ K*(A/2+1)-D*K*(K+1)/2 at hb
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKbound : 2*K ≤ A/D := by
    have hnat : 2*(⌊A/D⌋₊/2) ≤ ⌊A/D⌋₊ := Nat.mul_div_le _ _
    have hcast : 2*K ≤ (⌊A/D⌋₊ : ℝ) := by dsimp [K]; exact_mod_cast hnat
    exact hcast.trans hf
  have hKD : 2*D*K ≤ A := by nlinarith [(le_div_iff₀ hD0).mp hKbound]
  have hD1 : 1 ≤ D := hD
  have hKA : K ≤ A/2 := by nlinarith
  have hnon : 0 ≤ D*K := mul_nonneg hD0.le hK
  have hquad : K*A/2-D*K^2/2 ≤ A^2/(8*D) := by
    apply (le_div_iff₀ (show 0 < 8*D by positivity)).mpr
    nlinarith only [sq_nonneg (A-2*D*K)]
  change (H.card : ℝ) ≤ A^2/(8*D)+A/2
  nlinarith only [hb,hquad,hKA,hnon]

/-- A triangular region with both coordinates odd. -/
theorem odd_triangle_count (H : Finset (ℕ × ℕ)) (A C r : ℝ)
    (hA : 0 ≤ A) (hD : 1 ≤ C+r)
    (hH : ∀ t ∈ H, 0 < t.1 ∧ t.1%2=1 ∧ t.2%2=1 ∧
      C*t.1 ≤ t.2 ∧ (t.2 : ℝ)+r*t.1 ≤ A) :
    (H.card : ℝ) ≤ A^2/(8*(C+r))+A/2+1/2 := by
  let D := C+r
  have hD0 : 0 < D := by dsimp [D]; linarith
  have hf := Nat.floor_le (div_nonneg hA hD0.le)
  have hG : ∀ g ∈ oddG A D, D*g ≤ A := by
    intro g hg
    have hg' := (mem_oddG.mp hg).2.1
    have hgf : (g : ℝ) ≤ (⌊A/D⌋₊ : ℝ) := by exact_mod_cast hg'
    nlinarith only [(le_div_iff₀ hD0).mp (hgf.trans hf)]
  have hH' : ∀ t ∈ H, t.1 ∈ oddG A D ∧ t.2%2=1 ∧ C*t.1 ≤ t.2 ∧
      (t.2 : ℝ)+r*t.1 ≤ A := by
    intro t ht
    obtain ⟨hg,hpar,hpar',hl,hu⟩ := hH t ht
    have htD : D*t.1 ≤ A := by dsimp [D]; nlinarith
    have htR : (t.1 : ℝ) ≤ A/D := (le_div_iff₀ hD0).mpr (by nlinarith only [htD])
    exact ⟨mem_oddG.mpr ⟨hg,Nat.le_floor htR,hpar⟩,hpar',hl,hu⟩
  have hb := fiber_count H (oddG A D) A C r 1 (by omega) hG hH'
  change (H.card : ℝ) ≤ ∑ g ∈ oddG A D, ((A-D*g)/2+1) at hb
  rw [oddG_linear_sum] at hb
  let K : ℝ := ((⌊A/D⌋₊+1)/2 : ℕ)
  change (H.card : ℝ) ≤ K*(A/2+1)-D*K^2/2 at hb
  have hquad : K*(A/2+1)-D*K^2/2 ≤ (A+2)^2/(8*D) := by
    apply (le_div_iff₀ (show 0 < 8*D by positivity)).mpr
    nlinarith only [sq_nonneg (A+2-2*D*K)]
  have hrem : (A+1)/(2*D) ≤ (A+1)/2 := by
    apply (div_le_iff₀ (show 0 < 2*D by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ A+1 by linarith)
    change (A+1)*1 ≤ (A+1)*D at hh
    nlinarith only [hh]
  have heq : (A+2)^2/(8*D) = A^2/(8*D)+(A+1)/(2*D) := by
    field_simp
    ring
  change (H.card : ℝ) ≤ A^2/(8*D)+A/2+1/2
  rw [heq] at hquad
  linarith

/-- Both parity choices are allowed when the coordinate parities match. -/
theorem matching_triangle_count (H : Finset (ℕ × ℕ)) (A C r : ℝ)
    (hA : 0 ≤ A) (hD : 1 ≤ C+r)
    (hH : ∀ t ∈ H, 0 < t.1 ∧ t.1%2=t.2%2 ∧
      C*t.1 ≤ t.2 ∧ (t.2 : ℝ)+r*t.1 ≤ A) :
    (H.card : ℝ) ≤ A^2/(4*(C+r))+A+1/2 := by
  let E := H.filter (fun t => t.1%2=0)
  let O := H.filter (fun t => ¬t.1%2=0)
  have hE : ∀ t ∈ E, 0 < t.1 ∧ t.1%2=0 ∧ t.2%2=0 ∧
      C*t.1 ≤ t.2 ∧ (t.2 : ℝ)+r*t.1 ≤ A := by
    intro t ht
    obtain ⟨ht,hpar⟩ := mem_filter.mp ht
    obtain ⟨hg,he,hl,hu⟩ := hH t ht
    exact ⟨hg,hpar,he.symm.trans hpar,hl,hu⟩
  have hO : ∀ t ∈ O, 0 < t.1 ∧ t.1%2=1 ∧ t.2%2=1 ∧
      C*t.1 ≤ t.2 ∧ (t.2 : ℝ)+r*t.1 ≤ A := by
    intro t ht
    obtain ⟨ht,hpar⟩ := mem_filter.mp ht
    obtain ⟨hg,he,hl,hu⟩ := hH t ht
    have hp : t.1%2=1 := by omega
    exact ⟨hg,hp,he.symm.trans hp,hl,hu⟩
  have hbE := even_triangle_count E A C r hA hD hE
  have hbO := odd_triangle_count O A C r hA hD hO
  have hc : E.card+O.card=H.card := card_filter_add_card_filter_not _
  have hcR : (E.card : ℝ)+O.card=H.card := by exact_mod_cast hc
  have heq : A^2/(4*(C+r))=2*(A^2/(8*(C+r))) := by
    have hne : C+r ≠ 0 := by linarith
    field_simp
    ring
  rw [heq]
  linarith

#print axioms interval_card_bound
#print axioms parity_interval_card_bound
#print axioms even_triangle_count
#print axioms odd_triangle_count
#print axioms matching_triangle_count
end Erdos773.ParityTriangleCount
