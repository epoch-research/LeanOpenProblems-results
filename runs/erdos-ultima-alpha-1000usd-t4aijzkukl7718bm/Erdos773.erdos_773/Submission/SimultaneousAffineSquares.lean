import Submission.SimultaneousDifferenceSelection
import Submission.DivisorBound

/-!
Near-linear root sets with simultaneously bounded difference multiplicity for
polynomially many affine-square shifts. Multiplicity one is not claimed.
-/
namespace Erdos773.SimultaneousAffineSquares
open Finset Filter
open SimultaneousDifferenceSelection
set_option maxHeartbeats 1000000

/-- The quadratic obtained by removing the constant and common factor from
`(q*n+r)^2`. -/
def quadratic (q r n : ℕ) : ℕ := q*n^2 + 2*r*n

lemma quadratic_strictMono {q : ℕ} (hq : 0 < q) (r : ℕ) :
    StrictMono (quadratic q r) := by
  intro a b hab
  have hs := Nat.pow_lt_pow_left hab (by decide : (2 : ℕ) ≠ 0)
  have hm := Nat.mul_lt_mul_of_pos_left hs hq
  dsimp [quadratic]
  nlinarith

lemma quadratic_factor {q r a b D : ℕ} (hab : a < b)
    (he : quadratic q r b = quadratic q r a + D) :
    D = (b-a)*(q*(a+b)+2*r) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hab.le
  simp only [Nat.add_sub_cancel_left]
  dsimp [quadratic] at he
  nlinarith only [he]

private def root {N : ℕ} (a : Fin N) : ℕ := a.val+1
private def indexed (N q r : ℕ) (a : Fin N) : ℕ := quadratic q r (root a)

private lemma root_injective (N : ℕ) : Function.Injective (@root N) := by
  intro a b he
  apply Fin.ext
  dsimp [root] at he
  omega

private lemma indexed_injective (N q r : ℕ) (hq : 0 < q) :
    Function.Injective (indexed N q r) :=
  (quadratic_strictMono hq r).injective.comp (root_injective N)

private lemma reps_divisor_bound (N q r D : ℕ) (hq : 0 < q) (hD : 0 < D) :
    (reps (indexed N q r) D).card ≤ D.divisors.card := by
  apply card_le_card_of_injOn (fun ab => root ab.2 - root ab.1)
  · intro ab hab
    obtain ⟨hlt, he⟩ := (mem_filter.mp hab).2
    have hh : root ab.1 < root ab.2 := by simpa [root] using hlt
    exact Nat.mem_divisors.mpr ⟨⟨q*(root ab.1+root ab.2)+2*r,
      quadratic_factor hh he⟩, hD.ne'⟩
  · intro ab hab cd hcd heq
    obtain ⟨hlt, he⟩ := (mem_filter.mp hab).2
    obtain ⟨hlt', he'⟩ := (mem_filter.mp hcd).2
    have hh : root ab.1 < root ab.2 := by simpa [root] using hlt
    have hh' : root cd.1 < root cd.2 := by simpa [root] using hlt'
    have hfac := quadratic_factor hh he
    have hfac' := quadratic_factor hh' he'
    dsimp at heq
    rw [← heq] at hfac'
    have hsum : root ab.1+root ab.2 = root cd.1+root cd.2 := by
      have hf := mul_left_cancel₀ (Nat.sub_pos_of_lt hh).ne' (hfac.symm.trans hfac')
      exact mul_left_cancel₀ hq.ne' (Nat.add_right_cancel hf)
    apply Prod.ext <;> apply root_injective N <;> omega

private def shifts (N k : ℕ) : Finset (ℕ × ℕ) := Icc 1 (N^k) ×ˢ Icc 0 (N^k)
private def rangeBound (N k : ℕ) : ℕ := N^k*(N^2+2*N)

private lemma range_bound (N k : ℕ) {j : ℕ × ℕ} (hj : j ∈ shifts N k)
    (a : Fin N) : indexed N j.1 j.2 a ≤ rangeBound N k := by
  obtain ⟨hj1, hj2⟩ := mem_product.mp hj
  obtain ⟨_, hq⟩ := mem_Icc.mp hj1
  obtain ⟨_, hr⟩ := mem_Icc.mp hj2
  have ha : root a ≤ N := by dsimp [root]; omega
  have hsq := Nat.pow_le_pow_left ha 2
  have h1 := Nat.mul_le_mul hq hsq
  have h2 := Nat.mul_le_mul hr ha
  dsimp [indexed, quadratic, rangeBound]
  nlinarith only [h1,h2]

private lemma range_polynomial {N k : ℕ} (hN : 2 ≤ N) :
    rangeBound N k ≤ N^(k+3) := by
  have hpoly : N^2+2*N ≤ N^3 := by
    have h1 : 2*N ≤ N^2 := by nlinarith
    have h2 := Nat.mul_le_mul_right (N^2) hN
    nlinarith only [h1,h2]
  dsimp [rangeBound]
  rw [pow_add]
  exact Nat.mul_le_mul_left _ hpoly

private lemma family_polynomial {N k : ℕ} (hN : 2 ≤ N) :
    (shifts N k).card * rangeBound N k ≤ N^(3*k+4) := by
  have hQ : 1 ≤ N^k := Nat.one_le_pow k N (by omega)
  have hcnt : (shifts N k).card ≤ N^(2*k+1) := by
    have hc : (shifts N k).card = N^k*(N^k+1) := by simp [shifts]
    rw [hc]
    calc
      _ ≤ N^k*(2*N^k) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ N^k*(N*N^k) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hN)
      _ = _ := by rw [pow_add, pow_mul]; ring
  calc
    _ ≤ N^(2*k+1)*N^(k+3) := Nat.mul_le_mul hcnt (range_polynomial hN)
    _ = _ := by rw [← pow_add]; congr 1; omega

private lemma eventually_reps (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ shifts N k, ∀ D ∈ Icc 1 (rangeBound N k),
      ((reps (indexed N j.1 j.2) D).card : ℝ) ≤ (N : ℝ)^(ε/4) := by
  let δ : ℝ := (ε/8)/(k+3)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC, hdiv⟩ := divisor_card_subpower δ hδ
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(ε/8)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < ε/8)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, tendsto_atTop.mp ht C] with N hN hCN
  intro j hj D hD
  obtain ⟨hD0,hDR⟩ := mem_Icc.mp hD
  have hq : 0 < j.1 := (mem_Icc.mp (mem_product.mp hj).1).1
  have hDN : (D : ℝ) ≤ (N : ℝ)^(k+3) := by
    exact_mod_cast hDR.trans (range_polynomial hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (D.divisors.card : ℝ) := by exact_mod_cast reps_divisor_bound N j.1 j.2 D hq hD0
    _ ≤ C*(D : ℝ)^δ := hdiv D
    _ ≤ (N : ℝ)^(ε/8)*((N : ℝ)^(k+3))^δ :=
      mul_le_mul hCN (Real.rpow_le_rpow (Nat.cast_nonneg _) hDN hδ.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
    _ = (N : ℝ)^(ε/4) := by
      rw [← Real.rpow_natCast_mul hNpos.le, ← Real.rpow_add hNpos]
      congr 1
      dsimp [δ]
      push_cast
      field_simp
      ring

/-- Positive-difference representations for the normalized quadratic on a root set. -/
def quadraticReps (A : Finset ℕ) (q r D : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun ab => ab.1 < ab.2 ∧
    quadratic q r ab.2 = quadratic q r ab.1 + D)

private lemma image_selection {N : ℕ} (B : Finset (Fin N)) (q r D : ℕ) :
    (quadraticReps (B.image root) q r D).card ≤
      ((reps (indexed N q r) D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card := by
  have he : quadraticReps (B.image root) q r D =
      ((reps (indexed N q r) D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).image
        (fun ab => (root ab.1, root ab.2)) := by
    ext ab
    constructor
    · intro hab
      obtain ⟨hab, hlt, he⟩ := mem_filter.mp hab
      obtain ⟨ha,hb⟩ := mem_product.mp hab
      obtain ⟨a,ha,hea⟩ := mem_image.mp ha
      obtain ⟨b,hb,heb⟩ := mem_image.mp hb
      refine mem_image.mpr ⟨(a,b), ?_, Prod.ext hea heb⟩
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, ha, hb⟩
      · rw [← hea, ← heb] at hlt
        simpa [root] using hlt
      · simpa only [indexed, hea, heb] using he
    · intro hab
      obtain ⟨cd,hcd,rfl⟩ := mem_image.mp hab
      obtain ⟨hcd,hc,hd⟩ := mem_filter.mp hcd
      obtain ⟨hlt,he⟩ := (mem_filter.mp hcd).2
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_image.mpr ⟨cd.1,hc,rfl⟩,
        mem_image.mpr ⟨cd.2,hd,rfl⟩⟩, ?_, he⟩
      simpa [root] using hlt
  rw [he]
  exact card_image_le

/-- A single near-linear set controls all normalized affine squares of
polynomially bounded coefficients. The capacity depends on k and ε. -/
theorem near_linear_normalized (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℕ, ∀ᶠ N : ℕ in atTop, ∃ A ⊆ Icc 1 N,
      (N : ℝ)^(1-ε) ≤ A.card ∧
      ∀ q ∈ Icc 1 (N^k), ∀ r ∈ Icc 0 (N^k), ∀ D : ℕ, 0 < D →
        (quadraticReps A q r D).card ≤ g := by
  let m : ℕ := 3*k+4
  obtain ⟨g,hg⟩ := exists_nat_gt (4*(m : ℝ)/ε)
  have hg' : 4*(m : ℝ) < ε*g := by
    have hh := (div_lt_iff₀ hε).mp hg
    nlinarith
  let ρ : ℝ := ε/4*(g+1)-((m : ℝ)-1)
  have hρ : 0 < ρ := by dsimp [ρ]; nlinarith
  have ht (r : ℝ) (hr : 0 < r) :
      Tendsto (fun N : ℕ => (N : ℝ)^(-r)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2) (ht ρ hρ)
  have hslack := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)
    (ht (ε/2) (by positivity))
  refine ⟨g, ?_⟩
  filter_upwards [eventually_reps k ε hε, hsmall, hslack, eventually_ge_atTop 2]
    with N hrep hsmall hslack hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  let p : ℝ := (N : ℝ)^(-(ε/2))
  let K : ℝ := (N : ℝ)^(ε/4)
  let S : ℝ := (N : ℝ)^(1-ε/2)
  have hp : 0 ≤ p := Real.rpow_nonneg hNpos.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hS : 0 ≤ S := Real.rpow_nonneg hNpos.le _
  obtain ⟨B,hB,hcard⟩ := SimultaneousDifferenceSelection.finite_selection
    (shifts N k) (fun j => indexed N j.1 j.2) (rangeBound N k) g
    (fun j hj => indexed_injective N j.1 j.2 (mem_Icc.mp (mem_product.mp hj).1).1)
    (fun _ hj => range_bound N k hj) p K hp hp1 hrep
  have hfamily : ((shifts N k).card : ℝ) * rangeBound N k ≤ (N : ℝ)^m := by
    exact_mod_cast family_polynomial (k := k) hN
  have hcostle := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfamily (pow_nonneg (show 0 ≤ K by dsimp [K]; positivity) (g+1)))
    (pow_nonneg hp (g+2))
  have hPN : p*N = S := by
    dsimp [p,S]
    calc
      _ = (N : ℝ)^(-(ε/2))*(N : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring
  have hcost : (N : ℝ)^m*K^(g+1)*p^(g+2) = S*(N : ℝ)^(-ρ) := by
    dsimp [K,p,S,ρ]
    rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_mul_natCast hNpos.le,
      ← Real.rpow_natCast (N : ℝ) m]
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have htarget : (N : ℝ)^(1-ε) = S*(N : ℝ)^(-(ε/2)) := by
    dsimp [S]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have herror := mul_le_mul_of_nonneg_left hsmall hS
  have htargetle := mul_le_mul_of_nonneg_left hslack hS
  rw [hPN] at hcard
  rw [hcost] at hcostle
  refine ⟨B.image root, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a,ha,rfl⟩ := mem_image.mp ha
    apply mem_Icc.mpr
    dsimp [root]
    omega
  · rw [card_image_of_injective B (root_injective N), htarget]
    nlinarith only [hcard,hcostle,herror,htargetle]
  · intro q hq r hr D hD
    exact (image_selection B q r D).trans (hB (q,r) (mem_product.mpr ⟨hq,hr⟩) D hD)

/-- Positive square-difference representations after the affine map n ↦ q*n+r. -/
def affineReps (A : Finset ℕ) (q r D : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun ab => ab.1 < ab.2 ∧ (q*ab.2+r)^2 = (q*ab.1+r)^2+D)

lemma affineReps_bound {A : Finset ℕ} {q r g : ℕ} (hq : 0 < q)
    (hA : ∀ E : ℕ, 0 < E → (quadraticReps A q r E).card ≤ g)
    (D : ℕ) (_hD : 0 < D) : (affineReps A q r D).card ≤ g := by
  by_cases hn : (affineReps A q r D).Nonempty
  · obtain ⟨ab,hab⟩ := hn
    obtain ⟨_,hlt,he⟩ := mem_filter.mp hab
    have hltq := quadratic_strictMono hq r hlt
    let E := quadratic q r ab.2-quadratic q r ab.1
    have hE : 0 < E := Nat.sub_pos_of_lt hltq
    have hEq : quadratic q r ab.2 = quadratic q r ab.1+E := by
      dsimp [E]
      omega
    have hDE : D = q*E := by
      dsimp [quadratic] at hEq
      nlinarith only [he, congrArg (q*·) hEq]
    have hsub : affineReps A q r D ⊆ quadraticReps A q r E := by
      intro cd hcd
      obtain ⟨hcd,hlt,he⟩ := mem_filter.mp hcd
      apply mem_filter.mpr
      refine ⟨hcd,hlt,?_⟩
      apply Nat.eq_of_mul_eq_mul_left hq
      dsimp [quadratic]
      nlinarith only [he,hDE]
    exact (card_le_card hsub).trans (hA E hE)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

/-- One near-linear root set simultaneously has bounded positive-difference
multiplicity for all polynomially many affine-square shifts. This is weaker
than Sidon: the theorem does not assert g = 1. -/
theorem near_linear_affine (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℕ, ∀ᶠ N : ℕ in atTop, ∃ A ⊆ Icc 1 N,
      (N : ℝ)^(1-ε) ≤ A.card ∧
      ∀ q ∈ Icc 1 (N^k), ∀ r ∈ Icc 0 (N^k), ∀ D : ℕ, 0 < D →
        (affineReps A q r D).card ≤ g := by
  obtain ⟨g,hg⟩ := near_linear_normalized k ε hε
  refine ⟨g, ?_⟩
  filter_upwards [hg] with N hN
  obtain ⟨A,hA,hcard,hdiff⟩ := hN
  refine ⟨A,hA,hcard,?_⟩
  intro q hq r hr D hD
  exact affineReps_bound (mem_Icc.mp hq).1 (hdiff q hq r hr) D hD

#print axioms quadratic_strictMono
#print axioms quadratic_factor
#print axioms near_linear_normalized
#print axioms affineReps_bound
#print axioms near_linear_affine
end Erdos773.SimultaneousAffineSquares
