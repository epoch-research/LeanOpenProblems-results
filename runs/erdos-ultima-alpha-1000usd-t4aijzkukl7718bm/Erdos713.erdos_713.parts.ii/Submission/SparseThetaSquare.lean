import FormalConjecturesUtil
import Submission.ConditionalThetaWeighted

/-! A weaker, still UNPROVED local target for the apex-theta route.
SquareVanishing is an explicit hypothesis, not an axiom or a theorem.
Its conditional degree consequence does not settle Erdős 713. -/
open Finset SimpleGraph
namespace Erdos713SparseThetaSquare
open Erdos713ThetaGram Erdos713ThetaCross Erdos713GlobalLight Erdos713GlobalTheta
open Erdos713ConditionalThetaWeighted
set_option maxHeartbeats 2000000

/-- With k columns and column degrees at most K*k, o(k^2) rows and
light pairs should force o(k^2) incidences. No proof of this predicate
is supplied here, even for fixed K. -/
def SquareVanishing (K : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → (∀ b, Nat.card {a // R a b} ≤ K*Nat.card B) →
      (Nat.card A : ℝ) ≤ δ*(Nat.card B : ℝ)^2 →
      (lightCount R : ℝ) ≤ δ*(Nat.card B : ℝ)^2 →
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤ ε*(Nat.card B : ℝ)^2

/-- The earlier capped weighted estimate would imply this qualitative
target. The converse is not asserted. -/
lemma squareVanishing_of_weighted {K : ℕ} {C : ℝ} (hC : 0 < C)
    (h : CappedWeighted (K : ℝ) C) : SquareVanishing K := by
  intro ε hε
  let r : ℝ := min 1 (ε/(4*C*((K : ℝ)+1)))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrε : r ≤ ε/(4*C*((K : ℝ)+1)) := min_le_right _ _
  have hprod : 4*C*((K : ℝ)+1)*r ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*C*((K : ℝ)+1))).mp hrε
    nlinarith only [hh]
  have hr2 : r^2 ≤ r := by nlinarith only [hr,hr1]
  have hsmall : C*(r^2+(K : ℝ)*r) ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left hr2 hC.le
    nlinarith only [hh,hprod,hε]
  refine ⟨r^2,pow_pos hr 2,?_⟩
  intro A B instA instB R hFree hCap hm ht
  have hb := h A B R (K*Nat.card B) hFree hCap (by norm_cast)
  have hs : Real.sqrt (lightCount R) ≤ r*(Nat.card B : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [ht]
  have hcoef : 0 ≤ (K : ℝ)*(Nat.card B : ℝ) := by positivity
  calc
    _ ≤ C*((Nat.card A : ℝ)+(K*Nat.card B : ℕ)*Real.sqrt (lightCount R)) := hb
    _ ≤ C*(r^2*(Nat.card B : ℝ)^2+((K : ℝ)*Nat.card B)*(r*Nat.card B)) := by
      push_cast
      exact mul_le_mul_of_nonneg_left (add_le_add hm
        (mul_le_mul_of_nonneg_left hs hcoef)) hC.le
    _ = (C*(r^2+(K : ℝ)*r))*(Nat.card B : ℝ)^2 := by ring
    _ ≤ ε*(Nat.card B : ℝ)^2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)

/-- A fixed vanishing modulus already gives a uniform square-degree
bound for balanced hosts satisfying the explicit link exclusions.
No regularization or extremal-rate transfer is assumed in this lemma. -/
theorem degree_square_of_vanishing {K : ℕ} (hV : SquareVanishing K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ), 0 < n →
      ∀ R : Fin n → Fin n → Prop,
        (∀ a, ¬ HasTheta (link R a)) →
        (∀ a, d ≤ Nat.card {b // R a b}) →
        (∀ b, d ≤ Nat.card {a // R a b}) →
        (∀ a, Nat.card {b // R a b} ≤ K*d) →
        (∀ b, Nat.card {a // R a b} ≤ K*d) →
        (d : ℝ)^2 ≤ C*n := by
  classical
  let ε : ℝ := 1/(8*((K : ℝ)+1)^2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δ,hδ,hLocal⟩ := hV ε hε
  refine ⟨3/δ+2,by positivity,?_⟩
  intro n d hn R hFree hrows hcols hRowMax hColMax
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  by_cases hd : 2 ≤ d
  · by_contra hnot
    have hbad : (3/δ+2)*(n : ℝ) < (d : ℝ)^2 := lt_of_not_ge hnot
    have hthreshold : 3*(n : ℝ) ≤ δ*(d : ℝ)^2 := by
      have hh := mul_lt_mul_of_pos_left hbad hδ
      have he : δ*(3/δ+2) = 3+2*δ := by field_simp
      have hnon := mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) n)
      nlinarith only [hh,he,hnon]
    haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
    obtain ⟨a,ha⟩ := exists_row_with_few_light_pairs R 3
    simp only [Fintype.card_fin] at ha
    have ht : (lightPairs R 3 a).card ≤ 3*n := by
      have hh : n*(lightPairs R 3 a).card ≤ n*(3*n) := by nlinarith only [ha]
      exact Nat.le_of_mul_le_mul_left hh hn
    let A := {x : Fin n // x ≠ a}
    let B := {b : Fin n // R a b}
    have hm : Nat.card A ≤ n := by
      simpa only [A,Nat.card_fin] using Nat.card_le_card_of_injective
        (fun x : A => x.val) Subtype.val_injective
    have hdk : d ≤ Nat.card B := hrows a
    have hkd : Nat.card B ≤ K*d := hRowMax a
    have hdkR : (d : ℝ) ≤ Nat.card B := by exact_mod_cast hdk
    have hkp : (d : ℝ)^2 ≤ (Nat.card B : ℝ)^2 := by nlinarith only [hdkR,hdn]
    have hkpδ := mul_le_mul_of_nonneg_left hkp hδ.le
    have hmR : (Nat.card A : ℝ) ≤ δ*(Nat.card B : ℝ)^2 := by
      have hmn : (Nat.card A : ℝ) ≤ n := by exact_mod_cast hm
      nlinarith only [hmn,hthreshold,hkpδ,hnR]
    have htR : (lightCount (link R a) : ℝ) ≤ δ*(Nat.card B : ℝ)^2 := by
      have ht' : (lightCount (link R a) : ℝ) ≤ 3*(n : ℝ) := by
        rw [link_lightCount]
        exact_mod_cast ht
      exact ht'.trans (hthreshold.trans hkpδ)
    have hCap (b : B) : Nat.card {x : A // link R a x b} ≤ K*Nat.card B := by
      have hh := link_column_add_one R a b
      have hb := hColMax b.val
      have hmul := Nat.mul_le_mul_left K hdk
      calc
        _ ≤ Nat.card {x : A // link R a x b}+1 := Nat.le_succ _
        _ = Nat.card {x : Fin n // R x b.val} := hh
        _ ≤ K*d := hb
        _ ≤ K*Nat.card B := hmul
    have hE := hLocal A B (link R a) (hFree a) hCap hmR htR
    let E := Nat.card {p : A × B // link R a p.1 p.2}
    change (E : ℝ) ≤ ε*(Nat.card B : ℝ)^2 at hE
    have hLow : (d : ℝ)*((d : ℝ)-1) ≤ E := by
      have hh := link_incidence_lower R a d (hrows a) hcols
      have hh' : d*(d-1) ≤ E := hh
      have hhR : ((d*(d-1) : ℕ) : ℝ) ≤ (E : ℝ) := by exact_mod_cast hh'
      simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ d by omega),Nat.cast_one] using hhR
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hLow2 : (d : ℝ)^2 ≤ 2*(E : ℝ) := by nlinarith only [hLow,hdR]
    have hden : 0 < 8*((K : ℝ)+1)^2 := by positivity
    have hEden : (8*((K : ℝ)+1)^2)*(E : ℝ) ≤ (Nat.card B : ℝ)^2 := by
      calc
        _ ≤ (8*((K : ℝ)+1)^2)*(ε*(Nat.card B : ℝ)^2) :=
          mul_le_mul_of_nonneg_left hE hden.le
        _ = _ := by dsimp [ε]; field_simp
    have hkdR : (Nat.card B : ℝ) ≤ (K : ℝ)*d := by exact_mod_cast hkd
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hkpow : (Nat.card B : ℝ)^2 ≤ ((K : ℝ)*d)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hkdR 2
    have hKpow : (K : ℝ)^2 ≤ ((K : ℝ)+1)^2 := by nlinarith only [hK]
    have hKmul := mul_le_mul_of_nonneg_right hKpow (sq_nonneg (d : ℝ))
    have hE8mul : ((K : ℝ)+1)^2*(8*(E : ℝ)) ≤ ((K : ℝ)+1)^2*(d : ℝ)^2 := by
      nlinarith only [hEden,hkpow,hKmul]
    have hE8 : 8*(E : ℝ) ≤ (d : ℝ)^2 :=
      (mul_le_mul_iff_right₀ (by positivity : 0 < ((K : ℝ)+1)^2)).mp (by simpa only [mul_comm] using hE8mul)
    nlinarith only [hLow2,hE8,hdR]
  · have hdR : (d : ℝ) ≤ 1 := by exact_mod_cast (show d ≤ 1 by omega)
    have hC : (2 : ℝ) ≤ 3/δ+2 := by linarith [div_pos (by norm_num : (0 : ℝ) < 3) hδ]
    have hh := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [hdR,hdn,hnR,hh]

#print axioms squareVanishing_of_weighted
#print axioms degree_square_of_vanishing
end Erdos713SparseThetaSquare
