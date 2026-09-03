import Submission.EisensteinPrimeProducts
import Submission.Spec

/-! Exact quartic counts with last coordinate one. Such representations are
primitive, regardless of the common divisors of the other coordinates. -/
namespace Erdos322Research.QuarticUnitLastCount
noncomputable section
open Finset EisensteinIntegers EisensteinPrimeProducts
open scoped Classical
set_option Elab.async false

/-- Ordered quartic representations with the fourth coordinate equal to one. -/
def count (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 4 → Fin (n+1))).filter
    (fun a ↦ (∑ i, (a i : ℕ)^4)=n ∧ (a 3 : ℕ)=1)).card

theorem count_le_full (n : ℕ) : count n ≤ Erdos322.representationCount 4 n := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
  exact ha.1

/-- The last coordinate certifies primitivity. -/
theorem common_divisor_eq_one (a : Fin 4 → ℕ) (ha : a 3=1) (d : ℕ)
    (hd : ∀ i, d ∣ a i) : d=1 := by
  have h := hd 3
  rw [ha] at h
  exact Nat.dvd_one.mp h

def point (z : E) : Fin 4 → ℕ :=
  ![z.re.natAbs,z.im.natAbs,(z.re-z.im).natAbs,1]

lemma point_sum (z : E) (M : ℕ) (hz : z.norm=(M : ℤ)) :
    ∑ i, point z i^4=2*M^2+1 := by
  have he : (∑ i, (point z i : ℤ)^4)=2*z.norm^2+1 := by
    rw [Fin.sum_univ_four]
    change (z.re.natAbs : ℤ)^4+(z.im.natAbs : ℤ)^4+
      ((z.re-z.im).natAbs : ℤ)^4+1^4=2*z.norm^2+1
    simp only [Int.natCast_natAbs,Even.pow_abs (by decide : Even 4)]
    rw [EisensteinIntegers.norm_formula]
    ring
  rw [hz] at he
  exact_mod_cast he

private lemma signed_abs_injective :
    Function.Injective (fun z : ℤ ↦ (z.natAbs,decide (z<0))) := by
  intro a b h
  have hab := congrArg Prod.fst h
  have hs := decide_eq_decide.mp (congrArg Prod.snd h)
  have ha : |a|=|b| := by
    have hh := congrArg (fun n : ℕ ↦ (n : ℤ)) hab
    simpa only [Int.natCast_natAbs] using hh
  by_cases hneg : a<0
  · rw [abs_of_neg hneg,abs_of_neg (hs.mp hneg)] at ha
    omega
  · have hbn : ¬b<0 := fun hb ↦ hneg (hs.mpr hb)
    rw [abs_of_nonneg (by omega),abs_of_nonneg (by omega)] at ha
    exact ha

/-- Converting signed Eisenstein coordinates to absolute values costs at
most four, uniformly in the common norm and in the family size. -/
theorem family_count_bound {ι : Type*} [Fintype ι] (M : ℕ)
    (v : ι → E) (hv : Function.Injective v) (hnorm : ∀ a, (v a).norm=(M : ℤ)) :
    Fintype.card ι ≤ 4*count (2*M^2+1) := by
  let n := 2*M^2+1
  let w (a : ι) : Fin 4 → Fin (n+1) := fun i ↦ ⟨point (v a) i,by
    have hs := point_sum (v a) M (hnorm a)
    have hh := Finset.single_le_sum (f := fun j : Fin 4 ↦ point (v a) j^4)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hl : point (v a) i ≤ point (v a) i^4 := Nat.le_pow (by decide)
    change point (v a) i^4 ≤ ∑ j, point (v a) j^4 at hh
    omega⟩
  let enc (a : ι) := (w a,(decide ((v a).re<0),decide ((v a).im<0)))
  have hinj : Function.Injective enc := by
    intro a b h
    apply hv
    have hpt := congrArg Prod.fst h
    have hs := congrArg Prod.snd h
    apply QuadraticAlgebra.ext
    · have habs : (v a).re.natAbs=(v b).re.natAbs :=
        congrArg (fun x : Fin 4 → Fin (n+1) ↦ (x 0 : ℕ)) hpt
      have hsign : decide ((v a).re<0)=decide ((v b).re<0) :=
        congrArg (fun t : Bool × Bool ↦ t.1) hs
      exact signed_abs_injective (Prod.ext habs hsign)
    · have habs : (v a).im.natAbs=(v b).im.natAbs :=
        congrArg (fun x : Fin 4 → Fin (n+1) ↦ (x 1 : ℕ)) hpt
      have hsign : decide ((v a).im<0)=decide ((v b).im<0) :=
        congrArg (fun t : Bool × Bool ↦ t.2) hs
      exact signed_abs_injective (Prod.ext habs hsign)
  let T := (Finset.univ : Finset (Fin 4 → Fin (n+1))).filter
    (fun a ↦ (∑ i, (a i : ℕ)^4)=n ∧ (a 3 : ℕ)=1)
  have hc := Finset.card_le_card_of_injOn enc (s := Finset.univ)
    (t := T ×ˢ (Finset.univ : Finset (Bool × Bool))) (by
      intro a _
      apply Finset.mem_product.mpr
      refine ⟨?_,Finset.mem_univ _⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,point_sum (v a) M (hnorm a),?_⟩
      rfl) hinj.injOn
  simpa only [Finset.card_univ,Finset.card_product,Fintype.card_prod,Fintype.card_bool,
    show 2*2=4 by decide,mul_comm,T,n,count] using hc

/-- Split-prime choices give many primitive exact representations. -/
theorem prime_product_count (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime ∧ 3 ∣ p-1) :
    2^S.card ≤ 4*count (2*(∏ p ∈ S,p)^2+1) := by
  obtain ⟨v,hv,hnorm⟩ := exists_norm_family S hp
  simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe] using
    family_count_bound (∏ p ∈ S,p) v hv hnorm

end
end Erdos322Research.QuarticUnitLastCount
