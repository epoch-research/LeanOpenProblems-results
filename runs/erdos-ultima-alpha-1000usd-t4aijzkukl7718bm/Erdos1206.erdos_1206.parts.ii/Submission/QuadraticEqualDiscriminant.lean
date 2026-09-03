import Submission.QuadraticConditionalCounts
import Submission.SquarefreeConicFamily

/-! Equal discriminants give equal local zero frequencies. In the explicit
conic the two ordered pairs have matching prime frequencies; this is a local
cancellation identity, not an estimate for infinite score moments. -/
namespace Erdos1206.QuadraticEqualDiscriminant
open Finset QuadraticConditionalCounts PrimeBoxCRT
open scoped Classical
set_option maxHeartbeats 2000000

private def Q {K : Type*} [CommRing K] (a b c : K) (z : K × K) : K :=
  a*z.1^2+b*z.1*z.2+c*z.2^2

private def shear {K : Type*} [Field K] (a b a' b' : K) (z : K × K) : K × K :=
  ((2*a*z.1+(b-b')*z.2)/(2*a'),z.2)

private lemma shear_form {K : Type*} [Field K] (a b c a' b' c' : K)
    (h2 : (2:K)≠0) (ha' : a'≠0) (hD : b^2-4*a*c=b'^2-4*a'*c') (z : K × K) :
    a'*Q a' b' c' (shear a b a' b' z)=a*Q a b c z := by
  dsimp [shear,Q]
  field_simp
  linear_combination z.2^2*hD

private lemma shear_injective {K : Type*} [Field K] (a b a' b' : K)
    (h2 : (2:K)≠0) (ha : a≠0) (ha' : a'≠0) :
    Function.Injective (shear a b a' b') := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2' : x.2=y.2 := by simpa only [shear] using congrArg Prod.snd hxy
  dsimp [shear] at h1
  rw [div_eq_div_iff (mul_ne_zero h2 ha') (mul_ne_zero h2 ha')] at h1
  have hm : (2*a')*(2*a)*(x.1-y.1)=0 := by
    rw [h2'] at h1
    linear_combination h1
  have hx := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left
    (mul_ne_zero (mul_ne_zero h2 ha') (mul_ne_zero h2 ha)))
  exact Prod.ext hx h2'

private lemma zero_card_le {K : Type*} [Field K] [Fintype K]
    (a b c a' b' c' : K) (h2 : (2:K)≠0) (ha : a≠0) (ha' : a'≠0)
    (hD : b^2-4*a*c=b'^2-4*a'*c') :
    ((univ : Finset (K × K)).filter (fun z => Q a b c z=0)).card ≤
      ((univ : Finset (K × K)).filter (fun z => Q a' b' c' z=0)).card := by
  apply card_le_card_of_injOn (shear a b a' b') _ (shear_injective a b a' b' h2 ha ha').injOn
  intro z hz
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have hh := shear_form a b c a' b' c' h2 ha' hD z
  rw [(mem_filter.mp hz).2,mul_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_left ha'

lemma zeros_card_eq {a b c a' b' c' p : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hc : (c:ZMod p)≠0) (hc' : (c':ZMod p)≠0)
    (hD : (b:ℤ)^2-4*c*a=(b':ℤ)^2-4*c'*a') :
    (zeros a b c p).card=(zeros a' b' c' p).card := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2:ZMod p)≠0 := by
    intro hz
    have hd : p∣2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using hz)
    have := Nat.le_of_dvd (by decide : 0<2) hd
    omega
  have hD' : (b:ZMod p)^2-4*c*a=(b':ZMod p)^2-4*c'*a' := by
    have hh := congrArg (fun z : ℤ => (z:ZMod p)) hD
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using hh
  simp only [zeros,dif_pos hp,QuadraticUnitResidues.evalMod,Int.cast_natCast]
  change ((univ : Finset (ZMod p × ZMod p)).filter (fun z => Q (c:ZMod p) b a z=0)).card =
    ((univ : Finset (ZMod p × ZMod p)).filter (fun z => Q (c':ZMod p) b' a' z=0)).card
  convert Nat.le_antisymm
    (zero_card_le (c:ZMod p) b a c' b' a' h2 hc hc' hD')
    (zero_card_le (c':ZMod p) b' a' c b a h2 hc' hc hD'.symm) using 1 <;>
    congr 1 <;> ext z <;> simp only [mem_filter,mem_univ,true_and]

lemma localDensity_eq {a b c a' b' c' p : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hc : (c:ZMod p)≠0) (hc' : (c':ZMod p)≠0)
    (hD : (b:ℤ)^2-4*c*a=(b':ℤ)^2-4*c'*a') :
    localDensity (zeros a b c) p=localDensity (zeros a' b' c') p := by
  simp only [localDensity,zeros_card_eq hp hp2 hc hc' hD]

open SquarefreeConicFamily in
lemma paired_local_densities {p : ℕ} (hp : p.Prime) (hpbig : 1000000<p) :
    localDensity (zeros (a 0) (b 0) (c 0)) p=localDensity (zeros (a 1) (b 1) (c 1)) p ∧
    localDensity (zeros (a 2) (b 2) (c 2)) p=localDensity (zeros (a 3) (b 3) (c 3)) p := by
  have hci (i : Fin 4) : (c i:ZMod p)≠0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff (ZMod p) p (c i)).mp hz
    have hpos : 0<c i := by fin_cases i <;> norm_num [c]
    have hle : c i≤1000000 := by fin_cases i <;> norm_num [c]
    have := Nat.le_of_dvd hpos hd
    omega
  constructor
  · exact localDensity_eq hp (by omega) (hci 0) (hci 1) (by decide +kernel)
  · exact localDensity_eq hp (by omega) (hci 2) (hci 3) (by decide +kernel)

/-- The coefficient vector for the inner-minus-outer contrast. -/
def sign (i : Fin 4) : ℝ := ![-1,1,1,-1] i

lemma abs_sign (i : Fin 4) : |sign i|=1 := by fin_cases i <;> norm_num [sign]

open SquarefreeConicFamily in
lemma local_cancellation {p : ℕ} (hp : p.Prime) (hpbig : 1000000<p) :
    (∑i,sign i*localDensity (zeros (a i) (b i) (c i)) p)=0 := by
  obtain ⟨h01,h23⟩ := paired_local_densities hp hpbig
  have he (v : Fin 4 → ℝ) : (∑i,sign i*v i)=v 1+v 2-v 0-v 3 := by
    simp [Fin.sum_univ_succ,sign]
    ring
  rw [he]
  rw [h01,h23]
  ring

#print axioms paired_local_densities
#print axioms local_cancellation
end Erdos1206.QuadraticEqualDiscriminant
