import Submission.QuadraticSemiprimeDivisibility
import Submission.QuadraticConditionalCounts
import Submission.CoprimeBoxCRT

/-! Conditional frequencies at composite moduli, and uniform domination
for moduli with at most two prime factors counted with multiplicity. -/
namespace Erdos1206.QuadraticCompositeCounts
open Finset Filter QuadraticSquarefreeSieve QuadraticRootLattice QuadraticUnitResidues
  BoxDensityLimits PrimeBoxCRT QuadraticConditionalCounts QuadraticSemiprimeDivisibility
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def zeros (a b c d : ℕ) : Finset (ZMod d × ZMod d) :=
  if hd : d≠0 then
    letI : NeZero d := ⟨hd⟩
    univ.filter (fun z => evalMod c b a z=0)
  else ∅

lemma mem_zeros_nat (a b c : ℕ) {d : ℕ} (hd : d≠0) (x : ℕ × ℕ) :
    ((x.1:ZMod d),(x.2:ZMod d))∈zeros a b c d ↔ d∣quad a b c x.1 x.2 := by
  simp only [zeros,dif_pos hd,mem_filter,mem_univ,true_and,evalMod_quad]
  exact CharP.cast_eq_zero_iff (ZMod d) d _

lemma joint_positive_density (S : Finset ℕ) (hpos : ∀ d∈S, 0<d)
    (hcop : (↑S : Set ℕ).Pairwise Nat.Coprime)
    (G : (d : ℕ) → Finset (ZMod d × ZMod d)) :
    Tendsto (fun N : ℕ => ((positiveBox N (fun x =>
      ∀ d∈S, ((x.1:ZMod d),(x.2:ZMod d))∈G d)).card:ℝ)/(N:ℝ)^2)
      atTop (nhds (∏d∈S,localDensity G d)) := by
  let D : ℝ := ∏d∈S,(d:ℝ)
  apply normalized_limit _ _ (2*D+1) (D^2)
  intro N
  have hh := trimmed_discrepancy N (fun x => ∀ d∈S, ((x.1:ZMod d),(x.2:ZMod d))∈G d)
    (∏d∈S,localDensity G d) (2*(N:ℝ)*D+D^2) (by
      have heq : box N (fun x => ∀ d∈S, ((x.1:ZMod d),(x.2:ZMod d))∈G d) =
          (range N ×ˢ range N).filter (fun x => ∀ d∈S, ((x.1:ZMod d),(x.2:ZMod d))∈G d) := by
        ext x
        simp only [BoxDensityLimits.box,mem_filter]
      rw [heq,mul_comm (∏d∈S,localDensity G d)]
      exact CoprimeBoxCRT.joint_box_discrepancy id S hpos hcop G N)
  convert hh using 1; ring

def Avoids (S : Finset ℕ) (d : ℕ) : Prop := ∀ p∈S, ¬p∣d

lemma counts_empty_of_not_avoids (a b c : Fin 4 → ℕ) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime) (i : Fin 4) (N d : ℕ) (hd : ¬Avoids S d) :
    counts a b c S i N d=∅ := by
  classical
  change ¬∀ p∈S, ¬p∣d at hd
  push_neg at hd
  obtain ⟨p,hp,hpd⟩ := hd
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_,_,hx,hdiv⟩ := (mem_counts _ _ _ _ _ _ _ _).mp hx
  exact (mem_head a b c S hS x).mp hx p hp i (hpd.trans hdiv)

lemma conditional_tendsto (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (i : Fin 4) {d : ℕ} (hd : 0<d) (havoid : Avoids S d) :
    Tendsto (fun N : ℕ => ((counts a b c S i N d).card:ℝ)/(N:ℝ)^2)
      atTop (nhds (headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) d)) := by
  have hdS : d∉S := fun hh => havoid d hh (dvd_refl d)
  let U := units (fun i => (c i:ℤ)) (fun i => (b i:ℤ)) (fun i => (a i:ℤ))
  let G (q : ℕ) := if q=d then zeros (a i) (b i) (c i) q else U q
  have hrest (x : ℕ × ℕ) :
      (∀ q∈S, ((x.1:ZMod q),(x.2:ZMod q))∈G q) ↔ Head a b c S x := by
    apply forall₂_congr
    intro q hq
    have hqd : q≠d := fun he => hdS (he ▸ hq)
    simp only [G,if_neg hqd]
    rfl
  have hcond (x : ℕ × ℕ) :
      (∀ q∈insert d S, ((x.1:ZMod q),(x.2:ZMod q))∈G q) ↔
        Head a b c S x ∧ d∣quad (a i) (b i) (c i) x.1 x.2 := by
    rw [forall_mem_insert,hrest]
    simp only [G,if_pos rfl,mem_zeros_nat _ _ _ hd.ne',and_comm]
  have hcount (N : ℕ) : positiveBox N (fun x =>
      ∀ q∈insert d S, ((x.1:ZMod q),(x.2:ZMod q))∈G q)=counts a b c S i N d := by
    ext x
    simp only [positiveBox,counts,mem_filter,hcond]
  have hprod : (∏q∈insert d S,localDensity G q)=
      headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) d := by
    rw [prod_insert hdS]
    have hdG : localDensity G d=localDensity (zeros (a i) (b i) (c i)) d := by
      simp only [localDensity,G,if_pos rfl]
    have hSG : (∏q∈S,localDensity G q)=headDensity a b c S := by
      apply prod_congr rfl
      intro q hq
      have hqd : q≠d := fun he => hdS (he ▸ hq)
      simp only [localDensity,G,if_neg hqd,U]
    rw [hdG,hSG,mul_comm]
  have hcop : (↑(insert d S) : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hpq
    have hp' : p=d ∨ p∈S := mem_insert.mp hp
    have hq' : q=d ∨ q∈S := mem_insert.mp hq
    rcases hp' with hpd | hpS
    · subst p
      rcases hq' with hqd | hqS
      · exact (hpq hqd.symm).elim
      · exact ((hS q hqS).coprime_iff_not_dvd.mpr (havoid q hqS)).symm
    · rcases hq' with hqd | hqS
      · subst q
        exact (hS p hpS).coprime_iff_not_dvd.mpr (havoid p hpS)
      · exact (Nat.coprime_primes (hS p hpS) (hS q hqS)).mpr hpq
  have hh := joint_positive_density (insert d S)
    (fun q hq => (mem_insert.mp hq).elim (fun he => he ▸ hd) (fun h => (hS q h).pos)) hcop G
  simpa only [hcount,hprod] using hh

lemma counts_bound (a b c : Fin 4 → ℕ) (S : Finset ℕ) (i : Fin 4)
    (hQ : Anisotropic (c i) (b i) (a i))
    (hD : (b i:ℤ)^2-4*(c i)*(a i)≠0) (N d : ℕ) (hd : LowComplexity d) :
    ((counts a b c S i N d).card:ℝ)/(N:ℝ)^2 ≤ (constant (c i) (b i) (a i):ℝ)/d := by
  have hcard : (counts a b c S i N d).card ≤
      (QuadraticPrimeDivisibility.points (c i) (b i) (a i) N d).card := by
    apply card_le_card_of_injOn QuadraticNaturalPrime.lift _ QuadraticNaturalPrime.lift_injective.injOn
    intro x hx
    obtain ⟨hxbox,hxpos,_,hdiv⟩ := (mem_counts _ _ _ _ _ _ _ _).mp hx
    apply mem_filter.mpr
    refine ⟨QuadraticNaturalPrime.lift_mem_box hxbox,?_,?_⟩
    · intro he
      have hh : x.1=0 := Int.ofNat.inj (congrArg Prod.fst he)
      omega
    · rw [QuadraticNaturalPrime.form_lift]
      exact_mod_cast hdiv
  by_cases hN : N=0
  · simp only [hN,Nat.cast_zero,zero_pow (by decide : 2≠0),div_zero]
    positivity
  · have hNR : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hdR : (0:ℝ) < d := by exact_mod_cast lt_trans Nat.zero_lt_one hd.one_lt
    have hh := (Nat.mul_le_mul_left d hcard).trans (low_complexity_bound hQ hD N d hd)
    have hhR : (d:ℝ)*(counts a b c S i N d).card ≤ constant (c i) (b i) (a i)*(N:ℝ)^2 := by
      exact_mod_cast hh
    apply (div_le_iff₀ (sq_pos_of_pos hNR)).mpr
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hdR).mpr (by nlinarith only [hhR])

lemma zeros_density_bound (a b c : ℕ) (hQ : Anisotropic c b a)
    (hD : (b:ℤ)^2-4*c*a≠0) {d : ℕ} (hd : LowComplexity d) :
    0 ≤ localDensity (zeros a b c) d ∧
      localDensity (zeros a b c) d ≤ (constant c b a:ℝ)/d := by
  refine ⟨by dsimp [localDensity]; positivity,?_⟩
  have ht := conditional_tendsto (fun _ => a) (fun _ => b) (fun _ => c) ∅
    (by simp) 0 (lt_trans Nat.zero_lt_one hd.one_lt) (by simp [Avoids])
  simp only [headDensity,prod_empty,one_mul] at ht
  exact le_of_tendsto ht (Filter.Eventually.of_forall (fun N =>
    counts_bound (fun _ => a) (fun _ => b) (fun _ => c) ∅ 0 hQ hD N d hd))

#print axioms conditional_tendsto
#print axioms zeros_density_bound
end Erdos1206.QuadraticCompositeCounts
