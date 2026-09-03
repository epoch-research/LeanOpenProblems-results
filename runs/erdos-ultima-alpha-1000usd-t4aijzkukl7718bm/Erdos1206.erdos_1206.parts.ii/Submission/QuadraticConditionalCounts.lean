import Submission.BoxDensityLimits
import Submission.QuadraticNaturalPrime
import Submission.QuadraticUnitResidues

/-! Fixed-prime conditional frequencies for quadratic parameter families. -/
namespace Erdos1206.QuadraticConditionalCounts
open Finset Filter QuadraticSquarefreeSieve QuadraticRootLattice QuadraticUnitResidues
  BoxDensityLimits PrimeBoxCRT
open scoped Classical
set_option maxHeartbeats 2000000

lemma evalMod_quad (a b c p : ℕ) (x : ℕ × ℕ) :
    evalMod c b a ((x.1:ZMod p),(x.2:ZMod p))=(quad a b c x.1 x.2:ZMod p) := by
  simp only [evalMod,quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Int.cast_natCast]
  ring

noncomputable def zeros (a b c p : ℕ) : Finset (ZMod p × ZMod p) :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    univ.filter (fun z => evalMod c b a z=0)
  else ∅

lemma mem_zeros_nat (a b c : ℕ) {p : ℕ} (hp : p.Prime) (x : ℕ × ℕ) :
    ((x.1:ZMod p),(x.2:ZMod p))∈zeros a b c p ↔ p∣quad a b c x.1 x.2 := by
  simp only [zeros,dif_pos hp,mem_filter,mem_univ,true_and,evalMod_quad]
  exact CharP.cast_eq_zero_iff (ZMod p) p _

lemma zeros_density_bound (a b c : ℕ) (hQ : Anisotropic c b a) {p : ℕ} (hp : p.Prime) :
    0 ≤ localDensity (zeros a b c) p ∧
      localDensity (zeros a b c) p ≤ (48*mass c b a+1:ℝ)/p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hh := zero_residue_card hQ p
  have hhR : ((zeros a b c p).card:ℝ) ≤ (48*(mass c b a:ℝ)+1)*p := by
    simpa only [zeros,dif_pos hp] using (show
      (((univ : Finset (ZMod p × ZMod p)).filter (fun z => evalMod (c:ℤ) b a z=0)).card:ℝ) ≤
        (48*(mass c b a:ℝ)+1)*p from by exact_mod_cast hh)
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  refine ⟨by dsimp [localDensity]; positivity,?_⟩
  dsimp only [localDensity]
  apply (div_le_iff₀ (sq_pos_of_pos hpR)).mpr
  have he : (48*(mass c b a:ℝ)+1)/(p:ℝ)*(p:ℝ)^2=(48*(mass c b a:ℝ)+1)*p := by field_simp
  rwa [he]

def Head (a b c : Fin 4 → ℕ) (S : Finset ℕ) (x : ℕ × ℕ) : Prop :=
  ∀ p∈S, ((x.1:ZMod p),(x.2:ZMod p))∈units
    (fun i => (c i:ℤ)) (fun i => (b i:ℤ)) (fun i => (a i:ℤ)) p

noncomputable def headDensity (a b c : Fin 4 → ℕ) (S : Finset ℕ) : ℝ :=
  ∏p∈S,localDensity (units (fun i => (c i:ℤ)) (fun i => (b i:ℤ)) (fun i => (a i:ℤ))) p

lemma mem_head (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime) (x : ℕ × ℕ) :
    Head a b c S x ↔ ∀ p∈S, ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2 := by
  unfold Head
  apply forall₂_congr
  intro p hp
  rw [mem_units (hS p hp)]
  apply forall_congr'
  intro i
  rw [evalMod_quad]
  exact not_congr (CharP.cast_eq_zero_iff (ZMod p) p _)

lemma head_density_pos (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (hQ : ∀ i, Anisotropic (c i) (b i) (a i))
    (hloc : ∀ p, p.Prime → ∃ x : ℕ × ℕ,
      ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2) :
    0 < headDensity a b c S := by
  apply prod_pos
  intro p hp
  obtain ⟨x,hx⟩ := hloc p (hS p hp)
  apply (density_bounds hQ (hS p hp) _).1
  refine ⟨((x.1:ZMod p),(x.2:ZMod p)),fun i => ?_⟩
  rw [evalMod_quad]
  exact fun hz => hx i ((CharP.cast_eq_zero_iff (ZMod p) p _).mp hz)

lemma head_tendsto (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime) :
    Tendsto (fun N : ℕ => ((positiveBox N (Head a b c S)).card:ℝ)/(N:ℝ)^2)
      atTop (nhds (headDensity a b c S)) := joint_positive_density S hS _

noncomputable def counts (a b c : Fin 4 → ℕ) (S : Finset ℕ) (i : Fin 4) (N p : ℕ) : Finset (ℕ × ℕ) :=
  positiveBox N (fun x => Head a b c S x ∧ p∣quad (a i) (b i) (c i) x.1 x.2)

lemma mem_counts (a b c : Fin 4 → ℕ) (S : Finset ℕ) (i : Fin 4) (N p : ℕ) (x : ℕ × ℕ) :
    x∈counts a b c S i N p ↔ x∈range N ×ˢ range N ∧ 0 < x.1 ∧
      Head a b c S x ∧ p∣quad (a i) (b i) (c i) x.1 x.2 := by
  simp only [counts,positiveBox,mem_filter]

lemma counts_empty (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (i : Fin 4) (N : ℕ) {p : ℕ} (hp : p∈S) : counts a b c S i N p=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_,_,hx,hdiv⟩ := (mem_counts _ _ _ _ _ _ _ _).mp hx
  exact (mem_head a b c S hS x).mp hx p hp i hdiv

lemma conditional_tendsto (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (i : Fin 4) {p : ℕ} (hp : p.Prime) (hpS : p∉S) :
    Tendsto (fun N : ℕ => ((counts a b c S i N p).card:ℝ)/(N:ℝ)^2)
      atTop (nhds (headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) p)) := by
  let U := units (fun i => (c i:ℤ)) (fun i => (b i:ℤ)) (fun i => (a i:ℤ))
  let G (q : ℕ) := if q=p then zeros (a i) (b i) (c i) q else U q
  have hrest (x : ℕ × ℕ) :
      (∀ q∈S, ((x.1:ZMod q),(x.2:ZMod q))∈G q) ↔ Head a b c S x := by
    apply forall₂_congr
    intro q hq
    have hqp : q≠p := fun he => hpS (he ▸ hq)
    simp only [G,if_neg hqp]
    rfl
  have hcond (x : ℕ × ℕ) :
      (∀ q∈insert p S, ((x.1:ZMod q),(x.2:ZMod q))∈G q) ↔
        Head a b c S x ∧ p∣quad (a i) (b i) (c i) x.1 x.2 := by
    rw [forall_mem_insert,hrest]
    simp only [G,if_pos rfl,mem_zeros_nat _ _ _ hp,and_comm]
  have hcount (N : ℕ) : positiveBox N (fun x =>
      ∀ q∈insert p S, ((x.1:ZMod q),(x.2:ZMod q))∈G q)=counts a b c S i N p := by
    ext x
    simp only [positiveBox,counts,mem_filter,hcond]
  have hprod : (∏q∈insert p S,localDensity G q)=
      headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) p := by
    rw [prod_insert hpS]
    have hpG : localDensity G p=localDensity (zeros (a i) (b i) (c i)) p := by
      simp only [localDensity,G,if_pos rfl]
    have hSG : (∏q∈S,localDensity G q)=headDensity a b c S := by
      apply prod_congr rfl
      intro q hq
      have hqp : q≠p := fun he => hpS (he ▸ hq)
      simp only [localDensity,G,if_neg hqp,U]
    rw [hpG,hSG,mul_comm]
  have hh := joint_positive_density (insert p S)
    (fun q hq => (mem_insert.mp hq).elim (fun he => he ▸ hp) (hS q)) G
  simpa only [hcount,hprod] using hh

lemma counts_bound (a b c : Fin 4 → ℕ) (S : Finset ℕ) (i : Fin 4)
    (hQ : Anisotropic (c i) (b i) (a i)) (N p : ℕ) (hp : p.Prime) :
    ((counts a b c S i N p).card:ℝ)/(N:ℝ)^2 ≤ (48*mass (c i) (b i) (a i):ℝ)/p := by
  have hcard : (counts a b c S i N p).card ≤
      (QuadraticPrimeDivisibility.points (c i) (b i) (a i) N p).card := by
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
    have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
    have hh := (Nat.mul_le_mul_left p hcard).trans (QuadraticPrimeDivisibility.prime_divisibility_bound hQ N p hp)
    have hhR : (p:ℝ)*(counts a b c S i N p).card ≤ 48*mass (c i) (b i) (a i)*(N:ℝ)^2 := by
      exact_mod_cast hh
    apply (div_le_iff₀ (sq_pos_of_pos hNR)).mpr
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hpR).mpr (by nlinarith only [hhR])

#print axioms conditional_tendsto
#print axioms counts_bound
end Erdos1206.QuadraticConditionalCounts
