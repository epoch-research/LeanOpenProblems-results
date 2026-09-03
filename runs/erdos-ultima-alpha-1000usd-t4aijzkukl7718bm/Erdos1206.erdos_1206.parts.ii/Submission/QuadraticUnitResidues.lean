import Submission.QuadraticPrimeDivisibility
import Submission.PrimeBoxCRT

/-! Local unit densities for finite families of irreducible binary quadratics. -/
namespace Erdos1206.QuadraticUnitResidues
open Finset QuadraticLatticeLines QuadraticRootLattice QuadraticPrimeDivisibility
open scoped Classical
set_option maxHeartbeats 1000000

def evalMod (a b c : ℤ) {p : ℕ} (z : ZMod p × ZMod p) : ZMod p :=
  a*z.1^2+b*z.1*z.2+c*z.2^2

lemma zero_residue_card {a b c : ℤ} (hQ : Anisotropic a b c)
    (p : ℕ) [Fact p.Prime] :
    ((univ : Finset (ZMod p × ZMod p)).filter (fun z => evalMod a b c z=0)).card ≤
      (48*mass a b c+1)*p := by
  have hp : p.Prime := Fact.out
  let Z := (univ : Finset (ZMod p × ZMod p)).filter (fun z => evalMod a b c z=0)
  let lift (z : ZMod p × ZMod p) : Vec := ((z.1.val:ℤ),(z.2.val:ℤ))
  have hlift (z : ZMod p × ZMod p) :
      ((lift z).1:ZMod p)=z.1 ∧ ((lift z).2:ZMod p)=z.2 := by
    simp [lift]
  have hmap : ∀ z∈Z.erase 0, lift z∈points a b c p p := by
    intro z hz
    have hz0 := (mem_erase.mp hz).1
    have hze := (mem_filter.mp (mem_erase.mp hz).2).2
    apply mem_filter.mpr
    refine ⟨?_,?_,?_⟩
    · apply mem_box_iff.mpr
      dsimp [ht,lift]
      rw [abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
      exact max_le (by exact_mod_cast z.1.val_lt.le) (by exact_mod_cast z.2.val_lt.le)
    · intro he
      apply hz0
      have h₁ := congrArg (fun x : Vec => (x.1:ZMod p)) he
      have h₂ := congrArg (fun x : Vec => (x.2:ZMod p)) he
      exact Prod.ext (by simpa only [(hlift z).1,Prod.fst_zero,Int.cast_zero] using h₁)
        (by simpa only [(hlift z).2,Prod.snd_zero,Int.cast_zero] using h₂)
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simpa only [form,Int.cast_add,Int.cast_mul,Int.cast_pow,
        (hlift z).1,(hlift z).2,evalMod] using hze
  have hinj : Set.InjOn lift (Z.erase 0) := by
    intro x hx y hy he
    have h₁ := congrArg (fun z : Vec => (z.1:ZMod p)) he
    have h₂ := congrArg (fun z : Vec => (z.2:ZMod p)) he
    exact Prod.ext (by simpa only [(hlift x).1,(hlift y).1] using h₁)
      (by simpa only [(hlift x).2,(hlift y).2] using h₂)
  have hc := card_le_card_of_injOn lift hmap hinj
  have hbound := (Nat.mul_le_mul_left p hc).trans (prime_divisibility_bound hQ p p hp)
  have hsmall : (Z.erase 0).card ≤ 48*mass a b c*p := by
    apply Nat.le_of_mul_le_mul_left (c := p) _ hp.pos
    convert hbound using 1
    ring
  have hz : (0 : ZMod p × ZMod p)∈Z := by simp [Z,evalMod]
  have hcard := card_erase_add_one hz
  change Z.card ≤ (48*mass a b c+1)*p
  nlinarith [hp.one_le]

noncomputable def units (a b c : Fin 4 → ℤ) (p : ℕ) : Finset (ZMod p × ZMod p) :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    (univ : Finset (ZMod p × ZMod p)).filter (fun z => ∀ i, evalMod (a i) (b i) (c i) z ≠ 0)
  else ∅

def boundConstant (a b c : Fin 4 → ℤ) : ℕ := ∑i,(48*mass (a i) (b i) (c i)+1)

lemma mem_units {a b c : Fin 4 → ℤ} {p : ℕ} (hp : p.Prime) (z : ZMod p × ZMod p) :
    z∈units a b c p ↔ ∀ i, evalMod (a i) (b i) (c i) z ≠ 0 := by
  simp [units,hp]

/-- Local admissibility and summable prime reciprocals suffice to keep the
Euler-product factors uniformly away from zero. These are local estimates. -/
lemma density_bounds {a b c : Fin 4 → ℤ}
    (hQ : ∀ i, Anisotropic (a i) (b i) (c i)) {p : ℕ} (hp : p.Prime)
    (hex : ∃ z : ZMod p × ZMod p, ∀ i, evalMod (a i) (b i) (c i) z ≠ 0) :
    0 < PrimeBoxCRT.localDensity (units a b c) p ∧
      PrimeBoxCRT.localDensity (units a b c) p ≤ 1 ∧
      1-PrimeBoxCRT.localDensity (units a b c) p ≤ (boundConstant a b c:ℝ)/p := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Z (i : Fin 4) := (univ : Finset (ZMod p × ZMod p)).filter
    (fun z => evalMod (a i) (b i) (c i) z=0)
  let B := univ.biUnion Z
  have hbad : B.card ≤ boundConstant a b c*p := by
    calc
      B.card ≤ ∑i,(Z i).card := card_biUnion_le
      _ ≤ ∑i,(48*mass (a i) (b i) (c i)+1)*p :=
        sum_le_sum (fun i _ => zero_residue_card (hQ i) p)
      _ = boundConstant a b c*p := by simp only [boundConstant,sum_mul]
  have hpart : (units a b c p).card+B.card=p^2 := by
    have he : B=(univ : Finset (ZMod p × ZMod p)).filter
        (fun z => ¬ ∀ i, evalMod (a i) (b i) (c i) z ≠ 0) := by
      ext z
      simp only [B,Z,mem_biUnion,mem_univ,mem_filter,true_and,not_forall,not_not]
    rw [he]
    have hu : units a b c p=(univ : Finset (ZMod p × ZMod p)).filter
        (fun z => ∀ i, evalMod (a i) (b i) (c i) z ≠ 0) := by simp [units,hp]
    rw [hu,card_filter_add_card_filter_not]
    simp [pow_two]
  have hpos : 0 < (units a b c p).card := by
    obtain ⟨z,hz⟩ := hex
    exact card_pos.mpr ⟨z,(mem_units hp z).mpr hz⟩
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpartR : ((units a b c p).card:ℝ)+B.card=(p:ℝ)^2 := by exact_mod_cast hpart
  have hbadR : (B.card:ℝ) ≤ (boundConstant a b c:ℝ)*p := by exact_mod_cast hbad
  have hposR : (0:ℝ) < ((units a b c p).card:ℝ) := by exact_mod_cast hpos
  change 0 < ((units a b c p).card:ℝ)/(p:ℝ)^2 ∧ _
  refine ⟨div_pos hposR (sq_pos_of_pos hpR),?_,?_⟩
  · dsimp only [PrimeBoxCRT.localDensity]
    apply (div_le_one (sq_pos_of_pos hpR)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) B.card]
  · dsimp only [PrimeBoxCRT.localDensity]
    calc
      1-((units a b c p).card:ℝ)/(p:ℝ)^2 = (B.card:ℝ)/(p:ℝ)^2 := by
        apply (eq_div_iff (pow_ne_zero 2 hpR.ne')).mpr
        field_simp
        linarith
      _ ≤ ((boundConstant a b c:ℝ)*p)/(p:ℝ)^2 :=
        div_le_div_of_nonneg_right hbadR (sq_nonneg _)
      _ = (boundConstant a b c:ℝ)/p := by field_simp

#print axioms zero_residue_card
#print axioms density_bounds
end Erdos1206.QuadraticUnitResidues
