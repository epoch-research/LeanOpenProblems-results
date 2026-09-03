import Submission.Forest93ConcreteAvoidance
import Submission.Forest93ShapeArithmetic

/-! Chinese remainder and integer residue interpretation of the concrete boxes. -/
namespace Erdos7Forest93Concrete
open scoped BigOperators
open Erdos7Forest93Certificate Erdos7Forest93Shapes Erdos7Forest93ShapeArithmetic
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option Elab.async false

def coordSize : Fin 8 → ℕ := Fin.cases 9 (fun j => primes j.succ)
def coordValue : (j : Fin 8) → Coord j → ℕ := Fin.cases Fin.val (fun _ => Fin.val)
lemma coordSize_pos (j : Fin 8) : 0 < coordSize j := by
  induction j using Fin.cases with
  | zero => decide
  | succ j => exact (prime_properties.2 j.succ).1.pos
lemma coordValue_lt (j : Fin 8) (x : Coord j) : coordValue j x < coordSize j := by
  induction j using Fin.cases <;> exact x.isLt
lemma coordSize_eq : ∀ j,coordSize j = primes j^caps j := by decide +kernel
lemma coordSize_coprime : Pairwise (Function.onFun Nat.Coprime coordSize) := by
  unfold Pairwise Function.onFun
  decide +kernel

def residueFin (n : ℕ) (hn : 0 < n) (a : ℤ) : Fin n :=
  ⟨(a:ZMod n).val,by letI : NeZero n := ⟨ne_of_gt hn⟩; exact ZMod.val_lt _⟩
def arithResidue (a : ℤ) : Space := Fin.cases (residueFin 9 (by decide) a)
  (fun j => residueFin (primes j.succ) (prime_properties.2 j.succ).1.pos a)
lemma residueFin_val (n : ℕ) (hn : 0 < n) (a : ℤ) : ((residueFin n hn a).val:ℤ) = a % n := by
  letI : NeZero n := ⟨ne_of_gt hn⟩
  exact ZMod.val_intCast a
lemma residueFin_congr (n : ℕ) (hn : 0 < n) (a : ℤ) :
    a ≡ ((residueFin n hn a).val:ℤ) [ZMOD n] := by
  change a % n = _ % n
  rw [residueFin_val,Int.emod_emod]
lemma residueFin_mod (n d : ℕ) (hn : 0 < n) (hd : d ∣ n) (a : ℤ) :
    (((residueFin n hn a).val%d:ℕ):ℤ) = a%d := by
  rw [Int.natCast_mod,residueFin_val]
  exact Int.emod_emod_of_dvd a (by exact_mod_cast hd)
lemma residueFin_mod_zero (n d : ℕ) (hn : 0 < n) (hd : d ∣ n) (a : ℤ) :
    (residueFin n hn a).val%d = 0 ↔ (d:ℤ) ∣ a := by
  have hh := residueFin_mod n d hn hd a
  constructor
  · intro h
    rw [h,Nat.cast_zero] at hh
    exact Int.dvd_of_emod_eq_zero hh.symm
  · intro h
    rw [Int.emod_eq_zero_of_dvd h] at hh
    exact_mod_cast hh

lemma exists_crt (x : Space) : ∃ z : ℤ,∀ j,z ≡ (coordValue j (x j):ℤ) [ZMOD coordSize j] := by
  let z := Nat.chineseRemainderOfFinset (fun j => coordValue j (x j)) coordSize Finset.univ
    (fun j _ => ne_of_gt (coordSize_pos j)) (fun i _ j _ hij => coordSize_coprime hij)
  refine ⟨z.val,fun j => ?_⟩
  exact Int.natCast_modEq_iff.mpr (z.property j (Finset.mem_univ _))

lemma coord_residue_mod (n d : ℕ) (hn : 0 < n) (hd : d ∣ n)
    (x : Fin n) (a z : ℤ) (hx : z ≡ (x.val:ℤ) [ZMOD n]) (ha : z ≡ a [ZMOD d]) :
    x.val%d = (residueFin n hn a).val%d := by
  have hh := (hx.of_dvd (by exact_mod_cast hd)).symm.trans
    (ha.trans ((residueFin_congr n hn a).of_dvd (by exact_mod_cast hd)))
  exact Int.natCast_modEq_iff.mp hh
lemma coord_residue_eq (n : ℕ) (hn : 0 < n) (x : Fin n) (a z : ℤ)
    (hx : z ≡ (x.val:ℤ) [ZMOD n]) (ha : z ≡ a [ZMOD n]) :
    x = residueFin n hn a := by
  apply Fin.ext
  have hh := coord_residue_mod n n hn (dvd_refl _) x a z hx ha
  simpa only [Nat.mod_eq_of_lt x.isLt,Nat.mod_eq_of_lt (residueFin n hn a).isLt] using hh

lemma coverage_box (i : Index) (a z : ℤ) (x : Space)
    (hx : ∀ j,z ≡ (coordValue j (x j):ℤ) [ZMOD coordSize j])
    (ha : (modulus i:ℤ) ∣ z-a) : residueBox i (arithResidue a) x := by
  have he (j : Fin 8) : z ≡ a [ZMOD (primes j^exponent i j:ℕ)] := by
    apply Int.modEq_iff_dvd.mpr
    have hd : ((primes j^exponent i j:ℕ):ℤ) ∣ (modulus i:ℤ) := by
      exact_mod_cast exponent_pow_dvd i j
    simpa only [neg_sub] using dvd_neg.mpr (hd.trans ha)
  intro j
  induction j using Fin.cases with
  | zero =>
    change x 0 ∈ rootSection i (arithResidue a 0)
    by_cases h0 : exponent i 0 = 0
    · simp [rootSection,h0]
    · by_cases h1 : exponent i 0 = 1
      · simp only [rootSection,if_neg h0,if_pos h1,Finset.mem_filter,Finset.mem_univ,true_and]
        apply coord_residue_mod 9 3 (by decide) (by decide) (x 0) a z (hx 0)
        simpa only [h1,primes,Matrix.cons_val_zero,pow_one] using he 0
      · have h2 : exponent i 0 = 2 := by have := exponent_le i 0; change exponent i 0 ≤ 2 at this; omega
        simp only [rootSection,if_neg h0,if_neg h1,Finset.mem_singleton]
        apply coord_residue_eq 9 (by decide) (x 0) a z (hx 0)
        simpa only [h2,primes,Matrix.cons_val_zero,show (3:ℕ)^2 = 9 from rfl] using he 0
  | succ j =>
    change x j.succ ∈ (if exponent i j.succ = 0 then Finset.univ else {arithResidue a j.succ})
    split_ifs with h0
    · exact Finset.mem_univ _
    · rw [Finset.mem_singleton]
      have h1 : exponent i j.succ = 1 := by
        have hh := exponent_le i j.succ
        have hc : caps j.succ = 1 := by fin_cases j <;> rfl
        rw [hc] at hh
        omega
      apply coord_residue_eq (primes j.succ) (prime_properties.2 j.succ).1.pos (x j.succ) a z (hx j.succ)
      simpa only [h1,pow_one] using he j.succ

lemma coprime_not_prime_dvd (a : ℤ) (m p : ℕ) (hp : p.Prime)
    (hm : IsCoprime a (m:ℤ)) (hd : p ∣ m) : ¬(p:ℤ) ∣ a := by
  intro ha
  have hu := hm.isUnit_of_dvd' ha (by exact_mod_cast hd)
  have hh := Int.isUnit_iff_natAbs_eq.mp hu
  simp only [Int.natAbs_natCast] at hh
  exact hp.ne_one hh

lemma arithResidue_good (i : Index) (a : ℤ) (ha : IsCoprime a (modulus i:ℤ)) :
    good i (arithResidue a) := by
  constructor
  · intro h0 hz
    have hd : (3:ℤ) ∣ a := (residueFin_mod_zero 9 3 (by decide) (by decide) a).mp hz
    exact coprime_not_prime_dvd a (modulus i) 3 (by norm_num) ha
      (exponent_prime_dvd i 0 h0) hd
  · intro j hj hz
    have hv : (residueFin (primes j.succ) (prime_properties.2 j.succ).1.pos a).val = 0 :=
      congrArg Fin.val hz
    have hd : (primes j.succ:ℤ) ∣ a :=
      (residueFin_mod_zero _ _ (prime_properties.2 j.succ).1.pos (dvd_refl _) a).mp (by rw [hv]; simp)
    exact coprime_not_prime_dvd a (modulus i) (primes j.succ) (prime_properties.2 j.succ).1 ha
      (exponent_prime_dvd i j.succ hj) hd

lemma allowed_not_prime (b : Fin 9) (x : Space) (hx : ∀ j,x j ∈ allowed b j)
    (z : ℤ) (hz : ∀ j,z ≡ (coordValue j (x j):ℤ) [ZMOD coordSize j])
    (j : Fin 8) : ¬(primes j:ℤ) ∣ z := by
  intro hd
  induction j using Fin.cases with
  | zero =>
    have hx0 : (x 0).val%3 ≠ 0 := by
      have hh := hx 0
      change x 0 ∈ root b at hh
      exact (Finset.mem_filter.mp hh).2.1
    have hcon : z ≡ ((x 0).val:ℤ) [ZMOD 3] := (hz 0).of_dvd (by decide : (3:ℤ) ∣ 9)
    have hdiv : 3 ∣ (x 0).val := by exact_mod_cast hcon.dvd_iff.mp hd
    exact hx0 (Nat.mod_eq_zero_of_dvd hdiv)
  | succ j =>
    have hxj : x j.succ ≠ zeroLeaf j := (Finset.mem_erase.mp (hx j.succ)).1
    have hdiv : primes j.succ ∣ (x j.succ).val := by exact_mod_cast (hz j.succ).dvd_iff.mp hd
    have hval : (x j.succ).val = 0 := Nat.eq_zero_of_dvd_of_lt hdiv (x j.succ).isLt
    exact hxj (Fin.ext hval)

lemma allowed_not_nine (a : ℤ) (x : Space) (hx : ∀ j,x j ∈ allowed (arithResidue a 0) j)
    (z : ℤ) (hz : ∀ j,z ≡ (coordValue j (x j):ℤ) [ZMOD coordSize j]) : ¬(9:ℤ) ∣ z-a := by
  intro hd
  have hne : x 0 ≠ arithResidue a 0 := by
    have hh := hx 0
    change x 0 ∈ root (arithResidue a 0) at hh
    exact (Finset.mem_filter.mp hh).2.2
  apply hne
  apply coord_residue_eq 9 (by decide) (x 0) a z (hz 0)
  apply Int.modEq_iff_dvd.mpr
  simpa only [neg_sub] using dvd_neg.mpr hd

#print axioms coverage_box
#print axioms arithResidue_good
#print axioms allowed_not_prime
#print axioms allowed_not_nine
end Erdos7Forest93Concrete
