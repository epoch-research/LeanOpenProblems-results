import Submission.StoppingTwoPrimeExample
import Submission.DivisorAssignment

/-! The two-prime stopping obstruction persists even if every active class
may be enlarged to an independently assigned nontrivial divisor modulus. -/
namespace Erdos7StoppingDivisorExample
open scoped BigOperators
open Erdos7Digits Erdos7AllDigits
open Erdos7StoppingDigitRestriction Erdos7StoppingTwoPrimeExample
open Erdos7DivisorAssignment
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4000

def projected (i : Fin 2) (T : (Fin 4 → Fin (primes i)) → Fin 4) (k : Fin 24) : ℕ :=
  ∏ j, primes j ^ eraseExponent i (T (digits i k)).val (exponents k) j

lemma projected_table : ∀ i : Fin 2, ∀ k : Fin 24, ∀ t : Fin 4,
    (∏ j, primes j ^ eraseExponent i t.val (exponents k) j) =
      if t.val < exponents k i then modulus k/primes i else modulus k := by
  decide +kernel

/-- Every divisor of a selected upper image has a lower prefix agreeing with
all but the last digit of the same central path. -/
lemma saturation_data : ∀ i : Fin 2, ∀ t : Fin 4, ∀ r : Fin (primes i), ∀ l : Fin 24,
    modulus l ∣ modulus (upper i t r)/primes i →
      exponents l i ≤ t.val ∧ Agree (exponents l i-1) (digits i l) (center i) := by
  unfold Agree
  decide +kernel

lemma quotient_data : ∀ i : Fin 2, ∀ t : Fin 4, ∀ r : Fin (primes i),
    0 < modulus (upper i t r)/primes i ∧
    modulus (upper i t r)/primes i < modulus (upper i t r) ∧
    modulus (upper i t r)/primes i ∣ modulus (upper i t r) := by
  decide +kernel

/-- No solver certificate is used: the obstruction is a finite saturated
set and the pigeonhole principle, for EVERY predictable position/value rule. -/
theorem no_divisor_assignment (i : Fin 2)
    (T : (Fin 4 → Fin (primes i)) → Fin 4)
    (V : (Fin 4 → Fin (primes i)) → Fin (primes i))
    (hT : Predictable T) (hV : PredictableValue T V) :
    ¬ ∃ f : Fin 24 → ℕ,
      (∀ k, active primes caps i T V (exponents k) (residue k) →
        1 < f k ∧ f k ∣ projected i T k) ∧
      ∀ k l, active primes caps i T V (exponents k) (residue k) →
        active primes caps i T V (exponents l) (residue l) → f k=f l → k=l := by
  classical
  rintro ⟨f,hf,hinj⟩
  let t := T (center i)
  let r := V (center i)
  let k := upper i t r
  let M := modulus k/primes i
  let R := M.divisors.erase 1
  let P (l : Fin 24) := active primes caps i T V (exponents l) (residue l)
  obtain ⟨hek,ha,hr,_,_⟩ := forcing_data i t r
  have htk : T (digits i k)=t := hT (center i) (digits i k) ha.symm
  have hvk : V (digits i k)=r := hV (center i) (digits i k) ha.symm
  have hk : P k := by
    right
    change digits i k (T (digits i k)) = V (digits i k)
    rw [htk,hvk]
    exact hr
  have hproj : projected i T k=M := by
    dsimp only [projected]
    rw [htk,projected_table,if_pos (by rw [hek]; omega)]
  obtain ⟨hM,hlt,hMd⟩ := quotient_data i t r
  change 0 < M at hM
  change M < modulus k at hlt
  change M ∣ modulus k at hMd
  have hmem {d : ℕ} (h1 : 1<d) (hd : d ∣ M) : d ∈ R :=
    Finset.mem_erase.mpr ⟨by omega,Nat.mem_divisors.mpr ⟨hd,hM.ne'⟩⟩
  have hbase : ∀ d ∈ R, ∃ l, P l ∧ modulus l=d ∧ f l ∈ R := by
    intro d hd
    have hd' := Finset.mem_erase.mp hd
    have hdM := (Nat.mem_divisors.mp hd'.2).1
    have hdp : 0 < d := Nat.pos_of_dvd_of_pos hdM hM
    have hd1 : 1 < d := by omega
    obtain ⟨l,hl⟩ := divisor_closed k d (hdM.trans hMd) hd1
    have hld : modulus l ∣ M := by simpa only [hl] using hdM
    obtain ⟨hle,hpre⟩ := saturation_data i t r l hld
    have hlong : exponents l i ≤ (T (digits i l)).val := by
      by_contra! hs
      have hpre' : Agree (T (digits i l)).val (digits i l) (center i) :=
        hpre.mono (by omega)
      have hh := congrArg Fin.val (hT (digits i l) (center i) hpre')
      change t.val = (T (digits i l)).val at hh
      omega
    have hlp : P l := Or.inl hlong
    have hpl : projected i T l=modulus l := by
      dsimp only [projected]
      rw [eraseExponent_eq_self i (T (digits i l)).val (exponents l) hlong]
      exact (arithmetic_data.2.2.2.2 l).symm
    have hfl := hf l hlp
    rw [hpl] at hfl
    exact ⟨l,hlp,hl,hmem hfl.1 (hfl.2.trans hld)⟩
  have hfk := hf k hk
  rw [hproj] at hfk
  have hkey : modulus k ∉ R := by
    intro hh
    have hd := (Nat.mem_divisors.mp (Finset.mem_erase.mp hh).2).1
    have hle := Nat.le_of_dvd hM hd
    omega
  exact saturated_obstruction R P modulus f hinj hbase k hk (hmem hfk.1 hfk.2) hkey

#print axioms projected_table
#print axioms saturation_data
#print axioms no_divisor_assignment
end Erdos7StoppingDivisorExample
