import Submission.FlatParallelLocal

/-! Necessary local conditions when exactly one body diagonal is allowed to vary.
These results are not a nonexistence theorem for this family or for general
planar integral-distance configurations. -/
set_option synthInstance.maxSize 10000

namespace Erdos213.FlatParallelVaryBody
open FlatParallelLocal (F SqResidue square_residue)
local instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- Twice the edge/face lengths, the variable body length, and the denominator. -/
def equations {R : Type*} [CommRing R] (j : Fin 11 → R) : Fin 8 → R :=
  let A := (j 0)^2
  let B := (j 1)^2
  let C := (j 2)^2
  let X := (j 9)^2
  let Z := (j 10)^2
  let d := X-61268*Z
  let e := X-86700*Z
  let f := X-93300*Z
  ![A+B+C-X-241268*Z,
    (j 3)^2-(A+B+d), (j 4)^2-(A+B-d),
    (j 5)^2-(A+C+e), (j 6)^2-(A+C-e),
    (j 7)^2-(B+C+f), (j 8)^2-(B+C-f),
    4*A*B*C+d*e*f-A*f^2-B*e^2-C*d^2]

def boundaryPolynomial {R : Type*} [CommRing R] (X Z : R) : R :=
  (X-62500*Z)*(X-86436*Z)*(X-93636*Z)*(X-722500*Z)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma local_affine_test (A B X : F)
    (ha : SqResidue A) (hb : SqResidue B) (hx : SqResidue X) (_hz : SqResidue (1 : F))
    (hc : SqResidue (X+6*(1 : F)-A-B))
    (habp : SqResidue (A+B+(X-12*(1 : F)))) (habm : SqResidue (A+B-(X-12*(1 : F))))
    (hacp : SqResidue (A+(X+6*(1 : F)-A-B)+(X-3*(1 : F))))
    (hacm : SqResidue (A+(X+6*(1 : F)-A-B)-(X-3*(1 : F))))
    (hbcp : SqResidue (B+(X+6*(1 : F)-A-B)+(X-10*(1 : F))))
    (hbcm : SqResidue (B+(X+6*(1 : F)-A-B)-(X-10*(1 : F))))
    (hd : 4*A*B*(X+6*(1 : F)-A-B)+(X-12*(1 : F))*(X-3*(1 : F))*(X-10*(1 : F))-
      A*(X-10*(1 : F))^2-B*(X-3*(1 : F))^2-(X+6*(1 : F)-A-B)*(X-12*(1 : F))^2=0) :
    (X-9*(1 : F))*(X-5*(1 : F))*(X-4*(1 : F))*(X-6*(1 : F))=0 ∧ ((1 : F)=0 → A=0 ∧ B=0 ∧ X=0) := by
  revert A B X
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma local_boundary_test (A B X : F)
    (ha : SqResidue A) (hb : SqResidue B) (hx : SqResidue X) (_hz : SqResidue (0 : F))
    (hc : SqResidue (X+6*(0 : F)-A-B))
    (habp : SqResidue (A+B+(X-12*(0 : F)))) (habm : SqResidue (A+B-(X-12*(0 : F))))
    (hacp : SqResidue (A+(X+6*(0 : F)-A-B)+(X-3*(0 : F))))
    (hacm : SqResidue (A+(X+6*(0 : F)-A-B)-(X-3*(0 : F))))
    (hbcp : SqResidue (B+(X+6*(0 : F)-A-B)+(X-10*(0 : F))))
    (hbcm : SqResidue (B+(X+6*(0 : F)-A-B)-(X-10*(0 : F))))
    (hd : 4*A*B*(X+6*(0 : F)-A-B)+(X-12*(0 : F))*(X-3*(0 : F))*(X-10*(0 : F))-
      A*(X-10*(0 : F))^2-B*(X-3*(0 : F))^2-(X+6*(0 : F)-A-B)*(X-12*(0 : F))^2=0) :
    (X-9*(0 : F))*(X-5*(0 : F))*(X-4*(0 : F))*(X-6*(0 : F))=0 ∧ ((0 : F)=0 → A=0 ∧ B=0 ∧ X=0) := by
  revert A B X
  decide +kernel

lemma residue_div (a b : F) (ha : SqResidue a) (hb : SqResidue b) : SqResidue (a/b) := by
  revert a b
  decide +kernel

lemma local_test (A B X Z : F)
    (ha : SqResidue A) (hb : SqResidue B) (hx : SqResidue X) (hz : SqResidue Z)
    (hc : SqResidue (X+6*Z-A-B))
    (habp : SqResidue (A+B+(X-12*Z))) (habm : SqResidue (A+B-(X-12*Z)))
    (hacp : SqResidue (A+(X+6*Z-A-B)+(X-3*Z)))
    (hacm : SqResidue (A+(X+6*Z-A-B)-(X-3*Z)))
    (hbcp : SqResidue (B+(X+6*Z-A-B)+(X-10*Z)))
    (hbcm : SqResidue (B+(X+6*Z-A-B)-(X-10*Z)))
    (hd : 4*A*B*(X+6*Z-A-B)+(X-12*Z)*(X-3*Z)*(X-10*Z)-
      A*(X-10*Z)^2-B*(X-3*Z)^2-(X+6*Z-A-B)*(X-12*Z)^2=0) :
    (X-9*Z)*(X-5*Z)*(X-4*Z)*(X-6*Z)=0 ∧ (Z=0 → A=0 ∧ B=0 ∧ X=0) := by
  by_cases hz0 : Z=0
  · subst Z
    exact local_boundary_test A B X ha hb hx hz hc habp habm hacp hacm hbcp hbcm hd
  have hA := residue_div A Z ha hz
  have hB := residue_div B Z hb hz
  have hX := residue_div X Z hx hz
  have hc' : SqResidue ((X/Z)+6-(A/Z)-(B/Z)) := by
    convert residue_div (X+6*Z-A-B) Z hc hz using 1
    field_simp
  have habp' : SqResidue ((A/Z)+(B/Z)+((X/Z)-12)) := by
    convert residue_div (A+B+(X-12*Z)) Z habp hz using 1
    field_simp
  have habm' : SqResidue ((A/Z)+(B/Z)-((X/Z)-12)) := by
    convert residue_div (A+B-(X-12*Z)) Z habm hz using 1
    field_simp
  have hacp' : SqResidue ((A/Z)+((X/Z)+6-(A/Z)-(B/Z))+((X/Z)-3)) := by
    convert residue_div (A+(X+6*Z-A-B)+(X-3*Z)) Z hacp hz using 1
    field_simp
  have hacm' : SqResidue ((A/Z)+((X/Z)+6-(A/Z)-(B/Z))-((X/Z)-3)) := by
    convert residue_div (A+(X+6*Z-A-B)-(X-3*Z)) Z hacm hz using 1
    field_simp
  have hbcp' : SqResidue ((B/Z)+((X/Z)+6-(A/Z)-(B/Z))+((X/Z)-10)) := by
    convert residue_div (B+(X+6*Z-A-B)+(X-10*Z)) Z hbcp hz using 1
    field_simp
  have hbcm' : SqResidue ((B/Z)+((X/Z)+6-(A/Z)-(B/Z))-((X/Z)-10)) := by
    convert residue_div (B+(X+6*Z-A-B)-(X-10*Z)) Z hbcm hz using 1
    field_simp
  have hd' : 4*(A/Z)*(B/Z)*(X/Z+6-A/Z-B/Z)+(X/Z-12)*(X/Z-3)*(X/Z-10)-
      (A/Z)*(X/Z-10)^2-(B/Z)*(X/Z-3)^2-(X/Z+6-A/Z-B/Z)*(X/Z-12)^2=0 := by
    field_simp
    linear_combination hd
  have hh := local_affine_test (A/Z) (B/Z) (X/Z) hA hB hX
    (by decide +kernel) (by simpa using hc') (by simpa using habp')
    (by simpa using habm') (by simpa using hacp') (by simpa using hacm')
    (by simpa using hbcp') (by simpa using hbcm') (by simpa using hd')
  constructor
  · have hp := hh.1
    have he : (X-9*Z)*(X-5*Z)*(X-4*Z)*(X-6*Z) =
        Z^4*((X/Z-9*1)*(X/Z-5*1)*(X/Z-4*1)*(X/Z-6*1)) := by
      field_simp
    rw [he,hp]
    ring
  · exact fun h => (hz0 h).elim

lemma equations_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (j : Fin 11 → R) :
    equations (fun i => f (j i)) = fun i => f (equations j i) := by
  ext i
  fin_cases i <;> simp [equations, map_ofNat]

lemma local_conditions (j : Fin 11 → F) (h : equations j=0) :
    boundaryPolynomial ((j 9)^2) ((j 10)^2)=0 ∧ (j 10=0 → j=0) := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  have h7 := congrFun h 7
  dsimp [equations] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [show (241268 : F)=6 by decide +kernel] at h0
  rw [show (61268 : F)=12 by decide +kernel] at h1 h2 h7
  rw [show (86700 : F)=3 by decide +kernel] at h3 h4 h7
  rw [show (93300 : F)=10 by decide +kernel] at h5 h6 h7
  have hc : (j 2)^2=(j 9)^2+6*(j 10)^2-(j 0)^2-(j 1)^2 := by linear_combination h0
  rw [hc] at h3 h4 h5 h6 h7
  have habp : (j 0)^2+(j 1)^2+((j 9)^2-12*(j 10)^2)=(j 3)^2 := by linear_combination -h1
  have habm : (j 0)^2+(j 1)^2-((j 9)^2-12*(j 10)^2)=(j 4)^2 := by linear_combination -h2
  have hacp : (j 0)^2+((j 9)^2+6*(j 10)^2-(j 0)^2-(j 1)^2)+((j 9)^2-3*(j 10)^2)=(j 5)^2 := by linear_combination -h3
  have hacm : (j 0)^2+((j 9)^2+6*(j 10)^2-(j 0)^2-(j 1)^2)-((j 9)^2-3*(j 10)^2)=(j 6)^2 := by linear_combination -h4
  have hbcp : (j 1)^2+((j 9)^2+6*(j 10)^2-(j 0)^2-(j 1)^2)+((j 9)^2-10*(j 10)^2)=(j 7)^2 := by linear_combination -h5
  have hbcm : (j 1)^2+((j 9)^2+6*(j 10)^2-(j 0)^2-(j 1)^2)-((j 9)^2-10*(j 10)^2)=(j 8)^2 := by linear_combination -h6
  have hh := local_test ((j 0)^2) ((j 1)^2) ((j 9)^2) ((j 10)^2)
    (square_residue _) (square_residue _) (square_residue _) (square_residue _)
    (by rw [← hc]; exact square_residue _)
    (by rw [habp]; exact square_residue _) (by rw [habm]; exact square_residue _)
    (by rw [hacp]; exact square_residue _) (by rw [hacm]; exact square_residue _)
    (by rw [hbcp]; exact square_residue _) (by rw [hbcm]; exact square_residue _) h7
  constructor
  · unfold boundaryPolynomial
    rw [show (62500 : F)=9 by decide +kernel,
        show (86436 : F)=5 by decide +kernel,
        show (93636 : F)=4 by decide +kernel,
        show (722500 : F)=6 by decide +kernel]
    exact hh.1
  · intro hz
    obtain ⟨ha,hb,hx⟩ := hh.2 (by simp [hz])
    have hA : j 0=0 := sq_eq_zero_iff.mp ha
    have hB : j 1=0 := sq_eq_zero_iff.mp hb
    have hX : j 9=0 := sq_eq_zero_iff.mp hx
    have hC : j 2=0 := by rw [hA,hB,hX,hz] at hc; simpa using hc
    have hD : j 3=0 := by rw [hA,hB,hX,hz] at h1; simpa using h1
    have hE : j 4=0 := by rw [hA,hB,hX,hz] at h2; simpa using h2
    have hF : j 5=0 := by rw [hA,hB,hX,hz] at h3; simpa using h3
    have hG : j 6=0 := by rw [hA,hB,hX,hz] at h4; simpa using h4
    have hH : j 7=0 := by rw [hA,hB,hX,hz] at h5; simpa using h5
    have hI : j 8=0 := by rw [hA,hB,hX,hz] at h6; simpa using h6
    ext i
    fin_cases i <;> simp [hA,hB,hC,hD,hE,hF,hG,hH,hI,hX,hz]

lemma integral_conditions (j : Fin 11 → ℤ) (h : equations j=0) :
    (19 : ℤ) ∣ boundaryPolynomial ((j 9)^2) ((j 10)^2) ∧
    ((19 : ℤ) ∣ j 10 → ∀ i, (19 : ℤ) ∣ j i) := by
  have hc : equations (fun i => (j i : F))=0 := by
    change equations (fun i => (Int.castRingHom F) (j i))=0
    rw [equations_map,h]
    rfl
  have hh := local_conditions _ hc
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 19).mp
    simpa [boundaryPolynomial] using hh.1
  · intro hz i
    have he := hh.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd (j 10) 19).mpr hz)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (j i) 19).mp (congrFun he i)

lemma equations_scale {R : Type*} [CommRing R] (r : R) (j : Fin 11 → R) :
    equations (fun i => r*j i) = fun i => r^(if i=7 then 6 else 2)*equations j i := by
  ext i
  fin_cases i <;> dsimp [equations] <;> ring

/-- Every rational solution with denominator coordinate 1 admits an integral
model whose denominator is prime to 19. This is not an existence assertion. -/
lemma rational_integral_model (j : Fin 11 → ℚ) (hj : equations j=0) (hj1 : j 10=1) :
    ∃ k : Fin 11 → ℤ, equations k=0 ∧ ¬ (19 : ℤ) ∣ k 10 ∧
      ∀ i, j i=(k i : ℚ)/(k 10 : ℚ) := by
  obtain ⟨b,hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) j
  change ∀ i, ∃ k : ℤ, (k : ℚ)=(b : ℤ) • j i at hb
  choose k hk using hb
  have he : (fun i => (k i : ℚ))=fun i => ((b : ℤ) : ℚ)*j i := by
    ext i
    simpa only [zsmul_eq_mul] using hk i
  have hc : equations (fun i => (k i : ℚ))=0 := by
    rw [he,equations_scale,hj]
    ext i
    simp
  have hi : equations k=0 := by
    change equations (fun i => (Int.castRingHom ℚ) (k i))=0 at hc
    rw [equations_map] at hc
    ext i
    have hh := congrFun hc i
    change ((equations k i : ℤ) : ℚ)=0 at hh
    exact_mod_cast hh
  have hb0 : (b : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hbQ : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hk10 : k 10=(b : ℤ) := by
    have hh := congrFun he 10
    simp only [hj1,mul_one] at hh
    exact_mod_cast hh
  have hkn : k 10 ≠ 0 := hk10 ▸ hb0
  have hnorm : ∀ i, j i=(k i : ℚ)/(k 10 : ℚ) := by
    intro i
    rw [hk10,congrFun he i]
    field_simp
  have descend : ∀ N : ℕ, ∀ v : Fin 11 → ℤ, (v 10).natAbs=N →
      equations v=0 → v 10 ≠ 0 → (∀ i, j i=(v i : ℚ)/(v 10 : ℚ)) →
      ∃ k : Fin 11 → ℤ, equations k=0 ∧ ¬ (19 : ℤ) ∣ k 10 ∧
        ∀ i, j i=(k i : ℚ)/(k 10 : ℚ) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro v hvN hv hv0 hvr
      by_cases hdiv : (19 : ℤ) ∣ v 10
      · choose w hw using (integral_conditions v hv).2 hdiv
        have hev : v=fun i => (19 : ℤ)*w i := funext hw
        have hw0 : w 10 ≠ 0 := by
          intro h0
          apply hv0
          rw [hw 10,h0]
          simp
        have hwpos : 0<(w 10).natAbs := Int.natAbs_pos.mpr hw0
        have hn : (w 10).natAbs<N := by
          rw [hev] at hvN
          norm_num [Int.natAbs_mul] at hvN
          nlinarith only [hvN,hwpos]
        have hwe : equations w=0 := by
          rw [hev,equations_scale] at hv
          ext i
          have hhi := congrFun hv i
          exact (mul_eq_zero.mp hhi).resolve_left (pow_ne_zero _ (by norm_num))
        have hwr : ∀ i, j i=(w i : ℚ)/(w 10 : ℚ) := by
          intro i
          rw [hvr i,hev]
          push_cast
          ring_nf
        exact ih _ hn w rfl hwe hw0 hwr
      · exact ⟨v,hv,hdiv,hvr⟩
  exact descend _ k rfl hi hkn hnorm

/-- In the primitive integral model, the variable length has one of the four
signed collinear boundary classes modulo 19. -/
lemma rational_residue_model (j : Fin 11 → ℚ) (hj : equations j=0) (hj1 : j 10=1) :
    ∃ k : Fin 11 → ℤ, equations k=0 ∧ ¬ (19 : ℤ) ∣ k 10 ∧
      (∀ i, j i=(k i : ℚ)/(k 10 : ℚ)) ∧
      (19 : ℤ) ∣ boundaryPolynomial ((k 9)^2) ((k 10)^2) := by
  obtain ⟨k,hk,hden,he⟩ := rational_integral_model j hj hj1
  exact ⟨k,hk,hden,he,(integral_conditions k hk).1⟩

/-- Algebraic connection with a rational flat Gram matrix. The three fixed
body lengths are 300,278,272; the fourth length is r. -/
lemma rational_gram_encoding (r A B C d e f : ℚ)
    (hs : 4*(A+B+C)=r^2+241268)
    (hd : 8*d=r^2-61268) (he : 8*e=r^2-86700) (hf : 8*f=r^2-93300)
    (ha : IsSquare A) (hb : IsSquare B) (hc : IsSquare C)
    (h₁ : IsSquare (A+B+2*d)) (h₂ : IsSquare (A+B-2*d))
    (h₃ : IsSquare (A+C+2*e)) (h₄ : IsSquare (A+C-2*e))
    (h₅ : IsSquare (B+C+2*f)) (h₆ : IsSquare (B+C-2*f))
    (hdet : A*B*C+2*d*e*f-A*f^2-B*e^2-C*d^2=0) :
    ∃ j : Fin 11 → ℚ, equations j=0 ∧ j 9=r ∧ j 10=1 := by
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨b,rfl⟩ := hb
  obtain ⟨c,rfl⟩ := hc
  obtain ⟨u₁,hu₁⟩ := h₁
  obtain ⟨u₂,hu₂⟩ := h₂
  obtain ⟨u₃,hu₃⟩ := h₃
  obtain ⟨u₄,hu₄⟩ := h₄
  obtain ⟨u₅,hu₅⟩ := h₅
  obtain ⟨u₆,hu₆⟩ := h₆
  refine ⟨![2*a,2*b,2*c,2*u₁,2*u₂,2*u₃,2*u₄,2*u₅,2*u₆,r,1],?_,rfl,rfl⟩
  ext i
  fin_cases i <;> dsimp [equations] <;> norm_num
  · linear_combination hs
  · linear_combination -4*hu₁+hd
  · linear_combination -4*hu₂-hd
  · linear_combination -4*hu₃+he
  · linear_combination -4*hu₄-he
  · linear_combination -4*hu₅+hf
  · linear_combination -4*hu₆-hf
  · rw [← hd,← he,← hf]
    linear_combination 256*hdet

#print axioms rational_gram_encoding
#print axioms rational_integral_model
#print axioms rational_residue_model
#print axioms local_test
#print axioms local_conditions
#print axioms integral_conditions
end Erdos213.FlatParallelVaryBody
