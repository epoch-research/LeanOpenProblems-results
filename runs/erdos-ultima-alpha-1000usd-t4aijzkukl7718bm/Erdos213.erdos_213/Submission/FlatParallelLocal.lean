import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Integer

/-! A local obstruction to flattening ONE fixed-body-diagonal parallelepiped.
This is not a bound on general planar integral-distance sets. -/
namespace Erdos213.FlatParallelLocal

local instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩
abbrev F := ZMod 19

def SqResidue (x : F) : Prop := x ∈ ({0,1,4,5,6,7,9,11,16,17} : Finset F)

instance (x : F) : Decidable (SqResidue x) := by
  unfold SqResidue
  infer_instance

lemma square_residue (x : F) : SqResidue (x^2) := by
  revert x
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma local_test (A B Z : F)
    (ha : SqResidue A) (hb : SqResidue B) (hz : SqResidue Z)
    (hc : SqResidue (Z-A-B))
    (habp : SqResidue (A+B+6*Z)) (habm : SqResidue (A+B-6*Z))
    (hacp : SqResidue (A+(Z-A-B)+13*Z)) (hacm : SqResidue (A+(Z-A-B)-13*Z))
    (hbcp : SqResidue (B+(Z-A-B)+16*Z)) (hbcm : SqResidue (B+(Z-A-B)-16*Z))
    (hd : A*B*(Z-A-B)+(2*A-Z)*Z^2=0) : A=0 ∧ B=0 ∧ Z=0 := by
  revert A B Z
  decide +kernel

/-- Nine length variables and their common homogeneous denominator. -/
def equations {R : Type*} [CommRing R] (j : Fin 10 → R) : Fin 8 → R :=
  ![(j 0)^2+(j 1)^2+(j 2)^2-95286*(j 9)^2,
    (j 3)^2-((j 0)^2+(j 1)^2+19652*(j 9)^2),
    (j 4)^2-((j 0)^2+(j 1)^2-19652*(j 9)^2),
    (j 5)^2-((j 0)^2+(j 2)^2+13294*(j 9)^2),
    (j 6)^2-((j 0)^2+(j 2)^2-13294*(j 9)^2),
    (j 7)^2-((j 1)^2+(j 2)^2+11644*(j 9)^2),
    (j 8)^2-((j 1)^2+(j 2)^2-11644*(j 9)^2),
    (j 0)^2*(j 1)^2*(j 2)^2+2*9826*6647*5822*(j 9)^6-
      (j 0)^2*5822^2*(j 9)^4-(j 1)^2*6647^2*(j 9)^4-
      (j 2)^2*9826^2*(j 9)^4]

lemma equations_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (j : Fin 10 → R) :
    equations (fun i => f (j i)) = fun i => f (equations j i) := by
  ext i
  fin_cases i <;> simp [equations, map_ofNat]

lemma equations_scale {R : Type*} [CommRing R] (r : R) (j : Fin 10 → R) :
    equations (fun i => r*j i) = fun i => r^(if i=7 then 6 else 2)*equations j i := by
  ext i
  fin_cases i <;> dsimp [equations] <;> ring

lemma local_zero (j : Fin 10 → F) (h : equations j=0) : j=0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  have h7 := congrFun h 7
  dsimp [equations] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [show (95286 : F)=1 by decide +kernel] at h0
  rw [show (19652 : F)=6 by decide +kernel] at h1 h2
  rw [show (13294 : F)=13 by decide +kernel] at h3 h4
  rw [show (11644 : F)=16 by decide +kernel] at h5 h6
  rw [show (2*9826*6647*5822 : F)=8 by decide +kernel,
      show (5822 : F)^2=7 by decide +kernel,
      show (6647 : F)^2=9 by decide +kernel,
      show (9826 : F)^2=9 by decide +kernel] at h7
  have hc : (j 2)^2=(j 9)^2-(j 0)^2-(j 1)^2 := by linear_combination h0
  have hd : (j 0)^2*(j 1)^2*((j 9)^2-(j 0)^2-(j 1)^2)+
      (2*(j 0)^2-(j 9)^2)*((j 9)^2)^2=0 := by
    linear_combination h7-((j 0)^2*(j 1)^2-9*(j 9)^4)*h0
  have habp : (j 0)^2+(j 1)^2+6*(j 9)^2=(j 3)^2 := by linear_combination -h1
  have habm : (j 0)^2+(j 1)^2-6*(j 9)^2=(j 4)^2 := by linear_combination -h2
  have hacp : (j 0)^2+((j 9)^2-(j 0)^2-(j 1)^2)+13*(j 9)^2=(j 5)^2 := by
    rw [← hc]; linear_combination -h3
  have hacm : (j 0)^2+((j 9)^2-(j 0)^2-(j 1)^2)-13*(j 9)^2=(j 6)^2 := by
    rw [← hc]; linear_combination -h4
  have hbcp : (j 1)^2+((j 9)^2-(j 0)^2-(j 1)^2)+16*(j 9)^2=(j 7)^2 := by
    rw [← hc]; linear_combination -h5
  have hbcm : (j 1)^2+((j 9)^2-(j 0)^2-(j 1)^2)-16*(j 9)^2=(j 8)^2 := by
    rw [← hc]; linear_combination -h6
  obtain ⟨ha,hb,hz⟩ := local_test ((j 0)^2) ((j 1)^2) ((j 9)^2)
    (square_residue _) (square_residue _) (square_residue _)
    (by rw [← hc]; exact square_residue _)
    (by rw [habp]; exact square_residue _) (by rw [habm]; exact square_residue _)
    (by rw [hacp]; exact square_residue _) (by rw [hacm]; exact square_residue _)
    (by rw [hbcp]; exact square_residue _) (by rw [hbcm]; exact square_residue _) hd
  have hA : j 0=0 := sq_eq_zero_iff.mp ha
  have hB : j 1=0 := sq_eq_zero_iff.mp hb
  have hZ : j 9=0 := sq_eq_zero_iff.mp hz
  have hC : j 2=0 := by rw [hA,hB,hZ] at hc; simpa using hc
  have hD : j 3=0 := by rw [hA,hB,hZ] at h1; simpa using h1
  have hE : j 4=0 := by rw [hA,hB,hZ] at h2; simpa using h2
  have hG : j 5=0 := by rw [hA,hC,hZ] at h3; simpa using h3
  have hH : j 6=0 := by rw [hA,hC,hZ] at h4; simpa using h4
  have hI : j 7=0 := by rw [hB,hC,hZ] at h5; simpa using h5
  have hJ : j 8=0 := by rw [hB,hC,hZ] at h6; simpa using h6
  ext i
  fin_cases i <;> simp [hA,hB,hC,hD,hE,hG,hH,hI,hJ,hZ]

lemma integral_divisible (j : Fin 10 → ℤ) (h : equations j=0) :
    ∀ i, (19 : ℤ) ∣ j i := by
  have hc : equations (fun i => (j i : F))=0 := by
    change equations (fun i => (Int.castRingHom F) (j i))=0
    rw [equations_map,h]
    rfl
  have hz := local_zero _ hc
  intro i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (j i) 19).mp (congrFun hz i)

private lemma descent_zero {ι : Type*} (R : (ι → ℤ) → Prop) (p : ℕ) (hp : 1<p)
    (hdiv : ∀ j, R j → ∃ k, R k ∧ j=fun i => (p : ℤ)*k i)
    (j : ι → ℤ) (hj : R j) : j=0 := by
  ext i
  have hc : ∀ N : ℕ, ∀ k : ι → ℤ, (k i).natAbs=N → R k → k i=0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro k hkN hk
      obtain ⟨l,hl,hkl⟩ := hdiv k hk
      by_cases hi : l i=0
      · rw [hkl]; simp [hi]
      have hlpos : 0<(l i).natAbs := Int.natAbs_pos.mpr hi
      have hn : (l i).natAbs<N := by
        rw [hkl] at hkN
        simp only [Int.natAbs_mul,Int.natAbs_natCast] at hkN
        nlinarith
      exact (hi (ih _ hn l rfl hl)).elim
  exact hc _ j rfl hj

lemma integral_zero (j : Fin 10 → ℤ) (h : equations j=0) : j=0 := by
  apply descent_zero (fun k => equations k=0) 19 (by norm_num) _ j h
  intro k hk
  choose l hl using integral_divisible k hk
  have he : k=fun i => (19 : ℤ)*l i := funext hl
  refine ⟨l,?_,he⟩
  rw [he,equations_scale] at hk
  ext i
  have hc := congrFun hk i
  exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (by norm_num))

lemma rational_zero (j : Fin 10 → ℚ) (h : equations j=0) : j=0 := by
  obtain ⟨b,hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) j
  change ∀ i, ∃ k : ℤ, (k : ℚ)=(b : ℤ) • j i at hb
  choose k hk using hb
  have he : (fun i => (k i : ℚ))=fun i => ((b : ℤ) : ℚ)*j i := by
    ext i
    simpa only [zsmul_eq_mul] using hk i
  have hc : equations (fun i => (k i : ℚ))=0 := by
    rw [he,equations_scale,h]
    ext i
    simp
  have hi : equations k=0 := by
    change equations (fun i => (Int.castRingHom ℚ) (k i))=0 at hc
    rw [equations_map] at hc
    ext i
    have hh := congrFun hc i
    change ((equations k i : ℤ) : ℚ)=0 at hh
    exact_mod_cast hh
  have hz := integral_zero k hi
  have hb0 : (b : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  ext i
  have hh := congrFun he i
  rw [hz] at hh
  have hbQ : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hb0
  exact (mul_eq_zero.mp hh.symm).resolve_left hbQ

/-- No flat rational Gram matrix in this fixed-body-diagonal family can have
all edge and face-diagonal lengths rational. No positivity assumptions are needed. -/
lemma no_flat_fixed_body_diagonals (A B C : ℚ)
    (hs : A+B+C=95286)
    (ha : IsSquare A) (hb : IsSquare B) (hc : IsSquare C)
    (h₁ : IsSquare (A+B+19652)) (h₂ : IsSquare (A+B-19652))
    (h₃ : IsSquare (A+C+13294)) (h₄ : IsSquare (A+C-13294))
    (h₅ : IsSquare (B+C+11644)) (h₆ : IsSquare (B+C-11644))
    (hd : A*B*C+2*9826*6647*5822-A*5822^2-B*6647^2-C*9826^2=0) : False := by
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨b,rfl⟩ := hb
  obtain ⟨c,rfl⟩ := hc
  obtain ⟨u₁,hu₁⟩ := h₁
  obtain ⟨u₂,hu₂⟩ := h₂
  obtain ⟨u₃,hu₃⟩ := h₃
  obtain ⟨u₄,hu₄⟩ := h₄
  obtain ⟨u₅,hu₅⟩ := h₅
  obtain ⟨u₆,hu₆⟩ := h₆
  let j : Fin 10 → ℚ := ![a,b,c,u₁,u₂,u₃,u₄,u₅,u₆,1]
  have hj : equations j=0 := by
    ext i
    fin_cases i <;> dsimp [equations,j] <;> norm_num
    · linear_combination hs
    · linear_combination -hu₁
    · linear_combination -hu₂
    · linear_combination -hu₃
    · linear_combination -hu₄
    · linear_combination -hu₅
    · linear_combination -hu₆
    · linear_combination hd
  have hz := congrFun (rational_zero j hj) 9
  change (1 : ℚ) = 0 at hz
  norm_num at hz

#print axioms integral_zero
#print axioms rational_zero
#print axioms no_flat_fixed_body_diagonals

#print axioms local_test
#print axioms local_zero
end Erdos213.FlatParallelLocal
