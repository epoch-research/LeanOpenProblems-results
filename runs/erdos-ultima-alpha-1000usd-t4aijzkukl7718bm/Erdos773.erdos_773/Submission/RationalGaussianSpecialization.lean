import Submission.FormalGaussianSidon

/-! An exact rational-base specialization obstruction. This is not a
counterexample to Erdős 773. The four digit vectors have small coordinatewise
variation, not small absolute coefficients relative to the denominator. -/
namespace Erdos773.RationalGaussianSpecialization
open Finset Polynomial
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

def denominator : ℕ := 234000000000000

def coefficient : Fin 4 → Fin 12 → ℕ := ![![834799500000000,234234000000,233867200500,231830568000,227187634500,23399987171130000,13962527325916000,5218012586724000,231411830000,233284765961,234273000000,949233922000000],
  ![834799500000000,233766000000,234132799500,236169432000,240812365500,23400012828870000,13962551674084000,5218027413276000,236588170000,234715233961,233727000000,949234078000000],
  ![834799500000000,233766000000,234132799500,236169432000,240812365500,23400012828870000,13962551674084000,5218027335276000,236900170000,234169234039,234039000000,949234000000000],
  ![834799500000000,234234000000,233867200500,231830568000,227187634500,23399987171130000,13962527325916000,5218012664724000,231099830000,233830766039,233961000000,949234000000000]]

lemma coefficient_pos : ∀ i j, 1 ≤ coefficient i j := by decide +kernel
lemma coefficient_spread : ∀ i k j,
    6000 * Int.natAbs ((coefficient i j:ℤ)-coefficient k j) < denominator := by
  decide +kernel

def q (t : ℕ) : ℕ := denominator*(t+1)
def p (t : ℕ) : ℕ := q t+1

def digit (t : ℕ) (i : Fin 4) (j : Fin 12) : ℕ :=
  (coefficient i j-1)*(t+1)+t+(if j.val=11 then 0 else 1)

def cleared (t : ℕ) (i : Fin 4) : ℕ :=
  (p t)^13+6*(q t)^13+
    6*∑ j : Fin 12, digit t i j*(p t)^(j.val+1)*(q t)^(12-j.val)

lemma digit_cast (t : ℕ) (i : Fin 4) (j : Fin 12) :
    (digit t i j:ℚ)=(coefficient i j:ℚ)*(t+1)-(if j.val=11 then 1 else 0) := by
  unfold digit
  rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (coefficient_pos i j)]
  push_cast
  split_ifs <;> norm_num <;> ring

def raw (z : ℚ) (i : Fin 4) : ℚ :=
  (z+1)^13+6*z^13+
    6*∑ j : Fin 12, ((coefficient i j:ℚ)/denominator*z-(if j.val=11 then 1 else 0))*
      (z+1)^(j.val+1)*z^(12-j.val)

def F (z : ℚ) : ℚ := 1+z^2*(z+1)^2
def G (z : ℚ) : ℚ :=
  (3412787/3000)*z^10+(33904063/6500)*z^9+(798975701/78000)*z^8+
  (886034519/78000)*z^7+(2539698/325)*z^6+(5149939/1500)*z^5+
  (1435693/1500)*z^4+(86539/500)*z^3+(44009/1500)*z^2+7*z+1

def U (z : ℚ) : ℚ := (1/1000000)*z^2*(z+1)^2
def V (z : ℚ) : ℚ := (1/1000000)*z^2*(z+1)^8

def factored (z : ℚ) : Fin 4 → ℚ :=
  ![F z*G z-U z*V z-F z*V z-G z*U z,
    F z*G z-U z*V z+F z*V z+G z*U z,
    F z*G z+U z*V z-F z*V z+G z*U z,
    F z*G z+U z*V z+F z*V z-G z*U z]

lemma raw_factor (z : ℚ) (i : Fin 4) : raw z i=factored z i := by
  fin_cases i <;>
    norm_num [raw,coefficient,denominator,factored,F,G,U,V,Fin.sum_univ_succ] <;> ring

lemma cleared_cast (t : ℕ) (i : Fin 4) : (cleared t i:ℚ)=raw (q t) i := by
  unfold cleared raw
  simp only [p,Nat.cast_add]
  push_cast
  congr 1
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [digit_cast]
  have he : (coefficient i j:ℚ)*(t+1)=(coefficient i j:ℚ)/denominator*(q t) := by
    simp only [q,denominator,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  rw [he]

lemma raw_collision (z : ℚ) : (raw z 0)^2+(raw z 1)^2=(raw z 2)^2+(raw z 3)^2 := by
  simp only [raw_factor]
  change (F z*G z-U z*V z-F z*V z-G z*U z)^2+
      (F z*G z-U z*V z+F z*V z+G z*U z)^2=
      (F z*G z+U z*V z-F z*V z+G z*U z)^2+
      (F z*G z+U z*V z+F z*V z-G z*U z)^2
  ring

lemma collision (t : ℕ) : (cleared t 0)^2+(cleared t 1)^2=
    (cleared t 2)^2+(cleared t 3)^2 := by
  have hh := raw_collision (q t)
  simp only [← cleared_cast] at hh
  exact_mod_cast hh

lemma q_pos (t : ℕ) : 0<q t := by unfold q denominator; positivity
lemma p_pos (t : ℕ) : 0<p t := by unfold p; omega
lemma coprime (t : ℕ) : Nat.Coprime (p t) (q t) := by
  exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left (q t))

lemma cleared_pos (t : ℕ) (i : Fin 4) : 0<cleared t i := by
  have hp := pow_pos (p_pos t) 13
  unfold cleared
  omega

lemma raw_nontrivial (z : ℚ) (hz : 0<z) : raw z 0<raw z 2 ∧ raw z 0<raw z 3 := by
  have hf : 0<F z := by unfold F; positivity
  have hg : 0<G z := by unfold G; positivity
  have hu : 0<U z := by unfold U; positivity
  have hv : 0<V z := by unfold V; positivity
  simp only [raw_factor]
  change F z*G z-U z*V z-F z*V z-G z*U z < F z*G z+U z*V z-F z*V z+G z*U z ∧
    F z*G z-U z*V z-F z*V z-G z*U z < F z*G z+U z*V z+F z*V z-G z*U z
  constructor
  · nlinarith only [mul_pos hu (add_pos hv hg)]
  · nlinarith only [mul_pos hv (add_pos hu hf)]

lemma cleared_nontrivial (t : ℕ) : cleared t 0<cleared t 2 ∧ cleared t 0<cleared t 3 := by
  have hh := raw_nontrivial (q t) (by exact_mod_cast q_pos t)
  simp only [← cleared_cast] at hh
  exact_mod_cast hh

/-- The colliding natural square values are not merely an evaluation alias. -/
theorem not_sidon (t : ℕ) :
    ¬IsSidon ((fun i : Fin 4 => (cleared t i)^2) '' Set.univ) := by
  intro hs
  have hm (i : Fin 4) : (cleared t i)^2 ∈ (fun i : Fin 4 => (cleared t i)^2) '' Set.univ :=
    ⟨i,Set.mem_univ i,rfl⟩
  have h := hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision t)
  have hn := cleared_nontrivial t
  rcases h with h | h
  · exact (Nat.pow_lt_pow_left hn.1 (by decide : (2:ℕ) ≠ 0)).ne h.1
  · exact (Nat.pow_lt_pow_left hn.2 (by decide : (2:ℕ) ≠ 0)).ne h.1

def parameter (t : ℕ) (i : Fin 4) : ℤ[X] :=
  C 1+∑ j : Fin 12, C (digit t i j:ℤ)*X^(j.val+1)

def poly (t : ℕ) (i : Fin 4) : ℤ[X] := FormalGaussianSidon.encoding 13 (parameter t i)

lemma parameter_constant (t : ℕ) (i : Fin 4) : (parameter t i).coeff 0=1 := by
  simp [parameter]

lemma parameter_degree (t : ℕ) (i : Fin 4) : (parameter t i).natDegree<13 := by
  have hh : (parameter t i).natDegree ≤ 12 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have he (j : Fin 12) : n ≠ j.val+1 := by have hj := j.isLt; omega
    simp [parameter,coeff_one,he,show n ≠ 0 by omega]
  omega

lemma admissible (t : ℕ) (i : Fin 4) : FormalGaussianSidon.Admissible 13 (parameter t i) := by
  exact ⟨parameter_degree t i,by rw [parameter_constant]; norm_num⟩

/-- Sidonness is valid before specializing the polynomial variable. -/
theorem formal_sidon (t : ℕ) : IsSidon ((fun i : Fin 4 => (poly t i)^2) '' Set.univ) := by
  have hm {x : ℤ[X]} (hx : x ∈ (fun i : Fin 4 => (poly t i)^2) '' Set.univ) :
      x ∈ (fun P : ℤ[X] => (FormalGaussianSidon.encoding 13 P)^2) ''
        {P | FormalGaussianSidon.Admissible 13 P} := by
    obtain ⟨i,hi,rfl⟩ := hx
    exact ⟨parameter t i,admissible t i,rfl⟩
  intro a ha b hb c hc d hd he
  exact FormalGaussianSidon.formal_sidon 13 a (hm ha) b (hm hb) c (hm hc) d (hm hd) he

/-- Clearing the rational evaluation really gives the natural roots above. -/
lemma evaluation (t : ℕ) (i : Fin 4) :
    (q t:ℚ)^13 * (poly t i).eval₂ (Int.castRingHom ℚ) ((p t:ℚ)/q t) = cleared t i := by
  have hq : (q t:ℚ) ≠ 0 := by exact_mod_cast (q_pos t).ne'
  unfold poly FormalGaussianSidon.encoding parameter cleared
  simp only [eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
  push_cast
  simp only [Fin.sum_univ_succ]
  norm_num [Fin.val_succ]
  field_simp
  ring

lemma spread_certificate : ∀ i k j,
    6000*abs ((coefficient i j:ℚ)-coefficient k j) < denominator := by decide +kernel

/-- This bounds coordinatewise variation, not absolute digit sizes. -/
theorem digit_spread (t : ℕ) (i k : Fin 4) (j : Fin 12) :
    1000*abs (6*(digit t i j:ℚ)-6*(digit t k j:ℚ)) < q t := by
  rw [digit_cast,digit_cast]
  have hh := mul_lt_mul_of_pos_right (spread_certificate i k j)
    (show (0:ℚ)<t+1 by positivity)
  have he : 6*((coefficient i j:ℚ)*(t+1)-(if j.val=11 then 1 else 0))-
      6*((coefficient k j:ℚ)*(t+1)-(if j.val=11 then 1 else 0)) =
      6*((coefficient i j:ℚ)-coefficient k j)*(t+1) := by ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg (show (0:ℚ) ≤ 6 by norm_num),
    abs_of_nonneg (show (0:ℚ) ≤ t+1 by positivity)]
  simp only [q,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  nlinarith only [hh]

lemma G_lower {z : ℚ} (hz : 0<z) : F z*(z+1)^6<G z := by
  have he : G z-F z*(z+1)^6 =
      (3409787/3000)*z^10+(33852063/6500)*z^9+(796791701/78000)*z^8+
      (881666519/78000)*z^7+(2516623/325)*z^6+(5056939/1500)*z^5+
      (1371193/1500)*z^4+(72539/500)*z^3+(20009/1500)*z^2+z := by
    unfold G F
    ring
  apply sub_pos.mp
  rw [he]
  positivity

lemma raw_order {z : ℚ} (hz : 0<z) :
    raw z 0<raw z 3 ∧ raw z 3<raw z 2 ∧ raw z 2<raw z 1 := by
  have hu : 0<U z := by unfold U; positivity
  have hv : 0<V z := by unfold V; positivity
  have hfu : U z<F z := by
    have hh : 0<1+(999999/1000000:ℚ)*z^2*(z+1)^2 := by positivity
    unfold U F
    nlinarith only [hh]
  have hgu := mul_lt_mul_of_pos_right (G_lower hz) hu
  have hvu : V z=U z*(z+1)^6 := by unfold U V; ring
  refine ⟨(raw_nontrivial z hz).2,?_,?_⟩
  · simp only [raw_factor]
    change F z*G z+U z*V z+F z*V z-G z*U z <
      F z*G z+U z*V z-F z*V z+G z*U z
    rw [hvu] at *
    nlinarith only [hgu]
  · have hh := mul_lt_mul_of_pos_right hfu hv
    simp only [raw_factor]
    change F z*G z+U z*V z-F z*V z+G z*U z <
      F z*G z-U z*V z+F z*V z+G z*U z
    nlinarith only [hh]

lemma cleared_order (t : ℕ) : cleared t 0<cleared t 3 ∧
    cleared t 3<cleared t 2 ∧ cleared t 2<cleared t 1 := by
  have hh := raw_order (show (0:ℚ)<q t by exact_mod_cast q_pos t)
  simp only [← cleared_cast] at hh
  exact_mod_cast hh

lemma cleared_injective (t : ℕ) : Function.Injective (cleared t) := by
  obtain ⟨h₁,h₂,h₃⟩ := cleared_order t
  intro i j he
  fin_cases i <;> fin_cases j
  · rfl
  · change cleared t 0=cleared t 1 at he
    omega
  · change cleared t 0=cleared t 2 at he
    omega
  · change cleared t 0=cleared t 3 at he
    omega
  · change cleared t 1=cleared t 0 at he
    omega
  · rfl
  · change cleared t 1=cleared t 2 at he
    omega
  · change cleared t 1=cleared t 3 at he
    omega
  · change cleared t 2=cleared t 0 at he
    omega
  · change cleared t 2=cleared t 1 at he
    omega
  · rfl
  · change cleared t 2=cleared t 3 at he
    omega
  · change cleared t 3=cleared t 0 at he
    omega
  · change cleared t 3=cleared t 1 at he
    omega
  · change cleared t 3=cleared t 2 at he
    omega
  · rfl

lemma coefficient_nonneg (t : ℕ) (i : Fin 4) (n : ℕ) : 0 ≤ (poly t i).coeff n := by
  have hp : 0 ≤ (parameter t i).coeff n := by
    simp only [parameter,coeff_add,finset_sum_coeff,coeff_C_mul,coeff_X_pow,coeff_C]
    apply add_nonneg
    · split_ifs <;> norm_num
    · apply sum_nonneg
      intro j hj
      split_ifs <;> positivity
  simp only [poly,FormalGaussianSidon.encoding,coeff_add,coeff_X_pow,coeff_C_mul]
  positivity

/-- The counterexamples have coprime rational bases arbitrarily close to one.
Only coordinatewise spread is small; no small absolute-digit bound is asserted. -/
theorem specialization_obstruction (t : ℕ) :
    0<q t ∧ Nat.Coprime (p t) (q t) ∧
    IsSidon ((fun i : Fin 4 => (poly t i)^2) '' Set.univ) ∧
    (∀ i n, 0 ≤ (poly t i).coeff n) ∧
    (∀ i k j, 1000*abs (6*(digit t i j:ℚ)-6*(digit t k j:ℚ)) < q t) ∧
    (∀ i, (q t:ℚ)^13 * (poly t i).eval₂ (Int.castRingHom ℚ) ((p t:ℚ)/q t)=cleared t i) ∧
    Function.Injective (cleared t) ∧
    ¬IsSidon ((fun i : Fin 4 => (cleared t i)^2) '' Set.univ) := by
  exact ⟨q_pos t,coprime t,formal_sidon t,coefficient_nonneg t,digit_spread t,
    evaluation t,cleared_injective t,not_sidon t⟩

#print axioms raw_factor
#print axioms cleared_injective
#print axioms coefficient_nonneg
#print axioms specialization_obstruction

#print axioms collision
#print axioms not_sidon
#print axioms formal_sidon
#print axioms evaluation
#print axioms digit_spread

end
end Erdos773.RationalGaussianSpecialization
