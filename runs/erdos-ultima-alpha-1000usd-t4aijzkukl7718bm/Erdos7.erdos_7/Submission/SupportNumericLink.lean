import Submission.SupportPrefixMetadata
import Submission.SupportCertificateScaling

/-! Interpretation of individual certified integer rows. Full numerical row
certificates are supplied separately; the hypotheses are explicit here. -/
namespace Erdos7SupportNumericLink
open scoped BigOperators
open Erdos7SupportPrefixData Erdos7SupportPrefixChecks Erdos7SupportPrefixMetadata
open Erdos7SupportCertificateScaling Erdos7SupportLowerLaw Erdos7SupportCompression
open Erdos7CompressionSieve Erdos7SupportMomentMatrix
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

lemma prime_gt (i : Fin 167) : 1 < p i := by have := (cap_bounds i).2.2; omega

lemma cap_rat_bounds (i : Fin 167) : 1 ≤ cap i ∧ cap i ≤ p i := by
  obtain ⟨h₁,h₂,h₃⟩ := cap_bounds i
  have hd : (0:ℚ) < capDen := by norm_num [capDen]
  unfold cap
  constructor
  · apply (le_div_iff₀ hd).mpr
    simpa using (show (capDen:ℚ) ≤ cn i by exact_mod_cast h₁)
  · apply (div_le_iff₀ hd).mpr
    simpa [mul_comm] using (show (cn i:ℚ) ≤ (capDen:ℚ)*p i by exact_mod_cast h₂)

lemma lower_row_rat (i : Fin 167) (j : Fin 180) (h : lowerRow i j) :
    low (i.val+1) j ≤ (1-cap i/(p i:ℚ))*low i j+
      ∑ a : Fin 12,cap i*((p i:ℚ)-1)/(p i:ℚ)^(a.val+2)*(pred j a).elim 0 (low i) := by
  let w (a : Fin 12) := cn i*(p i-1)*(p i)^(12-1-a.val)
  let v (a : Fin 12) := lowNat i (predIndex j a)
  have hn : lowNat (i.val+1) j*(capDen*(p i)^13) ≤
      lowNat i j*((capDen*p i-cn i)*(p i)^12)+∑ a : Fin 12,w a*v a := by
    unfold lowerRow at h
    change lowNat (i.val+1) j*(capDen*(p i)^(12+1)) ≤
      lowNat i j*(capDen*p i-cn i)*(p i)^12+
        ∑ a ∈ Finset.range 12,lowNat i (getNat (predecessor[j.val]?.getD #[]) a)*
          cn i*(p i-1)*(p i)^(12-1-a) at h
    have he : (∑ a : Fin 12,w a*v a)=
        ∑ a ∈ Finset.range 12,lowNat i (getNat (predecessor[j.val]?.getD #[]) a)*
          cn i*(p i-1)*(p i)^(12-1-a) := by
      dsimp only [w,v,predIndex]
      rw [Fin.sum_univ_eq_sum_range (fun a => cn i*(p i-1)*(p i)^(12-1-a)*
        lowNat i (getNat (predecessor[j.val]?.getD #[]) a)) 12]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [he]
    simpa only [mul_assoc] using h
  have hp := prime_gt i
  have hh := normalized_row lawScale (capDen*(p i)^13) (lowNat i j) (lowNat (i.val+1) j)
    ((capDen*p i-cn i)*(p i)^12) w v (by norm_num [lawScale]) (Nat.mul_pos (by norm_num [capDen]) (pow_pos (by omega) _)) hn
  have hb := base_coefficient (p i) capDen (cn i) 12 (by omega) (by norm_num [capDen]) (cap_bounds i).2.1
  have hw (a : Fin 12) : ((w a:ℕ):ℚ)/((capDen*(p i)^13:ℕ):ℚ)=
      cap i*((p i:ℚ)-1)/(p i:ℚ)^(a.val+2) :=
    increment_coefficient (p i) capDen (cn i) 12 a.val hp (by norm_num [capDen]) a.isLt
  have hv (a : Fin 12) : ((v a:ℕ):ℚ)/lawScale=(pred j a).elim 0 (low i) :=
    (pred_value ⟨i.val,by omega⟩ j a).symm
  simpa only [hw,hv,hb,cap,low] using hh

/-- The checked lower rows propagate a genuine lower sublaw at every finite
exponent cap at least13. No equality with the full distribution is asserted. -/
theorem lower_encoded_step (i : Fin 167) (E : ℕ) (hE : 12 < E)
    (hrow : ∀ j : Fin 180,lowerRow i j) :
    encode repr (low (i.val+1)) ≤ tripleStep E (powerTail (p i) (cap i) E) (encode repr (low i)) := by
  exact lower_step repr repr_injective (low i) (low (i.val+1)) (low_nonneg i)
    (p i) E 12 (prime_gt i) hE (cap i) (by have := (cap_rat_bounds i).1; linarith)
    (cap_rat_bounds i).2 pred pred_equation (fun j => lower_row_rat i j (hrow j))

lemma moment_row_rat (i : Fin 167) (j : Fin 10) (h : momentRow i j) :
    advance (p i) (cap i) (mom i) j ≤ mom (i.val+1) j := by
  let den := capDen*(p i-1)^3
  let R (k : ℕ) := getNat #[cn i*(p i-1)^2,cn i*(p i+1)*(p i-1),cn i*((p i)^2+4*p i+1)] k
  let V (k a : ℕ) := getNat ((matrix[k]?.getD #[])[j.val]?.getD #[]) a
  have hinner (k : ℕ) : (∑ a : Fin 10,V k a*momNat i a)=
      ∑ a ∈ Finset.range 10,V k a*momNat i a :=
    Fin.sum_univ_eq_sum_range (fun a => V k a*momNat i a) 10
  have hsum : (∑ k : Fin 3,R k*∑ a : Fin 10,V k a*momNat i a)=
      ∑ k ∈ Finset.range 3,R k*∑ a ∈ Finset.range 10,V k a*momNat i a := by
    simp_rw [hinner]
    exact Fin.sum_univ_eq_sum_range (fun k => R k*∑ a ∈ Finset.range 10,V k a*momNat i a) 3
  have hn : den*momNat i j+(∑ k : Fin 3,R k*∑ a : Fin 10,V k a*momNat i a) ≤
      den*momNat (i.val+1) j := by
    rw [hsum]
    exact h
  have hp := prime_gt i
  have hd : 0 < den := Nat.mul_pos (by norm_num [capDen]) (pow_pos (by omega) _)
  have hh := normalized_moment_row momentScale den (momNat i j) (momNat (i.val+1) j)
    (fun k : Fin 3 => R k) (fun k : Fin 3 => fun a : Fin 10 => V k a) (fun a : Fin 10 => momNat i a)
    (by norm_num [momentScale]) hd hn
  have hV (k : Fin 3) (a : Fin 10) : (V k a:ℚ)=coeff k j a := matrix_info k j a
  simp_rw [hV] at hh
  rw [Fin.sum_univ_three] at hh
  norm_num only [Fin.val_zero,Fin.val_one,Fin.val_ofNat,Fin.coe_ofNat_eq_mod] at hh
  obtain ⟨hr₀,hr₁,hr₂⟩ := moment_coefficients (p i) capDen (cn i) hp (by norm_num [capDen])
  change (R 0:ℚ)/den=cap i/((p i:ℚ)-1) at hr₀
  change (R 1:ℚ)/den=cap i*((p i:ℚ)+1)/((p i:ℚ)-1)^2 at hr₁
  change (R 2:ℚ)/den=cap i*((p i:ℚ)^2+4*p i+1)/((p i:ℚ)-1)^3 at hr₂
  rw [hr₀,hr₁,hr₂] at hh
  simpa only [advance,mom,add_assoc] using hh

lemma loss_row_rat (i : Fin 167) (h : lossRow i) :
    cap i/((p i:ℚ)-1)*(mom i 0+mom i 1+mom i 4)-
      (∑ j : Fin 180,low i j*min (cap i-1) (cap i/((p i:ℚ)-1)*(tripleCount (repr j):ℚ))) ≤ cost i := by
  let K (j : ℕ) := 1+(states[j]?.getD (0,0)).1+(states[j]?.getD (0,0)).2
  let A (j : ℕ) := min ((cn i-capDen)*(p i-1)) (cn i*K j)
  let S := ∑ j : Fin 180,lowNat i j*A j
  let M := momNat i 0+momNat i 1+momNat i 4
  have hsum : S=∑ j ∈ Finset.range 180,lowNat i j*A j :=
    Fin.sum_univ_eq_sum_range (fun j => lowNat i j*A j) 180
  have hn : cn i*M*lawScale*costScale ≤
      getNat costs i*(capDen*(p i-1)*momentScale*lawScale)+momentScale*costScale*S := by
    rw [hsum]
    exact h
  have hp := prime_gt i
  have hpQ : (1:ℚ) < p i := by exact_mod_cast hp
  have hm : (p i:ℚ)-1≠0 := by linarith
  have hqcast : ((p i-1:ℕ):ℚ)=(p i:ℚ)-1 := by exact_mod_cast Nat.cast_sub (show 1 ≤ p i by omega)
  have hmin (j : Fin 180) : min (cap i-1) (cap i/((p i:ℚ)-1)*(tripleCount (repr j):ℚ))=
      (A j:ℚ)/((capDen:ℚ)*((p i:ℚ)-1)) := by
    have hh := min_coefficient capDen (cn i) (p i-1) (K j) (by norm_num [capDen])
      (by omega) (cap_bounds i).1
    simpa only [cap,hqcast,Nat.cast_mul,Erdos7SupportPrefixMetadata.repr,tripleCount,K,A] using hh
  have htotal : (∑ j : Fin 180,low i j*min (cap i-1)
      (cap i/((p i:ℚ)-1)*(tripleCount (repr j):ℚ))) =
      (S:ℚ)/((capDen:ℚ)*((p i:ℚ)-1)*lawScale) := by
    simp_rw [hmin]
    dsimp only [low,S]
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
    <;> ring
  rw [htotal]
  have hh := normalized_loss_row lawScale momentScale costScale capDen (cn i) (p i-1)
    M S (getNat costs i) (by norm_num [lawScale]) (by norm_num [momentScale])
    (by norm_num [costScale]) (by norm_num [capDen]) (by omega) hn
  rw [hqcast] at hh
  simpa only [cap,cost,mom,M,Nat.cast_add,add_div] using hh

#print axioms loss_row_rat

#print axioms moment_row_rat

#print axioms lower_encoded_step
end Erdos7SupportNumericLink
