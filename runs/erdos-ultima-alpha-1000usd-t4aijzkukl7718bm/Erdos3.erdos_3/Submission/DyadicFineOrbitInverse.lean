import Submission.FineMultipleOrbitCompression
import Submission.CircleIntegerApproximation

/-! Dyadic parameter form of fine orbit compression, preserving a higher-power
error scale and gaining one power of interval length. -/
namespace Erdos3DyadicFineOrbitInverse
open Erdos3FineMultipleOrbitCompression Erdos3CircleIntegerApproximation
open scoped Classical
set_option maxHeartbeats 3000000

lemma nat_pow_ge_self {N k : ℕ} (hk : 1 ≤ k) : N ≤ N^k := by
  by_cases hN : N = 0
  · subst N; exact Nat.zero_le _
  · simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < N) hk

/-- Bounded multiples for all short dilates at error N^-k force a single
bounded denominator at error N^-(k+1). -/
theorem dyadic_fine_orbit_inverse (v : ℂ) (hv : ‖v‖ = 1) (d h e k N : ℕ)
    (hk : 1 ≤ k) (hN : 2^(13+2*d+3*h+2*e) ≤ N)
    (hgood : ∀ t < N/2^d, ∃ a : ℕ, 0 < a ∧ a < 2^h ∧
      ‖v^(a*t)-1‖ ≤ (2 : ℝ)^e/(N : ℝ)^k) :
    ∃ q : ℕ, 0 < q ∧ q < 2^(3+d+2*h) ∧
      ‖v^q-1‖ ≤ (2 : ℝ)^(8+2*d+2*h+e)/(N : ℝ)^(k+1) := by
  let D := 2^d
  let H := 2^h
  let E := 2^e
  let ε := (2 : ℝ)^e/(N : ℝ)^k
  let α := unitAngle v
  have hD : 0 < D := Nat.two_pow_pos _
  have hH : 0 < H := Nat.two_pow_pos _
  have hE : 0 < E := Nat.two_pow_pos _
  have hN0 : 0 < N := (Nat.two_pow_pos _).trans_le hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hpow (c a b r : ℕ) : 2^c*D^a*H^b*E^r = 2^(c+d*a+h*b+e*r) := by
    dsimp only [D,H,E]
    simp only [← pow_mul,← pow_add]
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hεE : ε ≤ (E : ℝ)/(N : ℝ) := by
    dsimp only [ε,E]
    push_cast
    exact div_le_div_of_nonneg_left (by positivity) hNr (by exact_mod_cast nat_pow_ge_self hk (N := N))
  have hNE : 8*(2*D*H)*(6*E+1) ≤ N := by
    have h6 : 6*E+1 ≤ 7*E := by omega
    have hh := Nat.mul_le_mul_left (8*(2*D*H)) h6
    have hp : 128*D*H*E = 2^(7+d+h+e) := by
      simpa only [pow_one,show 2^7 = 128 by norm_num,Nat.mul_one] using hpow 7 1 1 1
    calc
      _ ≤ 128*D*H*E := by nlinarith only [hh,Nat.zero_le (D*H*E)]
      _ = _ := hp
      _ ≤ 2^(13+2*d+3*h+2*e) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _ := hN
  have hDN : 4*D ≤ N := by
    have hp : 4*D = 2^(2+d) := by dsimp only [D]; rw [show 4=2^2 by norm_num,← pow_add]
    rw [hp]
    exact (Nat.pow_le_pow_right (by decide) (by omega : 2+d ≤ 13+2*d+3*h+2*e)).trans hN
  have hdet : 4*(H*(256*D^2*H^2*E*(6*E+1))+(8*D*H^2)*E) ≤ N := by
    have h6 : 6*E+1 ≤ 7*E := by omega
    have hh := Nat.mul_le_mul_left (1024*D^2*H^3*E) h6
    have hmult : 1 ≤ D*H*E := Nat.mul_pos (Nat.mul_pos hD hH) hE
    have hbase := Nat.mul_le_mul_left (D*H^2*E) hmult
    have hp : 8192*D^2*H^3*E^2 = 2^(13+2*d+3*h+2*e) := by
      simpa only [show 2^13 = 8192 by norm_num,Nat.mul_comm d 2,Nat.mul_comm h 3,Nat.mul_comm e 2] using hpow 13 2 3 2
    calc
      _ ≤ 8192*D^2*H^3*E^2 := by nlinarith only [hh,hbase,Nat.zero_le (D^2*H^3*E^2)]
      _ = _ := hp
      _ ≤ _ := hN
  have hnear : ∀ t < N/D, ∃ a : ℕ, ∃ b : ℤ, 0 < a ∧ a < H ∧
      |α*((a*t : ℕ) : ℝ)-(b : ℝ)| ≤ ε := by
    intro t ht
    obtain ⟨a,ha,haH,he⟩ := hgood t ht
    obtain ⟨b,hb⟩ := exists_integer_near (α*((a*t : ℕ) : ℝ))
    have hephase : ephase (α*((a*t : ℕ) : ℝ)) = v^(a*t) := by
      rw [mul_comm α,← ephase_pow]
      dsimp only [α]
      rw [ephase_unitAngle v hv]
    rw [hephase] at hb
    refine ⟨a,b,ha,haH,?_⟩
    change ‖v^(a*t)-1‖ ≤ ε at he
    linarith only [hb,he,hε]
  obtain ⟨q,b,hq,hqb,herr⟩ := fine_multiple_linear_orbit_inverse α hD hH hNE hDN hdet hε hεE hnear
  have hQ : 8*D*H^2 = 2^(3+d+2*h) := by
    dsimp only [D,H]
    rw [show 8=2^3 by norm_num,← pow_mul,← pow_add,← pow_add]
    congr 1
    omega
  refine ⟨q,hq,by simpa only [hQ] using hqb,?_⟩
  have hc := ephase_near_integer (α*(q : ℝ)) b
  have hephase : ephase (α*(q : ℝ)) = v^q := by
    rw [mul_comm α,← ephase_pow]
    dsimp only [α]
    rw [ephase_unitAngle v hv]
  rw [hephase] at hc
  have hnum : 256*(D : ℝ)^2*(H : ℝ)^2*(2 : ℝ)^e = (2 : ℝ)^(8+2*d+2*h+e) := by
    dsimp only [D,H]
    push_cast
    rw [show (256 : ℝ)=2^8 by norm_num,← pow_mul,← pow_mul,← pow_add,← pow_add,← pow_add]
    congr 1
    omega
  calc
    _ ≤ 8*|α*(q : ℝ)-(b : ℝ)| := hc
    _ ≤ 8*(32*(D : ℝ)^2*(H : ℝ)^2*ε/(N : ℝ)) := mul_le_mul_of_nonneg_left herr (by norm_num)
    _ = (256*(D : ℝ)^2*(H : ℝ)^2*(2 : ℝ)^e)/(N : ℝ)^(k+1) := by
      dsimp only [ε]
      rw [pow_succ]
      ring
    _ = _ := by rw [hnum]

#print axioms dyadic_fine_orbit_inverse
end Erdos3DyadicFineOrbitInverse
