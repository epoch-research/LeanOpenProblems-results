import Submission.RationalObstruction
import Submission.PrimeIntervalCounts

/-! Large-denominator rational slopes have a locally admissible residue in
the interior fractional-part window used by RationalRoute. This does not
prove simultaneous primality or the finite prime-input bound in that route. -/
namespace Erdos972RationalInteriorAdmissibility

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972ChebyshevPNT Erdos972PrimeIntervalCounts Erdos972Local

set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma theta_interval_le_log_of_all_dvd {x y : ℝ} {n : ℕ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hn : n ≠ 0)
    (hdiv : ∀ p : ℕ, p.Prime → x < p → (p:ℝ) ≤ y → p ∣ n) :
    Chebyshev.theta y - Chebyshev.theta x ≤ Real.log n := by
  classical
  have he : Chebyshev.theta y - Chebyshev.theta x =
      ∑ p ∈ primesBetween ⌊x⌋₊ ⌊y⌋₊, Real.log p := by
    simpa only [Chebyshev.theta, Nat.floor_natCast] using
      (theta_interval_sum (Nat.floor_mono hxy)).symm
  rw [he, ← vonMangoldt_sum]
  calc
    _ = ∑ p ∈ primesBetween ⌊x⌋₊ ⌊y⌋₊, vonMangoldt p := by
      apply sum_congr rfl
      intro p hp
      exact (vonMangoldt_apply_prime (mem_primesBetween.mp hp).2.2).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hlo, hhi, hprime⟩ := mem_primesBetween.mp hp
        exact Nat.mem_divisors.mpr ⟨hdiv p hprime ((Nat.floor_lt hx).mp hlo)
          ((Nat.le_floor_iff (hx.trans hxy)).mp hhi), hn⟩
      · intro p hp hnot
        exact vonMangoldt_nonneg

/-- A polynomially bounded integer cannot contain every prime in this
fixed proportional interval. The threshold is uniform in that integer. -/
lemma eventually_prime_not_dvd {A : ℝ} (hA : 0 < A) :
    ∃ B : ℕ, ∀ b : ℕ, B ≤ b → ∀ n : ℕ, 0 < n →
      (n:ℝ) ≤ A*(b:ℝ)^2 →
      ∃ p : ℕ, p.Prime ∧ (b:ℝ)/4 < p ∧ (p:ℝ) ≤ (b:ℝ)/3 ∧ ¬ p ∣ n := by
  have hlog : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hsmall : Tendsto (fun x : ℝ => (Real.log A+2*Real.log x)/x) atTop (𝓝 0) := by
    have hh := (tendsto_id.const_div_atTop (Real.log A)).add (hlog.const_mul 2)
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hh
  have hθ := eventually_theta_interval_lower (a := (1:ℝ)/4) (b := (1:ℝ)/3)
    (by norm_num) (by norm_num)
  have hsm := (tendsto_order.mp hsmall).2 (1/24) (by norm_num : (0:ℝ) < 1/24)
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop.eventually (hθ.and hsm)).and (eventually_ge_atTop (1:ℕ)))
  refine ⟨B, ?_⟩
  intro b hb n hn hsize
  obtain ⟨⟨hbθ, hbsm⟩, hb1⟩ := hB b hb
  have hbR : (0:ℝ) < b := Nat.cast_pos.mpr hb1
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hlogn : Real.log n ≤ Real.log A+2*Real.log b := by
    have hh := Real.log_le_log hnR hsize
    rw [Real.log_mul hA.ne' (pow_ne_zero _ hbR.ne'), Real.log_pow] at hh
    simpa only [Nat.cast_ofNat] using hh
  have hsmall' : Real.log A+2*Real.log b < (b:ℝ)/24 := by
    have hh := (div_lt_iff₀ hbR).mp hbsm
    linarith only [hh]
  have htheta : (b:ℝ)/24 ≤ Chebyshev.theta ((b:ℝ)/3)-Chebyshev.theta ((b:ℝ)/4) := by
    convert hbθ using 1 <;> ring_nf
  by_contra hh
  have hd : ∀ p : ℕ, p.Prime → (b:ℝ)/4 < p → (p:ℝ) ≤ (b:ℝ)/3 → p ∣ n := by
    intro p hp hlo hhi
    by_contra hnot
    exact hh ⟨p, hp, hlo, hhi, hnot⟩
  have hbound := theta_interval_le_log_of_all_dvd (by positivity : 0 ≤ (b:ℝ)/4)
    (by linarith : (b:ℝ)/4 ≤ (b:ℝ)/3) hn.ne' hd
  linarith only [htheta, hbound, hlogn, hsmall']

lemma residue_of_coprime_determinant {a b t : ℕ} (hab : a.Coprime b)
    (hb : 1 < b) (ht0 : 0 < t) (htb : t < b)
    (hat : a.Coprime t) (hbt : b.Coprime t) :
    ∃ r c : ℕ, 0 < r ∧ r < b ∧ a*r = b*c+t ∧ b.Coprime r ∧ a.Coprime c := by
  obtain ⟨u, _, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hab hb
  let r := t*u%b
  have hrb : r < b := Nat.mod_lt _ (by omega)
  have hrmod : a*r%b = t := by
    dsimp [r]
    rw [Nat.mul_mod_mod]
    calc
      a*(t*u)%b = t*(a*u)%b := by congr 1; ring
      _ = t*(a*u%b)%b := (Nat.mul_mod_mod _ _ _).symm
      _ = t := by rw [hu, mul_one, Nat.mod_eq_of_lt htb]
  have hr0 : 0 < r := by
    by_contra hh
    have hz : r = 0 := by omega
    rw [hz] at hrmod
    simp at hrmod
    omega
  have he : a*r = b*(a*r/b)+t := by
    have hh := Nat.div_add_mod (a*r) b
    rw [hrmod] at hh
    omega
  obtain ⟨hbr, hac⟩ := coprime_of_determinant he hat hbt
  exact ⟨r, a*r/b, hr0, hrb, he, hbr, hac⟩

/-- Unlike the determinant-one/two construction, the chosen determinant is
strictly inside (b/4,3b/4), uniformly for slopes in a fixed bounded range. -/
theorem exists_interior_admissible_residue {A : ℝ} (hA : 1 < A) :
    ∃ B : ℕ, ∀ a b : ℕ, a.Coprime b → b < a → (a:ℝ) ≤ A*b → B < b →
      ∃ r c t : ℕ, 0 < r ∧ r < b ∧ a*r = b*c+t ∧
        (b:ℝ)/4 < t ∧ (t:ℝ) < 3*(b:ℝ)/4 ∧
        (∀ k : ℕ, (a*k+c:ℕ)+1/4 < ((a:ℝ)/b)*(b*k+r:ℕ) ∧
          ((a:ℝ)/b)*(b*k+r:ℕ) < (a*k+c:ℕ)+3/4) ∧
        ∀ ℓ : ℕ, ℓ.Prime → ∃ k : ℕ, k ≤ 2 ∧
          ¬ ℓ ∣ b*k+r ∧ ¬ ℓ ∣ a*k+c := by
  obtain ⟨T, hT⟩ := eventually_prime_not_dvd (show 0 < A by linarith)
  refine ⟨max T 2, ?_⟩
  intro a b hab hba habound hb
  have hb2 : 2 < b := (le_max_right T 2).trans_lt hb
  have hbR : (0:ℝ) < b := Nat.cast_pos.mpr (by omega)
  have hn : 0 < a*b := Nat.mul_pos (by omega) (by omega)
  have hsize : (a*b:ℕ) ≤ A*(b:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_right habound hbR.le
    push_cast
    nlinarith only [hh]
  obtain ⟨p, hp, hplo, hphi, hpd⟩ := hT b ((le_max_left T 2).trans hb.le) (a*b) hn hsize
  obtain ⟨hpa, hpb⟩ := Nat.coprime_mul_iff_right.mp (hp.coprime_iff_not_dvd.mpr hpd)
  have ht : ∃ t : ℕ, (b:ℝ)/4 < t ∧ (t:ℝ) < 3*(b:ℝ)/4 ∧
      a.Coprime t ∧ b.Coprime t ∧ ((Odd a ∧ Odd b) → Even t) := by
    by_cases ho : Odd a ∧ Odd b
    · refine ⟨2*p, ?_, ?_, Nat.coprime_mul_iff_right.mpr
        ⟨ho.1.coprime_two_right, hpa.symm⟩,
        Nat.coprime_mul_iff_right.mpr ⟨ho.2.coprime_two_right, hpb.symm⟩, ?_⟩
      · push_cast
        linarith only [hplo, hbR]
      · push_cast
        linarith only [hphi, hbR]
      · intro _
        exact even_two_mul p
    · exact ⟨p, hplo, by linarith only [hphi, hbR], hpa.symm, hpb.symm,
        fun h => (ho h).elim⟩
  obtain ⟨t, htlo, hthi, hat, hbt, hte⟩ := ht
  have ht0 : 0 < t := Nat.cast_pos.mp (by linarith only [htlo, hbR] : (0:ℝ) < t)
  have htb : t < b := Nat.cast_lt.mp (by linarith only [hthi, hbR] : (t:ℝ) < b)
  obtain ⟨r, c, hr0, hrb, he, hbr, hac⟩ :=
    residue_of_coprime_determinant hab (by omega) ht0 htb hat hbt
  refine ⟨r, c, t, hr0, hrb, he, htlo, hthi, ?_, ?_⟩
  · intro k
    have heR : (a:ℝ)*r = (b:ℝ)*c+t := by exact_mod_cast he
    have hidentity : ((a:ℝ)/b)*(b*k+r:ℕ) = (a*k+c:ℕ)+(t:ℝ)/b := by
      push_cast
      field_simp
      nlinarith only [heR]
    rw [hidentity]
    have hl : (1:ℝ)/4 < (t:ℝ)/b := (lt_div_iff₀ hbR).mpr (by linarith only [htlo])
    have hh : (t:ℝ)/b < (3:ℝ)/4 := (div_lt_iff₀ hbR).mpr (by linarith only [hthi])
    constructor <;> linarith only [hl, hh]
  · intro ℓ hℓ
    by_cases h2 : ℓ = 2
    · subst ℓ
      obtain ⟨k, hk, hkr, hkc⟩ := two_local_residue he hbr hac hte
      exact ⟨k, hk.trans (by omega), hkr, hkc⟩
    · exact odd_prime_local_residue hbr hac hℓ h2

/-- Prime inputs can be arbitrarily large while remaining in the interior
window and making the output avoid every prime in a fixed finite modulus.
There is no upper bound on the prime input here, and the output is not
asserted to be prime. -/
theorem exists_interior_prime_input_coprime_output {A : ℝ} (hA : 1 < A) :
    ∃ B : ℕ, ∀ a b : ℕ, a.Coprime b → b < a → (a:ℝ) ≤ A*b → B < b →
      ∀ M : ℕ, M ≠ 0 → ∀ P : ℕ,
        ∃ p q : ℕ, P < p ∧ p.Prime ∧ q.Coprime M ∧
          (q:ℝ)+1/4 < ((a:ℝ)/b)*p ∧ ((a:ℝ)/b)*p < (q:ℝ)+3/4 ∧
          ⌊((a:ℝ)/b)*p⌋₊ = q := by
  obtain ⟨B, hB⟩ := exists_interior_admissible_residue hA
  refine ⟨B, ?_⟩
  intro a b hab hba habound hb M hM P
  obtain ⟨r, c, t, hr0, hrb, he, htlo, hthi, hwindow, hlocal⟩ :=
    hB a b hab hba habound hb
  have hloc : ∀ ℓ : ℕ, ℓ.Prime → ∃ k : ℕ, ¬ ℓ ∣ b*k+r ∧ ¬ ℓ ∣ a*k+c := by
    intro ℓ hℓ
    obtain ⟨k, hk, hrest⟩ := hlocal ℓ hℓ
    exact ⟨k, hrest⟩
  have hb0 : b ≠ 0 := by omega
  obtain ⟨k, hk, hp, hc⟩ := admissible_prime_input hb0 hloc M hM P
  obtain ⟨hlo, hhi⟩ := hwindow k
  refine ⟨b*k+r, a*k+c, hk, hp, hc, hlo, hhi, ?_⟩
  apply (Nat.floor_eq_iff (by positivity : 0 ≤ ((a:ℝ)/b)*(b*k+r:ℕ))).mpr
  constructor <;> linarith only [hlo, hhi]

#print axioms theta_interval_le_log_of_all_dvd
#print axioms eventually_prime_not_dvd
#print axioms exists_interior_admissible_residue
#print axioms exists_interior_prime_input_coprime_output

end Erdos972RationalInteriorAdmissibility
