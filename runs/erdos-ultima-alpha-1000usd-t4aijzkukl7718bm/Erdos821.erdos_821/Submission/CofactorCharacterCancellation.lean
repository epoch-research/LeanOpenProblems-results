import Submission.CompositeCharacterErrors
import Submission.SharpPairSieve

/-!
# Cancellation in cofactor intervals at small primitive conductors

The estimate is uniform in the endpoints and in the lifted modulus. The
prime-weighted factor can remain completely untreated: the cancellation
comes from the unweighted cofactor interval, before taking absolute values.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 2000000

lemma sum_multiples_natural_interval {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (A B d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Icc (A+1) B with d ∣ n, f n) =
      ∑ k ∈ Icc (A/d+1) (B/d), f (d*k) := by
  have hset : (Icc (A+1) B).filter (fun n => d ∣ n) =
      (Icc (A/d+1) (B/d)).image (fun k => d*k) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnI,hdn⟩ := mem_filter.mp hn
      have he : d*(n/d)=n := Nat.mul_div_cancel' hdn
      refine mem_image.mpr ⟨n/d,mem_Icc.mpr ⟨?_,Nat.div_le_div_right (mem_Icc.mp hnI).2⟩,he⟩
      have hnA : A < (n/d)*d := by rw [mul_comm _ d,he]; exact (mem_Icc.mp hnI).1
      exact Nat.succ_le_iff.mpr ((Nat.div_lt_iff_lt_mul hd).mpr hnA)
    · intro hn
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
      obtain ⟨hkA,hkB⟩ := mem_Icc.mp hk
      have hA := (Nat.div_lt_iff_lt_mul hd).mp (show A/d < k by omega)
      have hB := (Nat.le_div_iff_mul_le hd).mp hkB
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by simpa only [mul_comm] using hA,
        by simpa only [mul_comm] using hB⟩,Nat.dvd_mul_right _ _⟩
  rw [hset,sum_image (by intro a ha b hb he; exact Nat.eq_of_mul_eq_mul_left hd he)]

lemma polya_vinogradov_natural_interval {c : ℕ} (hc : 2 ≤ c)
    (ψ : DirichletCharacter ℂ c) (hψ : ψ.IsPrimitive) (A B : ℕ) :
    ‖∑ n ∈ Icc (A+1) B, ψ (n : ZMod c)‖ ≤ Real.sqrt c*(1+Real.log c) := by
  letI : NeZero c := ⟨by omega⟩
  have hh := polya_vinogradov hc hψ ((A+1 : ℕ) : ℤ) (B-A)
  rw [show Icc (A+1) B = Ico (A+1) (B+1) by ext n; simp,
    sum_Ico_eq_sum_range]
  simpa only [intervalCharacterSum,Nat.add_sub_add_right,Nat.cast_add,
    Int.cast_add,Int.cast_natCast] using hh

noncomputable def primeSiftedCharacter {c : ℕ} (ψ : DirichletCharacter ℂ c)
    (P : Finset ℕ) (n : ℕ) : ℂ :=
  if ∀ p ∈ P, ¬p ∣ n then ψ (n : ZMod c) else 0

lemma primeSiftedCharacter_insert {c : ℕ} (ψ : DirichletCharacter ℂ c)
    (P : Finset ℕ) (p n : ℕ) :
    primeSiftedCharacter ψ (insert p P) n = primeSiftedCharacter ψ P n-
      (if p ∣ n then primeSiftedCharacter ψ P n else 0) := by
  simp only [primeSiftedCharacter,Finset.forall_mem_insert]
  split_ifs <;> simp_all

lemma primeSiftedCharacter_prime_mul {c : ℕ} (ψ : DirichletCharacter ℂ c)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : p.Prime)
    (hpP : p ∉ P) (n : ℕ) :
    primeSiftedCharacter ψ P (p*n) = ψ (p : ZMod c)*primeSiftedCharacter ψ P n := by
  have havoid : (∀ q ∈ P, ¬q ∣ p*n) ↔ (∀ q ∈ P, ¬q ∣ n) := by
    apply forall₂_congr
    intro q hq
    have hqp : ¬q ∣ p := by
      intro hh
      have he := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hh
      exact hpP (he ▸ hq)
    rw [(hP q hq).dvd_mul]
    simp only [hqp,false_or]
  simp only [primeSiftedCharacter,havoid,Nat.cast_mul,map_mul]
  split_ifs <;> simp

/-- Removing each additional prime costs at most a factor two, while the
interval bound remains independent of both endpoints. -/
lemma primeSiftedCharacter_interval_bound {c : ℕ} (ψ : DirichletCharacter ℂ c)
    (M : ℝ)
    (H : ∀ A B : ℕ, ‖∑ n ∈ Icc (A+1) B, ψ (n : ZMod c)‖ ≤ M)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (A B : ℕ) :
    ‖∑ n ∈ Icc (A+1) B, primeSiftedCharacter ψ P n‖ ≤ (2 : ℝ)^P.card*M := by
  induction P using Finset.induction generalizing A B with
  | empty => simpa [primeSiftedCharacter] using H A B
  | @insert p P hpP ih =>
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have he : (∑ n ∈ Icc (A+1) B, primeSiftedCharacter ψ (insert p P) n) =
        (∑ n ∈ Icc (A+1) B, primeSiftedCharacter ψ P n)-
          ψ (p : ZMod c)*(∑ n ∈ Icc (A/p+1) (B/p), primeSiftedCharacter ψ P n) := by
      simp_rw [primeSiftedCharacter_insert]
      rw [sum_sub_distrib,← sum_filter,sum_multiples_natural_interval _ A B p hp.pos]
      simp_rw [primeSiftedCharacter_prime_mul ψ P hP' p hp hpP]
      rw [← mul_sum]
    rw [he,card_insert_of_notMem hpP,pow_succ]
    calc
      _ ≤ ‖∑ n ∈ Icc (A+1) B, primeSiftedCharacter ψ P n‖+
          ‖ψ (p : ZMod c)*(∑ n ∈ Icc (A/p+1) (B/p), primeSiftedCharacter ψ P n)‖ :=
        norm_sub_le _ _
      _ ≤ (2 : ℝ)^P.card*M+1*((2 : ℝ)^P.card*M) := by
        apply add_le_add (ih hP' A B)
        rw [norm_mul]
        exact mul_le_mul (ψ.norm_le_one _) (ih hP' (A/p) (B/p)) (norm_nonneg _) (by norm_num)
      _ = _ := by ring

lemma coprime_iff_avoid_primeFactors (n d : ℕ) (hd : d ≠ 0) :
    n.Coprime d ↔ ∀ p ∈ d.primeFactors, ¬p ∣ n := by
  constructor
  · intro h p hp hpn
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p,Nat.prime_of_mem_primeFactors hp,hpn,Nat.dvd_of_mem_primeFactors hp⟩) h
  · intro h
    by_contra hh
    obtain ⟨p,hp,hpn,hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
    exact h p (Nat.mem_primeFactors.mpr ⟨hp,hpd,hd⟩) hpn

lemma changeLevel_eq_primeSiftedCharacter {c d : ℕ} (hcd : c ∣ d) (hd : d ≠ 0)
    (ψ : DirichletCharacter ℂ c) (n : ℕ) :
    (DirichletCharacter.changeLevel hcd ψ) (n : ZMod d) =
      primeSiftedCharacter ψ d.primeFactors n := by
  simp only [changeLevel_apply_nat,primeSiftedCharacter,coprime_iff_avoid_primeFactors n d hd]

/-- A conductor-sensitive Pólya--Vinogradov estimate for lifted characters. -/
theorem changeLevel_interval_character_bound {c d : ℕ} (hcd : c ∣ d)
    (hc : 2 ≤ c) (hd : d ≠ 0) (ψ : DirichletCharacter ℂ c)
    (hψ : ψ.IsPrimitive) (A B : ℕ) :
    ‖∑ n ∈ Icc (A+1) B, (DirichletCharacter.changeLevel hcd ψ) (n : ZMod d)‖ ≤
      (2 : ℝ)^d.primeFactors.card*(Real.sqrt c*(1+Real.log c)) := by
  simp_rw [changeLevel_eq_primeSiftedCharacter hcd hd ψ]
  apply primeSiftedCharacter_interval_bound ψ _
    (polya_vinogradov_natural_interval hc ψ hψ) d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-- The same estimate expressed using the actual conductor of a nonprincipal
character. No estimate for its prime-weighted sum is assumed. -/
theorem cofactor_character_interval_bound {d : ℕ} (hd : d ≠ 0)
    (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) (A B : ℕ) :
    ‖∑ n ∈ Icc (A+1) B, χ (n : ZMod d)‖ ≤ (2 : ℝ)^d.primeFactors.card*
      (Real.sqrt χ.conductor*(1+Real.log χ.conductor)) := by
  have hc0 : 0 < χ.conductor := Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (Nat.pos_of_ne_zero hd)
  have hc1 : χ.conductor ≠ 1 := by
    intro he
    exact hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one hd).mpr he)
  have hh := changeLevel_interval_character_bound χ.conductor_dvd_level (by omega)
    hd χ.primitiveCharacter χ.primitiveCharacter_isPrimitive A B
  rw [← character_eq_lift_primitive χ] at hh
  exact hh

/-- A fixed subpower bound absorbs the number of deleted local factors,
uniformly in the growing lifted modulus. -/
theorem exists_uniform_cofactor_character_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, d ≠ 0 →
      ∀ χ : DirichletCharacter ℂ d, χ ≠ 1 → ∀ A B : ℕ,
        ‖∑ n ∈ Icc (A+1) B, χ (n : ZMod d)‖ ≤
          C*(d : ℝ)^ε*(Real.sqrt χ.conductor*(1+Real.log χ.conductor)) := by
  obtain ⟨C,hC,HC⟩ := Sieve.exists_card_pow_le_const_product_rpow 2 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro d hd χ hχ A B
  apply (cofactor_character_interval_bound hd χ hχ A B).trans
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_natCast_nonneg χ.conductor]))
  apply (HC d.primeFactors (fun p hp => Nat.pos_of_mem_primeFactors hp)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (Nat.prod_primeFactors_dvd d))) hε.le

end Erdos821.AnalyticSieve
