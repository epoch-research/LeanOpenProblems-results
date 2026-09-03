import FormalConjecturesUtil

/-!
# Prime inputs with no successors in a finite multiplier family

For every fixed finite family of positive multipliers, there are arbitrarily
large prime inputs p for which all a*p+1 are composite. The input primes
can lie in any prescribed reduced residue class, and the blocking prime
factors can all exceed an arbitrary prescribed cutoff.

This is an obstruction to a uniform prime-successor lower bound for
arbitrary retained prime weights, not a disproof of Erdős 821.
-/
open Nat Finset
open scoped Classical BigOperators
namespace Erdos821.SuccessorAvoidance

lemma negative_inverse_residue (a q : ℕ) (hq : q.Prime) (ha : 0 < a) (haq : a < q) :
    ∃ r : ℕ, r.Coprime q ∧ q ∣ a*r+1 := by
  letI : Fact q.Prime := ⟨hq⟩
  have ha0 : (a : ZMod q) ≠ 0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff a q).mp he
    exact (Nat.not_dvd_of_pos_of_lt ha haq) hd
  let z : ZMod q := -(a : ZMod q)⁻¹
  refine ⟨z.val, ?_, ?_⟩
  · apply (ZMod.isUnit_iff_coprime _ _).mp
    rw [ZMod.natCast_zmod_val]
    exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (inv_ne_zero ha0))
  · apply (ZMod.natCast_eq_zero_iff (a*z.val+1) q).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    dsimp [z]
    rw [mul_neg, mul_inv_cancel₀ ha0]
    ring

/-- A reduced residue class carrying an explicit large prime divisor of
 every successor in the finite multiplier family. -/
theorem exists_successor_avoiding_class (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (M b K : ℕ) (hM : 0 < M) (hb : b.Coprime M) :
    ∃ D r : ℕ, 0 < D ∧ M ∣ D ∧ r.Coprime D ∧ r ≡ b [MOD M] ∧
      ∀ a ∈ A, ∃ q : ℕ, K < q ∧ q.Prime ∧ q ∣ D ∧ q ∣ a*r+1 := by
  induction A using Finset.induction with
  | empty =>
    exact ⟨M,b,hM,dvd_refl M,hb,Nat.ModEq.refl b,by simp⟩
  | @insert a A haA ih =>
    have ha : 0 < a := hA a (mem_insert_self _ _)
    have hA' : ∀ c ∈ A, 0 < c := fun c hc => hA c (mem_insert_of_mem hc)
    obtain ⟨D,r,hD,hMD,hrD,hrb,Hr⟩ := ih hA'
    obtain ⟨q,hqbig,hq⟩ := Nat.exists_infinite_primes (D+a+K+1)
    have hqD : D < q := by omega
    have haq : a < q := by omega
    have hKq : K < q := by omega
    have hDq : D.Coprime q := (Nat.coprime_of_lt_prime hD.ne' hqD hq).symm
    obtain ⟨s,hs,hroot⟩ := negative_inverse_residue a q hq ha haq
    obtain ⟨r',hr'D,hr'q⟩ := Nat.chineseRemainder hDq r s
    have hcopD : r'.Coprime D := by
      change Nat.gcd r' D=1
      rw [hr'D.gcd_eq]
      exact hrD
    have hcopq : r'.Coprime q := by
      change Nat.gcd r' q=1
      rw [hr'q.gcd_eq]
      exact hs
    refine ⟨D*q,r',Nat.mul_pos hD hq.pos,hMD.trans (Nat.dvd_mul_right D q),
      hcopD.mul_right hcopq,(hr'D.of_dvd hMD).trans hrb,?_⟩
    intro c hc
    rcases mem_insert.mp hc with rfl | hc
    · refine ⟨q,hKq,hq,Nat.dvd_mul_left q D,?_⟩
      exact (((hr'q.mul_left c).add_right 1).dvd_iff (dvd_refl q)).mpr hroot
    · obtain ⟨l,hKl,hl,hlD,hld⟩ := Hr c hc
      refine ⟨l,hKl,hl,hlD.trans (Nat.dvd_mul_right D q),?_⟩
      exact (((hr'D.mul_left c).add_right 1).dvd_iff hlD).mpr hld

/-- The blocking factors are proper divisors once the prime input exceeds
 the constructed modulus. Dirichlet supplies arbitrarily large inputs. -/
theorem exists_prime_no_successors (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (M b K T : ℕ) (hM : 0 < M) (hb : b.Coprime M) :
    ∃ p : ℕ, T < p ∧ p.Prime ∧ p ≡ b [MOD M] ∧
      ∀ a ∈ A, ∃ q : ℕ, K < q ∧ q.Prime ∧ q ∣ a*p+1 ∧ q < a*p+1 := by
  obtain ⟨D,r,hD,hMD,hrD,hrb,Hr⟩ := exists_successor_avoiding_class A hA M b K hM hb
  obtain ⟨p,hpbig,hp,hpr⟩ := Nat.forall_exists_prime_gt_and_modEq (D+T) hD.ne' hrD
  refine ⟨p,by omega,hp,(hpr.of_dvd hMD).trans hrb,?_⟩
  intro a ha
  obtain ⟨q,hKq,hq,hqD,hqar⟩ := Hr a ha
  have hqp : q < p := (Nat.le_of_dvd hD hqD).trans_lt (by omega)
  have hpa : p ≤ a*p := by
    simpa using Nat.mul_le_mul_right p (hA a ha)
  exact ⟨q,hKq,hq,(((hpr.mul_left a).add_right 1).dvd_iff hqD).mpr hqar,by omega⟩

theorem infinite_primes_no_successors (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (M b : ℕ) (hM : 0 < M) (hb : b.Coprime M) :
    {p : ℕ | p.Prime ∧ p ≡ b [MOD M] ∧ ∀ a ∈ A, ¬(a*p+1).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro T
  obtain ⟨p,hTp,hp,hpb,H⟩ := exists_prime_no_successors A hA M b 0 T hM hb
  refine ⟨p,⟨hp,hpb,?_⟩,hTp⟩
  intro a ha
  obtain ⟨q,_hKq,hq,hqd,hqlt⟩ := H a ha
  exact Nat.not_prime_of_dvd_of_lt hqd hq.two_le hqlt

/-- In particular all positive products in a finite rectangle can be
blocked, using only prime factors above the chosen cutoff. -/
theorem exists_prime_no_rectangle_successors (B C K T : ℕ) :
    ∃ p : ℕ, T < p ∧ p.Prime ∧ ∀ a ∈ Icc 1 B, ∀ b ∈ Icc 1 C,
      ∃ q : ℕ, K < q ∧ q.Prime ∧ q ∣ a*b*p+1 ∧ q < a*b*p+1 := by
  let A := ((Icc 1 B) ×ˢ (Icc 1 C)).image (fun ab => ab.1*ab.2)
  have hA : ∀ a ∈ A, 0 < a := by
    intro a ha
    obtain ⟨⟨i,j⟩,hij,rfl⟩ := mem_image.mp ha
    obtain ⟨hi,hj⟩ := mem_product.mp hij
    exact Nat.mul_pos (mem_Icc.mp hi).1 (mem_Icc.mp hj).1
  obtain ⟨p,hTp,hp,_hmod,H⟩ := exists_prime_no_successors A hA 1 1 K T (by decide) (by decide)
  refine ⟨p,hTp,hp,?_⟩
  intro a ha b hb
  exact H (a*b) (mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,rfl⟩)

end Erdos821.SuccessorAvoidance
