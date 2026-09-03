import Submission.FullFiberOverlap

/-!
Weighted pigeonhole counting of the modular gap matches embedded into actual
full-fiber overlaps. These estimates do not apply to arbitrary partial fibers.
-/
namespace Erdos773.FullFiberOverlapCount
open Finset PartialResidueFibers PartialFiberSelection FullFiberOverlap
set_option maxHeartbeats 2000000

section FiniteHash
variable {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Weighted collision energy of a finite hash, with a label that distinguishes
all colliding distinct elements. -/
theorem hash_energy (T : Finset α) (hash : α → β) (label : α → ℕ) (w : α → ℝ)
    (hunique : ∀ a ∈ T, ∀ b ∈ T, label a=label b → hash a=hash b → a=b) :
    (∑ a ∈ T, w a)^2 ≤ (Fintype.card β : ℝ)*
      ((∑ a ∈ T, w a^2) + 2*(∑ ab ∈ (T ×ˢ T).filter
        (fun ab => label ab.1 < label ab.2 ∧ hash ab.1=hash ab.2), w ab.1*w ab.2)) := by
  classical
  let F (d : β) : ℝ := ∑ a ∈ T, if hash a=d then w a else 0
  have hsum : (∑ d : β, F d)=∑ a ∈ T, w a := by
    dsimp [F]
    rw [sum_comm]
    simp
  have hexpand : (∑ d : β, F d^2) =
      ∑ a ∈ T, ∑ b ∈ T, if hash a=hash b then w a*w b else 0 := by
    calc
      _ = ∑ d : β, ∑ a ∈ T, ∑ b ∈ T,
          if hash a=d ∧ hash b=d then w a*w b else 0 := by
        apply sum_congr rfl
        intro d _
        dsimp [F]
        rw [pow_two,sum_mul]
        apply sum_congr rfl
        intro a ha
        rw [mul_sum]
        apply sum_congr rfl
        intro b hb
        by_cases ha : hash a=d <;> by_cases hb : hash b=d <;> simp [ha,hb]
      _ = ∑ a ∈ T, ∑ b ∈ T, ∑ d : β,
          if hash a=d ∧ hash b=d then w a*w b else 0 := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a ha
        rw [sum_comm]
      _ = _ := by
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro b hb
        by_cases he : hash a=hash b
        · simp [he]
        · have hn (d : β) : ¬(hash a=d ∧ hash b=d) := by rintro ⟨ha,hb⟩; exact he (ha.trans hb.symm)
          simp [hn,he]
  have hterm (a : α) (ha : a ∈ T) (b : α) (hb : b ∈ T) :
      (if hash a=hash b then w a*w b else 0) =
        (if a=b then w a^2 else 0) +
        (if label a<label b ∧ hash a=hash b then w a*w b else 0) +
        (if label b<label a ∧ hash b=hash a then w b*w a else 0) := by
    by_cases he : hash a=hash b
    · rcases lt_trichotomy (label a) (label b) with hl | hl | hl
      · have hab : a ≠ b := by intro h; subst b; omega
        simp [he,hl,not_lt_of_ge hl.le,hab]
      · have hab := hunique a ha b hb hl he
        subst b
        simp [pow_two]
      · have hab : a ≠ b := by intro h; subst b; omega
        simp only [if_pos he,hab,if_false,hl,not_lt_of_ge hl.le,false_and,if_false,true_and,if_pos he.symm,zero_add]
        ring
    · have hab : a ≠ b := fun h => he (congrArg hash h)
      simp [he,Ne.symm he,hab]
  have hdiag : (∑ a ∈ T, ∑ b ∈ T, if a=b then w a^2 else 0)=∑ a ∈ T, w a^2 := by simp
  have hswap : (∑ a ∈ T, ∑ b ∈ T,
      if label b<label a ∧ hash b=hash a then w b*w a else 0) =
      ∑ a ∈ T, ∑ b ∈ T, if label a<label b ∧ hash a=hash b then w a*w b else 0 := sum_comm
  have hsplit : (∑ d : β, F d^2) = (∑ a ∈ T, w a^2) +
      2*(∑ ab ∈ (T ×ˢ T).filter (fun ab => label ab.1<label ab.2 ∧ hash ab.1=hash ab.2),
        w ab.1*w ab.2) := by
    rw [hexpand, sum_filter, sum_product]
    have hh : (∑ a ∈ T, ∑ b ∈ T, if hash a=hash b then w a*w b else 0) =
        (∑ a ∈ T, ∑ b ∈ T, if a=b then w a^2 else 0) +
        (∑ a ∈ T, ∑ b ∈ T, if label a<label b ∧ hash a=hash b then w a*w b else 0) +
        (∑ a ∈ T, ∑ b ∈ T, if label b<label a ∧ hash b=hash a then w b*w a else 0) := by
      simp_rw [← sum_add_distrib]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact hterm a ha b hb
    rw [hh,hdiag,hswap]
    ring
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset β) F (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one] at hc
  rw [hsum,hsplit] at hc
  simpa only [mul_comm] using hc

end FiniteHash

/-- Weighted count of modular matches for an interval of L+1 gaps. -/
theorem short_weight_pigeonhole (q L : ℕ) (R : Finset ℕ) (hq : 0 < q)
    (hLq : 2*L < q) (hunit : ∀ r ∈ R, q.Coprime r) (p : ℕ → ℝ) :
    ((L+1 : ℕ)*(∑ r ∈ R, p r^2) : ℝ)^2 ≤ (q : ℝ)*
      (((L+1 : ℕ) : ℝ)*(∑ r ∈ R, p r^4) +
        2*(∑ k ∈ shortKeys q L R, p k.1.1^2*p k.2.1^2)) := by
  classical
  let T := R ×ˢ Icc L (2*L)
  let hash : ℕ × ℕ → Fin q := fun a => ⟨a.1*a.2%q,Nat.mod_lt _ hq⟩
  have hu : ∀ a ∈ T, ∀ b ∈ T, a.1=b.1 → hash a=hash b → a=b := by
    intro a ha b hb hr he
    have hh := congrArg Fin.val he
    change a.1*a.2 ≡ b.1*b.2 [MOD q] at hh
    rw [← hr] at hh
    have hcan := hh.cancel_left_of_coprime (hunit a.1 (mem_product.mp ha).1)
    have ha' := (mem_Icc.mp (mem_product.mp ha).2).2
    have hb' := (mem_Icc.mp (mem_product.mp hb).2).2
    exact Prod.ext hr (hcan.eq_of_lt_of_lt (by omega) (by omega))
  have hh := hash_energy T hash Prod.fst (fun a => p a.1^2) hu
  have heq : ((T ×ˢ T).filter (fun ab => ab.1.1 < ab.2.1 ∧ hash ab.1=hash ab.2)) =
      shortKeys q L R := by
    ext k
    simp only [shortKeys,mem_filter]
    simp only [hash,Fin.mk.injEq,Nat.ModEq]
    rfl
  rw [heq] at hh
  have hcard : (Icc L (2*L)).card=L+1 := by rw [Nat.card_Icc]; omega
  have hs2 : (∑ a ∈ T, p a.1^2)=((L+1 : ℕ) : ℝ)*(∑ r ∈ R, p r^2) := by
    rw [sum_product]
    simp [hcard,← mul_sum]
  have hs4 : (∑ a ∈ T, (p a.1^2)^2)=((L+1 : ℕ) : ℝ)*(∑ r ∈ R, p r^4) := by
    rw [sum_product]
    simp [hcard,← pow_mul,← mul_sum]
  rw [hs2,hs4,Fintype.card_fin] at hh
  exact hh

/-- Every short modular collision counted by pigeonhole is paid for by the
actual full-fiber overlap budget. -/
theorem full_weight_pigeonhole (q L : ℕ) (R : Finset ℕ) (hq : q.Prime)
    (hL : 0 < L) (hqL : 10*L ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r)) (p : ℕ → ℝ) :
    ((L+1 : ℕ)*(∑ r ∈ R, p r^2) : ℝ)^2 ≤ (q : ℝ)*
      (((L+1 : ℕ) : ℝ)*(∑ r ∈ R, p r^4) +
        2*(∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2)) := by
  have hh := short_weight_pigeonhole q L R hq.pos (by omega)
    (fun r hr => Nat.Coprime.of_dvd_right (dvd_mul_left r 2) (hunit r hr)) p
  have hc := prime_shortKeys_weight_le q L R hq hL hqL hR hunit p
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith only [hh,mul_le_mul_of_nonneg_left hc hq0]

#print axioms short_weight_pigeonhole
#print axioms full_weight_pigeonhole
end Erdos773.FullFiberOverlapCount
