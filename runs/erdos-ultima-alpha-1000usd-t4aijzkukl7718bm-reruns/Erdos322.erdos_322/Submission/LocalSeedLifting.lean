import Submission.LocalSeedDensity

/-! Lifting every nonsingular first-coordinate seed removes the prime-size
loss from the critical local density bound for even exponents. -/
namespace Erdos322Research.LocalSeedLifting
noncomputable section
open Finset LocalPowerRoots LocalPeakCounting LocalSeedDensity
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

private def tailCoordinate (p e k : ℕ) [Fact p.Prime]
    (s : FirstSeeds k p) (t : Fin (k+1) → Fin (p^e)) (j : Fin (k+1)) : Fin (p^(e+1)) :=
  ⟨(s.val j.succ).val+p*(t j : ℕ),by
    have hs := ZMod.val_lt (s.val j.succ)
    have ht := (t j).isLt
    rw [pow_succ]
    nlinarith⟩

private lemma tailCoordinate_reduction (p e k : ℕ) [Fact p.Prime]
    (s : FirstSeeds k p) (t : Fin (k+1) → Fin (p^e)) (j : Fin (k+1)) :
    reduction p e ((tailCoordinate p e k s t j : ℕ) : ZMod (p^(e+1)))=s.val j.succ := by
  rw [reduction_natCast]
  simp only [tailCoordinate,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,
    zero_mul,add_zero,ZMod.natCast_zmod_val]

private theorem exists_first_coordinate (p e k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (s : FirstSeeds k p) (t : Fin (k+1) → Fin (p^e)) :
    ∃ x : Fin (p^(e+1)), ((x : ℕ) : ZMod p)=s.val 0 ∧
      p^(e+1) ∣ (x : ℕ)^(k+2)+∑ j, (tailCoordinate p e k s t j : ℕ)^(k+2) := by
  let b : Fin (k+1) → ZMod (p^(e+1)) := fun j ↦ (tailCoordinate p e k s t j : ℕ)
  have hb : reduction p e (-∑ j, b j^(k+2))=(s.val 0)^(k+2) := by
    simp only [map_neg,map_sum,map_pow,b,tailCoordinate_reduction]
    have hs := s.property.1
    rw [Fin.sum_univ_succ] at hs
    linear_combination -hs
  obtain ⟨x,hx,hxpow⟩ := exists_pow_root p e (k+2) hk (s.val 0) s.property.2
    (-∑ j, b j^(k+2)) hb
  refine ⟨⟨x.val,ZMod.val_lt x⟩,?_,?_⟩
  · change (x.val : ZMod p)=s.val 0
    rw [← reduction_natCast p e,ZMod.natCast_zmod_val]
    exact hx
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [ZMod.natCast_zmod_val,hxpow]
    exact neg_add_cancel _

private def liftedRoot (p e k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (s : FirstSeeds k p) (t : Fin (k+1) → Fin (p^e)) :
    Roots (k+2) (p^(e+1)) :=
  ⟨Fin.cons (exists_first_coordinate p e k hk s t).choose (tailCoordinate p e k s t),by
    simpa only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ] using
      (exists_first_coordinate p e k hk s t).choose_spec.2⟩

private lemma liftedRoot_reduction (p e k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (s : FirstSeeds k p) (t : Fin (k+1) → Fin (p^e))
    (i : Fin (k+2)) : (((liftedRoot p e k hk s t).val i : ℕ) : ZMod p)=s.val i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact (exists_first_coordinate p e k hk s t).choose_spec.1
  · change ((tailCoordinate p e k s t j : ℕ) : ZMod p)=s.val j.succ
    rw [← reduction_natCast p e]
    exact tailCoordinate_reduction p e k s t j

private lemma liftedRoot_first (p e k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (s : FirstSeeds k p) (t : Fin (k+1) → Fin (p^e)) :
    ¬p ∣ ((liftedRoot p e k hk s t).val 0 : ℕ) := by
  intro hd
  apply s.property.2
  rw [← liftedRoot_reduction p e k hk s t 0]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hd

private lemma liftedRoot_injective (p e k : ℕ) [Fact p.Prime] (hk : ¬p ∣ k+2) :
    Function.Injective (fun z : FirstSeeds k p × (Fin (k+1) → Fin (p^e)) ↦
      liftedRoot p e k hk z.1 z.2) := by
  rintro ⟨s,t⟩ ⟨v,u⟩ h
  have hsv : s=v := by
    apply Subtype.ext
    funext i
    have hh := congrArg (fun x : Roots (k+2) (p^(e+1)) ↦ ((x.val i : ℕ) : ZMod p)) h
    simpa only [liftedRoot_reduction] using hh
  subst v
  refine Prod.ext rfl ?_
  funext j
  apply Fin.ext
  have hh := congrArg (fun x : Roots (k+2) (p^(e+1)) ↦ (x.val j.succ : ℕ)) h
  change (s.val j.succ).val+p*(t j : ℕ)=(s.val j.succ).val+p*(u j : ℕ) at hh
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos (Nat.add_left_cancel hh)

/-- Each nonsingular seed lifts independently with all tail digits free. -/
theorem primitive_seed_count_lower (p e k : ℕ) [Fact p.Prime] (hk : ¬p ∣ k+2) :
    firstSeedCount k p*p^(e*(k+1)) ≤
      Fintype.card {x : Roots (k+2) (p^(e+1)) // ¬p ∣ (x.val 0 : ℕ)} := by
  let f : (FirstSeeds k p × (Fin (k+1) → Fin (p^e))) →
      {x : Roots (k+2) (p^(e+1)) // ¬p ∣ (x.val 0 : ℕ)} :=
    fun z ↦ ⟨liftedRoot p e k hk z.1 z.2,liftedRoot_first p e k hk z.1 z.2⟩
  have hf : Function.Injective f := by
    intro x y h
    exact liftedRoot_injective p e k hk (congrArg Subtype.val h)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [firstSeedCount,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,← pow_mul] using hh

/-- Nonsingular seed contributions and all-p-divisible roots are disjoint. -/
theorem rootCount_seed_step (p m k : ℕ) [Fact p.Prime] (hk : ¬p ∣ k+2) :
    firstSeedCount k p*p^((m+k+1)*(k+1))+
      rootCount (k+2) (p^m)*p^((k+2)*(k+1)) ≤ rootCount (k+2) (p^(m+k+2)) := by
  let P : Roots (k+2) (p^(m+k+2)) → Prop := fun x ↦ p ∣ (x.val 0 : ℕ)
  have hprim : firstSeedCount k p*p^((m+k+1)*(k+1)) ≤ Fintype.card {x // ¬P x} := by
    simpa only [P,Nat.add_assoc] using primitive_seed_count_lower p (m+k+1) k hk
  have hdiv : rootCount (k+2) (p^m)*p^((k+2)*(k+1)) ≤ Fintype.card {x // P x} := by
    have hd := divisible_count_lower p (p^m) k (Fact.out : p.Prime).pos
      (pow_pos (Fact.out : p.Prime).pos _)
    rw [← pow_add,show k+2+m=m+k+2 by omega] at hd
    exact hd
  have hcard := Fintype.card_subtype_compl P
  have hle := Fintype.card_subtype_le P
  change Fintype.card {x // ¬P x}=rootCount (k+2) (p^(m+k+2))-Fintype.card {x // P x} at hcard
  change Fintype.card {x // P x} ≤ rootCount (k+2) (p^(m+k+2)) at hle
  omega

/-- Critical growth, weighted by the number of available nonsingular seeds. -/
theorem rootCount_seed_growth (p k : ℕ) [Fact p.Prime] (hk : ¬p ∣ k+2) (d : ℕ) :
    (d+1)*firstSeedCount k p*p^((k+2)*d*(k+1)) ≤ rootCount (k+2) (p^((k+2)*d+1)) := by
  induction d with
  | zero =>
    have hprim := primitive_seed_count_lower p 0 k hk
    have hle := Fintype.card_subtype_le (fun x : Roots (k+2) (p^(0+1)) ↦ ¬p ∣ (x.val 0 : ℕ))
    simpa only [mul_zero,zero_mul,pow_zero,zero_add,one_mul] using hprim.trans hle
  | succ d ih =>
    have hs := rootCount_seed_step p ((k+2)*d+1) k hk
    have hE : ((k+2)*d+1+k+1)*(k+1)=(k+2)*(d+1)*(k+1) := by ring
    have hM : (k+2)*d+1+k+2=(k+2)*(d+1)+1 := by ring
    rw [hE,hM] at hs
    calc
      (d+1+1)*firstSeedCount k p*p^((k+2)*(d+1)*(k+1)) =
          firstSeedCount k p*p^((k+2)*(d+1)*(k+1))+
          ((d+1)*firstSeedCount k p*p^((k+2)*d*(k+1)))*p^((k+2)*(k+1)) := by
        rw [show (k+2)*(d+1)*(k+1)=(k+2)*d*(k+1)+(k+2)*(k+1) by ring,pow_add]
        ring
      _ ≤ firstSeedCount k p*p^((k+2)*(d+1)*(k+1))+
          rootCount (k+2) (p^((k+2)*d+1))*p^((k+2)*(k+1)) := by gcongr
      _ ≤ _ := hs

/-- The normalized local density grows uniformly with depth, losing only
2k rather than a power of the prime. -/
theorem uniform_even_local_density (p k : ℕ) [Fact p.Prime] (hk : ¬p ∣ k+2)
    (he : Even (k+2)) (a : ZMod p) (ha : a^(k+2)+1=0) (d : ℕ) :
    (d+1)*(p^((k+2)*d+1))^(k+1) ≤
      (2*(k+2))*rootCount (k+2) (p^((k+2)*d+1)) := by
  have hs := first_seed_density k p he a ha
  have hg := rootCount_seed_growth p k hk d
  calc
    (d+1)*(p^((k+2)*d+1))^(k+1) =
        (d+1)*p^(k+1)*p^((k+2)*d*(k+1)) := by
      rw [← pow_mul,show ((k+2)*d+1)*(k+1)=(k+1)+(k+2)*d*(k+1) by ring,pow_add]
      ring
    _ ≤ (d+1)*((2*(k+2))*firstSeedCount k p)*p^((k+2)*d*(k+1)) := by gcongr
    _ = (2*(k+2))*((d+1)*firstSeedCount k p*p^((k+2)*d*(k+1))) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hg

end
end Erdos322Research.LocalSeedLifting
