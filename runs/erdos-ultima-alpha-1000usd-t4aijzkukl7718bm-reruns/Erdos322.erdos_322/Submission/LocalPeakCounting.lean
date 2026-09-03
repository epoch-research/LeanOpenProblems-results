import Submission.LocalPowerRoots

/-! Prime-power congruence concentration and exact representation counts. -/
namespace Erdos322Research.LocalPeakCounting
noncomputable section
open Finset LocalPowerRoots
set_option maxHeartbeats 0

/-- Ordered tuples in a box whose power sum vanishes modulo the box length. -/
abbrev Roots (k q : ℕ) := {x : Fin k → Fin q // q ∣ ∑ i, (x i : ℕ)^k}

def rootCount (k q : ℕ) : ℕ := Fintype.card (Roots k q)

/-- A nonsingular zero modulo some prime exists for every power at least two. -/
theorem exists_good_prime (k : ℕ) (hk : 2 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ k ∧ ∃ a : ZMod p, a ≠ 0 ∧ a^k+1=0 := by
  have hb : 0 < (2*k)^k := pow_pos (by omega) _
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show (2*k)^k+1 ≠ 1 by omega)
  have hn : ¬p ∣ 2*k := by
    intro hh
    have hh' : p ∣ (2*k)^k := dvd_pow hh (by omega : k ≠ 0)
    have h1 : p ∣ 1 := by simpa using Nat.dvd_sub hd hh'
    exact hp.not_dvd_one h1
  refine ⟨p,hp,fun h ↦ hn (dvd_mul_of_dvd_right h 2),(2*k : ℕ),?_,?_⟩
  · exact (ZMod.natCast_eq_zero_iff _ _).not.mpr hn
  · have hh := (ZMod.natCast_eq_zero_iff ((2*k)^k+1) p).mpr hd
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hh

variable {k p q : ℕ}

private def liftTuple (hp : 0 < p) (hq : 0 < q) (hk : 0 < k)
    (x : Roots k q) (t : Fin k → Fin (p^(k-1))) : Fin k → Fin (p^k*q) :=
  fun i ↦ ⟨p*((x.val i : ℕ)+q*(t i : ℕ)),by
    have hx := (x.val i).isLt
    have ht := (t i).isLt
    have hb : (x.val i : ℕ)+q*(t i : ℕ)<q*p^(k-1) := by nlinarith
    have hh := Nat.mul_lt_mul_of_pos_left hb hp
    have he : p*(q*p^(k-1))=p^k*q := by
      calc
        p*(q*p^(k-1))=(p^(k-1)*p)*q := by ring
        _ = p^k*q := by rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ k)]
    simpa only [he] using hh⟩

private lemma liftTuple_root (hp : 0 < p) (hq : 0 < q) (hk : 0 < k)
    (x : Roots k q) (t : Fin k → Fin (p^(k-1))) :
    p^k*q ∣ ∑ i, (liftTuple hp hq hk x t i : ℕ)^k := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hh : q ∣ ∑ i, ((x.val i : ℕ)+q*(t i : ℕ))^k := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    simp only [ZMod.natCast_self,zero_mul,add_zero]
    have hx := (ZMod.natCast_eq_zero_iff _ _).mpr x.property
    simpa only [Nat.cast_sum,Nat.cast_pow] using hx
  have hd := Nat.mul_dvd_mul_left (p^k) hh
  simpa only [liftTuple,mul_pow,← Finset.mul_sum] using hd

private def liftRoot (hp : 0 < p) (hq : 0 < q) (hk : 0 < k)
    (x : Roots k q) (t : Fin k → Fin (p^(k-1))) : Roots k (p^k*q) :=
  ⟨liftTuple hp hq hk x t,liftTuple_root hp hq hk x t⟩

private lemma liftRoot_injective (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) :
    Function.Injective (fun z : Roots k q × (Fin k → Fin (p^(k-1))) ↦
      liftRoot hp hq hk z.1 z.2) := by
  rintro ⟨x,t⟩ ⟨y,u⟩ h
  have he (i : Fin k) : (x.val i : ℕ)+q*(t i : ℕ)=(y.val i : ℕ)+q*(u i : ℕ) := by
    have hh := congrArg (fun z : Roots k (p^k*q) ↦ (z.val i : ℕ)) h
    change p*((x.val i : ℕ)+q*(t i : ℕ))=p*((y.val i : ℕ)+q*(u i : ℕ)) at hh
    exact Nat.eq_of_mul_eq_mul_left hp hh
  have hxy : x=y := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hh := congrArg (fun n ↦ n%q) (he i)
    simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (x.val i).isLt,
      Nat.mod_eq_of_lt (y.val i).isLt] using hh
  subst y
  refine Prod.ext rfl ?_
  funext i
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel (he i))

/-- The all-divisible-by-p part of the congruence count has critical scaling. -/
theorem scaled_rootCount_le (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) :
    rootCount k q*p^(k*(k-1)) ≤ rootCount k (p^k*q) := by
  have hh := Fintype.card_le_of_injective _ (liftRoot_injective hp hq hk)
  simpa [rootCount,Fintype.card_prod,Fintype.card_fun,← pow_mul,mul_comm k] using hh


private def tailCoordinate (p e : ℕ) (hp : 2 ≤ p) (k : ℕ)
    (t : Fin (k+1) → Fin (p^e)) (j : Fin (k+1)) : Fin (p^(e+1)) :=
  ⟨(if j=0 then 1 else 0)+p*(t j : ℕ),by
    have ht := (t j).isLt
    have hs : (if j=0 then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
    rw [pow_succ]
    nlinarith⟩

private lemma tailCoordinate_reduction (p e : ℕ) [Fact p.Prime] (k : ℕ)
    (t : Fin (k+1) → Fin (p^e)) (j : Fin (k+1)) :
    reduction p e ((tailCoordinate p e (Fact.out : p.Prime).two_le k t j : ℕ) :
      ZMod (p^(e+1))) = if j=0 then 1 else 0 := by
  rw [reduction_natCast]
  simp only [tailCoordinate,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero]
  split_ifs <;> norm_num

private theorem exists_first_coordinate (p e k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (a : ZMod p) (ha : a ≠ 0) (hseed : a^(k+2)+1=0)
    (t : Fin (k+1) → Fin (p^e)) :
    ∃ x : Fin (p^(e+1)), ((x : ℕ) : ZMod p)=a ∧
      p^(e+1) ∣ (x : ℕ)^(k+2)+∑ j, (tailCoordinate p e (Fact.out : p.Prime).two_le k t j : ℕ)^(k+2) := by
  let b : Fin (k+1) → ZMod (p^(e+1)) := fun j ↦
    (tailCoordinate p e (Fact.out : p.Prime).two_le k t j : ℕ)
  have hb : reduction p e (-∑ j, b j^(k+2))=a^(k+2) := by
    simp only [map_neg,map_sum,map_pow,b,tailCoordinate_reduction]
    simp only [ite_pow,one_pow,zero_pow (by omega : k+2 ≠ 0),
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    linear_combination -hseed
  obtain ⟨x,hx,hxpow⟩ := exists_pow_root p e (k+2) hk a ha (-∑ j, b j^(k+2)) hb
  refine ⟨⟨x.val,ZMod.val_lt x⟩,?_,?_⟩
  · change (x.val : ZMod p)=a
    rw [← reduction_natCast p e, ZMod.natCast_zmod_val]
    exact hx
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [ZMod.natCast_zmod_val,hxpow]
    exact neg_add_cancel _

private def primitiveRoot (p e k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (a : ZMod p) (ha : a ≠ 0) (hseed : a^(k+2)+1=0)
    (t : Fin (k+1) → Fin (p^e)) : Roots (k+2) (p^(e+1)) :=
  ⟨Fin.cons (exists_first_coordinate p e k hk a ha hseed t).choose
    (tailCoordinate p e (Fact.out : p.Prime).two_le k t),by
    simpa only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ] using
      (exists_first_coordinate p e k hk a ha hseed t).choose_spec.2⟩

private lemma primitiveRoot_first (p e k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (a : ZMod p) (ha : a ≠ 0) (hseed : a^(k+2)+1=0)
    (t : Fin (k+1) → Fin (p^e)) :
    ¬p ∣ ((primitiveRoot p e k hk a ha hseed t).val 0 : ℕ) := by
  intro hd
  have hh := (exists_first_coordinate p e k hk a ha hseed t).choose_spec.1
  apply ha
  rw [← hh]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hd

private lemma primitiveRoot_injective (p e k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (a : ZMod p) (ha : a ≠ 0) (hseed : a^(k+2)+1=0) :
    Function.Injective (primitiveRoot p e k hk a ha hseed) := by
  intro t u h
  funext j
  apply Fin.ext
  have hh := congrArg (fun x : Roots (k+2) (p^(e+1)) ↦ (x.val j.succ : ℕ)) h
  change (if j=0 then 1 else 0)+p*(t j : ℕ)=(if j=0 then 1 else 0)+p*(u j : ℕ) at hh
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos (Nat.add_left_cancel hh)

/-- A full box of free tail digits gives nonsingular congruence roots. -/
theorem primitive_count_lower (p e k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (a : ZMod p) (ha : a ≠ 0) (hseed : a^(k+2)+1=0) :
    p^(e*(k+1)) ≤ Fintype.card {x : Roots (k+2) (p^(e+1)) // ¬p ∣ (x.val 0 : ℕ)} := by
  classical
  let f : (Fin (k+1) → Fin (p^e)) →
      {x : Roots (k+2) (p^(e+1)) // ¬p ∣ (x.val 0 : ℕ)} :=
    fun t ↦ ⟨primitiveRoot p e k hk a ha hseed t,primitiveRoot_first p e k hk a ha hseed t⟩
  have hf : Function.Injective f := by
    intro t u h
    exact primitiveRoot_injective p e k hk a ha hseed (congrArg Subtype.val h)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun,Fintype.card_fin,← pow_mul] using hh

theorem divisible_count_lower (p q k : ℕ) (hp : 0 < p) (hq : 0 < q) :
    rootCount (k+2) q*p^((k+2)*(k+1)) ≤
      Fintype.card {x : Roots (k+2) (p^(k+2)*q) // p ∣ (x.val 0 : ℕ)} := by
  classical
  let f : (Roots (k+2) q × (Fin (k+2) → Fin (p^(k+1)))) →
      {x : Roots (k+2) (p^(k+2)*q) // p ∣ (x.val 0 : ℕ)} := fun z ↦
    ⟨liftRoot hp hq (by omega : 0 < k+2) z.1 z.2, by
      change p ∣ p*_
      exact dvd_mul_right _ _⟩
  have hf : Function.Injective f := by
    intro x y h
    exact liftRoot_injective hp hq (by omega : 0 < k+2) (congrArg Subtype.val h)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [rootCount,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,← pow_mul,
    mul_comm (k+1) (k+2)] using hh


/-- Primitive roots and roots divisible by p contribute disjointly. -/
theorem rootCount_step (p m k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (a : ZMod p) (ha : a ≠ 0) (hseed : a^(k+2)+1=0) :
    p^((m+k+1)*(k+1))+rootCount (k+2) (p^m)*p^((k+2)*(k+1)) ≤
      rootCount (k+2) (p^(m+k+2)) := by
  classical
  let P : Roots (k+2) (p^(m+k+2)) → Prop := fun x ↦ p ∣ (x.val 0 : ℕ)
  have hprim : p^((m+k+1)*(k+1)) ≤ Fintype.card {x // ¬P x} := by
    simpa only [P,Nat.add_assoc] using primitive_count_lower p (m+k+1) k hk a ha hseed
  have hdiv : rootCount (k+2) (p^m)*p^((k+2)*(k+1)) ≤ Fintype.card {x // P x} := by
    have hd := divisible_count_lower p (p^m) k (Fact.out : p.Prime).pos (pow_pos (Fact.out : p.Prime).pos _)
    rw [← pow_add,show k+2+m=m+k+2 by omega] at hd
    exact hd
  have hcard := Fintype.card_subtype_compl P
  have hle := Fintype.card_subtype_le P
  change Fintype.card {x // ¬P x}=rootCount (k+2) (p^(m+k+2))-Fintype.card {x // P x} at hcard
  change Fintype.card {x // P x} ≤ rootCount (k+2) (p^(m+k+2)) at hle
  omega

/-- Critical homogeneity makes the density contributions add, rather than decay. -/
theorem rootCount_growth (p k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (a : ZMod p) (ha : a ≠ 0) (hseed : a^(k+2)+1=0) (d : ℕ) :
    (d+1)*p^((k+2)*d*(k+1)) ≤ rootCount (k+2) (p^((k+2)*d+1)) := by
  classical
  induction d with
  | zero =>
    have hprim := primitive_count_lower p 0 k hk a ha hseed
    have hle := Fintype.card_subtype_le (fun x : Roots (k+2) (p^(0+1)) ↦ ¬p ∣ (x.val 0 : ℕ))
    simpa only [mul_zero,zero_mul,pow_zero,zero_add,one_mul] using hprim.trans hle
  | succ d ih =>
    have hs := rootCount_step p ((k+2)*d+1) k hk a ha hseed
    have hE : ((k+2)*d+1+k+1)*(k+1)=(k+2)*(d+1)*(k+1) := by ring
    have hM : (k+2)*d+1+k+2=(k+2)*(d+1)+1 := by ring
    rw [hE,hM] at hs
    calc
      (d+1+1)*p^((k+2)*(d+1)*(k+1)) =
          p^((k+2)*(d+1)*(k+1))+((d+1)*p^((k+2)*d*(k+1)))*p^((k+2)*(k+1)) := by
        rw [show (k+2)*(d+1)*(k+1)=(k+2)*d*(k+1)+(k+2)*(k+1) by ring,pow_add]
        ring
      _ ≤ p^((k+2)*(d+1)*(k+1))+rootCount (k+2) (p^((k+2)*d+1))*p^((k+2)*(k+1)) := by gcongr
      _ ≤ _ := hs

end
end Erdos322Research.LocalPeakCounting
