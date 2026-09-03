import Submission.PrimePowerFirstExit
import Submission.FiniteUnitCover

/-!
A conditional construction: a twofold odd cover with no modulus divisible by3
would give a strict odd cover. No such twofold cover is supplied here.
-/
namespace Erdos7TwofoldNoThreeLift
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

lemma crt_pair (u v : ℕ) (h : u.Coprime v) (r s : ℤ) :
    ∃ z : ℤ, (u : ℤ) ∣ z-r ∧ (v : ℤ) ∣ z-s := by
  obtain ⟨a,b,hab⟩ := h.isCoprime
  refine ⟨a*(u : ℤ)*s+b*(v : ℤ)*r,?_,?_⟩
  · refine ⟨a*(s-r),?_⟩
    nlinarith [congrArg (fun t : ℤ => t*r) hab]
  · refine ⟨b*(r-s),?_⟩
    nlinarith [congrArg (fun t : ℤ => t*s) hab]

lemma three_power_unique (u v a b : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hu3 : ¬ 3 ∣ u) (hv3 : ¬ 3 ∣ v) (he : 3^a*u=3^b*v) : a=b ∧ u=v := by
  have hf := congrArg (fun n : ℕ => n.factorization 3) he
  dsimp only at hf
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) hu.ne',
    Nat.factorization_mul (pow_ne_zero _ (by decide)) hv.ne',
    Finsupp.add_apply,Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hu3,
    Nat.factorization_eq_zero_of_not_dvd hv3] at hf
  simp only [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul,
    Nat.prime_three.factorization_self,mul_one,add_zero] at hf
  refine ⟨hf,?_⟩
  rw [hf] at he
  exact Nat.eq_of_mul_eq_mul_left (by positivity) he

lemma odd_cover_of_arithmetic {K : Type} [Fintype K]
    (n : K → ℕ) (r : K → ℤ) (hinj : Function.Injective n)
    (hn : ∀ k,1 < n k ∧ Odd (n k))
    (hc : ∀ x : ℤ,∃ k,(n k : ℤ) ∣ x-r k) :
    ∃ C : StrictCoveringSystem ℤ,∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  let C : StrictCoveringSystem ℤ := {
    ι := K
    residue := r
    moduli := fun k => Ideal.span {(n k : ℤ)}
    unionCovers := by
      ext x
      simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
      obtain ⟨k,hk⟩ := hc x
      refine ⟨k,?_⟩
      rw [Set.mem_add]
      exact ⟨r k,Set.mem_singleton _,x-r k,Ideal.mem_span_singleton.mpr hk,by ring⟩
    ne_bot := by
      intro k he
      have hh := congrArg Ideal.absNorm he
      simp only [Erdos7FiniteUnitCover.span_norm,Ideal.absNorm_bot] at hh
      have := (hn k).1
      omega
    ne_top := by
      intro k he
      have hh := congrArg Ideal.absNorm he
      simp only [Erdos7FiniteUnitCover.span_norm,Ideal.absNorm_top] at hh
      have := (hn k).1
      omega
    injective_moduli := by
      intro k l he
      apply hinj
      simpa only [Erdos7FiniteUnitCover.span_norm] using congrArg Ideal.absNorm he }
  refine ⟨C,fun i => ⟨?_,C.ne_top i⟩⟩
  change ¬ Ideal.span {(n i : ℤ)} ≤ Ideal.span {2}
  rw [Ideal.span_singleton_le_span_singleton,← even_iff_two_dvd,
    Int.not_even_iff_odd,Int.odd_coe_nat]
  exact (hn i).2

section
variable {I : Type} [Fintype I]
variable (m : I → ℕ) (q : ℕ)

def cofactor : Option (Option I) → ℕ
  | none => q
  | some none => 1
  | some (some i) => m i

def Index := I ⊕ (Fin q × Option (Option I))

instance : Fintype (Index (I := I) q) := inferInstanceAs (Fintype (I ⊕ (Fin q × Option (Option I))))

def modulus : Index (I := I) q → ℕ
  | .inl i => m i
  | .inr (t,k) => 3^(t.val+1)*cofactor m q k

lemma cofactor_data (hm : ∀ i,1 < m i ∧ Odd (m i)) (h3 : ∀ i,¬ 3 ∣ m i)
    (hq : q.Prime) (hq3 : 3 < q) (k : Option (Option I)) :
    0 < cofactor m q k ∧ Odd (cofactor m q k) ∧ ¬ 3 ∣ cofactor m q k := by
  cases k with
  | none =>
    refine ⟨hq.pos,hq.odd_of_ne_two (by omega),?_⟩
    intro hh
    have he := (Nat.dvd_prime hq).mp hh
    rcases he with he | he <;> omega
  | some k =>
    cases k with
    | none => norm_num [cofactor]
    | some i => exact ⟨by dsimp [cofactor]; have := (hm i).1; omega,(hm i).2,h3 i⟩

lemma cofactor_injective (hinj : Function.Injective m) (hm : ∀ i,1 < m i)
    (hq3 : 3 < q) (hqbig : ∀ i,m i < q) : Function.Injective (cofactor m q) := by
  intro k l he
  cases k with
  | none =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | none => have : q=1 := he; omega
      | some i => have : q=m i := he; have := hqbig i; omega
  | some k =>
    cases l with
    | none =>
      cases k with
      | none => have : 1=q := he; omega
      | some i => have : m i=q := he; have := hqbig i; omega
    | some l =>
      cases k with
      | none =>
        cases l with
        | none => rfl
        | some j => have : 1=m j := he; have := hm j; omega
      | some i =>
        cases l with
        | none => have : m i=1 := he; have := hm i; omega
        | some j => exact congrArg (fun i => some (some i)) (hinj he)

lemma modulus_data (hinj : Function.Injective m) (hm : ∀ i,1 < m i ∧ Odd (m i))
    (h3 : ∀ i,¬ 3 ∣ m i) (hq : q.Prime) (hq3 : 3 < q) (hqbig : ∀ i,m i < q) :
    Function.Injective (modulus m q) ∧
      ∀ k,1 < modulus m q k ∧ Odd (modulus m q k) := by
  have hc := cofactor_data m q hm h3 hq hq3
  have hci := cofactor_injective m q hinj (fun i => (hm i).1) hq3 hqbig
  have hp (t : Fin q) : 3 ∣ 3^(t.val+1) := by
    rw [pow_succ]; exact dvd_mul_left _ _
  constructor
  · intro k l he
    cases k with
    | inl i =>
      cases l with
      | inl j => exact congrArg Sum.inl (hinj he)
      | inr z =>
        apply False.elim
        apply h3 i
        change m i=3^(z.1.val+1)*cofactor m q z.2 at he
        rw [he]
        exact dvd_mul_of_dvd_left (hp z.1) (cofactor m q z.2)
    | inr z =>
      cases l with
      | inl i =>
        apply False.elim
        apply h3 i
        change 3^(z.1.val+1)*cofactor m q z.2=m i at he
        rw [← he]
        exact dvd_mul_of_dvd_left (hp z.1) (cofactor m q z.2)
      | inr w =>
        obtain ⟨ht,hk⟩ := three_power_unique _ _ _ _ (hc z.2).1 (hc w.2).1
          (hc z.2).2.2 (hc w.2).2.2 he
        have ht' : z.1=w.1 := Fin.ext (by omega)
        exact congrArg Sum.inr (Prod.ext ht' (hci hk))
  · intro k
    cases k with
    | inl i => exact hm i
    | inr z =>
      change 1 < 3^(z.1.val+1)*cofactor m q z.2 ∧ Odd (3^(z.1.val+1)*cofactor m q z.2)
      have hp3 : 3 ≤ 3^(z.1.val+1) := by
        have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 3) (show 1≤z.1.val+1 by omega)
        simpa using hh
      have hcf := (hc z.2).1
      exact ⟨by nlinarith,((by decide : Odd 3).pow).mul (hc z.2).2.1⟩

variable (a₀ a₁ : I → ℤ)

def ternaryResidue (t : Fin q) : Option (Option I) → ℤ
  | none => -1
  | some none => Erdos7PrimePowerCombFamily.exitValue 3 (t.val+1) 1
  | some (some _) => Erdos7PrimePowerCombFamily.exitValue 3 (t.val+1) 2

def cofactorResidue (t : Fin q) : Option (Option I) → ℤ
  | none => t.val
  | some none => 0
  | some (some i) => a₁ i

lemma exists_residues (hm : ∀ i,1 < m i ∧ Odd (m i)) (h3 : ∀ i,¬ 3 ∣ m i)
    (hq : q.Prime) (hq3 : 3 < q) :
    ∃ a : Index (I := I) q → ℤ,
      (∀ i,a (.inl i)=a₀ i) ∧
      (∀ t k,(3 : ℤ)^(t.val+1) ∣ a (.inr (t,k))-ternaryResidue q t k ∧
        (cofactor m q k : ℤ) ∣ a (.inr (t,k))-cofactorResidue q a₁ t k) := by
  have hc (k) := (Nat.prime_three.coprime_iff_not_dvd.mpr
    (cofactor_data m q hm h3 hq hq3 k).2.2)
  choose z hz using fun (t : Fin q) k => crt_pair (3^(t.val+1)) (cofactor m q k)
    ((hc k).pow_left _) (ternaryResidue q t k) (cofactorResidue q a₁ t k)
  refine ⟨Sum.elim a₀ (fun z' => z z'.1 z'.2),fun _ => rfl,?_⟩
  intro t k
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hz t k

lemma lifted_covers (hm : ∀ i,1 < m i ∧ Odd (m i)) (h3 : ∀ i,¬ 3 ∣ m i)
    (hq : q.Prime) (hq3 : 3 < q)
    (hcover : ∀ x : ℤ,∃ i,(m i : ℤ) ∣ x-a₀ i ∨ (m i : ℤ) ∣ x-a₁ i)
    (a : Index (I := I) q → ℤ)
    (ha₀ : ∀ i,a (.inl i)=a₀ i)
    (ha : ∀ (t : Fin q) k,(3 : ℤ)^(t.val+1) ∣ a (.inr (t,k))-ternaryResidue q t k ∧
      (cofactor m q k : ℤ) ∣ a (.inr (t,k))-cofactorResidue q a₁ t k) :
    ∀ x : ℤ,∃ k,(modulus m q k : ℤ) ∣ x-a k := by
  intro x
  have hhit (t : Fin q) (k : Option (Option I))
      (hter : (3 : ℤ)^(t.val+1) ∣ x-ternaryResidue q t k)
      (hcf : (cofactor m q k : ℤ) ∣ x-cofactorResidue q a₁ t k) :
      (modulus m q (.inr (t,k)) : ℤ) ∣ x-a (.inr (t,k)) := by
    have hc := ((Nat.prime_three.coprime_iff_not_dvd.mpr
      (cofactor_data m q hm h3 hq hq3 k).2.2).pow_left (t.val+1)).isCoprime
    have ht' : (3 : ℤ)^(t.val+1) ∣ x-a (.inr (t,k)) := by
      convert dvd_sub hter (ha t k).1 using 1 <;> ring
    have hc' : (cofactor m q k : ℤ) ∣ x-a (.inr (t,k)) := by
      convert dvd_sub hcf (ha t k).2 using 1 <;> ring
    simpa only [modulus,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      hc.mul_dvd (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht') hc'
  by_cases hstem : (3 : ℤ)^q ∣ x+1
  · have hqpos : (0 : ℤ) < q := by omega
    have hr0 := Int.emod_nonneg x hqpos.ne'
    have hrq := Int.emod_lt_of_pos x hqpos
    let t : Fin q := ⟨(x%(q : ℤ)).toNat,by omega⟩
    have ht : (t.val : ℤ)=x%(q : ℤ) := Int.toNat_of_nonneg hr0
    refine ⟨.inr (t,none),hhit t none ?_ ?_⟩
    · change (3 : ℤ)^(t.val+1) ∣ x-(-1)
      simpa only [sub_neg_eq_add] using
        (pow_dvd_pow (3 : ℤ) (by omega : t.val+1 ≤ q)).trans hstem
    · change (q : ℤ) ∣ x-(t.val : ℤ)
      rw [ht]
      exact ⟨x/(q : ℤ),by have hh := Int.emod_add_mul_ediv x (q : ℤ); nlinarith⟩
  · obtain ⟨e,c,he,heq,hc0,hc3,hx⟩ :=
      Erdos7PrimePowerFirstExit.first_exit 3 q (by decide) x hstem
    let t : Fin q := ⟨e-1,by omega⟩
    have ht : t.val+1=e := by dsimp [t]; omega
    by_cases hc1 : c=1
    · subst c
      refine ⟨.inr (t,some none),hhit t (some none) ?_ ?_⟩
      · simpa only [ternaryResidue,ht] using hx
      · change (1 : ℤ) ∣ x-0
        exact one_dvd _
    · have hc2 : c=2 := by omega
      subst c
      obtain ⟨i,hi | hi⟩ := hcover x
      · exact ⟨.inl i,by simpa only [modulus,ha₀] using hi⟩
      · refine ⟨.inr (t,some (some i)),hhit t (some (some i)) ?_ ?_⟩
        · simpa only [ternaryResidue,ht] using hx
        · exact hi

/-- A no-3 twofold odd cover is a sufficient finite construction criterion for
precisely the original strict odd covering existential. -/
theorem exists_strict_cover_of_twofold
    (hinj : Function.Injective m) (hm : ∀ i,1 < m i ∧ Odd (m i))
    (h3 : ∀ i,¬ 3 ∣ m i)
    (hcover : ∀ x : ℤ,∃ i,(m i : ℤ) ∣ x-a₀ i ∨ (m i : ℤ) ∣ x-a₁ i) :
    ∃ C : StrictCoveringSystem ℤ,∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  classical
  obtain ⟨q,hqB,hq⟩ := Nat.exists_infinite_primes (4+∑ i,m i)
  have hq3 : 3 < q := by omega
  have hqbig (i : I) : m i < q := by
    have hh : m i ≤ ∑ j,m j := Finset.single_le_sum
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  obtain ⟨a,ha₀,ha⟩ := exists_residues m q a₀ a₁ hm h3 hq hq3
  have hd := modulus_data m q hinj hm h3 hq hq3 hqbig
  exact odd_cover_of_arithmetic (modulus m q) a hd.1 hd.2
    (lifted_covers m q a₀ a₁ hm h3 hq hq3 hcover a ha₀ ha)

end
#print axioms exists_strict_cover_of_twofold
end Erdos7TwofoldNoThreeLift
