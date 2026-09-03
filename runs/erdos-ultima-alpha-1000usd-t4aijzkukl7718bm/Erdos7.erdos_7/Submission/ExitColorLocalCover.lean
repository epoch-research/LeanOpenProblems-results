import Submission.ExitColorPatterns
import Submission.PrimePowerFirstExit

/-! A finite color-cover lifts to an actual local congruence cover. The
 existence of the color-cover is a hypothesis, not a claim made here. -/
namespace Erdos7ExitColorLocalCover
open scoped BigOperators
open Finset Erdos7ExitColorPatterns
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section
variable {I J : Type*} [Fintype I] [DecidableEq I]
variable (p : I → ℕ) (q : ℕ) (S : J → Finset I) (c : J → (i : I) → Fin (p i - 2))

noncomputable def digit (e : Old (I := I) q) (i : I) : ℕ := by
  classical
  exact if h : ∃ j, S j = support q e then (c h.choose i).val + 2 else 1

noncomputable def residue : Index (I := I) q → Option I → ℤ
  | .inl e, none => 0
  | .inl e, some i => Erdos7PrimePowerCombFamily.exitValue (p i) (e.val i).val (digit (p := p) q S c e i)
  | .inr (i,t), none => t.val
  | .inr (i,t), some k => if k=i then -1 else 0

lemma digit_of_support (hSi : Function.Injective S) (e : Old (I := I) q) (j : J)
    (he : S j = support q e) (i : I) : digit (p := p) q S c e i = (c j i).val + 2 := by
  classical
  have h : ∃ k, S k = support q e := ⟨j,he⟩
  simp only [digit, dif_pos h]
  have hh : h.choose=j := hSi (h.choose_spec.trans he.symm)
  rw [hh]

lemma digit_of_singleton (hS : ∀ j, 2 ≤ (S j).card)
    (e : Old (I := I) q) (i : I) (he : support q e = {i}) (k : I) : digit (p := p) q S c e k = 1 := by
  classical
  have hn : ¬ ∃ j, S j = support q e := by
    rintro ⟨j,hj⟩
    have hh := hS j
    rw [hj,he,card_singleton] at hh
    omega
  simp only [digit, dif_neg hn]

/-- Patches cover the entire finite stem cylinder, not just one limiting point. -/
lemma patch_hit (hq : 0 < q) (x : ℤ) (i : I) (hi : (p i : ℤ)^q ∣ x+1) :
    ∃ t : Fin q, ∀ k, (base p q k : ℤ) ^ exponent q (.inr (i,t)) k ∣
      x - residue p q S c (.inr (i,t)) k := by
  have hqz : (0 : ℤ)<q := by exact_mod_cast hq
  have ht0 : 0 ≤ x % (q : ℤ) := Int.emod_nonneg _ hqz.ne'
  have htq : x % (q : ℤ) < q := Int.emod_lt_of_pos _ hqz
  let t : Fin q := ⟨(x % (q : ℤ)).toNat, (Int.toNat_lt ht0).mpr htq⟩
  have ht : (t.val : ℤ) = x % (q : ℤ) := Int.natCast_toNat_eq_self.mpr ht0
  refine ⟨t, fun k => ?_⟩
  cases k with
  | none =>
    change (q : ℤ)^1 ∣ x - (t.val : ℤ)
    rw [pow_one,ht,Int.emod_def]
    exact ⟨x/(q : ℤ), by ring⟩
  | some k =>
    by_cases hki : k=i
    · subst k
      change (p i : ℤ) ^ (if i=i then t.val+1 else 0) ∣ x - (if i=i then -1 else 0)
      simp only [ite_true, sub_neg_eq_add]
      exact (pow_dvd_pow (p i : ℤ) (by have := t.isLt; omega : t.val+1 ≤ q)).trans hi
    · simp [base,exponent,residue,hki]

lemma pure_hit (hS : ∀ j, 2 ≤ (S j).card) (x : ℤ) (i : I) (e : ℕ)
    (he : 0 < e) (heq : e ≤ q)
    (hx : (p i : ℤ)^e ∣ x - Erdos7PrimePowerCombFamily.exitValue (p i) e 1) :
    ∃ d : Old (I := I) q, ∀ k, (base p q k : ℤ) ^ exponent q (.inl d) k ∣
      x - residue p q S c (.inl d) k := by
  classical
  let d : Old (I := I) q := ⟨fun k => if k=i then ⟨e, by omega⟩ else 0,
    ⟨i, by simp; omega⟩⟩
  have hs : support q d = {i} := by
    ext k
    simp only [mem_support, mem_singleton]
    dsimp [d]
    by_cases hki : k=i <;> simp [hki] <;> omega
  refine ⟨d, fun k => ?_⟩
  cases k with
  | none => simp [base,exponent,residue]
  | some k =>
    by_cases hki : k=i
    · subst k
      have hd := digit_of_singleton (p := p) q S c hS d i hs i
      simpa [base,exponent,residue,d,hd] using hx
    · simp [base,exponent,residue,d,hki]

lemma mixed_hit (hSi : Function.Injective S) (hS : ∀ j, 2 ≤ (S j).card)
    (x : ℤ) (e b : I → ℕ) (he : ∀ i, 0 < e i ∧ e i ≤ q)
    (hb : ∀ i, 2 ≤ b i ∧ b i < p i)
    (hx : ∀ i, (p i : ℤ)^e i ∣ x - Erdos7PrimePowerCombFamily.exitValue (p i) (e i) (b i))
    (j : J) (hj : ∀ i ∈ S j, b i = (c j i).val+2) :
    ∃ d : Old (I := I) q, ∀ k, (base p q k : ℤ) ^ exponent q (.inl d) k ∣
      x - residue p q S c (.inl d) k := by
  classical
  have hSne : (S j).Nonempty := card_pos.mp (by have := hS j; omega)
  obtain ⟨i₀,hi₀⟩ := hSne
  let d : Old (I := I) q := ⟨fun i => if i ∈ S j then ⟨e i, by have := (he i).2; omega⟩ else 0,
    ⟨i₀, by simp only [if_pos hi₀]; intro hh; have hz := congrArg Fin.val hh; have := (he i₀).1; simp at hz; omega⟩⟩
  have hs : support q d = S j := by
    ext i
    simp only [mem_support]
    dsimp [d]
    by_cases hi : i ∈ S j <;> simp [hi] <;> have := (he i).1 <;> omega
  refine ⟨d,fun k => ?_⟩
  cases k with
  | none => simp [base,exponent,residue]
  | some i =>
    by_cases hi : i ∈ S j
    · have hd := digit_of_support (p := p) q S c hSi d j hs.symm i
      have hm := hx i
      rw [hj i hi] at hm
      simpa [base,exponent,residue,d,hi,hd] using hm
    · simp [base,exponent,residue,d,hi]

/-- Every integer is covered by one of the distinct exponent-pattern classes,
provided the finite nonunary distinct-support color cover exists. -/
theorem local_cover (hp : ∀ i, 3 ≤ p i) (hq : 0 < q)
    (hSi : Function.Injective S) (hS : ∀ j, 2 ≤ (S j).card)
    (hcover : ∀ v : (i : I) → Fin (p i-2), ∃ j, ∀ i ∈ S j, v i=c j i) (x : ℤ) :
    ∃ d : Index (I := I) q, ∀ k, (base p q k : ℤ) ^ exponent q d k ∣
      x - residue p q S c d k := by
  classical
  by_cases hstem : ∃ i, (p i : ℤ)^q ∣ x+1
  · obtain ⟨i,hi⟩ := hstem
    obtain ⟨t,ht⟩ := patch_hit p q S c hq x i hi
    exact ⟨.inr (i,t),ht⟩
  · have hex (i : I) := Erdos7PrimePowerFirstExit.first_exit (p i) q (by have := hp i; omega) x
      (fun h => hstem ⟨i,h⟩)
    choose e b he heq hb0 hbp hx using hex
    by_cases hpure : ∃ i, b i=1
    · obtain ⟨i,hi⟩ := hpure
      obtain ⟨d,hd⟩ := pure_hit p q S c hS x i (e i) (he i) (heq i) (by simpa [hi] using hx i)
      exact ⟨.inl d,hd⟩
    · have hb2 (i : I) : 2 ≤ b i := by have := hb0 i; have hn : b i ≠ 1 := fun h => hpure ⟨i,h⟩; omega
      let v (i : I) : Fin (p i-2) := ⟨b i-2, by have := hbp i; have := hb2 i; omega⟩
      obtain ⟨j,hj⟩ := hcover v
      have hh (i : I) (hi : i ∈ S j) : b i=(c j i).val+2 := by
        have hv := congrArg Fin.val (hj i hi)
        change b i-2=(c j i).val at hv
        have := hb2 i
        omega
      obtain ⟨d,hd⟩ := mixed_hit p q S c hSi hS x e b (fun i => ⟨he i,heq i⟩)
        (fun i => ⟨hb2 i,hbp i⟩) hx j hh
      exact ⟨.inl d,hd⟩
end

#print axioms local_cover
end Erdos7ExitColorLocalCover
