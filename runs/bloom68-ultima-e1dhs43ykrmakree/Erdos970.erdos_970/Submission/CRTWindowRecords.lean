import Submission.CRTWindowRigidity

/-!
# Euclidean enumeration of CRT prefix records

A direct kernel proof of the record-set recursion and the count of favorable
remainders. No Jacobsthal conjecture is imported or used.
-/

namespace IntegerSieve.CRTWindow.RecordCount

open Finset

/-- The canonical CRT root of a grid point. -/
def root {p q : ℕ} (hc : p.Coprime q) (a b : ℕ) : ℕ :=
  (Nat.chineseRemainder hc a b).val

lemma root_lt {p q : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q) (a b : ℕ) :
    root hc a b < p * q := Nat.chineseRemainder_lt_mul hc a b hp.ne' hq.ne'

lemma root_mod_left {p q a : ℕ} (hc : p.Coprime q) (ha : a < p) (b : ℕ) :
    root hc a b % p = a := by
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha] using (Nat.chineseRemainder hc a b).property.1

lemma root_mod_right {p q b : ℕ} (hc : p.Coprime q) (hb : b < q) (a : ℕ) :
    root hc a b % q = b := by
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb] using (Nat.chineseRemainder hc a b).property.2

lemma root_eq {p q r a b : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q)
    (hr : r < p * q) (hrp : r ≡ a [MOD p]) (hrq : r ≡ b [MOD q]) :
    root hc a b = r := by
  exact (Nat.chineseRemainder_modEq_unique hc hrp hrq).symm.eq_of_lt_of_lt
    (root_lt hc hp hq a b) hr

lemma root_of_nat {p q r : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q)
    (hr : r < p * q) : root hc (r % p) (r % q) = r := by
  apply root_eq hc hp hq hr <;> simp [Nat.ModEq]

lemma root_swap {p q : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q) (a b : ℕ) :
    root hc a b = root hc.symm b a := by
  apply root_eq hc hp hq
  · simpa [Nat.mul_comm] using root_lt hc.symm hq hp b a
  · exact (Nat.chineseRemainder hc.symm b a).property.2
  · exact (Nat.chineseRemainder hc.symm b a).property.1

/-- A prefix maximum in the CRT grid. -/
def GridRecord {p q : ℕ} (hc : p.Coprime q) (a b : ℕ) : Prop :=
  ∀ x : ℕ, x ≤ a → ∀ y : ℕ, y ≤ b → root hc x y ≤ root hc a b

noncomputable def records {p q : ℕ} (hc : p.Coprime q) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range p).product (Finset.range q)).filter fun v => GridRecord hc v.1 v.2

lemma mem_records {p q a b : ℕ} (hc : p.Coprime q) :
    (a, b) ∈ records hc ↔ a < p ∧ b < q ∧ GridRecord hc a b := by
  classical
  simp [records, and_assoc]

lemma gridRecord_iff {p q a b : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q)
    (ha : a < p) (hb : b < q) :
    GridRecord hc a b ↔ IsRecord p q (root hc a b) := by
  constructor
  · intro h s hs hsp hsq
    rw [root_mod_left hc ha] at hsp
    rw [root_mod_right hc hb] at hsq
    have hh := h (s % p) hsp (s % q) hsq
    simpa only [root_of_nat hc hp hq hs] using hh
  · intro h x hx y hy
    apply h (root hc x y) (root_lt hc hp hq x y)
    · simpa only [root_mod_left hc (hx.trans_lt ha), root_mod_left hc ha] using hx
    · simpa only [root_mod_right hc (hy.trans_lt hb), root_mod_right hc hb] using hy

/-- A generic radix comparison: changing the radix preserves order if all the
low digits lie below both radices. -/
lemma radix_order {m n b d j k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hbm : b < m) (hdm : d < m) (hbn : b < n) (hdn : d < n) :
    b + m * j ≤ d + m * k ↔ b + n * j ≤ d + n * k := by
  suffices hdir : ∀ m n : ℕ, 0 < m → 0 < n → b < m → d < m → b < n → d < n →
      b + m * j ≤ d + m * k → b + n * j ≤ d + n * k by
    exact ⟨hdir m n hm hn hbm hdm hbn hdn, hdir n m hn hm hbn hdn hbm hdm⟩
  intro m n hm hn hbm hdm hbn hdn h
  have hdiv := Nat.div_le_div_right (c := m) h
  rw [Nat.add_mul_div_left _ _ hm, Nat.add_mul_div_left _ _ hm,
    Nat.div_eq_of_lt hbm, Nat.div_eq_of_lt hdm] at hdiv
  by_cases heq : j = k
  · subst k
    have hbd : b ≤ d := by omega
    omega
  · have hjk : j + 1 ≤ k := by omega
    have hmul := Nat.mul_le_mul_left n hjk
    nlinarith

/-- On the smaller rectangle the two CRT roots have the same high digit. -/
lemma root_reduce {p q a b : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hpq : p < q)
    (ha : a < p) (hb : b < q - p) :
    root ((Nat.coprime_sub_self_right hpq.le).mpr hc) a b =
      b + (q - p) * (root hc a b / q) := by
  have hq : 0 < q := by omega
  have hd : 0 < q - p := by omega
  have hbq : b < q := by omega
  let j := root hc a b / q
  have hdecomp : b + q * j = root hc a b := by
    simpa only [root_mod_right hc hbq] using (Nat.mod_add_div (root hc a b) q)
  have hj : j < p := (Nat.div_lt_iff_lt_mul hq).mpr (root_lt hc hp hq a b)
  have hbase : q = p + (q - p) := by omega
  have hrel : b + (q - p) * j + p * j = root hc a b := by nlinarith
  apply root_eq _ hp hd
  · change b + (q - p) * j < p * (q - p)
    have hmul := Nat.mul_le_mul_left (q - p) (Nat.succ_le_of_lt hj)
    nlinarith
  · change (b + (q - p) * j) % p = a % p
    have hm : (b + (q - p) * j) % p = root hc a b % p := by
      conv_rhs => rw [← hrel]
      simp
    rw [hm, root_mod_left hc ha, Nat.mod_eq_of_lt ha]
  · simp only [Nat.ModEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

lemma root_order_reduce {p q a b x y : ℕ} (hc : p.Coprime q)
    (hp : 0 < p) (hpq : p < q) (ha : a < p) (hx : x < p)
    (hb : b < q - p) (hy : y < q - p) :
    root hc a b ≤ root hc x y ↔
      root ((Nat.coprime_sub_self_right hpq.le).mpr hc) a b ≤
        root ((Nat.coprime_sub_self_right hpq.le).mpr hc) x y := by
  have hq : 0 < q := by omega
  have hba : b + q * (root hc a b / q) = root hc a b := by
    simpa only [root_mod_right hc (show b < q by omega)] using
      (Nat.mod_add_div (root hc a b) q)
  have hyx : y + q * (root hc x y / q) = root hc x y := by
    simpa only [root_mod_right hc (show y < q by omega)] using
      (Nat.mod_add_div (root hc x y) q)
  rw [root_reduce hc hp hpq ha hb, root_reduce hc hp hpq hx hy]
  conv_lhs => rw [← hba, ← hyx]
  exact radix_order hq (by omega) (by omega) (by omega) hb hy

lemma gridRecord_reduce {p q a b : ℕ} (hc : p.Coprime q)
    (hp : 0 < p) (hpq : p < q) (ha : a < p) (hb : b < q - p) :
    GridRecord hc a b ↔
      GridRecord ((Nat.coprime_sub_self_right hpq.le).mpr hc) a b := by
  constructor <;> intro h x hx y hy
  · exact (root_order_reduce hc hp hpq (hx.trans_lt ha) ha (hy.trans_lt hb) hb).mp (h x hx y hy)
  · exact (root_order_reduce hc hp hpq (hx.trans_lt ha) ha (hy.trans_lt hb) hb).mpr (h x hx y hy)

/-- The last `p` roots form the diagonal in the new strip. -/
lemma root_top {p q i : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hpq : p < q)
    (hi : i < p) : root hc i (q - p + i) = p * (q - 1) + i := by
  have hq : 0 < q := by omega
  have hb : q - p + i < q := by omega
  have hidentity : p * (q - 1) + i = (q - p + i) + q * (p - 1) := by
    have h₁ : q - 1 + 1 = q := by omega
    have h₂ : p - 1 + 1 = p := by omega
    have h₃ : q - p + p = q := by omega
    nlinarith
  apply root_eq hc hp hq
  · have h₁ : q - 1 + 1 = q := by omega
    nlinarith
  · simp [Nat.ModEq, Nat.add_mod, Nat.mod_eq_of_lt hi]
  · rw [hidentity]
    simp [Nat.ModEq, Nat.mod_eq_of_lt hb]

/-- A grid point has one of the last `p` roots exactly on that diagonal. -/
lemma root_ge_top_iff {p q a b : ℕ} (hc : p.Coprime q)
    (hp : 0 < p) (hpq : p < q) (ha : a < p) (hb : b < q) :
    p * (q - 1) ≤ root hc a b ↔ b = q - p + a := by
  have hq : 0 < q := by omega
  constructor
  · intro h
    let i := root hc a b - p * (q - 1)
    have hdecomp : p * (q - 1) + i = root hc a b := by omega
    have hi : i < p := by
      have hlt := root_lt hc hp hq a b
      have h₁ : q - 1 + 1 = q := by omega
      nlinarith
    have hrt := root_top hc hp hpq hi
    rw [hdecomp] at hrt
    have hia : i = a := by
      have := congrArg (fun n => n % p) hrt
      simpa only [root_mod_left hc hi, root_mod_left hc ha] using this
    have hbi : q - p + i = b := by
      have := congrArg (fun n => n % q) hrt
      simpa only [root_mod_right hc (show q - p + i < q by omega), root_mod_right hc hb] using this
    omega
  · intro h
    rw [h, root_top hc hp hpq ha]
    omega

lemma gridRecord_strip_iff {p q a b : ℕ} (hc : p.Coprime q)
    (hp : 0 < p) (hpq : p < q) (ha : a < p) (hb : b < q) (hstrip : q - p ≤ b) :
    GridRecord hc a b ↔ b = q - p + a := by
  constructor
  · intro h
    by_contra hne
    have hsmall : root hc a b < p * (q - 1) :=
      Nat.lt_of_not_ge (fun hh => hne ((root_ge_top_iff hc hp hpq ha hb).mp hh))
    let i := min a (b - (q - p))
    have hia : i ≤ a := Nat.min_le_left _ _
    have hib : i ≤ b - (q - p) := Nat.min_le_right _ _
    have hi : i < p := hia.trans_lt ha
    have hcount := h i hia (q - p + i) (by omega)
    rw [root_top hc hp hpq hi] at hcount
    omega
  · intro heq x hx y hy
    have hx' : x < p := hx.trans_lt ha
    have hy' : y < q := hy.trans_lt hb
    by_cases ht : p * (q - 1) ≤ root hc x y
    · have hyx := (root_ge_top_iff hc hp hpq hx' hy').mp ht
      rw [hyx, heq, root_top hc hp hpq hx', root_top hc hp hpq ha]
      omega
    · have ht' : p * (q - 1) ≤ root hc a b :=
        (root_ge_top_iff hc hp hpq ha hb).mpr heq
      omega


/-- The diagonal contributed by one Euclidean subtraction. -/
def stripDiagonal (p q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range p).image fun i => (i, q - p + i)

lemma mem_stripDiagonal {p q a b : ℕ} :
    (a, b) ∈ stripDiagonal p q ↔ a < p ∧ b = q - p + a := by
  simp [stripDiagonal, Prod.mk.injEq, eq_comm]

/-- The exact disjoint Euclidean record-set recursion. -/
theorem records_reduce {p q : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hpq : p < q) :
    records hc = records ((Nat.coprime_sub_self_right hpq.le).mpr hc) ∪ stripDiagonal p q := by
  classical
  ext ⟨a, b⟩
  simp only [Finset.mem_union, mem_records, mem_stripDiagonal]
  constructor
  · rintro ⟨ha, hb, hg⟩
    by_cases hb' : b < q - p
    · exact Or.inl ⟨ha, hb', (gridRecord_reduce hc hp hpq ha hb').mp hg⟩
    · exact Or.inr ⟨ha, (gridRecord_strip_iff hc hp hpq ha hb (by omega)).mp hg⟩
  · rintro (⟨ha, hb, hg⟩ | ⟨ha, hb⟩)
    · exact ⟨ha, by omega, (gridRecord_reduce hc hp hpq ha hb).mpr hg⟩
    · exact ⟨ha, by omega,
        (gridRecord_strip_iff hc hp hpq ha (by omega) (by omega)).mpr hb⟩

lemma records_reduce_disjoint {p q : ℕ} (hc : p.Coprime q) (hpq : p < q) :
    Disjoint (records ((Nat.coprime_sub_self_right hpq.le).mpr hc)) (stripDiagonal p q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro ⟨a, b⟩ hr hd
  obtain ⟨_, hb, _⟩ := (mem_records _).mp hr
  obtain ⟨_, heq⟩ := mem_stripDiagonal.mp hd
  omega

lemma card_stripDiagonal (p q : ℕ) : (stripDiagonal p q).card = p := by
  have hi : Set.InjOn (fun i : ℕ => (i, q - p + i)) (↑(Finset.range p) : Set ℕ) := by
    intro i _ j _ h
    exact congrArg Prod.fst h
  have h := (Finset.card_image_iff.mpr hi)
  simpa [stripDiagonal] using h

lemma card_records_reduce {p q : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hpq : p < q) :
    (records hc).card = (records ((Nat.coprime_sub_self_right hpq.le).mpr hc)).card + p := by
  rw [records_reduce hc hp hpq, Finset.card_union_of_disjoint (records_reduce_disjoint hc hpq),
    card_stripDiagonal]

lemma gridRecord_swap {p q a b : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q) :
    GridRecord hc a b ↔ GridRecord hc.symm b a := by
  constructor
  · intro h x hx y hy
    simpa only [root_swap hc hp hq] using h y hy x hx
  · intro h x hx y hy
    simpa only [root_swap hc.symm hq hp] using h y hy x hx

lemma card_records_swap {p q : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q) :
    (records hc).card = (records hc.symm).card := by
  classical
  apply Finset.card_bij (fun v _ => v.swap)
  · intro ⟨a, b⟩ hv
    obtain ⟨ha, hb, hg⟩ := (mem_records hc).mp hv
    exact (mem_records hc.symm).mpr ⟨hb, ha, (gridRecord_swap hc hp hq).mp hg⟩
  · intro a _ b _ hab
    have h := congrArg Prod.swap hab
    simpa using h
  · intro ⟨a, b⟩ hv
    obtain ⟨ha, hb, hg⟩ := (mem_records hc.symm).mp hv
    refine ⟨(b, a), (mem_records hc).mpr
      ⟨hb, ha, (gridRecord_swap hc hp hq).mpr hg⟩, rfl⟩

lemma root_one_left {q b : ℕ} (hc : Nat.Coprime 1 q) (hq : 0 < q) (hb : b < q) :
    root hc 0 b = b := by
  apply root_eq hc (by decide) hq (by simpa using hb) <;> simp [Nat.ModEq, Nat.mod_one]

lemma card_records_one_left {q : ℕ} (hc : Nat.Coprime 1 q) (hq : 0 < q) :
    (records hc).card = q := by
  classical
  have heq : records hc = (Finset.range 1).product (Finset.range q) := by
    unfold records
    apply Finset.filter_eq_self.mpr
    intro ⟨a, b⟩ hv
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hv
    have ha0 : a = 0 := by simpa using ha
    have hbq : b < q := Finset.mem_range.mp hb
    subst a
    intro x hx y hy
    have hx0 : x = 0 := by omega
    subst x
    rw [root_one_left hc hq (hy.trans_lt hbq), root_one_left hc hq hbq]
    exact hy
  rw [heq]
  simp

lemma card_records_one_right {p : ℕ} (hc : Nat.Coprime p 1) (hp : 0 < p) :
    (records hc).card = p := by
  rw [card_records_swap hc hp (by decide), card_records_one_left hc.symm hp]

/-- Complete enumeration, including composite coprime moduli and the 1D base cases. -/
theorem card_records {p q : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q) :
    (records hc).card = p + q - 1 := by
  have main : ∀ n : ℕ, ∀ p q : ℕ, 0 < p → 0 < q → (hc : p.Coprime q) →
      p + q = n → (records hc).card = p + q - 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p q hp hq hc hn
      by_cases hp1 : p = 1
      · subst p
        simpa using card_records_one_left hc hq
      by_cases hq1 : q = 1
      · subst q
        simpa using card_records_one_right hc hp
      have hne : p ≠ q := by
        intro heq
        subst q
        exact hp1 ((Nat.coprime_self p).mp hc)
      by_cases hpq : p < q
      · rw [card_records_reduce hc hp hpq,
          ih q (by omega) p (q - p) hp (by omega)
            ((Nat.coprime_sub_self_right hpq.le).mpr hc) (by omega)]
        omega
      · have hqp : q < p := by omega
        rw [card_records_swap hc hp hq, card_records_reduce hc.symm hq hqp,
          ih p (by omega) q (p - q) hq (by omega)
            ((Nat.coprime_sub_self_right hqp.le).mpr hc.symm) (by omega)]
        omega
  exact main (p + q) p q hp hq hc rfl


/-- Favorable positive tails, with the endpoint `pq` temporarily retained. -/
noncomputable def fullForcing (p q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (p * q)).filter (ForcingRemainder p q)

/-- The nonzero proper remainders for which the maximal-singleton implication holds. -/
noncomputable def favorable (p q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (p * q)).filter fun t => 0 < t ∧ ForcingRemainder p q t

lemma mem_fullForcing {p q t : ℕ} :
    t ∈ fullForcing p q ↔ 0 < t ∧ t ≤ p * q ∧ ForcingRemainder p q t := by
  classical
  simp only [fullForcing, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  constructor <;> rintro ⟨h0, hN, hf⟩ <;> exact ⟨by omega, hN, hf⟩

lemma mem_favorable {p q t : ℕ} :
    t ∈ favorable p q ↔ 0 < t ∧ t < p * q ∧ ForcingRemainder p q t := by
  classical
  simp [favorable, and_left_comm]

/-- The root-plus-one correspondence between grid records and forcing tails. -/
lemma card_fullForcing {p q : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q) :
    (fullForcing p q).card = (records hc).card := by
  classical
  symm
  apply Finset.card_bij (fun v _ => root hc v.1 v.2 + 1)
  · intro ⟨a, b⟩ hv
    obtain ⟨ha, hb, hg⟩ := (mem_records hc).mp hv
    apply mem_fullForcing.mpr
    refine ⟨by omega, Nat.succ_le_of_lt (root_lt hc hp hq a b), ?_⟩
    apply (forcing_iff_record (by omega)).mpr
    simpa only [Nat.add_sub_cancel] using (gridRecord_iff hc hp hq ha hb).mp hg
  · intro ⟨a, b⟩ hv ⟨x, y⟩ hw heq
    obtain ⟨ha, hb, _⟩ := (mem_records hc).mp hv
    obtain ⟨hx, hy, _⟩ := (mem_records hc).mp hw
    change root hc a b + 1 = root hc x y + 1 at heq
    have hr : root hc a b = root hc x y := Nat.add_right_cancel heq
    have hp' := congrArg (fun n => n % p) hr
    have hq' := congrArg (fun n => n % q) hr
    apply Prod.ext
    · simpa only [root_mod_left hc ha, root_mod_left hc hx] using hp'
    · simpa only [root_mod_right hc hb, root_mod_right hc hy] using hq'
  · intro t ht
    obtain ⟨ht0, htN, hf⟩ := mem_fullForcing.mp ht
    have hrN : t - 1 < p * q := by omega
    have heq := root_of_nat hc hp hq hrN
    have hg : GridRecord hc ((t - 1) % p) ((t - 1) % q) := by
      apply (gridRecord_iff hc hp hq (Nat.mod_lt _ hp) (Nat.mod_lt _ hq)).mpr
      rw [heq]
      exact (forcing_iff_record ht0).mp hf
    refine ⟨((t - 1) % p, (t - 1) % q),
      (mem_records hc).mpr ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hq, hg⟩, ?_⟩
    change root hc ((t - 1) % p) ((t - 1) % q) + 1 = t
    omega

lemma favorable_eq_erase (p q : ℕ) :
    favorable p q = (fullForcing p q).erase (p * q) := by
  classical
  ext t
  rw [mem_favorable, Finset.mem_erase, mem_fullForcing]
  constructor
  · rintro ⟨h0, hN, hf⟩
    exact ⟨by omega, h0, hN.le, hf⟩
  · rintro ⟨hne, h0, hN, hf⟩
    exact ⟨h0, by omega, hf⟩

/-- Exactly `p+q-2` nonzero remainders force a ceiling intersection whenever
both singleton counts are their ceilings. Integral singleton cases are included. -/
theorem card_favorable {p q : ℕ} (hc : p.Coprime q) (hp : 0 < p) (hq : 0 < q) :
    (favorable p q).card = p + q - 2 := by
  classical
  have hmem : p * q ∈ fullForcing p q := mem_fullForcing.mpr
    ⟨Nat.mul_pos hp hq, le_rfl, fun r hr _ _ => hr⟩
  rw [favorable_eq_erase, Finset.card_erase_of_mem hmem,
    card_fullForcing hc hp hq, card_records hc hp hq, Nat.sub_sub]

end IntegerSieve.CRTWindow.RecordCount

#print axioms IntegerSieve.CRTWindow.RecordCount.records_reduce
#print axioms IntegerSieve.CRTWindow.RecordCount.card_records
#print axioms IntegerSieve.CRTWindow.RecordCount.card_favorable
