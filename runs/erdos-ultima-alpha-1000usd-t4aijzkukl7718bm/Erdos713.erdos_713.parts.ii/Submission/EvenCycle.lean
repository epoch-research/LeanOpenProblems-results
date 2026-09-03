import FormalConjecturesUtil
import Submission.Current

/-! Path-colouring lemmas for an even cycle with a chord. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713EvenCycle

lemma periodic_mod {A : Type*} {c : ℤ → A} {p : ℤ} (hp : Function.Periodic c p) (z : ℤ) :
    c (z % p) = c z := by
  rw [Int.emod_def]
  simpa only [mul_comm] using hp.sub_int_mul_eq (x := z) (z / p)

lemma periodic_eq_on_interval {A : Type*} {f g : ℤ → A} {p : ℤ}
    (hp : 0 < p) (hf : Function.Periodic f p) (hg : Function.Periodic g p)
    (h : ∀ i, 0 ≤ i → i < p → f i = g i) : f = g := by
  funext i
  rw [← periodic_mod hf i, ← periodic_mod hg i]
  exact h _ (Int.emod_nonneg _ hp.ne') (Int.emod_lt_of_pos _ hp)

lemma periodic_of_chord_paths {A : Type*} {c : ℤ → A} {l m : ℤ}
    (hl : 0 < l) (hm : 1 < m) (hper : Function.Periodic c l)
    (hLong : ∀ a, 0 ≤ a → a < l → c (-a) = c (m + l - 1 - a))
    (hFirst : ∀ a, 0 ≤ a → a < min m l → c a = c (m + l - 1 - a))
    (hSecond : ∀ a, 0 ≤ a → a < min m l → c (1 - l + a) = c (m - a)) :
    Function.Periodic c 2 := by
  have hNeg : Function.Periodic (fun a => c (-a)) l := by
    intro a
    simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using hper.sub_eq (-a)
  have hLong' : ∀ a, c (-a) = c (m - 1 - a) := by
    have hh : (fun a => c (-a)) = (fun a => c (m - 1 - a)) := by
      apply periodic_eq_on_interval hl hNeg (hper.const_sub (m - 1))
      intro a ha hal
      have hh := hLong a ha hal
      convert hh using 1
      rw [show m + l - 1 - a = (m - 1 - a) + l by ring, hper]
    exact congrFun hh
  have hmp : Function.Periodic c (m - 1) := by
    intro z
    simpa only [neg_neg, sub_neg_eq_add, add_comm] using (hLong' (-z)).symm
  let p := min l (m - 1)
  have hp : 0 < p := by dsimp [p]; omega
  have hpPer : Function.Periodic c p := by
    by_cases hh : l ≤ m - 1
    · simpa only [p, min_eq_left hh] using hper
    · simpa only [p, min_eq_right (le_of_not_ge hh)] using hmp
  have hpml : p ≤ min m l := by dsimp [p]; omega
  have hReflect0 : ∀ z, c z = c (m - 1 - z) := by
    have hh : c = (fun z => c (m - 1 - z)) := by
      apply periodic_eq_on_interval hp hpPer (hpPer.const_sub (m - 1))
      intro a ha hap
      have hh := hFirst a ha (lt_of_lt_of_le hap hpml)
      convert hh using 1
      rw [show m + l - 1 - a = (m - 1 - a) + l by ring, hper]
    exact congrFun hh
  have hReflect1 : ∀ z, c (1 + z) = c (m - z) := by
    have hh : (fun z => c (1 + z)) = (fun z => c (m - z)) := by
      apply periodic_eq_on_interval hp (hpPer.const_add 1) (hpPer.const_sub m)
      intro a ha hap
      have hh := hSecond a ha (lt_of_lt_of_le hap hpml)
      convert hh using 1
      rw [show 1 - l + a = (1 + a) - l by ring, hper.sub_eq]
    exact congrFun hh
  intro z
  calc
    c (z + 2) = c (m - 1 - z) := by
      convert hReflect1 (z + 1) using 1 <;> congr 1 <;> ring
    _ = c z := (hReflect0 z).symm

/-- Every simple path of a fixed length has equally coloured endpoints. -/
def PathMonochromatic {V A : Type*} (G : SimpleGraph V) (c : V → A) (l : ℤ) : Prop :=
  ∀ p : ℤ → V, Set.InjOn p (Set.Icc 0 l) →
    (∀ i, 0 ≤ i → i < l → G.Adj (p i) (p (i + 1))) → c (p 0) = c (p l)

lemma eq_of_dvd_of_bounds {n a b : ℤ} (hdiv : n ∣ a - b)
    (hlo : -n < a - b) (hhi : a - b < n) : a = b := by
  rcases le_total b a with h | h
  · have hh := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ a - b) hhi hdiv
    omega
  · have hd : n ∣ b - a := by simpa only [neg_sub] using dvd_neg.mpr hdiv
    have hh := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ b - a)
      (by omega : b - a < n) hd
    omega

lemma endpoints_equal_of_positions {V A : Type*} {G : SimpleGraph V} {c : V → A}
    {l n m : ℤ} (hc : PathMonochromatic G c l) (f : ℤ → V)
    (hinj : ∀ i j, f i = f j → n ∣ i - j)
    (hadj : ∀ i, G.Adj (f i) (f (i + 1))) (hchord : G.Adj (f 0) (f m))
    (p : ℤ → ℤ) (hp : Set.InjOn p (Set.Icc 0 l))
    (hb : ∀ i ∈ Set.Icc 0 l, ∀ j ∈ Set.Icc 0 l, -n < p i - p j ∧ p i - p j < n)
    (hs : ∀ i, 0 ≤ i → i < l →
      p (i + 1) = p i + 1 ∨ p i = p (i + 1) + 1 ∨ p i = 0 ∧ p (i + 1) = m) :
    c (f (p 0)) = c (f (p l)) := by
  apply hc (f ∘ p)
  · intro i hi j hj hij
    exact hp hi hj (eq_of_dvd_of_bounds (hinj _ _ hij) (hb i hi j hj).1 (hb i hi j hj).2)
  · intro i hi hil
    change G.Adj (f (p i)) (f (p (i + 1)))
    rcases hs i hi hil with h | h | ⟨h, h'⟩
    · rw [h]; exact hadj _
    · rw [h]; exact (hadj _).symm
    · rw [h, h']; exact hchord

lemma two_periodic_of_long_chorded_cycle {V A : Type*} {G : SimpleGraph V} {c : V → A}
    {l n m : ℤ} (hl : 0 < l) (hm : 1 < m) (hml : m + l ≤ n)
    (hc : PathMonochromatic G c l) (f : ℤ → V)
    (hinj : ∀ i j, f i = f j → n ∣ i - j)
    (hadj : ∀ i, G.Adj (f i) (f (i + 1))) (hchord : G.Adj (f 0) (f m)) :
    Function.Periodic (c ∘ f) 2 := by
  have hper : Function.Periodic (c ∘ f) l := by
    intro z
    have hh := hc (fun i => f (z + i)) ?_ ?_
    · simpa only [Function.comp_apply, add_zero] using hh.symm
    · intro i hi j hj hij
      dsimp at hij
      have hd := hinj _ _ hij
      have hh := eq_of_dvd_of_bounds hd (by rcases hi with ⟨_, _⟩; rcases hj with ⟨_, _⟩; omega)
        (by rcases hi with ⟨_, _⟩; rcases hj with ⟨_, _⟩; omega)
      omega
    · intro i hi hil
      simpa only [add_assoc] using hadj (z + i)
  apply periodic_of_chord_paths hl hm hper
  · intro a ha hal
    let p : ℤ → ℤ := fun i => if i ≤ a then i - a else m + i - a - 1
    have hh := endpoints_equal_of_positions hc f hinj hadj hchord p ?_ ?_ ?_
    · simpa only [Function.comp_apply, p, if_pos ha, if_neg (by omega : ¬l ≤ a), zero_sub, show m + l - a - 1 = m + l - 1 - a by ring] using hh
    · intro i hi j hj hij
      dsimp [p] at hij
      split_ifs at hij <;> omega
    · intro i hi j hj
      dsimp [p]
      rcases hi with ⟨hi0, hil⟩; rcases hj with ⟨hj0, hjl⟩
      split_ifs <;> constructor <;> omega
    · intro i hi hil
      dsimp [p]
      split_ifs <;> omega
  · intro a ha hal
    have ham : a < m := lt_of_lt_of_le hal (min_le_left _ _)
    have hal' : a < l := lt_of_lt_of_le hal (min_le_right _ _)
    let p : ℤ → ℤ := fun i => if i ≤ a then a - i else m + i - a - 1
    have hh := endpoints_equal_of_positions hc f hinj hadj hchord p ?_ ?_ ?_
    · simpa only [Function.comp_apply, p, if_pos ha, if_neg (by omega : ¬l ≤ a), sub_zero, show m + l - a - 1 = m + l - 1 - a by ring] using hh
    · intro i hi j hj hij
      dsimp [p] at hij
      rcases hi with ⟨hi0, hil⟩; rcases hj with ⟨hj0, hjl⟩
      split_ifs at hij <;> omega
    · intro i hi j hj
      dsimp [p]
      rcases hi with ⟨hi0, hil⟩; rcases hj with ⟨hj0, hjl⟩
      split_ifs <;> constructor <;> omega
    · intro i hi hil
      dsimp [p]
      split_ifs <;> omega
  · intro a ha hal
    have ham : a < m := lt_of_lt_of_le hal (min_le_left _ _)
    have hal' : a < l := lt_of_lt_of_le hal (min_le_right _ _)
    let b : ℤ := l - 1 - a
    have hb : 0 ≤ b := by dsimp [b]; omega
    have hbl : b < l := by dsimp [b]; omega
    let p : ℤ → ℤ := fun i => if i ≤ b then i - b else m - i + b + 1
    have hh := endpoints_equal_of_positions hc f hinj hadj hchord p ?_ ?_ ?_
    · have he0 : p 0 = 1 - l + a := by
        dsimp only [p]
        rw [if_pos hb]
        dsimp [b]
        ring
      have hel : p l = m - a := by
        dsimp only [p]
        rw [if_neg (by omega : ¬l ≤ b)]
        dsimp [b]
        ring
      simpa only [Function.comp_apply, he0, hel] using hh
    · intro i hi j hj hij
      dsimp [p] at hij
      rcases hi with ⟨hi0, hil⟩; rcases hj with ⟨hj0, hjl⟩
      dsimp [b] at hij
      split_ifs at hij <;> omega
    · intro i hi j hj
      dsimp [p, b]
      rcases hi with ⟨hi0, hil⟩; rcases hj with ⟨hj0, hjl⟩
      split_ifs <;> constructor <;> omega
    · intro i hi hil
      dsimp [p]
      split_ifs <;> omega

def cyclicLift {V : Type*} (n : ℕ) (f : ℕ → V) (i : ℤ) : V :=
  f ((i % (n : ℤ)).toNat)

lemma cyclicLift_nat {V : Type*} {n : ℕ} (f : ℕ → V) {i : ℕ} (hi : i < n) :
    cyclicLift n f i = f i := by
  simp only [cyclicLift, Int.emod_eq_of_lt (Int.natCast_nonneg i) (show (i : ℤ) < (n : ℤ) by exact_mod_cast hi),
    Int.toNat_natCast]

lemma cyclicLift_inj {V : Type*} {n : ℕ} (hn : 0 < n) (f : ℕ → V)
    (hf : Set.InjOn f (Set.Iio n)) (i j : ℤ) (hij : cyclicLift n f i = cyclicLift n f j) :
    (n : ℤ) ∣ i - j := by
  have hn' : 0 < (n : ℤ) := by exact_mod_cast hn
  have hpos (z : ℤ) : 0 ≤ z % (n : ℤ) := Int.emod_nonneg _ hn'.ne'
  have hlt (z : ℤ) : z % (n : ℤ) < n := Int.emod_lt_of_pos _ hn'
  have hIn (z : ℤ) : (z % (n : ℤ)).toNat ∈ Set.Iio n :=
    (Int.toNat_lt (hpos z)).mpr (hlt z)
  have hh := hf (hIn i) (hIn j) hij
  have hh' := congrArg (fun k : ℕ => (k : ℤ)) hh
  simp only [Int.toNat_of_nonneg (hpos i), Int.toNat_of_nonneg (hpos j)] at hh'
  exact Int.modEq_iff_dvd.mp hh'.symm

lemma cyclicLift_adj {V : Type*} {G : SimpleGraph V} {n : ℕ} (hn : 2 ≤ n) (f : ℕ → V)
    (hs : ∀ i, i + 1 < n → G.Adj (f i) (f (i + 1)))
    (he : G.Adj (f (n - 1)) (f 0)) (z : ℤ) :
    G.Adj (cyclicLift n f z) (cyclicLift n f (z + 1)) := by
  have hn' : 0 < (n : ℤ) := by omega
  have hz0 := Int.emod_nonneg z hn'.ne'
  have hzn := Int.emod_lt_of_pos z hn'
  have hStep : (z + 1) % (n : ℤ) = (z % (n : ℤ) + 1) % (n : ℤ) := by
    rw [Int.add_emod, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ 1) (by omega : (1 : ℤ) < n)]
  dsimp only [cyclicLift]
  rw [hStep]
  by_cases hz : z % (n : ℤ) + 1 = n
  · rw [hz, Int.emod_self, Int.toNat_zero]
    have hh : (z % (n : ℤ)).toNat = n - 1 := by omega
    rw [hh]
    exact he
  · rw [Int.emod_eq_of_lt (by omega : 0 ≤ z % (n : ℤ) + 1) (by omega)]
    rw [Int.toNat_add hz0 (by omega)]
    exact hs _ (by omega)

lemma colours_equal_on_cycle_parity {V A : Type*} {G : SimpleGraph V} {c : V → A}
    {l n m : ℕ} (hl : 0 < l) (hm : 1 < m) (hml : m + l ≤ n)
    (hc : PathMonochromatic G c l) (f : ℕ → V) (hf : Set.InjOn f (Set.Iio n))
    (hs : ∀ i, i + 1 < n → G.Adj (f i) (f (i + 1)))
    (he : G.Adj (f (n - 1)) (f 0)) (hchord : G.Adj (f 0) (f m))
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i % 2 = j % 2) : c (f i) = c (f j) := by
  have hper : Function.Periodic (c ∘ cyclicLift n f) 2 := by
    apply two_periodic_of_long_chorded_cycle (n := (n : ℤ)) (m := (m : ℤ))
      (by exact_mod_cast hl) (by exact_mod_cast hm)
      (by exact_mod_cast hml) hc _ (cyclicLift_inj (by omega) f hf)
      (cyclicLift_adj (by omega) f hs he)
    simpa only [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
      cyclicLift_nat f (show 0 < n by omega), cyclicLift_nat f (show m < n by omega)] using hchord
  have hi' := periodic_mod hper (i : ℤ)
  have hj' := periodic_mod hper (j : ℤ)
  have heq : (i : ℤ) % 2 = (j : ℤ) % 2 := by exact_mod_cast hij
  rw [heq] at hi'
  have hh := hi'.symm.trans hj'
  simpa only [Function.comp_apply, cyclicLift_nat f hi, cyclicLift_nat f hj] using hh

open scoped Classical in
lemma exists_long_chorded_cycle {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (l : ℕ) (hl : 0 < l) (hd : ∀ v, l + 2 ≤ G.degree v) :
    ∃ (n m : ℕ) (f : ℕ → V), 1 < m ∧ m + l ≤ n ∧ Set.InjOn f (Set.Iio n) ∧
      (∀ i, i + 1 < n → G.Adj (f i) (f (i + 1))) ∧
      G.Adj (f (n - 1)) (f 0) ∧ G.Adj (f 0) (f m) := by
  classical
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hNbr {w : V} (hw : G.Adj u w) : w ∈ p.support := by
    by_contra hh
    have hpath : (p.cons hw.symm).IsPath := Walk.cons_isPath_iff _ _ |>.mpr ⟨hp, hh⟩
    have he := hmax w v (p.cons hw.symm) hpath
    simp only [Walk.length_cons] at he
    omega
  let S : Finset ℕ := (Finset.range (p.length + 1)).filter (fun i => G.Adj u (p.getVert i))
  have hS (i : ℕ) : i ∈ S ↔ i ≤ p.length ∧ G.Adj u (p.getVert i) := by
    simp only [S, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hCard : S.card = G.degree u := by
    rw [← card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun i _ => p.getVert i)
    · intro i hi
      exact (mem_neighborFinset G u _).mpr ((hS i).mp hi).2
    · intro i hi j hj hij
      exact hp.getVert_injOn ((hS i).mp hi).1 ((hS j).mp hj).1 hij
    · intro w hw
      obtain ⟨i, hiw, hi⟩ := Walk.mem_support_iff_exists_getVert.mp
        (hNbr ((mem_neighborFinset G u w).mp hw))
      exact ⟨i, (hS i).mpr ⟨hi, by simpa only [hiw] using (mem_neighborFinset G u w).mp hw⟩, hiw⟩
  have hS0 : 0 ∉ S := by
    intro hh
    have hbad := ((hS 0).mp hh).2
    exact G.loopless u (by simpa only [Walk.getVert_zero] using hbad)
  have hCard' : l + 2 ≤ S.card := by rw [hCard]; exact hd u
  have hNonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  let t := S.max' hNonempty
  have ht : t ∈ S := Finset.max'_mem S hNonempty
  have htlen : t ≤ p.length := ((hS t).mp ht).1
  have hErCard : l + 1 ≤ (S.erase 1).card := by
    have hh : S.card - 1 ≤ (S.erase 1).card := Finset.pred_card_le_card_erase
    omega
  have hEr : (S.erase 1).Nonempty := Finset.card_pos.mp (by omega)
  let m := (S.erase 1).min' hEr
  have hmMem : m ∈ S.erase 1 := Finset.min'_mem _ hEr
  have hmS : m ∈ S := Finset.mem_of_mem_erase hmMem
  have hm1 : m ≠ 1 := (Finset.mem_erase.mp hmMem).1
  have hm0 : m ≠ 0 := fun hh => hS0 (hh ▸ hmS)
  have hm : 1 < m := by omega
  have hSub : S.erase 1 ⊆ Finset.Icc m t := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ i hi,
      Finset.le_max' S i (Finset.mem_of_mem_erase hi)⟩
  have hGap := Finset.card_le_card hSub
  rw [Nat.card_Icc] at hGap
  have hml : m + l ≤ t + 1 := by omega
  refine ⟨t + 1, m, p.getVert, hm, hml, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    exact hp.getVert_injOn (x₁ := i) (x₂ := j)
      (by change i ≤ p.length; change i < t + 1 at hi; omega)
      (by change j ≤ p.length; change j < t + 1 at hj; omega) hij
  · intro i hi
    exact p.adj_getVert_succ (by omega)
  · simpa only [Nat.add_sub_cancel, Walk.getVert_zero] using ((hS t).mp ht).2.symm
  · simpa only [Walk.getVert_zero] using ((hS m).mp hmS).2

open Fin.NatCast
lemma colours_equal_on_fin_cycle {A : Type*} {n m l : ℕ} [NeZero n]
    (D : SimpleGraph (Fin n)) (c : Fin n → A) (hl : 0 < l) (hm : 1 < m) (hml : m + l ≤ n)
    (hc : PathMonochromatic D c l) (hs : ∀ x, D.Adj x (x + 1)) (he : D.Adj 0 (↑m : Fin n))
    {x y : Fin n} (hxy : x.val % 2 = y.val % 2) : c x = c y := by
  have hNat : Set.InjOn (fun i : ℕ => (↑i : Fin n)) (Set.Iio n) := by
    intro i hi j hj hij
    have hh := congrArg Fin.val hij
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hh
  have hStep (i : ℕ) (_hi : i + 1 < n) : D.Adj (↑i : Fin n) (↑(i + 1) : Fin n) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hs (↑i : Fin n)
  have hEnd : D.Adj (↑(n - 1) : Fin n) (0 : Fin n) := by
    have hh := hs (↑(n - 1) : Fin n)
    have heq : (↑(n - 1) : Fin n) + 1 = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_natCast, Fin.val_one', Fin.val_zero]
      rw [Nat.mod_eq_of_lt (by omega : n - 1 < n), Nat.mod_eq_of_lt (by omega : 1 < n),
        Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
    rwa [heq] at hh
  have hh := colours_equal_on_cycle_parity hl hm hml hc (fun i : ℕ => (↑i : Fin n)) hNat
    hStep hEnd he x.isLt y.isLt hxy
  simpa only [Fin.cast_val_eq_self] using hh

#print axioms colours_equal_on_fin_cycle

end Erdos713EvenCycle
