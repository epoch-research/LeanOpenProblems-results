import FormalConjecturesUtil
import Submission.CompactBlockAssemblyAudit

/-! Compact extraction of the verified even-cycle upper bound and the C10 rate. -/

/- Path-colouring lemmas for an even cycle with a chord. -/

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


end Erdos713EvenCycle

/- Breadth-first ancestry and the construction of cycles from layer paths. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713BreadthFirst

lemma contained_of_cyclic_chain {V : Type*} (G : SimpleGraph V) {n : ℕ} (hn : 3 ≤ n)
    (f : ℕ → V) (hf : Set.InjOn f (Set.Iio n))
    (hs : ∀ i, i + 1 < n → G.Adj (f i) (f (i + 1)))
    (he : G.Adj (f (n - 1)) (f 0)) : cycleGraph n ⊑ G := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  let g : Fin (k + 2) → V := fun i => f i.val
  have hStep (i : Fin (k + 2)) : G.Adj (g i) (g (i + 1)) := by
    by_cases hi : i.val + 1 < k + 2
    · have hh : (i + 1).val = i.val + 1 := by
        simp only [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt hi]
      simpa only [g, hh] using hs i.val hi
    · have hi' : i.val = k + 1 := by omega
      have hh : (i + 1).val = 0 := by simp [Fin.val_add, Fin.val_one, hi']
      simpa only [g, hi', hh, Nat.add_sub_cancel] using he
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro u v huv
    rcases cycleGraph_adj.mp huv with h | h
    · rw [sub_eq_iff_eq_add'.mp h]
      exact (hStep v).symm
    · rw [sub_eq_iff_eq_add'.mp h]
      exact hStep u
  · intro i j hij
    apply Fin.ext
    exact hf i.isLt j.isLt hij

lemma cycle_of_two_paths {V : Type*} (G : SimpleGraph V) {l m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hn : 3 ≤ l + m) (p q : ℕ → V)
    (hp : Set.InjOn p (Set.Iic l)) (hq : Set.InjOn q (Set.Iic m))
    (hs : ∀ i, i < l → G.Adj (p i) (p (i + 1)))
    (ht : ∀ i, i < m → G.Adj (q i) (q (i + 1)))
    (hStart : p 0 = q m) (hEnd : p l = q 0)
    (hCross : ∀ i ≤ l, ∀ j ≤ m, p i = q j → (i = 0 ∧ j = m) ∨ (i = l ∧ j = 0)) :
    cycleGraph (l + m) ⊑ G := by
  let f : ℕ → V := fun i => if i ≤ l then p i else q (i - l)
  apply contained_of_cyclic_chain G hn f
  · intro i hi j hj hij
    change i < l + m at hi
    change j < l + m at hj
    dsimp [f] at hij
    split_ifs at hij with hi' hj' hj'
    · exact hp hi' hj' hij
    · have hh := hCross i hi' (j - l) (by omega) hij
      omega
    · have hh := hCross j hj' (i - l) (by omega) hij.symm
      omega
    · have hh := hq (by change i - l ≤ m; omega) (by change j - l ≤ m; omega) hij
      omega
  · intro i hi
    dsimp only [f]
    by_cases hil : i < l
    · rw [if_pos (by omega), if_pos (by omega)]
      exact hs i hil
    by_cases he : i = l
    · subst i
      rw [if_pos le_rfl, if_neg (by omega), hEnd]
      simpa using ht 0 hm
    · rw [if_neg (by omega), if_neg (by omega)]
      have hh := ht (i - l) (by omega)
      simpa only [show i + 1 - l = i - l + 1 by omega] using hh
  · have hlast : l ≤ l + m - 1 := by omega
    dsimp only [f]
    rw [if_pos (by omega : 0 ≤ l)]
    by_cases hm1 : m = 1
    · subst m
      simp only [Nat.add_sub_cancel, if_pos le_rfl]
      rw [hEnd, hStart]
      exact ht 0 (by omega)
    · rw [if_neg (by omega : ¬l + m - 1 ≤ l), hStart]
      have hh := ht (m - 1) (by omega)
      simpa only [show l + m - 1 - l = m - 1 by omega, Nat.sub_add_cancel hm] using hh

structure Layering {V : Type*} (G : SimpleGraph V) (root : V) where
  level : V → ℕ
  zero_iff : ∀ v, level v = 0 ↔ v = root
  parent : V → V
  parent_adj : ∀ v, v ≠ root → G.Adj v (parent v)
  parent_level : ∀ v, v ≠ root → level (parent v) + 1 = level v

namespace Layering
variable {V : Type*} {G : SimpleGraph V} {root : V} (L : Layering G root)

lemma level_iterate (v : V) (n : ℕ) (hn : n ≤ L.level v) :
    L.level (L.parent^[n] v) = L.level v - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (by omega)
    have hv : L.parent^[n] v ≠ root := by
      intro hh
      have hz : L.level (L.parent^[n] v) = 0 := (L.zero_iff _).mpr hh
      omega
    have hh := L.parent_level _ hv
    rw [Function.iterate_succ_apply']
    omega

def ancestor (v : V) (j : ℕ) : V := L.parent^[L.level v - j] v

lemma ancestor_level (v : V) {j : ℕ} (hj : j ≤ L.level v) :
    L.level (L.ancestor v j) = j := by
  dsimp [ancestor]
  rw [L.level_iterate _ _ (Nat.sub_le _ _)]
  omega

lemma ancestor_top (v : V) : L.ancestor v (L.level v) = v := by simp [ancestor]

lemma ancestor_zero (v : V) : L.ancestor v 0 = root :=
  (L.zero_iff _).mp (L.ancestor_level v (Nat.zero_le _))

lemma ancestor_parent (v : V) {j : ℕ} (hj : j < L.level v) :
    L.parent (L.ancestor v (j + 1)) = L.ancestor v j := by
  dsimp [ancestor]
  rw [← Function.iterate_succ_apply' (f := L.parent) (L.level v - (j + 1)) v]
  congr 1
  omega

lemma ancestor_adj (v : V) {j : ℕ} (hj : j < L.level v) :
    G.Adj (L.ancestor v j) (L.ancestor v (j + 1)) := by
  have hv : L.ancestor v (j + 1) ≠ root := by
    intro hh
    have hz := (L.zero_iff _).mpr hh
    rw [L.ancestor_level v (by omega)] at hz
    omega
  have hh := (L.parent_adj _ hv).symm
  rwa [L.ancestor_parent v hj] at hh

lemma ancestor_ancestor (v : V) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L.level v) :
    L.ancestor (L.ancestor v j) i = L.ancestor v i := by
  dsimp only [ancestor]
  rw [L.level_iterate _ _ (Nat.sub_le _ _)]
  rw [← Function.iterate_add_apply]
  congr 1
  omega

lemma ancestor_coalesce {v w : V} {i j : ℕ} (hij : i ≤ j)
    (hv : j ≤ L.level v) (hw : j ≤ L.level w)
    (he : L.ancestor v j = L.ancestor w j) : L.ancestor v i = L.ancestor w i := by
  rw [← L.ancestor_ancestor v hij hv, he, L.ancestor_ancestor w hij hw]

end Layering

lemma exists_dist_predecessor {V : Type*} (G : SimpleGraph V) (hconn : G.Connected)
    (root v : V) (hv : v ≠ root) :
    ∃ w, G.Adj v w ∧ G.dist root w + 1 = G.dist root v := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v root
  cases p with
  | nil => exact (hv rfl).elim
  | @cons v w root h p =>
    refine ⟨w, h, ?_⟩
    have hlo := G.dist_le p
    have hhi := hconn.dist_triangle (u := v) (v := w) (w := root)
    rw [dist_eq_one_iff_adj.mpr h] at hhi
    simp only [Walk.length_cons] at hp
    rw [dist_comm (u := root) (v := w), dist_comm (u := root) (v := v)]
    omega

noncomputable def Layering.ofConnected {V : Type*} (G : SimpleGraph V)
    (hconn : G.Connected) (root : V) : Layering G root := by
  classical
  let p : V → V := fun v => if h : v = root then root
    else (exists_dist_predecessor G hconn root v h).choose
  refine ⟨G.dist root, fun v => hconn.dist_eq_zero_iff.trans eq_comm, p, ?_, ?_⟩
  · intro v hv
    dsimp only [p]
    rw [dif_neg hv]
    exact (exists_dist_predecessor G hconn root v hv).choose_spec.1
  · intro v hv
    dsimp only [p]
    rw [dif_neg hv]
    exact (exists_dist_predecessor G hconn root v hv).choose_spec.2

lemma colouring_path_parity {V : Type*} {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    {u v : V} (p : G.Walk u v) : ((χ u).val + p.length) % 2 = (χ v).val := by
  induction p with
  | nil => simpa using Nat.mod_eq_of_lt (χ _).isLt
  | @cons u w v h p ih =>
    have hu := (χ u).isLt
    have hw := (χ w).isLt
    have hne : (χ u).val ≠ (χ w).val := fun hh => χ.valid h (Fin.ext hh)
    simp only [Walk.length_cons]
    omega

lemma adj_dist_diff_one {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    (hBip : G.IsBipartite) (root : V) {u v : V} (huv : G.Adj u v) :
    G.dist root u + 1 = G.dist root v ∨ G.dist root v + 1 = G.dist root u := by
  obtain ⟨χ⟩ := hBip
  have hNe : G.dist root u ≠ G.dist root v := by
    intro hh
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist root u
    obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist root v
    have hc1 := colouring_path_parity χ p
    have hc2 := colouring_path_parity χ q
    rw [hp, hh] at hc1
    rw [hq] at hc2
    exact χ.valid huv (Fin.ext (hc1.symm.trans hc2))
  have hh := huv.diff_dist_adj (u := root)
  omega

lemma Layering.path_below {V : Type*} {G : SimpleGraph V} {root : V}
    (L : Layering G root) {a b : V} {i j : ℕ} (ha : L.level a = i) (hb : L.level b = i)
    (hj : j < i) (hc : L.ancestor a j = L.ancestor b j)
    (hne : L.ancestor a (j + 1) ≠ L.ancestor b (j + 1)) :
    ∃ q : ℕ → V, q 0 = b ∧ q (2 * (i - j)) = a ∧
      Set.InjOn q (Set.Iic (2 * (i - j))) ∧
      (∀ t, t < 2 * (i - j) → G.Adj (q t) (q (t + 1))) ∧
      (∀ t, 0 < t → t < 2 * (i - j) → L.level (q t) < i) := by
  let d := i - j
  have hd : 0 < d := by dsimp [d]; omega
  have hid : j + d = i := by dsimp [d]; omega
  let q : ℕ → V := fun t => if t ≤ d then L.ancestor b (i - t)
    else L.ancestor a (j + (t - d))
  have hCross (t s : ℕ) (ht : t ≤ d) (hs : d < s) (hs' : s ≤ 2 * d) :
      L.ancestor b (i - t) ≠ L.ancestor a (j + (s - d)) := by
    intro he
    have hEq := congrArg L.level he
    rw [L.ancestor_level b (by omega), L.ancestor_level a (by omega)] at hEq
    have hr : j + 1 ≤ i - t := by omega
    rw [← hEq] at he
    have hh := L.ancestor_coalesce hr (by omega : i - t ≤ L.level b)
      (by omega : i - t ≤ L.level a) he
    exact hne hh.symm
  refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [q]
    rw [if_pos (Nat.zero_le _), Nat.sub_zero, ← hb, L.ancestor_top]
  · dsimp only [q]
    rw [if_neg (by omega : ¬2 * (i - j) ≤ d)]
    have he : j + (2 * (i - j) - d) = i := by dsimp [d]; omega
    rw [he, ← ha, L.ancestor_top]
  · intro t ht s hs he
    change t ≤ 2 * (i - j) at ht
    change s ≤ 2 * (i - j) at hs
    change t ≤ 2 * d at ht
    change s ≤ 2 * d at hs
    dsimp only [q] at he
    split_ifs at he with ht' hs' hs'
    · have hh := congrArg L.level he
      rw [L.ancestor_level b (by omega), L.ancestor_level b (by omega)] at hh
      omega
    · exact (hCross t s ht' (by omega) hs he).elim
    · exact (hCross s t hs' (by omega) ht he.symm).elim
    · have hh := congrArg L.level he
      rw [L.ancestor_level a (by omega), L.ancestor_level a (by omega)] at hh
      omega
  · intro t ht
    change t < 2 * d at ht
    dsimp only [q]
    by_cases ht' : t < d
    · rw [if_pos (by omega), if_pos (by omega)]
      have hh := (L.ancestor_adj b (j := i - (t + 1)) (by omega)).symm
      simpa only [show i - (t + 1) + 1 = i - t by omega] using hh
    by_cases htd : t = d
    · subst t
      rw [if_pos le_rfl, if_neg (by omega)]
      have hleft : i - d = j := by omega
      have hright : j + (d + 1 - d) = j + 1 := by omega
      rw [hleft, hright, ← hc]
      exact L.ancestor_adj a (by omega)
    · rw [if_neg (by omega), if_neg (by omega)]
      have hh := L.ancestor_adj a (j := j + (t - d)) (by omega)
      simpa only [show j + (t + 1 - d) = j + (t - d) + 1 by omega] using hh
  · intro t ht ht'
    change t < 2 * d at ht'
    dsimp only [q]
    split_ifs with htd
    · rw [L.ancestor_level b (by omega)]
      omega
    · rw [L.ancestor_level a (by omega)]
      omega

lemma Layering.cycle_of_layer_path {V : Type*} {G : SimpleGraph V} {root : V}
    (L : Layering G root) {i j l : ℕ} (hj : j < i) (hl : 0 < l)
    (hn : 3 ≤ l + 2 * (i - j)) (p : ℕ → V)
    (hp : Set.InjOn p (Set.Iic l)) (hs : ∀ t, t < l → G.Adj (p t) (p (t + 1)))
    (hlevels : ∀ t ≤ l, i ≤ L.level (p t))
    (hstart : L.level (p 0) = i) (hend : L.level (p l) = i)
    (hc : L.ancestor (p 0) j = L.ancestor (p l) j)
    (hne : L.ancestor (p 0) (j + 1) ≠ L.ancestor (p l) (j + 1)) :
    cycleGraph (l + 2 * (i - j)) ⊑ G := by
  obtain ⟨q, hq0, hqEnd, hqInj, hqAdj, hqLev⟩ := L.path_below hstart hend hj hc hne
  apply cycle_of_two_paths G hl (by omega) hn p q hp hqInj hs hqAdj hqEnd.symm hq0.symm
  intro t ht s hs he
  by_cases hs0 : s = 0
  · subst s
    rw [hq0] at he
    exact Or.inr ⟨hp ht (show l ∈ Set.Iic l from Nat.le_refl l) he, rfl⟩
  by_cases hsEnd : s = 2 * (i - j)
  · subst s
    rw [hqEnd] at he
    exact Or.inl ⟨hp ht (show 0 ∈ Set.Iic l from Nat.zero_le _) he, rfl⟩
  have hh := hqLev s (by omega) (by omega)
  rw [← he] at hh
  exact (not_lt_of_ge (hlevels t ht) hh).elim

lemma colouring_chain_parity {V : Type*} {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    (p : ℕ → V) (l : ℕ) (hs : ∀ t, t < l → G.Adj (p t) (p (t + 1))) :
    ((χ (p 0)).val + l) % 2 = (χ (p l)).val := by
  induction l with
  | zero => simpa using Nat.mod_eq_of_lt (χ (p 0)).isLt
  | succ l ih =>
    have hh := ih (fun t ht => hs t (by omega))
    have hne : (χ (p l)).val ≠ (χ (p (l + 1))).val :=
      fun he => χ.valid (hs l (by omega)) (Fin.ext he)
    have h0 := (χ (p 0)).isLt
    have h1 := (χ (p l)).isLt
    have h2 := (χ (p (l + 1))).isLt
    omega

lemma pullback_cycle_step {V : Type*} (G : SimpleGraph V) {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (f : ℕ → V) (hs : ∀ i, i + 1 < n → G.Adj (f i) (f (i + 1)))
    (he : G.Adj (f (n - 1)) (f 0)) :
    ∀ x : Fin n, (G.comap (fun x : Fin n => f x.val)).Adj x (x + 1) := by
  intro x
  change G.Adj (f x.val) (f (x + 1).val)
  by_cases hx : x.val + 1 < n
  · have hh : (x + 1).val = x.val + 1 := by
      simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n),
        Nat.mod_eq_of_lt hx]
    rw [hh]
    exact hs _ hx
  · have hx' : x.val = n - 1 := by omega
    have hh : (x + 1).val = 0 := by
      simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), hx']
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
    rw [hx', hh]
    exact he

open scoped Classical in
noncomputable def levelColouring {V : Type*} {G K : SimpleGraph V} {root : V}
    (L : Layering G root) (i : ℕ)
    (hK : ∀ u v, K.Adj u v →
      (L.level u = i ∧ L.level v = i + 1) ∨ (L.level u = i + 1 ∧ L.level v = i)) :
    K.Coloring (Fin 2) where
  toFun v := if L.level v = i then 0 else 1
  map_rel' := by
    intro u v huv
    change (if L.level u = i then (0 : Fin 2) else 1) ≠
      (if L.level v = i then (0 : Fin 2) else 1)
    rcases hK u v huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> simp [hu, hv]

open Fin.NatCast

lemma Layering.ancestors_equal_on_chorded_cycle {V : Type*} {G : SimpleGraph V} {root : V}
    (L : Layering G root) {k i n m : ℕ} [NeZero n] (hk : 2 ≤ k) (hi : i < k)
    (hm : 1 < m) (hLong : m + (2 * k - 2) ≤ n)
    (D : SimpleGraph (Fin n)) (e : Fin n → V) (he : Function.Injective e)
    (hMap : ∀ x y, D.Adj x y → G.Adj (e x) (e y))
    (hLevel : ∀ x y, D.Adj x y →
      (L.level (e x) = i ∧ L.level (e y) = i + 1) ∨
      (L.level (e x) = i + 1 ∧ L.level (e y) = i))
    (hStep : ∀ x, D.Adj x (x + 1)) (hChord : D.Adj 0 (m : Fin n))
    (hFree : (cycleGraph (2 * k)).Free G) :
    ∀ j ≤ i, ∀ x y, L.level (e x) = i → L.level (e y) = i →
      L.ancestor (e x) j = L.ancestor (e y) j := by
  classical
  let χ : D.Coloring (Fin 2) :=
    { toFun := fun x => if L.level (e x) = i then 0 else 1
      map_rel' := by
        intro x y hxy
        change (if L.level (e x) = i then (0 : Fin 2) else 1) ≠
          (if L.level (e y) = i then (0 : Fin 2) else 1)
        rcases hLevel x y hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [hx, hy] }
  have hχ (x : Fin n) : χ x = (if L.level (e x) = i then 0 else 1) := rfl
  have hRange (x : Fin n) : L.level (e x) = i ∨ L.level (e x) = i + 1 := by
    rcases hLevel x (x + 1) (hStep x) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hFormula (x : Fin n) : ((χ 0).val + x.val) % 2 = (χ x).val := by
    have hh := colouring_chain_parity χ (fun t : ℕ => (t : Fin n)) x.val
      (fun t _ => by simpa only [Nat.cast_add, Nat.cast_one] using hStep (t : Fin n))
    simpa only [Nat.cast_zero, Fin.cast_val_eq_self] using hh
  have hParity (x y : Fin n) (hx : L.level (e x) = i) (hy : L.level (e y) = i) :
      x.val % 2 = y.val % 2 := by
    have hhx := hFormula x
    have hhy := hFormula y
    have hχx : χ x = 0 := by rw [hχ, if_pos hx]
    have hχy : χ y = 0 := by rw [hχ, if_pos hy]
    rw [hχx] at hhx
    rw [hχy] at hhy
    have hh0 := (χ 0).isLt
    simp only [Fin.val_zero] at hhx hhy
    omega
  intro j
  induction j with
  | zero => intro _ x y _ _; rw [L.ancestor_zero, L.ancestor_zero]
  | succ j ih =>
    intro hj x y hx hy
    let l := 2 * (k - i + j)
    have hl : 0 < l := by dsimp [l]; omega
    have hll : l ≤ 2 * k - 2 := by dsimp [l]; omega
    have hj' : j < i := by omega
    have hnEq : l + 2 * (i - j) = 2 * k := by dsimp [l]; omega
    let c : Fin n → Option V := fun z => if L.level (e z) = i
      then some (L.ancestor (e z) (j + 1)) else none
    have hMono : Erdos713EvenCycle.PathMonochromatic D c l := by
      intro p hp hAdj
      have hSame : χ (p 0) = χ (p (l : ℤ)) := by
        have hh := colouring_chain_parity χ (fun t : ℕ => p (t : ℤ)) l (by
          intro t ht
          simpa only [Nat.cast_add, Nat.cast_one] using hAdj (t : ℤ)
            (Int.natCast_nonneg t) (by exact_mod_cast ht))
        simp only [Nat.cast_zero] at hh
        have hc0 := (χ (p 0)).isLt
        have hEven : l % 2 = 0 := by dsimp [l]; omega
        apply Fin.ext
        omega
      by_cases ha : L.level (e (p 0)) = i
      · have hb : L.level (e (p (l : ℤ))) = i := by
          by_contra hb
          have hχa : χ (p 0) = 0 := by rw [hχ, if_pos ha]
          have hχb : χ (p (l : ℤ)) = 1 := by rw [hχ, if_neg hb]
          rw [hχa, hχb] at hSame
          exact (by decide : (0 : Fin 2) ≠ 1) hSame
        have hAnc : L.ancestor (e (p 0)) (j + 1) = L.ancestor (e (p (l : ℤ))) (j + 1) := by
          by_contra hne
          have hCycle := L.cycle_of_layer_path hj' hl (by omega : 3 ≤ l + 2 * (i - j))
            (fun t : ℕ => e (p (t : ℤ))) ?_ ?_ ?_ ha hb (ih (by omega) _ _ ha hb) hne
          · rw [hnEq] at hCycle
            exact hFree hCycle
          · intro t ht s hs hEq
            have hh := hp (show (t : ℤ) ∈ Set.Icc 0 (l : ℤ) from
                ⟨Int.natCast_nonneg t, by exact_mod_cast ht⟩)
              (show (s : ℤ) ∈ Set.Icc 0 (l : ℤ) from
                ⟨Int.natCast_nonneg s, by exact_mod_cast hs⟩) (he hEq)
            exact_mod_cast hh
          · intro t ht
            apply hMap
            simpa only [Nat.cast_add, Nat.cast_one] using hAdj (t : ℤ)
              (Int.natCast_nonneg t) (by exact_mod_cast ht)
          · intro t _
            change i ≤ L.level (e (p (t : ℤ)))
            rcases hRange (p (t : ℤ)) with h | h <;> omega
        simp only [c, if_pos ha, if_pos hb, hAnc]
      · have hb : L.level (e (p (l : ℤ))) ≠ i := by
          intro hb
          have hχa : χ (p 0) = 1 := by rw [hχ, if_neg ha]
          have hχb : χ (p (l : ℤ)) = 0 := by rw [hχ, if_pos hb]
          rw [hχa, hχb] at hSame
          exact (by decide : (1 : Fin 2) ≠ 0) hSame
        simp only [c, if_neg ha, if_neg hb]
    have hh := Erdos713EvenCycle.colours_equal_on_fin_cycle D c hl hm (by omega)
      hMono hStep hChord (hParity x y hx hy)
    simpa only [c, if_pos hx, if_pos hy, Option.some.injEq] using hh

open scoped Classical in
lemma Layering.no_dense_layer {V W : Type*} [Fintype W] [Nonempty W]
    {G : SimpleGraph V} {root : V} (L : Layering G root) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k)
    (K : SimpleGraph W) (e : W → V) (he : Function.Injective e)
    (hMap : ∀ x y, K.Adj x y → G.Adj (e x) (e y))
    (hLevel : ∀ x y, K.Adj x y →
      (L.level (e x) = i ∧ L.level (e y) = i + 1) ∨
      (L.level (e x) = i + 1 ∧ L.level (e y) = i))
    (hFree : (cycleGraph (2 * k)).Free G) (hDeg : ∀ x, 2 * k ≤ K.degree x) : False := by
  classical
  obtain ⟨n, m, f, hm, hLong, hf, hs, heEnd, heChord⟩ :=
    Erdos713EvenCycle.exists_long_chorded_cycle K (2 * k - 2) (by omega)
      (fun x => by have hh := hDeg x; omega)
  have hn : 4 ≤ n := by omega
  letI : NeZero n := ⟨by omega⟩
  let D := K.comap (fun x : Fin n => f x.val)
  let g : Fin n → V := fun x => e (f x.val)
  have hg : Function.Injective g := by
    intro x y hxy
    exact Fin.ext (hf x.isLt y.isLt (he hxy))
  have hDMap (x y : Fin n) (hxy : D.Adj x y) : G.Adj (g x) (g y) := hMap _ _ hxy
  have hDLevel (x y : Fin n) (hxy : D.Adj x y) :
      (L.level (g x) = i ∧ L.level (g y) = i + 1) ∨
      (L.level (g x) = i + 1 ∧ L.level (g y) = i) := hLevel _ _ hxy
  have hDStep : ∀ x, D.Adj x (x + 1) := pullback_cycle_step K (by omega) f hs heEnd
  have hDChord : D.Adj 0 (m : Fin n) := by
    change K.Adj (f (0 : Fin n).val) (f (m : Fin n).val)
    simpa only [Fin.val_zero, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : m < n)] using heChord
  have hAnc := L.ancestors_equal_on_chorded_cycle hk hi hm hLong D g hg hDMap hDLevel
    hDStep hDChord hFree
  have hUnique (x y : Fin n) (hx : L.level (g x) = i) (hy : L.level (g y) = i) : x = y := by
    have hh := hAnc i (Nat.le_refl i) x y hx hy
    have htx : L.ancestor (g x) i = g x := by rw [← hx, L.ancestor_top]
    have hty : L.ancestor (g y) i = g y := by rw [← hy, L.ancestor_top]
    rw [htx, hty] at hh
    exact hg hh
  have h01 := hLevel (f 0) (f 1) (hs 0 (by omega))
  have h12 := hLevel (f 1) (f 2) (hs 1 (by omega))
  have h23 := hLevel (f 2) (f 3) (hs 2 (by omega))
  rcases h01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have h2 : L.level (e (f 2)) = i := by omega
    have hh := hUnique ⟨0, by omega⟩ ⟨2, by omega⟩ h0 h2
    have hbad := congrArg Fin.val hh
    norm_num at hbad
  · have h3 : L.level (e (f 3)) = i := by omega
    have hh := hUnique ⟨1, by omega⟩ ⟨3, by omega⟩ h1 h3
    have hbad := congrArg Fin.val hh
    norm_num at hbad

open scoped Classical in
lemma Layering.layer_edge_bound {V W : Type*} [Fintype W]
    {G : SimpleGraph V} {root : V} (L : Layering G root) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k)
    (K : SimpleGraph W) (e : W → V) (he : Function.Injective e)
    (hMap : ∀ x y, K.Adj x y → G.Adj (e x) (e y))
    (hLevel : ∀ x y, K.Adj x y →
      (L.level (e x) = i ∧ L.level (e y) = i + 1) ∨
      (L.level (e x) = i + 1 ∧ L.level (e y) = i))
    (hFree : (cycleGraph (2 * k)).Free G) : K.edgeFinset.card ≤ 2 * k * Fintype.card W := by
  classical
  obtain ⟨Q, hQK, hDeg, hBound⟩ := Erdos713Leaf.exists_pruned K (2 * k)
  have hQ : Q = ⊥ := by
    by_contra hQ
    obtain ⟨x, y, hxy⟩ := ne_bot_iff_exists_adj.mp hQ
    letI : Nonempty Q.support := ⟨⟨x, y, hxy⟩⟩
    refine L.no_dense_layer hk hi (Q.induce Q.support) (e ∘ Subtype.val)
      (he.comp Subtype.val_injective) ?_ ?_ hFree ?_
    · intro u v huv
      exact hMap _ _ (hQK huv)
    · intro u v huv
      exact hLevel _ _ (hQK huv)
    · intro u
      rw [Q.degree_induce_support]
      rcases hDeg u.val with hz | hd
      · have hp := (Q.degree_pos_iff_mem_support u.val).mpr u.prop
        rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] at hz
        omega
      · simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hd
  rw [hQ] at hBound
  simpa only [edgeSet_bot, Nat.card_eq_fintype_card, Fintype.card_ofIsEmpty, zero_add,
    ← edgeFinset_card] using hBound

namespace Layering
open Finset
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {root : V} (L : Layering G root)

noncomputable def levelFinset (i : ℕ) : Finset V := by
  classical
  exact univ.filter (fun v => L.level v = i)

@[simp] lemma mem_levelFinset (v : V) (i : ℕ) : v ∈ L.levelFinset i ↔ L.level v = i := by
  classical
  simp [levelFinset]

lemma levelFinset_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (L.levelFinset i) (L.levelFinset j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  exact hij ((L.mem_levelFinset v i).mp hv |>.symm.trans ((L.mem_levelFinset v j).mp hv'))

def between (i : ℕ) : SimpleGraph V := G.between (↑(L.levelFinset i)) (↑(L.levelFinset (i + 1)))

lemma between_bipartite (i : ℕ) : (L.between i).IsBipartiteWith
    (↑(L.levelFinset i)) (↑(L.levelFinset (i + 1))) :=
  between_isBipartiteWith (Finset.disjoint_coe.mpr (L.levelFinset_disjoint (by omega)))

lemma between_le (i : ℕ) : L.between i ≤ G := fun _ _ h => h.1

lemma between_levels (i : ℕ) {u v : V} (h : (L.between i).Adj u v) :
    (L.level u = i ∧ L.level v = i + 1) ∨ (L.level u = i + 1 ∧ L.level v = i) := by
  simpa only [Finset.mem_coe, mem_levelFinset] using h.2

open scoped Classical in
lemma between_edge_bound {k i : ℕ} (hk : 2 ≤ k) (hi : i < k)
    (hFree : (cycleGraph (2 * k)).Free G) :
    (L.between i).edgeFinset.card ≤ 2 * k * ((L.levelFinset i).card + (L.levelFinset (i + 1)).card) := by
  classical
  let S := L.levelFinset i ∪ L.levelFinset (i + 1)
  have hSupp : (L.between i).support ⊆ (S : Set V) := by
    rintro v ⟨w, hvw⟩
    rcases hvw.2 with ⟨hv, _⟩ | ⟨hv, _⟩
    · exact mem_union_left _ hv
    · exact mem_union_right _ hv
  have hb := L.layer_edge_bound hk hi ((L.between i).induce (S : Set V)) Subtype.val
    Subtype.val_injective (fun _ _ h => h.1) (fun _ _ h => L.between_levels i h) hFree
  have he : Nat.card ((L.between i).induce (S : Set V)).edgeSet = Nat.card (L.between i).edgeSet := by
    simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using card_edgeFinset_induce_of_support_subset hSupp
  have hc : Nat.card ↥(S : Set V) = (L.levelFinset i).card + (L.levelFinset (i + 1)).card := by
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact card_union_of_disjoint (L.levelFinset_disjoint (by omega))
  simp only [edgeFinset_card, Fintype.card_eq_nat_card, he, hc] at hb ⊢
  exact hb

lemma levelFinset_zero : L.levelFinset 0 = {root} := by
  classical
  ext v
  simp only [mem_levelFinset, mem_singleton, L.zero_iff]

open scoped Classical in
lemma degree_root_eq_card_level_one
    (hStep : ∀ u v, G.Adj u v → L.level u + 1 = L.level v ∨ L.level v + 1 = L.level u) :
    G.degree root = (L.levelFinset 1).card := by
  classical
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext v
  rw [mem_neighborFinset, mem_levelFinset]
  have hr : L.level root = 0 := (L.zero_iff root).mpr rfl
  constructor
  · intro h
    have hh := hStep root v h
    omega
  · intro hv
    have hv' : v ≠ root := by intro he; rw [he, hr] at hv; omega
    have hp := L.parent_level v hv'
    have hp' : L.parent v = root := (L.zero_iff _).mp (by omega)
    have hh := (L.parent_adj v hv').symm
    simpa only [hp'] using hh

open scoped Classical in
lemma layer_degree_sum (d i : ℕ) (hDeg : ∀ v, d ≤ G.degree v)
    (hStep : ∀ u v, G.Adj u v → L.level u + 1 = L.level v ∨ L.level v + 1 = L.level u) :
    d * (L.levelFinset (i + 1)).card ≤
      (L.between i).edgeFinset.card + (L.between (i + 1)).edgeFinset.card := by
  classical
  have hD (v : V) (hv : v ∈ L.levelFinset (i + 1)) :
      d ≤ (L.between i).degree v + (L.between (i + 1)).degree v := by
    have hvl : L.level v = i + 1 := (L.mem_levelFinset v _).mp hv
    have hSub : G.neighborFinset v ⊆ (L.between i).neighborFinset v ∪
        (L.between (i + 1)).neighborFinset v := by
      intro w hw
      have hvw : G.Adj v w := (mem_neighborFinset G v w).mp hw
      rcases hStep v w hvw with h | h
      · apply mem_union_right
        rw [mem_neighborFinset]
        exact ⟨hvw, Or.inl ⟨hv, (L.mem_levelFinset w _).mpr (by omega)⟩⟩
      · apply mem_union_left
        rw [mem_neighborFinset]
        exact ⟨hvw, Or.inr ⟨hv, (L.mem_levelFinset w _).mpr (by omega)⟩⟩
    have hh := (card_le_card hSub).trans (card_union_le _ _)
    simp only [card_neighborFinset_eq_degree] at hh
    exact (hDeg v).trans hh
  have hh := sum_le_sum (s := L.levelFinset (i + 1)) (fun v hv => hD v hv)
  rw [sum_add_distrib, isBipartiteWith_sum_degrees_eq_card_edges (L.between_bipartite i).symm,
    isBipartiteWith_sum_degrees_eq_card_edges (L.between_bipartite (i + 1))] at hh
  simpa only [sum_const, Nat.nsmul_eq_mul, mul_comm] using hh

end Layering

lemma numerical_layer_growth {k d N : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N) (a : ℕ → ℕ)
    (ha0 : a 0 = 1) (ha1 : d ≤ a 1) (haN : a k ≤ N)
    (hRec : ∀ j, j + 1 < k → d * a (j + 1) ≤
      2 * k * (a j + a (j + 1)) + 2 * k * (a (j + 1) + a (j + 2))) :
    d ^ k ≤ (12 * k) ^ k * N := by
  by_cases hd : d ≤ 12 * k
  · exact (Nat.pow_le_pow_left hd k).trans (Nat.le_mul_of_pos_right _ hN)
  have hd' : 12 * k ≤ d := by omega
  have hk' : 0 < 4 * k := by omega
  have hGrow : ∀ j, j < k → d * a j ≤ 4 * k * a (j + 1) ∧ a j ≤ a (j + 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [ha0, mul_one]
      refine ⟨ha1.trans (Nat.le_mul_of_pos_left _ hk'), ?_⟩
      change 1 ≤ a 1
      omega
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hh := hRec j hj
      have hp := Nat.mul_le_mul_left (2 * k) hprev.2
      have hdc := Nat.mul_le_mul_right (a (j + 1)) hd'
      have hnext : d * a (j + 1) ≤ 4 * k * a (j + 2) := by nlinarith only [hh, hp, hdc]
      refine ⟨hnext, ?_⟩
      have hm := Nat.mul_le_mul_right (a (j + 1)) (show 4 * k ≤ d by omega)
      exact Nat.le_of_mul_le_mul_left (hm.trans hnext) hk'
  have hPow : ∀ j, j ≤ k → d ^ j ≤ (4 * k) ^ j * a j := by
    intro j
    induction j with
    | zero => intro _; simp [ha0]
    | succ j ih =>
      intro hj
      have hp := ih (by omega)
      have hg := (hGrow j (by omega)).1
      calc
        d ^ (j + 1) = d * d ^ j := pow_succ' _ _
        _ ≤ d * ((4 * k) ^ j * a j) := Nat.mul_le_mul_left _ hp
        _ = (4 * k) ^ j * (d * a j) := by ring
        _ ≤ (4 * k) ^ j * (4 * k * a (j + 1)) := Nat.mul_le_mul_left _ hg
        _ = (4 * k) ^ (j + 1) * a (j + 1) := by ring
  calc
    d ^ k ≤ (4 * k) ^ k * a k := hPow k (Nat.le_refl k)
    _ ≤ (4 * k) ^ k * N := Nat.mul_le_mul_left _ haN
    _ ≤ (12 * k) ^ k * N := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) k)

open scoped Classical in
lemma Layering.degree_power_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {root : V}
    (L : Layering G root) {k d : ℕ} (hk : 2 ≤ k)
    (hFree : (cycleGraph (2 * k)).Free G) (hDeg : ∀ v, d ≤ G.degree v)
    (hStep : ∀ u v, G.Adj u v → L.level u + 1 = L.level v ∨ L.level v + 1 = L.level u) :
    d ^ k ≤ (12 * k) ^ k * Fintype.card V := by
  classical
  apply numerical_layer_growth (by omega) (Fintype.card_pos_iff.mpr ⟨root⟩)
    (fun j => (L.levelFinset j).card)
  · rw [L.levelFinset_zero]
    simp
  · have hh := hDeg root
    rwa [L.degree_root_eq_card_level_one hStep] at hh
  · exact Finset.card_le_univ _
  · intro j hj
    exact (L.layer_degree_sum d j hDeg hStep).trans (Nat.add_le_add
      (L.between_edge_bound hk (by omega) hFree) (L.between_edge_bound hk hj hFree))

open scoped Classical in
lemma connected_degree_power_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hBip : G.IsBipartite) {k d : ℕ} (hk : 2 ≤ k)
    (hFree : (cycleGraph (2 * k)).Free G) (hDeg : ∀ v, d ≤ G.degree v) :
    d ^ k ≤ (12 * k) ^ k * Fintype.card V := by
  classical
  let root : V := hconn.nonempty.some
  exact (Layering.ofConnected G hconn root).degree_power_bound hk hFree hDeg
    (fun _ _ h => adj_dist_diff_one hconn hBip root h)

open scoped Classical in
lemma degree_power_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hBip : G.IsBipartite) {k d : ℕ} (hk : 2 ≤ k)
    (hFree : (cycleGraph (2 * k)).Free G)
    (hDeg : ∀ u v, G.Adj u v → d ≤ G.degree u) {u v : V} (huv : G.Adj u v) :
    d ^ k ≤ (12 * k) ^ k * Fintype.card V := by
  classical
  let C := G.connectedComponentMk u
  have hu : u ∈ C.supp := rfl
  have hSupp : C.supp ⊆ G.support := by
    intro w hw
    by_cases hwu : w = u
    · subst w; exact ⟨v, huv⟩
    · exact mem_support_of_reachable hwu (C.reachable_of_mem_supp hw hu)
  let H := G.induce C.supp
  have hCDeg (w : ↥C.supp) : d ≤ H.degree w := by
    have hSub : G.neighborSet w.val ⊆ C.supp := by
      intro z hz
      exact C.mem_supp_of_adj_mem_supp w.prop hz
    have heq : H.degree w = G.degree w.val := degree_induce_of_neighborSet_subset hSub
    rw [heq]
    obtain ⟨z, hwz⟩ := hSupp w.prop
    exact hDeg w.val z hwz
  have hCFree : (cycleGraph (2 * k)).Free H :=
    fun hc => hFree (hc.trans ⟨Copy.induce G C.supp⟩)
  have hh := connected_degree_power_bound H C.connected_toSimpleGraph
    (Colorable.of_hom (Copy.induce G C.supp).toHom hBip) hk hCFree hCDeg
  exact hh.trans (Nat.mul_le_mul_left _ (Fintype.card_subtype_le (· ∈ C.supp)))

open scoped Classical in
lemma bipartite_edge_power_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hBip : G.IsBipartite) {k : ℕ} (hk : 2 ≤ k) (hFree : (cycleGraph (2 * k)).Free G) :
    G.edgeFinset.card ^ k ≤ 4 ^ k * ((12 * k) ^ k + 1) * Fintype.card V ^ (k + 1) := by
  classical
  let e := G.edgeFinset.card
  let n := Fintype.card V
  by_cases he : e = 0
  · change e ^ k ≤ _
    simp [he, show k ≠ 0 by omega]
  have hGne : G ≠ ⊥ := by
    intro hh
    exact he (by simp [e, hh])
  obtain ⟨u, v, huv⟩ := ne_bot_iff_exists_adj.mp hGne
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨u⟩
  let d := e / (2 * n)
  have hdiv : d * (2 * n) ≤ e := Nat.div_mul_le_self e (2 * n)
  obtain ⟨K, hKG, hDeg, hBound⟩ := Erdos713Leaf.exists_pruned G d
  have hKne : K ≠ ⊥ := by
    intro hK
    have hb : e ≤ d * n := by
      simpa only [hK, edgeSet_bot, Nat.card_eq_fintype_card, Fintype.card_ofIsEmpty,
        zero_add, ← edgeFinset_card] using hBound
    nlinarith only [hb, hdiv, Nat.pos_of_ne_zero he]
  obtain ⟨x, y, hxy⟩ := ne_bot_iff_exists_adj.mp hKne
  have hKBip : K.IsBipartite := Colorable.of_hom (Copy.ofLE K G hKG).toHom hBip
  have hKFree : (cycleGraph (2 * k)).Free K := fun hc => hFree (hc.mono_right hKG)
  have hKD (x y : V) (hxy : K.Adj x y) : d ≤ K.degree x := by
    rcases hDeg x with hz | hd
    · have hp : 0 < K.degree x := hxy.degree_pos_left
      rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] at hz
      omega
    · simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hd
  have hdk : d ^ k ≤ (12 * k) ^ k * n := degree_power_bound K hKBip hk hKFree hKD hxy
  have heUpper : e ≤ 2 * n * (d + 1) := (Nat.lt_mul_div_succ e (by omega : 0 < 2 * n)).le
  have hAdd : (d + 1) ^ k ≤ 2 ^ k * (d ^ k + 1) := by
    by_cases hd0 : d = 0
    · simp only [hd0, zero_add, one_pow, zero_pow (by omega : k ≠ 0)]
      simpa only [mul_one] using Nat.one_le_pow k 2 (by decide : 0 < 2)
    · calc
        (d + 1) ^ k ≤ (2 * d) ^ k := Nat.pow_le_pow_left (by omega) k
        _ = 2 ^ k * d ^ k := mul_pow _ _ _
        _ ≤ 2 ^ k * (d ^ k + 1) := Nat.mul_le_mul_left _ (by omega)
  change e ^ k ≤ 4 ^ k * ((12 * k) ^ k + 1) * n ^ (k + 1)
  calc
    e ^ k ≤ (2 * n * (d + 1)) ^ k := Nat.pow_le_pow_left heUpper k
    _ = (2 * n) ^ k * (d + 1) ^ k := mul_pow _ _ _
    _ ≤ (2 * n) ^ k * (2 ^ k * (d ^ k + 1)) := Nat.mul_le_mul_left _ hAdd
    _ = 4 ^ k * n ^ k * (d ^ k + 1) := by
      rw [show (4 : ℕ) = 2 * 2 by decide, mul_pow, mul_pow]
      ring
    _ ≤ 4 ^ k * n ^ k * ((12 * k) ^ k * n + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right hdk 1)
    _ ≤ 4 ^ k * n ^ k * (((12 * k) ^ k + 1) * n) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    _ = 4 ^ k * ((12 * k) ^ k + 1) * n ^ (k + 1) := by rw [pow_succ]; ring

open scoped Classical in
lemma edge_power_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    {k : ℕ} (hk : 2 ≤ k) (hFree : (cycleGraph (2 * k)).Free G) :
    G.edgeFinset.card ^ k ≤ 8 ^ k * ((12 * k) ^ k + 1) * Fintype.card V ^ (k + 1) := by
  classical
  obtain ⟨K, hKG, hKBip, hhalf⟩ := Erdos713Cut.exists_bipartite_half G
  have hKFree : (cycleGraph (2 * k)).Free K := fun hc => hFree (hc.mono_right hKG)
  calc
    G.edgeFinset.card ^ k ≤ (2 * K.edgeFinset.card) ^ k := Nat.pow_le_pow_left hhalf k
    _ = 2 ^ k * K.edgeFinset.card ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (4 ^ k * ((12 * k) ^ k + 1) * Fintype.card V ^ (k + 1)) :=
      Nat.mul_le_mul_left _ (bipartite_edge_power_bound K hKBip hk hKFree)
    _ = 8 ^ k * ((12 * k) ^ k + 1) * Fintype.card V ^ (k + 1) := by
      rw [show (8 : ℕ) ^ k = 2 ^ k * 4 ^ k by simpa using (mul_pow (2 : ℕ) 4 k)]
      ring

lemma extremal_power_bound {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (extremalNumber n (cycleGraph (2 * k))) ^ k ≤ 8 ^ k * ((12 * k) ^ k + 1) * n ^ (k + 1) := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | (cycleGraph (2 * k)).Free G}
  change (S.sup (fun G => G.edgeFinset.card)) ^ k ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨G, hG, he⟩ := Finset.exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
    rw [he]
    have hFree : (cycleGraph (2 * k)).Free G := by simpa [S] using hG
    simpa only [Fintype.card_fin] using edge_power_bound G hk hFree
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp [show k ≠ 0 by omega]

end Erdos713BreadthFirst

/- A polynomial incidence construction excluding ten-cycles. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713C10
open Finset Erdos713C6

theorem singleton_colour {A : Type*} (a : Fin 5 → A)
    (ha : ∀ i, a i ≠ a (i + 1)) : ∃ i, ∀ j, a j = a i → j = i := by
  classical
  have h0 : a 0 ≠ a 1 := ha 0
  have h1 : a 1 ≠ a 2 := ha 1
  have h2 : a 2 ≠ a 3 := ha 2
  have h3 : a 3 ≠ a 4 := ha 3
  have h4 : a 4 ≠ a 0 := ha 4
  by_cases h02 : a 0 = a 2
  · by_cases h14 : a 1 = a 4
    · refine ⟨3, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨4, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
  by_cases h03 : a 0 = a 3
  · by_cases h14 : a 1 = a 4
    · refine ⟨2, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨1, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
  · refine ⟨0, ?_⟩
    intro j hj
    fin_cases j <;> simp_all

theorem weighted_eval_zero {I F : Type*} [Fintype I] [Field F] (a r : I → F) {m : ℕ}
    (hm : ∀ k < m, ∑ i, r i * a i ^ k = 0) (P : Polynomial F) (hP : P.natDegree < m) :
    ∑ i, r i * P.eval (a i) = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range' hP, mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro k hk
  calc
    ∑ i, r i * (P.coeff k * a i ^ k) = P.coeff k * ∑ i, r i * a i ^ k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hm k (mem_range.mp hk), mul_zero]

theorem singleton_moment_zero {I F : Type*} [Fintype I] [Field F] (a r : I → F)
    (hm : ∀ k < Fintype.card I, ∑ i, r i * a i ^ k = 0) (i : I)
    (hi : ∀ j, a j = a i → j = i) : r i = 0 := by
  classical
  let P : Polynomial F := ∏ j ∈ (univ.erase i), (Polynomial.X - Polynomial.C (a j))
  have hP : P.natDegree < Fintype.card I := by
    calc
      P.natDegree ≤ ∑ j ∈ univ.erase i, (Polynomial.X - Polynomial.C (a j)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ = Fintype.card I - 1 := by simp
      _ < Fintype.card I := Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨i⟩) (by decide)
  have hEval (j : I) (hj : j ≠ i) : P.eval (a j) = 0 := by
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply prod_eq_zero (mem_erase.mpr ⟨hj, mem_univ _⟩)
    exact sub_self _
  have hNonzero : P.eval (a i) ≠ 0 := by
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun hh => (mem_erase.mp hj).1 (hi j hh.symm))
  have hh := weighted_eval_zero a r hm P hP
  have hs : ∑ j, r j * P.eval (a j) = r i * P.eval (a i) := by
    apply sum_eq_single i
    · intro j _ hj
      rw [hEval j hj, mul_zero]
    · simp
  rw [hs] at hh
  exact (mul_eq_zero.mp hh).resolve_right hNonzero

abbrev Coordinates (F : Type*) := F × (Fin 4 → F)

def Incidence {F : Type*} [Field F] (p l : Coordinates F) : Prop :=
  ∀ j : Fin 4, p.2 j = l.1 ^ (j.val + 1) * p.1 + l.2 j

abbrev incidenceGraph (F : Type*) [Field F] := bipGraph (Incidence (F := F))

theorem point_eq_of_x_eq {F : Type*} [Field F] {p q l : Coordinates F}
    (hp : Incidence p l) (hq : Incidence q l) (h : p.1 = q.1) : p = q := by
  apply Prod.ext h
  funext j
  rw [hp j, hq j, h]

theorem line_eq_of_slope_eq {F : Type*} [Field F] {p l m : Coordinates F}
    (hl : Incidence p l) (hm : Incidence p m) (h : l.1 = m.1) : l = m := by
  apply Prod.ext h
  funext j
  have hh := hl j
  rw [h] at hh
  exact add_left_cancel (hh.symm.trans (hm j))

theorem sum_next_sub {F : Type*} [Field F] (x : Fin 5 → F) : ∑ i, (x (i + 1) - x i) = 0 := by
  rw [sum_sub_distrib]
  apply sub_eq_zero.mpr
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin 5)) x

theorem no_decagon {F : Type*} [Field F] (p l : Fin 5 → Coordinates F)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, Incidence (p i) (l i)) (hB : ∀ i, Incidence (p (i + 1)) (l i)) : False := by
  have hNe : ∀ i : Fin 5, i ≠ i + 1 := by decide
  let a : Fin 5 → F := fun i => (l i).1
  let r : Fin 5 → F := fun i => (p (i + 1)).1 - (p i).1
  have hAdj : ∀ i, a i ≠ a (i + 1) := by
    intro i he
    exact hNe i (hl (line_eq_of_slope_eq (hB i) (hA (i + 1)) he))
  have hr : ∀ i, r i ≠ 0 := by
    intro i he
    have hx : (p i).1 = (p (i + 1)).1 := (sub_eq_zero.mp he).symm
    exact hNe i (hp (point_eq_of_x_eq (hA i) (hB i) hx))
  have hm : ∀ k < Fintype.card (Fin 5), ∑ i, r i * a i ^ k = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa only [pow_zero, mul_one, r] using sum_next_sub (fun i => (p i).1)
    have hk5 : k < 5 := by simpa using hk
    let j : Fin 4 := ⟨k - 1, by omega⟩
    have hj : j.val + 1 = k := by dsimp [j]; omega
    have hStep (i : Fin 5) : r i * a i ^ k = (p (i + 1)).2 j - (p i).2 j := by
      have hhA := hA i j
      have hhB := hB i j
      rw [hj] at hhA hhB
      dsimp only [r, a]
      linear_combination hhA - hhB
    simp_rw [hStep]
    exact sum_next_sub (fun i => (p i).2 j)
  obtain ⟨i, hi⟩ := singleton_colour a hAdj
  exact hr i (singleton_moment_zero a r hm i hi)

abbrev C10 := cycleGraph 10

theorem injective_of_map {I J U V : Type*} (f : J → V) (hf : Function.Injective f)
    (g : U → V) (x : I → U) (k : I → J) (hk : Function.Injective k)
    (he : ∀ i, f (k i) = g (x i)) : Function.Injective x := by
  intro i j hij
  apply hk
  apply hf
  rw [he i, he j, hij]

theorem free_of_no_decagon {P L : Type*} (R : P → L → Prop)
    (h : ∀ (a : Fin 5 → P) (b : Fin 5 → L), Function.Injective a → Function.Injective b →
      (∀ i, R (a i) (b i)) → (∀ i, R (a (i + 1)) (b i)) → False) :
    C10.Free (bipGraph R) := by
  rintro ⟨f⟩
  have h01 := f.toHom.map_rel' (show C10.Adj 0 1 by decide)
  have h12 := f.toHom.map_rel' (show C10.Adj 1 2 by decide)
  have h23 := f.toHom.map_rel' (show C10.Adj 2 3 by decide)
  have h34 := f.toHom.map_rel' (show C10.Adj 3 4 by decide)
  have h45 := f.toHom.map_rel' (show C10.Adj 4 5 by decide)
  have h56 := f.toHom.map_rel' (show C10.Adj 5 6 by decide)
  have h67 := f.toHom.map_rel' (show C10.Adj 6 7 by decide)
  have h78 := f.toHom.map_rel' (show C10.Adj 7 8 by decide)
  have h89 := f.toHom.map_rel' (show C10.Adj 8 9 by decide)
  have h90 := f.toHom.map_rel' (show C10.Adj 9 0 by decide)
  change (bipGraph R).Adj (f 0) (f 1) at h01
  change (bipGraph R).Adj (f 1) (f 2) at h12
  change (bipGraph R).Adj (f 2) (f 3) at h23
  change (bipGraph R).Adj (f 3) (f 4) at h34
  change (bipGraph R).Adj (f 4) (f 5) at h45
  change (bipGraph R).Adj (f 5) (f 6) at h56
  change (bipGraph R).Adj (f 6) (f 7) at h67
  change (bipGraph R).Adj (f 7) (f 8) at h78
  change (bipGraph R).Adj (f 8) (f 9) at h89
  change (bipGraph R).Adj (f 9) (f 0) at h90
  cases e0 : f 0 with
  | inl x0 =>
    rw [e0] at h01
    obtain ⟨y0, e1, hR0⟩ := right_of_adj_left h01
    rw [e1] at h12
    obtain ⟨x1, e2, hR1⟩ := left_of_adj_right h12
    rw [e2] at h23
    obtain ⟨y1, e3, hR2⟩ := right_of_adj_left h23
    rw [e3] at h34
    obtain ⟨x2, e4, hR3⟩ := left_of_adj_right h34
    rw [e4] at h45
    obtain ⟨y2, e5, hR4⟩ := right_of_adj_left h45
    rw [e5] at h56
    obtain ⟨x3, e6, hR5⟩ := left_of_adj_right h56
    rw [e6] at h67
    obtain ⟨y3, e7, hR6⟩ := right_of_adj_left h67
    rw [e7] at h78
    obtain ⟨x4, e8, hR7⟩ := left_of_adj_right h78
    rw [e8] at h89
    obtain ⟨y4, e9, hR8⟩ := right_of_adj_left h89
    have hR9 : R x0 y4 := by simpa only [e9, e0] using h90
    apply h ![x0, x1, x2, x3, x4] ![y0, y1, y2, y3, y4]
    · apply injective_of_map f f.injective Sum.inl _ ![0, 2, 4, 6, 8] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_of_map f f.injective Sum.inr _ ![1, 3, 5, 7, 9] (by decide)
      intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
  | inr y0 =>
    rw [e0] at h01
    obtain ⟨x0, e1, hR0⟩ := left_of_adj_right h01
    rw [e1] at h12
    obtain ⟨y1, e2, hR1⟩ := right_of_adj_left h12
    rw [e2] at h23
    obtain ⟨x1, e3, hR2⟩ := left_of_adj_right h23
    rw [e3] at h34
    obtain ⟨y2, e4, hR3⟩ := right_of_adj_left h34
    rw [e4] at h45
    obtain ⟨x2, e5, hR4⟩ := left_of_adj_right h45
    rw [e5] at h56
    obtain ⟨y3, e6, hR5⟩ := right_of_adj_left h56
    rw [e6] at h67
    obtain ⟨x3, e7, hR6⟩ := left_of_adj_right h67
    rw [e7] at h78
    obtain ⟨y4, e8, hR7⟩ := right_of_adj_left h78
    rw [e8] at h89
    obtain ⟨x4, e9, hR8⟩ := left_of_adj_right h89
    have hR9 : R x4 y0 := by simpa only [e9, e0] using h90
    apply h ![x0, x1, x2, x3, x4] ![y1, y2, y3, y4, y0]
    · apply injective_of_map f f.injective Sum.inl _ ![1, 3, 5, 7, 9] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_of_map f f.injective Sum.inr _ ![2, 4, 6, 8, 0] (by decide)
      intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption

theorem incidenceGraph_free (F : Type*) [Field F] : C10.Free (incidenceGraph F) :=
  free_of_no_decagon Incidence no_decagon

def leftNeighbors {F : Type*} [Field F] (p : Coordinates F) :
    F ↪ (incidenceGraph F).neighborSet (Sum.inl p) where
  toFun a := ⟨Sum.inr (a, fun j => p.2 j - a ^ (j.val + 1) * p.1), by
    change Incidence p _
    intro j
    dsimp
    ring⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Coordinates F => x.1)
      (fun x : Coordinates F => x.1) v.val) h

def rightNeighbors {F : Type*} [Field F] (l : Coordinates F) :
    F ↪ (incidenceGraph F).neighborSet (Sum.inr l) where
  toFun x := ⟨Sum.inl (x, fun j => l.1 ^ (j.val + 1) * x + l.2 j), by
    change Incidence _ l
    intro j
    rfl⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Coordinates F => x.1)
      (fun x : Coordinates F => x.1) v.val) h

open scoped Classical in
theorem incidenceGraph_degree_lower (F : Type*) [Field F] [Fintype F]
    (v : Coordinates F ⊕ Coordinates F) : Fintype.card F ≤ (incidenceGraph F).degree v := by
  classical
  rw [← card_neighborSet_eq_degree]
  cases v with
  | inl p => exact Fintype.card_le_of_embedding (leftNeighbors p)
  | inr l => exact Fintype.card_le_of_embedding (rightNeighbors l)

open scoped Classical in
theorem incidenceGraph_edge_lower (F : Type*) [Field F] [Fintype F] :
    Fintype.card F ^ 6 ≤ (incidenceGraph F).edgeFinset.card := by
  classical
  have hh : ∑ v : Coordinates F ⊕ Coordinates F, Fintype.card F ≤
      ∑ v : Coordinates F ⊕ Coordinates F, (incidenceGraph F).degree v :=
    sum_le_sum fun v _ => incidenceGraph_degree_lower F v
  rw [sum_degrees_eq_twice_card_edges] at hh
  simp only [sum_const, card_univ, Fintype.card_sum, Coordinates, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.nsmul_eq_mul] at hh
  nlinarith

theorem extremal_lower_prime (p : ℕ) (hp : p.Prime) :
    p ^ 6 ≤ extremalNumber (2 * p ^ 5) C10 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have he := incidenceGraph_edge_lower (ZMod p)
  have hExt := card_edgeFinset_le_extremalNumber (incidenceGraph_free (ZMod p))
  have hc : Fintype.card (Coordinates (ZMod p) ⊕ Coordinates (ZMod p)) = 2 * p ^ 5 := by
    simp only [Coordinates, Fintype.card_sum, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, ZMod.card]
    ring
  rw [hc] at hExt
  rw [ZMod.card] at he
  exact he.trans hExt

theorem lower_exponent_of_prime_bound {f : ℕ → ℕ} {a : ℝ}
    (hO : (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hlow : ∀ p : ℕ, p.Prime → p ^ 6 ≤ f (2 * p ^ 5)) : (6 : ℝ) / 5 ≤ a := by
  by_contra ha
  have ha' : a < (6 : ℝ) / 5 := lt_of_not_ge ha
  obtain ⟨C, _, hC⟩ := hO.exists_pos
  have ht : Tendsto (fun p : ℕ => 2 * p ^ 5) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro p
    have hp := Nat.le_self_pow (by decide : 5 ≠ 0) p
    change p ≤ 2 * p ^ 5
    omega
  have hratio : ∀ᶠ p : ℕ in atTop,
      p.Prime → (p : ℝ) ^ (6 - 5 * a) ≤ C * (2 : ℝ) ^ a := by
    filter_upwards [ht.eventually hC.bound, eventually_gt_atTop (0 : ℕ)] with p hp hpos
    intro hprime
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpos
    have hl : (p : ℝ) ^ 6 ≤ (f (2 * p ^ 5) : ℝ) := by exact_mod_cast hlow p hprime
    have hu : (f (2 * p ^ 5) : ℝ) ≤ C * (2 * (p : ℝ) ^ 5) ^ a := by
      rw [Real.norm_natCast, Real.norm_of_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg (2 * p ^ 5)) a)] at hp
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hp
    have he := hl.trans hu
    have hp3 : ((p : ℝ) ^ 5) ^ a = (p : ℝ) ^ (5 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      norm_num
    rw [Real.mul_rpow (by norm_num) (pow_nonneg hp0.le 5), hp3] at he
    rw [Real.rpow_sub hp0, div_le_iff₀ (Real.rpow_pos_of_pos hp0 (5 * a))]
    have hp4 : (p : ℝ) ^ (6 : ℝ) = (p : ℝ) ^ (6 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (p : ℝ) 6
    rw [hp4]
    simpa only [mul_assoc] using he
  have htop : Tendsto (fun p : ℕ => (p : ℝ) ^ (6 - 5 * a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 6 - 5 * a)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hratio.and (htop.eventually_gt_atTop (C * (2 : ℝ) ^ a)))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  exact (not_lt_of_ge ((hN p hpN).1 hp)) ((hN p hpN).2)

theorem exponent_lower_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : C10 ⊑ H) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : (6 : ℝ) / 5 ≤ a := by
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc).mp h.isBigO
  apply lower_exponent_of_prime_bound hO
  intro p hp
  exact (extremal_lower_prime p hp).trans hH.extremalNumber_le


end Erdos713C10

/- Upper growth rates for even cycles, and the exact power threshold for the ten-cycle. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713EvenCycle

theorem upper {k : ℕ} (hk : 2 ≤ k) :
    (fun n : ℕ => (extremalNumber n (cycleGraph (2 * k)) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (((k + 1 : ℕ) : ℝ) / k)) :=
  Erdos713Rate.upper_of_power_bound (by omega) (Erdos713BreadthFirst.extremal_power_bound hk)

theorem exponent_upper_of_containment {W : Type*} {H : SimpleGraph W} {k : ℕ} (hk : 2 ≤ k)
    (hH : H ⊑ cycleGraph (2 * k)) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ ((k + 1 : ℕ) : ℝ) / k := by
  apply Erdos713Forest.exponent_le_of_isBigO
  exact ((isBigO_const_mul_left_iff hc).mp h.isBigO_symm).trans
    ((Erdos713Rate.extremal_mono_bigO hH).trans (upper hk))

theorem rate_upper_of_containment {W : Type*} {H : SimpleGraph W} {k : ℕ} (hk : 2 ≤ k)
    (hH : H ⊑ cycleGraph (2 * k)) {a : ℝ} (h : Erdos713Rate.HasRate H a) :
    a ≤ ((k + 1 : ℕ) : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply h.lower _ ((le_div_iff₀ hk').mpr ?_)
    ((Erdos713Rate.extremal_mono_bigO hH).trans (upper hk))
  simp only [one_mul, Nat.cast_add, Nat.cast_one]
  linarith

end Erdos713EvenCycle

namespace Erdos713C10

theorem rate_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : C10 ⊑ H) (hhi : H ⊑ C10) : Erdos713Rate.HasRate H ((6 : ℝ) / 5) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · apply (Erdos713Rate.extremal_mono_bigO hhi).trans
    simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] using
      Erdos713EvenCycle.upper (by decide : 2 ≤ 5)
  · intro a _ h
    apply lower_exponent_of_prime_bound h
    intro p hp
    exact (extremal_lower_prime p hp).trans hlo.extremalNumber_le

theorem rate : Erdos713Rate.HasRate C10 ((6 : ℝ) / 5) :=
  rate_of_containment (IsContained.refl _) (IsContained.refl _)

theorem exponent_eq_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : C10 ⊑ H) (hhi : H ⊑ C10) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (6 : ℝ) / 5 := by
  have ha := exponent_lower_of_containment hlo hc h
  exact Erdos713Rate.exponent_eq (rate_of_containment hlo hhi) (by linarith) hc h

theorem rational_exponent_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : C10 ⊑ H) (hhi : H ⊑ C10) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨6 / 5, ?_⟩
  simpa using (exponent_eq_of_containment hlo hhi hc h).symm


end Erdos713C10

#print axioms Erdos713EvenCycle.upper
#print axioms Erdos713C10.rate
