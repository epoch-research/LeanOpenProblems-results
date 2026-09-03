import FormalConjecturesUtil
import Submission.EvenCycle

/-! Breadth-first ancestry and the construction of cycles from layer paths. -/

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

#print axioms extremal_power_bound
end Erdos713BreadthFirst
