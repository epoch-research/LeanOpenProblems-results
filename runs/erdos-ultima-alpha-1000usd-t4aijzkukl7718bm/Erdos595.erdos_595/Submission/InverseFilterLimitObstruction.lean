import FormalConjecturesUtil

/-! Exact marginals of proper countably complete filters do not give a
coherent thread in a countable inverse system. This is an obstruction to
a limit step, not a proof or disproof of Erdos 595. -/
set_option autoImplicit false
open Set Filter
namespace Erdos595InverseFilterLimit

abbrev A := Ordinal.{0}

instance : CountableInterFilter (atTop : Filter A) where
  countable_sInter_mem T hTc hT := by
    classical
    letI : Countable T := hTc.to_subtype
    choose a ha using fun t : T => Filter.mem_atTop_sets.mp (hT t.val t.property)
    refine Filter.mem_atTop_sets.mpr ⟨⨆ t, a t,?_⟩
    intro b hb S hS
    exact ha ⟨S,hS⟩ b ((Ordinal.le_iSup a ⟨S,hS⟩).trans hb)

/-- Increasing tuples, with bonding maps deleting their FIRST coordinate.
A thread would keep prepending smaller ordinals. -/
abbrev X (n : ℕ) := {f : Fin (n+1) → A // StrictMono f}

def low {n : ℕ} (x : X n) : A := x.val 0

def drop (n : ℕ) (x : X (n+1)) : X n :=
  ⟨Fin.tail x.val,x.property.comp (fun _ _ h => Fin.succ_lt_succ_iff.mpr h)⟩

noncomputable def ascending (n : ℕ) (a : A) : X n :=
  ⟨fun i => a + (i.val : Ordinal),by
    intro i j hij
    exact add_lt_add_right (by exact_mod_cast hij) a⟩

@[simp] lemma low_ascending (n : ℕ) (a : A) : low (ascending n a) = a := by
  simp [low,ascending]

def F (n : ℕ) : Filter (X n) := Filter.comap low atTop

instance (n : ℕ) : CountableInterFilter (F n) :=
  inferInstanceAs (CountableInterFilter (Filter.comap low atTop))

instance (n : ℕ) : (F n).NeBot := by
  apply Filter.comap_neBot
  intro S hS
  obtain ⟨a,ha⟩ := (show (atTop : Filter A).NeBot from inferInstance).nonempty_of_mem hS
  exact ⟨ascending n a,by simpa using ha⟩

lemma mem_F (n : ℕ) (S : Set (X n)) : S ∈ F n ↔ ∃ a, ∀ x : X n, a ≤ low x → x ∈ S := by
  rw [F,Filter.mem_comap]
  constructor
  · rintro ⟨T,hT,hTS⟩
    obtain ⟨a,ha⟩ := Filter.mem_atTop_sets.mp hT
    exact ⟨a,fun x hx => hTS (ha _ hx)⟩
  · rintro ⟨a,ha⟩
    exact ⟨Set.Ici a,Filter.mem_atTop a,ha⟩

noncomputable def prepend {n : ℕ} (a : A) (x : X n) (h : a < low x) : X (n+1) :=
  ⟨Fin.cons a x.val,by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact (lt_irrefl _ hij).elim
      · intro hij; exact h.trans_le (x.property.monotone (Fin.zero_le j))
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact (Fin.not_lt_zero _ hij).elim
      · intro hij; exact x.property (Fin.succ_lt_succ_iff.mp hij)⟩

@[simp] lemma low_prepend {n : ℕ} (a : A) (x : X n) (h : a < low x) :
    low (prepend a x h) = a := rfl

@[simp] lemma drop_prepend {n : ℕ} (a : A) (x : X n) (h : a < low x) :
    drop n (prepend a x h) = x := by
  apply Subtype.ext
  simp only [drop, prepend, Fin.tail_cons]

/-- Every bonding map has EXACTLY the stipulated marginal filter. -/
theorem map_drop (n : ℕ) : Filter.map (drop n) (F (n+1)) = F n := by
  apply Filter.ext
  intro S
  change (drop n) ⁻¹' S ∈ F (n+1) ↔ S ∈ F n
  rw [mem_F,mem_F]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a+1,?_⟩
    intro x hx
    have hx' : a < low x := (lt_add_one a).trans_le hx
    have hh := ha (prepend a x hx') (by simp)
    simpa using hh
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    intro x hx
    exact ha (drop n x) (hx.trans (x.property.monotone (Fin.zero_le _)))

/-- There is not even a set-theoretic thread, despite proper countably
complete filters and exact projection marginals at all finite levels. -/
theorem no_thread : ¬∃ x : ∀ n, X n, ∀ n, drop n (x (n+1)) = x n := by
  rintro ⟨x,hx⟩
  let f : ℕ → A := fun n => low (x n)
  letI : IsWellFounded A (· < ·) := ⟨Ordinal.lt_wf⟩
  obtain ⟨n,hn⟩ := WellFounded.not_rel_apply_succ (r := (· < ·)) f
  apply hn
  have hh := congrArg low (hx n)
  have hs := (x (n+1)).property (show (0 : Fin (n+2)) < (1 : Fin (n+2)) by exact Fin.zero_lt_one)
  exact hs.trans_eq hh

#print axioms map_drop
#print axioms no_thread
end Erdos595InverseFilterLimit
