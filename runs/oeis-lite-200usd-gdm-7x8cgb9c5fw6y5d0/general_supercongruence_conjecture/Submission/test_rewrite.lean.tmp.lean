import FormalConjectures.Util.ProblemImports

def N0 (α : Prop) := α
def N1 (α : Prop) := N0 α → False
def N2 (α : Prop) := N1 α → False
def N3 (α : Prop) := N2 α → False
def N4 (α : Prop) := N3 α → False

inductive Bad : Prop → Prop where
| base {α : Prop} : N1 α → Bad α
| mk {α : Prop} : Bad (N3 α) → Bad (N1 α)

open Classical

noncomputable def f : (α : Prop) → Bad α → N1 α
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  if h_alpha' : α' then
    fun (h1 : N1 α') => h1 h_alpha'
  else
    let recurse := f (N3 α') h
    fun (h1 : N1 α') => recurse (fun (h2 : N2 α') => h2 h1)

-- Proof of N2 True and N4 True
def p2 : N2 True := fun (h1 : N1 True) => h1 True.intro
def p4 : N4 True := fun (h3 : N3 True) => h3 p2

-- Equality proof for cast
theorem h_eq : N1 True = False := by
  have h_iff : N1 True ↔ False := by
    apply Iff.intro
    · intro h
      exact h True.intro
    · intro h
      exact False.elim h
  exact propext h_iff

theorem false_proof : False := by
  have bad_rk : Bad (N3 True) := Bad.base p4
  have bad_m : Bad (N1 True) := Bad.mk bad_rk
  have bad_target : Bad False := h_eq ▸ bad_m
  have f_res : N1 False := f False bad_target
  
  -- Let's see if we can rewrite f_res
  have h_f : f False bad_target = (by
    -- we want to cast the type of f (N1 True) bad_m
    -- f (N1 True) bad_m has type N1 (N1 True) = N2 True.
    -- We want to cast it to N1 False.
    -- Since N1 True = False, we can cast N1 (N1 True) to N1 False using h_eq.
    -- Specifically, N1 (N1 True) = N1 False.
    -- Let's prove this equality of types.
    have h_type : N1 (N1 True) = N1 False := by rw [h_eq]
    exact h_type ▸ (f (N1 True) bad_m)
  ) := by
    generalize h_eq' : N1 True = False' at bad_target f_res
    subst h_eq'
    rfl
  
  -- Now, f_res is equal to h_type ▸ (f (N1 True) bad_m)
  -- So we can rewrite f_res!
  rw [h_f]
  -- Now we want to evaluate f (N1 True) bad_m.
  -- Since bad_m is @Bad.mk True bad_rk.
  -- f (N1 True) (@Bad.mk True bad_rk) is definitionally equal to:
  -- if h_alpha' : True then fun h1 => h1 h_alpha' else ...
  -- Since True is True, it is definitionally equal to fun h1 => h1 True.intro !
  -- Let's prove this!
  have h_eval : f (N1 True) bad_m = (fun (h1 : N1 True) => h1 True.intro) := by
    rfl
  
  rw [h_eval]
  -- Now we have a cast of (fun h1 => h1 True.intro).
  -- Its type is N1 False.
  -- Let's see if we can get False!
  sorry

#print axioms false_proof
