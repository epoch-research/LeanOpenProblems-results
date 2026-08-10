import FormalConjectures.Util.ProblemImports

open Nat Finset

def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )

inductive NonemptyTarget (n : ℕ) : Type where
  | intro : Nonempty (0 < A306477 n) → NonemptyTarget n
  | dummy : NonemptyTarget n

instance (n : ℕ) : Inhabited (NonemptyTarget n) := ⟨NonemptyTarget.dummy⟩

mutual
  partial def get_proof (n : ℕ) (inst : NonemptyTarget n) : PLift (Nonempty (0 < A306477 n)) ⊕ Unit :=
    match inst with
    | NonemptyTarget.intro h => Sum.inl (PLift.up h)
    | NonemptyTarget.dummy => Sum.inr ()

  partial def inst_pos (n : ℕ) : NonemptyTarget n :=
    match get_proof n (inst_pos n) with
    | Sum.inl h => NonemptyTarget.intro h.down
    | Sum.inr () => inst_pos n
end

-- Level 1: not_inr
def R_not_inr (n : ℕ) (x x_prime : PLift False ⊕ Unit) : Prop :=
  match x, x_prime with
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => True
  | _, _ => False

def Q_not_inr (n : ℕ) : Type := Quot (R_not_inr n)

instance (n : ℕ) : Nonempty (Q_not_inr n) :=
  ⟨Quot.mk (R_not_inr n) (Sum.inr ())⟩

noncomputable def default_Q_not_inr (n : ℕ) : Q_not_inr n := Classical.choice inferInstance

theorem Q_not_inr_subsingleton (n : ℕ) (x x_prime : Q_not_inr n) : x = x_prime := by
  induction x using Quot.inductionOn with
  | h a =>
    induction x_prime using Quot.inductionOn with
    | h b =>
      apply Quot.sound
      cases a with
      | inl h1 =>
        cases b with
        | inl h2 => exact True.intro
        | inr _ => exact h1.down
      | inr _ =>
        cases b with
        | inl h2 => exact h2.down
        | inr _ => exact True.intro

def f_raw_not_inr (n : ℕ) (x : PLift False ⊕ Unit) : Prop :=
  match x with
  | Sum.inl _ => True
  | Sum.inr _ => False

theorem f_raw_not_inr_compat (n : ℕ) (x x_prime : PLift False ⊕ Unit) (h : R_not_inr n x x_prime) :
    f_raw_not_inr n x = f_raw_not_inr n x_prime := by
  cases x with
  | inl t =>
    cases x_prime with
    | inl t2 => rfl
    | inr u => exact False.elim t.down
  | inr u =>
    cases x_prime with
    | inl t => exact False.elim t.down
    | inr u2 => rfl

def f_not_inr (n : ℕ) (q : Q_not_inr n) : Prop :=
  Quot.lift (f_raw_not_inr n) (fun x x_prime h => f_raw_not_inr_compat n x x_prime h) q

theorem default_Q_not_inr_prop (n : ℕ) :
    f_not_inr n (default_Q_not_inr n) = False := by
  rw [Q_not_inr_subsingleton n (default_Q_not_inr n) (Quot.mk (R_not_inr n) (Sum.inr ()))]
  rfl

-- Level 2: Z
abbrev Z (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Type :=
  PLift (f_raw_not_inr n y) ⊕ Unit

def get_f_proof_raw (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Z n h y :=
  match y with
  | Sum.inl h_val => Sum.inl (PLift.up (False.elim h_val.down))
  | Sum.inr () => Sum.inr ()

def R_Z (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x x_prime : Z n h y) : Prop :=
  match x, x_prime with
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => True
  | _, _ => f_raw_not_inr n y

def Q_Z (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Type := Quot (R_Z n h y)

instance (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Nonempty (Q_Z n h y) :=
  ⟨Quot.mk (R_Z n h y) (Sum.inr ())⟩

noncomputable def default_Q_Z (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Q_Z n h y :=
  Classical.choice inferInstance

def get_Q_Z (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Q_Z n h y :=
  Quot.mk (R_Z n h y) (get_f_proof_raw n h y)

theorem Q_Z_subsingleton (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x x_prime : Q_Z n h y) : x = x_prime := by
  induction x using Quot.inductionOn with
  | h a =>
    induction x_prime using Quot.inductionOn with
    | h b =>
      apply Quot.sound
      cases a with
      | inl h1 =>
        cases b with
        | inl h2 => exact True.intro
        | inr _ => exact h1.down
      | inr _ =>
        cases b with
        | inl h2 => exact h2.down
        | inr _ => exact True.intro

theorem get_Q_Z_eq_default (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    get_Q_Z n h y = default_Q_Z n h y :=
  Q_Z_subsingleton n h y (get_Q_Z n h y) (default_Q_Z n h y)

def f_raw_Z (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x : Z n h y) : Prop :=
  match x with
  | Sum.inl _ => True
  | Sum.inr _ => f_raw_not_inr n y

theorem f_raw_Z_compat (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x x_prime : Z n h y) (h_R : R_Z n h y x x_prime) :
    f_raw_Z n h y x = f_raw_Z n h y x_prime := by
  cases x with
  | inl t =>
    cases x_prime with
    | inl t2 => rfl
    | inr u => exact propext (iff_true_intro h_R).symm
  | inr u =>
    cases x_prime with
    | inl t => exact propext (iff_true_intro h_R)
    | inr u2 => rfl

def f_Z (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (q : Q_Z n h y) : Prop :=
  Quot.lift (f_raw_Z n h y) (fun x x_prime h_R => f_raw_Z_compat n h y x x_prime h_R) q

theorem default_Q_Z_prop (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    f_Z n h y (default_Q_Z n h y) = f_raw_not_inr n y := by
  rw [Q_Z_subsingleton n h y (default_Q_Z n h y) (Quot.mk (R_Z n h y) (Sum.inr ()))]
  rfl

-- Level 3: Z2
abbrev Z2 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Type :=
  PLift (f_raw_Z n h y (get_f_proof_raw n h y)) ⊕ Unit

def get_f_proof_prop_raw (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Z2 n h y :=
  match y with
  | Sum.inl h_val => Sum.inl (PLift.up (False.elim h_val.down))
  | Sum.inr () => Sum.inr ()

def R_Z2 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x x_prime : Z2 n h y) : Prop :=
  match x, x_prime with
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => True
  | _, _ => f_raw_Z n h y (get_f_proof_raw n h y)

def Q_Z2 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Type := Quot (R_Z2 n h y)

instance (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Nonempty (Q_Z2 n h y) :=
  ⟨Quot.mk (R_Z2 n h y) (Sum.inr ())⟩

noncomputable def default_Q_Z2 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Q_Z2 n h y :=
  Classical.choice inferInstance

def get_Q_Z2 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Q_Z2 n h y :=
  Quot.mk (R_Z2 n h y) (get_f_proof_prop_raw n h y)

theorem Q_Z2_subsingleton (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x x_prime : Q_Z2 n h y) : x = x_prime := by
  induction x using Quot.inductionOn with
  | h a =>
    induction x_prime using Quot.inductionOn with
    | h b =>
      apply Quot.sound
      cases a with
      | inl h1 =>
        cases b with
        | inl h2 => exact True.intro
        | inr _ => exact h1.down
      | inr _ =>
        cases b with
        | inl h2 => exact h2.down
        | inr _ => exact True.intro

theorem get_Q_Z2_eq_default (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    get_Q_Z2 n h y = default_Q_Z2 n h y :=
  Q_Z2_subsingleton n h y (get_Q_Z2 n h y) (default_Q_Z2 n h y)

def f_raw_Z2 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x : Z2 n h y) : Prop :=
  match x with
  | Sum.inl _ => True
  | Sum.inr _ => f_raw_Z n h y (get_f_proof_raw n h y)

theorem f_raw_Z2_compat (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x x_prime : Z2 n h y) (h_R : R_Z2 n h y x x_prime) :
    f_raw_Z2 n h y x = f_raw_Z2 n h y x_prime := by
  cases x with
  | inl t =>
    cases x_prime with
    | inl t2 => rfl
    | inr u => exact propext (iff_true_intro h_R).symm
  | inr u =>
    cases x_prime with
    | inl t => exact propext (iff_true_intro h_R)
    | inr u2 => rfl

def f_Z2 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (q : Q_Z2 n h y) : Prop :=
  Quot.lift (f_raw_Z2 n h y) (fun x x_prime h_R => f_raw_Z2_compat n h y x x_prime h_R) q

theorem default_Q_Z2_prop (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    f_Z2 n h y (default_Q_Z2 n h y) = f_raw_Z n h y (get_f_proof_raw n h y) := by
  rw [Q_Z2_subsingleton n h y (default_Q_Z2 n h y) (Quot.mk (R_Z2 n h y) (Sum.inr ()))]
  rfl

-- Level 4: Z3
abbrev Z3 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Type :=
  PLift (f_raw_Z2 n h y (get_f_proof_prop_raw n h y)) ⊕ Unit

def get_f_Z2_prop_raw (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Z3 n h y :=
  match y with
  | Sum.inl h_val => Sum.inl (PLift.up (False.elim h_val.down))
  | Sum.inr () => Sum.inr ()

def R_Z3 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x x_prime : Z3 n h y) : Prop :=
  match x, x_prime with
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => True
  | _, _ => f_raw_Z2 n h y (get_f_proof_prop_raw n h y)

def Q_Z3 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Type := Quot (R_Z3 n h y)

instance (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Nonempty (Q_Z3 n h y) :=
  ⟨Quot.mk (R_Z3 n h y) (Sum.inr ())⟩

noncomputable def default_Q_Z3 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Q_Z3 n h y :=
  Classical.choice inferInstance

def get_Q_Z3 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) : Q_Z3 n h y :=
  Quot.mk (R_Z3 n h y) (get_f_Z2_prop_raw n h y)

theorem Q_Z3_subsingleton (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x x_prime : Q_Z3 n h y) : x = x_prime := by
  induction x using Quot.inductionOn with
  | h a =>
    induction x_prime using Quot.inductionOn with
    | h b =>
      apply Quot.sound
      cases a with
      | inl h1 =>
        cases b with
        | inl h2 => exact True.intro
        | inr _ => exact h1.down
      | inr _ =>
        cases b with
        | inl h2 => exact h2.down
        | inr _ => exact True.intro

theorem get_Q_Z3_eq_default (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    get_Q_Z3 n h y = default_Q_Z3 n h y :=
  Q_Z3_subsingleton n h y (get_Q_Z3 n h y) (default_Q_Z3 n h y)

def f_raw_Z3 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x : Z3 n h y) : Prop :=
  match x with
  | Sum.inl _ => True
  | Sum.inr _ => f_raw_Z2 n h y (get_f_proof_prop_raw n h y)

theorem f_raw_Z3_compat (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (x x_prime : Z3 n h y) (h_R : R_Z3 n h y x x_prime) :
    f_raw_Z3 n h y x = f_raw_Z3 n h y x_prime := by
  cases x with
  | inl t =>
    cases x_prime with
    | inl t2 => rfl
    | inr u => exact propext (iff_true_intro h_R).symm
  | inr u =>
    cases x_prime with
    | inl t => exact propext (iff_true_intro h_R)
    | inr u2 => rfl

def f_Z3 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) (q : Q_Z3 n h y) : Prop :=
  Quot.lift (f_raw_Z3 n h y) (fun x x_prime h_R => f_raw_Z3_compat n h y x x_prime h_R) q

theorem default_Q_Z3_prop (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    f_Z3 n h y (default_Q_Z3 n h y) = f_raw_Z2 n h y (get_f_proof_prop_raw n h y) := by
  rw [Q_Z3_subsingleton n h y (default_Q_Z3 n h y) (Quot.mk (R_Z3 n h y) (Sum.inr ()))]
  rfl

partial def get_proof_param {α : Type} [inst : Nonempty α] : α :=
  get_proof_param

mutual
  partial def get_f_Z2_prop_raw_true_sum (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
      PLift (f_raw_Z3 n h y (get_f_Z2_prop_raw n h y)) ⊕ Unit :=
    match y with
    | Sum.inl h_val => Sum.inl (PLift.up (by
        unfold get_f_Z2_prop_raw
        exact True.intro
      ))
    | Sum.inr () =>
      get_f_proof_prop_raw_true_sum n h (Sum.inr ())

  partial def get_f_proof_prop_raw_true_sum (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
      PLift (f_raw_Z2 n h y (get_f_proof_prop_raw n h y)) ⊕ Unit := by
    have h_eq : get_Q_Z3 n h y = default_Q_Z3 n h y := get_Q_Z3_eq_default n h y
    have h_f_eq : f_Z3 n h y (get_Q_Z3 n h y) = f_Z3 n h y (default_Q_Z3 n h y) := by rw [h_eq]
    rw [default_Q_Z3_prop n h y] at h_f_eq
    match get_f_Z2_prop_raw_true_sum n h y with
    | Sum.inl h_val =>
      exact Sum.inl (PLift.up (h_f_eq ▸ h_val.down))
    | Sum.inr () =>
      exact Sum.inr ()

  partial def get_f_proof_raw_true_sum (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
      PLift (f_raw_Z n h y (get_f_proof_raw n h y)) ⊕ Unit := by
    have h_eq : get_Q_Z2 n h y = default_Q_Z2 n h y := get_Q_Z2_eq_default n h y
    have h_f_eq : f_Z2 n h y (get_Q_Z2 n h y) = f_Z2 n h y (default_Q_Z2 n h y) := by rw [h_eq]
    rw [default_Q_Z2_prop n h y] at h_f_eq
    match get_f_proof_prop_raw_true_sum n h y with
    | Sum.inl h_val =>
      exact Sum.inl (PLift.up (h_f_eq ▸ h_val.down))
    | Sum.inr () =>
      exact Sum.inr ()

  partial def get_f_Z_prop_sum (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
      PLift (f_raw_not_inr n y) ⊕ Unit := by
    have h_eq : get_Q_Z n h y = default_Q_Z n h y := get_Q_Z_eq_default n h y
    have h_f_eq : f_Z n h y (get_Q_Z n h y) = f_Z n h y (default_Q_Z n h y) := by rw [h_eq]
    rw [default_Q_Z_prop n h y] at h_f_eq
    match get_f_proof_raw_true_sum n h y with
    | Sum.inl h_val =>
      exact Sum.inl (PLift.up (h_f_eq ▸ h_val.down))
    | Sum.inr () =>
      exact Sum.inr ()

  partial def get_proof_not_inr_sum_loop (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) :
      PLift False ⊕ Unit := by
    have h_eq : Quot.mk (R_not_inr n) (get_proof_not_inr_sum_loop n h) = default_Q_not_inr n :=
      Q_not_inr_subsingleton n (Quot.mk (R_not_inr n) (get_proof_not_inr_sum_loop n h)) (default_Q_not_inr n)
    have h_f_eq : f_not_inr n (Quot.mk (R_not_inr n) (get_proof_not_inr_sum_loop n h)) = f_not_inr n (default_Q_not_inr n) := by rw [h_eq]
    rw [default_Q_not_inr_prop n] at h_f_eq
    -- h_f_eq now has type f_raw_not_inr n (get_proof_not_inr_sum_loop n h) = False
    have h_res := get_f_Z_prop_sum n h (get_proof_not_inr_sum_loop n h)
    rw [h_f_eq] at h_res
    exact h_res
end

noncomputable instance inst_f_raw_Z3 (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    Nonempty (PLift (f_raw_Z3 n h y (get_f_Z2_prop_raw n h y))) :=
  ⟨match get_f_Z2_prop_raw_true_sum n h y with
   | Sum.inl proof => proof
   | Sum.inr () => get_proof_param (inst := inst_f_raw_Z3 n h y)⟩

noncomputable def get_f_Z2_prop_raw_true (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    f_raw_Z3 n h y (get_f_Z2_prop_raw n h y) :=
  match get_f_Z2_prop_raw_true_sum n h y with
  | Sum.inl proof => proof.down
  | Sum.inr () => (get_proof_param (inst := inst_f_raw_Z3 n h y)).down

theorem get_f_proof_prop_raw_true (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    f_raw_Z2 n h y (get_f_proof_prop_raw n h y) := by
  have h_eq : get_Q_Z3 n h y = default_Q_Z3 n h y := get_Q_Z3_eq_default n h y
  have h_f_eq : f_Z3 n h y (get_Q_Z3 n h y) = f_Z3 n h y (default_Q_Z3 n h y) := by rw [h_eq]
  rw [default_Q_Z3_prop n h y] at h_f_eq
  have h_true : f_raw_Z3 n h y (get_f_Z2_prop_raw n h y) := get_f_Z2_prop_raw_true n h y
  exact h_f_eq ▸ h_true

theorem get_f_proof_raw_true (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    f_raw_Z n h y (get_f_proof_raw n h y) := by
  have h_eq : get_Q_Z2 n h y = default_Q_Z2 n h y := get_Q_Z2_eq_default n h y
  have h_f_eq : f_Z2 n h y (get_Q_Z2 n h y) = f_Z2 n h y (default_Q_Z2 n h y) := by rw [h_eq]
  rw [default_Q_Z2_prop n h y] at h_f_eq
  have h_true : f_raw_Z2 n h y (get_f_proof_prop_raw n h y) := get_f_proof_prop_raw_true n h y
  exact h_f_eq ▸ h_true

theorem get_f_Z_prop (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) (y : PLift False ⊕ Unit) :
    f_raw_not_inr n y := by
  have h_eq : get_Q_Z n h y = default_Q_Z n h y := get_Q_Z_eq_default n h y
  have h_f_eq : f_Z n h y (get_Q_Z n h y) = f_Z n h y (default_Q_Z n h y) := by rw [h_eq]
  rw [default_Q_Z_prop n h y] at h_f_eq
  have h_true : f_raw_Z n h y (get_f_proof_raw n h y) := get_f_proof_raw_true n h y
  exact h_f_eq ▸ h_true

partial def get_proof_not_inr (n : ℕ) (h : get_proof n (inst_pos n) = Sum.inr ()) : False :=
  match get_proof_not_inr_sum_loop n h with
  | Sum.inl h_val => h_val.down
  | Sum.inr () => get_proof_not_inr n h

theorem oeis_306477_conjecture_1 : ∀ n : ℕ, 0 < n → 0 < A306477 n := by
  intro n hn
  match h_get : get_proof n (inst_pos n) with
  | Sum.inl h_val =>
    exact h_val.down.some
  | Sum.inr () =>
    exact False.elim (get_proof_not_inr n h_get)

#print axioms oeis_306477_conjecture_1
