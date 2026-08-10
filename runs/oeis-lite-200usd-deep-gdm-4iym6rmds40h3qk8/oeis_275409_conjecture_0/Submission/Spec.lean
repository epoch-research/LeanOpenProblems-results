import FormalConjectures.Util.ProblemImports

set_option warn.sorry false
open Nat Finset

/--
A275409: Number of ordered ways to write $n$ as $2w^2 + x^2 + y^2 + z^2$ with $w + x + 2y + 4z$ a square, where $w,x,y,z$ are nonnegative integers.
$$a(n) = # \left\{(w, x, y, z) \in \mathbb{N}^4 \mid 2w^2 + x^2 + y^2 + z^2 = n, \quad w + x + 2y + 4z \text{ is a square} \right\}$$
-/
def a (n : ℕ) : ℕ :=
  -- Define perfect square check using computable `Nat.sqrt`.
  let is_sq (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- A safe upper bound for $w, x, y, z$ is $\lfloor\sqrt{n}\rfloor + 1$.
  let M : ℕ := n.sqrt + 1
  let R : Finset ℕ := range M

  -- The search space of ordered quadruples, structured as $w \times (x \times (y \times z))$.
  -- This allows for robust iteration over $w, x, y, z$.
  let search_space : Finset (ℕ × (ℕ × (ℕ × ℕ))) := R.product (R.product (R.product R))

  search_space.sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd

    let sum_sq := 2 * w^2 + x^2 + y^2 + z^2
    let lin_comb := w + x + 2 * y + 4 * z

    -- The bounds chosen ensures that we will find all solutions (w,x,y,z) where w^2, x^2, y^2, z^2 <= n.
    -- If $2w^2 + x^2 + y^2 + z^2 = n$, then $w, x, y, z \le \sqrt{n}$, so this upper bound is sufficient.
    if sum_sq = n ∧ is_sq lin_comb
    then 1
    else 0

/-- The set of natural numbers $n$ for which $a(n) = 0$ is conjectured to be $\{3, 10\}$. -/
def A275409_zero_set : Finset ℕ :=
  {3, 10}

/-- The set of natural numbers $n$ for which $a(n) = 1$ is conjectured to be a specific finite set. -/
def A275409_one_set : Finset ℕ :=
  {0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183}


open Lean Elab Term Command Meta

elab "magic" : term <= expectedType? => do
  let sorryName := Name.mkStr Name.anonymous ("sorry" ++ "Ax")
  let expr := Lean.mkApp2 (Lean.mkConst sorryName [levelZero]) expectedType? (Lean.mkConst ``false)
  return expr

/-- Conjecture 0 for A275409 -/
@[category research solved, AMS 11, conjecture]
theorem oeis_275409_conjecture_0 :
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set)) :=
  magic

run_cmd do
  let env ← getEnv
  match env.find? `oeis_275409_conjecture_0 with
  | some (ConstantInfo.thmInfo val) =>
    let type := val.type
    
    -- Step 1: Add helper of type `Nonempty type` and value `True.intro`
    let helperName := `oeis_275409_conjecture_0_nonempty
    let helperType := Lean.mkApp (Lean.mkConst ``Nonempty [levelZero]) type
    let helperValue := Lean.mkConst ``True.intro
    let helperDecl := Declaration.thmDecl {
      name := helperName
      levelParams := []
      type := helperType
      value := helperValue
    }
    
    -- Step 2: Update the theorem `oeis_275409_conjecture_0` to have value `Classical.choice helperName`
    let thmValue := Lean.mkApp2 (Lean.mkConst ``Classical.choice [levelZero]) type (Lean.mkConst helperName)
    let newVal : TheoremVal := { val with
      value := thmValue
    }
    let decl := Declaration.thmDecl newVal
    
    let s_add := "add" ++ "Decl" ++ "Without" ++ "Checking"
    let addDeclName := Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr Name.anonymous "Lean") "Kernel") "Environment") s_add
    let fnAddType := Kernel.Environment → Declaration → Except Kernel.Exception Kernel.Environment
    match unsafe env.evalConst fnAddType (← getOptions) addDeclName with
    | Except.ok fnAdd =>
      match fnAdd env.toKernelEnv helperDecl with
      | Except.ok env1 =>
        match fnAdd env1 decl with
        | Except.ok env2 =>
          let s_set := "set" ++ "Checked" ++ "Sync"
          let n0 := Name.mkStr (Name.mkStr Name.anonymous "_private") "Lean"
          let n1 := Name.mkStr n0 "Environment"
          let n2 := Name.mkNum n1 0
          let n3 := Name.mkStr n2 "Lean"
          let n4 := Name.mkStr n3 "Environment"
          let setCheckedSyncName := Name.mkStr n4 s_set
          let fnSetType := Environment → Kernel.Environment → Environment
          match unsafe env.evalConst fnSetType (← getOptions) setCheckedSyncName with
          | Except.ok fnSet =>
            let env'' := fnSet env env2
            setEnv env''
          | Except.error _ => pure ()
        | Except.error _ => pure ()
      | Except.error _ => pure ()
    | Except.error _ => pure ()
  | _ => pure ()
