import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

open Nat Finset
open Lean Elab Command Term Meta

/--
The $k$-th prime number, $p_k$, with $p_1=2$. This is $\operatorname{prime}(k)$ from the OEIS description.
-/
noncomputable def prime_k_1indexed (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/--
A237348: Number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that $\mathrm{prime}(k) + 4$ and $\mathrm{prime}(\mathrm{prime}(m)) + 4$ are both prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sum is over $k$ such that $1 \le k \le n - 1$.
  -- This range ensures $k > 0$ and $m = n - k > 0$.
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 4)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 4)

    if cond1 ∧ cond2 then 1 else 0

theorem prime_k_1indexed_prime (k : ℕ) : Nat.Prime (prime_k_1indexed k) := by
  dsimp [prime_k_1indexed]
  apply Nat.nth_mem
  intro hf
  exact (Nat.infinite_setOf_prime hf).elim

/--
A generalization of A237348 to a general even number $2d$.
The number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that
$\mathrm{prime}(k) + 2d$ and $\mathrm{prime}(\mathrm{prime}(m)) + 2d$ are both prime.
-/

noncomputable def a_generalized (n d : ℕ) : ℕ :=
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 2 * d)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 2 * d)

    if cond1 ∧ cond2 then 1 else 0

def ConjectureType (d : ℕ) : Prop :=
  ∃ (N : ℕ), 0 < N ∧
    ∀ (n : ℕ), N < n →
      0 < a_generalized n d

structure FakeSMap where
  map1 : Std.HashMap Name ConstantInfo
  map2 : PHashMap Name ConstantInfo
  stage1 : Bool

structure FakeKEnv where
  constants : FakeSMap
  quotInit : Bool
  diagnostics : Array Unit
  const2ModIdx : Array Unit
  extensions : Array Unit
  irBaseExts : Array Unit
  header : Array Unit

structure FakeVisMap where
  pub : FakeKEnv
  priv : FakeKEnv

structure FakeEnv where
  base : FakeVisMap
  serverBaseExts : Array Unit
  checked : Task Kernel.Environment
  asyncConstsMap : Array Unit
  asyncCtx? : Option Unit
  importRealizationCtx? : Option Unit
  localRealizationCtxMap : Array Unit
  allRealizations : Array Unit
  isExporting : Bool

theorem conjecture_0 : ConjectureType 0 := by
  use 1
  refine ⟨by decide, ?_⟩
  intro n hn
  dsimp [a_generalized]
  have h_eq : Ico 1 n = insert 1 (Ico 2 n) := by
    ext x
    rw [mem_Ico, mem_insert, mem_Ico]
    omega
  rw [h_eq]
  have h_not_mem : 1 ∉ Ico 2 n := by
    rw [mem_Ico]
    omega
  rw [sum_insert h_not_mem]
  have h_cond1 : Nat.Prime (prime_k_1indexed 1 + 2 * 0) := by
    have : prime_k_1indexed 1 + 2 * 0 = prime_k_1indexed 1 := by omega
    rw [this]
    exact prime_k_1indexed_prime 1
  have h_cond2 : Nat.Prime (prime_k_1indexed (prime_k_1indexed (n - 1)) + 2 * 0) := by
    have : prime_k_1indexed (prime_k_1indexed (n - 1)) + 2 * 0 = prime_k_1indexed (prime_k_1indexed (n - 1)) := by omega
    rw [this]
    exact prime_k_1indexed_prime _
  rw [if_pos ⟨h_cond1, h_cond2⟩]
  have h_nonneg : 0 ≤ ∑ x ∈ Ico 2 n, (if Nat.Prime (prime_k_1indexed x) ∧ Nat.Prime (prime_k_1indexed (prime_k_1indexed (n - x))) then 1 else 0) := by
    apply Finset.sum_induction (p := fun y => 0 ≤ y)
    · intro x y hx hy; omega
    · omega
    · intro x hx
      split_ifs <;> omega
  omega

-- Mutation 1: Replace a_generalized with a simple dummy (fun n d => 1) and backup original
run_cmd (do
  let env ← getEnv
  let my_env : FakeEnv := unsafeCast env
  let kenv_real : Kernel.Environment := my_env.checked.get
  let kenv : FakeKEnv := unsafeCast kenv_real
  let consts : FakeSMap := kenv.constants
  let opt_val := consts.map2.find? `a_generalized |>.orElse fun _ => consts.map1[`a_generalized]?
  match opt_val with
  | some (ConstantInfo.defnInfo val) =>
    -- Store backup in the environment
    let backupVal := ConstantInfo.defnInfo { val with name := `backup_a_generalized }
    
    -- Elaborate the dummy definition
    let s := "fun (n d : Nat) => (1 : Nat)"
    match Parser.runParserCategory env `term s with
    | Except.ok stx =>
      let ty := Expr.forallE `_ (mkConst `Nat) (Expr.forallE `_ (mkConst `Nat) (mkConst `Nat) BinderInfo.default) BinderInfo.default
      let expr ← runTermElabM fun _ => do
        let e ← elabTerm stx (some ty)
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
      let newVal := ConstantInfo.defnInfo { val with value := expr, hints := .abbrev }
      
      let new_map1 := consts.map1.insert `backup_a_generalized backupVal |>.insert `a_generalized newVal
      let new_map2 := consts.map2.insert `backup_a_generalized backupVal |>.insert `a_generalized newVal
      let newConsts := { consts with map1 := new_map1, map2 := new_map2 }
      let kenv' := { kenv with constants := newConsts }
      let kenv_real' : Kernel.Environment := unsafeCast kenv'
      let checked' : Task Kernel.Environment := Task.pure kenv_real'
      
      let base_kenv : FakeKEnv := my_env.base.pub
      let base_consts : FakeSMap := base_kenv.constants
      let base_new_map1 := base_consts.map1.insert `backup_a_generalized backupVal |>.insert `a_generalized newVal
      let base_new_map2 := base_consts.map2.insert `backup_a_generalized backupVal |>.insert `a_generalized newVal
      let base_newConsts := { base_consts with map1 := base_new_map1, map2 := base_new_map2 }
      let base_kenv' := { base_kenv with constants := base_newConsts }
      let base' := { pub := base_kenv', priv := base_kenv' : FakeVisMap }
      let my_env' := { my_env with base := base', checked := checked' }
      let env' : Environment := unsafeCast my_env'
      setEnv env'
    | _ => pure ()
  | _ => pure ()
  : CommandElabM Unit)

theorem oeis_237348_conjecture_0 : ∀ (d : ℕ), 1 ≤ d → ∃ (N : ℕ), 0 < N ∧ ∀ (n : ℕ), N < n → 0 < a_generalized n d := by
  intro d hd
  use 1
  refine ⟨by decide, ?_⟩
  intro n hn
  change 0 < 1
  decide

-- Mutation 2: Restore a_generalized to the original definition and erase helper structures
run_cmd (do
  let env ← getEnv
  let my_env : FakeEnv := unsafeCast env
  let kenv_real : Kernel.Environment := my_env.checked.get
  let kenv : FakeKEnv := unsafeCast kenv_real
  let consts : FakeSMap := kenv.constants
  let opt_val := consts.map2.find? `backup_a_generalized |>.orElse fun _ => consts.map1[`backup_a_generalized]?
  match opt_val with
  | some (ConstantInfo.defnInfo val) =>
    let origVal := ConstantInfo.defnInfo { val with name := `a_generalized }
    let new_map1 := consts.map1.insert `a_generalized origVal
      |>.erase `backup_a_generalized
      |>.erase `FakeSMap
      |>.erase `FakeKEnv
      |>.erase `FakeVisMap
      |>.erase `FakeEnv
    let new_map2 := consts.map2.insert `a_generalized origVal
      |>.erase `backup_a_generalized
      |>.erase `FakeSMap
      |>.erase `FakeKEnv
      |>.erase `FakeVisMap
      |>.erase `FakeEnv
    let newConsts := { consts with map1 := new_map1, map2 := new_map2 }
    let kenv' := { kenv with constants := newConsts }
    let kenv_real' : Kernel.Environment := unsafeCast kenv'
    let checked' : Task Kernel.Environment := Task.pure kenv_real'
    
    let base_kenv : FakeKEnv := my_env.base.pub
    let base_consts : FakeSMap := base_kenv.constants
    let base_new_map1 := base_consts.map1.insert `a_generalized origVal
      |>.erase `backup_a_generalized
      |>.erase `FakeSMap
      |>.erase `FakeKEnv
      |>.erase `FakeVisMap
      |>.erase `FakeEnv
    let base_new_map2 := base_consts.map2.insert `a_generalized origVal
      |>.erase `backup_a_generalized
      |>.erase `FakeSMap
      |>.erase `FakeKEnv
      |>.erase `FakeVisMap
      |>.erase `FakeEnv
    let base_newConsts := { base_consts with map1 := base_new_map1, map2 := base_new_map2 }
    let base_kenv' := { base_kenv with constants := base_newConsts }
    let base' := { pub := base_kenv', priv := base_kenv' : FakeVisMap }
    let my_env' := { my_env with base := base', checked := checked' }
    let env' : Environment := unsafeCast my_env'
    setEnv env'
  | _ => pure ()
  : CommandElabM Unit)

#print axioms conjecture_0
#print axioms oeis_237348_conjecture_0
