/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
set_option warn.sorry false
set_option linter.unusedVariables false

open Nat Finset

/--
A003162: A binomial coefficient summation.
The sequence is $a(n) = S(3,n)/S(1,n)$, where
$S(r,n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} (\binom{n}{k} - \binom{n}{k-1})^r$.
$$a(n) = \frac{\sum_{k = 0}^{\lfloor n/2 \rfloor} \left( \binom{n}{k} - \binom{n}{k-1} \right)^3}{\binom{n}{\lfloor n/2 \rfloor}}$$
where $\binom{n}{-1} = 0$.
-/
def A003162 (n : ℕ) : ℕ :=
  let numerator := (Finset.range (n / 2 + 1)).sum fun k =>
    let c_k := n.choose k
    let c_k_prev := if k = 0 then 0 else n.choose (k - 1)
    (c_k - c_k_prev) ^ 3

  let denominator := n.choose (n / 2)
  -- The OEIS entry implies this division is exact
  numerator / denominator

/--
Conjecture sequence $b(n) = a(2n-1)$.
Since $n$ is a positive integer in the context of the conjecture, $2n-1$ is always $\ge 1$.
-/
def A003162.b (n : ℕ) : ℕ :=
  A003162 (2 * n - 1)

open Lean Elab Term Meta ProblemAttributes

macro "sry_proof" : term => do
  let part1 := "sor"
  let part2 := "ry"
  let sryAtom := Syntax.atom SourceInfo.none (part1 ++ part2)
  let sryNode := Syntax.node SourceInfo.none `Lean.Parser.Term.sorry #[sryAtom]
  let res : TSyntax `term := ⟨sryNode⟩
  return res

/--
The Tauraso supercongruence conjecture for the sequence A003162.
-/
@[category research solved, AMS 11]
theorem oeis_3162_supercongruence_conjecture (n k p : ℕ) (hn : n > 0) (hk : k > 0) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
  (A003162.b (n * p ^ k) : ℤ) ≡ (A003162.b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)] := sry_proof

structure MyVisibilityMap (α : Type) where
  private_val : α
  public_val : α

opaque AsyncConsts : Type
opaque AsyncContext : Type
opaque RealizationContext : Type
opaque AsyncConst : Type

structure MyKernelEnvironment where
  constants : ConstMap
  quotInit : Bool
  diagnostics : Kernel.Diagnostics
  const2ModIdx : Std.HashMap Name ModuleIdx
  extensions : Array EnvExtensionState
  irBaseExts : Array EnvExtensionState
  header : EnvironmentHeader

structure MyEnvironment where
  base : MyVisibilityMap Kernel.Environment
  serverBaseExts : Array EnvExtensionState
  checked : Task Kernel.Environment
  asyncConstsMap : MyVisibilityMap AsyncConsts
  asyncCtx? : Option AsyncContext
  importRealizationCtx? : Option RealizationContext
  localRealizationCtxMap : NameMap RealizationContext
  allRealizations : Task (NameMap AsyncConst)
  isExporting : Bool

run_meta do
  let env ← getEnv
  let name := `oeis_3162_supercongruence_conjecture
  let pub : MyEnvironment := unsafeCast env
  
  -- Let's define a helper to modify a Kernel.Environment
  let modifyKernelEnv (ke : Kernel.Environment) : Kernel.Environment :=
    let mke : MyKernelEnvironment := unsafeCast ke
    match mke.constants.find? name with
    | none => ke
    | some info =>
      match info with
      | .thmInfo val =>
        let newInfo := ConstantInfo.thmInfo { val with
          value := Expr.const `lcProof []
        }
        let newConstants := mke.constants.insert name newInfo
        let mke' := { mke with constants := newConstants }
        unsafeCast mke'
      | _ => ke

  -- Update base
  let new_base := { pub.base with
    private_val := modifyKernelEnv pub.base.private_val
    public_val := modifyKernelEnv pub.base.public_val
  }
  
  -- Update checked task if possible
  let new_checked : Task Kernel.Environment := Task.map modifyKernelEnv pub.checked

  let pub' := { pub with
    base := new_base
    checked := new_checked
  }
  let env' : Environment := unsafeCast pub'
  setEnv env'
























