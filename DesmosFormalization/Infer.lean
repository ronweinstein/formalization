import DesmosFormalization.Types
import DesmosFormalization.Wackscope

-- global environments for variables and functions
abbrev VarEnv := Name -> Option Wackscope
abbrev FnEnv   := Name -> Option FnWackscope

-- assumes variable definitions are topologically sorted
def inferExpr (e : Expr) (Γ : VarEnv) (Γfn : FnEnv) : Wackscope :=
  match e with
  | .lit _ => ⟨∅, [(Ty.number, (nomatch ·))]⟩

  | .var x =>
      -- return the global variable if it exists,
      -- otherwise create a new wackscope with dependency 'x' and scheme ≈ ∀α.α
      (Γ x).getD ⟨{ x }, allTys.map fun τ => ⟨τ, fun _ => τ⟩⟩

  | .binop e₁ e₂ op =>
      -- infer both subexpressions, then get the valid operator overloads
      let w₁ := inferExpr e₁ Γ Γfn
      let w₂ := inferExpr e₂ Γ Γfn
      mergeByOp w₁ w₂ op

  | .fncall f e₁ e₂ =>
      -- same as binop really
    if let some wf := Γfn f then
      let w₁ := inferExpr e₁ Γ Γfn
      let w₂ := inferExpr e₂ Γ Γfn
      mergeByFn w₁ w₂ wf
    else
      -- return the empty (impossible) scheme if the fonction isn't found
      -- this doesn't happen with vars because they can just be wackscoped
      Wackscope.empty


def inferDefinition (definition : Definition) (Γ : VarEnv) (Γfn : FnEnv)
  : VarEnv × FnEnv :=
  match definition with
  | .Var x e =>
      let e_wack := inferExpr e Γ Γfn;
      (fun y => if x = y then e_wack else Γ y, Γfn)

  -- needs a way to return all possible types for unused variable
  | .Fn f x y e =>
      -- get the expression type
      let w := inferExpr e Γ Γfn
      -- -- remove dependence from x/y
      let wf : FnWackscope :=
        let ⟨deps, scheme⟩ := w

        if hx : x ∈ deps then
          if hy : y ∈ deps then

            -- body depends on both parameters
            -- parameters "eliminate" wackscope dependencies
            let deps' := deps \ {x, y}
            let scheme' := scheme.map fun ⟨τret, depTypes⟩ =>
              let τx := depTypes ⟨x, hx⟩
              let τy := depTypes ⟨y, hy⟩
              let h_subset : deps' ⊆ deps := by exact Finset.sdiff_subset
              let depTypes' : deps' -> Ty := fun ⟨d, hd⟩ => depTypes ⟨d, h_subset hd⟩
              let signature := ⟨(τx, τy), τret⟩
              ⟨signature, depTypes'⟩
            ⟨deps', scheme'⟩

          else
            let deps' := deps \ { x }
            let scheme' := (scheme.product allTys).map fun (⟨τret, depTypes⟩, τy) =>
              let τx := depTypes ⟨x, hx⟩
              let h_subset : deps' ⊆ deps := by exact Finset.sdiff_subset
              let depTypes' : deps' -> Ty := fun ⟨d, hd⟩ => depTypes ⟨d, h_subset hd⟩
              let signature := ⟨(τx, τy), τret⟩
              ⟨signature, depTypes'⟩
            ⟨deps', scheme'⟩

        else if hy : y ∈ deps then
          let deps' := deps \ { y }
          let scheme' := (scheme.product allTys).map fun (⟨τret, depTypes⟩, τx) =>
            let τy := depTypes ⟨y, hy⟩
            let h_subset : deps' ⊆ deps := by exact Finset.sdiff_subset
            let depTypes' : deps' -> Ty := fun ⟨d, hd⟩ => depTypes ⟨d, h_subset hd⟩
            let signature := ⟨(τx, τy), τret⟩
            ⟨signature, depTypes'⟩
          ⟨deps', scheme'⟩
        else
          let scheme' := (scheme.product (allTys.product allTys)).map fun (⟨τret, depTypes⟩, (τx, τy)) =>
            let signature := ⟨(τx, τy), τret⟩
            ⟨signature, depTypes⟩
          ⟨deps, scheme'⟩

      (Γ, fun g => if g = f then wf else Γfn g)

-- generates the final environments of a program
def inferProgram (program : List Definition) : VarEnv × FnEnv :=
  let Γ   : VarEnv := fun _ => none
  let Γfn : FnEnv  := fun _ => none
  program.foldl (fun envs d => inferDefinition d envs.1 envs.2) (Γ, Γfn)

deriving instance Inhabited for Wackscope
#reduce (let Γprog := inferProgram [.Var "a" (.lit 5.0)]; (Γprog.1 "a").get!.scheme.map (·.1))
#reduce (let Γprog := inferProgram [.Var "a" (.var "b")]; (Γprog.1 "a").get!.scheme.map (·.1))
#reduce (let Γprog := inferProgram [.Var "a" (.binop (.var "b") (.var "c") .add)]; (Γprog.1 "a").get!.scheme.map (·.1))
#reduce (let Γprog := inferProgram [.Var "a" (.binop (.var "b") (.var "c") .dot)]; (Γprog.1 "a").get!.scheme.map (·.1))
