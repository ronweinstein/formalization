import DesmosFormalization.Types
import DesmosFormalization.Wackscope


abbrev WackEnv := Name -> Option Wackscope
abbrev FnEnv   := Name -> Option WackscopeFn

def inferExpr (e : Expr) (Γglob : WackEnv) (Γfn : FnEnv) : Wackscope :=
  match e with
  | .lit => {
      deps  := ∅
      scheme := { (Ty.number, fun e => nomatch e) }
    }
  | .var x =>
      if let some wack := Γglob x then
        if ∃ y ∈ wack.deps, (inferExpr (Expr.var y) Γglob).deps = ∅ then
          Wackscope.empty
        else by sorry
      else by sorry
  | .binop e₁ e₂ op =>
      let w₁ := inferExpr e₁ Γglob Γfn
      let w₂ := inferExpr e₂ Γglob Γfn
      mergeByOp w₁ w₂ op
  | .fncall f e₁ e₂ =>
    by sorry

def inferDefinition (definition : Definition) (Γglob : WackEnv) (Γfn : FnEnv)
  : WackEnv × FnEnv :=
  match definition with
  | .Var x e =>
      let e_wack := inferExpr e Γglob Γfn;
      (fun y => if x = y then e_wack else Γglob y, Γfn)

  | .Fn f x y e =>
      -- get the expression type
      let w := inferExpr e Γglob Γfn
      -- -- remove dependence from x/y (as they're in scope)
      -- let w := w.eliminateDeps { x, y }
      let w_fn : WackscopeFn :=
        let ⟨deps, scheme⟩ := w
        let scheme' := scheme.map (fun ⟨ret, depTypes⟩ =>
          if hx : x ∈ deps then
            let τx := depTypes ⟨x, hx⟩
            if hy : y ∈ deps then
              let τy := depTypes ⟨y, hy⟩
              let w := w.eliminateDeps { x, y }
              ⟨⟨(τx, τy), ret⟩, depTypes⟩
            else by sorry
          else by sorry
        )
        ⟨deps, scheme'⟩

      (Γglob, Γfn)

def inferProgram (program : List Definition) : WackEnv × FnEnv := by sorry
