import DesmosFormalization.Types
import DesmosFormalization.Wackscope


abbrev WackEnv := Name -> Option Wackscope

def infer (e : Expr) (Γwack : WackEnv) : Wackscope :=
  match e with
  | .lit => {
      deps  := ∅
      types := { (Ty.number, fun e => nomatch e) }
    }
  | .var x =>
      if let some wack := Γwack x then
        if ∃ y ∈ wack.deps, (infer (Expr.var y) Γwack).deps = ∅ then
          Wackscope.empty
        else by sorry
      else by sorry
  | .binop e₁ e₂ op =>
      let w₁ := infer e₁ Γwack
      let w₂ := infer e₂ Γwack
      mergeByOp w₁ w₂ op
  | .vardef x e =>
    by sorry
  | .fndef f x y e =>
    by sorry
  | .fncall f e₁ e₂ =>
    by sorry

  -- | .fncall e₁ e₂ => ?
