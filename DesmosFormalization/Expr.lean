import DesmosFormalization.Types
import DesmosFormalization.Wackscope
import DesmosFormalization.Infer

inductive Value
  | bool   : Bool -> Value
  | number : Float -> Value
  | point  : Float -> Float -> Value
  deriving Repr

inductive HasType : Value -> Ty -> Prop
 | htBool    : HasType (.bool b)    .bool
 | htNum     : HasType (.number n)  .number
 | htPoint : HasType (.point x y) .point

def VarExprEnv := Name -> Option Expr
def FnExprEnv  := Name -> Option (Name -> Name -> Expr)

def evalOp : BinOp -> Value -> Value -> Option Value
  | .add, .number x, .number y =>
      some (.number (x + y))
  | .add, .point x₁ y₁, .point x₂ y₂ =>
      some (.point (x₁ + x₂) (y₁ + y₂))
  | .dot, .number x, .number y =>
      some (.number (x * y))
  | .dot, .point x₁ y₁, .point x₂ y₂ =>
      some (.number (x₁ * x₂ + y₁ * y₂))
  | .dot, .number s, .point x y =>
      some (.point (s * x) (s * y))
  | .dot, .point x y, .number s =>
      some (.point (s * x) (s * y))
  | .point, .number x, .number y =>
      some (.point x y)
  | .leq, .number x, .number y =>
      some (.bool (x <= y))
  | _, _, _ =>
      none

def evalVar (x : Name) (Γvar : VarExprEnv) (Γfn : FnExprEnv) : Option Value := do
  let expr <- Γvar x
  evalExpr expr


  some (.number 5)

def evalExpr 
