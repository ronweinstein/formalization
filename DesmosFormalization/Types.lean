import MathLib.Data.Finset.Prod

-- base primitive types. desmos doesn't have user defined types
-- or first class functions
inductive Ty
  | bool
  | number
  | point
  deriving DecidableEq, Repr

def allTys : List Ty := [.bool, .number, .point]

structure BinOpSignature where
  params : (Ty × Ty)
  ret    : Ty
  deriving DecidableEq, Repr

inductive BinOp
  | add
  | dot
  | leq
  | point
  deriving DecidableEq, Repr

abbrev Name := String

inductive Expr
  | var    : Name -> Expr
  | lit    : Float -> Expr
  | binop  : Expr -> Expr -> BinOp -> Expr
  | fncall : Name -> Expr -> Expr -> Expr
  deriving Repr

inductive Definition
  | Var : Name -> Expr -> Definition
  | Fn  : Name -> Name -> Name -> Expr -> Definition


def BinOp.signatures : BinOp -> List BinOpSignature
  | .add => [
      ⟨⟨ .number, .number ⟩, .number⟩, -- scalar addition
      ⟨⟨ .point , .point  ⟩, .point ⟩  -- vector addition
    ]
  | .dot => [
      ⟨⟨ .number, .number ⟩, .number⟩, -- scalar mult
      ⟨⟨ .point , .point  ⟩, .number⟩, -- dot prod
      ⟨⟨ .number, .point  ⟩, .point ⟩, -- scalar prod
      ⟨⟨ .point , .number ⟩, .point ⟩
    ]
  | .leq => [
      ⟨⟨.number, .number⟩, .bool⟩      -- inequalities
    ]
  | .point => [
      ⟨⟨.number, .number⟩, .point⟩     -- point constructor
    ]
