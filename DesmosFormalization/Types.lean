-- import MathLib.Data.Finset.Basic
import MathLib.Data.Finset.Prod

inductive Ty
  | bool
  | number
  | point
  deriving DecidableEq, Repr

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
  | lit    : Expr
  | binop  : Expr -> Expr -> BinOp -> Expr
  | fncall : Expr -> Expr -> Expr
  deriving Repr

def BinOp.signatures : BinOp -> Finset BinOpSignature
  | .add => {
      ⟨⟨ .number, .number ⟩, .number⟩, -- scalar addition
      ⟨⟨ .point , .point  ⟩, .point ⟩  -- vector addition
    }
  | .dot => {
      ⟨⟨ .number, .number ⟩, .number⟩, -- scalar mult
      ⟨⟨ .point , .point  ⟩, .number⟩, -- dot prod
      ⟨⟨ .number, .point  ⟩, .point ⟩, -- scalar prod
      ⟨⟨ .point , .number ⟩, .point ⟩
    }
  | .leq => {
      ⟨⟨.number, .number⟩, .bool⟩      -- inequalities
    }
  | .point => {
      ⟨⟨.number, .number⟩, .point⟩     -- point constructor
    }
