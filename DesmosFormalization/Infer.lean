import DesmosFormalization.Types
import DesmosFormalization.Wackscope

-- global environments for variables and functions
abbrev VarEnv := Name -> Option Scheme
abbrev FnEnv   := Name -> Option FnScheme

def VarEnv.extend (Γ : VarEnv) (x : Name) (s : Scheme) : VarEnv :=
  fun y => if y = x then s else Γ y

def FnEnv.extend (Γ : FnEnv) (f : Name) (fs : FnScheme) : FnEnv :=
  fun g => if g = f then fs else Γ g

-- assumes variable definitions are topologically sorted
def inferExpr (Γv : VarEnv) (Γf : FnEnv) (e : Expr) : Scheme :=
  match e with
  | .lit _ => ⟨∅, [(Ty.number, (nomatch ·))]⟩

  | .var x =>
      -- return the global variable if it exists,
      -- otherwise create a new wackscope with dependency 'x' and scheme ≈ ∀α.α
      (Γv x).getD (Scheme.freeVar x)

  | .binop e₁ e₂ op =>
      -- infer both subexpressions, then get the valid operator overloads
      let s₁ := inferExpr Γv Γf e₁
      let s₂ := inferExpr Γv Γf e₂
      mergeByOp s₁ s₂ op

  | .call f e₁ e₂ =>
      -- same as binop really
    if let some fs := Γf f then
      let s₁ := inferExpr Γv Γf e₁
      let s₂ := inferExpr Γv Γf e₂
      mergeByFn s₁ s₂ fs
    else
      -- return the empty (impossible) scheme if the function isn't found
      -- this doesn't happen with vars because they can just be wackscoped
      Scheme.empty


def inferDefinition (definition : Definition) (Γv : VarEnv) (Γf : FnEnv)
  : VarEnv × FnEnv :=
  match definition with
  | .varDef x e =>
      let s := inferExpr Γv Γf e;
      (Γv.extend x s, Γf)

  -- needs a way to return all possible types for unused variable
  | .fnDef f x y e =>
      -- get the expression type
      let s := inferExpr Γv Γf e
      -- -- remove dependence from x/y
      let fs : FnScheme :=
        let ⟨deps, scheme⟩ := s

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

        -- -- attempt at making this n-ary generalizable
        -- -- it kinda worked but has also heavily messed the #reduce output
        -- let params := [x, y]

        -- let deps' := deps \ params.toFinset
        -- let h_subset : deps' ⊆ deps := Finset.sdiff_subset

        -- -- -- List (⟨paramTypes, retType⟩, deps -> Ty)
        -- let scheme' :=
        --   scheme.flatMap fun ⟨τret, f⟩ =>
        --     -- [x, y] -> [[τ₁x, τ₁y],[τ₂x, τ₂y], ...]
        --     let rec prod : List Name -> List (List Ty)
        --     | [] => [[]]
        --     | x :: rest =>
        --         let xTys := if h : x ∈ deps
        --         then [f ⟨x, by assumption⟩]
        --         else allTys

        --         (xTys.product (prod rest)).map fun (τx, l) =>
        --           τx :: l

        --     (prod params).map fun paramTys =>
        --       (⟨(paramTys[1], paramTys[2]), τret⟩, fun ⟨x, hx⟩ => f ⟨x, h_subset hx⟩)

        -- ⟨deps', scheme'⟩

      (Γv, Γf.extend f fs)

-- generates the final environments of a program
def inferProgram (program : List Definition) : VarEnv × FnEnv :=
  let Γ   : VarEnv := fun _ => none
  let Γf : FnEnv  := fun _ => none
  program.foldl (fun envs d => inferDefinition d envs.1 envs.2) (Γ, Γf)



-- helper for printing types with #reduce
deriving instance Inhabited for Scheme
def getVarType (program : List Definition) (var : Name) : List Ty :=
  let Γprog := inferProgram program
  (Γprog.1 var).get!.scheme.map (·.1)

#reduce getVarType [.varDef "a" (.lit 5)] "a"
