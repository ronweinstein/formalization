import DesmosFormalization.Types
import DesmosFormalization.Wackscope
import DesmosFormalization.Infer

abbrev Assignment := Name -> Ty

def Agrees (σ : Assignment) (s : Scheme) (case : Ty × (s.deps -> Ty))
  : Prop :=
  ∀ d : s.deps, σ d = case.2 d



inductive HasType :
  VarEnv -> FnEnv -> Assignment -> Expr -> Ty -> Prop

  | var_defined
    (Γv Γf σ x s case τ)
    (hlookup : Γv x = some s)
    (hmem    : case ∈ s.scheme)
    (hagree  : Agrees σ s case)
    (hτ      : τ = case.1) :
    HasType Γv Γf σ (.var x) τ

  | var_free
    (Γv Γf σ x)
    (hLookup : Γv x = none) :
    HasType Γv Γf σ (.var x) (σ x)

  | lit : HasType Γv Γf σ (.lit x) .number

  | add_number
    (h₁ : HasType Γv Γf σ e₁ .number)
    (h₂ : HasType Γv Γf σ e₂ .number) :
    HasType Γv Γf σ (.binop e₁ e₂ .add) .number

  | add_point
    (h₁ : HasType Γv Γf σ e₁ .point)
    (h₂ : HasType Γv Γf σ e₂ .point) :
    HasType Γv Γf σ (.binop e₁ e₂ .add) .point

  | call
    (hlookup : Γf f = some s)
    (hmem    : case ∈ s.scheme)
    (hagree  : ∀ d : s.deps, σ d = case.2 d)
    :
    HasType Γv Γf σ (.call f e₁ e₂) τret

def SchemeDenotes Γv Γf e (s : Scheme) :=
  ∀ σ τ,
    HasType Γv Γf σ e τ
    ↔
    (τ, fun x : s.deps => σ x) ∈ s.scheme

lemma freeVarScheme_complete :
  ∀ σ x,
    ∃ case ∈ (Scheme.freeVar x).scheme,
    case.1 = σ x ∧ Agrees σ _ case := by sorry

theorem inferExpr_sound :
  inferExpr Γv Γf e = s -> SchemeDenotes Γv Γf e s := by
  induction e generalizing s
  case var x =>
    intro hEq
    simp [inferExpr] at hEq
    unfold SchemeDenotes
    intro σ τ
    apply Iff.intro
    · intro hType
      cases hType with
      | var_defined Γv Γf σ x s case τ hlookup hmem hagree hτ =>
        simp [hlookup] at hEq
        unfold Agrees at hagree
        aesop
      | var_free Γv Γf σ x hlookup =>
        rw [hlookup] at hEq
        simp at hEq
        have hsingleton : s.deps = { x } := by
          rw [<-hEq]
          unfold Scheme.freeVar
          simp
        have hfun : (fun x₁ : s.deps => σ x₁) = (fun x₁ => σ x) := by
          grind
        rw [hfun]
        rw [<-hEq]
        unfold Scheme.freeVar
        unfold allTys
        cases σ x
        grind
        grind
        grind

    · cases hlookup : Γv x
      rw [hlookup] at hEq
      simp at hEq
      rw [<-hEq]
      intro hmem
      rcases List.mem_map.mp hmem with ⟨τ', hτ', hpair⟩
      injection hpair with hτeq hfun
      have hσx : τ = σ x := by
        rw [<-hτeq]
        have := congrArg (fun f => f ⟨x, by grind⟩) hfun
        simp at this
        exact this
      rw [hσx]
      apply HasType.var_free
      exact hlookup

      rw [hlookup] at hEq
      simp at hEq
      intro hmem
      -- have case :=
      apply HasType.var_defined Γv Γf σ x s (τ, (σ ·)) τ
      rw [hEq] at hlookup
      exact hlookup
      exact Multiset.mem_coe.mp hmem
      exact (congrFun ∘ fun a => a) rfl
      exact ((fun a => a) ∘ fun a => a) rfl

  case lit x =>
    intro hEq
    simp [inferExpr] at hEq
    unfold SchemeDenotes
    intro σ τ
    apply Iff.intro
    intro hType
    cases hType
    rw [<-hEq]
    simp
    aesop

    intro hmem
    rw [<-hEq] at hmem
    simp at hmem
    rw [hmem.1]
    apply HasType.lit

  case binop e₁ e₂ op ih₁ ih₂ =>
    intro hEq
    simp [inferExpr] at hEq
    let s₁ := inferExpr Γv Γf e₁
    let s₂ := inferExpr Γv Γf e₂
    have h₁ : SchemeDenotes Γv Γf e₁ s₁ := by
      exact (ih₁ ∘ congrArg (inferExpr Γv Γf)) rfl
    have h₂ : SchemeDenotes Γv Γf e₂ s₂ := by
      exact (ih₂ ∘ congrArg (inferExpr Γv Γf)) rfl
    intro σ τ

    apply Iff.intro
    




    -- apply HasType.lit Γv Γf σ (.lit x) .number







      -- have case := (τ, fun x : ↥s.deps => σ x)















      -- cases hσ : σ x
      -- simp [Scheme.freeVar, hσ]

      -- have hfun : (fun x₁ => σ ↑x₁) = (fun _ => Ty.bool) := by
      --   funext x₁





    -- cases hlookup
    -- simp at hEq

    -- cases hType






-- theorem soundness
