import BSWLean.CNF

/-!
# Conversion of assignments into clauses

The negation of assignment is a clause.

This file provides all necessary definitions to make this conversion.
-/

/-- Takes assignment `ρ`, variable `v` and produce a literal contradicting `ρ`, if `v` happens
to be in the preimage of `ρ`. -/
@[simp]
def Assignment.negVariable {vars} (ρ : Assignment vars) (v : Variable) : Option (Literal vars) :=
  if h_v_mem_vars : v ∈ vars then
    some (Literal.mk ⟨v, h_v_mem_vars⟩ ¬ρ v h_v_mem_vars)
  else
    none

lemma Assignment.negVariable_inj {vars} {ρ : Assignment vars} {x₁ x₂ : Variable} {y : Literal vars}
    (h_y_in_mp_x1 : y ∈ ρ.negVariable x₁) (h_y_in_mp_x2 : y ∈ ρ.negVariable x₂) : x₁ = x₂ := by
  grind [Assignment.negVariable, Variable.toLiteral, Variable.toNegLiteral]

/-- The assignment to clause conversion function. -/
def Assignment.toClause {vars} (ρ : Assignment vars) : Clause vars :=
  vars.filterMap (ρ.negVariable) (by exact fun a a' b a_1 a_2 ↦ negVariable_inj a_1 a_2)

@[simp]
lemma Assignment.in_toClause {vars} (ρ : Assignment vars) (l : Literal vars) :
    l ∈ ρ.toClause ↔ (l.variable ∈ vars ∧ l.eval ρ = false) := by
  unfold Assignment.toClause
  simp only [Finset.mem_filterMap]
  constructor
  · aesop (add safe unfold Literal.eval)
  intro ⟨h_var, h_eval⟩
  use l.variable
  unfold Assignment.negVariable
  unfold Literal.eval at h_eval
  simp_all [↓reduceDIte]
  ext
  all_goals grind

@[simp]
lemma Assignment.toClause_eval {vars} (ρ : Assignment vars) : ρ.toClause.eval ρ = false := by
  rw [Clause.eval_eq_false_iff_all_falsified_literals]
  aesop

@[simp]
lemma Assignment.toClause_variables {vars} (ρ : Assignment vars) : ρ.toClause.variables = vars := by
  unfold Clause.variables
  ext v
  refine ⟨fun a => by aesop, fun h_v_in_vars => ?_⟩
  rw [Finset.mem_image]
  use (ρ.negVariable v).get <| by aesop
  aesop (add safe unfold Literal.eval)

#lint
