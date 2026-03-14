import BSWLean.CNF

/-!
# Conversion of assignments into clauses

The negation of assignment is a clause.

This file provides all necessary definitions to make this conversion.
-/

/-- Takes assignment `ρ`, variable `v` and produce a literal contradicting `ρ`, if `v` happens
to be in the preimage of `ρ`. -/
def Assignment.negVariable {vars} (ρ : Assignment vars) (v : Variable) : Option (Literal vars) :=
  if h_v_mem_vars : v ∈ vars then
    if ρ v h_v_mem_vars then
      some (Variable.toNegLiteral v h_v_mem_vars)
    else
      some (Variable.toLiteral v h_v_mem_vars)
  else
    none

@[aesop unsafe]
lemma Assignment.negVariable_variable {vars} {ρ : Assignment vars} {v : Variable}
    {y : Literal vars} (h : y ∈ Assignment.negVariable ρ v) : y.variable = v := by
  unfold Assignment.negVariable at h
  aesop

@[aesop unsafe]
lemma Assignment.negVariable_inj {vars} {ρ : Assignment vars} {x₁ x₂ : Variable} {y : Literal vars}
    (h_y_in_mp_x1 : y ∈ ρ.negVariable x₁) (h_y_in_mp_x2 : y ∈ ρ.negVariable x₂) : x₁ = x₂ := by
  grind [Assignment.negVariable, Variable.toLiteral, Variable.toNegLiteral]

@[simp]
lemma Assignment.negVariable_some_iff_variable_in_vars {vars} {ρ : Assignment vars} {v} :
    (ρ.negVariable v).isSome ↔ v ∈ vars := by
  grind [Assignment.negVariable]

/-- The assignment to clause conversion function. -/
def Assignment.toClause {vars} (ρ : Assignment vars) : Clause vars :=
  vars.filterMap (ρ.negVariable) (by exact fun a a' b a_1 a_2 ↦ negVariable_inj a_1 a_2)

@[simp]
lemma Assignment.in_toClause {vars} (ρ : Assignment vars) (l : Literal vars) :
    l ∈ ρ.toClause ↔ (l.variable ∈ vars ∧ l.eval ρ = false) := by
  unfold Assignment.toClause
  simp only [Finset.mem_filterMap, Literal.variable_mem_vars, true_and]
  constructor
  case mpr =>
    intro h_l_in_toClause
    use l.variable
    unfold Assignment.negVariable Literal.variable
    unfold Literal.eval at h_l_in_toClause
    aesop
  case mp =>
    grind [Assignment.negVariable, Variable.toLiteral, Variable.toNegLiteral, Literal.eval]

@[simp]
lemma Assignment.toClause_eval {vars} (ρ : Assignment vars) : ρ.toClause.eval ρ = false := by
  grind [Assignment.toClause, Clause.eval_eq_false_iff_all_falsified_literals,
  Assignment.negVariable, Literal.eval, Variable.toLiteral, Variable.toNegLiteral]

@[simp]
lemma Assignment.toClause_variables {vars} (ρ : Assignment vars) : ρ.toClause.variables = vars := by
  unfold Clause.variables
  ext v
  refine ⟨fun a => by aesop, fun h_v_in_vars => ?_⟩
  rw [Finset.mem_image]
  use (ρ.negVariable v).get <| by rwa [negVariable_some_iff_variable_in_vars]
  constructor
  · rw [in_toClause]
    constructor
    · simp [Literal.variable_mem_vars]
    · grind [Assignment.negVariable, Variable.toLiteral, Variable.toNegLiteral, Literal.eval]
  · aesop

#lint
