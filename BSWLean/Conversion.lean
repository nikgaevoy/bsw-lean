import BSWLean.CNF

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


@[simp]
lemma Assignment.negVariable_inj {vars} {ρ : Assignment vars} {x₁ x₂ : Variable} {y : Literal vars}
    (h_y_in_mp_x1 : y ∈ ρ.negVariable x₁) (h_y_in_mp_x2 : y ∈ ρ.negVariable x₂) : x₁ = x₂ := by
  unfold Assignment.negVariable at h_y_in_mp_x1 h_y_in_mp_x2
  simp_all only [Option.mem_def, Option.dite_none_right_eq_some]
  obtain ⟨h_x1_in_vars, h_y_eq_lit1⟩ := h_y_in_mp_x1
  obtain ⟨h_x2_in_vars, h_y_eq_lit2⟩ := h_y_in_mp_x2
  unfold Variable.toLiteral Variable.toNegLiteral at h_y_eq_lit1 h_y_eq_lit2
  aesop

@[simp]
lemma Assignment.negVariable_some_iff_variable_in_vars {vars} {ρ : Assignment vars} {v} :
    (ρ.negVariable v).isSome ↔ v ∈ vars := by
  unfold Assignment.negVariable

  aesop

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
    simp only [Literal.variable_mem_vars, true_and]
    unfold Assignment.negVariable Literal.variable
    unfold Literal.eval at h_l_in_toClause
    aesop
  case mp =>
    intro h
    obtain ⟨v, ⟨h_v_in_vars, h_l_eval_ρ_false⟩⟩ := h
    unfold Assignment.negVariable Variable.toLiteral Variable.toNegLiteral at h_l_eval_ρ_false
    unfold Literal.eval
    aesop

@[simp]
lemma Assignment.toClause_eval {vars} (ρ : Assignment vars) : ρ.toClause.eval ρ = false := by
  unfold Assignment.toClause
  rw [Clause.eval_eq_false_iff_all_falsified_literals]
  intro l
  unfold Assignment.negVariable
  simp only [Finset.mem_filterMap, Option.dite_none_right_eq_some, and_exists_self,
    forall_exists_index]
  intro v h_v_mem_vars h_l_eq_lit
  unfold Literal.eval
  unfold Variable.toLiteral Variable.toNegLiteral at h_l_eq_lit

  aesop

@[simp]
lemma Assignment.toClause_variables {vars} (ρ : Assignment vars) : ρ.toClause.variables = vars := by
  unfold Clause.variables
  ext v
  constructor
  case mpr =>
    intro h_v_in_vars
    simp only [Finset.mem_image]
    let l := ρ.negVariable v
    have h_l_some : l.isSome := by
      rw [@negVariable_some_iff_variable_in_vars]
      assumption
    let l_some := l.get h_l_some
    use l_some

    constructor
    · rw [@in_toClause]
      simp_all only [Literal.variable_mem_vars, true_and, l_some, l]
      unfold Assignment.negVariable
      simp_all only [↓reduceDIte]
      split
      next h =>
        unfold Variable.toNegLiteral Literal.eval
        aesop
      next h =>
        aesop

    · unfold l_some l
      aesop

  case mp =>
    intro a
    aesop
