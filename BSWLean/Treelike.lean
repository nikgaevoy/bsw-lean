import BSWLean.CNF

inductive TreeLikeResolution {vars} (φ : CNFFormula vars) : (c : Clause vars) → Type where
  | axiom_clause {c} (h_c_in_φ : c ∈ φ) : TreeLikeResolution φ c
  | weakening {c} (c' : Clause vars) (h_c'_subset_c : c' ⊆ c) (π' : TreeLikeResolution φ c')
      : TreeLikeResolution φ c
  | resolve {c} (c₁ c₂ : Clause vars) (v : Variable)
      (h_v_mem_vars : v ∈ vars)
      (h_v_not_mem_c : v ∉ c.variables)
      (π₁ : TreeLikeResolution φ c₁)
      (π₂ : TreeLikeResolution φ c₂)
      (h_resolve : (c ∪ { v.toLiteral h_v_mem_vars } = c₁) ∧
                   (c ∪ { v.toNegLiteral h_v_mem_vars } = c₂))
      : TreeLikeResolution φ c

abbrev BotClause {vars} : Clause vars := ∅
abbrev TreeLikeRefutation {vars} (φ : CNFFormula vars) :=
  TreeLikeResolution φ BotClause

class Unsat {vars} (f : CNFFormula vars) : Prop where
  h_unsat : ∀ a, f.eval a = false

lemma tree_like_proof_is_correct {vars} {φ : CNFFormula vars} (c : Clause vars)
    (π : TreeLikeResolution φ c) : ∀ a, φ.eval a → c.eval a := by
  intro a h_φ_eval_a
  rw [CNFFormula.eval_eq_true_iff_all_satisfied_clauses] at h_φ_eval_a
  induction π
  case axiom_clause h_c_in_φ =>
    (expose_names; exact h_φ_eval_a c_1 h_c_in_φ)
  case weakening c' h_c'_subset_c π' ih =>
    expose_names
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal]
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at ih
    obtain ⟨l, h_l_in_c', h_l_eval_a⟩ := ih
    use l
    constructor
    · exact h_c'_subset_c h_l_in_c'
    · exact h_l_eval_a
  case resolve c₁ c₂ v h_v_mem_vars h_v_not_mem_c π₁ π₂ h_resolve ih₁ ih₂ =>
    expose_names
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal]
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at ih₁
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at ih₂
    by_cases a v h_v_mem_vars
    case neg h =>
      obtain ⟨l₁, h_l₁_in_c₁, h_l₁_eval_a⟩ := ih₁
      rw [←h_resolve.left] at h_l₁_in_c₁
      use l₁
      simp only [h_l₁_eval_a, and_true]
      contrapose! h_l₁_in_c₁
      simp only [Finset.union_singleton, Finset.mem_insert, h_l₁_in_c₁, or_false]
      suffices l₁.eval a ≠ (v.toLiteral h_v_mem_vars).eval a by
        contrapose! this
        simp only [this]
      rw [h_l₁_eval_a]
      unfold Literal.eval
      unfold Variable.toLiteral
      simp only [ne_eq, Bool.true_eq, Bool.not_eq_true]
      exact eq_false_of_ne_true h
    case pos h =>
      obtain ⟨l₂, h_l₂_in_c₂, h_l₂_eval_a⟩ := ih₂
      rw [←h_resolve.right] at h_l₂_in_c₂
      use l₂
      simp only [h_l₂_eval_a, and_true]
      contrapose! h_l₂_in_c₂
      simp only [Finset.union_singleton, Finset.mem_insert, h_l₂_in_c₂, or_false]
      suffices l₂.eval a ≠ (v.toNegLiteral h_v_mem_vars).eval a by
        contrapose! this
        simp only [this]
      rw [h_l₂_eval_a]
      unfold Literal.eval
      unfold Variable.toNegLiteral
      simp only [ne_eq, Bool.true_eq, Bool.not_eq_true]
      exact Bool.not_eq_eq_eq_not.mpr h


theorem tree_like_refutation_implies_unsat {vars} {φ : CNFFormula vars}
    (π : TreeLikeRefutation φ) : Unsat φ := by
  unfold TreeLikeRefutation at π
  apply tree_like_proof_is_correct at π
  have : ∀ a : Assignment vars, BotClause.eval a = false := by
    unfold Clause.eval
    unfold BotClause
    exact fun a ↦ rfl
  constructor
  intro a
  by_contra! h
  simp only [ne_eq, Bool.not_eq_false] at h
  apply π a at h
  contradiction
