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

lemma tree_like_proof_is_correct {vars} {φ : CNFFormula vars} (c : Clause vars) (h_c_in_φ : c ∈ φ)
    (π : TreeLikeResolution φ c) : ∀ a, φ.eval a → c.eval a := by
  intro a h_φ_eval_a
  rw [CNFFormula.eval_eq_true_iff_all_satisfied_clauses] at h_φ_eval_a
  sorry
