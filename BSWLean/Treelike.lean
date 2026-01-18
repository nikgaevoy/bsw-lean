import BSWLean.CNF
import BSWLean.Substitutions
import BSWLean.Conversion
import BSWLean.SuperCNF

inductive TreeLikeResolution {vars} (φ : CNFFormula vars) : (c : Clause vars) → Type where
  | axiom_clause {c} (h_c_in_φ : c ∈ φ) : TreeLikeResolution φ c
  | resolve {c} (c₁ c₂ : Clause vars) (v : Variable)
      (h_v_mem_vars : v ∈ vars)
      (h_v_not_mem_c : v ∉ c.variables)
      (π₁ : TreeLikeResolution φ c₁)
      (π₂ : TreeLikeResolution φ c₂)
      (h_resolve : (c₁ ⊆ c ∪ { v.toLiteral h_v_mem_vars }) ∧
                   (c₂ ⊆ c ∪ { v.toNegLiteral h_v_mem_vars }))
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
  case resolve c₁ c₂ v h_v_mem_vars h_v_not_mem_c π₁ π₂ h_resolve ih₁ ih₂ =>
    expose_names
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal]
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at ih₁
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at ih₂
    by_cases a v h_v_mem_vars
    case neg h =>
      obtain ⟨l₁, h_l₁_in_c₁, h_l₁_eval_a⟩ := ih₁
      apply Finset.mem_of_subset h_resolve.left at h_l₁_in_c₁
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
      apply Finset.mem_of_subset h_resolve.right at h_l₂_in_c₂
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

lemma CNFFormula.substitute_maintains_unsat {vars} (φ : CNFFormula vars)
    (sub_vars : Variables) (h_subset : sub_vars ⊆ vars) (ρ' : Assignment sub_vars)
    (h_unsat : Unsat φ)
  : Unsat (φ.substitute ρ') := by
  constructor
  intro ρ
  by_contra!
  simp only [ne_eq, Bool.not_eq_false] at this

  let ρ_full : Assignment vars :=
    fun v h_v_mem_vars =>
      if h_v_mem : v ∈ sub_vars then
        ρ' v h_v_mem
      else
        ρ v (by
          refine Finset.mem_sdiff.mpr ?_
          constructor
          · exact h_v_mem_vars
          · exact h_v_mem
        )

  have h_restrict_in : ρ_full.restrict (sub_vars) (by exact h_subset) = ρ' := by
    unfold ρ_full
    unfold Assignment.restrict
    simp only
    simp_all only [↓reduceDIte]

  have h_restrict_out : ρ_full.restrict (vars \ sub_vars) (by exact Finset.sdiff_subset) = ρ := by
    unfold ρ_full
    unfold Assignment.restrict
    simp only
    have : ∀ v ∈ (vars \ sub_vars), v ∉ sub_vars := by
      intro v h_v_mem_vars_sdiff
      simp only [Finset.mem_sdiff] at h_v_mem_vars_sdiff
      exact h_v_mem_vars_sdiff.2
    simp_all only [↓reduceDIte]

  have h_sub : ∀ c : Clause vars, c.eval ρ_full = true ↔
    c.substitute ρ' = none ∨
     ∃ c' : Clause (vars \ sub_vars), c.substitute ρ' = some c' ∧ c'.eval ρ = true := by
    intro c
    let (c_in, c_out) := c.split sub_vars
    have h' : ρ_full.restrict (vars ∩ sub_vars) (by exact
      Finset.inter_subset_left) = ρ'.restrict (vars ∩ sub_vars) (by
        exact Finset.inter_subset_right) := by
      have :vars ∩ sub_vars = sub_vars := by
        exact Finset.inter_eq_right.mpr h_subset
      rw [←h_restrict_in]
      simp only [Assignment.double_restrict]

    rw [Clause.split_correctness c sub_vars ρ_full
    (by exact Finset.inter_subset_left) (by exact Finset.sdiff_subset)]

    simp_all only [Bool.or_eq_true]
    constructor

    case mp =>
      intro h
      by_cases (c.split sub_vars).1.eval (ρ'.restrict (vars ∩ sub_vars) (by exact
        Finset.inter_subset_right)) = true
      case pos h_eval_c_in_true =>
        left
        rw [Clause.substitute_eq_none_iff_eval_subclause_true]
        assumption
      case neg h_eval_c_in_false =>
        right
        use (c.split sub_vars).2
        constructor
        · unfold Clause.substitute
          simp_all only [Bool.false_eq_true, false_or, Bool.not_eq_true, ↓reduceIte]
        · simp only [h_eval_c_in_false] at h
          simp at h
          assumption

    case mpr =>
      intro h
      cases h
      case inl h_c_subst_none =>
        rw [Clause.substitute_eq_none_iff_eval_subclause_true] at h_c_subst_none
        exact Or.symm (Or.inr h_c_subst_none)
      case inr h_exists_c_out =>
        obtain ⟨c_out, h_c_out_eval_ρ⟩ := h_exists_c_out
        right
        unfold Clause.substitute at h_c_out_eval_ρ
        simp_all only [Option.ite_none_left_eq_some, Bool.not_eq_true, Option.some.injEq]


  have h_eval_φ : φ.eval ρ_full = true := by
    rw [CNFFormula.eval_eq_true_iff_all_satisfied_clauses]
    intro c h_c_in_φ
    rw [h_sub c]
    by_cases h_ρ' : c.substitute ρ' = none
    case pos =>
      left
      assumption
    case neg =>
      right
      let c_out := (c.substitute ρ').get (by exact Option.isSome_iff_ne_none.mpr h_ρ')
      use c_out
      constructor
      · simp_all only [Option.some_get, ρ_full, c_out]
      · simp [c_out]
        rw [CNFFormula.eval_eq_true_iff_all_satisfied_clauses] at this
        unfold CNFFormula.substitute at this
        simp_all only [Finset.mem_filterMap, Finset.mem_image, id_eq, exists_eq_right,
          forall_exists_index, and_imp, ρ_full]
        apply this
        on_goal 2 => {
          simp_all only [Option.some_get]
          rfl
        }
        · simp_all only

  have := h_unsat.h_unsat ρ_full
  rw [h_eval_φ] at this
  contradiction


def TreeLikeResolution.size {vars} {φ : CNFFormula vars} :
    ∀ {c : Clause vars}, TreeLikeResolution φ c → Nat
  | _, .axiom_clause _ => 1
  | _, .resolve _ _ _ _ _ π₁ π₂ _ => 1 + size π₁ + size π₂

noncomputable def TreeLikeResolution.unsubstitute_rhs {vars} {sub_vars} {c} {φ : CNFFormula vars}
    (h_subset : sub_vars ⊆ vars) (ρ : Assignment sub_vars)
    (π : TreeLikeResolution (φ.substitute ρ) c) : Clause vars :=
  match π with
  | .axiom_clause h_c_in_φ =>
    let good := fun c' => (c'.substitute ρ) = some c
    have : ∃ c' ∈ φ, good c' := by exact CNFFormula.substitute_preimage φ ρ c h_c_in_φ
    Classical.choose this
  | .resolve c₁ c₂ x h_x_in h_x_out π₁ π₂ h =>
    let c₁' := TreeLikeResolution.unsubstitute_rhs h_subset ρ π₁
    let c₂' := TreeLikeResolution.unsubstitute_rhs h_subset ρ π₂

    have h_x_in_vars : x ∈ vars := by
      apply Finset.sdiff_subset
      trivial

    Clause.resolve c₁' c₂' x h_x_in_vars

lemma finset_right_cup {vars} (x : Clause vars) (y : Clause vars) (z : Clause vars) :
    x ⊆ y → x ∪ z ⊆ y ∪ z := by
    intro h
    exact Finset.union_subset_union h fun ⦃a⦄ a_1 ↦ a_1

lemma TreeLikeResolution.unsubstitute_rhs_variables {vars} {sub_vars} {c} {φ : CNFFormula vars}
    (h_subset : sub_vars ⊆ vars) (ρ : Assignment sub_vars)
    (π : TreeLikeResolution (φ.substitute ρ) c) :
    (TreeLikeResolution.unsubstitute_rhs h_subset ρ π) ⊆
      (Clause.combine c ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
      := by
  let c' := (TreeLikeResolution.unsubstitute_rhs h_subset ρ π)
  let rhs := (Clause.combine c ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
  induction π
  case axiom_clause c h_c_in_φ =>
    suffices h : c' ⊆ rhs by aesop

    let good := fun cl => cl ∈ φ ∧ (Clause.substitute cl ρ) = some c
    have h_c'_good : good c' := by
      unfold c'
      unfold TreeLikeResolution.unsubstitute_rhs
      simp only
      apply Classical.choose_spec
    have h_sub := h_c'_good.right
    have h_c'_substitute_isSome : (c'.substitute ρ).isSome := by aesop
    have := Clause.substitute_combine c' ρ h_subset h_c'_substitute_isSome
    aesop
  case resolve c c₁ c₂ x h_x_in h_x_out π₁ π₂ h h_π₁ h_π₂ =>
    unfold unsubstitute_rhs
    unfold Clause.resolve
    simp_all only
    refine Finset.union_subset_iff.mpr ?_
    constructor
    · rw [← @Finset.subset_insert_iff]
      let c_π₁ := (c₁.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
      trans c_π₁
      · trivial
      · unfold c_π₁
        apply Clause.convert_trivial_subset_insert
        unfold Clause.combine
        simp only
        rw [←Finset.insert_union]
        apply finset_right_cup
        let h' := h.left
        apply Clause.convert_maintains_subset_insert
        · unfold Variable.toLiteral
          unfold Literal.convert
          unfold Variable.toLiteral at h'
          simp_all only
          suffices q : insert (Literal.pos x h_x_in) c = c ∪ {Literal.pos x h_x_in} by
            rw [q]
            assumption
          aesop
    · rw [← @Finset.subset_insert_iff]
      let c_π₂ := (c₂.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
      trans c_π₂
      · trivial
      · unfold c_π₂
        apply Clause.convert_trivial_subset_insert
        unfold Clause.combine
        simp only
        rw [←Finset.insert_union]
        apply finset_right_cup
        let h' := h.right
        apply Clause.convert_maintains_subset_insert
        · unfold Variable.toNegLiteral
          unfold Literal.convert
          unfold Variable.toNegLiteral at h'
          simp_all only
          suffices q : insert (Literal.neg x h_x_in) c = c ∪ {Literal.neg x h_x_in} by
            rw [q]
            assumption
          aesop


noncomputable def TreeLikeResolution.unsubstitute {vars} {sub_vars} {c} {φ : CNFFormula vars}
    (h_subset : sub_vars ⊆ vars) (ρ : Assignment sub_vars)
    (π : TreeLikeResolution (φ.substitute ρ) c)
: TreeLikeResolution φ (TreeLikeResolution.unsubstitute_rhs h_subset ρ π) :=
    let c' := (TreeLikeResolution.unsubstitute_rhs h_subset ρ π)

    match h_match : π with
    | .axiom_clause h_c_in_φ =>
      have : c' ∈ φ := by
        let good := fun cl => cl ∈ φ ∧ (Clause.substitute cl ρ) = some c
        suffices q : good c' by
          exact q.left
        unfold c'
        unfold TreeLikeResolution.unsubstitute_rhs
        simp [h_match]
        apply Classical.choose_spec

      TreeLikeResolution.axiom_clause (by aesop)
    | .resolve c₁ c₂ x h_x_in h_x_out π₁ π₂ h =>
      let π₁' := unsubstitute h_subset ρ π₁
      let π₂' := unsubstitute h_subset ρ π₂

      let c₁' := unsubstitute_rhs h_subset ρ π₁
      let c₂' := unsubstitute_rhs h_subset ρ π₂

      have h_in : x ∈ vars := by
        have : vars \ sub_vars ⊆ vars := by aesop
        exact this h_x_in

      have h_out : x ∉ c'.variables := by
        unfold c'
        apply Clause.not_in_variables_subset (unsubstitute_rhs h_subset ρ π)
          ((Clause.combine c ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop))
        · exact unsubstitute_rhs_variables h_subset ρ π
        · have h_not_in_ρ : x ∉ ρ.toClause.variables := by
            rw [Assignment.toClause_variables]
            rw [Finset.mem_sdiff] at h_x_in
            exact h_x_in.right
          have : x ∉ (c.combine ρ.toClause Finset.sdiff_disjoint).variables := by
            apply Clause.combine_not_variables
            · assumption
            · assumption
          rw [←Clause.convert_trivial_keeps_variables]
          assumption

      have : (c₁' ⊆ c' ∪ { x.toLiteral h_in }) ∧
             (c₂' ⊆ c' ∪ { x.toNegLiteral h_in }) := by
        constructor
        · unfold c'
          unfold unsubstitute_rhs
          simp [h_match]
          unfold Clause.resolve
          unfold c₁'
          refine Finset.subset_insert_iff.mpr ?_
          exact Finset.subset_union_left
        · unfold c'
          unfold unsubstitute_rhs
          simp [h_match]
          unfold Clause.resolve
          unfold c₂'
          refine Finset.subset_insert_iff.mpr ?_
          exact Finset.subset_union_right

      TreeLikeResolution.resolve c₁' c₂' x h_in (by aesop) π₁' π₂' (by aesop)


lemma TreeLikeResolution.unsubstitute_size {vars} {sub_vars} {φ : CNFFormula vars}
    (h_subset : sub_vars ⊆ vars) (ρ : Assignment sub_vars) :
    ∀ c' : Clause (vars \ sub_vars),
    ∃ c : Clause vars, c' ∈ (c.substitute ρ) ∧
    ∀ π' : TreeLikeResolution (φ.substitute ρ) c',
    ∃ π : TreeLikeResolution φ c, π.size ≤ π'.size := by
  intro c'
  sorry

theorem unsat_implies_tree_like_refutation {vars} {φ : CNFFormula vars}
    (h_unsat : Unsat φ) : ∃ π : TreeLikeRefutation φ, π.size ≤ 2 * 2 ^ vars.card - 1 := by
    induction vars using Finset.induction_on'
    case empty =>
      have h := h_unsat.h_unsat
      have : BotClause ∈ φ := by
        let a : Assignment ∅ := fun v h_v_mem_vars => by
          exfalso
          exact (List.mem_nil_iff v).mp h_v_mem_vars
        specialize h a
        rw [CNFFormula.eval_eq_false_iff_exists_falsified_clause] at h
        obtain ⟨c, h_c_in_φ, h_c_eval_a_false⟩ := h
        have h_c_eq_bot : c = BotClause := by
          unfold BotClause
          rw [@Finset.eq_empty_iff_forall_notMem]
          intro l h_l_in_c
          cases l
          case pos v h_v_mem_vars =>
            contradiction
          case neg v h_v_mem_vars =>
            contradiction
        rw [←h_c_eq_bot]
        exact h_c_in_φ
      use TreeLikeResolution.axiom_clause this
      simp only [Finset.card_empty, pow_zero]
      unfold TreeLikeResolution.size
      trivial

    case insert v vars' h_v_in_vars h_subset h_v_not_in_vars' ih =>
      let ρ_true : Assignment {v} := (fun _ => fun _ => True)
      let φ_true := φ.substitute ρ_true
      let ρ_false : Assignment {v} := (fun _ => fun _ => False)
      let φ_false := φ.substitute ρ_false

      have h_vars' : (insert v vars') \ {v} = vars' := by
        rw [@Finset.sdiff_singleton_eq_erase]
        rw [Finset.erase_insert h_v_not_in_vars']

      have h_unsat_true : Unsat φ_true := by
        refine CNFFormula.substitute_maintains_unsat φ {v} ?_ (fun x x_1 ↦ decide True) h_unsat
        exact Finset.union_subset_left fun ⦃a⦄ a_1 ↦ a_1

      have h_unsat_false : Unsat φ_false := by
        refine CNFFormula.substitute_maintains_unsat φ {v} ?_ (fun x x_1 ↦ decide False) h_unsat
        exact Finset.union_subset_left fun ⦃a⦄ a_1 ↦ a_1

      rw [←h_vars'] at ih

      obtain ⟨π_true, h_size_π_true⟩ := ih h_unsat_true
      obtain ⟨π_false, h_size_π_false⟩ := ih h_unsat_false

      sorry
