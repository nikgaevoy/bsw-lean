import BSWLean.CNF
import BSWLean.Substitutions
import BSWLean.Conversion
import BSWLean.SuperCNF

/-!
# Tree-Like Resolution

This file defines the tree-like Resolution proof system and proves it soundness and completeness.

## Implementation notes

The proof system is defined as an inductive type with two options (without an explicit weakening
rule), but the resolution rule admits weakening inside.

The interesting moment is unavoidable noncomputability of function `unsubstitute`. See the comment
near the function for more details.
-/

/-- Tree-like Resolution proof system. Defines `φ ⊢ c`. -/
inductive TreeLikeResolution {vars} (φ : CNFFormula vars) : (c : Clause vars) → Type where
  /-- A clause that is present in the formula. -/
  | axiom_clause {c} (h_c_in_φ : c ∈ φ) : TreeLikeResolution φ c

  /-- Resolution step. -/
  | resolve {c} (c₁ c₂ : Clause vars) (v : Variable)
      (h_v_mem_vars : v ∈ vars)
      (h_v_not_mem_c : v ∉ c.variables)
      (π₁ : TreeLikeResolution φ c₁)
      (π₂ : TreeLikeResolution φ c₂)
      (h_resolve : (c₁ ⊆ c ∪ { v.toLiteral h_v_mem_vars true }) ∧
                   (c₂ ⊆ c ∪ { v.toLiteral h_v_mem_vars false }))
      : TreeLikeResolution φ c

/-- Empty clause. -/
abbrev BotClause (vars : Variables) : Clause vars := ∅

/-- Defines a proof in tree-like Resolution. -/
abbrev TreeLikeRefutation {vars} (φ : CNFFormula vars) :=
  TreeLikeResolution φ (BotClause vars)

/-- Unsatisfiable formula defined as a formula that cannot be satisfied. -/
@[aesop safe [constructors, cases]]
class Unsat {vars} (f : CNFFormula vars) : Prop where
  h_unsat : ∀ a, f.eval a = false

@[simp]
lemma BotClause.variables_is_empty (vars : Variables) : (BotClause vars).variables = ∅ := by aesop

--lemma evaluation_is_correct

lemma tree_like_proof_is_correct {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) (ρ : Assignment vars) (h_φ_eval_a : φ.eval ρ) : c.eval ρ := by
  rw [CNFFormula.eval_eq_true_iff_all_satisfied_clauses] at h_φ_eval_a
  induction π
  case axiom_clause c h_c_in_φ => exact h_φ_eval_a c h_c_in_φ
  case resolve c c₁ c₂ v h_v_mem_vars h_v_not_mem_c π₁ π₂ h_resolve ih₁ ih₂ =>
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal]
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at ih₁ ih₂
    by_cases ρ v h_v_mem_vars
    case neg h =>
      obtain ⟨l₁, h_l₁_in_c₁, h_l₁_eval_a⟩ := ih₁
      apply Finset.mem_of_subset h_resolve.left at h_l₁_in_c₁
      use l₁
      simp only [h_l₁_eval_a, and_true]
      contrapose! h_l₁_in_c₁
      simp only [Finset.union_singleton, Finset.mem_insert, h_l₁_in_c₁, or_false]
      suffices l₁.eval ρ ≠ (v.toLiteral h_v_mem_vars true).eval ρ by
        contrapose! this
        simp only [this]
      aesop (add safe unfold Literal.eval)
    case pos h =>
      obtain ⟨l₂, h_l₂_in_c₂, h_l₂_eval_a⟩ := ih₂
      apply Finset.mem_of_subset h_resolve.right at h_l₂_in_c₂
      use l₂
      simp only [h_l₂_eval_a, and_true]
      contrapose! h_l₂_in_c₂
      simp only [Finset.union_singleton, Finset.mem_insert, h_l₂_in_c₂, or_false]
      suffices l₂.eval ρ ≠ (v.toLiteral h_v_mem_vars false).eval ρ by
        contrapose! this
        simp only [this]
      aesop (add safe unfold Literal.eval)

/-- Tree-like Resolution is sound. -/
theorem tree_like_refutation_implies_unsat {vars} {φ : CNFFormula vars}
    (π : TreeLikeRefutation φ) : Unsat φ := by
  unfold TreeLikeRefutation at π
  apply tree_like_proof_is_correct at π
  have : ∀ a : Assignment vars, (BotClause vars).eval a = false := by
    unfold Clause.eval BotClause
    exact fun a ↦ rfl
  constructor
  aesop

lemma CNFFormula.substitute_maintains_unsat {vars sub_vars} {φ : CNFFormula vars}
    (h_subset : sub_vars ⊆ vars) (ρ' : Assignment sub_vars) (h_unsat : Unsat φ) :
    Unsat (φ.substitute ρ') := by
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
    unfold ρ_full Assignment.restrict
    simp_all

  have h_restrict_out : ρ_full.restrict (vars \ sub_vars) (by exact Finset.sdiff_subset) = ρ := by
    unfold ρ_full Assignment.restrict
    simp only
    have : ∀ v ∈ (vars \ sub_vars), v ∉ sub_vars := by aesop
    simp_all only [↓reduceDIte]

  have h_sub : ∀ c : Clause vars, c.eval ρ_full = true ↔
      c.substitute ρ' = none ∨
      ∃ c' : Clause (vars \ sub_vars), c.substitute ρ' = some c' ∧ c'.eval ρ = true := by
    intro c
    let (c_in, c_out) := c.split sub_vars
    have h' : ρ_full.restrict (vars ∩ sub_vars) Finset.inter_subset_left =
              ρ'.restrict (vars ∩ sub_vars) Finset.inter_subset_right := by
      simp [←h_restrict_in]

    rw [Clause.split_correctness c sub_vars ρ_full]

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
        aesop (add safe unfold Clause.substitute)

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
        simp_all

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
      aesop (add simp CNFFormula.eval_eq_true_iff_all_satisfied_clauses)

  aesop (add safe cases Unsat)

/-- Size of the proof. -/
def TreeLikeResolution.size {vars} {φ : CNFFormula vars} :
    ∀ {c : Clause vars}, TreeLikeResolution φ c → Nat
  | _, .axiom_clause _ => 1
  | _, .resolve _ _ _ _ _ π₁ π₂ _ => 1 + size π₁ + size π₂

/-- Width of the proof. -/
def TreeLikeResolution.width {vars} {φ : CNFFormula vars} :
    ∀ {c : Clause vars}, TreeLikeResolution φ c → Nat
  | c, .axiom_clause _ => c.card
  | c, .resolve _ _ _ _ _ π₁ π₂ _ => max c.card (max (width π₁) (width π₂))

/-- Defines the right-hand-side of `TreeLikeResolution.unsubstitute`. -/
noncomputable def TreeLikeResolution.unsubstitute_rhs {vars sub_vars} {c} {φ : CNFFormula vars}
    (ρ : Assignment sub_vars) (π : TreeLikeResolution (φ.substitute ρ) c) : Clause vars :=
  match π with
  | .axiom_clause h_c_in_φ =>
    let good := fun c' => (c'.substitute ρ) = some c
    have : ∃ c' ∈ φ, good c' := by exact CNFFormula.substitute_preimage h_c_in_φ
    Classical.choose this
  | .resolve c₁ c₂ x h_x_in h_x_out π₁ π₂ h =>
    let c₁' := π₁.unsubstitute_rhs ρ
    let c₂' := π₂.unsubstitute_rhs ρ

    have h_x_in_vars : x ∈ vars := by
      apply Finset.sdiff_subset
      trivial

    Clause.resolve c₁' c₂' x h_x_in_vars

/-- Technical rewrite lemma. Used once. -/
lemma finset_right_cup {vars} (x : Clause vars) (y : Clause vars) (z : Clause vars) :
    x ⊆ y → x ∪ z ⊆ y ∪ z := by
  intro h
  exact Finset.union_subset_union h fun ⦃a⦄ a_1 ↦ a_1

lemma TreeLikeResolution.unsubstitute_rhs_variables {vars sub_vars} {c} {φ : CNFFormula vars}
    (ρ : Assignment sub_vars) (π : TreeLikeResolution (φ.substitute ρ) c)
    (h_subset : sub_vars ⊆ vars) :
    (π.unsubstitute_rhs ρ) ⊆
      (Clause.combine c ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
      := by
  let c' := π.unsubstitute_rhs ρ
  let rhs := (Clause.combine c ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
  induction π
  case axiom_clause c h_c_in_φ =>
    suffices h : c' ⊆ rhs by aesop
    let good := fun cl => cl ∈ φ ∧ (Clause.substitute cl ρ) = some c
    have h_c'_good : good c' := by
      unfold c' TreeLikeResolution.unsubstitute_rhs
      simp only
      apply Classical.choose_spec
    have h_sub := h_c'_good.right
    have h_c'_substitute_isSome : (c'.substitute ρ).isSome := by aesop
    have := Clause.substitute_combine c' ρ h_subset h_c'_substitute_isSome
    aesop
  case resolve c c₁ c₂ x h_x_in h_x_out π₁ π₂ h h_π₁ h_π₂ =>
    unfold unsubstitute_rhs Clause.resolve
    simp_all only
    refine Finset.union_subset_iff.mpr ?_
    constructor
    · rw [← @Finset.subset_insert_iff]
      let c_π₁ := (c₁.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
      trans c_π₁
      · trivial
      unfold c_π₁
      apply Clause.convert_trivial_subset_insert
      unfold Clause.combine
      simp only
      rw [←Finset.insert_union]
      apply finset_right_cup
      have h' := h.left
      apply Clause.convert_maintains_subset_insert
      all_goals grind [Literal.variable, Variable.toLiteral, Literal.convert]
    · rw [← @Finset.subset_insert_iff]
      let c_π₂ := (c₂.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
      trans c_π₂
      · trivial
      unfold c_π₂
      apply Clause.convert_trivial_subset_insert
      unfold Clause.combine
      simp only
      rw [←Finset.insert_union]
      apply finset_right_cup
      let h' := h.right
      apply Clause.convert_maintains_subset_insert
      all_goals grind [Literal.variable, Variable.toLiteral, Literal.convert]

/-- Transforms `φ.substitute ρ ⊢ c` into `φ ⊢ c ∨ ¬ρ`. Has to be noncomputable, because in the
general setting, we need the axiom of choice to recover a clause in the axiom clause case.
Making this function computable requires adding some structure to Variables (like total ordering),
which we want to avoid. -/
noncomputable def TreeLikeResolution.unsubstitute {vars} {sub_vars} {c} {φ : CNFFormula vars}
    (ρ : Assignment sub_vars) (π : TreeLikeResolution (φ.substitute ρ) c)
    (h_subset : sub_vars ⊆ vars) : TreeLikeResolution φ (π.unsubstitute_rhs ρ) :=
    let c' := π.unsubstitute_rhs ρ

    match h_match : π with
    | .axiom_clause h_c_in_φ =>
      have : c' ∈ φ := by
        let good := fun cl => cl ∈ φ ∧ (Clause.substitute cl ρ) = some c
        suffices q : good c' by exact q.left
        unfold c' TreeLikeResolution.unsubstitute_rhs
        simp [h_match]
        apply Classical.choose_spec

      TreeLikeResolution.axiom_clause (by aesop)
    | .resolve c₁ c₂ x h_x_in h_x_out π₁ π₂ h =>
      let π₁' := π₁.unsubstitute ρ h_subset
      let π₂' := π₂.unsubstitute ρ h_subset

      let c₁' := π₁.unsubstitute_rhs ρ
      let c₂' := π₂.unsubstitute_rhs ρ

      have h_in : x ∈ vars := by
        have : vars \ sub_vars ⊆ vars := by aesop
        exact this h_x_in

      have h_out : x ∉ c'.variables := by
        unfold c'
        apply Clause.not_in_variables_subset (π.unsubstitute_rhs_variables ρ h_subset)
        have h_not_in_ρ : x ∉ ρ.toClause.variables := by
          rw [Finset.mem_sdiff] at h_x_in
          aesop
        aesop

      have : (c₁' ⊆ c' ∪ { x.toLiteral h_in true }) ∧
             (c₂' ⊆ c' ∪ { x.toLiteral h_in false }) := by
        constructor
        · unfold c' unsubstitute_rhs
          simp [h_match]
          unfold c₁' Clause.resolve
          refine Finset.subset_insert_iff.mpr ?_
          exact Finset.subset_union_left
        · unfold c' unsubstitute_rhs
          simp [h_match]
          unfold c₂' Clause.resolve
          refine Finset.subset_insert_iff.mpr ?_
          exact Finset.subset_union_right

      TreeLikeResolution.resolve c₁' c₂' x h_in (by aesop) π₁' π₂' (by aesop)


lemma TreeLikeResolution.unsubstitute_size {vars sub_vars} {φ : CNFFormula vars}
    (ρ : Assignment sub_vars) {c : Clause (vars \ sub_vars)}
    (π : TreeLikeResolution (φ.substitute ρ) c) (h_subset : sub_vars ⊆ vars) :
    (π.unsubstitute ρ h_subset).size ≤ π.size := by
  induction π
  case axiom_clause =>
    aesop
  case resolve =>
    unfold unsubstitute size
    linarith

/-- Trivial conversion function, similar to `Clause.convert_trivial`. -/
def TreeLikeResolution.convert {vars} {φ : CNFFormula vars} {c c' : Clause vars}
    (π : TreeLikeResolution φ c) (h : c = c') : TreeLikeResolution φ c' :=
  match h_match : π with
  | .axiom_clause h =>
    TreeLikeResolution.axiom_clause (by aesop)
  | .resolve c₁ c₂ x h_x_in h_x_out π₁ π₂ h =>
    TreeLikeResolution.resolve c₁ c₂ x (by aesop) (by aesop) π₁ π₂ (by aesop)

lemma TreeLikeResolution.convert_size {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) (c' : Clause vars) (h : c = c') :
    (π.convert h).size = π.size := by aesop (add safe unfold TreeLikeResolution.convert)

lemma right_cancel {x y : ℕ} (z : ℕ) : x ≤ y ↔ x + z ≤ y + z := by omega

lemma left_cancel_one {x y : ℕ} : y ≥ 1 → x ≤ y - 1 → 1 + x ≤ 1 + y - 1 := by omega

lemma empty_cnf_contains_bot {φ : CNFFormula ∅} (h : ∀ (a : Assignment ∅), φ.eval a = false) :
   (BotClause ∅) ∈ φ := by
  let a : Assignment ∅ := fun v h_v_mem_vars => by
      exfalso
      exact (List.mem_nil_iff v).mp h_v_mem_vars
  specialize h a
  rw [CNFFormula.eval_eq_false_iff_exists_falsified_clause] at h
  obtain ⟨c, h_c_in_φ, h_c_eval_a_false⟩ := h
  have h_c_eq_bot : c = BotClause ∅ := by grind
  grind

/-- Tree-like Resolution is complete. -/
theorem unsat_implies_tree_like_refutation {vars} {φ : CNFFormula vars}
    (h_unsat : Unsat φ) : ∃ π : TreeLikeRefutation φ, π.size ≤ 2 * 2 ^ vars.card - 1 := by
  induction vars using Finset.induction_on'
  case empty =>
    have h := h_unsat.h_unsat
    have : (BotClause ∅) ∈ φ := by
      exact empty_cnf_contains_bot h
    use TreeLikeResolution.axiom_clause this
    grind [TreeLikeResolution.size]

  case insert v vars' h_v_in_vars h_subset h_v_not_in_vars' ih =>
    let ρ_true : Assignment {v} := (fun _ => fun _ => True)
    let φ_true := φ.substitute ρ_true
    let ρ_false : Assignment {v} := (fun _ => fun _ => False)
    let φ_false := φ.substitute ρ_false

    have h_vars' : (insert v vars') \ {v} = vars' := by
      rw [@Finset.sdiff_singleton_eq_erase]
      rw [Finset.erase_insert h_v_not_in_vars']

    have h_unsat_true : Unsat φ_true := by
      grind [Finset.union_subset_left, CNFFormula.substitute_maintains_unsat]
    have h_unsat_false : Unsat φ_false := by
      grind [Finset.union_subset_left, CNFFormula.substitute_maintains_unsat]

    rw [←h_vars'] at ih
    clear h_vars'

    obtain ⟨π_true, h_size_π_true⟩ := ih h_unsat_true
    obtain ⟨π_false, h_size_π_false⟩ := ih h_unsat_false

    -- to speed up aesop
    clear ih

    let π_true_lifted := π_true.unsubstitute ρ_true (by aesop)
    let π_false_lifted := π_false.unsubstitute ρ_false (by aesop)

    let also_vars := insert v vars'

    have h_size_π_true_lifted : π_true_lifted.size ≤ 2^also_vars.card - 1 := by
      grind [TreeLikeResolution.unsubstitute_size]
    have h_size_π_false_lifted : π_false_lifted.size ≤ 2^also_vars.card - 1 := by
      grind [TreeLikeResolution.unsubstitute_size]

    let c_true := π_true.unsubstitute_rhs ρ_true
    let c_false := π_false.unsubstitute_rhs ρ_false

    have h_convert : (Finset.disjUnion (insert v vars' \ {v}) {v} (Finset.sdiff_disjoint)) =
        also_vars := by grind
    have : vars' ⊆ also_vars := by exact Finset.subset_insert v vars'

    let v_pos : Clause also_vars := {Variable.toLiteral v (Finset.mem_insert_self v vars') true}
    let v_neg : Clause also_vars := {Variable.toLiteral v (Finset.mem_insert_self v vars') false}

    have ρ_true_clause : ρ_true.toClause.convert also_vars (by aesop) = v_neg := by
      exact trivial_subs_unfold (v.toLiteral (by aesop) true) true ρ_true (by rfl) (by aesop)
    have ρ_false_clause : ρ_false.toClause.convert also_vars (by aesop) = v_pos := by
      exact trivial_subs_unfold (v.toLiteral (by aesop) true) false ρ_false (by rfl) (by aesop)

    have h_c_true : c_true ⊆ v_neg := by
      unfold c_true
      have h := π_true.unsubstitute_rhs_variables ρ_true
          (by exact Finset.union_subset_left fun ⦃a⦄ a_1 ↦ a_1)
      let mid := ((BotClause (insert v vars' \ {v})).combine ρ_true.toClause
        Finset.sdiff_disjoint).convert_trivial also_vars h_convert
      trans mid
      all_goals aesop

    have h_c_false : c_false ⊆ v_pos := by
      unfold c_false
      have h := π_false.unsubstitute_rhs_variables ρ_false
        (by exact Finset.union_subset_left fun ⦃a⦄ a_1 ↦ a_1)
      let mid := ((BotClause (insert v vars' \ {v})).combine ρ_false.toClause
        Finset.sdiff_disjoint).convert_trivial also_vars h_convert
      trans mid
      all_goals aesop

    have h_card_inequality : 2 ^ also_vars.card - 1 ≤ 2 * 2 ^ (insert v vars').card - 1 := by grind

    by_cases h_true_empty : c_true = ∅
    case pos =>
      use π_true_lifted.convert h_true_empty
      grind [TreeLikeResolution.convert_size]
    case neg =>
      by_cases h_false_empty : c_false = ∅
      case pos =>
        use π_false_lifted.convert h_false_empty
        grind [TreeLikeResolution.convert_size]
      case neg =>
        use TreeLikeResolution.resolve
          c_false c_true v (Finset.mem_insert_self v vars')
          (by exact Disjoint.notMem_of_mem_left_finset (fun ⦃x⦄ a a_1 ↦ a_1) h_v_in_vars)
          π_false_lifted π_true_lifted <| by aesop
        clear h_unsat_true h_unsat_false ρ_false_clause ρ_true_clause
        grind [TreeLikeResolution.size, Nat.one_le_two_pow]

#lint
