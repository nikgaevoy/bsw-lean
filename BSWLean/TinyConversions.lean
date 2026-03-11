import BSWLean.Treelike

def is_resolve {vars} {φ : CNFFormula vars} {c : Clause vars} :
    TreeLikeResolution φ c → Prop
  | .axiom_clause _ => false
  | .resolve .. => true

def IsRegularRes {vars} {φ : CNFFormula vars} : ∀ {c : Clause vars}, TreeLikeResolution φ c → Prop
  | _, .axiom_clause _ => True
  | _, .resolve c₁ c₂ v _ _ π₁ π₂ _ =>
      v ∈ c₁.variables ∧ v ∈ c₂.variables ∧ IsRegularRes π₁ ∧ IsRegularRes π₂


@[simp]
lemma trivial_convert_card {vars₁ vars₂} {C : Clause vars₁} {h} :
    (C.convert_trivial vars₂ h).card = C.card := by
  refine Set.BijOn.finsetCard_eq ?_ ?_
  · intro lit₁
    subst h
    exact lit₁
  subst h
  simp_all only
  constructor
  · unfold Clause.convert_trivial
    unfold Clause.convert
    simp only [Literal.convert_self, dite_eq_ite, Finset.coe_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq, and_self_left, exists_eq_right,
      SetLike.setOf_mem_eq]
    exact fun ⦃x⦄ a ↦ a
  unfold Clause.convert_trivial
  unfold Clause.convert
  simp
  refine Finset.surjOn_of_injOn_of_card_le (fun lit₁ ↦ lit₁) (fun ⦃x⦄ a ↦ a) ?_ ?_
  · exact Function.Injective.injOn fun ⦃a₁ a₂⦄ a ↦ a
  · exact (Finset.eq_iff_card_ge_of_superset fun ⦃a⦄ a_1 ↦ a_1).mpr rfl

lemma convert_card_ineq {vars₁ vars₂} {C : Clause vars₁} {h}
  : (C.convert vars₂ h).card ≤ C.card := by
  unfold Clause.convert
  exact filterMap_card C

lemma convert_card_ineq_oppsite {vars₁ vars₂} {C : Clause vars₁} {h}
  : (C.convert vars₂ h).card ≥ C.card := by
    have h₂ : ∀ l ∈ (C.convert vars₂ h), l.variable ∈ vars₁ := by
      intro l a
      unfold Clause.convert at a
      simp at a
      obtain ⟨w, h_1⟩ := a
      obtain ⟨w_1, h_1⟩ := h_1
      subst h_1
      simp_all only [Literal.convert_variable, Literal.variable_mem_vars]
    have idea₁ : ((C.convert vars₂ h).convert vars₁ h₂).card ≤ (C.convert vars₂ h).card := by
      exact convert_card_ineq
    simp_all

@[simp]
lemma convert_card {vars₁ vars₂} {C : Clause vars₁} {h} :
    (C.convert vars₂ h).card = C.card := by
  refine Nat.le_antisymm ?_ ?_
  · exact convert_card_ineq
  · exact convert_card_ineq_oppsite



lemma to_clause_card_less_than_sub_vars_card {sub_vars : Variables} (ρ : Assignment sub_vars) :
  (Finset.card ρ.toClause ≤ Finset.card sub_vars) := by
  unfold Assignment.toClause
  exact filterMap_card sub_vars

lemma disjoint_contradiction {α} [DecidableEq α] (s₁ s₂ : Finset α) (h_disj : Disjoint s₁ s₂)
    (h : ∃ x ∈ s₁, x ∈ s₂) : False := by
  rw [Finset.disjoint_iff_inter_eq_empty] at h_disj
  obtain ⟨x, h_x_in_s₁, h_x_in_s₂⟩ := h
  have : x ∈ s₁ ∩ s₂ := by
    simp only [Finset.mem_inter]
    constructor
    · assumption
    · assumption
  rw [h_disj] at this
  contradiction

@[simp]
lemma subset_combine {vars₁ vars₂} (c₁ c₂ : Clause vars₁) (c' : Clause vars₂)
    (h_disj : Disjoint vars₁ vars₂) :
    (Clause.combine c₁ c' h_disj) ⊆ (Clause.combine c₂ c' h_disj) ↔ c₁ ⊆ c₂ := by
  unfold Clause.combine
  simp only
  constructor
  case mpr =>
    intro h_subset
    refine Finset.union_subset_union_left ?_
    aesop
  case mp =>
    intro h_subset
    have : c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ⊆
           c₂.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) := by
      rw [Finset.union_subset_iff] at h_subset
      replace h_subset := h_subset.1
      intro l h_l_in_c₁
      have h_apply_subset : l ∈ c₂.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ∪
                                c'.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) := by
        apply h_subset
        assumption
      simp only [Finset.mem_union] at h_apply_subset
      by_contra!
      simp_all only [false_or]
      have h_l_in_vars₁ : l.variable ∈ vars₁ := by
        have : l.variable ∈
            (c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop)).variables := by
          exact literal_in_clause_variables h_l_in_c₁
        rw [Clause.convert_keeps_variables] at this
        have h₁ : c₁.variables ⊆ vars₁ := by aesop
        aesop
      have h_l_in_vars₂ : l.variable ∈ vars₂ := by
        have : l.variable ∈
            (c'.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop)).variables := by
          exact literal_in_clause_variables (by assumption)
        rw [Clause.convert_keeps_variables] at this
        have h₁ : c'.variables ⊆ vars₂ := by aesop
        aesop
      have : l.variable ∈ vars₁ ∩ vars₂ := by aesop
      unfold Disjoint at h_disj
      apply disjoint_contradiction vars₁ vars₂ h_disj
      use l.variable

    intro l h_l_in_c₁
    have h_l_in_c_convert : l.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ∈
        c₂.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) := by
      apply this
      aesop

    simp_all

lemma resolve_substitute_left {vars sub_vars} (c₁ c₂ : Clause vars) {x : Variable}
    (ρ : Assignment sub_vars) (h_x_in : x ∈ vars) (h₂ : (c₂.substitute ρ).isNone)
    (h_res : ((c₁.resolve c₂ x h_x_in).substitute ρ).isSome) : x ∈ sub_vars := by
  unfold Clause.resolve at h_res
  rw [Clause.substitute_isSome_iff_eval_subclause_false] at h_res
  simp only [Option.isNone_iff_eq_none] at h₂
  rw [Clause.substitute_eq_none_iff_eval_subclause_true] at h₂
  unfold Clause.split Clause.shrink at *
  simp_all only [Finset.mem_filter, Bool.not_eq_true, Finset.mem_union, Finset.mem_erase, ne_eq]
  rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at h₂
  rw [Clause.eval_eq_false_iff_all_falsified_literals] at h_res
  simp_all only [Finset.mem_filterMap, Finset.mem_filter, Option.dite_none_right_eq_some,
    Option.some.injEq, and_exists_self, forall_exists_index, forall_and_index, Finset.mem_union,
    Finset.mem_erase, ne_eq, ↓existsAndEq, true_and]
  obtain ⟨l₂, ⟨⟨h_l₂_in_c₂, h_l₂_var_in_sub_vars⟩, h_l₂_eval⟩⟩ := h₂
  by_contra!
  have h_l₂_var_not_x : l₂.variable ≠ x := by aesop
  have : l₂ ≠ x.toNegLiteral h_x_in := by
    unfold Literal.variable Variable.toNegLiteral at *
    aesop
  have := h_res (l₂.restrict (vars ∩ sub_vars) (by aesop)) l₂
    (by aesop) h_l₂_var_in_sub_vars (by rfl)
  aesop

lemma resolve_substitute_right {vars sub_vars} (c₁ c₂ : Clause vars) {x : Variable}
    (ρ : Assignment sub_vars) (h_x_in : x ∈ vars) (h₁ : (c₁.substitute ρ).isNone)
    (h_res : ((c₁.resolve c₂ x h_x_in).substitute ρ).isSome) : x ∈ sub_vars := by
  unfold Clause.resolve at h_res
  rw [Clause.substitute_isSome_iff_eval_subclause_false] at h_res
  simp only [Option.isNone_iff_eq_none] at h₁
  rw [Clause.substitute_eq_none_iff_eval_subclause_true] at h₁
  unfold Clause.split Clause.shrink at *
  simp_all only [Finset.mem_filter, Bool.not_eq_true, Finset.mem_union, Finset.mem_erase, ne_eq]
  rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at h₁
  rw [Clause.eval_eq_false_iff_all_falsified_literals] at h_res
  simp_all only [Finset.mem_filterMap, Finset.mem_filter, Option.dite_none_right_eq_some,
    Option.some.injEq, and_exists_self, forall_exists_index, forall_and_index, Finset.mem_union,
    Finset.mem_erase, ne_eq, ↓existsAndEq, true_and]
  obtain ⟨l₁, ⟨⟨h_l₁_in_c₁, h_l₁_var_in_sub_vars⟩, h_l₁_eval⟩⟩ := h₁
  by_contra!
  have h_l₁_var_not_x : l₁.variable ≠ x := by aesop
  have : l₁ ≠ x.toLiteral h_x_in := by
    unfold Literal.variable Variable.toLiteral at *
    aesop
  have := h_res (l₁.restrict (vars ∩ sub_vars) (by aesop)) l₁
    (by aesop) h_l₁_var_in_sub_vars (by rfl)
  aesop

def TreeLikeResolution.restrict_rhs {vars₁ vars₂ : Variables} {φ : CNFFormula vars₂}
    {C : Clause vars₂} (π : TreeLikeResolution φ C) (ρ : Assignment vars₁)
    (h_some : (C.substitute ρ).isSome) :
    Clause (vars₂ \ vars₁) :=
  match h : π with
  | .axiom_clause h_in =>
      (C.substitute ρ).get h_some
  | .resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
      have : Clause.resolve c₁ c₂ v h_v_mem ⊆ C := by
        unfold Clause.resolve
        refine Finset.union_subset_iff.mpr ?_
        constructor
        · refine Finset.subset_insert_iff.mp ?_
          aesop
        · refine Finset.subset_insert_iff.mp ?_
          aesop
      have h_resolve_isSome : ((Clause.resolve c₁ c₂ v h_v_mem).substitute ρ).isSome := by aesop
      if h₁ : c₁.substitute ρ = none then
        have : (c₂.substitute ρ).isSome := by
          contrapose! h_resolve_isSome
          simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff] at h_resolve_isSome
          rw [←Option.isNone_iff_eq_none] at h₁
          simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff]
          exact Clause.resolve_substitute_isNone h_v_mem h₁ h_resolve_isSome
        π₂.restrict_rhs ρ this
      else if h₂ : c₂.substitute ρ = none then
        π₁.restrict_rhs ρ (Option.isSome_iff_ne_none.mpr h₁)
      else
        let c₁' := π₁.restrict_rhs ρ (Option.isSome_iff_ne_none.mpr h₁)
        let c₂' := π₂.restrict_rhs ρ (Option.isSome_iff_ne_none.mpr h₂)
        if h_v : v ∈ vars₁ then
          if h_ρ_v : ρ v h_v then
            c₂'
          else
            c₁'
        else
          Clause.resolve c₁' c₂' v (by aesop)

lemma TreeLikeResolution.restrict_rhs_subset_substitute {vars₁ vars₂ : Variables}
    {φ : CNFFormula vars₂} {C : Clause vars₂} (π : TreeLikeResolution φ C) (ρ : Assignment vars₁)
    (h_some : (C.substitute ρ).isSome) :
    π.restrict_rhs ρ h_some ⊆ (C.substitute ρ).get h_some := by
  induction h : π
  case axiom_clause c h_in =>
    unfold TreeLikeResolution.restrict_rhs
    trivial
  case resolve c c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ =>
    have : Clause.resolve c₁ c₂ v h_v_mem ⊆ c := by
      unfold Clause.resolve
      refine Finset.union_subset_iff.mpr ?_
      constructor
      · refine Finset.subset_insert_iff.mp ?_
        aesop
      · refine Finset.subset_insert_iff.mp ?_
        aesop
    have h_resolve_isSome : ((Clause.resolve c₁ c₂ v h_v_mem).substitute ρ).isSome := by aesop
    unfold TreeLikeResolution.restrict_rhs
    simp only [dite_eq_ite]
    by_cases h₁ : c₁.substitute ρ = none
    case pos =>
      simp only [h₁, ↓reduceDIte]
      have h_c₂_isSome : (c₂.substitute ρ).isSome := by
        contrapose! h_resolve_isSome
        simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff] at h_resolve_isSome
        rw [←Option.isNone_iff_eq_none] at h₁
        simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff]
        exact Clause.resolve_substitute_isNone h_v_mem h₁ h_resolve_isSome
      have h_left := ih₂ π₂ h_c₂_isSome (by rfl)
      trans (c₂.substitute ρ).get h_c₂_isSome
      · exact h_left
      have h_x_in_vars₁ : v ∈ vars₁ := by
        apply resolve_substitute_right c₁ c₂ ρ h_v_mem (by aesop) h_resolve_isSome
      trans ((c₁.resolve c₂ v h_v_mem).substitute ρ).get h_resolve_isSome
      swap
      · aesop
      unfold Clause.resolve Clause.substitute Clause.split Clause.shrink
      simp only [Finset.mem_filter, Option.get_ite', Finset.mem_union, Finset.mem_erase, ne_eq]
      intro l h_l
      rw [Finset.mem_filterMap] at h_l
      obtain ⟨l', ⟨h_l'_mem, h_l_eval⟩⟩ := h_l
      rw [Finset.mem_filterMap]
      have h_l'_neq : l' ≠ v.toNegLiteral h_v_mem := by
        unfold Literal.variable Variable.toNegLiteral at *
        aesop
      use l'
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_erase, ne_eq,
        Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self]
      use by aesop
      aesop
    case neg =>
      simp only [h₁, ↓reduceDIte]
      by_cases h₂ : c₂.substitute ρ = none
      case pos =>
        simp only [h₂, ↓reduceDIte]
        have h_c₁_isSome : (c₁.substitute ρ).isSome := by
          contrapose! h_resolve_isSome
          simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff] at h_resolve_isSome
          rw [←Option.isNone_iff_eq_none] at h₂
          simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff]
          exact Clause.resolve_substitute_isNone h_v_mem h_resolve_isSome h₂
        have h_left := ih₁ π₁ h_c₁_isSome (by rfl)
        trans (c₁.substitute ρ).get h_c₁_isSome
        · exact h_left
        have h_x_in_vars₁ : v ∈ vars₁ := by
          apply resolve_substitute_left c₁ c₂ ρ h_v_mem (by aesop) h_resolve_isSome
        trans ((c₁.resolve c₂ v h_v_mem).substitute ρ).get h_resolve_isSome
        swap
        · aesop
        unfold Clause.resolve Clause.substitute Clause.split Clause.shrink
        simp only [Finset.mem_filter, Option.get_ite', Finset.mem_union, Finset.mem_erase, ne_eq]
        intro l h_l
        rw [Finset.mem_filterMap] at h_l
        obtain ⟨l', ⟨h_l'_mem, h_l_eval⟩⟩ := h_l
        rw [Finset.mem_filterMap]
        have h_l'_neq : l' ≠ v.toLiteral h_v_mem := by
          unfold Literal.variable Variable.toLiteral at *
          aesop
        use l'
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_erase, ne_eq,
          Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self]
        use by aesop
        aesop
      case neg =>
        simp only [h₂, ↓reduceDIte]
        let h_some₁ := Option.isSome_iff_ne_none.mpr h₁
        let h_some₂ := Option.isSome_iff_ne_none.mpr h₂
        let c₁' := (c₁.substitute ρ).get h_some₁
        let c₂' := (c₂.substitute ρ).get h_some₂
        have h_left := ih₂ π₂ (Option.isSome_iff_ne_none.mpr h₂) (by rfl)
        have h_right := ih₁ π₁ (Option.isSome_iff_ne_none.mpr h₁) (by rfl)

        by_cases h_v : v ∈ vars₁
        case neg =>
          simp only [h_v, ↓reduceDIte]
          trans ((Clause.resolve c₁ c₂ v h_v_mem).substitute ρ).get h_resolve_isSome
          swap
          · apply Clause.substitute_maintains_subset
            assumption
          have ih₁' : π₁.restrict_rhs ρ h_some₁ ⊆ c₁' := by aesop
          have ih₂' : π₂.restrict_rhs ρ h_some₂ ⊆ c₂' := by aesop
          trans (c₁'.resolve c₂' v (by aesop))
          · apply Clause.resolve_maintains_subset
            · assumption
            · assumption
          unfold c₁' c₂'
          rw [Clause.substitute_resolve_eq_resolve_substitute]
          assumption
        case pos =>
          simp only [h_v, ↓reduceDIte]
          by_cases h_ρ : ρ v h_v
          case pos =>
            simp only [h_ρ, ↓reduceIte]
            trans c₂'
            · assumption
            trans ((c₁.resolve c₂ v h_v_mem).substitute ρ).get h_resolve_isSome
            swap
            · aesop
            unfold Clause.resolve Clause.substitute Clause.split Clause.shrink
            intro l h_l
            unfold c₂' at h_l
            unfold Clause.substitute Clause.split Clause.shrink at h_l
            simp_all only [Finset.mem_filter, Finset.mem_union, Finset.mem_erase, ne_eq,
              Option.get_ite', Finset.mem_filterMap, Option.dite_none_right_eq_some,
              Option.some.injEq, and_exists_self]
            obtain ⟨l', ⟨h_l'_mem, h_l_eval⟩⟩ := h_l
            use l'
            use by
              constructor
              swap
              · exact h_l'_mem.right
              right
              constructor
              · unfold Literal.variable Variable.toNegLiteral at *
                aesop
              · exact h_l'_mem.left
          case neg =>
            simp only [h_ρ, Bool.false_eq_true, ↓reduceIte]
            trans c₁'
            · assumption
            trans ((c₁.resolve c₂ v h_v_mem).substitute ρ).get h_resolve_isSome
            swap
            · aesop
            unfold Clause.resolve Clause.substitute Clause.split Clause.shrink
            intro l h_l
            unfold c₁' at h_l
            unfold Clause.substitute Clause.split Clause.shrink at h_l
            simp_all only [Finset.mem_filter, Finset.mem_union, Finset.mem_erase, ne_eq,
              Option.get_ite', Finset.mem_filterMap, Option.dite_none_right_eq_some,
              Option.some.injEq, and_exists_self]
            obtain ⟨l', ⟨h_l'_mem, h_l_eval⟩⟩ := h_l
            use l'
            use by
              constructor
              swap
              · exact h_l'_mem.right
              left
              constructor
              · unfold Literal.variable Variable.toLiteral at *
                aesop
              · exact h_l'_mem.left

def TreeLikeResolution.convert_trivial {vars} {φ : CNFFormula vars} {c₁ c₂ : Clause vars}
    (π : TreeLikeResolution φ c₁) (h_eq : c₁ = c₂) : TreeLikeResolution φ c₂ :=
  match h : π with
  | .axiom_clause h_in =>
    .axiom_clause (by aesop)
  | .resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
    .resolve c₁ c₂ v h_v_mem (by aesop) π₁ π₂ (by aesop)

def TreeLikeResolution.restrict {vars₁ vars₂ : Variables} {φ : CNFFormula vars₂}
    {C : Clause vars₂} (π : TreeLikeResolution φ C) (ρ : Assignment vars₁)
    (h_some : (C.substitute ρ).isSome) :
    TreeLikeResolution (φ.substitute ρ) (TreeLikeResolution.restrict_rhs π ρ h_some) :=
  match h : π with
  | .axiom_clause h_in =>
    .axiom_clause (by
      unfold TreeLikeResolution.restrict_rhs CNFFormula.substitute
      aesop
    )
  | .resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
    have : Clause.resolve c₁ c₂ v h_v_mem ⊆ C := by
      unfold Clause.resolve
      refine Finset.union_subset_iff.mpr ?_
      constructor
      · refine Finset.subset_insert_iff.mp ?_
        aesop
      · refine Finset.subset_insert_iff.mp ?_
        aesop
    have h_resolve_isSome : ((Clause.resolve c₁ c₂ v h_v_mem).substitute ρ).isSome := by aesop
    if h₁ : c₁.substitute ρ = none then
      have : (c₂.substitute ρ).isSome := by
        contrapose! h_resolve_isSome
        simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff] at h_resolve_isSome
        rw [←Option.isNone_iff_eq_none] at h₁
        simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff]
        exact Clause.resolve_substitute_isNone h_v_mem h₁ h_resolve_isSome
      have h_eq : ((resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res).restrict_rhs ρ h_some) =
          (π₂.restrict_rhs ρ this) := by
        unfold restrict_rhs
        simp only [h₁, ↓reduceDIte]
        subst h
        simp_all only [dite_eq_ite]
        obtain ⟨left, right⟩ := h_res
        split
        next h_in => rfl
        next c₁_1 c₂_1 v_1 h_v_mem_1 h_v_not_1 π₁_1 π₂
          h_res =>
          obtain ⟨left_1, right_1⟩ := h_res
          rfl
      (π₂.restrict ρ this).convert_trivial (by aesop)
    else if h₂ : c₂.substitute ρ = none then
      have : (c₁.substitute ρ).isSome := by
        contrapose! h_resolve_isSome
        simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff] at h_resolve_isSome
        rw [←Option.isNone_iff_eq_none] at h₂
        simp only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff]
        exact Clause.resolve_substitute_isNone h_v_mem h_resolve_isSome h₂
      have h_eq : ((resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res).restrict_rhs ρ h_some) =
          (π₁.restrict_rhs ρ this) := by
        unfold restrict_rhs
        subst h
        simp_all only [↓reduceDIte, dite_eq_ite]
        simp_all only [Finset.union_singleton]
        obtain ⟨left, right⟩ := h_res
        split
        next h_in => rfl
        next c₁_1 c₂_1 v_1 h_v_mem_1 h_v_not_1 π₁ π₂_1
          h_res =>
          obtain ⟨left_1, right_1⟩ := h_res
          rfl

      (π₁.restrict ρ this).convert_trivial (by aesop)
    else
      if h_v : v ∈ vars₁ then
        if h_ρ_v : ρ v h_v then
          (π₂.restrict ρ (Option.isSome_iff_ne_none.mpr h₂)).convert_trivial (by
            unfold TreeLikeResolution.restrict_rhs
            aesop
          )
        else
          (π₁.restrict ρ (Option.isSome_iff_ne_none.mpr h₁)).convert_trivial (by
            unfold TreeLikeResolution.restrict_rhs
            aesop
          )
      else
        let c₁'_rhs := π₁.restrict_rhs ρ (Option.isSome_iff_ne_none.mpr h₁)
        let c₂'_rhs := π₂.restrict_rhs ρ (Option.isSome_iff_ne_none.mpr h₂)
        let c₁' := (c₁.substitute ρ).get (Option.isSome_iff_ne_none.mpr h₁)
        let c₂' := (c₂.substitute ρ).get (Option.isSome_iff_ne_none.mpr h₂)

        have h_π₁ : c₁'_rhs ⊆ c₁' := by
          exact restrict_rhs_subset_substitute π₁ ρ (Option.isSome_iff_ne_none.mpr h₁)
        have h_π₂ : c₂'_rhs ⊆ c₂' := by
          exact restrict_rhs_subset_substitute π₂ ρ (Option.isSome_iff_ne_none.mpr h₂)
        have h_v_notMem_resolve : v ∉
            ((resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res).restrict_rhs ρ h_some).variables := by
          unfold TreeLikeResolution.restrict_rhs
          simp only [h₁, h₂, h_v, ↓reduceDIte]
          unfold Clause.variables
          simp only [Finset.mem_image, not_exists, not_and]
          intro l l_in

          have h_l_in_resolve : l ∈ (c₁'.resolve c₂' v (by aesop)) := by
            apply Clause.resolve_maintains_subset (by aesop) h_π₁ h_π₂
            assumption
          have : l ∈ ((Clause.resolve c₁ c₂ v h_v_mem).substitute ρ).get h_resolve_isSome := by
            rw [←Clause.substitute_resolve_eq_resolve_substitute]
            assumption
          have : l ∈ (C.substitute ρ).get (by aesop) := by
            apply Clause.substitute_maintains_subset
            · assumption
            · assumption
          have h_C_subst_variables : ((C.substitute ρ).get (by assumption)).variables =
              C.variables \ vars₁ := by simp

          by_contra! h_l_var
          have : v ∈ ((C.substitute ρ).get (by assumption)).variables := by
            rw [←h_l_var]
            apply literal_in_clause_variables
            assumption

          simp only [Clause.substitute_variables, Finset.mem_sdiff] at this
          tauto

        (TreeLikeResolution.resolve c₁'_rhs c₂'_rhs v (by aesop) h_v_notMem_resolve)
          (π₁.restrict ρ (Option.isSome_iff_ne_none.mpr h₁))
          (π₂.restrict ρ (Option.isSome_iff_ne_none.mpr h₂)) (by
          unfold TreeLikeResolution.restrict_rhs
          simp only [h₁, h₂, h_v, ↓reduceDIte]
          constructor
          · apply Clause.resolve_satisfies_h_resolve_left
          · apply Clause.resolve_satisfies_h_resolve_right
        )

@[simp]
lemma TreeLikeResolution.convert_trivial_size {vars} {φ : CNFFormula vars} {c₁ c₂ : Clause vars}
    (π : TreeLikeResolution φ c₁) (h_eq : c₁ = c₂) : (π.convert_trivial h_eq).size = π.size := by
  unfold TreeLikeResolution.convert_trivial TreeLikeResolution.size
  aesop

@[simp]
lemma TreeLikeResolution.convert_trivial_width {vars} {φ : CNFFormula vars} {c₁ c₂ : Clause vars}
    (π : TreeLikeResolution φ c₁) (h_eq : c₁ = c₂) : (π.convert_trivial h_eq).width = π.width := by
  unfold TreeLikeResolution.convert_trivial TreeLikeResolution.width
  aesop

@[simp]
lemma resolution_restrict_size {vars sub_vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) (ρ : Assignment sub_vars) (h_some) :
    (π.restrict ρ h_some).size ≤ π.size := by
  induction π
  case axiom_clause => aesop
  case resolve c c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ =>
    unfold TreeLikeResolution.restrict
    trans 1 + π₁.size + π₂.size
    swap
    · aesop

    if h₁ : c₁.substitute ρ = none then
      simp only [h₁, ↓reduceDIte]
      trans π₂.size
      · aesop
      · omega
    else if h₂ : c₂.substitute ρ = none then
      simp only [h₂, ↓reduceDIte]
      trans π₁.size
      · aesop
      · omega
    else
      simp only [h₁, h₂, ↓reduceDIte]
      if h_v : v ∈ sub_vars then
        if h_ρ_v : ρ v h_v then
          simp only [h_v, h_ρ_v, ↓reduceDIte]
          trans π₂.size
          · aesop
          · omega
        else
          simp only [h_v, h_ρ_v, ↓reduceDIte]
          trans π₁.size
          · aesop
          · omega
      else
        simp only [h_v, ↓reduceDIte, TreeLikeResolution.size]
        have h_π₁ : (π₁.restrict ρ (Option.isSome_iff_ne_none.mpr h₁)).size ≤ π₁.size := by aesop
        have h_π₂ : (π₂.restrict ρ (Option.isSome_iff_ne_none.mpr h₂)).size ≤ π₂.size := by aesop
        omega

lemma max_inequality {x x' y y' z z' : ℕ} (h_x : x ≤ x') (h_y : y ≤ y') (h_z : z ≤ z') :
    max x (max y z) ≤ max x' (max y' z') := by grind

@[simp]
lemma resolution_restrict_width {vars sub_vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) (ρ : Assignment sub_vars) (h_some) :
    (π.restrict ρ h_some).width ≤ π.width := by
  have h_c_card : ((c.substitute ρ).get h_some).card ≤ c.card := by aesop

  induction π
  case axiom_clause c h => aesop
  case resolve c c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ =>
    unfold TreeLikeResolution.restrict
    trans max c.card (max π₁.width π₂.width)
    swap
    · simp [TreeLikeResolution.width]

    if h₁ : c₁.substitute ρ = none then
      simp only [h₁, ↓reduceDIte]
      trans π₂.width
      · aesop
      · omega
    else if h₂ : c₂.substitute ρ = none then
      simp only [h₂, ↓reduceDIte]
      trans π₁.width
      · aesop
      · omega
    else
      simp only [h₁, h₂, ↓reduceDIte]
      if h_v : v ∈ sub_vars then
        if h_ρ_v : ρ v h_v then
          simp only [h_v, h_ρ_v, ↓reduceDIte]
          trans π₂.width
          · aesop
          · omega
        else
          simp only [h_v, h_ρ_v, ↓reduceDIte]
          trans π₁.width
          · aesop
          · omega
      else
        simp only [h_v, ↓reduceDIte, TreeLikeResolution.width]
        have h_π₁ : (π₁.restrict ρ (Option.isSome_iff_ne_none.mpr h₁)).width ≤ π₁.width := by aesop
        have h_π₂ : (π₂.restrict ρ (Option.isSome_iff_ne_none.mpr h₂)).width ≤ π₂.width := by aesop
        apply max_inequality
        · trans ((c.substitute ρ).get h_some).card
          · apply Finset.card_le_card
            exact
              TreeLikeResolution.restrict_rhs_subset_substitute
                (TreeLikeResolution.resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res) ρ h_some
          · assumption
        · assumption
        · assumption


lemma resolution_restrict {vars₁ vars₂ : Variables} {φ : CNFFormula vars₂}
    (ρ : Assignment vars₁) {C : Clause vars₂} (π : TreeLikeResolution φ C) :
    (C.substitute ρ = none) ∨
    (∃ c_res, C.substitute ρ = some c_res ∧
      ∃ c', c' ⊆ c_res ∧
      ∃ (π' : TreeLikeResolution (φ.substitute ρ) c'),
        π'.width ≤ π.width ∧ π'.size ≤ π.size) := by
  if h_none : C.substitute ρ = none then
    left
    assumption
  else
    right
    have : ∃ c_res, C.substitute ρ = some c_res := by
      use (C.substitute ρ).get (by exact Option.isSome_iff_ne_none.mpr h_none)
      aesop
    obtain ⟨c_res, h_some⟩ := this
    use c_res
    constructor
    · assumption
    use π.restrict_rhs ρ (by aesop)
    constructor
    · let w := (C.substitute ρ).get (by aesop)
      trans w
      · apply TreeLikeResolution.restrict_rhs_subset_substitute π ρ
      · aesop
    · let π' := π.restrict ρ (Option.isSome_of_mem h_some)
      use π'
      aesop

lemma substitute_trivial_property {vars}
    (φ : CNFFormula vars)
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (C_0 : Clause vars)
    (h_subs : (vars \ {x.variable}) ⊆ vars)
    (ρ_false : (Assignment ({x.variable} : Finset Variable)))
    (h_value_false : ρ_false = (fun _ _ => (¬x.polarity : Bool)))
    (h_c : C_0 ∈ ((CNFFormula.simple_convert
        (vars \ {x.variable}) vars (φ.substitute ρ_false) h_subs)))
    (C_1 : Clause (vars \ {x.variable}))
    (h_C_1_conv_left : C_1 ∈ (φ.substitute ρ_false))
    (h_incl : ∀ l ∈ C_1, l.variable ∈ vars)
    (h_C_1_conv_right : C_1.convert vars h_incl = C_0)
    (C_2 : Clause vars)
    (h_C_2_conv : C_2 ∈ φ ∧ C_2.substitute ρ_false = some C_1)
    : C_2 ⊆ C_0 ∪ ({x} : Clause vars) := by
  intro l hl

  obtain ⟨left, right⟩ := h_C_2_conv
  rw [← h_C_1_conv_right]


  -- 3. Since l ∈ C_1.convert, there must be a source literal l' ∈ C_1
  -- You'll likely need to unfold Clause.convert or use a lemma like 'mem_convert'
  unfold Clause.convert
  simp
  by_cases l = x
  case pos h_l =>
    exact Or.symm (Or.inr h_l)
  case neg h_l =>
    refine Or.symm (Or.intro_left (l = x) ?_)
    unfold Clause.substitute at right
    simp at right
    obtain ⟨h_sp_l, h_sp_r⟩ := right
    -- aesop
    -- unfold Clause.split
    -- aesop
    -- unfold Clause.shrink
    -- aesop
    -- unfold Clause.split at h_c
    -- aesop
    -- unfold Clause.shrink at h_c
    -- aesop
    -- unfold Clause.convert at h_c
    -- simp at h_c
    sorry

lemma weaken_proof {vars} {φ : CNFFormula vars} {c c' : Clause vars}
    (π : TreeLikeResolution φ c) (h_sub : c ⊆ c') :
    ∃ (π' : TreeLikeResolution φ c'), IsRegularRes π → (IsRegularRes π' ∧ π'.size ≤ π.size) := by
  -- This requires its own induction on π.
  -- If you encounter a resolve node where the resolved variable is already in c',
  -- you must bypass that node here as well to maintain IsRegularRes.
  induction π with
  | axiom_clause h_in =>
      -- Base case is trivially regular
      sorry
      -- use TreeLikeResolution.axiom_clause h_in
      -- simp [IsRegularRes, TreeLikeResolution.size]
      -- sorry
  | resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ => sorry

lemma eliminate_vacuous_resolutions_prep {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) :
    ∃ (c' : Clause vars) (π' : TreeLikeResolution φ c'),
      (c' ⊆ c) ∧ IsRegularRes π' ∧ π'.size ≤ π.size := by
  induction π with
  | axiom_clause h_in =>
      -- Base case is trivially regular
      -- use .axiom_clause h_in
      -- simp [IsRegularRes, TreeLikeResolution.size]
      sorry
  | resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ =>
      -- 1. Extract the regularized subproofs from the inductive hypotheses
      -- obtain ⟨π₁', h_reg₁, h_size₁⟩ := ih₁
      -- obtain ⟨π₂', h_reg₂, h_size₂⟩ := ih₂

      -- -- 2. Check if the resolution is vacuous
      -- by_cases hv1 : v ∈ c₁.variables
      -- · by_cases hv2 : v ∈ c₂.variables
      --   · -- Case A: Non-vacuous. Both contain v.
      --     -- We can safely reconstruct the resolve node.
      --     use .resolve c₁ c₂ v h_v_mem h_v_not π₁' π₂' h_res

      --     -- The size and regularity bounds hold by simple arithmetic and the IHs
      --     constructor
      --     · simp only [IsRegularRes]
      --       exact ⟨hv1, hv2, h_reg₁, h_reg₂⟩
      --     · -- π'.size = 1 + π₁'.size + π₂'.size ≤ 1 + π₁.size + π₂.size
      --       -- (Use 'omega' or 'linarith' here)
      --       sorry

      --   · -- Case B: Vacuous on the right. v ∉ c₂.variables.
      --     -- Because c₂ ⊆ c ∪ {~v} and v ∉ c₂, it must be that c₂ ⊆ c.
      --     have h_c2_sub_c : c₂ ⊆ c := by
      --       -- Prove this using your Finset/Clause API
      --       sorry

      --     -- We completely bypass π₁' and the resolve node!
      --     obtain ⟨π_new, h_new_prop⟩ := weaken_proof π₂' h_c2_sub_c
      --     --use π_new

      --     -- π_new.size ≤ π₂'.size ≤ π₂.size < 1 + π₁.size + π₂.size
      --     -- (Apply h_new_prop to h_reg₂ to get regularity and size)
      --     sorry

      -- · -- Case C: Vacuous on the left. v ∉ c₁.variables.
      --   -- Exactly symmetrical to Case B.
      --   have h_c1_sub_c : c₁ ⊆ c := by
      --     sorry

      --   obtain ⟨π_new, h_new_prop⟩ := weaken_proof π₁' h_c1_sub_c
      --   --use π_new
      --   sorry
    sorry

@[aesop safe]
lemma proof_size_positive {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) : π.size > 0 := by
  unfold TreeLikeResolution.size
  aesop

lemma size_one_proof {vars} (φ : CNFFormula vars)
    (W_c : ℕ) (h_clause_card : ∀ C ∈ φ, C.card ≤ W_c) (π : TreeLikeRefutation φ)
    (h_size : π.size ≤ 1) :
     π.width ≤ W_c := by
  cases h : π with
  | axiom_clause h_in => aesop
  | resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
      -- This is impossible, as a resolution step has size > 1.
      -- You can close this branch by contradiction.
    suffices π.size > 1 by
      omega

    unfold TreeLikeResolution.size at *
    subst h
    simp_all only [gt_iff_lt]
    trans 1 + π₁.size
    · aesop
    · aesop
