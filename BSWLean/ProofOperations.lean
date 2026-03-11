import BSWLean.Treelike

def IsRegularRes {vars} {φ : CNFFormula vars} : ∀ {c : Clause vars}, TreeLikeResolution φ c → Prop
  | _, .axiom_clause _ => True
  | _, .resolve c₁ c₂ v _ _ π₁ π₂ _ =>
      v ∈ c₁.variables ∧ v ∈ c₂.variables ∧ IsRegularRes π₁ ∧ IsRegularRes π₂

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
    {c : Clause vars₂} (π : TreeLikeResolution φ c) (ρ : Assignment vars₁)
    (h_some : (c.substitute ρ).isSome) :
    Clause (vars₂ \ vars₁) :=
  match h : π with
  | .axiom_clause h_in =>
      (c.substitute ρ).get h_some
  | .resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
      have : Clause.resolve c₁ c₂ v h_v_mem ⊆ c := by
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
    {φ : CNFFormula vars₂} {c : Clause vars₂} (π : TreeLikeResolution φ c) (ρ : Assignment vars₁)
    (h_some : (c.substitute ρ).isSome) :
    π.restrict_rhs ρ h_some ⊆ (c.substitute ρ).get h_some := by
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

def TreeLikeResolution.restrict {vars₁ vars₂ : Variables} {φ : CNFFormula vars₂}
    {c : Clause vars₂} (π : TreeLikeResolution φ c) (ρ : Assignment vars₁)
    (h_some : (c.substitute ρ).isSome) :
    TreeLikeResolution (φ.substitute ρ) (TreeLikeResolution.restrict_rhs π ρ h_some) :=
  match h : π with
  | .axiom_clause h_in =>
    .axiom_clause (by
      unfold TreeLikeResolution.restrict_rhs CNFFormula.substitute
      aesop
    )
  | .resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
    have : Clause.resolve c₁ c₂ v h_v_mem ⊆ c := by
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
      (π₂.restrict ρ this).convert (by aesop)
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

      (π₁.restrict ρ this).convert (by aesop)
    else
      if h_v : v ∈ vars₁ then
        if h_ρ_v : ρ v h_v then
          (π₂.restrict ρ (Option.isSome_iff_ne_none.mpr h₂)).convert (by
            unfold TreeLikeResolution.restrict_rhs
            aesop
          )
        else
          (π₁.restrict ρ (Option.isSome_iff_ne_none.mpr h₁)).convert (by
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
          have : l ∈ (c.substitute ρ).get (by aesop) := by
            apply Clause.substitute_maintains_subset
            · assumption
            · assumption
          have h_C_subst_variables : ((c.substitute ρ).get (by assumption)).variables =
              c.variables \ vars₁ := by simp

          by_contra! h_l_var
          have : v ∈ ((c.substitute ρ).get (by assumption)).variables := by
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
    (π : TreeLikeResolution φ c₁) (h_eq : c₁ = c₂) : (π.convert h_eq).size = π.size := by
  unfold TreeLikeResolution.convert TreeLikeResolution.size
  aesop

@[simp]
lemma TreeLikeResolution.convert_trivial_width {vars} {φ : CNFFormula vars} {c₁ c₂ : Clause vars}
    (π : TreeLikeResolution φ c₁) (h_eq : c₁ = c₂) : (π.convert h_eq).width = π.width := by
  unfold TreeLikeResolution.convert TreeLikeResolution.width
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
    (ρ : Assignment vars₁) {c : Clause vars₂} (π : TreeLikeResolution φ c) :
    (c.substitute ρ = none) ∨
    (∃ c_res, c.substitute ρ = some c_res ∧
      ∃ c', c' ⊆ c_res ∧
      ∃ (π' : TreeLikeResolution (φ.substitute ρ) c'),
        π'.width ≤ π.width ∧ π'.size ≤ π.size) := by
  if h_none : c.substitute ρ = none then
    left
    assumption
  else
    right
    have : ∃ c_res, c.substitute ρ = some c_res := by
      use (c.substitute ρ).get (by exact Option.isSome_iff_ne_none.mpr h_none)
      aesop
    obtain ⟨c_res, h_some⟩ := this
    use c_res
    constructor
    · assumption
    use π.restrict_rhs ρ (by aesop)
    constructor
    · let w := (c.substitute ρ).get (by aesop)
      trans w
      · apply TreeLikeResolution.restrict_rhs_subset_substitute π ρ
      · aesop
    · let π' := π.restrict ρ (Option.isSome_of_mem h_some)
      use π'
      aesop

def TreeLikeResolution.regularize_rhs {vars : Variables} {φ : CNFFormula vars}
    {c : Clause vars} (π : TreeLikeResolution φ c) : Clause vars :=
  match π with
  | .axiom_clause _ => c
  | .resolve _ _ v h_v_mem _ π₁ π₂ _ =>
    if v.toLiteral h_v_mem ∉ π₁.regularize_rhs then
      π₁.regularize_rhs
    else if v.toNegLiteral h_v_mem ∉ π₂.regularize_rhs then
      π₂.regularize_rhs
    else
      π₁.regularize_rhs.resolve π₂.regularize_rhs v h_v_mem

@[aesop safe]
lemma TreeLikeResolution.regularize_rhs_subset {vars : Variables} {φ : CNFFormula vars}
    {c : Clause vars} (π : TreeLikeResolution φ c) : π.regularize_rhs ⊆ c := by
  induction π
  case axiom_clause => aesop
  case resolve c c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ =>
    let c₁' := π₁.regularize_rhs
    let c₂' := π₂.regularize_rhs

    if h₁ : v.toLiteral h_v_mem ∉ c₁' then
      unfold regularize_rhs
      simp [c₁', h₁]
      trans c₁ \ {v.toLiteral h_v_mem}
      · grind
      · grind
    else if h₂ : v.toNegLiteral h_v_mem ∉ c₂' then
      unfold regularize_rhs
      simp [c₁', h₁, c₂', h₂]
      trans c₂ \ {v.toNegLiteral h_v_mem}
      · grind
      · grind
    else
      unfold regularize_rhs
      simp [c₁', h₁, c₂', h₂]
      trans c₁.resolve c₂ v h_v_mem
      · aesop
      · unfold Clause.resolve
        grind


def TreeLikeResolution.regularize {vars : Variables} {φ : CNFFormula vars}
    {c : Clause vars} (π : TreeLikeResolution φ c) : TreeLikeResolution φ π.regularize_rhs :=
  match h : π with
  | .axiom_clause _ => π.convert (by aesop)
  | .resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
    let c₁' := π₁.regularize_rhs
    let c₂' := π₂.regularize_rhs

    if h₁ : v.toLiteral h_v_mem ∉ c₁' then
      π₁.regularize.convert (by
        conv =>
          rhs
          unfold regularize_rhs
        aesop)
    else if h₂ : v.toNegLiteral h_v_mem ∉ c₂' then
      π₂.regularize.convert (by
        conv =>
          rhs
          unfold regularize_rhs
        aesop)
    else
      have h_v_not' : v ∉ π.regularize_rhs.variables := by
        by_contra!
        have : v ∈ c.variables := by
          apply clause_variable_mem_variables_maintains_subset _ this
          aesop
        contradiction
      have h_res' : c₁' ⊆ π.regularize_rhs ∪ {v.toLiteral h_v_mem} ∧
          c₂' ⊆ π.regularize_rhs ∪ {v.toNegLiteral h_v_mem} := by
        unfold regularize_rhs
        simp only [h, h₁, h₂, c₁', c₂', ↓reduceIte]
        constructor
        · apply Clause.resolve_satisfies_h_resolve_left
        · apply Clause.resolve_satisfies_h_resolve_right

      TreeLikeResolution.resolve c₁' c₂' v h_v_mem (by aesop)
        π₁.regularize π₂.regularize (by aesop)

@[aesop safe]
lemma TreeLikeResolution.regularize_size {vars : Variables} {φ : CNFFormula vars}
    {c : Clause vars} (π : TreeLikeResolution φ c) : π.regularize.size ≤ π.size := by
  induction π
  case axiom_clause => aesop
  case resolve c c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ =>
    let c₁' := π₁.regularize_rhs
    let c₂' := π₂.regularize_rhs

    if h₁ : v.toLiteral h_v_mem ∉ c₁' then
      unfold regularize
      simp only [h₁, not_false_eq_true, ↓reduceDIte, convert_trivial_size, ge_iff_le, c₁']
      conv =>
        rhs
        unfold size
      omega
    else if h₂ : v.toNegLiteral h_v_mem ∉ c₂' then
      unfold regularize
      simp only [h₁, ↓reduceDIte, h₂, not_false_eq_true, convert_trivial_size, ge_iff_le, c₂', c₁']
      conv =>
        rhs
        unfold size
      omega
    else
      unfold regularize
      simp only [h₁, ↓reduceDIte, h₂, ge_iff_le, c₂', c₁']
      unfold size
      omega

@[simp]
lemma TreeLikeResolution.convert_isRegularRes {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) (c' : Clause vars) (h : c = c') :
    IsRegularRes (π.convert h) = IsRegularRes π := by
  unfold convert
  aesop

@[aesop safe]
lemma TreeLikeResolution.regularize_isRegularRes {vars : Variables} {φ : CNFFormula vars}
    {c : Clause vars} (π : TreeLikeResolution φ c) : IsRegularRes π.regularize := by
  induction h : π
  case axiom_clause =>
    unfold IsRegularRes regularize convert
    aesop
  case resolve c c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ =>
    let c₁' := π₁.regularize_rhs
    let c₂' := π₂.regularize_rhs

    have h_π₁ := ih₁ π₁ rfl
    have h_π₂ := ih₂ π₂ rfl

    if h₁ : v.toLiteral h_v_mem ∉ c₁' then
      unfold regularize
      simp [h₁, c₁', h_π₁]
    else if h₂ : v.toNegLiteral h_v_mem ∉ c₂' then
      unfold regularize
      simp [h₁, c₁', h₂, c₂', h_π₂]
    else
      unfold regularize
      simp only [h₁, ↓reduceDIte, h₂, c₂', c₁']
      unfold IsRegularRes
      have : (v.toLiteral h_v_mem).variable ∈ c₁'.variables := by aesop
      have : (v.toNegLiteral h_v_mem).variable ∈ c₂'.variables := by aesop
      aesop

lemma resolution_regularize {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) :
    ∃ (c' : Clause vars) (π' : TreeLikeResolution φ c'),
      (c' ⊆ c) ∧ IsRegularRes π' ∧ π'.size ≤ π.size := by
  use π.regularize_rhs
  use π.regularize
  aesop
