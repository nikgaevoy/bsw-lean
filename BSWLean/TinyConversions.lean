import BSWLean.Treelike
import BSWLean.ProofOperations

/-!
# TinyConversions

This is a file connecting `SizeWidth` to the rest of the project.

It proves technical lemmas needed for the lower bounds, that are stated on structures defined
outside of `SizeWidth`.
-/

/-- A technical function used in `SizeWidth`. -/
def is_resolve {vars} {φ : CNFFormula vars} {c : Clause vars} :
    TreeLikeResolution φ c → Prop
  | .axiom_clause _ => false
  | .resolve .. => true

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
      aesop (add safe unfold Clause.convert)

    simp_all

lemma substitute_trivial_property_human_form {vars} {c : Clause vars} {l : Literal vars} {h} :
    c ⊆
    ((c.substitute (fun _ _ => ¬l.polarity : Assignment {l.variable})).get h).convert
      vars (by
        intro t
        have := Literal.variable_mem_vars t
        aesop) ∪ {l} := by
  intro t h_t
  simp only [Bool.not_eq_true, Bool.decide_eq_false, Finset.union_singleton, Finset.mem_insert]
  by_cases h_var : t.variable = l.variable
  case pos =>
    left
    rw [Clause.substitute_isSome_iff_eval_subclause_false] at h
    simp at h
    rw [Clause.eval_eq_false_iff_all_falsified_literals] at h
    simp only [Finset.mem_filter, Finset.mem_filterMap,
      Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self, forall_exists_index,
      forall_and_index] at h

    let t' := t.restrict (vars ∩ {l.variable}) (by aesop)
    have := h t' t h_t (by aesop) rfl
    have h_t' : t'.polarity = t.polarity := by aesop

    by_cases l.polarity
    all_goals by_cases t.polarity
    all_goals simp_all [Literal.eval, Literal.variable, Literal.restrict]
    all_goals have : l.polarity = t.polarity := by grind;
    all_goals grind
  case neg =>
    right
    unfold Clause.substitute Clause.split Clause.shrink Clause.convert
    simp only [Finset.mem_singleton, Finset.mem_filter, Option.get_ite', Finset.mem_filterMap,
      Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self, Lean.Elab.WF.paramLet]

    let t' := t.restrict (vars \ {l.variable}) (by aesop)
    use t'

    use by
      use t
      use by aesop

    simp [t']
    unfold Literal.convert Literal.restrict
    aesop

lemma substitute_trivial_property {vars}
    (φ : CNFFormula vars)
    (x : Literal vars)
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
    (h_C_2_conv : C_2 ∈ φ ∧ C_2.substitute ρ_false = some C_1) :
    C_2 ⊆ C_0 ∪ ({x} : Clause vars) := by
  suffices C_0 =
      ((C_2.substitute (fun _ _ => ¬x.polarity : Assignment {x.variable})).get (by aesop)).convert
        vars (by
          intro t
          have := Literal.variable_mem_vars t
          aesop) by
    rw [this]
    exact substitute_trivial_property_human_form

  subst h_value_false
  simp only [Bool.not_eq_true, Bool.decide_eq_false] at h_C_2_conv
  simp_all

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

#lint
