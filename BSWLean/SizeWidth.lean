import BSWLean.Treelike
import BSWLean.TinyConversions

def TreeLikeResolution.width {vars} {φ : CNFFormula vars} :
    ∀ {c : Clause vars}, TreeLikeResolution φ c → Nat
  | C, .axiom_clause _ => C.card
  | C, .resolve _ _ _ _ _ π₁ π₂ _ => max C.card (max (width π₁) (width π₂))

lemma card_combination {vars} {sub_vars} {ρ : Assignment sub_vars}
    (c : Clause (vars \ sub_vars)) (C : Clause (vars \ sub_vars)) {h₁ h₂}
    : Finset.card ((C.combine ρ.toClause h₁).convert_trivial vars h₂)
    ≤ Finset.card C + (Finset.card sub_vars) := by
  unfold Clause.combine
  simp
  have idea₁ : Finset.card (C.convert (Finset.disjUnion (vars \ sub_vars) sub_vars h₁)
    (Clause.combine._proof_1 C h₁ : ∀ l ∈ C, l.variable ∈ Finset.disjUnion (vars \ sub_vars) sub_vars h₁))
    ≤ (Finset.card C) := by
    simp
  have idea₂: Finset.card (ρ.toClause.convert (Finset.disjUnion (vars \ sub_vars) sub_vars h₁)
    (Clause.combine._proof_2 ρ.toClause h₁ : ∀ l ∈ ρ.toClause, l.variable ∈ Finset.disjUnion (vars \ sub_vars) sub_vars h₁))
    ≤ Finset.card sub_vars := by
    simp
    exact to_clause_card_less_than_sub_vars_card ρ
  grind only [usr Finset.card_union_add_card_inter]

lemma resolve_subsets (x : Variable) (vars) (c₁ c₂ c₃ c₄ : Clause (vars))
    (h_x : x ∈ vars) (h₁ : c₁ ⊆ c₃) (h₂ : c₂ ⊆ c₄) : (c₁.resolve c₂ x h_x) ⊆ (c₃.resolve c₄ x h_x)
    := by
    unfold Clause.resolve
    grind

lemma resolve_subsets_trick (x : Variable) (vars) (c₁ c₂ c₃ : Clause (vars))
    (h_x : x ∈ vars) (h₁ : c₂ ⊆ c₁ ∪ {x.toLiteral h_x}) (h₂: c₃ ⊆ c₁ ∪ {x.toNegLiteral h_x}) : Finset.card (c₂.resolve c₃ x h_x) ≤ Finset.card c₁
    := by
    unfold Clause.resolve
    have idea : (Finset.erase c₂ (x.toLiteral h_x) ∪ Finset.erase c₃ (x.toNegLiteral h_x)) ⊆ c₁
      := by
      simp_all only [Finset.union_singleton]
      grind
    exact Finset.card_le_card idea

lemma clause_combine_superset (vars₁ vars₂) {x : Variable} (c₁ c₂: Clause (vars₁)) (c₃ : Clause (vars₂))
    (h₀ : x ∈ vars₁) (h₁ : c₂ ⊆ c₁ ∪ {x.toLiteral h₀}) (h_disj: Disjoint vars₁ vars₂) (h₂ : x ∈ (vars₁.disjUnion vars₂ h_disj)):
    (Clause.combine c₂ c₃ h_disj) ⊆ ((Clause.combine c₁ c₃ h_disj) ∪ {x.toLiteral h₂})
    := by
    simp
    unfold Clause.combine
    simp
    refine Finset.union_subset ?_ ?_
    trans insert (x.toLiteral h₂) (c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop))
    refine
      Clause.convert_maintains_subset_insert c₂ c₁ (Finset.disjUnion vars₁ vars₂ h_disj)
        (x.toLiteral h₂) h₀ ?_
    simp_all only [Finset.union_singleton]
    exact h₁
    simp
    trans (c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ∪ c₃.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop))
    simp
    simp

@[aesop safe]
lemma loose_convert {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂} (h_subset : c₁ ⊆ c₂) :
    (c₁.convert vars₂ h₁) ⊆ (c₂.convert vars₂ h₂) := by
  exact Clause.convert_keeps_subset vars₂ h_subset

@[simp]
lemma loose_convert_eq {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂} (h_subset : c₁ = c₂) :
    (c₁.convert vars₂ h₁) = (c₂.convert vars₂ h₂) := by
  aesop

@[aesop safe]
lemma loose_convert_trivial {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂} (h_subset : c₁ ⊆ c₂) :
    (c₁.convert_trivial vars₂ h₁) ⊆ (c₂.convert_trivial vars₂ h₂) := by
  unfold Clause.convert_trivial
  aesop

@[simp]
lemma carry_through_convert {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁} :
    ((c₁ ∪ c₂).convert vars₂ h₁) =
    (c₁.convert vars₂ (by aesop)) ∪ (c₂.convert vars₂ (by aesop)) := by
  unfold Clause.convert
  aesop

@[simp]
lemma carry_through_convert_trivial {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂} :
    ((c₁ ∪ c₂).convert_trivial vars₂ h₁) =
    (c₁.convert_trivial vars₂ h₂) ∪ (c₂.convert_trivial vars₂ h₂) := by
  unfold Clause.convert_trivial
  aesop

lemma cup_subset_cup {α} [DecidableEq α] (a b c d : Finset α) (h : a ⊆ c) (h' : b ⊆ d) :
    (a ∪ b) ⊆ (c ∪ d) := by
  grind

lemma remove_middle_subset {α} [DecidableEq α] (a b c d : Finset α) (h : a ⊆ b ∪ d) :
    a ⊆ b ∪ c ∪ d := by grind


lemma unsub_increase_width {vars sub_vars} {φ : CNFFormula vars}
    {ρ : Assignment sub_vars} (c : Clause (vars \ sub_vars))
    (π : TreeLikeResolution (φ.substitute ρ) c) (h_subset : sub_vars ⊆ vars) :
    (π.unsubstitute h_subset).width ≤ π.width + sub_vars.card := by
  induction π
  case axiom_clause C h =>
    unfold TreeLikeResolution.unsubstitute
    simp_all only
    unfold TreeLikeResolution.width
    trans ((Clause.combine C ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)).card
    · refine Finset.card_le_card ?_
      exact TreeLikeResolution.unsubstitute_rhs_variables (TreeLikeResolution.axiom_clause h) h_subset
    exact card_combination c C
  case resolve c_1 c_2 c_3 var h_4 h_0 p_1 p_2 h_1 h_2 h_3 =>
    unfold TreeLikeResolution.width
    obtain ⟨left, right⟩ := h_1
    split
    next x x_1 h_c_in_φ heq =>
      unfold TreeLikeResolution.unsubstitute_rhs
      simp
      -- have idea₁ : Finset.card (p_1.unsubstitute_rhs h_subset) ≤ Finset.card c_2 + Finset.card sub_vars := by
      --   have inter_idea₁ : (p_1.unsubstitute_rhs h_subset) ⊆
      --     (Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
      --     := by
      --     exact TreeLikeResolution.unsubstitute_rhs_variables p_1 h_subset
      --   have inter_idea₂ :
      --     Finset.card ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)) ≤
      --     Finset.card c_2 + Finset.card sub_vars
      --     := by
      --     exact card_combination c c_2
      --   trans Finset.card ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop))
      --   exact Finset.card_le_card inter_idea₁
      --   exact inter_idea₂
      -- have idea₂ : Finset.card (p_2.unsubstitute_rhs h_subset) ≤ Finset.card c_3 + Finset.card sub_vars := by
      --   have inter_idea₁ : (p_2.unsubstitute_rhs h_subset) ⊆
      --     (Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
      --     := by
      --     exact TreeLikeResolution.unsubstitute_rhs_variables p_2 h_subset
      --   have inter_idea₂ :
      --     Finset.card ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)) ≤
      --     Finset.card c_3 + Finset.card sub_vars
      --     := by
      --     exact card_combination c c_3
      --   trans Finset.card ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop))
      --   exact Finset.card_le_card inter_idea₁
      --   exact inter_idea₂
      have idea₁ : (p_1.unsubstitute_rhs h_subset) ⊆
        (Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
        := by
        exact TreeLikeResolution.unsubstitute_rhs_variables p_1 h_subset
      have idea₂ : (p_2.unsubstitute_rhs h_subset) ⊆
        (Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)
        := by
        exact TreeLikeResolution.unsubstitute_rhs_variables p_2 h_subset

      trans Finset.card (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)).resolve
        ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)) var (Finset.sdiff_subset h_4 : var ∈ vars))

      have inter_idea :
        ((p_1.unsubstitute_rhs h_subset).resolve (p_2.unsubstitute_rhs h_subset) var (Finset.sdiff_subset h_4 : var ∈ vars)) ⊆
        (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)).resolve
        ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)) var (Finset.sdiff_subset h_4 : var ∈ vars)) := by
        exact
          resolve_subsets var vars (p_1.unsubstitute_rhs h_subset) (p_2.unsubstitute_rhs h_subset)
            ((c_2.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars
              (of_eq_true
                (Eq.trans
                  (Eq.trans
                    (congrArg (fun x ↦ x = vars)
                      (Eq.trans
                        (Finset.disjUnion_eq_union (vars \ sub_vars) sub_vars Finset.sdiff_disjoint)
                        Finset.sdiff_union_self_eq_union))
                    Finset.union_eq_left._simp_1)
                  (eq_true h_subset))))
            ((c_3.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars
              (of_eq_true
                (Eq.trans
                  (Eq.trans
                    (congrArg (fun x ↦ x = vars)
                      (Eq.trans
                        (Finset.disjUnion_eq_union (vars \ sub_vars) sub_vars Finset.sdiff_disjoint)
                        Finset.sdiff_union_self_eq_union))
                    Finset.union_eq_left._simp_1)
                  (eq_true h_subset))))
            (Finset.sdiff_subset h_4) idea₁ idea₂
      exact Finset.card_le_card inter_idea
      trans Finset.card c_1 + Finset.card sub_vars
      trans Finset.card ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop))
      have temp₁ : Finset.disjUnion (vars \ sub_vars) sub_vars (Finset.sdiff_disjoint : Disjoint (vars \ sub_vars) sub_vars) = vars := by
        aesop
      have idea₃ : ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)) ⊆
        ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)) ∪ {var.toLiteral (by grind)} := by
        have : Clause.convert {var.toLiteral h_4} vars
            (by intro l h_l; have q := Literal.variable_mem_vars l; aesop) =
            {var.toLiteral (by grind)} := by
          unfold Clause.convert
          simp only [Finset.mem_singleton]
          aesop
        rw [←this]
        unfold Clause.combine
        unfold Clause.convert_trivial
        simp only [Finset.disjUnion_eq_union, Finset.sdiff_union_self_eq_union, Finset.mem_union,
          Literal.variable_mem_vars, or_true, implies_true, carry_through_convert,
          Clause.convert_convert, Finset.union_assoc]
        apply Finset.union_subset
        swap
        · grind
        rw [←Finset.union_assoc]
        apply remove_middle_subset
        unfold Clause.convert
        grind

      have idea₄ : ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)) ⊆
        ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)) ∪ {var.toNegLiteral (by grind)} := by
        sorry
      simp only [ge_iff_le]
      apply resolve_subsets_trick var vars ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars temp₁)
        ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars temp₁)
        ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars temp₁)
        (by grind) idea₃ idea₄
      exact card_combination c c_1
      simp_all only [add_le_add_iff_right, le_sup_left]
    next x x_1 c₁ c₂ v h_v_mem_vars π₁ π₂ h_v_not_mem_c h_resolve
      heq =>
      simp_all only [sup_le_iff]
      obtain ⟨left_1, right_1⟩ := h_resolve
      apply And.intro
      · sorry
      · apply And.intro
        · sorry
        · sorry





lemma width_combine {vars} {φ : CNFFormula vars}
    (h_unsat : Unsat φ) (x : Literal vars)
    (ρ_true : Assignment {x.variable} := (fun _ => fun _ => x.polarity))
    (ρ_false : Assignment {x.variable} := (fun _ => fun _ => ¬x.polarity))
    (φ_true := φ.substitute ρ_true) (φ_false := φ.substitute ρ_false)
    (W : ℕ) (π₁ : TreeLikeRefutation φ_true) (h_width_true : π₁.width ≤ W)
    (π₂ : TreeLikeRefutation φ_false) (h_width_false : π₂.width ≤ W - 1) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W := by

  sorry


theorem width_imply_size {vars} {φ : CNFFormula vars}
    (h_unsat : Unsat φ) (π : TreeLikeRefutation φ) (W : ℕ) (h_size : π.size ≤ 2 ^ W) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W := by
  sorry
