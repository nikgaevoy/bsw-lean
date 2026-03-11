import BSWLean.Treelike
import BSWLean.TinyConversions
import Mathlib.Data.Finset.Basic

lemma lit_subst_is_Bot_false {vars}
    (l : Literal vars)
    (ρ_false : (Assignment ({l.variable} : Finset Variable)))
    (h_value : ρ_false = (fun _ _ => (¬l.polarity : Bool))) :
    ({l} : Clause vars).substitute ρ_false = BotClause (vars \ {l.variable}):= by

  unfold BotClause
  unfold Clause.substitute
  subst h_value
  simp_all only [Bool.not_eq_true, Bool.decide_eq_false, Option.ite_none_left_eq_some,
    Option.some.injEq]
  apply And.intro
  · have : l.variable ∈ (vars ∩ {l.variable}) := by
      aesop
    let l' : Literal (vars ∩ {l.variable}) := l.convert (vars ∩ {l.variable}) this
    have : (({l} : Clause vars).split {l.variable}).1 = ({l'} :
        Clause ((vars) ∩ {l.variable})) := by
      unfold Clause.split
      simp_all [l']
      unfold Literal.convert Clause.shrink
      aesop
    simp_all only [l']
    unfold Literal.convert
    aesop
  · unfold Clause.split Clause.shrink
    aesop



lemma shrink_width_ineq {vars} {sub_vars}
    (C : Clause (vars)) {h} :
    Finset.card (Clause.shrink C (vars \ sub_vars) h) ≤ C.card := by
    unfold Clause.shrink
    simp_all only [filterMap_card]


lemma shrink_width_ineq_adv {vars} {sub_vars} (C : Clause (vars)) {h} :
    Finset.card (Clause.shrink ({l ∈ C | l.variable ∉ sub_vars}) (vars \ sub_vars) h) ≤
      Finset.card C := by
    trans Finset.card ({l ∈ C | l.variable ∉ sub_vars})
    · exact shrink_width_ineq ({l ∈ C | l.variable ∉ sub_vars})
    · exact Finset.card_filter_le C fun l ↦ l.variable ∉ sub_vars


lemma card_subst {vars} {sub_vars} {ρ : Assignment sub_vars} (C : Clause (vars)) :
    (C.substitute ρ = none) ∨
    (∃ c_res, C.substitute ρ = some c_res ∧ Finset.card c_res ≤ Finset.card C) := by
  cases h : C.substitute ρ with
  | none =>
      -- Case 1: C.substitute ρ = none
      apply Or.inl
      rfl
  | some c_res =>
      -- Case 2: C.substitute ρ = some c_res
      apply Or.inr
      use c_res
      constructor
      · rfl
      · unfold Clause.substitute at h
        simp_all
        obtain ⟨h_left, h_right⟩ := h
        subst h_right
        unfold Clause.split
        simp_all only
        have h : ∀ l ∈ {l ∈ C | l.variable ∉ sub_vars}, l.variable ∈ vars \ sub_vars := by
          aesop
        have : Finset.card (Clause.shrink ({l ∈ C | l.variable ∉ sub_vars}) (vars \ sub_vars) h) ≤
            Finset.card C := by
          exact shrink_width_ineq_adv C
        simp_all only


lemma card_combination {vars} {sub_vars} {ρ : Assignment sub_vars} (C : Clause (vars \ sub_vars))
    {h₁ h₂} : Finset.card ((C.combine ρ.toClause h₁).convert_trivial vars h₂)
    ≤ Finset.card C + (Finset.card sub_vars) := by
  unfold Clause.combine
  simp
  have idea₁ : Finset.card (C.convert (Finset.disjUnion (vars \ sub_vars) sub_vars h₁)
    (Clause.combine._proof_1 C h₁ :
    ∀ l ∈ C, l.variable ∈ Finset.disjUnion (vars \ sub_vars) sub_vars h₁)) ≤ (Finset.card C) := by
    simp
  have idea₂: Finset.card (ρ.toClause.convert (Finset.disjUnion (vars \ sub_vars) sub_vars h₁)
    (Clause.combine._proof_2 ρ.toClause h₁ :
    ∀ l ∈ ρ.toClause, l.variable ∈ Finset.disjUnion (vars \ sub_vars) sub_vars h₁))
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
    (h_x : x ∈ vars) (h₁ : c₂ ⊆ c₁ ∪ {x.toLiteral h_x})
    (h₂ : c₃ ⊆ c₁ ∪ {x.toNegLiteral h_x}) :
    Finset.card (c₂.resolve c₃ x h_x) ≤ Finset.card c₁
    := by
  unfold Clause.resolve
  have idea : (Finset.erase c₂ (x.toLiteral h_x) ∪ Finset.erase c₃ (x.toNegLiteral h_x)) ⊆ c₁
    := by
    simp_all only [Finset.union_singleton]
    grind
  exact Finset.card_le_card idea

lemma clause_combine_superset (vars₁ vars₂) {x : Variable} (c₁ c₂ : Clause (vars₁))
    (c₃ : Clause (vars₂)) (h₀ : x ∈ vars₁) (h₁ : c₂ ⊆ c₁ ∪ {x.toLiteral h₀})
    (h_disj : Disjoint vars₁ vars₂) (h₂ : x ∈ (vars₁.disjUnion vars₂ h_disj)) :
    (Clause.combine c₂ c₃ h_disj) ⊆ ((Clause.combine c₁ c₃ h_disj) ∪ {x.toLiteral h₂}) := by
  simp
  unfold Clause.combine
  simp
  refine Finset.union_subset ?_ ?_
  · trans insert (x.toLiteral h₂) (c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop))
    · refine Clause.convert_maintains_subset_insert c₂ c₁ (Finset.disjUnion vars₁ vars₂ h_disj)
        (x.toLiteral h₂) h₀ ?_
      simp_all only [Finset.union_singleton]
      exact h₁
    · simp
  · trans (c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ∪
           c₃.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop))
    · simp
    · simp

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
lemma carry_through_convert₂ {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂ h₃} :
    ((c₁ ∪ c₂).convert vars₂ h₁) =
    (c₁.convert vars₂ h₂) ∪ (c₂.convert vars₂ h₃) := by
  unfold Clause.convert
  aesop

@[simp]
lemma carry_through_convert_expl (vars₁ vars₂) (c₁ c₂ : Clause vars₁) (h₁ h₂ h₃) :
    ((c₁ ∪ c₂).convert vars₂ h₁) =
    (c₁.convert vars₂ h₂) ∪ (c₂.convert vars₂ h₃) := by
  unfold Clause.convert
  aesop

@[simp]
lemma carry_through_convert_expl_lit (vars₁ vars₂) (c₁ : Clause vars₁)
    (l : Literal vars₁) (h₁ h₂ h₃) :
    ((c₁ ∪ {l}).convert vars₂ h₁) =
    (c₁.convert vars₂ h₂) ∪ {(l.convert vars₂ h₃)} := by
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

lemma subset_of_vars_clause (vars₁ vars₂) (c : Clause vars₁) (h : vars₁ ⊆ vars₂) :
    ∀ l ∈ c, l.variable ∈ vars₂ := by aesop

lemma inter_idea_new_version (vars sub_vars) (lit : Literal (vars \ sub_vars))
    (ρ : Assignment sub_vars) (c_1 c_2 : Clause (vars \ sub_vars))
    (inter_proof : Finset.disjUnion (vars \ sub_vars) sub_vars (Finset.sdiff_disjoint
      : Disjoint (vars \ sub_vars) sub_vars) = vars)
    (var_incl : lit.variable ∈ vars)
    (left : c_2 ⊆ c_1 ∪ {lit}) :
    ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ⊆
    ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ∪
      {lit.convert vars var_incl} := by
  have h_subset : sub_vars ⊆ vars := by aesop
  have : Clause.convert {lit} vars
      (by intro l h_l; have q := Literal.variable_mem_vars l; aesop) =
      {lit.convert vars var_incl} := by
    unfold Clause.convert
    simp only [Finset.mem_singleton]
    aesop
  rw [←this]
  have fact : (Finset.disjUnion (vars \ sub_vars) sub_vars
      (Finset.sdiff_disjoint : Disjoint (vars \ sub_vars) sub_vars)) = vars := by
    aesop
  unfold Clause.combine
  unfold Clause.convert_trivial
  simp only [carry_through_convert, Finset.union_assoc]
  apply Finset.union_subset
  swap
  · grind
  rw [←Finset.union_assoc]
  apply remove_middle_subset
  rw [this]
  have fact₁ : (vars \ sub_vars) ⊆ vars := by aesop
  have fact₂ : ∀ l ∈ c_2, l.variable ∈ vars := by
    exact fun l a ↦
      subset_of_vars_clause (vars \ sub_vars) vars (c_1 ∪ {lit}) fact₁ l (left a)
  have fact₃ : ∀ l ∈ c_1, l.variable ∈ vars := by
    exact fun l a ↦ subset_of_vars_clause (vars \ sub_vars) vars c_1 fact₁ l a
  have fact₄ : ∀ l ∈ (c_1 ∪ {lit}), l.variable ∈ vars := by
    exact fun l a ↦
      subset_of_vars_clause (vars \ sub_vars) vars (c_1 ∪ {lit}) fact₁ l a
  have fact₅ : ∀ l ∈ (c_1 ∪ {lit}), l.variable ∈ (vars \ sub_vars) := by
    exact fun l a ↦
      subset_of_vars_clause (vars \ sub_vars) (vars \ sub_vars) (c_1 ∪ {lit})
        (fun ⦃a⦄ a_1 ↦ a_1) l a
  have fact₅ : (lit).variable ∈ vars := by
    aesop
  trans c_2.convert vars fact₂
  · aesop
  trans ((c_1 ∪ {lit}).convert vars fact₄)
  · aesop
  have final_idea : ((lit).convert vars fact₅) = lit.convert vars var_incl := by
    aesop
  trans (c_1.convert  vars fact₃) ∪ {lit.convert vars var_incl}
  · trans (c_1.convert  vars fact₃) ∪ {((lit).convert vars fact₅)}
    · refine Finset.subset_of_eq ?_
      exact carry_through_convert_expl_lit (vars \ sub_vars) vars c_1 (lit) fact₄ fact₃ (by aesop)
    · aesop
  · aesop


lemma resolve_ineq (vars sub_vars) (φ : CNFFormula vars) (var : Variable)
    (ρ : Assignment sub_vars) (c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_subset : sub_vars ⊆ vars)
    (h_4 : var ∈ vars \ sub_vars) (h_0 : var ∉ c_1.variables)
    (p_1 : TreeLikeResolution (φ.substitute ρ) c_2)
    (p_2 : TreeLikeResolution (φ.substitute ρ) c_3)
    (left : c_2 ⊆ c_1 ∪ {var.toLiteral h_4})
    (right : c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4}) :
    Finset.card ((TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
    (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧
      c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute_rhs ρ h_subset) ≤
    max (Finset.card c_1) (max p_1.width p_2.width) + Finset.card sub_vars := by
  unfold TreeLikeResolution.unsubstitute_rhs
  simp
  have inter_proof : Finset.disjUnion (vars \ sub_vars) sub_vars (Finset.sdiff_disjoint :
    Disjoint (vars \ sub_vars) sub_vars) = vars := by
    aesop
  have var_incl : var ∈ vars := by
    grind
  have idea₁ : (p_1.unsubstitute_rhs ρ h_subset) ⊆
    (Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (inter_proof)
    := by
    exact TreeLikeResolution.unsubstitute_rhs_variables ρ p_1 h_subset
  have idea₂ : (p_2.unsubstitute_rhs ρ h_subset) ⊆
    (Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (inter_proof)
    := by
    exact TreeLikeResolution.unsubstitute_rhs_variables ρ p_2 h_subset

  trans Finset.card (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial
    vars inter_proof).resolve ((Clause.combine c_3 ρ.toClause
      Finset.sdiff_disjoint).convert_trivial vars inter_proof) var
        (Finset.sdiff_subset h_4 : var ∈ vars))

  · have inter_idea :
      ((p_1.unsubstitute_rhs ρ h_subset).resolve (p_2.unsubstitute_rhs ρ h_subset) var
        (Finset.sdiff_subset h_4 : var ∈ vars)) ⊆
      (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars
        inter_proof).resolve ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial
          vars inter_proof) var (Finset.sdiff_subset h_4 : var ∈ vars)) := by
      exact
        resolve_subsets var vars (p_1.unsubstitute_rhs ρ h_subset) (p_2.unsubstitute_rhs ρ h_subset)
          ((c_2.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof)
          ((c_3.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof)
          (Finset.sdiff_subset h_4) idea₁ idea₂

    exact Finset.card_le_card inter_idea
  trans Finset.card c_1 + Finset.card sub_vars
  swap
  · simp_all only [add_le_add_iff_right, le_sup_left]
  trans Finset.card ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars
    inter_proof)
  swap
  · exact card_combination c_1
  have temp₁ : Finset.disjUnion (vars \ sub_vars) sub_vars
      (Finset.sdiff_disjoint : Disjoint (vars \ sub_vars) sub_vars) = vars := by
    aesop

  have idea₃ :
      ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ⊆
      ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ∪
        {var.toLiteral var_incl} := by
    exact inter_idea_new_version vars sub_vars (var.toLiteral h_4) ρ c_1 c_2 inter_proof
      var_incl left

  have idea₄ :
    ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ⊆
    ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ∪
      {var.toNegLiteral var_incl} := by
    exact inter_idea_new_version vars sub_vars (var.toNegLiteral h_4) ρ c_1 c_3 inter_proof
      var_incl right

  simp only [ge_iff_le]

  apply resolve_subsets_trick var vars
    ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars temp₁)
    ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars temp₁)
    ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars temp₁)
    (by grind) idea₃ idea₄


lemma resolve_width_case (vars sub_vars) (φ : CNFFormula vars) (var : Variable)
    (ρ : Assignment sub_vars) (c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_subset : sub_vars ⊆ vars)
    (h_4 : var ∈ vars \ sub_vars) (h_0 : var ∉ c_1.variables)
    (p_1 : TreeLikeResolution (φ.substitute ρ) c_2)
    (p_2 : TreeLikeResolution (φ.substitute ρ) c_3)
    (c₁ c₂ : Clause vars)
    (π₁ : TreeLikeResolution φ c₁)
    (π₂ : TreeLikeResolution φ c₂)
    (left : c_2 ⊆ c_1 ∪ {var.toLiteral h_4})
    (right : c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})
    (v : Variable)
    (h_v_mem_vars : v ∈ vars)
    (h_v_not_mem_c : v ∉ ((TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
      (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧ c_3 ⊆ c_1 ∪
      {var.toNegLiteral h_4})).unsubstitute_rhs ρ h_subset).variables)
    (left_1 : c₁ ⊆ (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
      (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧
      c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute_rhs ρ h_subset ∪ {v.toLiteral h_v_mem_vars})
    (right_1 : c₂ ⊆
      (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
      (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧
        c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute_rhs ρ h_subset ∪
      {v.toNegLiteral h_v_mem_vars})
    (heq : (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
      (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧
        c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute ρ h_subset =
      TreeLikeResolution.resolve c₁ c₂ v h_v_mem_vars h_v_not_mem_c π₁ π₂
        (⟨left_1, right_1⟩ : c₁ ⊆ (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
        (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧
          c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute_rhs ρ
            h_subset ∪ {v.toLiteral h_v_mem_vars} ∧ c₂ ⊆
      (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2 (⟨left, right⟩ :
        c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧ c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute_rhs ρ
          h_subset ∪ {v.toNegLiteral h_v_mem_vars}))
    (h_2 : (p_1.unsubstitute ρ h_subset).width ≤ p_1.width + Finset.card sub_vars)
    (h_3 : (p_2.unsubstitute ρ h_subset).width ≤ p_2.width + Finset.card sub_vars) :
    (π₁.width ≤ max (Finset.card c_1) (max p_1.width p_2.width) + Finset.card sub_vars) ∧
      (π₂.width ≤ max (Finset.card c_1) (max p_1.width p_2.width) + Finset.card sub_vars)
    := by

    constructor

    · trans p_1.width + Finset.card sub_vars
      swap
      · simp
      trans (p_1.unsubstitute ρ h_subset).width
      swap
      · exact h_2
      unfold TreeLikeResolution.unsubstitute at heq
      simp at heq
      obtain ⟨heq₁, heq₂, heq₃, heq₄, heq₅⟩ := heq
      subst heq₁ heq₂ heq₃
      simp_all only [heq_eq_eq, Finset.union_singleton, le_refl]

    · trans p_2.width + Finset.card sub_vars
      swap
      · simp
      trans (p_2.unsubstitute ρ h_subset).width
      swap
      · exact h_3
      unfold TreeLikeResolution.unsubstitute at heq
      simp at heq
      obtain ⟨heq₁, heq₂, heq₃, heq₄, heq₅⟩ := heq
      subst heq₁ heq₂ heq₃
      simp_all only [heq_eq_eq, Finset.union_singleton, le_refl]



lemma induction_step_width_incr {vars sub_vars} {φ : CNFFormula vars} {var : Variable}
    {ρ : Assignment sub_vars} (c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_subset : sub_vars ⊆ vars)
    (h_4 : var ∈ vars \ sub_vars) (h_0 : var ∉ c_1.variables)
    (p_1 : TreeLikeResolution (φ.substitute ρ) c_2)
    (p_2 : TreeLikeResolution (φ.substitute ρ) c_3)
    (h_1 : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧ c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})
    (h_2 : (p_1.unsubstitute ρ h_subset).width ≤ p_1.width + Finset.card sub_vars)
    (h_3 : (p_2.unsubstitute ρ h_subset).width ≤ p_2.width + Finset.card sub_vars) :
    ((TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2 h_1).unsubstitute ρ h_subset).width ≤
    (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2 h_1).width + Finset.card sub_vars := by
  unfold TreeLikeResolution.width
  obtain ⟨left, right⟩ := h_1
  split
  next x x_1 h_c_in_φ heq =>
    exact resolve_ineq vars sub_vars φ var ρ c_1 c_2 c_3 h_subset h_4 h_0 p_1 p_2 left right
  next x x_1 c₁ c₂ v h_v_mem_vars π₁ π₂ h_v_not_mem_c h_resolve
    heq =>
    simp_all only [sup_le_iff]
    obtain ⟨left_1, right_1⟩ := h_resolve
    apply And.intro
    · exact resolve_ineq vars sub_vars φ var ρ c_1 c_2 c_3 h_subset h_4 h_0 p_1 p_2 left right
    · apply resolve_width_case vars sub_vars φ
          var ρ c_1 c_2 c_3 h_subset h_4 h_0 p_1
          p_2 c₁ c₂ π₁ π₂ left right v h_v_mem_vars h_v_not_mem_c
          left_1 right_1 heq h_2 h_3



lemma unsub_increase_width {vars sub_vars} {φ : CNFFormula vars}
    {ρ : Assignment sub_vars} (c : Clause (vars \ sub_vars))
    (π : TreeLikeResolution (φ.substitute ρ) c) (h_subset : sub_vars ⊆ vars) :
    (π.unsubstitute ρ h_subset).width ≤ π.width + sub_vars.card := by
  induction π
  case axiom_clause C h =>
    unfold TreeLikeResolution.unsubstitute
    simp_all only
    unfold TreeLikeResolution.width
    trans ((Clause.combine C ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)).card
    · refine Finset.card_le_card ?_
      · exact TreeLikeResolution.unsubstitute_rhs_variables ρ
          (TreeLikeResolution.axiom_clause h) h_subset
    exact card_combination C
  case resolve c_1 c_2 c_3 var h_4 h_0 p_1 p_2 h_1 h_2 h_3 =>
    exact induction_step_width_incr c_1 c_2 c_3 h_subset h_4 h_0 p_1 p_2 h_1 h_2 h_3


lemma var_unsub_increase_width {vars} {φ : CNFFormula vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ : Assignment {x.variable}) (c : Clause (vars \ {x.variable}))
    (π : TreeLikeResolution (φ.substitute ρ) c) :
    (π.unsubstitute ρ (by exact Finset.singleton_subset_iff.mpr h₀)).width ≤ π.width + 1 := by
  have : {x.variable} ⊆ vars := by
    exact Finset.singleton_subset_iff.mpr h₀
  trans π.width + ({x.variable} : Finset Variable).card
  · exact unsub_increase_width c π (Finset.singleton_subset_iff.mpr h₀)
  · exact Nat.le_refl (π.width + ({x.variable} : Finset Variable).card)

-- Managed to vibe code it succesfully!

lemma width_closure {vars} (φ₁ φ₂ : CNFFormula vars) (W : ℕ) (C_0 : Clause vars)
    (h_all : ∀ C ∈ φ₂, ∃ (π : TreeLikeResolution φ₁ C), π.width ≤ W)
    (h_once : ∃ (π_1 : TreeLikeResolution φ₂ C_0), π_1.width ≤ W) :
    ∃ π' : TreeLikeResolution φ₁ C_0, π'.width  ≤ W := by

  obtain ⟨π₁, hπ₁⟩ := h_once

  -- 1. Extract the "Subtype" (Tree + Proof) for every axiom
  let T2_with_bound : ∀ {C}, C ∈ φ₂ → { π : TreeLikeResolution φ₁ C // π.width ≤ W } :=
    fun hC => ⟨Classical.choose (h_all _ hC), Classical.choose_spec (h_all _ hC)⟩

  -- 2. Define the recursive grafting
  let rec graft {c : Clause vars} (π : TreeLikeResolution φ₂ c) :
    { P : TreeLikeResolution φ₁ c // P.width ≤ max (π.width) W } :=
    match π with
    | .axiom_clause h_in =>
        let ⟨sub_tree, h_sub_w⟩ := T2_with_bound h_in
        ⟨sub_tree, by
          -- Logic: width π is just c.size here.
          -- Since c is an axiom, width sub_tree ≤ W, so width ≤ max(c.size, W)
          aesop ⟩

    | .resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
        let ⟨P₁, hP₁⟩ := graft π₁
        let ⟨P₂, hP₂⟩ := graft π₂
        let P_final := TreeLikeResolution.resolve c₁ c₂ v h_v_mem h_v_not P₁ P₂ h_res
        ⟨P_final, by
          -- Logic: width P_final is max(c.size, width P₁, width P₂)
          -- Use hP₁ and hP₂ to show this is ≤ max (width T1) W
          unfold TreeLikeResolution.width
          simp
          grind⟩

  -- Execute the recursion on T1 to produce the final proof P
  let X := graft π₁

  obtain ⟨π₁', hπ₁'⟩ := X
  use π₁'
  aesop


lemma trivial_subs_unfold {vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : ρ_true = (fun _ _ => (x.polarity : Bool)))
    (h_1 : ∀ l ∈ ρ_true.toClause, l.variable ∈ vars) :
    (ρ_true.toClause).convert vars h_1 = ({x.negate} : Clause vars) := by
  cases x
  case neg v_1 hv =>
    have idea_2 : ρ_true (Literal.pos v_1 hv).variable (by aesop) = false := by
      aesop
    unfold Assignment.toClause
    unfold Clause.convert
    unfold Assignment.negVariable
    aesop
  case pos v_1 hv =>
    have idea_2 : ρ_true (Literal.pos v_1 hv).variable (by aesop) = true := by
      aesop
    unfold Assignment.toClause
    unfold Clause.convert
    unfold Assignment.negVariable
    aesop



lemma ufold_one_literal {vars} {φ : CNFFormula vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : ρ_true = (fun _ _ => (x.polarity : Bool)))
    (π_1 : TreeLikeRefutation (φ.substitute ρ_true))
    (fact₀ : {x.variable} ⊆ vars) :
    (TreeLikeResolution.unsubstitute_rhs ρ_true π_1 fact₀) ⊆ ({x.negate} : Clause vars) := by

  unfold TreeLikeRefutation at π_1

  have trick :  Finset.disjUnion (vars \ {x.variable}) {x.variable}
      (Finset.sdiff_disjoint : Disjoint (vars \ {x.variable}) {x.variable}) = vars := by
    aesop

  have : (π_1.unsubstitute_rhs ρ_true fact₀) ⊆
      (Clause.combine (BotClause (vars \ {x.variable})) ρ_true.toClause
      Finset.sdiff_disjoint).convert_trivial vars trick := by
    exact TreeLikeResolution.unsubstitute_rhs_variables ρ_true π_1 fact₀

  trans ((BotClause (vars \ {x.variable})).combine ρ_true.toClause
    (Finset.sdiff_disjoint : Disjoint (vars \ {x.variable}) {x.variable})).convert_trivial
    vars trick

  · exact this

  have trick₁ : ∀ l ∈ ρ_true.toClause, l.variable ∈ vars := by
    aesop

  have idea : (ρ_true.toClause).convert vars trick₁ = ({x.negate} : Clause vars):= by
    exact trivial_subs_unfold x h₀ ρ_true h_value trick₁

  rw[<-idea]

  unfold BotClause

  unfold Clause.combine
  simp
  unfold Clause.convert_trivial
  aesop


def convert_proof (W : ℕ) {vars₁ vars₂ : Variables} {φ : CNFFormula vars₁} {C : Clause vars₁}
  {φ₁ : CNFFormula vars₂} (h_subs : vars₁ ⊆ vars₂)
  (h_conv : (CNFFormula.simple_convert vars₁ vars₂ φ h_subs) = φ₁)
  (π₁ : TreeLikeResolution φ C)
  (h_width : π₁.width ≤ W) :
  { π₂ : TreeLikeResolution φ₁
  (C.convert vars₂ (by exact fun l a ↦
    subset_of_vars_clause vars₁ vars₂ C h_subs l a)) // π₂.width ≤ W } :=

  have idea : ∀ c : Clause vars₁, (∀ l ∈ c, l.variable ∈ vars₂) := by
    intro c l a
    subst h_conv
    apply h_subs
    simp_all only [Literal.variable_mem_vars]


  have idea' : Finset.card C ≤ W := by
    induction π₁
    · subst h_conv
      exact h_width
    rename_i h_resolve π₁_ih π₂_ih
    subst h_conv
    obtain ⟨left, right⟩ := h_resolve
    unfold TreeLikeResolution.width at h_width
    simp_all only [Finset.union_singleton, sup_le_iff]

  match π₁ with
  -- CASE 1: The proof is just an axiom
  | .axiom_clause h_in =>
      let C_new := C.convert vars₂ (by exact fun l a ↦ idea C l a)
        have : C_new ∈ φ₁ := by
          rw[<-h_conv]
          unfold CNFFormula.simple_convert
          aesop
        let π₂ := TreeLikeResolution.axiom_clause (by
        -- Prove that C_new is in the converted formula
        -- This follows from the definition of CNFFormula.simple_convert
          exact this)
        ⟨π₂, by
        -- Width of an axiom is the size of the clause.
        -- Since convert doesn't change the number of literals, width remains the same.
          unfold TreeLikeResolution.width
          aesop ⟩

  -- CASE 2: The proof is a resolution step
  | .resolve c₁ c₂ v h_v_mem h_v_not π_a π_b h_res =>
      -- 1. Recursively convert the sub-proofs
      -- (You need to split the width bound h_width into bounds for π_a and π_b)
      have idea₁ : π_a.width ≤ W := by
        unfold TreeLikeResolution.width at h_width
        subst h_conv
        simp_all only [Finset.union_singleton, sup_le_iff, true_and]
      have idea₂ : π_b.width ≤ W := by
        unfold TreeLikeResolution.width at h_width
        subst h_conv
        simp_all only [Finset.union_singleton, sup_le_iff, true_and]

      let ⟨π_a_new, h_wa⟩ := convert_proof W h_subs h_conv π_a idea₁
        -- width π₁ = max |C| (max (width π_a) (width π_b)), so width π_a ≤ width π₁


      let ⟨π_b_new, h_wb⟩ := convert_proof W h_subs h_conv π_b idea₂

      -- 2. Lift the resolution variable to the new context
      let v_new_mem := h_subs h_v_mem

      have fact₁ : ∀ l ∈ c₁, l.variable ∈ vars₂ := by
        exact fun l a ↦ idea c₁ l a

      have fact₂ : ∀ l ∈ c₂, l.variable ∈ vars₂ := by
        exact fun l a ↦ idea c₂ l a

      have fact₀ :  ∀ l ∈ C, l.variable ∈ vars₂ := by
        exact fun l a ↦ idea C l a

      have fact₄ : v ∉ (C.convert vars₂ fact₀).variables := by
        aesop

      have left : c₁ ⊆ C ∪ {v.toLiteral h_v_mem} := by
        exact h_res.left

      have right : c₂ ⊆ C ∪ {v.toNegLiteral h_v_mem} := by
        exact h_res.right

      have h_resolve : c₁.convert vars₂ fact₁ ⊆ C.convert vars₂ fact₀ ∪ {v.toLiteral v_new_mem} ∧
        c₂.convert vars₂ fact₂ ⊆ C.convert vars₂ fact₀ ∪ {v.toNegLiteral v_new_mem} := by
        have incl₁ : ∀ l ∈ C ∪ {v.toLiteral h_v_mem}, l.variable ∈ vars₂ := by
          exact fun l a ↦ idea (C ∪ {v.toLiteral h_v_mem}) l a
        have incl₂ : ∀ l ∈ ({v.toLiteral h_v_mem} : Clause vars₁), l.variable ∈ vars₂ := by
          exact fun l a ↦ idea {v.toLiteral h_v_mem} l a
        constructor
        · trans (C ∪ ({v.toLiteral h_v_mem} : Clause vars₁)).convert vars₂ incl₁
          · exact loose_convert c₁ (C ∪ {v.toLiteral h_v_mem}) left
          trans C.convert vars₂ fact₀ ∪ ({v.toLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂
          · have new₁ : (C ∪ {v.toLiteral h_v_mem}).convert vars₂ incl₁ = C.convert vars₂ fact₀ ∪
                ({v.toLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂ := by
              exact carry_through_convert_expl vars₁ vars₂ C ({v.toLiteral h_v_mem} : Clause vars₁)
                incl₁ fact₀ incl₂
            exact Finset.subset_of_eq new₁
          · have new₂ : ({v.toLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂ =
                {v.toLiteral v_new_mem} := by
              unfold Clause.convert
              simp
              subst h_conv
              simp_all only [Clause.convert_keeps_variables, not_false_eq_true,
                Finset.union_singleton, Finset.mem_insert, forall_eq_or_imp, Finset.mem_singleton,
                implies_true, and_self]
              obtain ⟨left_1, right_1⟩ := h_res
              ext a : 1
              simp_all only [Finset.mem_filterMap, Finset.mem_singleton,
                Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self, exists_prop_eq]
              apply Iff.intro
              · intro a_1
                subst a_1
                rfl
              · intro a_1
                subst a_1
                rfl

            rw [new₂]

        have incl₁ : ∀ l ∈ C ∪ {v.toNegLiteral h_v_mem}, l.variable ∈ vars₂ := by
          exact fun l a ↦ idea (C ∪ {v.toNegLiteral h_v_mem}) l a
        have incl₂ : ∀ l ∈ ({v.toNegLiteral h_v_mem} : Clause vars₁), l.variable ∈ vars₂ := by
          exact fun l a ↦ idea {v.toNegLiteral h_v_mem} l a
        trans (C ∪ ({v.toNegLiteral h_v_mem} : Clause vars₁)).convert vars₂ incl₁
        · exact loose_convert c₂ (C ∪ {v.toNegLiteral h_v_mem}) right
        trans C.convert vars₂ fact₀ ∪ ({v.toNegLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂
        · have new₁ : (C ∪ {v.toNegLiteral h_v_mem}).convert vars₂ incl₁ = C.convert vars₂ fact₀ ∪
              ({v.toNegLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂ := by
            exact carry_through_convert_expl vars₁ vars₂ C
              ({v.toNegLiteral h_v_mem} : Clause vars₁) incl₁ fact₀  incl₂
          subst h_conv
          simp_all only [Clause.convert_keeps_variables, not_false_eq_true, Finset.union_singleton,
            subset_refl]
        have new₂ : ({v.toNegLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂ =
            {v.toNegLiteral v_new_mem} := by
          unfold Clause.convert
          simp
          subst h_conv
          simp_all only [Clause.convert_keeps_variables, not_false_eq_true, Finset.union_singleton,
            Finset.mem_insert, forall_eq_or_imp, Finset.mem_singleton, implies_true, and_self]
          obtain ⟨left_1, right_1⟩ := h_res
          ext a : 1
          simp_all only [Finset.mem_filterMap, Finset.mem_singleton, Option.dite_none_right_eq_some,
            Option.some.injEq, and_exists_self, exists_prop_eq]
          apply Iff.intro
          · intro a_1
            subst a_1
            rfl
          · intro a_1
            subst a_1
            rfl
        rw [new₂]


      -- 3. Construct the new resolution node
      let π_new := TreeLikeResolution.resolve
        (c₁.convert vars₂ fact₁)
        (c₂.convert vars₂ fact₂)
        v v_new_mem fact₄ π_a_new π_b_new h_resolve

      ⟨π_new, by
        -- width is max of |C_new| and the sub-widths.
        -- All these are ≤ W because the original ones were.
        unfold TreeLikeResolution.width
        subst h_conv
        simp_all only [Finset.union_singleton, convert_card, sup_le_iff, and_self]⟩

-- Tried to vibe code this one - ended up horribly...

lemma width_respect_convert (vars₁ vars₂) (φ : CNFFormula vars₁)
   (φ₁ : CNFFormula vars₂) (h_subs : vars₁ ⊆ vars₂)
   (h_conv : (CNFFormula.simple_convert vars₁ vars₂ φ h_subs) = φ₁)
   (W : ℕ) (C : Clause vars₁)
   (π_1 : TreeLikeResolution φ C) (h_width_true : π_1.width ≤ W)
   (int_proof : ∀ l ∈ C, l.variable ∈ vars₂) :
   ∃ (π_2 : TreeLikeResolution φ₁ (C.convert vars₂ int_proof)), π_2.width ≤ W  := by
  let ⟨π, h⟩ := convert_proof W h_subs h_conv π_1 h_width_true
  exact ⟨π, h⟩

-- def convert_proof_substitution {vars₁ vars₂ : Finset Variable}
--     {φ : CNFFormula vars₂}
--     (ρ : Assignment vars₁)
--     (h_subs : vars₁ ⊆ vars₂)
--     (π : TreeLikeResolution φ (BotClause vars₂)) :
--     TreeLikeResolution (φ.substitute ρ) (BotClause (vars₂ \ vars₁)) :=

--   match π with
--   | .axiom_clause h_in =>
--     have : (BotClause (vars₂ \ vars₁)) ∈ (φ.substitute ρ) := by
--       unfold CNFFormula.substitute
--       simp
--       aesop
--     let π₂ := TreeLikeResolution.axiom_clause (by
--     -- Prove that C_new is in the converted formula
--     -- This follows from the definition of CNFFormula.simple_convert
--       exact this)
--     π₂
--   | .resolve c₁ c₂ v h_v_mem h_v_not_mem π₁ π₂ h_res =>
--       -- Here you handle whether 'v' was substituted by 'ρ' or not
--       let π_new := TreeLikeResolution.resolve
--         (c₁.substitute ρ)
--         (c₂.substitute ρ)
--         v v_new_mem fact₄ π_a_new π_b_new h_resolve
--       π_new












-- This lemma was partially vibe-coded

lemma substitute_second_trivial_property {vars}
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
    (h_C_2_conv : C_2 ∈ φ ∧ C_2.substitute ρ_false = some C_1)
    : C_0 ⊆ C_2 := by

  -- 1. Take an arbitrary literal in C_0
  intro l hl

  -- 2. Unfold the conversion of C_1 to C_0
  -- h_C_1_conv_right : C_1.convert vars h_incl = C_0
  rw [← h_C_1_conv_right] at hl

  -- 3. Since l ∈ C_1.convert, there must be a source literal l' ∈ C_1
  -- You'll likely need to unfold Clause.convert or use a lemma like 'mem_convert'
  unfold Clause.convert at hl
  simp only [Finset.mem_filterMap] at hl
  rcases hl with ⟨l_orig, hl_orig_in, h_l_eq⟩
  -- h_l_eq tells us that l is just the converted version of l_orig

  -- 4. Now look at the substitution: C_2.substitute ρ_false = some C_1
  have h_sub := h_C_2_conv.right
  unfold Clause.substitute at h_sub

  -- 5. Handle the match/split logic
  generalize h_split : Clause.split C_2 {x.variable} = split_res at h_sub
  rcases split_res with ⟨c_in, c_out⟩

  split at h_sub
  next c_in c_out prop C_xx =>
  split_ifs at h_sub with h_eval

  · injection h_sub with h_c_out_eq

    -- 6. Connect l_orig (in C_1) to C_2
    -- Since C_1 = c_out, l_orig is in c_out
    rw [← h_c_out_eq] at hl_orig_in

    unfold Clause.split at h_split

    simp at h_split
    subst h_value_false h_C_1_conv_right h_c_out_eq
    simp_all only [Prod.mk.injEq, Bool.not_eq_true, Bool.decide_eq_false, ↓reduceDIte,
      Option.some.injEq]
    subst h_l_eq
    obtain ⟨fst, snd⟩ := c_in
    obtain ⟨left, right⟩ := C_xx
    obtain ⟨left_1, right_1⟩ := h_split
    obtain ⟨left_2, right_2⟩ := h_C_2_conv
    subst left right left_1 right_1

    unfold Literal.convert
    split
    next l h_mem v h_v_mem_vars h_mem_1 =>
      unfold Clause.shrink at hl_orig_in
      simp at hl_orig_in
      obtain ⟨w, h⟩ := hl_orig_in
      obtain ⟨w_1, h⟩ := h
      obtain ⟨left, right⟩ := w_1
      have : Literal.pos v h_mem_1 = w := by
        unfold Literal.restrict at h
        split at h
        next l_1 h_mem_2 v_1 h_v_mem_vars_1 h_mem_3 =>
          simp_all only [Finset.mem_sdiff, Literal.variable_mem_vars, Finset.mem_singleton,
            true_and, Literal.pos.injEq]
        next l_1 h_mem_2 v_1 h_v_mem_vars_1 h_mem_3 =>
          simp_all only [Finset.mem_sdiff, Literal.variable_mem_vars, Finset.mem_singleton,
            true_and, reduceCtorEq]
      subst this
      simp_all only
    next l h_mem v h_v_mem_vars h_mem_1 =>
      unfold Clause.shrink at hl_orig_in
      simp at hl_orig_in
      obtain ⟨w, h⟩ := hl_orig_in
      obtain ⟨w_1, h⟩ := h
      obtain ⟨left, right⟩ := w_1
      have : Literal.neg v h_mem_1 = w := by
        unfold Literal.restrict at h
        split at h
        next l_1 h_mem_2 v_1 h_v_mem_vars_1 h_mem_3 =>
          simp_all only [Finset.mem_sdiff, Literal.variable_mem_vars, Finset.mem_singleton,
            true_and, reduceCtorEq]
        next l_1 h_mem_2 v_1 h_v_mem_vars_1 h_mem_3 =>
          simp_all only [Finset.mem_sdiff, Literal.variable_mem_vars, Finset.mem_singleton,
            true_and, Literal.neg.injEq]
      subst this
      simp_all only

-- Gemini generated this lemma

lemma var_mem_of_literal_mem {v_set} (l : Literal v_set) :
  l.variable ∈ v_set := by
  cases l <;> simp [Literal.variable, *]



lemma width_combine (vars) {φ : CNFFormula vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : ρ_true = (fun _ _ => (x.polarity : Bool)))
    (ρ_false : (Assignment ({x.variable} : Finset Variable)))
    (h_value_false : ρ_false = (fun _ _ => (¬x.polarity : Bool)))
    (W : ℕ) (π_1 : TreeLikeRefutation (φ.substitute ρ_true)) (h_width_true : π_1.width ≤ W)
    (π_2 : TreeLikeRefutation (φ.substitute ρ_false)) (h_width_false : π_2.width ≤ W + 1)
    (h_clause_card : ∀ C ∈ φ, C.card ≤ W + 1) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W + 1 := by

  have fact₀ : {x.variable} ⊆ vars := by
    exact Finset.singleton_subset_iff.mpr h₀

  let π_1_unfolded := TreeLikeResolution.unsubstitute ρ_true π_1 fact₀

  have idea₀ : (TreeLikeResolution.unsubstitute_rhs ρ_true π_1 fact₀) ⊆ ({x.negate}) := by
    exact ufold_one_literal x h₀ ρ_true h_value π_1 fact₀


  have idea₁ : π_1_unfolded.width ≤ W + 1 := by
    trans π_1.width + ({x.variable} : Finset Variable).card
    · exact unsub_increase_width (BotClause (vars \ {x.variable})) π_1 fact₀
    trans TreeLikeResolution.width π_1 + 1
    · exact Nat.le_refl (TreeLikeResolution.width π_1 + ({x.variable} : Finset Variable).card)
    · exact Nat.add_le_add_right h_width_true 1



  have fact₁ : (C : Clause (vars \ {x.variable})) -> (∀ l ∈ C, l.variable ∈ vars) := by
    intro C l h'
    have : l.variable ∈ (vars \ {x.variable}) := by
      exact subset_of_vars_clause (vars \ {x.variable}) (vars \ {x.variable}) C
        (fun ⦃a⦄ a_1 ↦ a_1) l h'
    simp_all only [Literal.variable_mem_vars, Finset.mem_sdiff, Finset.mem_singleton, π_1_unfolded]


  let vars₁ := (vars \ {x.variable})

  let φ_subs_false_unconv := (φ.substitute ρ_false)

  have h_subs : vars₁ ⊆ vars := by
    exact Finset.sdiff_subset

  let φ_subs_false_conv := (CNFFormula.simple_convert
      vars₁ vars (φ_subs_false_unconv) h_subs)

  -- 2. Change the type of π_1 in the context
  change TreeLikeResolution φ_subs_false_unconv (BotClause vars₁) at π_2

  -- 3. If you want the width bound to reflect the new name as well:
  --change π_1.width ≤ W at h_width_false

  --by_cases (TreeLikeResolution.unsubstitute_rhs ρ_true π_1 fact₀) = ({x.negate})
  have h_cases := Finset.subset_singleton_iff.mp idea₀
  rcases h_cases with h_empty | h_eq
  · -- Case 1: The set is empty
  -- h_empty : TreeLikeResolution.unsubstitute_rhs ... = ∅
    -- cast(by rw [h_empty] at π_1_unfolded)
    -- let answ :  TreeLikeRefutation φ := π_1_unfolded
    -- use answ
    -- 1. Transport the proof A along the equality h_1
    let π_refutation : TreeLikeRefutation φ := cast (by rw [h_empty]) π_1_unfolded
    -- 2. Prove that the width is preserved
    -- Since h_1 is C = ∅, transport doesn't change the physical
    -- nodes of the tree, so the width is identical.
    have h_width :  π_refutation.width ≤ W + 1:= by
      -- We use 'subst' to replace C with ∅ in the goal,
      -- making π_refutation definitionally equal to A.
      subst h_value
      grind


  -- 3. Package it into the existential
    exact ⟨π_refutation, h_width⟩

  · -- Case 2: The set is the singleton
  -- h_eq : TreeLikeResolution.unsubstitute_rhs ... = {x.negate}
    have idea₂ : ∀ C ∈ φ_subs_false_conv, ∃ (π : TreeLikeResolution φ C), π.width ≤ W + 1:= by

      intro C_0 h_c
      have entry₁ : ∃ C_1 ∈ φ_subs_false_unconv,
          (C_1.convert vars (by exact fun l a ↦ fact₁ C_1 l a)) = C_0 := by
        -- unfold φ_subs_false_unconv
        -- unfold φ_subs_false_conv at h_c
        unfold φ_subs_false_conv CNFFormula.simple_convert at h_c
        -- 2. Use the 'mem_image' lemma to turn membership into an existential
        -- 'h_c' is C_0 ∈ (φ_subs_false_unconv.image (fun c => c.convert ...))
        rw [Finset.mem_image] at h_c
        -- 3. Extract the witness and the properties
        -- h_c becomes: ∃ C_1 ∈ φ_subs_false_unconv, C_1.convert ... = C_0
        rcases h_c with ⟨C_1, h_C1_in, h_eq⟩
        -- 4. Satisfy the goal
        use C_1

      obtain ⟨C_1, h_C_1_conv⟩ := entry₁
      obtain ⟨h_C_1_conv_left, h_C_1_conv_right⟩ := h_C_1_conv

      have entry₂ : ∃ C_2 ∈ φ, (C_2.substitute ρ_false) = C_1 := by
        unfold CNFFormula.substitute at h_C_1_conv_left

        -- 2. Use mem_filterMap to show that C_1 came from a 'some C_1' in the intermediate set
        -- Intermediate set: (φ.image (fun c => c.substitute ρ_false))
        unfold φ_subs_false_unconv at h_C_1_conv_left
        unfold CNFFormula.substitute at h_C_1_conv_left
        rw [Finset.mem_filterMap] at h_C_1_conv_left
        -- This gives: ∃ o ∈ φ.image (fun c => c.substitute ρ_false), id o = some C_1
        rcases h_C_1_conv_left with ⟨o, h_o_in, h_o_eq⟩
        simp at h_o_eq -- This makes it: o = some C_1

        -- 3. Use mem_image to find the original clause C_2 in φ
        rw [Finset.mem_image] at h_o_in
        -- This gives: ∃ C_2 ∈ φ, (fun c => c.substitute ρ_false) C_2 = o
        rcases h_o_in with ⟨C_2, h_C2_in, h_sub_eq⟩

        -- 4. Combine the results
        use C_2
        constructor
        · exact h_C2_in
        · rw [h_sub_eq, h_o_eq]
      obtain ⟨C_2, h_C_2_conv⟩ := entry₂


      have idea₂ : C_2 ⊆ C_0 ∪ ({x} : Clause vars) := by
        exact
          substitute_trivial_property φ x C_0 h_subs ρ_false h_value_false h_c C_1
            h_C_1_conv_left (fun l a ↦ fact₁ C_1 l a) h_C_1_conv_right C_2 h_C_2_conv

      have this_1 : C_0 ⊆ C_2 := by
          exact
          substitute_second_trivial_property φ x C_0 h_subs ρ_false h_value_false h_c C_1
            h_C_1_conv_left (fun l a ↦ fact₁ C_1 l a) h_C_1_conv_right C_2 h_C_2_conv

      obtain ⟨left, right⟩ := h_C_2_conv
      -- have idea₃ : (C_0 = C_2 \ ({x} : Clause vars)) := by
      --   sorry

      have h_v_not_mem_c : x.variable ∉ C_0.variables := by
        have h_prep : x.variable ∉ C_1.variables := by
          intro h_mem
          rcases Finset.mem_image.1 h_mem with ⟨l, _, hl_eq⟩
          have h_in := var_mem_of_literal_mem l
          rw [hl_eq] at h_in
          simp at h_in
        subst h_value h_value_false h_C_1_conv_right
        simp_all


      have temp_fix₁ : x.variable ∈ vars := by
        subst h_value h_value_false h_C_1_conv_right
        simp_all only [Literal.variable_mem_vars, subset_refl, Bool.not_eq_true,
          Bool.decide_eq_false, Finset.union_singleton, Clause.convert_keeps_variables,
          π_1_unfolded, φ_subs_false_unconv, φ_subs_false_conv, vars₁]


      let π_new : TreeLikeResolution φ {x.negate} := h_eq ▸ π_1_unfolded
      unfold π_1_unfolded at idea₁
      have idea_new : π_new.width ≤ W + 1 := by grind

      induction x with
      | pos v h_val =>
        have temp_fix₂ : C_2 ⊆ C_0 ∪ {v.toLiteral temp_fix₁} ∧
            {Literal.neg v h_val} ⊆ C_0 ∪ {v.toNegLiteral temp_fix₁} := by
          constructor
          · exact idea₂
          subst h_value h_value_false h_C_1_conv_right
          simp_all
          apply Or.inl
          rfl
        let π_ans : TreeLikeResolution φ C_0 := TreeLikeResolution.resolve C_2
          ({(Literal.neg v h_val)} : Clause vars) v temp_fix₁ h_v_not_mem_c
          (TreeLikeResolution.axiom_clause left) (π_new) temp_fix₂
        use π_ans
        unfold TreeLikeResolution.width
        have : C_0.card = C_1.card := by
          subst h_value h_value_false h_C_1_conv_right
          simp_all
        have : C_1.card ≤ W + 1 := by
          rw [<-this]
          trans C_2.card
          · expose_names
            exact Finset.card_le_card this_1
          · exact h_clause_card C_2 left
        aesop
      | neg v h_val =>
        have temp_fix₂ : {Literal.pos v h_val} ⊆ C_0 ∪ {v.toLiteral temp_fix₁} ∧
            C_2 ⊆ C_0 ∪ {v.toNegLiteral temp_fix₁}:= by
          constructor
          · subst h_value h_value_false h_C_1_conv_right
            simp_all
            apply Or.inl
            rfl
          exact idea₂
        let π_ans : TreeLikeResolution φ C_0 := TreeLikeResolution.resolve {Literal.pos v h_val}
          C_2 v temp_fix₁ h_v_not_mem_c (π_new) (TreeLikeResolution.axiom_clause left) temp_fix₂
        use π_ans
        unfold TreeLikeResolution.width
        have : C_0.card = C_1.card := by
          subst h_value h_value_false h_C_1_conv_right
          simp_all
        have : C_1.card ≤ W + 1 := by
          rw [<-this]
          trans C_2.card
          · expose_names
            exact Finset.card_le_card this_1
          · exact h_clause_card C_2 left
        aesop

    have idea₃ :
        ∃ (π : TreeLikeResolution φ_subs_false_conv (BotClause (vars))), π.width ≤ W + 1 := by
      let φ₁ : CNFFormula vars := (CNFFormula.simple_convert vars₁ vars φ_subs_false_unconv h_subs)
      have idea_subs : φ_subs_false_conv = φ₁ := by
        subst h_value
        simp_all only [Literal.variable_mem_vars, Bool.not_eq_true, Bool.decide_eq_false,
          subset_refl, φ_subs_false_conv, vars₁, φ_subs_false_unconv, π_1_unfolded, φ₁]
      have int_proof : ∀ l ∈ BotClause vars₁, l.variable ∈ vars := by
        intro l a
        subst h_value
        simp_all only [Literal.variable_mem_vars, Finset.notMem_empty, φ_subs_false_conv, vars₁,
          φ_subs_false_unconv, φ₁]
      have Bot_equiv : ((BotClause vars₁).convert vars int_proof) = BotClause vars := by
        subst h_value
        simp_all only [Literal.variable_mem_vars, Bool.not_eq_true, Bool.decide_eq_false,
          subset_refl, Clause.convert_empty, φ_subs_false_conv, vars₁, φ_subs_false_unconv, φ₁,
          π_1_unfolded]
      have : ∃ (π_2 : TreeLikeResolution φ₁ ((BotClause (vars₁)).convert vars int_proof)),
          π_2.width ≤ W + 1 := by
        exact width_respect_convert vars₁ vars φ_subs_false_unconv φ_subs_false_conv h_subs
          (by rfl) (W + 1) (BotClause (vars₁)) π_2 h_width_false int_proof
      obtain ⟨π_cand, h_cand_width⟩ := this
      change TreeLikeResolution φ_subs_false_conv (BotClause vars) at π_cand
      use π_cand

    have final_idea : ∃ (π : TreeLikeResolution φ (BotClause (vars))), π.width ≤ W + 1 := by
      exact width_closure φ φ_subs_false_conv (W + 1) (BotClause (vars)) idea₂ idea₃

    obtain ⟨π_final, final_proof⟩ := final_idea

    let π_refutation : TreeLikeRefutation φ := π_final
    have h_width :  π_refutation.width ≤ W + 1:= by
      subst h_value
      grind
    exact ⟨π_refutation, h_width⟩

def getRootVariable {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) : Option Variable :=
  match π with
  | .axiom_clause _ => none
  | .resolve _ _ v _ _ _ _ _ => some v

lemma axiom_if_none {vars} {φ : CNFFormula vars} {c : Clause vars} (π : TreeLikeResolution φ c) :
    getRootVariable π = none →
    ∃ (h_c_in_φ : c ∈ φ), π = TreeLikeResolution.axiom_clause h_c_in_φ := by
  intro h_none
  -- Split π into its two possible constructors
  cases π with
  | axiom_clause h_c_in_φ =>
      -- Case 1: π is an axiom_clause. This matches our goal.
      exists h_c_in_φ
  | resolve c₁ c₂ v h_vars h_c π₁ π₂ h_res =>
      -- Case 2: π is a resolve.
      -- But getRootVariable (resolve ...) returns 'some v'.
      -- This contradicts our assumption 'h_none' (some v = none).
      simp [getRootVariable] at h_none

lemma root_var_in_vars {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) (v : Variable) :
    getRootVariable π = some v → v ∈ vars := by
  intro h_get
  -- Split π into its constructors
  cases π with
  | axiom_clause h_in =>
      -- getRootVariable returns 'none' for axioms, so this branch is impossible
      simp [getRootVariable] at h_get
  | resolve c₁ c₂ v' h_v_in_vars h_not_in π₁ π₂ h_res =>
      -- Here, Lean sees that 'getRootVariable' returns 'some v''
      simp [getRootVariable] at h_get
      -- Since 'some v' = 'some v'', then 'v = v''
      rw [← h_get]
      exact h_v_in_vars

lemma size_split {a b k : ℕ} (h : a + b ≤ k + k) : a ≤ k ∨ b ≤ k := by
  -- Use proof by contradiction
  by_contra h_both
  -- Push the negation: ¬(a ≤ k ∨ b ≤ k) becomes (a > k ∧ b > k)
  simp [not_or] at h_both
  have ⟨ha, hb⟩ := h_both
  -- Since a and b are natural numbers, a > k means a ≥ k + 1
  have ha' : a ≥ k + 1 := Nat.succ_le_of_lt ha
  have hb' : b ≥ k + 1 := Nat.succ_le_of_lt hb
  -- Add the inequalities: a + b ≥ k + 1 + k + 1 = (k + k) + 2
  have h_sum := Nat.add_le_add ha' hb'
  -- This contradicts our hypothesis h : a + b ≤ k + k
  linarith





lemma eliminate_vacuous_resolutions {vars} {φ : CNFFormula vars} -- {c : Clause vars}
    (π : TreeLikeResolution φ (BotClause vars)) :
    ∃ (π' : TreeLikeResolution φ (BotClause vars)), IsRegularRes π' ∧ π'.size ≤ π.size := by

  have : ∃ (c' : Clause vars) (π' : TreeLikeResolution φ c'), (c' ⊆ (BotClause vars)) ∧
      IsRegularRes π' ∧ π'.size ≤ π.size := by
    exact resolution_regularize π
  obtain ⟨c', h_π⟩ := this
  obtain ⟨π', h_π⟩ := h_π
  have idea : c' = (BotClause vars) := by
    simp_all only [Finset.subset_empty]
  subst c'
  simp_all only [subset_refl, true_and]
  obtain ⟨left, right⟩ := h_π
  apply Exists.intro
  · apply And.intro
    on_goal 2 => { exact right
    }
    · simp_all only


lemma var_incl {vars} (v : Variable) (C : Clause vars) (h_v_in_vars : v ∈ vars)
  (h_sub : v ∈ C.variables) :
  {v.toLiteral h_v_in_vars} ⊆ C ∨ {v.toNegLiteral h_v_in_vars} ⊆ C := by
  unfold Clause.variables at h_sub
  unfold Literal.variable at h_sub
  simp_all
  obtain ⟨a, h_sub⟩ := h_sub
  obtain ⟨h_sub_left, h_sub_right⟩ := h_sub
  cases a
  case pos var h_v =>
    have : Literal.pos var h_v = v.toLiteral h_v_in_vars := by
      subst h_sub_right
      simp_all only
      rfl
    subst h_sub_right
    simp_all only [true_or]
  case neg var h_v =>
    have : Literal.neg var h_v = v.toNegLiteral h_v_in_vars := by
      subst h_sub_right
      simp_all only
      rfl
    subst h_sub_right
    simp_all only [or_true]


theorem width_imply_size_ind_version (W : ℕ)
    (W_c : ℕ) :
    --(h_ineq : W > W_c) :
    --(h_size : π.size ≤ 2 ^ (W - W_c)) :
    ∀ (vars) (φ : CNFFormula vars) (_ : ∀ C ∈ φ, C.card ≤ W_c) (π : TreeLikeRefutation φ),
      π.size ≤ 2 ^ (W) →
      ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W + W_c:= by

  induction W using Nat.strong_induction_on with
  | h W ih_0 =>
    intro vars φ h_clause_card π_0 h_0_size

    induction vars using Finset.strongInductionOn
    case a s ih =>
      have h_reg : ∃ (π : TreeLikeResolution φ (BotClause s)),
          IsRegularRes π ∧ π.size ≤ π_0.size := by
        exact eliminate_vacuous_resolutions π_0
      obtain ⟨π, h_reg⟩ := h_reg
      by_cases (getRootVariable π = none)
      case pos h_x =>
        have : ∃ (h_c_in_φ : (BotClause s) ∈ φ),
            π = TreeLikeResolution.axiom_clause h_c_in_φ := by
          exact axiom_if_none π h_x
        use π
        obtain ⟨C, h_C⟩ := this
        unfold TreeLikeResolution.width
        subst h_C
        simp_all only [Finset.card_empty, zero_le]
      case neg h_xx =>

        obtain ⟨h_reg, h_size_trans⟩ := h_reg
        have h_size :  TreeLikeResolution.size π ≤ 2 ^ (W) := by
          omega
        by_cases (W = 0)
        case pos h_W_eq =>
          have : π.size ≤ 1 := by
            subst h_W_eq
            simp_all only [not_lt_zero', not_isEmpty_of_nonempty, IsEmpty.forall_iff, forall_const,
              pow_zero, zero_add]
          have : π.width ≤ W_c := by
            exact size_one_proof φ W_c h_clause_card π this
          use π
          trans W_c
          · trivial
          · omega
        case neg h_W_neq =>
        have h_x : getRootVariable π ≠ none := h_xx
        -- Convert '≠ none' to 'isSome = true'
        let v : Variable := (getRootVariable π).get (Option.ne_none_iff_isSome.mp h_x)
        have grab_1 : getRootVariable π = some v → v ∈ s := by
          exact fun a ↦ root_var_in_vars π v a
        have h_v_incl : v ∈ s := by
          simp_all only [not_false_eq_true, Option.some_get, forall_const, v]



        let smaller_set := s.erase v

        -- Prove that removing x makes a strictly smaller subset
        have h_sub : smaller_set ⊂ s := Finset.erase_ssubset h_v_incl

        clear h_xx

        --unfold TreeLikeRefutation at π

        have ih' := ih smaller_set

        simp_all

        cases π with
        | axiom_clause h_in =>
            -- getRootVariable returns 'none' for axioms, so this branch is impossible
          exact False.elim (h_x rfl)
        | resolve c₁ c₂ v' h_v_in_vars h_not_in π₁ π₂ h_res =>
          have : v' = v := by
            simp_all only [implies_true, v, smaller_set]
            obtain ⟨left, right⟩ := h_res
            rfl

          have idea₁ : π₁.size ≤ 2^(W - 1) ∨ π₂.size ≤ 2^(W - 1) := by
            unfold TreeLikeResolution.size at h_size
            have temp : π₁.size + π₂.size ≤ 2^(W - 1) + 2^(W - 1) := by
              have h_pow : 2 ^ (W) = 2 ^ (W - 1) + 2 ^ (W - 1) := by
                have h_pos : 0 < W := by
                  omega
                nth_rewrite 1 [← Nat.sub_add_cancel h_pos]
                rw [pow_add, pow_one]
                ring

              -- 2. Substitute and finish
              rw [h_pow] at h_size
              omega
            exact size_split temp

          have h_gen_size_lb : π₁.size ≤ 2^(W) ∧ π₂.size ≤ 2^(W) := by
            unfold TreeLikeResolution.size at h_size
            omega


          let ρ_true : Assignment {v} := (fun _ => fun _ => True)
          let φ_true := φ.substitute ρ_true
          let ρ_false : Assignment {v} := (fun _ => fun _ => False)
          let φ_false := φ.substitute ρ_false

          obtain ⟨h_res_left, h_res_right⟩ := h_res

          have hsubset_left :
            c₁ ⊆ ({v'.toLiteral h_v_in_vars} : Clause s) := by
            simpa [BotClause] using h_res_left

          have hcases_left :
            c₁ = ∅ ∨ c₁ = {v'.toLiteral h_v_in_vars} :=
            Finset.subset_singleton_iff.mp hsubset_left

          -- cases hcases_left with
          -- | inl h_empty =>
          --     subst c₁
          --     use π₁
          --     obtain ⟨left, right⟩ := h_gen_size_lb

          --     sorry
          -- | inr h_single =>


          have h_π_1_existence :
              ∃ (π_1 : TreeLikeResolution (φ.substitute ρ_true) (BotClause (s \ {v}))),
              (π_1.size ≤ π₂.size) := by

            have h_v_sub : {v} ⊆ s := by
              exact Finset.singleton_subset_iff.mpr h_v_in_vars
            have fact₀ : (c₂.substitute ρ_true = none) ∨
              (∃ c_res, c₂.substitute ρ_true = some c_res ∧
                ∃ c', c' ⊆ c_res ∧
                ∃ (π' : TreeLikeResolution (φ.substitute ρ_true) c'),
                  π'.width ≤ π₂.width ∧ π'.size ≤ π₂.size) := by
              exact resolution_restrict ρ_true π₂
            have temp_fact : c₂ = ({v'.toNegLiteral h_v_in_vars} : Clause s) := by
              have idea₁ : v' ∈ c₂.variables := by
                unfold IsRegularRes at h_reg
                grind
              refine Finset.Subset.antisymm_iff.mpr ?_
              constructor
              · unfold BotClause at h_res_right
                exact h_res_right
              · have idea₂ :
                    {v'.toLiteral h_v_in_vars} ⊆ c₂ ∨ {v'.toNegLiteral h_v_in_vars} ⊆ c₂ := by
                  exact var_incl v' c₂ h_v_in_vars idea₁
                grind
            have idea₁ : ¬(c₂.substitute ρ_true = none) := by
              have : ({v'.toNegLiteral h_v_in_vars} : Clause s).substitute ρ_true =
                  BotClause ((s \ {v})) := by
                exact lit_subst_is_Bot_false (v'.toNegLiteral h_v_in_vars) ρ_true (by rfl)
              have : c₂.substitute ρ_true = BotClause ((s \ {v})) := by
                grind
              grind
            cases fact₀ with
            | inl hnone =>
                contradiction
            | inr fact₀ =>
                obtain ⟨c_res, h_c_res⟩ := fact₀
                obtain ⟨h_c_res_left, h_c_res_rigth⟩ := h_c_res
                have : c_res  = BotClause ((s \ {v})) := by
                  have : ({v'.toNegLiteral h_v_in_vars} : Clause s).substitute ρ_true =
                      BotClause ((s \ {v})) := by
                    exact lit_subst_is_Bot_false (v'.toNegLiteral h_v_in_vars) ρ_true (by rfl)
                  grind

                obtain ⟨c'_res, h_c'_res⟩ := h_c_res_rigth
                obtain ⟨h_c'_res_left, h_c'_res_right⟩ := h_c'_res
                have : c'_res = BotClause ((s \ {v})) := by
                  grind
                obtain ⟨π₁', h_c'_res_right⟩ := h_c'_res_right
                simp_all
                subst c'_res
                use π₁'
                obtain ⟨h_c'_res_right_left, h_c'_res_right_right⟩ := h_c'_res_right
                exact h_c'_res_right_right





          obtain ⟨π_1, h_π_1⟩ := h_π_1_existence

          have h_π_2_existence :
              ∃ (π_2 : TreeLikeResolution (φ.substitute ρ_false) (BotClause (s \ {v}))),
              (π_2.size ≤ π₁.size) := by
            have h_v_sub : {v} ⊆ s := by
              exact Finset.singleton_subset_iff.mpr h_v_in_vars
            have fact₀ : (c₁.substitute ρ_false = none) ∨
              (∃ c_res, c₁.substitute ρ_false = some c_res ∧
                ∃ c', c' ⊆ c_res ∧
                ∃ (π' : TreeLikeResolution (φ.substitute ρ_false) c'),
                  π'.width ≤ π₁.width ∧ π'.size ≤ π₁.size) := by
              exact resolution_restrict ρ_false π₁
            have temp_fact : c₁ = ({v'.toLiteral h_v_in_vars} : Clause s) := by
              have idea₁ : v' ∈ c₁.variables := by
                unfold IsRegularRes at h_reg
                grind
              refine Finset.Subset.antisymm_iff.mpr ?_
              constructor
              · unfold BotClause at h_res_left
                exact h_res_left
              · have idea₂ :
                    {v'.toLiteral h_v_in_vars} ⊆ c₁ ∨ {v'.toNegLiteral h_v_in_vars} ⊆ c₁ := by
                  exact var_incl v' c₁ h_v_in_vars idea₁
                grind
            have idea₁ : ¬(c₁.substitute ρ_false = none) := by
              have : ({v'.toLiteral h_v_in_vars} : Clause s).substitute ρ_false =
                  BotClause ((s \ {v})) := by
                exact lit_subst_is_Bot_false (v'.toLiteral h_v_in_vars) ρ_false (by rfl)
              have : c₁.substitute ρ_false = BotClause ((s \ {v})) := by
                grind
              grind
            cases fact₀ with
            | inl hnone =>
                contradiction
            | inr fact₀ =>
                obtain ⟨c_res, h_c_res⟩ := fact₀
                obtain ⟨h_c_res_left, h_c_res_rigth⟩ := h_c_res
                have : c_res  = BotClause ((s \ {v})) := by
                  have : ({v'.toLiteral h_v_in_vars} : Clause s).substitute ρ_false =
                      BotClause ((s \ {v})) := by
                    exact lit_subst_is_Bot_false (v'.toLiteral h_v_in_vars) ρ_false (by rfl)
                  grind

                obtain ⟨c'_res, h_c'_res⟩ := h_c_res_rigth
                obtain ⟨h_c'_res_left, h_c'_res_right⟩ := h_c'_res
                have : c'_res = BotClause ((s \ {v})) := by
                  grind
                obtain ⟨π₁', h_c'_res_right⟩ := h_c'_res_right
                simp_all
                subst c'_res
                use π₁'
                obtain ⟨h_c'_res_right_left, h_c'_res_right_right⟩ := h_c'_res_right
                exact h_c'_res_right_right





          obtain ⟨π_2, h_π_2⟩ := h_π_2_existence


          have h_clause_subs_width_true : ∀ C ∈ φ.substitute ρ_true, Finset.card C ≤ W_c := by
                intro C_2 h_c_2
                unfold CNFFormula.substitute at h_c_2
                simp at h_c_2
                obtain ⟨A, h_A⟩ := h_c_2
                obtain ⟨h_A_left, h_A_right⟩ := h_A
                trans Finset.card A
                swap
                · exact h_clause_card A h_A_left
                have : (A.substitute ρ_true = none) ∨
                    (∃ c_res, A.substitute ρ_true = some c_res ∧
                     Finset.card c_res ≤ Finset.card A) := by
                  exact card_subst A
                -- 1. Split the 'this' hypothesis
                rcases this with h_none | ⟨c_res, h_some, h_le⟩
                · -- Case: A.substitute ρ_true = none
                  -- This is impossible because we know it equals 'some C_2'
                  rw [h_A_right] at h_none
                  contradiction

                · -- Case: ∃ c_res, A.substitute ρ_true = some c_res ∧ ...
                  -- Since A.substitute ρ_true equals both 'some C_2' and 'some c_res'
                  rw [h_A_right] at h_some
                  -- Injectivity of 'some' tells us C_2 = c_res
                  injection h_some with h_eq
                  -- Substitute c_res for C_2 in the cardinality bound
                  rw [← h_eq] at h_le
                  exact h_le

          have h_clause_subs_width_false : ∀ C ∈ φ.substitute ρ_false, Finset.card C ≤ W_c := by
            intro C_2 h_c_2
            unfold CNFFormula.substitute at h_c_2
            simp at h_c_2
            obtain ⟨A, h_A⟩ := h_c_2
            obtain ⟨h_A_left, h_A_right⟩ := h_A
            trans Finset.card A
            swap
            · exact h_clause_card A h_A_left
            have : (A.substitute ρ_false = none) ∨
                (∃ c_res, A.substitute ρ_false = some c_res ∧
                Finset.card c_res ≤ Finset.card A) := by
              exact card_subst A
            -- 1. Split the 'this' hypothesis
            rcases this with h_none | ⟨c_res, h_some, h_le⟩
            · -- Case: A.substitute ρ_true = none
              -- This is impossible because we know it equals 'some C_2'
              rw [h_A_right] at h_none
              contradiction

            · -- Case: ∃ c_res, A.substitute ρ_true = some c_res ∧ ...
              -- Since A.substitute ρ_true equals both 'some C_2' and 'some c_res'
              rw [h_A_right] at h_some
              -- Injectivity of 'some' tells us C_2 = c_res
              injection h_some with h_eq
              -- Substitute c_res for C_2 in the cardinality bound
              rw [← h_eq] at h_le
              exact h_le



          cases idea₁ with
          | inr h_size₁ =>
              -- Case 1: π₁.size ≤ 2^(W - W_c - 1)
              -- Your hypothesis here is named h_size₁
              have idea_0 : π_1.size ≤ 2 ^ (W - 1) := by
                grind

              have ineq₁ : W - 1 < W := by
                grind



              have ih_1 := ih_0 (W - 1) ineq₁
                (s \ {v}) (φ.substitute ρ_true) h_clause_subs_width_true π_1 idea_0

              obtain ⟨π_1', idea_00'⟩ := ih_1

              have idea_00 : TreeLikeResolution.width π_1' ≤ W + W_c - 1 := by
                omega

              have idea_10 : π_2.size ≤ 2^(W) := by
                trans π₁.size
                · exact h_π_2
                · exact h_gen_size_lb.left

              have : smaller_set = s \ {v} := by
                exact Finset.erase_eq s v

              rw[this] at ih'

              have ih'_1 := ih' (φ.substitute ρ_false) h_clause_subs_width_false π_2 idea_10

              obtain ⟨π_2', idea_11⟩ := ih'_1



              have final_idea : ∃ (π' : TreeLikeRefutation φ),
                  TreeLikeResolution.width π' ≤ W + W_c - 1 + 1 := by
                apply width_combine s (v.toLiteral h_v_incl) h_v_incl ρ_true rfl ρ_false rfl
                  (W + W_c - 1) π_1' idea_00 π_2' (by grind)
                intro C''
                intro h_C''
                trans W + W_c
                · grind
                · omega
              obtain ⟨π_final, conclusion⟩ := final_idea

              use π_final
              grind


          | inl h_size₂ =>
              -- Case 1: π₁.size ≤ 2^(W - W_c - 1)
              -- Your hypothesis here is named h_size₁
              have idea_0 : π_2.size ≤ 2 ^ (W - 1) := by
                grind

              have ineq₁ : W - 1 < W := by
                grind



              have ih_1 := ih_0 (W - 1) ineq₁
                (s \ {v}) (φ.substitute ρ_false) h_clause_subs_width_false π_2 idea_0

              obtain ⟨π_2', idea_00'⟩ := ih_1

              have idea_00 : TreeLikeResolution.width π_2' ≤ W + W_c - 1 := by
                omega

              have idea_10 : π_1.size ≤ 2^(W) := by
                trans π₂.size
                · exact h_π_1
                · exact h_gen_size_lb.right

              have : smaller_set = s \ {v} := by
                exact Finset.erase_eq s v

              rw[this] at ih'

              have ih'_1 := ih' (φ.substitute ρ_true) h_clause_subs_width_true π_1 idea_10

              obtain ⟨π_1', idea_11⟩ := ih'_1



              have final_idea : ∃ (π' : TreeLikeRefutation φ),
                  TreeLikeResolution.width π' ≤ W + W_c - 1 + 1 := by
                apply width_combine s (v.toNegLiteral h_v_incl) h_v_incl ρ_false rfl ρ_true rfl
                  (W + W_c - 1) π_2' idea_00 π_1' (by grind)
                intro C''
                intro h_C''
                trans W + W_c
                · grind
                · omega
              obtain ⟨π_final, conclusion⟩ := final_idea

              use π_final
              grind
