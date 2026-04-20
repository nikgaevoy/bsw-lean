import BSWLean.Treelike
import BSWLean.TinyConversions
import Mathlib.Data.Finset.Basic

lemma lit_subst_is_Bot_false {vars}
    (l : Literal vars)
    (ρ_false : (Assignment ({l.variable} : Finset Variable)))
    (h_value : l.IsAssignment (¬l.polarity : Bool) ρ_false) :
    ({l} : Clause vars).substitute ρ_false = BotClause (vars \ {l.variable}):= by
  aesop (add safe apply clause_subst_eq_bot_of_falsified)

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
  | none => exact Or.inl rfl
  | some c_res =>
    refine Or.inr ⟨c_res, rfl, ?_⟩
    have h₁ : (C.substitute ρ).isSome := by simp [h]
    have := Clause.substitute_card_leq_card C ρ (h := h₁)
    simp [h] at this
    exact this

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
    (h_x : x ∈ vars) (h₁ : c₂ ⊆ c₁ ∪ {x.toLiteral h_x true})
    (h₂ : c₃ ⊆ c₁ ∪ {x.toLiteral h_x false}) :
    Finset.card (c₂.resolve c₃ x h_x) ≤ Finset.card c₁
    := by
  unfold Clause.resolve
  have idea :
      (Finset.erase c₂ (x.toLiteral h_x true) ∪ Finset.erase c₃ (x.toLiteral h_x false)) ⊆ c₁ := by
    grind
  exact Finset.card_le_card idea

lemma clause_combine_superset (vars₁ vars₂) {x : Variable} (c₁ c₂ : Clause (vars₁))
    (c₃ : Clause (vars₂)) (h₀ : x ∈ vars₁) (h₁ : c₂ ⊆ c₁ ∪ {x.toLiteral h₀ true})
    (h_disj : Disjoint vars₁ vars₂) (h₂ : x ∈ (vars₁.disjUnion vars₂ h_disj)) :
    (Clause.combine c₂ c₃ h_disj) ⊆ ((Clause.combine c₁ c₃ h_disj) ∪ {x.toLiteral h₂ true}) := by
  simp
  unfold Clause.combine
  simp
  refine Finset.union_subset ?_ ?_
  · trans insert (x.toLiteral h₂ true) (c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop))
    · refine Clause.convert_maintains_subset_insert c₂ c₁ (Finset.disjUnion vars₁ vars₂ h_disj)
        (x.toLiteral h₂ true) h₀ ?_
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
  unfold Clause.combine
  unfold Clause.convert_trivial
  simp_all only [carry_through_convert, Clause.convert_convert]
  apply Finset.union_subset
  swap
  · grind
  · apply remove_middle_subset
    grind [Finset.union_subset, Clause.convert, carry_through_convert,
      loose_convert, Finset.union_assoc]

lemma sdiff_disjUnion_eq_vars {vars sub_vars : Variables} (h_subset : sub_vars ⊆ vars) :
    Finset.disjUnion (vars \ sub_vars) sub_vars Finset.sdiff_disjoint = vars := by
  aesop

lemma var_in_vars_of_in_sdiff {vars sub_vars : Variables} {var : Variable}
    (h_4 : var ∈ vars \ sub_vars) : var ∈ vars := by
  grind

lemma resolve_combined_le_c1 (vars sub_vars : Variables) (var : Variable)
    (ρ : Assignment sub_vars) (c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_4 : var ∈ vars \ sub_vars)
    (inter_proof : Finset.disjUnion (vars \ sub_vars) sub_vars Finset.sdiff_disjoint = vars)
    (var_incl : var ∈ vars)
    (left : c_2 ⊆ c_1 ∪ {var.toLiteral h_4 true})
    (right : c_3 ⊆ c_1 ∪ {var.toLiteral h_4 false}) :
    Finset.card (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial
     vars inter_proof).resolve
      ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars
        inter_proof) var var_incl) ≤
    Finset.card ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial
       vars inter_proof) := by
  have idea₃ := inter_idea_new_version vars sub_vars
    (var.toLiteral h_4 true) ρ c_1 c_2 inter_proof var_incl left
  have idea₄ := inter_idea_new_version vars sub_vars
     (var.toLiteral h_4 false) ρ c_1 c_3 inter_proof var_incl right
  simp only [ge_iff_le]
  exact resolve_subsets_trick var vars
    ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof)
    ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof)
    ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof)
    (by grind) idea₃ idea₄

lemma resolve_ineq (vars sub_vars) (φ : CNFFormula vars) (var : Variable)
    (ρ : Assignment sub_vars) (c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_subset : sub_vars ⊆ vars)
    (h_4 : var ∈ vars \ sub_vars) (h_0 : var ∉ c_1.variables)
    (p_1 : TreeLikeResolution (φ.substitute ρ) c_2)
    (p_2 : TreeLikeResolution (φ.substitute ρ) c_3)
    (left : c_2 ⊆ c_1 ∪ {var.toLiteral h_4 true})
    (right : c_3 ⊆ c_1 ∪ {var.toLiteral h_4 false}) :
    Finset.card ((TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
    (⟨left, right⟩)).unsubstitute_rhs ρ) ≤
    max (Finset.card c_1) (max p_1.width p_2.width) + Finset.card sub_vars := by
  unfold TreeLikeResolution.unsubstitute_rhs
  simp

  have inter_proof := sdiff_disjUnion_eq_vars h_subset
  have var_incl := var_in_vars_of_in_sdiff h_4

  -- 1st Bound: Subset relation of unsubstitutions
  trans Finset.card (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial
     vars inter_proof).resolve
    ((Clause.combine c_3 ρ.toClause
    Finset.sdiff_disjoint).convert_trivial vars inter_proof) var var_incl)
  · clear left right c_1 h_0
    apply Finset.card_le_card
    grind only [TreeLikeResolution.unsubstitute_rhs_variables, resolve_subsets]

  -- 2nd Bound: Setup the upper maximum bound
  trans Finset.card c_1 + Finset.card sub_vars
  swap
  · simp_all only [add_le_add_iff_right, le_sup_left]

  -- 3rd Bound: Substitute the combined c_1 cardinality
  trans Finset.card ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial
    vars inter_proof)
  swap
  · exact card_combination c_1

  -- Final Step: Bounding the c_2/c_3 resolve combination by c_1 combination
  exact resolve_combined_le_c1
    vars sub_vars var ρ c_1 c_2 c_3 h_4 inter_proof var_incl left right

lemma induction_step_width_incr {vars sub_vars} {φ : CNFFormula vars} {var : Variable}
    {ρ : Assignment sub_vars} (c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_subset : sub_vars ⊆ vars)
    (h_4 : var ∈ vars \ sub_vars) (h_0 : var ∉ c_1.variables)
    (p_1 : TreeLikeResolution (φ.substitute ρ) c_2)
    (p_2 : TreeLikeResolution (φ.substitute ρ) c_3)
    (h_1 : c_2 ⊆ c_1 ∪ {var.toLiteral h_4 true} ∧ c_3 ⊆ c_1 ∪ {var.toLiteral h_4 false})
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
    · constructor
      · trans p_1.width + Finset.card sub_vars
        · trans (p_1.unsubstitute ρ h_subset).width
          · unfold TreeLikeResolution.unsubstitute at heq
            grind only [Finset.union_singleton, le_refl]
          · exact h_2
        · simp
      · trans p_2.width + Finset.card sub_vars
        · trans (p_2.unsubstitute ρ h_subset).width
          · unfold TreeLikeResolution.unsubstitute at heq
            grind only [Finset.union_singleton, le_refl]
          · exact h_3
        · simp

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
  simpa [Finset.card_singleton] using unsub_increase_width c π (Finset.singleton_subset_iff.mpr h₀)

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
        ⟨sub_tree, by aesop⟩

    | .resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
        let ⟨P₁, hP₁⟩ := graft π₁
        let ⟨P₂, hP₂⟩ := graft π₂
        let P_final := TreeLikeResolution.resolve c₁ c₂ v h_v_mem h_v_not P₁ P₂ h_res
        ⟨P_final, by
          unfold TreeLikeResolution.width
          simp
          grind⟩
  -- Execute the recursion on T1 to produce the final proof P
  let X := graft π₁

  obtain ⟨π₁', hπ₁'⟩ := X
  use π₁'
  aesop

lemma ufold_one_literal {vars} {φ : CNFFormula vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : x.IsAssignment x.polarity ρ_true)
    (π_1 : TreeLikeRefutation (φ.substitute ρ_true))
    (fact₀ : {x.variable} ⊆ vars) :
    (TreeLikeResolution.unsubstitute_rhs ρ_true π_1) ⊆ ({x.negate} : Clause vars) := by

  unfold TreeLikeRefutation at π_1

  trans ((BotClause (vars \ {x.variable})).combine ρ_true.toClause
    (Finset.sdiff_disjoint : Disjoint (vars \ {x.variable}) {x.variable})).convert_trivial
    vars (by aesop)

  · exact TreeLikeResolution.unsubstitute_rhs_variables ρ_true π_1 fact₀

  · unfold BotClause
    unfold Clause.combine
    simp
    unfold Clause.convert_trivial
    rw [Clause.convert_convert, trivial_subs_unfold x x.polarity ρ_true h_value]
    simp [Literal.negate]

--lemma local_convertion

lemma single_literal_conversion {vars₁ vars₂ : Variables} {lit : Literal vars₁}
    {v_new_mem : lit.variable ∈ vars₂} {h} :
    ({lit} : Clause vars₁).convert vars₂ h
      = ({ ⟨⟨lit.variable, v_new_mem⟩, lit.polarity⟩ } : Clause vars₂) := by
  unfold Clause.convert
  aesop

lemma clause_width_smaller_proof_width {vars : Variables} {φ} {C : Clause vars}
    (π : TreeLikeResolution φ C) : (C.card ≤ π.width) := by
  induction π
  · aesop
  rename_i h_resolve π₁_ih π₂_ih
  obtain ⟨left, right⟩ := h_resolve
  unfold TreeLikeResolution.width
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
    aesop

  have idea' : Finset.card C ≤ W := by
    grind only [clause_width_smaller_proof_width]

  match π₁ with
  | .axiom_clause h_in =>
      let C_new := C.convert vars₂ (by exact fun l a ↦ idea C l a)
        have : C_new ∈ φ₁ := by
          rw[<-h_conv]
          unfold CNFFormula.simple_convert
          aesop
        let π₂ := TreeLikeResolution.axiom_clause (by aesop)
        ⟨π₂, by grind [convert_card, TreeLikeResolution.width]⟩
  | .resolve c₁ c₂ v h_v_mem h_v_not π_a π_b h_res =>
      have idea₁ : π_a.width ≤ W := by
        grind [TreeLikeResolution.width, sup_le_iff]
      have idea₂ : π_b.width ≤ W := by
        grind [TreeLikeResolution.width, sup_le_iff]

      let ⟨π_a_new, h_wa⟩ := convert_proof W h_subs h_conv π_a idea₁
      let ⟨π_b_new, h_wb⟩ := convert_proof W h_subs h_conv π_b idea₂

      let v_new_mem := h_subs h_v_mem

      have fact₁ : ∀ l ∈ c₁, l.variable ∈ vars₂ := by
        aesop
      have fact₂ : ∀ l ∈ c₂, l.variable ∈ vars₂ := by
        aesop
      have fact₀ :  ∀ l ∈ C, l.variable ∈ vars₂ := by
        aesop

      have h_resolve : c₁.convert vars₂ fact₁ ⊆
          C.convert vars₂ fact₀ ∪ {v.toLiteral v_new_mem true} ∧
        c₂.convert vars₂ fact₂ ⊆ C.convert vars₂ fact₀ ∪ {v.toLiteral v_new_mem false} := by

        constructor

        · clear idea fact₂ h_v_not h_width
            idea₁ idea₂ idea' h_conv π_a_new π_a π_b h_wa π_b_new h_wb π₁ φ φ₁

          trans (C ∪ ({v.toLiteral h_v_mem true} : Clause vars₁)).convert vars₂ (by aesop)
          · grind only [loose_convert]
          · grind [single_literal_conversion,
              carry_through_convert, Finset.subset_of_eq, loose_convert]


        · clear idea h_v_not h_width fact₁
            idea₁ idea₂ idea' h_conv π_a_new π_a π_b h_wa π_b_new h_wb π₁ φ φ₁
          trans (C ∪ ({v.toLiteral h_v_mem false} : Clause vars₁)).convert vars₂ (by aesop)
          · grind only [loose_convert]
          · grind [single_literal_conversion,
              carry_through_convert, Finset.subset_of_eq, loose_convert]


      -- 3. Construct the new resolution node
      let π_new := TreeLikeResolution.resolve
        (c₁.convert vars₂ fact₁)
        (c₂.convert vars₂ fact₂)
        v v_new_mem (by aesop) π_a_new π_b_new h_resolve

      ⟨π_new, by
        unfold TreeLikeResolution.width
        aesop⟩

lemma width_respect_convert (vars₁ vars₂) (φ : CNFFormula vars₁)
   (φ₁ : CNFFormula vars₂) (h_subs : vars₁ ⊆ vars₂)
   (h_conv : (CNFFormula.simple_convert vars₁ vars₂ φ h_subs) = φ₁)
   (W : ℕ) (C : Clause vars₁)
   (π_1 : TreeLikeResolution φ C) (h_width_true : π_1.width ≤ W)
   (int_proof : ∀ l ∈ C, l.variable ∈ vars₂) :
   ∃ (π_2 : TreeLikeResolution φ₁ (C.convert vars₂ int_proof)), π_2.width ≤ W  := by
  let ⟨π, h⟩ := convert_proof W h_subs h_conv π_1 h_width_true
  exact ⟨π, h⟩


private lemma clause_substitute_convert_subset {vars sub_vars}
    {ρ : Assignment sub_vars} {C : Clause vars} {C' : Clause (vars \ sub_vars)}
    (h_sub : C.substitute ρ = some C') (h_incl : ∀ l ∈ C', l.variable ∈ vars) :
    C'.convert vars h_incl ⊆ C := by
  intro m hm
  simp only [Clause.convert, Finset.mem_filterMap] at hm
  obtain ⟨l', hl'_in, hl'_eq⟩ := hm
  simp only [dif_pos hl'_in, Option.some.injEq] at hl'_eq
  subst hl'_eq
  have h_preimage : ∃ l ∈ C, l.variable = l'.variable ∧ l.polarity = l'.polarity := by
    have hl'_in_sub : l' ∈ (C.substitute ρ).get (by simp [h_sub]) := by simp [h_sub, hl'_in]
    aesop (add safe unfold [Clause.substitute, Clause.split, Clause.shrink, Literal.restrict])
  obtain ⟨l, hl_mem, hl_var, hl_pol⟩ := h_preimage
  convert hl_mem using 1
  apply Literal.ext <;> simp [Literal.convert, hl_var, hl_pol]

lemma var_mem_of_literal_mem {v_set} (l : Literal v_set) :
    l.variable ∈ v_set := Literal.variable_mem_vars l


private lemma clause_card_substitute_le {vars sub_vars} {φ : CNFFormula vars}
    {ρ : Assignment sub_vars} {W_c : ℕ} (h_clause_card : ∀ C ∈ φ, C.card ≤ W_c) :
    ∀ C ∈ φ.substitute ρ, C.card ≤ W_c := by
  intro C h_c
  obtain ⟨A, h_A_in, h_A_sub⟩ := CNFFormula.substitute_preimage h_c
  have h₁ : (A.substitute ρ).isSome := by simp [h_A_sub]
  have h_le := Clause.substitute_card_leq_card A ρ (h := h₁)
  simp [h_A_sub] at h_le
  exact h_le.trans (h_clause_card A h_A_in)

private lemma resolve_axiom_with_negate {vars} {φ : CNFFormula vars}
    {x : Literal vars} {C_0 C_2 : Clause vars} {W : ℕ}
    (h_v_not_mem : x.variable ∉ C_0.variables)
    (h_C2_in_φ : C_2 ∈ φ) (h_C2_sub : C_2 ⊆ C_0 ∪ {x})
    (h_C0_card : C_0.card ≤ W + 1) (h_C2_card : C_2.card ≤ W + 1)
    (π_neg : TreeLikeResolution φ {x.negate})
    (h_neg_width : π_neg.width ≤ W + 1) :
    ∃ π : TreeLikeResolution φ C_0, π.width ≤ W + 1 := by
  let v := x.variable
  have h_val : v ∈ vars := Literal.variable_mem_vars x
  cases hpol : x.polarity with
  | true =>
    have hvx : v.toLiteral h_val true = x := Literal.ext rfl hpol.symm
    have hxn : x.negate = v.toLiteral h_val false :=
      Literal.ext rfl (by simp [Literal.negate, Variable.toLiteral, hpol])
    exact ⟨TreeLikeResolution.resolve C_2 {x.negate} v h_val h_v_not_mem
        (TreeLikeResolution.axiom_clause h_C2_in_φ) π_neg
        ⟨by rw [hvx]; exact h_C2_sub, by rw [hxn]; exact Finset.subset_union_right⟩,
      by unfold TreeLikeResolution.width; grind [TreeLikeResolution.width]⟩
  | false =>
    have hvx : v.toLiteral h_val false = x :=
      Literal.ext rfl (by simp [Variable.toLiteral, hpol])
    have hxn : x.negate = v.toLiteral h_val true :=
      Literal.ext rfl (by simp [Literal.negate, Variable.toLiteral, hpol])
    exact ⟨TreeLikeResolution.resolve {x.negate} C_2 v h_val h_v_not_mem
        π_neg (TreeLikeResolution.axiom_clause h_C2_in_φ)
        ⟨by rw [hxn]; exact Finset.subset_union_right, by rw [hvx]; exact h_C2_sub⟩,
      by unfold TreeLikeResolution.width; grind [TreeLikeResolution.width]⟩

/-!
Key lemma used to prove size-width relation. Corresponds to Lemma 3.2 from Ben-Sasson Wigderson
-/

lemma width_combine (vars) {φ : CNFFormula vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : x.IsAssignment x.polarity ρ_true)
    (ρ_false : (Assignment ({x.variable} : Finset Variable)))
    (h_value_false : x.IsAssignment (¬x.polarity : Bool) ρ_false)
    (W : ℕ) (π_1 : TreeLikeRefutation (φ.substitute ρ_true)) (h_width_true : π_1.width ≤ W)
    (π_2 : TreeLikeRefutation (φ.substitute ρ_false)) (h_width_false : π_2.width ≤ W + 1)
    (h_clause_card : ∀ C ∈ φ, C.card ≤ W + 1) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W + 1 := by

  let π_1_unfolded := TreeLikeResolution.unsubstitute ρ_true π_1 (by aesop)
  have idea₀ : (TreeLikeResolution.unsubstitute_rhs ρ_true π_1) ⊆ ({x.negate}) := by
    grind [ufold_one_literal]
  have idea₁ : π_1_unfolded.width ≤ W + 1 := by grind [unsub_increase_width]
  have fact₁ : (C : Clause (vars \ {x.variable})) → (∀ l ∈ C, l.variable ∈ vars) := by grind

  let vars₁ := vars \ {x.variable}
  let φ_subs_false_unconv := φ.substitute ρ_false
  --have h_subs : vars₁ ⊆ vars := Finset.sdiff_subset

  let φ_subs_false_conv :=
    CNFFormula.simple_convert vars₁ vars φ_subs_false_unconv (by aesop)
  change TreeLikeResolution φ_subs_false_unconv (BotClause vars₁) at π_2
  have h_cases := Finset.subset_singleton_iff.mp idea₀
  rcases h_cases with h_empty | h_eq
  · let π_refutation : TreeLikeRefutation φ := cast (by rw [h_empty]) π_1_unfolded
    exact ⟨π_refutation, by subst h_value; grind⟩
  · have idea₂ : ∀ C ∈ φ_subs_false_conv, ∃ (π : TreeLikeResolution φ C), π.width ≤ W + 1  := by
      intro C_0 h_c
      have entry₁ : ∃ C_1 ∈ φ_subs_false_unconv,
          (C_1.convert vars (by exact fun l a ↦ fact₁ C_1 l a)) = C_0 := by
        aesop (add safe unfold [CNFFormula.simple_convert])

      obtain ⟨C_1, h_C_1_conv_left, h_C_1_conv_right⟩ := entry₁
      obtain ⟨C_2, h_C2_in_φ, h_C2_sub⟩ := CNFFormula.substitute_preimage h_C_1_conv_left

      have h_left : C_2 ⊆ C_0 ∪ ({x} : Clause vars) := by
        grind [substitute_trivial_property_human_form]
      have h_right : C_0 ⊆ C_2 := by
        grind only [clause_substitute_convert_subset]

      have h_v_not_mem_c : x.variable ∉ C_0.variables := by
        have h_prep : x.variable ∉ C_1.variables := by
          intro h_mem
          obtain ⟨l, _, hl_eq⟩ := Finset.mem_image.1 h_mem
          exact absurd (hl_eq ▸ var_mem_of_literal_mem l) (by simp)
        aesop
      let π_new : TreeLikeResolution φ {x.negate} := h_eq ▸ π_1_unfolded

      have idea_new : π_new.width ≤ W + 1 := by grind

      exact resolve_axiom_with_negate h_v_not_mem_c h_C2_in_φ h_left
        ((Finset.card_le_card h_right).trans (h_clause_card C_2 h_C2_in_φ))
        (h_clause_card C_2 h_C2_in_φ) π_new idea_new

    have idea₃ :
        ∃ (π : TreeLikeResolution φ_subs_false_conv (BotClause (vars))), π.width ≤ W + 1 := by
      obtain ⟨π_cand, h_cand_width⟩ := width_respect_convert vars₁ vars φ_subs_false_unconv
        φ_subs_false_conv (by aesop) (by rfl) (W + 1) (BotClause vars₁) π_2 h_width_false (by aesop)
      change TreeLikeResolution φ_subs_false_conv (BotClause vars) at π_cand
      exact ⟨π_cand, h_cand_width⟩

    obtain ⟨π_final, final_proof⟩ :=
      width_closure φ φ_subs_false_conv (W + 1) (BotClause vars) idea₂ idea₃
    exact ⟨π_final, by subst h_value; grind⟩

def getRootVariable {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) : Option Variable :=
  match π with
  | .axiom_clause _ => none
  | .resolve _ _ v _ _ _ _ _ => some v

lemma axiom_if_none {vars} {φ : CNFFormula vars} {c : Clause vars} (π : TreeLikeResolution φ c) :
    getRootVariable π = none →
    ∃ (h_c_in_φ : c ∈ φ), π = TreeLikeResolution.axiom_clause h_c_in_φ := by
  intro h_none
  cases π with
  | axiom_clause h => exact ⟨h, rfl⟩
  | resolve => simp [getRootVariable] at h_none

lemma root_var_in_vars {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) (v : Variable) :
    getRootVariable π = some v → v ∈ vars := by
  cases π with
  | axiom_clause => simp [getRootVariable]
  | resolve _ _ v' h_v_in_vars =>
    simp [getRootVariable]
    rintro rfl
    exact h_v_in_vars

lemma size_split {a b k : ℕ} (h : a + b ≤ k + k) : a ≤ k ∨ b ≤ k := by omega


lemma eliminate_vacuous_resolutions {vars} {φ : CNFFormula vars}
    (π : TreeLikeResolution φ (BotClause vars)) :
    ∃ (π' : TreeLikeResolution φ (BotClause vars)), IsRegularRes π' ∧ π'.size ≤ π.size := by
  obtain ⟨c', π', h_sub, h_reg, h_size⟩ := resolution_regularize π
  have hc : c' = BotClause vars := Finset.subset_empty.mp h_sub
  subst hc; exact ⟨π', h_reg, h_size⟩


lemma var_incl {vars} (v : Variable) (C : Clause vars) (h_v_in_vars : v ∈ vars)
    (h_sub : v ∈ C.variables) :
    {v.toLiteral h_v_in_vars true} ⊆ C ∨ {v.toLiteral h_v_in_vars false} ⊆ C := by
  unfold Clause.variables at h_sub
  unfold Literal.variable at h_sub
  simp_all
  obtain ⟨a, h_sub⟩ := h_sub
  have : a = v.toLiteral h_v_in_vars a.polarity := by aesop (add safe unfold Variable.toLiteral)
  obtain ⟨h_sub_left, h_sub_right⟩ := h_sub
  by_cases a.polarity
  case pos h_v =>
    grind
  case neg h_v =>
    grind


/-!
Claude wrote this lemma
-/
private lemma width_ind_combine
    {s : Finset Variable} {W W_c : ℕ} (hW : 0 < W)
    {φ : CNFFormula s}
    (h_clause_card : ∀ C ∈ φ, C.card ≤ W_c)
    (lit : Literal s)
    {ρ_A ρ_B : Assignment ({lit.variable} : Finset Variable)}
    (h_lit_A : lit.IsAssignment lit.polarity ρ_A)
    (h_lit_B : lit.IsAssignment (¬lit.polarity : Bool) ρ_B)
    (π_A' : TreeLikeRefutation (φ.substitute ρ_A))
    (h_A_width : π_A'.width ≤ (W - 1) + W_c)
    (π_B' : TreeLikeRefutation (φ.substitute ρ_B))
    (h_B_width : π_B'.width ≤ W + W_c) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W + W_c - 1 + 1 :=
  width_combine s lit (Literal.variable_mem_vars lit)
    ρ_A h_lit_A ρ_B h_lit_B (W + W_c - 1)
    π_A' (by omega) π_B' (by omega)
    (fun C hC => (h_clause_card C hC).trans (by omega))

/-- Given a proof of a singleton literal clause and an assignment that falsifies the literal,
extract a refutation of the substituted formula whose size is no larger. -/
private lemma bot_refut_of_falsified_lit
    {s : Finset Variable} {φ : CNFFormula s}
    (lit : Literal s) (ρ : Assignment ({lit.variable} : Finset Variable))
    (h_ρ : lit.IsAssignment (¬lit.polarity : Bool) ρ)
    {c : Clause s} (h_c_eq : c = ({lit} : Clause s))
    (π : TreeLikeResolution φ c) :
    ∃ π' : TreeLikeResolution (φ.substitute ρ) (BotClause (s \ {lit.variable})),
      π'.size ≤ π.size := by
  have h_subst : c.substitute ρ = BotClause (s \ {lit.variable}) := by
    rw [h_c_eq]; exact lit_subst_is_Bot_false lit ρ h_ρ
  rcases resolution_restrict ρ π with h_none | ⟨c_res, h_cres, c', h_sub, π', _, h_size⟩
  · grind
  · have h_eq1 : c_res = BotClause (s \ {lit.variable}) := by grind
    subst h_eq1
    have h_eq2 : c' = BotClause (s \ {lit.variable}) := Finset.subset_empty.mp h_sub
    subst h_eq2
    exact ⟨π', h_size⟩

theorem width_imply_size_ind_version (W : ℕ)
    (W_c : ℕ) :
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
        let v : Variable := (getRootVariable π).get (Option.ne_none_iff_isSome.mp h_xx)
        have h_v_incl : v ∈ s :=
          root_var_in_vars π v (Option.some_get _).symm

        let smaller_set := s.erase v

        have h_sub : smaller_set ⊂ s := Finset.erase_ssubset h_v_incl

        have ih' := ih smaller_set

        simp_all

        cases π with
        | axiom_clause h_in =>
          exact False.elim (h_xx rfl)
        | resolve c₁ c₂ v' h_v_in_vars h_not_in π₁ π₂ h_res =>
          have h_pow : 2 ^ W = 2 ^ (W - 1) + 2 ^ (W - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h_W_neq)]
            rw [pow_succ, Nat.mul_two]
          have idea₁ : π₁.size ≤ 2^(W - 1) ∨ π₂.size ≤ 2^(W - 1) :=
            size_split (by unfold TreeLikeResolution.size at h_size; omega)
          have h_gen_size_lb : π₁.size ≤ 2^(W) ∧ π₂.size ≤ 2^(W) := by
            unfold TreeLikeResolution.size at h_size; omega

          let ρ_true : Assignment {v} := (fun _ => fun _ => True)
          let ρ_false : Assignment {v} := (fun _ => fun _ => False)

          obtain ⟨h_res_left, h_res_right⟩ := h_res

          have temp_fact_2 : c₂ = ({v'.toLiteral h_v_in_vars false} : Clause s) := by
            unfold IsRegularRes at h_reg
            refine Finset.Subset.antisymm ?_ ?_
            · simpa [BotClause] using h_res_right
            have h_v_in_c : v' ∈ c₂.variables := by grind
            have := var_incl v' c₂ h_v_in_vars h_v_in_c
            grind

          have h_π_1_existence :
              ∃ (π_1 : TreeLikeResolution (φ.substitute ρ_true) (BotClause (s \ {v}))),
              (π_1.size ≤ π₂.size) :=
            bot_refut_of_falsified_lit (v'.toLiteral h_v_in_vars false) ρ_true (by rfl)
              temp_fact_2 π₂

          obtain ⟨π_1, h_π_1⟩ := h_π_1_existence

          have temp_fact_1 : c₁ = ({v'.toLiteral h_v_in_vars true} : Clause s) := by
            unfold IsRegularRes at h_reg
            refine Finset.Subset.antisymm ?_ ?_
            · simpa [BotClause] using h_res_left
            have h_v_in_c : v' ∈ c₁.variables := by grind
            have := var_incl v' c₁ h_v_in_vars h_v_in_c
            grind

          have h_π_2_existence :
              ∃ (π_2 : TreeLikeResolution (φ.substitute ρ_false) (BotClause (s \ {v}))),
              (π_2.size ≤ π₁.size) :=
            bot_refut_of_falsified_lit (v'.toLiteral h_v_in_vars true) ρ_false (by rfl)
              temp_fact_1 π₁

          obtain ⟨π_2, h_π_2⟩ := h_π_2_existence

          have h_clause_subs_width_true : ∀ C ∈ φ.substitute ρ_true, Finset.card C ≤ W_c :=
            clause_card_substitute_le h_clause_card
          have h_clause_subs_width_false : ∀ C ∈ φ.substitute ρ_false, Finset.card C ≤ W_c :=
            clause_card_substitute_le h_clause_card

          cases idea₁ with
          | inr h_size₁ =>
              have idea_0 : π_1.size ≤ 2 ^ (W - 1) := by grind
              have ineq₁ : W - 1 < W := by grind
              have ih_1 := ih_0 (W - 1) ineq₁
                (s \ {v}) (φ.substitute ρ_true) h_clause_subs_width_true π_1 idea_0
              obtain ⟨π_1', idea_00'⟩ := ih_1
              have idea_10 : π_2.size ≤ 2^(W) := by
                trans π₁.size
                · exact h_π_2
                · exact h_gen_size_lb.left
              have : smaller_set = s \ {v} := Finset.erase_eq s v
              rw[this] at ih'
              have ih'_1 := ih' (φ.substitute ρ_false) h_clause_subs_width_false π_2 idea_10
              obtain ⟨π_2', idea_11⟩ := ih'_1
              obtain ⟨π_final, conclusion⟩ :=
                width_ind_combine (by omega) h_clause_card (v.toLiteral h_v_incl true)
                rfl rfl π_1' idea_00' π_2' idea_11
              use π_final
              grind


          | inl h_size₂ =>
              have idea_0 : π_2.size ≤ 2 ^ (W - 1) := by grind
              have ineq₁ : W - 1 < W := by grind
              have ih_1 := ih_0 (W - 1) ineq₁
                (s \ {v}) (φ.substitute ρ_false) h_clause_subs_width_false π_2 idea_0
              obtain ⟨π_2', idea_00'⟩ := ih_1
              have idea_10 : π_1.size ≤ 2^(W) := by
                trans π₂.size
                · exact h_π_1
                · exact h_gen_size_lb.right
              have : smaller_set = s \ {v} := Finset.erase_eq s v
              rw[this] at ih'
              have ih'_1 := ih' (φ.substitute ρ_true) h_clause_subs_width_true π_1 idea_10
              obtain ⟨π_1', idea_11⟩ := ih'_1
              obtain ⟨π_final, conclusion⟩ :=
                width_ind_combine (by omega) h_clause_card (v.toLiteral h_v_incl false)
                rfl rfl π_2' idea_00' π_1' idea_11
              use π_final
              grind

theorem width_imply_size (W : ℕ) (W_c : ℕ)
    (vars) (φ : CNFFormula vars)
    (h_W_c : ∀ C ∈ φ, C.card ≤ W_c)
    (π : TreeLikeRefutation φ)
    (h_size : π.size ≤ 2 ^ W) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W + W_c := by
    exact width_imply_size_ind_version W W_c vars φ h_W_c π h_size
