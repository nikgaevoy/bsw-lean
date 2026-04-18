import BSWLean.Treelike
import BSWLean.TinyConversions
import Mathlib.Data.Finset.Basic



lemma lit_subst_is_Bot_false {vars}
    (l : Literal vars)
    (ρ_false : (Assignment ({l.variable} : Finset Variable)))
    (h_value : ρ_false = (fun _ _ => (¬l.polarity : Bool))) :
    ({l} : Clause vars).substitute ρ_false = BotClause (vars \ {l.variable}):= by
  unfold Clause.substitute
  subst h_value
  simp_all only [Bool.not_eq_true, Bool.decide_eq_false, Option.ite_none_left_eq_some,
    Option.some.injEq]
  apply And.intro
  · have : l.variable ∈ (vars ∩ {l.variable}) := by aesop
    let l' : Literal (vars ∩ {l.variable}) := l.convert (vars ∩ {l.variable}) this
    have : (({l} : Clause vars).split {l.variable}).1 = ({l'} :
        Clause ((vars) ∩ {l.variable})) := by
      unfold Clause.split
      simp_all [l']
      unfold Literal.convert
      aesop
    simp_all only [l']
    unfold Literal.convert Assignment.restrict Clause.eval Literal.eval
    aesop
  · aesop



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

  have : Clause.convert {lit} vars
      (by intro l h_l; have q := Literal.variable_mem_vars l; aesop) =
      {lit.convert vars var_incl} := by
    grind [Clause.convert]
  rw [←this]
  unfold Clause.combine
  unfold Clause.convert_trivial
  simp only [carry_through_convert, Finset.union_assoc]
  apply Finset.union_subset
  swap
  · grind
  rw [←Finset.union_assoc]
  apply remove_middle_subset
  rw [this]
  trans ((c_1 ∪ {lit}).convert vars (by grind [subset_of_vars_clause]))
  · aesop
  grind [carry_through_convert, loose_convert, Clause.convert_convert, subset_refl]



lemma sdiff_disjUnion_eq_vars {vars sub_vars : Variables} (h_subset : sub_vars ⊆ vars) :
    Finset.disjUnion (vars \ sub_vars) sub_vars Finset.sdiff_disjoint = vars := by
  aesop

lemma var_in_vars_of_in_sdiff {vars sub_vars : Variables} {var : Variable}
    (h_4 : var ∈ vars \ sub_vars) : var ∈ vars := by
  grind

lemma resolve_unsubstitute_subset (vars sub_vars : Variables) (φ : CNFFormula vars)
    (var : Variable) (ρ : Assignment sub_vars) (c_2 c_3 : Clause (vars \ sub_vars))
    (h_subset : sub_vars ⊆ vars) (h_4 : var ∈ vars \ sub_vars)
    (p_1 : TreeLikeResolution (φ.substitute ρ) c_2)
    (p_2 : TreeLikeResolution (φ.substitute ρ) c_3)
    (inter_proof : Finset.disjUnion (vars \ sub_vars) sub_vars Finset.sdiff_disjoint = vars) :
    ((p_1.unsubstitute_rhs ρ).resolve (p_2.unsubstitute_rhs ρ) var
       (Finset.sdiff_subset h_4 : var ∈ vars)) ⊆
    (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial
      vars inter_proof).resolve
      ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial
        vars inter_proof) var (Finset.sdiff_subset h_4 : var ∈ vars)) := by
  grind only [TreeLikeResolution.unsubstitute_rhs_variables, resolve_subsets]

lemma resolve_combined_le_c1 (vars sub_vars : Variables) (var : Variable)
    (ρ : Assignment sub_vars) (c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_4 : var ∈ vars \ sub_vars)
    (inter_proof : Finset.disjUnion (vars \ sub_vars) sub_vars Finset.sdiff_disjoint = vars)
    (var_incl : var ∈ vars)
    (left : c_2 ⊆ c_1 ∪ {var.toLiteral h_4})
    (right : c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4}) :
    Finset.card (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial
     vars inter_proof).resolve
      ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars
        inter_proof) var var_incl) ≤
    Finset.card ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial
       vars inter_proof) := by

  have idea₃ := inter_idea_new_version vars sub_vars
    (var.toLiteral h_4) ρ c_1 c_2 inter_proof var_incl left
  have idea₄ := inter_idea_new_version vars sub_vars
     (var.toNegLiteral h_4) ρ c_1 c_3 inter_proof var_incl right
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
    (left : c_2 ⊆ c_1 ∪ {var.toLiteral h_4})
    (right : c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4}) :
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
  · exact Finset.card_le_card
      (resolve_unsubstitute_subset vars sub_vars φ var ρ c_2 c_3 h_subset h_4 p_1 p_2 inter_proof)

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
    (x : Literal vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : ρ_true = (fun _ _ => (x.polarity : Bool)))
    (h_1 : ∀ l ∈ ρ_true.toClause, l.variable ∈ vars) :
    (ρ_true.toClause).convert vars h_1 = ({x.negate} : Clause vars) := by
  unfold Literal.negate Assignment.toClause Clause.convert
  aesop



lemma ufold_one_literal {vars} {φ : CNFFormula vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : ρ_true = (fun _ _ => (x.polarity : Bool)))
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
    grind [trivial_subs_unfold, Clause.convert_convert, subset_refl]


--lemma local_convertion

lemma single_literal_conversion {vars₁ vars₂ : Variables} {lit : Literal vars₁}
    {v_new_mem : lit.variable ∈ vars₂} {h} :
    ({lit} : Clause vars₁).convert vars₂ h
      = ({ ⟨⟨lit.variable, v_new_mem⟩, lit.polarity⟩ } : Clause vars₂) := by
  unfold Clause.convert
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
    induction π₁
    · aesop
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
        let π₂ := TreeLikeResolution.axiom_clause (by aesop)

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
        aesop

      have fact₂ : ∀ l ∈ c₂, l.variable ∈ vars₂ := by
        aesop

      have fact₀ :  ∀ l ∈ C, l.variable ∈ vars₂ := by
        aesop

      have h_resolve : c₁.convert vars₂ fact₁ ⊆ C.convert vars₂ fact₀ ∪ {v.toLiteral v_new_mem} ∧
        c₂.convert vars₂ fact₂ ⊆ C.convert vars₂ fact₀ ∪ {v.toNegLiteral v_new_mem} := by


        constructor

        · clear idea fact₂ h_v_not h_width
            idea₁ idea₂ idea' h_conv π_a_new π_a π_b h_wa π_b_new h_wb π₁ φ φ₁

          trans (C ∪ ({v.toLiteral h_v_mem} : Clause vars₁)).convert vars₂ (by aesop)
          · grind only [loose_convert]
          · grind [single_literal_conversion,
              carry_through_convert, Finset.subset_of_eq, loose_convert]


        · clear idea h_v_not h_width fact₁
            idea₁ idea₂ idea' h_conv π_a_new π_a π_b h_wa π_b_new h_wb π₁ φ φ₁

          trans (C ∪ ({v.toNegLiteral h_v_mem} : Clause vars₁)).convert vars₂ (by aesop)
          · grind only [loose_convert]
          · grind [single_literal_conversion,
              carry_through_convert, Finset.subset_of_eq, loose_convert]


      -- 3. Construct the new resolution node
      let π_new := TreeLikeResolution.resolve
        (c₁.convert vars₂ fact₁)
        (c₂.convert vars₂ fact₂)
        v v_new_mem (by aesop) π_a_new π_b_new h_resolve

      ⟨π_new, by
        -- width is max of |C_new| and the sub-widths.
        -- All these are ≤ W because the original ones were.
        unfold TreeLikeResolution.width
        aesop⟩

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
    (h_C2_in_φ : C_2 ∈ φ)
    (h_C2_sub : C_2 ⊆ C_0 ∪ {x})
    (h_C0_card : C_0.card ≤ W + 1)
    (h_C2_card : C_2.card ≤ W + 1)
    (π_neg : TreeLikeResolution φ {x.negate})
    (h_neg_width : π_neg.width ≤ W + 1) :
    ∃ π : TreeLikeResolution φ C_0, π.width ≤ W + 1 := by
  let v := x.variable
  have h_val : v ∈ vars := Literal.variable_mem_vars x
  cases hpol : x.polarity with
  | true =>
    have hvx : v.toLiteral h_val = x := Literal.ext rfl hpol.symm
    have hxn : x.negate = v.toNegLiteral h_val :=
      Literal.ext rfl (by simp [Literal.negate, Variable.toNegLiteral, hpol])
    exact ⟨TreeLikeResolution.resolve C_2 {x.negate} v h_val h_v_not_mem
        (TreeLikeResolution.axiom_clause h_C2_in_φ) π_neg
        ⟨by rw [hvx]; exact h_C2_sub, by rw [hxn]; exact Finset.subset_union_right⟩,
      by unfold TreeLikeResolution.width; grind [TreeLikeResolution.width]⟩
  | false =>
    have hvx : v.toNegLiteral h_val = x :=
      Literal.ext rfl (by simp [Variable.toNegLiteral, hpol])
    have hxn : x.negate = v.toLiteral h_val :=
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
    (h_value : ρ_true = (fun _ _ => (x.polarity : Bool)))
    (ρ_false : (Assignment ({x.variable} : Finset Variable)))
    (h_value_false : ρ_false = (fun _ _ => (¬x.polarity : Bool)))
    (W : ℕ) (π_1 : TreeLikeRefutation (φ.substitute ρ_true)) (h_width_true : π_1.width ≤ W)
    (π_2 : TreeLikeRefutation (φ.substitute ρ_false)) (h_width_false : π_2.width ≤ W + 1)
    (h_clause_card : ∀ C ∈ φ, C.card ≤ W + 1) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W + 1 := by


  let π_1_unfolded := TreeLikeResolution.unsubstitute ρ_true π_1 (by aesop)

  have idea₀ : (TreeLikeResolution.unsubstitute_rhs ρ_true π_1) ⊆ ({x.negate}) := by
    exact ufold_one_literal x h₀ ρ_true h_value π_1 (by aesop)


  have idea₁ : π_1_unfolded.width ≤ W + 1 := by
    grind [unsub_increase_width]

  have fact₁ : (C : Clause (vars \ {x.variable})) -> (∀ l ∈ C, l.variable ∈ vars) := by
    grind


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

    have idea₂ : ∀ C ∈ φ_subs_false_conv, ∃ (π : TreeLikeResolution φ C), π.width ≤ W + 1 := by

      intro C_0 h_c
      have entry₁ : ∃ C_1 ∈ φ_subs_false_unconv,
          (C_1.convert vars (by exact fun l a ↦ (fact₁) C_1 l a)) = C_0 := by
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
        rw [← h_C_1_conv_right]
        exact clause_substitute_convert_subset h_C_2_conv.right (fun l a ↦ fact₁ C_1 l a)

      obtain ⟨left, right⟩ := h_C_2_conv


      have h_v_not_mem_c : x.variable ∉ C_0.variables := by
        have h_prep : x.variable ∉ C_1.variables := by
          intro h_mem
          rcases Finset.mem_image.1 h_mem with ⟨l, _, hl_eq⟩
          have h_in := var_mem_of_literal_mem l
          rw [hl_eq] at h_in
          simp at h_in
        aesop


      let π_new : TreeLikeResolution φ {x.negate} := h_eq ▸ π_1_unfolded
      unfold π_1_unfolded at idea₁
      have idea_new : π_new.width ≤ W + 1 := by grind

      exact resolve_axiom_with_negate h_v_not_mem_c left idea₂
        ((Finset.card_le_card this_1).trans (h_clause_card C_2 left))
        (h_clause_card C_2 left) π_new idea_new

    have idea₃ :
        ∃ (π : TreeLikeResolution φ_subs_false_conv (BotClause (vars))), π.width ≤ W + 1 := by
      let φ₁ : CNFFormula vars := (CNFFormula.simple_convert vars₁ vars φ_subs_false_unconv h_subs)
      have idea_subs : φ_subs_false_conv = φ₁ := by
        subst h_value
        simp_all only [Bool.not_eq_true, Bool.decide_eq_false,
          subset_refl, φ_subs_false_conv, vars₁, φ_subs_false_unconv, π_1_unfolded, φ₁]
      have int_proof : ∀ l ∈ BotClause vars₁, l.variable ∈ vars := by
        intro l a
        subst h_value
        simp_all only [Finset.notMem_empty, φ_subs_false_conv, vars₁,
          φ_subs_false_unconv, φ₁]
      have Bot_equiv : ((BotClause vars₁).convert vars int_proof) = BotClause vars := by
        subst h_value
        simp_all only [Bool.not_eq_true, Bool.decide_eq_false,
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
  {v.toLiteral h_v_in_vars} ⊆ C ∨ {v.toNegLiteral h_v_in_vars} ⊆ C := by
  unfold Clause.variables at h_sub
  unfold Literal.variable at h_sub
  simp_all
  obtain ⟨a, h_sub⟩ := h_sub
  obtain ⟨h_sub_left, h_sub_right⟩ := h_sub
  by_cases a.polarity
  case pos h_v =>
    have : a = v.toLiteral h_v_in_vars := by aesop (add safe unfold Variable.toLiteral)
    grind
  case neg h_v =>
    have : a = v.toNegLiteral h_v_in_vars := by aesop (add safe unfold Variable.toNegLiteral)
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
    (h_lit_A : ρ_A = (fun _ _ => (lit.polarity : Bool)))
    (h_lit_B : ρ_B = (fun _ _ => (¬lit.polarity : Bool)))
    (π_A' : TreeLikeRefutation (φ.substitute ρ_A))
    (h_A_width : π_A'.width ≤ (W - 1) + W_c)
    (π_B' : TreeLikeRefutation (φ.substitute ρ_B))
    (h_B_width : π_B'.width ≤ W + W_c) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W + W_c - 1 + 1 :=
  width_combine s lit (Literal.variable_mem_vars lit)
    ρ_A h_lit_A ρ_B h_lit_B (W + W_c - 1)
    π_A' (by omega) π_B' (by omega)
    (fun C hC => (h_clause_card C hC).trans (by omega))

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
                width_ind_combine (by omega) h_clause_card (v.toLiteral h_v_incl)
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
                width_ind_combine (by omega) h_clause_card (v.toNegLiteral h_v_incl)
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
