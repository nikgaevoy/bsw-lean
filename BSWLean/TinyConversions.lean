import BSWLean.Treelike

@[simp]
lemma trivial_convert_card {vars₁ vars₂} {C : Clause vars₁} {h}
  : (C.convert_trivial vars₂ h).card = C.card := by
  refine Set.BijOn.finsetCard_eq ?_ ?_
  intro lit₁
  subst h
  exact lit₁
  subst h
  simp_all only
  constructor
  unfold Clause.convert_trivial
  unfold Clause.convert
  simp
  exact fun ⦃x⦄ a ↦ a
  unfold Clause.convert_trivial
  unfold Clause.convert
  simp
  refine Finset.surjOn_of_injOn_of_card_le (fun lit₁ ↦ lit₁) (fun ⦃x⦄ a ↦ a) ?_ ?_
  exact Function.Injective.injOn fun ⦃a₁ a₂⦄ a ↦ a
  exact (Finset.eq_iff_card_ge_of_superset fun ⦃a⦄ a_1 ↦ a_1).mpr rfl

@[simp]
lemma filterMap_card {α β} [DecidableEq α] [DecidableEq β] (s : Finset α) {f : α → Option β} {h} :
    Finset.card (s.filterMap f h) ≤ Finset.card s := by
  induction s using Finset.induction_on
  case empty =>
    rfl
  case insert a s' h_a ih =>
    have : (insert a s').card = s'.card + 1 := by
      exact Finset.card_insert_of_notMem h_a
    rw [this]
    trans (Finset.filterMap f s' h).card + 1
    swap
    · simp [ih]
    let b : Finset β := if h : (f a).isSome then {(f a).get h} else ∅
    have : b.card ≤ 1 := by aesop
    trans ((Finset.filterMap f s' h) ∪ b).card
    swap
    · simp_all only [b]
      split
      next h_1 =>
        grind
      next h_1 =>
        simp_all
    refine (Finset.eq_iff_card_ge_of_superset ?_).mpr ?_
    · grind
    · grind


@[simp]
lemma convert_card_ineq {vars₁ vars₂} {C : Clause vars₁} {h}
  : (C.convert vars₂ h).card ≤  C.card := by
  unfold Clause.convert
  exact filterMap_card C

@[simp]
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

    sorry
