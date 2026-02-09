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
  : (C.convert vars₂ h).card ≥  C.card := by
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
    simp_all only [Literal.variable_mem_vars, implies_true, Clause.convert_convert, Clause.convert_self, ge_iff_le]

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

@[simp]
lemma subset_combine {vars₁ vars₂} (c₁ c₂ : Clause vars₁) (c' : Clause vars₂)
    (h_disj : Disjoint vars₁ vars₂) :
    (Clause.combine c₁ c' h_disj) ⊆ (Clause.combine c₂ c' h_disj) ↔ c₁ ⊆ c₂ := by
  sorry

