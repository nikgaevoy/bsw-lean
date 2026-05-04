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

lemma convert_card_ineq {vars₁ vars₂} {C : Clause vars₁} {h}
  : (C.convert vars₂ h).card ≤ C.card := by
  unfold Clause.convert
  exact filterMap_card C

lemma convert_card_ineq_oppsite {vars₁ vars₂} {C : Clause vars₁} {h}
  : (C.convert vars₂ h).card ≥ C.card := by
  have h₂ : ∀ l ∈ (C.convert vars₂ h), l.variable ∈ vars₁ := fun _ _ => by
    aesop (add safe unfold Clause.convert)
  simpa using convert_card_ineq (C := C.convert vars₂ h) (h := h₂)

@[simp]
lemma convert_card {vars₁ vars₂} {C : Clause vars₁} {h} :
    (C.convert vars₂ h).card = C.card :=
  Nat.le_antisymm convert_card_ineq convert_card_ineq_oppsite

@[simp]
lemma trivial_convert_card {vars₁ vars₂} {C : Clause vars₁} {h} :
    (C.convert_trivial vars₂ h).card = C.card := by
  unfold Clause.convert_trivial; exact convert_card



lemma to_clause_card_less_than_sub_vars_card {sub_vars : Variables} (ρ : Assignment sub_vars) :
  (Finset.card ρ.toClause ≤ Finset.card sub_vars) := by
  unfold Assignment.toClause
  exact filterMap_card sub_vars

@[simp]
lemma subset_combine {vars₁ vars₂} (c₁ c₂ : Clause vars₁) (c' : Clause vars₂)
    (h_disj : Disjoint vars₁ vars₂) :
    (Clause.combine c₁ c' h_disj) ⊆ (Clause.combine c₂ c' h_disj) ↔ c₁ ⊆ c₂ := by
  unfold Clause.combine
  refine ⟨fun h_subset l h_l_in_c₁ => ?_, fun h_subset => Finset.union_subset_union_left (by aesop)⟩
  rw [Finset.union_subset_iff] at h_subset
  have h_l_conv : l.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ∈
      c₂.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ∪
      c'.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) :=
    h_subset.1 (by aesop (add safe unfold Clause.convert))
  rw [Finset.mem_union] at h_l_conv
  rcases h_l_conv with h | h
  · simpa using h
  · exfalso
    have h_v₁ : l.variable ∈ vars₁ := Literal.variable_mem_vars l
    have h_v₂ : l.variable ∈ vars₂ := by
      have := literal_in_clause_variables h
      rw [Clause.convert_keeps_variables] at this
      exact clause_variables_subset_vars c' this
    exact Finset.disjoint_left.mp h_disj h_v₁ h_v₂

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
    all_goals aesop
  case neg =>
    right
    unfold Clause.substitute Clause.split Clause.shrink Clause.convert
    simp only [Finset.mem_singleton, Finset.mem_filter, Option.get_ite', Finset.mem_filterMap,
      Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self]
    refine ⟨t.restrict (vars \ {l.variable}) (by aesop), ⟨t, by aesop⟩, ?_⟩
    unfold Literal.convert Literal.restrict
    aesop


@[aesop safe]
lemma proof_size_positive {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) : π.size > 0 := by
  unfold TreeLikeResolution.size
  aesop

lemma size_one_proof {vars} (φ : CNFFormula vars)
    (W_c : ℕ) (h_clause_card : ∀ C ∈ φ, C.card ≤ W_c) (π : TreeLikeRefutation φ)
    (h_size : π.size ≤ 1) :
     π.width ≤ W_c := by
  cases π with
  | axiom_clause h_in => aesop
  | resolve _ _ _ _ _ π₁ π₂ _ =>
    have := proof_size_positive π₁
    have := proof_size_positive π₂
    simp [TreeLikeResolution.size] at h_size
    omega

/-- Substituting a clause by an assignment that falsifies every literal yields the empty clause. -/
lemma clause_subst_eq_bot_of_falsified {vars sub_vars}
    (c : Clause vars) (ρ : Assignment sub_vars)
    (h : ∀ l ∈ c, ∃ h_mem : l.variable ∈ sub_vars, ρ l.variable h_mem ≠ l.polarity) :
    c.substitute ρ = BotClause (vars \ sub_vars) := by
  unfold Clause.substitute Clause.split Clause.shrink BotClause
  simp_all only [Bool.not_eq_true, Option.ite_none_left_eq_some, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rw [Clause.eval_eq_false_iff_all_falsified_literals]
    intro l' hl'
    simp only [Finset.mem_filterMap, Finset.mem_filter, Option.dite_none_right_eq_some,
      Option.some.injEq, and_exists_self] at hl'
    obtain ⟨l, ⟨hl_in, _⟩, rfl⟩ := hl'
    simpa [Literal.eval, Assignment.restrict, Literal.restrict] using (h l hl_in).2
  · ext l'
    simp only [Finset.mem_filterMap, Finset.mem_filter, Option.dite_none_right_eq_some,
      Option.some.injEq, and_exists_self, Finset.notMem_empty, iff_false, not_exists]
    rintro l ⟨hl_in, hl_not_in⟩ _
    exact hl_not_in (h l hl_in).1

#lint
