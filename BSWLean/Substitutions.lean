import BSWLean.CNF

/-!
# Partial substitution to a formula

This file defines all basic structures to work with: Variables, Literals, Clauses,
CNF-Formulas, and Assignments.

## Implementation notes

Because applying a partial assignment changes the set of variables, this file also provides a ton
of functions for conversions between different sets of variables.

Another point of interest is `filterMap_card` function. It turns out that this statement was not
proven in the standard library, so we proved it here by induction.
-/


/-- Converts a literal to a literal over different set of variables. -/
@[aesop safe [unfold]]
def Literal.restrict {vars} (l : Literal vars) (sub_vars : Variables)
    (h_mem : l.variable ∈ sub_vars) : Literal sub_vars :=
  Literal.mk ⟨l.variable, h_mem⟩ l.polarity

@[simp, grind =]
lemma Literal.restrict_polarity {vars sub_vars} {l : Literal vars} (h_mem) :
    (l.restrict sub_vars h_mem).polarity = l.polarity := by aesop

@[simp, grind =]
lemma Literal.restrict_variable {vars sub_vars} {l : Literal vars} (h_mem) :
    (l.restrict sub_vars h_mem).variable = l.variable := by aesop

@[simp, grind =]
lemma Literal.restrict_toLiteral {vars sub_vars} {v : Variable} (h₁ : v ∈ vars) (h₂) (p : Bool) :
    ((v.toLiteral h₁ p).restrict sub_vars h₂) = (v.toLiteral h₂ p) := by aesop

lemma Literal.restrict_inj {vars sub_vars} {l₁ l₂ : Literal vars}
    (h_l₁_mem : l₁.variable ∈ sub_vars) (h_l₂_mem : l₂.variable ∈ sub_vars)
    (h_eq : l₁.restrict sub_vars h_l₁_mem = l₂.restrict sub_vars h_l₂_mem) : l₁ = l₂ := by aesop

/-- Converts a clause to a clause with different set of variables. -/
@[simp]
def Clause.shrink {vars} (c : Clause vars) (keep_vars : Variables)
    (h_mem : ∀ l, l ∈ c → l.variable ∈ keep_vars) : Clause keep_vars :=
  let f := fun l : Literal vars =>
      if h : l ∈ c then some (l.restrict keep_vars (h_mem l h)) else none

  c.filterMap f <| by aesop

/-- Splits clause `c` into two clauses `c_in` and `c_out` based on inclusion of literals to
`sub_vars`. It is guaranteed that `c = c_in ∨ c_out`. -/
@[simp]
def Clause.split {vars} (c : Clause vars) (split_vars : Variables) :
    (Clause (vars ∩ split_vars)) × (Clause (vars \ split_vars)) :=
  let c_in := c.filter (fun l => l.variable ∈ split_vars)
  let c_out := c.filter (fun l => l.variable ∉ split_vars)

  -- h_out has to be written explicitly for some reason
  have h_out : ∀ l, l ∈ c_out → l.variable ∈ (vars \ split_vars) := by aesop

  let c_in' := Clause.shrink c_in (vars ∩ split_vars) <| by aesop
  let c_out' := Clause.shrink c_out (vars \ split_vars) h_out

  (c_in', c_out')

/-- Generates a partial assignment over a subset of variables. -/
def Assignment.restrict {vars} (ρ : Assignment vars) (sub_vars : Variables)
    (h_subset : sub_vars ⊆ vars) : Assignment sub_vars :=
  fun v h_v_mem_sub_vars => ρ v (h_subset h_v_mem_sub_vars)

@[simp]
lemma Assignment.double_restrict {vars sub_vars₁ sub_vars₂} (ρ : Assignment vars)
    (h_subset₁ : sub_vars₁ ⊆ vars) (h_subset₂ : sub_vars₂ ⊆ sub_vars₁) :
    (ρ.restrict sub_vars₁ h_subset₁).restrict sub_vars₂ h_subset₂ =
    ρ.restrict sub_vars₂ (by exact fun ⦃a⦄ a_1 ↦ h_subset₁ (h_subset₂ a_1)) := by
  rfl

@[simp]
lemma Literal.restrict_correctness {vars sub_vars} {l : Literal vars} {ρ : Assignment vars}
    (h_subset : sub_vars ⊆ vars) (h_l : l.variable ∈ sub_vars) :
    (l.restrict sub_vars h_l).eval (ρ.restrict sub_vars h_subset) = l.eval ρ := by aesop

/-- Substitutes a partial assignment to a clause. Returns none if clause is satisfied and
the clause after substitution otherwise. -/
def Clause.substitute {vars sub_vars} (c : Clause vars) (ρ : Assignment sub_vars) :
    Option (Clause (vars \ sub_vars)) :=
  let (c_in, c_out) := Clause.split c sub_vars

  if c_in.eval (ρ.restrict (vars ∩ sub_vars) Finset.inter_subset_right) then
    none
  else
    some c_out

@[aesop unsafe]
lemma Clause.substitute_maintains_subset {vars sub_vars} {c₁ c₂ : Clause vars}
    {h_subset : c₁ ⊆ c₂} (ρ : Assignment sub_vars) (h₁) (h₂) :
    ((c₁.substitute ρ).get h₁ ⊆ (c₂.substitute ρ).get h₂) := by
  intro _
  aesop (add safe unfold Clause.substitute)

lemma Clause.substitute_eq_none_iff_eval_subclause_true {vars sub_vars} (c : Clause vars)
    (ρ : Assignment sub_vars) :
    c.substitute ρ = none ↔
    (c.split sub_vars).1.eval (ρ.restrict (vars ∩ sub_vars) Finset.inter_subset_right) := by
  aesop (add safe unfold Clause.substitute)

lemma Clause.substitute_isSome_iff_eval_subclause_false {vars sub_vars} (c : Clause vars)
    (ρ : Assignment sub_vars) :
    (c.substitute ρ).isSome ↔
    ¬(c.split sub_vars).1.eval (ρ.restrict (vars ∩ sub_vars) Finset.inter_subset_right) := by
  rw [← @substitute_eq_none_iff_eval_subclause_true]
  exact Option.isSome_iff_ne_none

@[simp]
lemma Assignment.restrict_correctness {vars} {h} (ρ : Assignment vars) : ρ.restrict vars h = ρ := by
  rfl

lemma Clause.split_correctness {vars} (c : Clause vars) (sub_vars : Variables)
    (ρ : Assignment vars) :
    c.eval ρ = ((c.split sub_vars).1.eval (ρ.restrict (vars ∩ sub_vars) (by aesop)) ||
                (c.split sub_vars).2.eval (ρ.restrict (vars \ sub_vars) (by aesop))) := by
  by_cases h_c : c.eval ρ

  case pos =>
    rw [h_c]
    simp only [Bool.true_eq, Bool.or_eq_true]
    rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at h_c
    obtain ⟨l, h_l_in_c, h_l_eval_ρ⟩ := h_c
    by_cases h_l_in_c_in : l.variable ∈ sub_vars
    case pos =>
      left
      rw [Clause.eval_eq_true_iff_exists_satisfied_literal]
      let l' := l.restrict (vars ∩ sub_vars) (by aesop)
      have h_l'_in_c_in : l' ∈ (c.split sub_vars).1 := by
        unfold Clause.split Clause.shrink
        simp only [Finset.mem_filter, Finset.mem_filterMap, Option.dite_none_right_eq_some,
          Option.some.injEq, and_exists_self]
        use l
        have : l ∈ c ∧ l.variable ∈ sub_vars := by aesop
        use this
      have h_l'_eval : l'.eval (ρ.restrict (vars ∩ sub_vars) (by aesop)) := by
        unfold l'
        aesop

      use l'
    case neg =>
      right
      rw [Clause.eval_eq_true_iff_exists_satisfied_literal]
      let l' := l.restrict (vars \ sub_vars) (by aesop)
      have h_unfold : l' = l.restrict (vars \ sub_vars) (by aesop) := by
        rfl
      have h_l'_in_c_in : l' ∈ (c.split sub_vars).2 := by
        unfold Clause.split Clause.shrink
        simp only [Finset.mem_filter, Finset.mem_filterMap, Option.dite_none_right_eq_some,
          Option.some.injEq, and_exists_self]
        use l
        have : l ∈ c ∧ l.variable ∉ sub_vars := by
          constructor
          · assumption
          · assumption
        use this
      have h_l'_eval : l'.eval (ρ.restrict (vars \ sub_vars) (by aesop)) := by
        rw [h_unfold]
        aesop

      use l'

  case neg =>
    simp at h_c
    rw [h_c]
    simp only [Bool.false_eq, Bool.or_eq_false_iff]
    constructor
    · rw [@eval_eq_false_iff_all_falsified_literals]
      intro l₁ h_l₁_in_c_in
      rw [Clause.split] at h_l₁_in_c_in
      unfold Clause.shrink at h_l₁_in_c_in
      simp only [Finset.mem_filter, Finset.mem_filterMap, Option.dite_none_right_eq_some,
        Option.some.injEq, and_exists_self] at h_l₁_in_c_in
      obtain ⟨l₂, h_l₂_in_c, h_l₂_vars⟩ := h_l₁_in_c_in
      rw [Clause.eval_eq_false_iff_all_falsified_literals] at h_c
      aesop
    · rw [@eval_eq_false_iff_all_falsified_literals]
      intro l₁ h_l₁_in_c_in
      rw [Clause.split] at h_l₁_in_c_in
      unfold Clause.shrink at h_l₁_in_c_in
      simp only [Finset.mem_filter, Finset.mem_filterMap, Option.dite_none_right_eq_some,
        Option.some.injEq, and_exists_self] at h_l₁_in_c_in
      obtain ⟨l₂, h_l₂_in_c, h_l₂_vars⟩ := h_l₁_in_c_in
      rw [Clause.eval_eq_false_iff_all_falsified_literals] at h_c
      aesop

/-- Partial substitution to a formula. -/
@[aesop safe [unfold]]
def CNFFormula.substitute {vars sub_vars} (φ : CNFFormula vars)
    (ρ : Assignment sub_vars) : CNFFormula (vars \ sub_vars) :=
  let f := fun c : Clause vars => c.substitute ρ

  let φ' := (φ.image f).filterMap id

  φ' (by exact fun a a' b a_1 a_2 ↦ Option.eq_of_mem_of_mem a_1 a_2)

lemma CNFFormula.substitute_preimage {vars sub_vars} {φ : CNFFormula vars}
    {ρ : Assignment sub_vars} {c} (h_c : c ∈ φ.substitute ρ) :
    ∃ c' ∈ φ, c'.substitute ρ = some c := by aesop

@[aesop unsafe]
lemma Clause.substitute_isSome_subset {vars sub_vars} {c₁ c₂ : Clause vars}
    {ρ : Assignment sub_vars} (h_subset : c₁ ⊆ c₂) (h : (c₂.substitute ρ).isSome) :
    (c₁.substitute ρ).isSome := by
  rw [Clause.substitute_isSome_iff_eval_subclause_false] at *
  simp_all only [Bool.not_eq_true]
  rw [Clause.eval_eq_false_iff_all_falsified_literals] at *
  suffices (c₁.split sub_vars).1 ⊆ (c₂.split sub_vars).1 by aesop
  intro l
  aesop

@[aesop unsafe]
lemma Clause.substitute_isNone_subset {vars sub_vars} {c₁ c₂ : Clause vars}
    {ρ : Assignment sub_vars} (h_subset : c₁ ⊆ c₂) (h : (c₁.substitute ρ).isNone) :
    (c₂.substitute ρ).isNone := by
  contrapose! h
  simp_all only [ne_eq, Option.isNone_iff_eq_none, ←Option.isSome_iff_ne_none]
  exact substitute_isSome_subset h_subset h

lemma Clause.resolve_substitute_isNone {vars sub_vars} {c₁ c₂ : Clause vars} {x : Variable}
    (h_x : x ∈ vars) {ρ : Assignment sub_vars} (h_c₁ : (c₁.substitute ρ).isNone)
    (h_c₂ : (c₂.substitute ρ).isNone) :
    ((Clause.resolve c₁ c₂ x h_x).substitute ρ).isNone := by
  simp_all only [Option.isNone_iff_eq_none]
  rw [Clause.substitute_eq_none_iff_eval_subclause_true] at *
  rw [Clause.eval_eq_true_iff_exists_satisfied_literal] at *
  obtain ⟨l₁, ⟨h_l₁_in_c₁, h_l₁_eval⟩⟩ := h_c₁
  obtain ⟨l₂, ⟨h_l₂_in_c₂, h_l₂_eval⟩⟩ := h_c₂

  if h : l₁.variable = x ∧ l₂.variable = x then
    have h_eq : l₁ = l₂ := by
      suffices h_pos : l₁.polarity = l₂.polarity by
        have : l₁.variable = l₂.variable := by aesop
        aesop
      aesop (add safe unfold Literal.eval)

    have : l₂ ∈ ((c₁.resolve c₂ x h_x).split sub_vars).1 := by
      simp_all only [Clause.resolve, Clause.split, Clause.shrink, Finset.mem_filterMap]
      simp_all only [Finset.mem_filter, Option.dite_none_right_eq_some, Option.some.injEq,
        and_exists_self, and_self, Finset.mem_union, Finset.mem_erase, ne_eq]

      obtain ⟨l₁', ⟨h_l₁'_mem, h₁⟩⟩ := h_l₁_in_c₁
      obtain ⟨l₂', ⟨h_l₂'_mem, h₂⟩⟩ := h_l₂_in_c₂

      subst h

      if h_pos : l₁.polarity then
        use l₂'
        simp_all only [and_true, exists_prop]
        subst h₂
        right
        suffices l₂'.polarity by
          grind [Variable.toLiteral]
        aesop
      else
        use l₁'
        simp_all only [and_true, exists_prop]
        subst h₁
        left
        suffices ¬l₁'.polarity by
          grind [Variable.toLiteral]
        aesop
    use l₂
  else if h_var₁ : l₁.variable ≠ x then
    have : l₁ ∈ ((c₁.resolve c₂ x h_x).split sub_vars).1 := by
      simp_all only [Clause.split, Clause.shrink, Finset.mem_filterMap]
      obtain ⟨l₁', ⟨h_l₁'_mem, h₁⟩⟩ := h_l₁_in_c₁
      use l₁'
      simp_all only [Finset.mem_filter, Option.dite_none_right_eq_some, Option.some.injEq,
        and_exists_self, false_and, not_false_eq_true, ne_eq, and_self, ↓reduceDIte, and_true,
        dite_eq_ite, ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not]
      unfold Clause.resolve
      simp only [Finset.mem_union, Finset.mem_erase, ne_eq]
      left
      have : l₁.variable = l₁'.variable := by aesop
      grind [Variable.toLiteral]
    use l₁
  else
    have h_var₂ : l₂.variable ≠ x := by aesop
    have : l₂ ∈ ((c₁.resolve c₂ x h_x).split sub_vars).1 := by
      unfold Clause.split Clause.shrink at *
      simp_all only
      rw [Finset.mem_filterMap] at h_l₂_in_c₂
      obtain ⟨l₂', ⟨h_l₂'_mem, h₂⟩⟩ := h_l₂_in_c₂
      rw [Finset.mem_filterMap]
      use l₂'
      simp_all only [Finset.mem_filter, Finset.mem_filterMap, Option.dite_none_right_eq_some,
        Option.some.injEq, and_exists_self, and_false, not_false_eq_true, ne_eq, Decidable.not_not,
        and_self, ↓reduceDIte, and_true, dite_eq_ite, ite_eq_left_iff, reduceCtorEq, imp_false]
      unfold Clause.resolve
      simp only [Finset.mem_union, Finset.mem_erase, ne_eq]
      right
      have : l₂.variable = l₂'.variable := by aesop
      grind [Variable.toLiteral]
    use l₂

@[simp]
lemma Clause.substitute_variables {vars sub_vars} {c : Clause vars} (ρ : Assignment sub_vars)
    (h_c : (c.substitute ρ).isSome) :
    ((c.substitute ρ).get h_c).variables = c.variables \ sub_vars := by
  unfold Clause.substitute Clause.split Clause.shrink Clause.variables
  simp only [Finset.mem_filter, Option.get_ite']
  ext v
  constructor
  · intro h
    simp_all only [Finset.mem_image, Finset.mem_filterMap, Finset.mem_filter,
      Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self, ↓existsAndEq, true_and,
      Finset.mem_sdiff]
    obtain ⟨l, ⟨h_l_in_c, h_l_vars⟩⟩ := h
    constructor
    swap
    · unfold Literal.restrict Literal.variable at *
      aesop
    use l
    unfold Literal.restrict Literal.variable at *
    aesop
  · intro h
    simp_all only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filterMap, Finset.mem_filter,
      Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self, ↓existsAndEq, true_and]
    have h_right := h.right
    obtain ⟨l, h_l_in_c, h_l_vars⟩ := h.left
    use l
    unfold Literal.restrict Literal.variable at *
    aesop

/-- Cardinaly of the image of filterMap cannot be larger than preimage.
This statement does not follow from the lemmas in the standard library, so we prove it here. -/
@[aesop safe, grind .]
lemma filterMap_card {α β} [DecidableEq α] [DecidableEq β] (s : Finset α) {f : α → Option β} {h} :
    Finset.card (s.filterMap f h) ≤ Finset.card s := by
  induction s using Finset.induction_on
  case empty => rfl
  case insert a s' h_a ih =>
    rw [Finset.card_insert_of_notMem h_a]
    grw [← ih]
    trans ((Finset.filterMap f s' h) ∪ if h : (f a).isSome then {(f a).get h} else ∅).card
    · exact (Finset.eq_iff_card_ge_of_superset (by grind)).mpr (by grind)
    grind

@[aesop safe]
lemma Clause.substitute_card_leq_card {vars sub_vars} (c : Clause vars) (ρ : Assignment sub_vars)
    {h} : ((c.substitute ρ).get h).card ≤ c.card := by
  unfold Clause.substitute Clause.split Clause.shrink
  simp only [Finset.mem_filter, Option.get_ite']
  trans {l ∈ c | l.variable ∉ sub_vars}.card
  · apply filterMap_card
  · apply Finset.card_filter_le

lemma Clause.substitute_resolve_eq_resolve_substitute {vars sub_vars} {c₁ c₂ : Clause vars}
    (ρ : Assignment sub_vars) (v : Variable) (h_v : v ∈ vars \ sub_vars) (h₁) (h₂)
    (h_res : ((c₁.resolve c₂ v (by
     rw [Finset.mem_sdiff] at h_v
     exact h_v.left)).substitute ρ).isSome) :
    ((c₁.substitute ρ).get h₁).resolve ((c₂.substitute ρ).get h₂) v h_v =
      ((c₁.resolve c₂ v (by
        rw [Finset.mem_sdiff] at h_v
        exact h_v.left
      )).substitute ρ).get h_res := by
  unfold Clause.resolve Clause.substitute Clause.split Clause.shrink
  simp_all only [Finset.mem_filter, Option.get_ite', Finset.mem_union, Finset.mem_erase, ne_eq]
  ext l
  constructor
  · intro h_l
    simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_filterMap,
      Finset.mem_filter, Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self]
    cases h_l
    case h.mp.inl h =>
      obtain ⟨h_neq, ⟨l', ⟨⟨h_l'_in, h_l'_var⟩, h_restrict⟩⟩⟩ := h
      use l'
      use by
        constructor
        swap
        · assumption
        left
        grind
    case h.mp.inr h =>
      obtain ⟨h_neq, ⟨l', ⟨⟨h_l'_in, h_l'_var⟩, h_restrict⟩⟩⟩ := h
      use l'
      use by
        constructor
        swap
        · assumption
        right
        grind
  · intro h_l
    simp_all only [Finset.mem_filterMap, Finset.mem_filter, Finset.mem_union, Finset.mem_erase,
      ne_eq, Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self]
    obtain ⟨l', ⟨⟨h_l', h_l'_var⟩, h_restrict⟩⟩ := h_l
    cases h_l'
    case h.mpr.inl h =>
      left
      obtain ⟨h_l'_neq, h_l'_in⟩ := h
      constructor
      · by_contra!
        rw [Literal.ext_iff] at h_l'_neq
        simp_all only [Variable.toLiteral]
        have : l.polarity := by grind
        have : l.variable = v := by grind
        have : (l'.variable = v ∧ l'.polarity) := by grind
        contradiction

      use l'
      use by aesop
    case h.mpr.inr h =>
      right
      obtain ⟨h_l'_neq, h_l'_in⟩ := h
      constructor
      · by_contra!
        rw [Literal.ext_iff] at h_l'_neq
        simp_all only [Variable.toLiteral]
        have : ¬l.polarity := by grind
        have : l.variable = v := by grind
        have : (l'.variable = v ∧ ¬l'.polarity) := by grind
        grind
      use l'
      use by aesop

#lint
