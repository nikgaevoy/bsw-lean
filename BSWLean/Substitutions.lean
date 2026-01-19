import BSWLean.CNF

def Literal.restrict {vars} (l : Literal vars)
    (sub_vars : Variables) (h_mem : l.variable ∈ sub_vars)
    : Literal sub_vars :=
  match l with
  | .pos v _ => Literal.pos v h_mem
  | .neg v _ => Literal.neg v h_mem

lemma Literal.restrict_inj {vars} (l₁ : Literal vars) (l₂ : Literal vars)
  (sub_vars : Variables) (h_l₁_mem : l₁.variable ∈ sub_vars) (h_l₂_mem : l₂.variable ∈ sub_vars)
  : l₁.restrict sub_vars h_l₁_mem = l₂.restrict sub_vars h_l₂_mem → l₁ = l₂ := by
  intros h_eq
  unfold Literal.restrict at h_eq
  cases l₁ <;> cases l₂ <;> simp_all

def Clause.shrink {vars} (c : Clause vars)
    (keep_vars : Variables) (h_mem : ∀ l, l ∈ c → l.variable ∈ keep_vars)
    : Clause keep_vars :=
  let f := fun l : Literal vars =>
      if h : l ∈ c then some (l.restrict keep_vars (h_mem l h)) else none

  have : ∀ l₁ l₂, ∀ r ∈ f l₁, r ∈ f l₂ → l₁ = l₂ := by
    intros l₁ l₂ b h₁ h₂
    unfold f at h₁ h₂
    simp_all only [Option.mem_def, Option.dite_none_right_eq_some, Option.some.injEq]
    obtain ⟨_, h⟩ := h₁
    obtain ⟨h_l₂_c, h_l₂_b⟩ := h₂
    rw [←h_l₂_b] at h
    have h_l₁_vars : l₁.variable ∈ keep_vars := by (expose_names; exact h_mem l₁ w)
    have h_l₂_vars : l₂.variable ∈ keep_vars := by (expose_names; exact h_mem l₂ h_l₂_c)
    unfold Literal.restrict at h
    expose_names;
    exact
      Literal.restrict_inj l₁ l₂ keep_vars
        (h_mem l₁ ((Iff.of_eq (Eq.refl (l₁ ∈ c))).mpr w))
        (h_mem l₂ ((Iff.of_eq (Eq.refl (l₂ ∈ c))).mpr h_l₂_c)) h

  c.filterMap f this

def Clause.split {vars} (c : Clause vars)
    (split_vars : Variables)
    : (Clause (vars ∩ split_vars)) × (Clause (vars \ split_vars)) :=
  let c_in := c.filter (fun l => l.variable ∈ split_vars)
  let c_out := c.filter (fun l => l.variable ∉ split_vars)

  have h_in : ∀ l, l ∈ c_in → l.variable ∈ (vars ∩ split_vars) := by
    intro l h_c_in
    unfold c_in at h_c_in
    simp only [Finset.mem_filter] at h_c_in
    rw [@Finset.mem_inter]
    constructor
    · simp only [Literal.variable_mem_vars]
    · apply h_c_in.2

  have h_out : ∀ l, l ∈ c_out → l.variable ∈ (vars \ split_vars) := by
    intro l h_c_out
    unfold c_out at h_c_out
    simp only [Finset.mem_filter] at h_c_out
    simp only [Finset.mem_sdiff]
    constructor
    · simp only [Literal.variable_mem_vars]
    · apply h_c_out.2


  let c_in' := Clause.shrink c_in (vars ∩ split_vars) h_in
  let c_out' := Clause.shrink c_out (vars \ split_vars) h_out

  (c_in', c_out')

def Assignment.restrict {vars} (ρ : Assignment vars)
    (sub_vars : Variables) (h_subset : sub_vars ⊆ vars) : Assignment sub_vars :=
  have : ∀ v ∈ sub_vars, v ∈ vars := by
    exact fun v a ↦ h_subset a

  fun v h_v_mem_sub_vars => ρ v (this v h_v_mem_sub_vars)

@[simp]
lemma Assignment.double_restrict {vars} (ρ : Assignment vars)
    (sub_vars₁ : Variables) (h_subset₁ : sub_vars₁ ⊆ vars)
    (sub_vars₂ : Variables) (h_subset₂ : sub_vars₂ ⊆ sub_vars₁)
  : (ρ.restrict sub_vars₁ h_subset₁).restrict sub_vars₂ h_subset₂ =
    ρ.restrict sub_vars₂ (by exact fun ⦃a⦄ a_1 ↦ h_subset₁ (h_subset₂ a_1)) := by
  rfl

lemma Literal.restrict_correctness {vars} (l : Literal vars) (sub_vars : Variables)
  (ρ : Assignment vars) (h_subset : sub_vars ⊆ vars) (h_l : l.variable ∈ sub_vars)
  : l.eval ρ = (l.restrict sub_vars h_l).eval (ρ.restrict sub_vars h_subset) := by
  unfold Literal.restrict
  unfold Literal.eval
  unfold Assignment.restrict
  cases l
  case pos v h_v_mem_vars =>
    simp only
  case neg v h_v_mem_vars =>
    simp only


def Clause.substitute {vars} (c : Clause vars)
    {sub_vars : Variables} (ρ : Assignment sub_vars)
    : Option (Clause (vars \ sub_vars)) :=
  let (c_in, c_out) := Clause.split c sub_vars

  if c_in.eval (ρ.restrict (vars ∩ sub_vars) Finset.inter_subset_right) then
    none
  else
    some c_out

lemma Clause.substitute_eq_none_iff_eval_subclause_true {vars} (c : Clause vars)
    (sub_vars : Variables) (ρ : Assignment sub_vars)
: c.substitute ρ = none ↔
  (c.split sub_vars).1.eval (ρ.restrict (vars ∩ sub_vars) Finset.inter_subset_right) := by
  unfold Clause.substitute
  constructor
  case mp =>
    simp_all only [ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false,
      implies_true]
  case mpr =>
    simp_all only [↓reduceIte, implies_true]

lemma Clause.substitute_isSome_iff_eval_subclause_false {vars} (c : Clause vars)
    (sub_vars : Variables) (ρ : Assignment sub_vars)
: (c.substitute ρ).isSome ↔
  ¬(c.split sub_vars).1.eval (ρ.restrict (vars ∩ sub_vars) Finset.inter_subset_right) := by
  rw [← @substitute_eq_none_iff_eval_subclause_true]
  exact Option.isSome_iff_ne_none

@[simp]
lemma Assignment.restrict_correctness {vars} {h} (ρ : Assignment vars)
    : ρ.restrict vars h = ρ := by
  rfl

lemma Clause.split_correctness {vars} (c : Clause vars)
    (sub_vars : Variables) (ρ : Assignment vars) (h₁) (h₂) :
    c.eval ρ = ((c.split sub_vars).1.eval (ρ.restrict (vars ∩ sub_vars) h₁)
            || (c.split sub_vars).2.eval (ρ.restrict (vars \ sub_vars) h₂)) := by
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
      let l' := l.restrict (vars ∩ sub_vars) (by
        simp only [Finset.mem_inter, Literal.variable_mem_vars, true_and]
        exact h_l_in_c_in
      )
      have h_unfold : l' = l.restrict (vars ∩ sub_vars) (by
        simp only [Finset.mem_inter, Literal.variable_mem_vars, true_and]
        exact h_l_in_c_in
      ) := by
        rfl
      have h_l'_in_c_in : l' ∈ (c.split sub_vars).1 := by
        unfold Clause.split
        simp only
        unfold Clause.shrink
        simp only [Finset.mem_filter, Finset.mem_filterMap, Option.dite_none_right_eq_some,
          Option.some.injEq, and_exists_self]
        use l
        have : l ∈ c ∧ l.variable ∈ sub_vars := by
          constructor
          · assumption
          · assumption
        use this
      have h_l'_eval : l'.eval (ρ.restrict (vars ∩ sub_vars) h₁) := by
        rw [h_unfold]
        rw [←Literal.restrict_correctness l (vars ∩ sub_vars) ρ]
        assumption

      use l'
    case neg =>
      right
      rw [Clause.eval_eq_true_iff_exists_satisfied_literal]
      let l' := l.restrict (vars \ sub_vars) (by
        simp only [Finset.mem_sdiff, Literal.variable_mem_vars, true_and]
        exact h_l_in_c_in
      )
      have h_unfold : l' = l.restrict (vars \ sub_vars) (by
        simp only [Finset.mem_sdiff, Literal.variable_mem_vars, true_and]
        exact h_l_in_c_in
      ) := by
        rfl
      have h_l'_in_c_in : l' ∈ (c.split sub_vars).2 := by
        unfold Clause.split
        simp only
        unfold Clause.shrink
        simp only [Finset.mem_filter, Finset.mem_filterMap, Option.dite_none_right_eq_some,
          Option.some.injEq, and_exists_self]
        use l
        have : l ∈ c ∧ l.variable ∉ sub_vars := by
          constructor
          · assumption
          · assumption
        use this
      have h_l'_eval : l'.eval (ρ.restrict (vars \ sub_vars) h₂) := by
        rw [h_unfold]
        rw [←Literal.restrict_correctness l (vars \ sub_vars) ρ]
        assumption

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
      specialize h_c l₂ h_l₂_in_c.1
      rw [←h_l₂_vars]
      rw [←Literal.restrict_correctness l₂ (vars ∩ sub_vars) ρ]
      trivial
    · rw [@eval_eq_false_iff_all_falsified_literals]
      intro l₁ h_l₁_in_c_in
      rw [Clause.split] at h_l₁_in_c_in
      unfold Clause.shrink at h_l₁_in_c_in
      simp only [Finset.mem_filter, Finset.mem_filterMap, Option.dite_none_right_eq_some,
        Option.some.injEq, and_exists_self] at h_l₁_in_c_in
      obtain ⟨l₂, h_l₂_in_c, h_l₂_vars⟩ := h_l₁_in_c_in
      rw [Clause.eval_eq_false_iff_all_falsified_literals] at h_c
      specialize h_c l₂ h_l₂_in_c.1
      rw [←h_l₂_vars]
      rw [←Literal.restrict_correctness l₂ (vars \ sub_vars) ρ]
      trivial


def CNFFormula.substitute {vars} (φ : CNFFormula vars)
    {sub_vars : Variables} (ρ : Assignment sub_vars)
    : CNFFormula (vars \ sub_vars) :=
  let f := fun c : Clause vars => c.substitute ρ

  let φ' := (φ.image f).filterMap id

  φ' (by exact fun a a' b a_1 a_2 ↦ Option.eq_of_mem_of_mem a_1 a_2)

lemma CNFFormula.substitute_preimage {vars} (φ : CNFFormula vars)
    {sub_vars : Variables} (ρ : Assignment sub_vars)
    : ∀ c ∈ φ.substitute ρ, ∃ c' ∈ φ, c'.substitute ρ = some c := by
    intro c h_c
    unfold CNFFormula.substitute at h_c
    simp_all only [Finset.mem_filterMap, Finset.mem_image, id_eq, exists_eq_right]
