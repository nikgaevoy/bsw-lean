import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

abbrev Variable := String
abbrev Variables := Finset String
abbrev Assignment (vars : Variables) := (v : Variable) → v ∈ vars → Bool

inductive Literal (vars : Variables)
  | pos (v : Variable) (h_v_mem_vars : v ∈ vars) : Literal vars
  | neg (v : Variable) (h_v_mem_vars : v ∈ vars) : Literal vars

deriving instance DecidableEq
for Literal

deriving instance DecidableEq
for Variable

def Variable.toLiteral {vars} (v : Variable) (h_v_mem_vars : v ∈ vars) : Literal vars :=
  Literal.pos v h_v_mem_vars

def Variable.toNegLiteral {vars} (v : Variable) (h_v_mem_vars : v ∈ vars) : Literal vars :=
  Literal.neg v h_v_mem_vars

def Literal.variable {vars} (l : Literal vars) : Variable :=
  match l with
  | .pos v _ => v
  | .neg v _ => v

def Literal.polarity {vars} (l : Literal vars) : Bool :=
  match l with
  | .pos _ _ => True
  | .neg _ _ => False

lemma Literal.eq_iff_polarity_and_variable_eq {vars} {l₁ l₂ : Literal vars} :
    l₁ = l₂ ↔ (l₁.polarity = l₂.polarity ∧ l₁.variable = l₂.variable) := by
  constructor

  case mp =>
    intro h
    rw [h]
    simp

  case mpr =>
    intro h
    unfold Literal.polarity Literal.variable at h
    aesop

@[simp]
lemma Literal.variable_mem_vars {vars} (l : Literal vars) : l.variable ∈ vars := by
  cases l
  case pos v h_v_mem_vars =>
    exact h_v_mem_vars
  case neg v h_v_mem_vars =>
    exact h_v_mem_vars

abbrev Clause (vars : Variables) := Finset (Literal vars)

def Clause.variables {vars} (c : Clause vars) : Finset Variable :=
  c.image Literal.variable

@[aesop unsafe]
lemma literal_in_clause_variables {vars} {l : Literal vars} {c : Clause vars} (h_l_in_c : l ∈ c) :
    l.variable ∈ c.variables := by
  unfold Clause.variables
  exact Finset.mem_image_of_mem Literal.variable h_l_in_c

@[aesop safe]
lemma clause_variables_subset_vars {vars} (c : Clause vars) : c.variables ⊆ vars := by
  unfold Clause.variables
  unfold Literal.variable
  grind

@[aesop unsafe]
lemma clause_variables_maintains_subset {vars} {c₁ c₂ : Clause vars} (h_sub : c₁ ⊆ c₂) :
    c₁.variables ⊆ c₂.variables := by
  unfold Clause.variables
  grind

@[aesop unsafe]
lemma clause_variable_mem_variables_maintains_subset {vars} {c₁ c₂ : Clause vars} (h_sub : c₁ ⊆ c₂)
    {v : Variable} (h_v_mem : v ∈ c₁.variables) : v ∈ c₂.variables := by
  have := clause_variables_maintains_subset h_sub
  aesop

abbrev CNFFormula (vars : Variables) := Finset (Clause vars)

def Literal.eval {vars} (l : Literal vars) (a : Assignment vars) : Bool :=
  match l with
  | .pos v h_v_mem_vars => a v h_v_mem_vars
  | .neg v h_v_mem_vars => !(a v h_v_mem_vars)

def Literal.negate {vars} (l : Literal vars) : (Literal vars) :=
  match l with
  | .pos v h_v_mem_vars => Literal.neg v h_v_mem_vars
  | .neg v h_v_mem_vars => Literal.pos v h_v_mem_vars

@[simp]
lemma Literal.eval_negate_eq_not_eval {vars} (l : Literal vars) (a : Assignment vars) :
    l.negate.eval a = ¬ l.eval a := by
  unfold Literal.eval Literal.negate
  simp only [Bool.not_eq_true, eq_iff_iff, Bool.coe_true_iff_false]
  cases l
  case pos v h_v_mem_vars =>
    rfl
  case neg v h_v_mem_vars =>
    simp

@[simp]
lemma Literal.neg_polarity {vars} (l : Literal vars) : l.negate.polarity = ¬l.polarity := by
  unfold polarity negate

  aesop

@[simp]
lemma Literal.neg_neg {vars} (l : Literal vars) : l.negate.negate = l := by
  unfold negate

  aesop

def Clause.eval {vars} (c : Clause vars) (a : Assignment vars) : Bool :=
  c.fold (Bool.or) false (fun l => l.eval a)

def CNFFormula.eval {vars} (φ : CNFFormula vars) (a : Assignment vars) : Bool :=
  φ.fold (Bool.and) true (fun c => c.eval a)


lemma CNFFormula.eval_eq_false_iff_exists_falsified_clause {vars} (φ : CNFFormula vars)
    (a : Assignment vars) : φ.eval a = false ↔ (∃ c, c ∈ φ ∧ c.eval a = false) := by
  constructor

  case mpr =>
    intro h_exists_falsified_clause
    unfold CNFFormula.eval
    obtain ⟨c, h_c_in_φ, h_c_eval_a_false⟩ := h_exists_falsified_clause
    let φ' := φ.erase c

    have h_c_not_in_φ' : c ∉ φ' := by
      rw [Finset.mem_erase]
      simp

    have : φ = insert c φ' := by
      rw [Finset.insert_erase h_c_in_φ]

    rw [this]
    rw [Finset.fold_insert h_c_not_in_φ']
    rw [h_c_eval_a_false]
    rfl

  case mp =>
    intro h_φ_eval_a_false
    contrapose! h_φ_eval_a_false
    simp only [ne_eq, Bool.not_eq_false]
    unfold CNFFormula.eval
    induction φ using Finset.induction_on with
    | empty =>
      trivial
    | insert c φ' h_c_not_in_φ' ih =>
      aesop

lemma Clause.eval_eq_true_iff_exists_satisfied_literal {vars} (c : Clause vars)
    (a : Assignment vars) : c.eval a = true ↔ (∃ l, l ∈ c ∧ l.eval a = true) := by
  constructor

  case mpr =>
    intro h_exists_falsified_c
    unfold Clause.eval
    obtain ⟨l, h_l_in_c, h_l_eval_a_false⟩ := h_exists_falsified_c
    let c' := c.erase l

    have h_l_not_in_c' : l ∉ c' := by
      rw [Finset.mem_erase]
      simp

    have : c = insert l c' := by
      rw [Finset.insert_erase h_l_in_c]

    rw [this]
    rw [Finset.fold_insert h_l_not_in_c']
    rw [h_l_eval_a_false]
    rfl

  case mp =>
    intro h_c_eval_a_false
    contrapose! h_c_eval_a_false
    simp only [ne_eq, Bool.not_eq_true]
    simp only [ne_eq, Bool.not_eq_true] at h_c_eval_a_false
    unfold Clause.eval
    induction c using Finset.induction_on with
    | empty =>
      trivial
    | insert l c' h_l_not_in_c' ih =>
      aesop

lemma neg_iff (A : Prop) (B : Prop) : (¬A ↔ ¬B) ↔ (A ↔ B) := by tauto

lemma CNFFormula.eval_eq_true_iff_all_satisfied_clauses {vars} (φ : CNFFormula vars)
    (a : Assignment vars) : φ.eval a = true ↔ (∀ c, c ∈ φ → c.eval a = true) := by
  rw [←neg_iff]
  push_neg
  simp only [ne_eq, Bool.not_eq_true]
  exact eval_eq_false_iff_exists_falsified_clause φ a

lemma Clause.eval_eq_false_iff_all_falsified_literals {vars} (c : Clause vars)
    (a : Assignment vars) : c.eval a = false ↔ (∀ l, l ∈ c → l.eval a = false) := by
  rw [←neg_iff]
  push_neg
  simp only [ne_eq, Bool.not_eq_false]
  exact eval_eq_true_iff_exists_satisfied_literal c a

def Clause.resolve {vars} (c₁ c₂ : Clause vars) (x : Variable) (h_x : x ∈ vars) :
    Clause vars :=
  c₁.erase (x.toLiteral h_x) ∪ c₂.erase (x.toNegLiteral h_x)

@[aesop unsafe]
lemma Clause.not_in_variables_subset {vars} {c₁ c₂ : Clause vars} {x : Variable}
    (h_subset : c₁ ⊆ c₂) (h : x ∉ c₂.variables) : x ∉ c₁.variables := by
  unfold Clause.variables
  unfold Clause.variables at h
  aesop

@[simp]
lemma Clause.union_variables {vars} (c₁ c₂ : Clause vars) :
    (c₁ ∪ c₂).variables = c₁.variables ∪ c₂.variables := by
  unfold Clause.variables
  aesop

@[aesop unsafe]
lemma Clause.subset_variables {vars} {c₁ c₂ : Clause vars} (h : c₁ ⊆ c₂) :
    c₁.variables ⊆ c₂.variables := by
  unfold Clause.variables
  rw [@Finset.image_subset_iff]
  intro l h_l
  have : l ∈ c₂ := by aesop
  aesop

@[aesop unsafe]
lemma Clause.resolve_maintains_subset {vars} {c₁ c₁' c₂ c₂' : Clause vars} {x : Variable}
    (h_x : x ∈ vars) (h_subset₁ : c₁ ⊆ c₁') (h_subset₂ : c₂ ⊆ c₂') :
    Clause.resolve c₁ c₂ x h_x ⊆ Clause.resolve c₁' c₂' x h_x := by
  unfold Clause.resolve
  intro l h_l_in_resolve
  aesop

@[aesop safe]
lemma Clause.resolve_satisfies_h_resolve_left {vars} {c₁ c₂ : Clause vars} {v : Variable}
    (h_v_mem_vars : v ∈ vars) :
    (c₁ ⊆ c₁.resolve c₂ v h_v_mem_vars ∪ { v.toLiteral h_v_mem_vars }) := by
  unfold Clause.resolve
  intro l h
  simp only [Finset.union_singleton, Finset.mem_insert, Finset.mem_union, Finset.mem_erase, ne_eq]
  tauto

@[aesop safe]
lemma Clause.resolve_satisfies_h_resolve_right {vars} {c₁ c₂ : Clause vars} {v : Variable}
    (h_v_mem_vars : v ∈ vars) :
    (c₂ ⊆ c₁.resolve c₂ v h_v_mem_vars ∪ { v.toNegLiteral h_v_mem_vars }) := by
  unfold Clause.resolve
  intro l h
  simp only [Finset.union_singleton, Finset.mem_insert, Finset.mem_union, Finset.mem_erase, ne_eq]
  tauto
