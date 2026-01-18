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

@[simp]
lemma literal_in_clause_variables {vars} (l : Literal vars) (c : Clause vars)
: l ∈ c → l.variable ∈ c.variables := by
  intro h_l_in_c
  unfold Clause.variables
  exact Finset.mem_image_of_mem Literal.variable h_l_in_c

@[simp]
lemma variable_in_clause_variables_implies_literal_in_clause {vars} (v : Variable) (c : Clause vars)
    (h_v_mem_vars : v ∈ vars) (h_v_mem_c : (v.toLiteral h_v_mem_vars ∈ c) ∨
                                           (v.toNegLiteral h_v_mem_vars ∈ c))
    : v ∈ c.variables := by
  unfold Clause.variables
  cases h_v_mem_c
  case inl h_lit_pos_in_c =>
    exact Finset.mem_image_of_mem Literal.variable h_lit_pos_in_c
  case inr h_lit_neg_in_c =>
    exact Finset.mem_image_of_mem Literal.variable h_lit_neg_in_c

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
lemma Literal.eval_negate_eq_not_eval {vars} (l : Literal vars) (a : Assignment vars)
: l.negate.eval a = ¬ l.eval a := by
  unfold Literal.eval
  unfold Literal.negate
  simp only [Bool.not_eq_true, eq_iff_iff, Bool.coe_true_iff_false]
  cases l
  case pos v h_v_mem_vars =>
    rfl
  case neg v h_v_mem_vars =>
    simp only [Bool.not_not]

@[simp]
lemma Literal.neg_polarity {vars} (l : Literal vars)
: l.negate.polarity = ¬l.polarity := by
  unfold polarity
  unfold negate

  aesop

@[simp]
lemma Literal.neg_neg {vars} (l : Literal vars)
: l.negate.negate = l := by
  unfold negate

  aesop

def Clause.eval {vars} (c : Clause vars) (a : Assignment vars) : Bool :=
  c.fold (Bool.or) false (fun l => l.eval a)

def CNFFormula.eval {vars} (φ : CNFFormula vars) (a : Assignment vars) : Bool :=
  φ.fold (Bool.and) true (fun c => c.eval a)


lemma CNFFormula.eval_eq_false_iff_exists_falsified_clause {vars} (φ : CNFFormula vars)
    (a : Assignment vars)
: φ.eval a = false ↔ (∃ c, c ∈ φ ∧ c.eval a = false) := by
  constructor
  case mpr =>
    intro h_exists_falsified_clause
    unfold CNFFormula.eval
    obtain ⟨c, h_c_in_φ, h_c_eval_a_false⟩ := h_exists_falsified_clause
    let φ' := φ.erase c
    have h_c_not_in_φ' : c ∉ φ' := by
      rw [Finset.mem_erase]
      simp only [ne_eq, not_true_eq_false, false_and, not_false_eq_true]
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
    simp only [ne_eq, Bool.not_eq_false] at h_φ_eval_a_false
    rename ∀ c ∈ φ, c.eval a = true => h_all_sat
    unfold CNFFormula.eval
    induction φ using Finset.induction_on with
    | empty =>
      trivial
    | insert c φ' h_c_not_in_φ' ih =>
      rw [Finset.fold_insert h_c_not_in_φ']
      rw [ih]

      · simp only [Bool.and_true]
        apply h_all_sat
        exact Finset.mem_insert_self c φ'
      · intro c' h_c'_in_φ'
        apply h_all_sat
        exact Finset.mem_insert_of_mem h_c'_in_φ'

lemma Clause.eval_eq_true_iff_exists_satisfied_literal {vars} (c : Clause vars)
    (a : Assignment vars)
: c.eval a = true ↔ (∃ l, l ∈ c ∧ l.eval a = true) := by
  constructor
  case mpr =>
    intro h_exists_falsified_c
    unfold Clause.eval
    obtain ⟨l, h_l_in_c, h_l_eval_a_false⟩ := h_exists_falsified_c
    let c' := c.erase l
    have h_l_not_in_c' : l ∉ c' := by
      rw [Finset.mem_erase]
      simp only [ne_eq, not_true_eq_false, false_and, not_false_eq_true]
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
    rename ∀ l ∈ c, l.eval a = false => h_all_unsat
    unfold Clause.eval
    induction c using Finset.induction_on with
    | empty =>
      trivial
    | insert l c' h_l_not_in_c' ih =>
      rw [Finset.fold_insert h_l_not_in_c']
      rw [ih]

      · simp only [Bool.or_false]
        apply h_all_unsat
        exact Finset.mem_insert_self l c'
      · intro l' h_l'_in_c'
        apply h_all_unsat
        exact Finset.mem_insert_of_mem h_l'_in_c'

lemma neg_iff (A : Prop) (B : Prop) : (A ↔ B) ↔ (¬A ↔ ¬B) := by tauto

lemma CNFFormula.eval_eq_true_iff_all_satisfied_clauses {vars} (φ : CNFFormula vars)
    (a : Assignment vars)
: φ.eval a = true ↔ (∀ c, c ∈ φ → c.eval a = true) := by
  rw [neg_iff]
  push_neg
  simp only [ne_eq, Bool.not_eq_true]
  exact eval_eq_false_iff_exists_falsified_clause φ a

lemma Clause.eval_eq_false_iff_all_falsified_literals {vars} (c : Clause vars)
    (a : Assignment vars)
: c.eval a = false ↔ (∀ l, l ∈ c → l.eval a = false) := by
  rw [neg_iff]
  push_neg
  simp only [ne_eq, Bool.not_eq_false]
  exact eval_eq_true_iff_exists_satisfied_literal c a

def Clause.resolve {vars} (c₁ : Clause vars) (c₂ : Clause vars) (x : Variable) (h_x : x ∈ vars)
: Clause vars :=
  c₁.erase (x.toLiteral h_x) ∪ c₂.erase (x.toNegLiteral h_x)
