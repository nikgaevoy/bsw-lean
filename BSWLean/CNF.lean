import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

/-!
# CNF-formulas

This file defines all basic structures to work with: Variables, Literals, Clauses,
CNF-Formulas, and Assignments.

## Implementation notes

Variables are defined as Strings. This is done solely for the sake of simplicity, to avoid writing
another polymorphic argument in all lemmas and theorems. Any other type would also work just fine,
as long as it satisfies `DecideableEQ`.

Literals, Clauses and CNF-Formulas are defined on a specific set of variables.
This design choice ultimately emerges from the necessity of defining completeness theorems for
proof systems, but leads to some problems in other places. For the structures of different form,
see SuperLiterals, SuperClauses, etc.
-/

/-- Definition of a variable. Strings could be replaced with any type. -/
structure Variable where
  /-- Not actually used in the code. -/
  name : String
deriving DecidableEq

/-- Set of variables. Self explanatory. -/
abbrev Variables := Finset Variable

/-- Assignment. PArtial assignments are assignments on a subset of variables. It leads to a
slightly different behavior of this set of variables than in the case of basically everything
else, but it cannot be avoided. -/
abbrev Assignment (vars : Variables) := (v : Variable) → v ∈ vars → Bool

/-- Literals are defined on a specific set of variables, and a literal stores the proof that
it's variable belongs to the set of variables. -/
@[aesop safe [constructors]]
structure Literal (vars : Variables) where
  /-- variable -/
  v : { v : Variable // v ∈ vars }
  /-- polarity: `True` if positive, `False` otherwise -/
  polarity : Bool
deriving DecidableEq

/-- Constructor for a literal with the given polarity. -/
def Variable.toLiteral {vars} (v : Variable) (h_v_mem_vars : v ∈ vars) (p : Bool) : Literal vars :=
  Literal.mk ⟨v, h_v_mem_vars⟩ p

/-- Constructor for a literal with the given polarity. -/
@[simp]
def Subtype.toLiteral {vars} (v : { v : Variable // v ∈ vars }) (p : Bool) : Literal vars :=
  (↑v : Variable).toLiteral (by aesop) p

/-- Projection on a variable. -/
def Literal.variable {vars} (l : Literal vars) : Variable := l.v

@[aesop safe, grind .]
lemma Literal.variable_mem_vars {vars} (l : Literal vars) : l.variable ∈ vars := by
  aesop (add safe unfold Literal.variable)

@[aesop safe, grind =]
lemma Literal.variable_eq {vars} (l : Literal vars) : l.variable = l.v := by rfl

@[simp]
lemma Literal.variable_mk {vars} (v : {v : Variable // v ∈ vars}) (p : Bool) :
    (Literal.mk v p).variable = v := by rfl

@[ext, aesop safe]
lemma Literal.ext {vars} {l₁ l₂ : Literal vars}
    (h₁ : l₁.variable = l₂.variable)
    (h₂ : l₁.polarity = l₂.polarity) :
    l₁ = l₂ := by
  cases l₁; cases l₂
  aesop

@[simp]
lemma Literal.mk_eta {vars} (l : Literal vars) :
    Literal.mk l.v l.polarity = l := by rfl

@[simp]
lemma Literal.reduce_self {vars} {l : Literal vars} (h : l.polarity) :
    (Literal.mk ⟨l.variable, by aesop⟩ true) = l := by aesop

@[simp]
lemma Literal.reduce_neg_self {vars} {l : Literal vars} (h : ¬l.polarity) :
    (Literal.mk ⟨l.variable, by aesop⟩ false) = l := by aesop

@[simp]
lemma Literal.reduce_toLiteral_variable {vars} {v : Variable} {h : v ∈ vars} {p : Bool} :
    (v.toLiteral h p).variable = v := by rfl

@[simp]
lemma Literal.reduce_toLiteral_polarity {vars} {v : Variable} {h : v ∈ vars} {p : Bool} :
    (v.toLiteral h p).polarity = p := by rfl

/-- Clauses are defined as finite set of literals, so we lose the order of them. -/
abbrev Clause (vars : Variables) := Finset (Literal vars)

/-- The set of variables appearing in the clause. -/
def Clause.variables {vars} (c : Clause vars) : Finset Variable :=
  c.image Literal.variable

@[aesop unsafe, grind →]
lemma literal_in_clause_variables {vars} {l : Literal vars} {c : Clause vars} (h_l_in_c : l ∈ c) :
    l.variable ∈ c.variables := by
  unfold Clause.variables
  exact Finset.mem_image_of_mem Literal.variable h_l_in_c

@[aesop safe, grind .]
lemma clause_variables_subset_vars {vars} (c : Clause vars) : c.variables ⊆ vars := by
  grind [Clause.variables]

@[aesop unsafe, grind →]
lemma clause_variables_maintains_subset {vars} {c₁ c₂ : Clause vars} (h_sub : c₁ ⊆ c₂) :
    c₁.variables ⊆ c₂.variables := by grind [Clause.variables]

@[aesop unsafe, grind →]
lemma clause_variable_mem_variables_maintains_subset {vars} {c₁ c₂ : Clause vars} (h_sub : c₁ ⊆ c₂)
    {v : Variable} (h_v_mem : v ∈ c₁.variables) : v ∈ c₂.variables := by grind

/-- Similarly to `Clause`, just a set of clauses.
This will lead to a `noncomputable` side-effects later. -/
abbrev CNFFormula (vars : Variables) := Finset (Clause vars)

/-- Evaluation function of a literal. -/
def Literal.eval {vars} : Literal vars → Assignment vars → Bool :=
  fun l => fun ρ => ρ l.variable (by aesop) = l.polarity

/-- l ↦ ¬l -/
def Literal.negate {vars} : Literal vars → Literal vars :=
  fun l => Literal.mk l.v ¬l.polarity

@[simp]
lemma Literal.eval_negate_eq_not_eval {vars} (l : Literal vars) (a : Assignment vars) :
    l.negate.eval a = ¬ l.eval a := by
  unfold eval negate Literal.variable;
  aesop (add unsafe Bool.eq_not.mpr)

@[simp, grind =]
lemma Literal.neg_polarity {vars} (l : Literal vars) : l.negate.polarity = ¬l.polarity := by
  aesop (add safe unfold negate)

@[simp]
lemma Literal.neg_neg {vars} (l : Literal vars) : l.negate.negate = l := by
  aesop (add safe unfold negate)

/-- Evaluation function of a clause. -/
def Clause.eval {vars} (c : Clause vars) (a : Assignment vars) : Bool :=
  c.fold (Bool.or) false (fun l => l.eval a)

/-- Evaluation function of a formula. -/
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
    have h_c_not_in_φ' : c ∉ φ' := by simp [φ']
    have : φ = insert c φ' := by rw [Finset.insert_erase h_c_in_φ]
    simp [this, Finset.fold_insert h_c_not_in_φ', h_c_eval_a_false]
  case mp =>
    intro h_φ_eval_a_false
    contrapose! h_φ_eval_a_false
    simp only [ne_eq, Bool.not_eq_false]
    unfold CNFFormula.eval
    induction φ using Finset.induction_on <;> aesop

lemma Clause.eval_eq_true_iff_exists_satisfied_literal {vars} (c : Clause vars)
    (a : Assignment vars) : c.eval a = true ↔ (∃ l, l ∈ c ∧ l.eval a = true) := by
  constructor
  case mpr =>
    intro h_exists_falsified_c
    unfold Clause.eval
    obtain ⟨l, h_l_in_c, h_l_eval_a_false⟩ := h_exists_falsified_c
    let c' := c.erase l
    have h_l_not_in_c' : l ∉ c' := by simp [c']
    have : c = insert l c' := by rw [Finset.insert_erase h_l_in_c]
    simp [this, Finset.fold_insert h_l_not_in_c', h_l_eval_a_false]
  case mp =>
    intro h_c_eval_a_false
    contrapose! h_c_eval_a_false
    simp only [ne_eq, Bool.not_eq_true] at h_c_eval_a_false ⊢
    unfold Clause.eval
    induction c using Finset.induction_on <;> aesop

lemma CNFFormula.eval_eq_true_iff_all_satisfied_clauses {vars} (φ : CNFFormula vars)
    (a : Assignment vars) : φ.eval a = true ↔ (∀ c, c ∈ φ → c.eval a = true) := by
  grind [eval_eq_false_iff_exists_falsified_clause]

lemma Clause.eval_eq_false_iff_all_falsified_literals {vars} (c : Clause vars)
    (a : Assignment vars) : c.eval a = false ↔ (∀ l, l ∈ c → l.eval a = false) := by
  grind [eval_eq_true_iff_exists_satisfied_literal]

/-- The result of application of the Resolution rule to a pair of clauses.
Does not require the resolution variable `x` to be present in both clauses. -/
def Clause.resolve {vars} (c₁ c₂ : Clause vars) (x : Variable) (h_x : x ∈ vars) : Clause (vars) :=
  c₁.erase (x.toLiteral h_x true) ∪ c₂.erase (x.toLiteral h_x false)

@[aesop unsafe, grind →]
lemma Clause.not_in_variables_subset {vars} {c₁ c₂ : Clause vars} {x : Variable}
    (h_subset : c₁ ⊆ c₂) (h : x ∉ c₂.variables) : x ∉ c₁.variables := by grind

@[simp]
lemma Clause.union_variables {vars} (c₁ c₂ : Clause vars) :
    (c₁ ∪ c₂).variables = c₁.variables ∪ c₂.variables := by grind [Clause.variables]

@[aesop unsafe, grind →]
lemma Clause.subset_variables {vars} {c₁ c₂ : Clause vars} (h : c₁ ⊆ c₂) :
    c₁.variables ⊆ c₂.variables := by
  unfold Clause.variables
  rw [Finset.image_subset_iff]
  intro l h_l
  aesop

lemma Clause.resolve_maintains_subset {vars} {c₁ c₁' c₂ c₂' : Clause vars} {x : Variable}
    (h_x : x ∈ vars) (h_subset₁ : c₁ ⊆ c₁') (h_subset₂ : c₂ ⊆ c₂') :
    Clause.resolve c₁ c₂ x h_x ⊆ Clause.resolve c₁' c₂' x h_x := by
  unfold Clause.resolve
  intro l h_l_in_resolve
  aesop

lemma Clause.resolve_satisfies_h_resolve_left {vars} {c₁ c₂ : Clause vars} {v : Variable}
    (h_v_mem_vars : v ∈ vars) :
    (c₁ ⊆ c₁.resolve c₂ v h_v_mem_vars ∪ { v.toLiteral h_v_mem_vars true }) := by
  unfold Clause.resolve
  intro l h
  simp only [Finset.union_singleton, Finset.mem_insert, Finset.mem_union, Finset.mem_erase, ne_eq]
  tauto

lemma Clause.resolve_satisfies_h_resolve_right {vars} {c₁ c₂ : Clause vars} {v : Variable}
    (h_v_mem_vars : v ∈ vars) :
    (c₂ ⊆ c₁.resolve c₂ v h_v_mem_vars ∪ { v.toLiteral h_v_mem_vars false }) := by
  unfold Clause.resolve
  intro l h
  simp only [Finset.union_singleton, Finset.mem_insert, Finset.mem_union, Finset.mem_erase, ne_eq]
  tauto

/-- Predicate: `ρ` is the partial assignment on `{x.variable}` that assigns it the value `b`.
Use `b = x.polarity` for a satisfying assignment, `b = !x.polarity` for a falsifying one. -/
abbrev Literal.IsAssignment {vars} (x : Literal vars) (b : Bool)
    (ρ : Assignment ({x.variable} : Finset Variable)) : Prop :=
  ρ = fun _ _ => b

#lint
