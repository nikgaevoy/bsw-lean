import BSWLean.CNF
import BSWLean.Substitutions
import BSWLean.Conversion

/-!
# Super-CNF-Formulas

A different way to define literals, clauses and CNF-formulas without a set of variables as a
polymorphic argument. Used to prove lemmas about conversions of previously defined literals and
clauses.

## Implementation notes

The absence of the polymorphic parameter allows us to use the standard `Equivalence` class, which
makes proving complex statements easier.
-/

/-- The analog of `Literal`. -/
@[aesop safe [constructors, cases]]
structure SuperLiteral where
  /-- The set of variables -/
  vars : Variables
  /-- The literal itself -/
  lit : Literal vars
deriving DecidableEq

/-- The analog of `Clause`. -/
@[aesop safe [constructors, cases]]
structure SuperClause where
  /-- The set of variables -/
  vars : Variables
  /-- Stored clause -/
  clause : Clause vars
deriving DecidableEq

/-- `Literal ↦ SuperLiteral` -/
@[simp]
def Literal.toSuperLiteral {vars} (l : Literal vars) : SuperLiteral :=
  SuperLiteral.mk vars l

/-- Conversion function for regular literals. -/
@[aesop safe [unfold]]
def Literal.convert {vars₁ : Variables} (l : Literal vars₁) (vars₂ : Variables)
    (h_mem : l.variable ∈ vars₂) : Literal vars₂ :=
  Literal.mk ⟨l.variable, h_mem⟩ l.polarity

/-- `SuperLiteral ↦ Literal` -/
@[aesop safe [unfold]]
def SuperLiteral.toLiteral (sl : SuperLiteral) (vars : Variables) : Option (Literal vars) :=
  if h : sl.vars == vars then
    some (sl.lit.convert vars (by aesop))
  else
    none

lemma Literal.convert_inj {vars vars'} {l₁ l₂ : Literal vars} {h₁ h₂}
    (h : Literal.convert l₁ vars' h₁ = Literal.convert l₂ vars' h₂) : l₁ = l₂ := by aesop

@[simp, grind =]
lemma Literal.convert_variable {vars₁ vars₂ : Variables} (l : Literal vars₁)
    {h_mem : l.variable ∈ vars₂} : (l.convert vars₂ h_mem).variable = l.variable := by aesop

@[simp, grind =]
lemma Literal.convert_polarity {vars₁ vars₂ : Variables} (l : Literal vars₁)
    {h_mem : l.variable ∈ vars₂} : (l.convert vars₂ h_mem).polarity = l.polarity := by aesop

@[simp]
lemma Literal.convert_keeps_equality {vars₁ vars₂ : Variables} (l₁ l₂ : Literal vars₁) {h₁ h₂} :
    l₁.convert vars₂ h₁ = l₂.convert vars₂ h₂ ↔ l₁ = l₂ := by aesop


@[simp]
lemma SuperLiteral.toLiteral_eq_none_iff_wrong_vars {vars} (sl : SuperLiteral) :
    sl.toLiteral vars = none ↔ vars != sl.vars := by aesop

/-- The equivalence class for literals. Cannot be plugged in to `Equivalence` since it is defined
for objects of two different types. -/
@[aesop safe [constructors, cases]]
class LiteralEquiv {vars₁ vars₂} (l₁ : Literal vars₁) (l₂ : Literal vars₂) : Prop where
  h_equiv : l₁.variable = l₂.variable ∧ l₁.polarity = l₂.polarity

/-- A class to prove `Equivalence`. -/
@[aesop safe [constructors, cases]]
class SuperLiteralEquiv (sl₁ sl₂ : SuperLiteral) : Prop where
  h_equiv : LiteralEquiv sl₁.lit sl₂.lit


@[simp]
lemma Literal.equiv_equiv {vars} (c₁ c₂ : Literal vars) : LiteralEquiv c₁ c₂ ↔ c₁ = c₂ := by aesop

@[aesop unsafe]
lemma Literal.equiv_trans {vars₁} {vars₂} {vars₃}
    {l₁ : Literal vars₁} (l₂ : Literal vars₂) {l₃ : Literal vars₃}
    (h_12 : LiteralEquiv l₁ l₂) (h_23 : LiteralEquiv l₂ l₃) : LiteralEquiv l₁ l₃ := by aesop

@[simp]
lemma SuperLiteral.equiv_Equivalence : Equivalence SuperLiteralEquiv := by
  constructor
  case refl =>
    intro x
    aesop
  case symm =>
    intro x y h_eq
    aesop
  case trans =>
    intro x y z hxy hyz
    aesop


@[aesop safe]
lemma Literal.convert_equiv {vars₁ vars₂ : Variables} (l : Literal vars₁) {h : l.variable ∈ vars₂} :
    LiteralEquiv (l.convert vars₂ h) l := by aesop

@[simp]
lemma Literal.convert_self {vars : Variables} (l : Literal vars) {h} : l.convert vars h = l := by
  aesop

@[simp]
lemma Literal.convert_convert {vars₁ vars₂ vars₃ : Variables} (l : Literal vars₁) {h₁ h₂} :
    (l.convert vars₂ h₁).convert vars₃ h₂ = l.convert vars₃ (by simp_all) := by aesop

@[simp]
lemma Literal.convert_eval {vars sub_vars : Variables}
    (l : Literal vars) (h_subset : sub_vars ⊆ vars) {h} (ρ : Assignment vars) :
    (l.convert sub_vars h).eval (ρ.restrict sub_vars h_subset) = l.eval ρ := by aesop

@[simp]
lemma Literal.eqiuv_SuperLiteral {vars} (l : Literal vars) (sl : SuperLiteral) :
    sl.toLiteral vars = some l ↔ l.toSuperLiteral = sl := by aesop

/-- Conversion function for super-literals. -/
@[simp]
def SuperLiteral.convert (sl : SuperLiteral) (vars : Variables)
    (h_mem : sl.lit.variable ∈ vars) : SuperLiteral :=
  SuperLiteral.mk vars (sl.lit.convert vars h_mem)

lemma SuperLiteral.convert_equivalence (sl : SuperLiteral) (vars : Variables) {h} :
    SuperLiteralEquiv sl (sl.convert vars h) := by aesop

@[simp]
lemma SuperLiteral.vars_isSome (sl : SuperLiteral) : (sl.toLiteral sl.vars).isSome := by aesop

@[simp]
lemma SuperLiteral.equiv_iff_LiteralEquiv (sl₁ sl₂ : SuperLiteral) :
    SuperLiteralEquiv sl₁ sl₂ ↔
    LiteralEquiv
      ((sl₁.toLiteral sl₁.vars).get (vars_isSome sl₁))
      ((sl₂.toLiteral sl₂.vars).get (vars_isSome sl₂)) := by aesop

/-- Conversion function for clauses. -/
def Clause.convert {vars₁ : Variables} (c : Clause vars₁) (vars₂ : Variables)
    (h_mem : ∀ l ∈ c, l.variable ∈ vars₂) : Clause vars₂ :=
  let q := fun l => if h : l ∈ c then some (Literal.convert l vars₂ (h_mem l h)) else none

  c.filterMap q <| by aesop

/-- Conversion for CNF-formulas. -/
def CNFFormula.simple_convert (vars₁ : Variables) (vars₂ : Variables) (φ : CNFFormula vars₁)
    (h_subs : vars₁ ⊆ vars₂) : CNFFormula vars₂ :=
  φ.image <| fun c => c.convert vars₂ <| by aesop

/-- Sometimes we have two different definitions of the same set of variables. This function
trivially converts from one definition to another. -/
@[aesop safe [unfold]]
def Clause.convert_trivial {vars₁ : Variables} (c : Clause vars₁) (vars₂ : Variables)
    (h_mem : vars₁ = vars₂) : Clause vars₂ :=
  c.convert vars₂ <| by aesop

/-- A class to represent `c₁ ⊆ c₂` for a pair of clauses of two different types. -/
@[aesop safe [constructors, cases]]
class ClauseSubset {vars₁} {vars₂} (c₁ : Clause vars₁) (c₂ : Clause vars₂) : Prop where
  h_subset : ∀ l ∈ c₁, ∃ l' ∈ c₂, LiteralEquiv l l'

/-- An equivalence class for clauses. Similar problem with two different types as we had with
`LiteralEquiv`. -/
@[aesop safe [constructors, cases]]
class ClauseEquiv {vars₁} {vars₂} (c₁ : Clause vars₁) (c₂ : Clause vars₂) : Prop where
  h_mp : ClauseSubset c₁ c₂
  h_mpr : ClauseSubset c₂ c₁

/-- `sc₁ ⊆ sc₂`. -/
@[aesop safe [constructors, cases]]
class SuperClauseSubset (sc₁ sc₂ : SuperClause) : Prop where
  h_subset : ClauseSubset sc₁.clause sc₂.clause

/-- A class to plug into `Equivalence`. -/
@[aesop safe [constructors, cases]]
class SuperClauseEquiv (sc₁ sc₂ : SuperClause) : Prop where
  h_equiv : ClauseEquiv sc₁.clause sc₂.clause

@[simp]
lemma Clause.ClauseEquiv_iff_eq {vars} (c₁ c₂ : Clause vars) :
    ClauseEquiv c₁ c₂ ↔ c₁ = c₂ := by aesop

@[aesop unsafe]
lemma Clause.subset_trans {vars₁} {vars₂} {vars₃}
    {c₁ : Clause vars₁} (c₂ : Clause vars₂) {c₃ : Clause vars₃}
    (h_12 : ClauseSubset c₁ c₂) (h_23 : ClauseSubset c₂ c₃) : ClauseSubset c₁ c₃ := by
  constructor
  intro l₁ h_l₁
  obtain ⟨l₂, h_l₂⟩ := h_12.h_subset l₁ h_l₁
  obtain ⟨l₃, h_l₃⟩ := h_23.h_subset l₂ h_l₂.left
  use l₃
  aesop

@[simp]
lemma SuperClause.equiv_Equivalence : Equivalence SuperClauseEquiv := by
  constructor
  case refl =>
    intro x
    aesop
  case symm =>
    intro x y h_xy
    aesop
  case trans =>
    intro x y z h_xy h_yz
    constructor
    constructor
    all_goals apply Clause.subset_trans y.clause
    all_goals aesop

/-- `Clause ↦ SuperClause`. -/
@[aesop safe [unfold]]
def Clause.toSuperClause {vars} (c : Clause vars) : SuperClause :=
  SuperClause.mk vars c

/-- `SuperClause ↦ Clause`. -/
@[aesop safe [unfold]]
def SuperClause.toClause (sc : SuperClause) (vars : Variables) : Option (Clause vars) :=
  if h : sc.vars = vars then
    some (sc.clause.convert vars (by aesop))
  else
    none

@[simp]
lemma SuperClause.vars_isSome (sc : SuperClause) : (sc.toClause sc.vars).isSome := by
  unfold toClause
  aesop


@[simp]
lemma Clause.convert_self {vars : Variables} (c : Clause vars) {h} : c.convert vars h = c := by
  unfold convert
  aesop

@[simp]
lemma Clause.eqiuv_SuperClause {vars} (c : Clause vars) (sc : SuperClause) :
    sc.toClause vars = some c ↔ c.toSuperClause = sc := by
  constructor
  case mp =>
    intro h
    aesop

  case mpr =>
    intro h
    unfold Clause.toSuperClause at h
    aesop


@[simp]
lemma SuperClause.equiv_iff_ClauseEquiv (sc₁ sc₂ : SuperClause) :
    SuperClauseEquiv sc₁ sc₂ ↔
    ClauseEquiv
      ((sc₁.toClause sc₁.vars).get (vars_isSome sc₁))
      ((sc₂.toClause sc₂.vars).get (vars_isSome sc₂)) := by aesop

@[grind .]
lemma Clause.equiv_sym {vars₁ vars₂} {c₁ : Clause vars₁} {c₂ : Clause vars₂}
    (h : ClauseEquiv c₁ c₂) : ClauseEquiv c₂ c₁ := by aesop

@[aesop unsafe]
lemma Clause.equiv_trans {vars₁ vars₂ vars₃}
    {c₁ : Clause vars₁} (c₂ : Clause vars₂) {c₃ : Clause vars₃}
    (h_12 : ClauseEquiv c₁ c₂) (h_23 : ClauseEquiv c₂ c₃) : ClauseEquiv c₁ c₃ := by
  let sc₁ := c₁.toSuperClause
  have h_1 : sc₁.toClause vars₁ = c₁ := by
    exact (eqiuv_SuperClause c₁ sc₁).mpr rfl
  have h_1_vars : sc₁.vars = vars₁ := by trivial
  let sc₂ := c₂.toSuperClause
  have h_2 : sc₂.toClause vars₂ = c₂ := by
    exact (eqiuv_SuperClause c₂ sc₂).mpr rfl
  have h_2_vars : sc₂.vars = vars₂ := by trivial
  let sc₃ := c₃.toSuperClause
  have h_3 : sc₃.toClause vars₃ = c₃ := by
    exact (eqiuv_SuperClause c₃ sc₃).mpr rfl
  have h_3_vars : sc₃.vars = vars₃ := by trivial

  have h_12' : SuperClauseEquiv sc₁ sc₂ := by
    exact { h_equiv := h_12 }

  have h_23' : SuperClauseEquiv sc₂ sc₃ := by
    exact { h_equiv := h_23 }

  have h_13' : SuperClauseEquiv sc₁ sc₃ := by
    apply SuperClause.equiv_Equivalence.trans
    · exact h_12'
    · exact h_23'

  rw [SuperClause.equiv_iff_ClauseEquiv] at h_13'
  grind only [= Option.get_some]

@[aesop unsafe]
lemma literal_mem_clause_convert_if_literal_convert_mem_clause {vars₁ vars₂}
    {l : Literal vars₁} {c : Clause vars₂} {h} (h_l_var : l.variable ∈ vars₂)
    (h_convert : l.convert vars₂ h_l_var ∈ c) : l ∈ c.convert vars₁ h := by
  simp only [Clause.convert, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    Option.some.injEq, and_exists_self]
  use l.convert vars₂ h_l_var
  aesop

@[simp, grind .]
lemma Clause.convert_equiv {vars₁} {vars₂} (c : Clause vars₁) {h} :
    ClauseEquiv (c.convert vars₂ h) c := by aesop (add safe unfold Clause.convert)

/-- Conversion for super-clauses. The important point that it does not change the type. -/
def SuperClause.convert (cl : SuperClause) (vars : Variables)
    (h_mem : ∀ l ∈ cl.clause, l.variable ∈ vars) : SuperClause :=
  SuperClause.mk vars (cl.clause.convert vars h_mem)

@[aesop safe]
lemma SuperClause.convert_equivalence (sc : SuperClause) (vars : Variables) {h} :
    SuperClauseEquiv sc (sc.convert vars h) := by
  unfold SuperClause.convert
  constructor
  constructor
  case h_equiv.h_mp =>
    constructor
    intro l h_l
    use l.convert vars <| h l h_l
    aesop (add safe unfold Clause.convert)
  case h_equiv.h_mpr =>
    aesop (add safe unfold Clause.convert)

@[simp]
lemma Clause.convert_keeps_literals {vars₁ : Variables} {c : Clause vars₁} {l : Literal vars₁}
    (vars₂ : Variables) {h_l} {h_c} : l.convert vars₂ h_l ∈ c.convert vars₂ h_c ↔ l ∈ c := by
  constructor
  · intro h_convert
    unfold Clause.convert at h_convert
    simp_all
  · unfold Clause.convert
    aesop

lemma convert_h₃ {vars₁ vars₂ vars₃ : Variables} (c : Clause vars₁)
    (h₁ : ∀ l ∈ c, l.variable ∈ vars₂) (h₂ : ∀ l ∈ (c.convert vars₂ h₁), l.variable ∈ vars₃) :
    ∀ l ∈ c, l.variable ∈ vars₃ := by
  intro l h_l_c
  suffices ∃ l' ∈ (c.convert vars₂ h₁), LiteralEquiv l l' by aesop
  use l.convert vars₂ (h₁ l h_l_c)
  apply And.intro
  · simp_all
  · aesop

@[simp]
lemma Clause.convert_convert {vars₁ vars₂ vars₃ : Variables} (c : Clause vars₁) {h₁ h₂} :
    (c.convert vars₂ h₁).convert vars₃ h₂ =
    c.convert vars₃ (by exact fun l a ↦ convert_h₃ c h₁ h₂ l a) := by
  let c₁ := c.convert vars₂ h₁
  let c₂ := c₁.convert vars₃ h₂
  let c₃ := c.convert vars₃ (by exact fun l a ↦ convert_h₃ c h₁ h₂ l a)

  rw [←Clause.ClauseEquiv_iff_eq]
  have : ClauseEquiv c₃ c := by
    exact convert_equiv c
  have h_03 : ClauseEquiv c c₃ := by
    constructor
    · exact ClauseEquiv.h_mpr
    · exact ClauseEquiv.h_mp
  have h_10 : ClauseEquiv c₁ c := by
    exact convert_equiv c
  have h_21 : ClauseEquiv c₂ c₁ := by
    exact convert_equiv c₁
  have : ClauseEquiv c₂ c := by
    exact equiv_trans c₁ h_21 h_10
  apply Clause.equiv_trans c
  · assumption
  · assumption

/-- Class defining the fact that two assignments agree on their intersection. -/
@[aesop safe [constructors, cases]]
class Agree {vars₁} {vars₂} (ρ₁ : Assignment vars₁) (ρ₂ : Assignment vars₂) : Prop where
  h_agree : ∀ v ∈ vars₁ ∩ vars₂, ∀ h₁ h₂, (ρ₁ v h₁) = (ρ₂ v h₂)

@[simp]
lemma Assignment.restrict_agree {vars} (ρ : Assignment vars) (sub_vars : Variables) {h} :
    Agree ρ (ρ.restrict sub_vars h) := by aesop

@[simp]
lemma Assignment.agree_iff_eq {vars} (ρ₁ ρ₂ : Assignment vars) :
    Agree ρ₁ ρ₂ ↔ ρ₁ = ρ₂ := by aesop

lemma Agree.sym {vars₁ vars₂} (ρ₁ : Assignment vars₁) (ρ₂ : Assignment vars₂) (h : Agree ρ₁ ρ₂) :
    Agree ρ₂ ρ₁ := by aesop

@[simp]
lemma Clause.convert_eval {vars sub_vars : Variables}
    (c : Clause vars) (h_subset : sub_vars ⊆ vars) {h} (ρ : Assignment vars) :
    (c.convert sub_vars h).eval (ρ.restrict sub_vars h_subset) = c.eval ρ := by
  induction c using Finset.induction_on'
  case empty => aesop
  case insert l c' h_l h_subset h_l_c' h_ind =>
    unfold Clause.eval
    have : convert (insert l c') sub_vars h =
      insert (l.convert sub_vars (by aesop)) (convert c' sub_vars (by aesop))  := by
      unfold Clause.convert
      aesop
    rw [this]
    simp only [Finset.fold_insert_idem, Literal.convert_eval]
    tauto


@[aesop unsafe]
lemma convert_agree_eval {vars₁ vars₂} (c₁ : Clause vars₁) (ρ₁ : Assignment vars₁)
    (c₂ : Clause vars₂) (ρ₂ : Assignment vars₂) (h_equiv : ClauseEquiv c₁ c₂)
    (h_agree : Agree ρ₁ ρ₂) : c₁.eval ρ₁ = c₂.eval ρ₂ := by
  let sub_vars := vars₁ ∩ vars₂
  have h_sub₁ : ∀ l ∈ c₁, l.variable ∈ sub_vars := by
    intro l h_l_c₁
    unfold sub_vars
    rw [@Finset.mem_inter]
    constructor
    · exact Literal.variable_mem_vars l
    · have : ∃ l' ∈ c₂, LiteralEquiv l l' := by
        apply h_equiv.h_mp.h_subset l
        assumption
      obtain ⟨l', h_l'⟩ := this
      aesop

  let c₁' := (c₁.convert sub_vars h_sub₁)
  let ρ₁' := (ρ₁.restrict sub_vars Finset.inter_subset_left)

  have h_c₁_eq : c₁.eval ρ₁ = c₁'.eval ρ₁' := by rw [Clause.convert_eval]

  have h_sub₂ : ∀ l ∈ c₂, l.variable ∈ sub_vars := by
    intro l h_l_c₂
    unfold sub_vars
    rw [@Finset.mem_inter]
    constructor
    · have : ∃ l' ∈ c₁, LiteralEquiv l l' := by
        apply h_equiv.h_mpr.h_subset l
        assumption
      obtain ⟨l', h_l'⟩ := this
      aesop
    · exact Literal.variable_mem_vars l

  let c₂' := (c₂.convert sub_vars h_sub₂)
  let ρ₂' := (ρ₂.restrict sub_vars Finset.inter_subset_right)

  have h_c₂_eq : c₂.eval ρ₂ = c₂'.eval ρ₂' := by
    rw [Clause.convert_eval]

  have : c₁' = c₂' := by
    refine (Clause.ClauseEquiv_iff_eq c₁' c₂').mp ?_
    have h₁ : ClauseEquiv c₁ c₁' := by grind
    have h₂ : ClauseEquiv c₂' c₂ := by grind
    apply Clause.equiv_trans c₁
    · grind
    apply Clause.equiv_trans c₂
    all_goals grind

  rw [h_c₁_eq]
  rw [h_c₂_eq]
  rw [←this]

  suffices h: ρ₁' = ρ₂' by rw [h]
  aesop

@[simp]
lemma Clause.convert_trivial_subset {vars₁ : Variables} {c₁ c₂ : Clause vars₁}
    (vars₂ : Variables) {h} (_ : c₁ ⊆ c₂) :
    c₁.convert_trivial vars₂ h ⊆ c₂.convert_trivial vars₂ h := by aesop

@[simp]
lemma Clause.convert_trivial_subset_insert {vars₁ vars₂ : Variables} {c₁ c₂ : Clause vars₁}
    {l : Literal vars₂} {h} (_ : c₁ ⊆ insert (l.convert vars₁ (by aesop)) c₂) :
    c₁.convert_trivial vars₂ h ⊆ insert l (c₂.convert_trivial vars₂ h) := by aesop

@[aesop safe]
lemma Clause.convert_keeps_subset {vars₁ : Variables} {c₁ c₂ : Clause vars₁} (vars₂ : Variables)
    {h_c₁ h_c₂} (h : c₁ ⊆ c₂) : c₁.convert vars₂ h_c₁ ⊆ c₂.convert vars₂ h_c₂ := by
  rw [@Finset.subset_iff]
  intro l h_l
  aesop (add safe unfold Clause.convert)

lemma Clause.equiv_keeps_subset {vars₁ vars₂ : Variables}
    (c₁ c₂ : Clause vars₁) {c₁' c₂' : Clause vars₂}
    (h₁ : ClauseSubset c₁' c₁) (h₂ : ClauseSubset c₂ c₂')
    (h_subset : c₁ ⊆ c₂) : c₁' ⊆ c₂' := by
  rw [@Finset.subset_iff]
  intro l₁ h_l₁
  obtain ⟨l, ⟨h_l, _⟩⟩ := h₁.h_subset l₁ h_l₁
  apply h_subset at h_l
  obtain ⟨l₂, ⟨h_l₂, _⟩⟩ := h₂.h_subset l h_l
  have : l₁ = l₂ := by
    rw [←Literal.equiv_equiv]
    apply Literal.equiv_trans l
    · assumption
    · assumption
  rw [this]
  assumption

/-- This is a technical lemma needed in one of the proofs. -/
lemma Clause.convert_maintains_subset_insert {vars₁ : Variables} (c₁ : Clause vars₁)
    (c₂ : Clause vars₁) (vars₂ : Variables) (l : Literal vars₂) (h : l.variable ∈ vars₁) {h₁} {h₂} :
    c₁ ⊆ insert (l.convert vars₁ h) c₂ →
    c₁.convert vars₂ h₁ ⊆ insert l (c₂.convert vars₂ h₂) := by
  intro h_c
  have h_c₁ : ClauseEquiv c₁ (c₁.convert vars₂ h₁) := by grind
  have h_c₂ : ClauseEquiv (insert (l.convert vars₁ h) c₂) (insert l (c₂.convert vars₂ h₂)) := by
    constructor
    · constructor
      intro l' h_l'
      rw [Finset.mem_insert] at h_l'
      cases h_l'
      case inl =>
        use l
        aesop
      case inr =>
        use l'.convert vars₂ <| by aesop
        constructor
        · refine Finset.mem_insert_of_mem ?_
          simp_all
        · aesop
    · constructor
      intro l' h_l'
      rw [Finset.mem_insert] at h_l'
      cases h_l'
      case inl => aesop
      case inr =>
        have : l'.variable ∈ vars₁ := by aesop (add safe unfold Clause.convert)
        use l'.convert vars₁ this
        aesop (add safe unfold Clause.convert)
  apply Clause.equiv_keeps_subset c₁ (insert (l.convert vars₁ h) c₂)
  all_goals aesop

/-- Combines two clauses into one. Inverse function to `Clause.split`. -/
@[aesop safe unfold]
def Clause.combine {vars₁ vars₂} (c₁ : Clause vars₁) (c₂ : Clause vars₂)
    (h : Disjoint vars₁ vars₂) : Clause (vars₁.disjUnion vars₂ h) :=
  let vars := (vars₁.disjUnion vars₂ h)
  let c₁' := c₁.convert vars (by aesop)
  let c₂' := c₂.convert vars (by aesop)

  c₁' ∪ c₂'

@[simp]
lemma Clause.convert_trivial_keeps_variables {vars₁ vars₂} (c : Clause vars₁)
    (h_eq : vars₁ = vars₂) : (c.convert_trivial vars₂ h_eq).variables = c.variables := by aesop

@[simp]
lemma Clause.convert_keeps_variables {vars₁} (c : Clause vars₁) (vars₂ : Variables) {h} :
    (c.convert vars₂ h).variables = c.variables := by
  aesop (add safe unfold [Clause.variables, Clause.convert])

@[simp]
lemma Clause.combine_variables {vars₁} {vars₂} (c₁ : Clause vars₁) (c₂ : Clause vars₂)
    (h : Disjoint vars₁ vars₂) : (c₁.combine c₂ h).variables = c₁.variables ∪ c₂.variables := by
  unfold combine
  simp

lemma Clause.combine_not_variables {vars₁} {vars₂} (c₁ : Clause vars₁) (c₂ : Clause vars₂)
    (h : Disjoint vars₁ vars₂) (x : Variable) (h₁ : x ∉ c₁.variables) (h₂ : x ∉ c₂.variables) :
    x ∉ (c₁.combine c₂ h).variables := by grind [Clause.combine_variables]

@[simp]
lemma Clause.convert_empty {vars₁ vars₂} (c : Clause vars₁) {h} (_ : c = ∅) :
    c.convert vars₂ h = ∅ := by aesop

@[aesop unsafe]
lemma Clause.substitute_subset {vars sub_vars} (c : Clause vars)
    (ρ : Assignment sub_vars) (h₁) :
    ((((c.substitute ρ).get h₁) : Clause (vars \ sub_vars)).convert vars <| by grind) ⊆ c := by
  intro _
  aesop (add safe unfold [Clause.substitute, Clause.convert])

/-- Another technical lemma from the future. -/
lemma Clause.substitute_combine {vars} {sub_vars} (c : Clause vars) (ρ : Assignment sub_vars)
    (h_subset : sub_vars ⊆ vars) (h : (c.substitute ρ).isSome) :
    c ⊆ (Clause.combine ((c.substitute ρ).get h)
                        ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop) := by
  let c_combine := (Clause.combine ((c.substitute ρ).get h) ρ.toClause Finset.sdiff_disjoint)
  let c_combine_convert := c_combine.convert_trivial vars (by aesop)

  have h_convert_subset : ClauseSubset c_combine c_combine_convert := by
    constructor
    unfold c_combine_convert
    intro l h_l
    unfold Clause.convert_trivial Clause.convert
    simp only [Finset.mem_filterMap, Option.dite_none_right_eq_some, Option.some.injEq,
      and_exists_self, ↓existsAndEq, true_and]
    use l
    aesop

  suffices h_subset : ClauseSubset c c_combine by
    have := Clause.subset_trans c_combine h_subset h_convert_subset
    aesop

  have h_ρ : ClauseSubset ρ.toClause c_combine := by
    constructor
    unfold c_combine Clause.combine
    simp only
    intro l h_l
    use l.convert (Finset.disjUnion (vars \ sub_vars) sub_vars (Finset.sdiff_disjoint)) <| by aesop
    constructor
    · rw [@Finset.mem_union]
      right
      simp_all
    · aesop

  have h_sub : ClauseSubset ((c.substitute ρ).get h) c_combine := by
    constructor
    unfold c_combine Clause.combine
    simp only
    intro l h_l
    have := Literal.variable_mem_vars l
    use l.convert (Finset.disjUnion (vars \ sub_vars) sub_vars (Finset.sdiff_disjoint)) <| by aesop
    constructor
    · rw [@Finset.mem_union]
      left
      simp_all
    · aesop

  constructor
  intro l h_l
  by_cases h_cases : l.variable ∈ sub_vars
  case pos =>
    suffices h_mid : ∃ l_ρ ∈ ρ.toClause, LiteralEquiv l l_ρ by
      obtain ⟨l_ρ, ⟨h_l_ρ, h_ρ_eq⟩⟩ := h_mid
      obtain ⟨l', ⟨h_l', h_l'_eq⟩⟩ := h_ρ.h_subset l_ρ h_l_ρ
      use l'
      constructor
      · assumption
      · apply Literal.equiv_trans l_ρ
        · assumption
        · assumption
    use (ρ.negVariable l.variable).get <| by aesop

    constructor
    · unfold Assignment.toClause
      aesop
    · constructor
      constructor
      · aesop
      · suffices h_eval : ρ l.variable (by aesop) = ¬l.polarity by aesop
        simp only [Bool.not_eq_true, eq_iff_iff, Bool.coe_true_iff_false]
        rw [substitute_isSome_iff_eval_subclause_false] at h
        simp only [Bool.not_eq_true] at h
        rw [eval_eq_false_iff_all_falsified_literals] at h
        let l' := l.restrict (vars ∩ sub_vars) <| by aesop
        have := h l' <| by aesop
        unfold Literal.eval Assignment.restrict at this
        aesop (add unsafe Bool.eq_not.mpr)

  case neg =>
    suffices h_mid : ∃ l_sub ∈ ((c.substitute ρ).get h), LiteralEquiv l l_sub by
      obtain ⟨l_sub, ⟨h_l_sub, h_sub_eq⟩⟩ := h_mid
      obtain ⟨l', ⟨h_l', h_l'_eq⟩⟩ := h_sub.h_subset l_sub h_l_sub
      use l'
      constructor
      · assumption
      · apply Literal.equiv_trans l_sub
        · assumption
        · assumption
    unfold Clause.substitute
    use l.restrict (vars \ sub_vars) (by aesop)
    constructor
    · simp only [split, shrink, Finset.mem_filter, Option.get_ite', Finset.mem_filterMap,
      Option.dite_none_right_eq_some, Option.some.injEq, and_exists_self]
      use l
      aesop
    · constructor
      unfold Literal.restrict
      aesop

lemma Clause.reverse_convert {vars₁ vars₂} {c : Clause vars₁} {h} {l : Literal vars₂}
  (h_l : l ∈ c.convert vars₂ h) : l.variable ∈ vars₁ := by
  have h_l_var := literal_in_clause_variables h_l
  have : (c.convert vars₂ h).variables = c.variables := by aesop
  rw [this] at h_l_var
  have : c.variables ⊆ vars₁ := by aesop
  aesop

@[simp]
lemma Clause.convert_maintains_eq {vars₁ vars₂} {c₁ c₂ : Clause vars₁} {h₁} {h₂} :
    c₁.convert vars₂ h₁ = c₂.convert vars₂ h₂ ↔ c₁ = c₂ := by
  let c₁' := c₁.convert vars₂ h₁
  let c₂' := c₂.convert vars₂ h₂

  let c₁'' := c₁'.convert vars₁ <| by aesop (add unsafe Clause.reverse_convert)
  let c₂'' := c₂'.convert vars₁ <| by aesop (add unsafe Clause.reverse_convert)

  have : c₁'' = c₁ := by aesop
  have : c₂'' = c₂ := by aesop

  constructor
  all_goals aesop

lemma trivial_subs_unfold_false {vars} (x : Literal vars)
    (ρ_false : (Assignment ({x.variable} : Finset Variable)))
    (h_value : x.IsFalsAssignment ρ_false)
    (h_1 : ∀ l ∈ ρ_false.toClause, l.variable ∈ vars) :
    (ρ_false.toClause).convert vars h_1 = ({x} : Clause vars) := by
  unfold Assignment.toClause Clause.convert
  aesop

lemma trivial_subs_unfold_true {vars}
    (x : Literal vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : x.IsSatAssignment ρ_true)
    (h_1 : ∀ l ∈ ρ_true.toClause, l.variable ∈ vars) :
    (ρ_true.toClause).convert vars h_1 = ({x.negate} : Clause vars) := by
  unfold Assignment.toClause Clause.convert Literal.negate
  aesop

#lint
