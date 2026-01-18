import BSWLean.CNF
import BSWLean.Substitutions
import BSWLean.Conversion

structure SuperLiteral where
  vars : Variables
  lit : Literal vars

deriving instance DecidableEq
for SuperLiteral

structure SuperClause where
  vars : Variables
  clause : Clause vars

deriving instance DecidableEq
for SuperClause

def Literal.toSuperLiteral {vars} (l : Literal vars) : SuperLiteral :=
  SuperLiteral.mk vars l

def Literal.convert {vars₁ : Variables} (l : Literal vars₁) (vars₂ : Variables)
    (h_mem : l.variable ∈ vars₂) : Literal vars₂ :=
  match l with
  | .pos v _ => Literal.pos v h_mem
  | .neg v _ => Literal.neg v h_mem

def SuperLiteral.toLiteral (sl : SuperLiteral) (vars : Variables) : Option (Literal vars) :=
  if h : sl.vars == vars then
    some (sl.lit.convert vars (by aesop))
  else
    none

lemma Literal.convert_inj {vars} (vars₂ : Variables)
: ∀ (l₁ l₂ : Literal vars), ∀ h₁, ∀ h₂,
    Literal.convert l₁ vars₂ h₁ = Literal.convert l₂ vars₂ h₂ → l₁ = l₂ := by
  unfold Literal.convert

  aesop

@[simp]
lemma Literal.convert_variable {vars₁ vars₂ : Variables} (l : Literal vars₁)
    {h_mem : l.variable ∈ vars₂} : (l.convert vars₂ h_mem).variable = l.variable := by
  unfold Literal.convert
  unfold Literal.variable

  aesop

@[simp]
lemma Literal.convert_polarity {vars₁ vars₂ : Variables} (l : Literal vars₁)
    {h_mem : l.variable ∈ vars₂} : (l.convert vars₂ h_mem).polarity = l.polarity := by
  unfold Literal.convert

  aesop

@[simp]
lemma SuperLiteral.toLiteral_eq_none_iff_wrong_vars {vars} (sl : SuperLiteral)
: sl.toLiteral vars = none ↔ vars != sl.vars := by
  unfold SuperLiteral.toLiteral

  aesop

class LiteralEquiv {vars₁} {vars₂} (l₁ : Literal vars₁) (l₂ : Literal vars₂) : Prop where
  h_equiv : l₁.variable = l₂.variable ∧ l₁.polarity = l₂.polarity

class SuperLiteralEquiv (sl₁ : SuperLiteral) (sl₂ : SuperLiteral) : Prop where
  h_equiv : LiteralEquiv sl₁.lit sl₂.lit


@[simp]
lemma Literal.equiv_equiv {vars} (c₁ : Literal vars) (c₂ : Literal vars)
: LiteralEquiv c₁ c₂ ↔ c₁ = c₂ := by
  constructor
  case mp =>
    intro h
    have h_equiv := h.h_equiv

    unfold Literal.variable at h_equiv
    unfold Literal.polarity at h_equiv

    aesop

  case mpr =>
    intro h
    constructor

    aesop

@[simp]
lemma Literal.equiv_trans {vars₁} {vars₂} {vars₃}
    (l₁ : Literal vars₁) (l₂ : Literal vars₂) (l₃ : Literal vars₃)
: LiteralEquiv l₁ l₂ → LiteralEquiv l₂ l₃ → LiteralEquiv l₁ l₃ := by
  intro h_12 h_23
  have h_12 := h_12.h_equiv
  have h_23 := h_23.h_equiv
  constructor
  aesop


lemma SuperLiteral.equiv_Equivalence : Equivalence SuperLiteralEquiv := by
  constructor
  case refl =>
    intro x
    constructor
    constructor
    unfold Literal.variable
    unfold Literal.polarity
    simp only [decide_true, decide_false, and_self]
  case symm =>
    intro x y h_eq
    have := h_eq.h_equiv.h_equiv
    constructor
    constructor
    aesop
  case trans =>
    intro x y z hxy hyz
    replace hxy := hxy.h_equiv.h_equiv
    replace hyz := hyz.h_equiv.h_equiv
    constructor
    constructor
    aesop


@[simp]
lemma Literal.convert_equiv {vars₁ vars₂ : Variables} (l : Literal vars₁) {h : l.variable ∈ vars₂}
: LiteralEquiv (l.convert vars₂ h) l := by
  constructor

  aesop

@[simp]
lemma Literal.convert_self {vars : Variables} (l : Literal vars) {h} : l.convert vars h = l := by
  unfold convert

  aesop

@[simp]
lemma Literal.convert_convert {vars₁ vars₂ vars₃ : Variables} (l : Literal vars₁) {h₁ h₂ h₃}
: (l.convert vars₂ h₁).convert vars₃ h₂ = l.convert vars₃ h₃ := by
  unfold convert

  aesop

@[simp]
lemma Literal.convert_eval {vars sub_vars : Variables}
    (l : Literal vars) (h_subset : sub_vars ⊆ vars) {h}
: ∀ ρ : Assignment vars, (l.convert sub_vars h).eval (ρ.restrict sub_vars h_subset) = l.eval ρ := by
  unfold convert

  aesop

@[simp]
lemma Literal.eqiuv_SuperLiteral {vars} (l : Literal vars) (sl : SuperLiteral)
: sl.toLiteral vars = some l ↔ l.toSuperLiteral = sl := by
  constructor
  case mp =>
    intro h
    unfold Literal.toSuperLiteral
    unfold SuperLiteral.toLiteral at h
    simp only [beq_iff_eq, Option.dite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨h_vars, h⟩ := h
    rw [←h]

    aesop

  case mpr =>
    intro h
    unfold SuperLiteral.toLiteral
    unfold Literal.toSuperLiteral at h

    aesop

def SuperLiteral.convert (sl : SuperLiteral) (vars : Variables)
    (h_mem : sl.lit.variable ∈ vars) : SuperLiteral :=
  SuperLiteral.mk vars (sl.lit.convert vars h_mem)

@[simp]
lemma SuperLiteral.convert_equivalence (sl : SuperLiteral) (vars : Variables) {h}
: SuperLiteralEquiv sl (sl.convert vars h) := by
  unfold SuperLiteral.convert
  constructor
  constructor
  aesop

@[simp]
lemma SuperLiteral.vars_isSome (sl : SuperLiteral) : (sl.toLiteral sl.vars).isSome := by
  unfold SuperLiteral.toLiteral
  aesop

@[simp]
lemma SuperLiteral.equiv_iff_LiteralEquiv (sl₁ : SuperLiteral) (sl₂ : SuperLiteral)
: SuperLiteralEquiv sl₁ sl₂ ↔
   LiteralEquiv
   ((sl₁.toLiteral sl₁.vars).get (vars_isSome sl₁))
   ((sl₂.toLiteral sl₂.vars).get (vars_isSome sl₂)) := by
  constructor
  case mp =>
    intro h
    constructor
    replace h := h.h_equiv.h_equiv
    unfold SuperLiteral.toLiteral
    aesop

  case mpr =>
    intro h
    constructor
    constructor
    replace h := h.h_equiv
    unfold SuperLiteral.toLiteral at h
    aesop

def Clause.convert {vars₁ : Variables} (c : Clause vars₁) (vars₂ : Variables)
    (h_mem : ∀ l ∈ c, l.variable ∈ vars₂) : Clause vars₂ :=
  let q := fun l => if h: l ∈ c then some (Literal.convert l vars₂ (h_mem l h)) else none

  have : (∀ (a a' : Literal vars₁), ∀ b ∈ q a, b ∈ q a' → a = a') := by
    unfold q
    unfold Literal.convert

    aesop

  c.filterMap q this

def Clause.convert_trivial {vars₁ : Variables} (c : Clause vars₁) (vars₂ : Variables)
    (h_mem : vars₁ = vars₂) : Clause vars₂ :=
  c.convert vars₂ (by aesop)

class ClauseSubset {vars₁} {vars₂} (c₁ : Clause vars₁) (c₂ : Clause vars₂) : Prop where
  h_subset : ∀ l ∈ c₁, ∃ l' ∈ c₂, LiteralEquiv l l'

class ClauseEquiv {vars₁} {vars₂} (c₁ : Clause vars₁) (c₂ : Clause vars₂) : Prop where
  h_mp : ClauseSubset c₁ c₂
  h_mpr : ClauseSubset c₂ c₁

class SuperClauseSubset (sc₁ : SuperClause) (sc₂ : SuperClause) : Prop where
  h_subset : ClauseSubset sc₁.clause sc₂.clause

class SuperClauseEquiv (sc₁ : SuperClause) (sc₂ : SuperClause) : Prop where
  h_equiv : ClauseEquiv sc₁.clause sc₂.clause

@[simp]
lemma Clause.equiv_equiv {vars} (c₁ : Clause vars) (c₂ : Clause vars) :
    ClauseEquiv c₁ c₂ ↔ c₁ = c₂ := by
  constructor

  case mp =>
    intro equiv
    have h_mp := equiv.h_mp.h_subset
    have h_mpr := equiv.h_mpr.h_subset

    ext
    aesop

  case mpr =>
    intro h_eq
    constructor
    · constructor
      aesop
    · constructor
      aesop

@[simp]
lemma Clause.subset_trans {vars₁} {vars₂} {vars₃}
    (c₁ : Clause vars₁) (c₂ : Clause vars₂) (c₃ : Clause vars₃)
    : ClauseSubset c₁ c₂ → ClauseSubset c₂ c₃ → ClauseSubset c₁ c₃ := by
  intro h_12 h_23
  replace h_12 := h_12.h_subset
  replace h_23 := h_23.h_subset

  constructor

  intro l₁ h_l₁
  obtain ⟨l₂, h_l₂⟩ := h_12 l₁ h_l₁
  obtain ⟨l₃, h_l₃⟩ := h_23 l₂ h_l₂.left
  use l₃
  constructor
  · exact h_l₃.left
  · apply Literal.equiv_trans l₁ l₂ l₃
    · exact h_l₂.right
    · exact h_l₃.right


@[simp]
lemma SuperClause.equiv_Equivalence : Equivalence SuperClauseEquiv := by
  constructor
  case refl =>
    intro x
    constructor
    aesop
  case symm =>
    intro x y h_xy
    constructor
    constructor
    · exact h_xy.h_equiv.h_mpr
    · exact h_xy.h_equiv.h_mp
  case trans =>
    intro x y z h_xy h_yz
    constructor
    constructor
    · apply Clause.subset_trans x.clause y.clause z.clause
      · exact h_xy.h_equiv.h_mp
      · exact h_yz.h_equiv.h_mp
    · apply Clause.subset_trans z.clause y.clause x.clause
      · exact h_yz.h_equiv.h_mpr
      · exact h_xy.h_equiv.h_mpr

def Clause.toSuperClause {vars} (c : Clause vars) : SuperClause :=
  SuperClause.mk vars c

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
lemma Clause.eqiuv_SuperClause {vars} (c : Clause vars) (sc : SuperClause)
: sc.toClause vars = some c ↔ c.toSuperClause = sc := by
  constructor
  case mp =>
    intro h
    unfold SuperClause.toClause at h
    unfold Clause.toSuperClause
    simp only [Option.dite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨_, h⟩ := h
    rw [←h]
    aesop

  case mpr =>
    intro h
    unfold SuperClause.toClause
    unfold Clause.toSuperClause at h
    aesop


@[simp]
lemma SuperClause.equiv_iff_ClauseEquiv (sc₁ : SuperClause) (sc₂ : SuperClause)
: SuperClauseEquiv sc₁ sc₂ ↔
   ClauseEquiv
   ((sc₁.toClause sc₁.vars).get (vars_isSome sc₁))
   ((sc₂.toClause sc₂.vars).get (vars_isSome sc₂)) := by
  constructor
  case mp =>
    intro h_super
    replace h_super := h_super.h_equiv
    unfold toClause
    aesop
  case mpr =>
    intro h
    constructor
    unfold toClause at h
    aesop


@[simp]
lemma Clause.equiv_sym {vars₁} {vars₂} (c₁ : Clause vars₁) (c₂ : Clause vars₂)
: ClauseEquiv c₁ c₂ → ClauseEquiv c₂ c₁ := by
  intro h
  constructor
  · exact ClauseEquiv.h_mpr
  · exact ClauseEquiv.h_mp

@[simp]
lemma Clause.equiv_trans {vars₁} {vars₂} {vars₃}
    (c₁ : Clause vars₁) (c₂ : Clause vars₂) (c₃ : Clause vars₃)
: ClauseEquiv c₁ c₂ → ClauseEquiv c₂ c₃ → ClauseEquiv c₁ c₃ := by
  intro h_12 h_23

  let sc₁ := c₁.toSuperClause
  have h_1 : sc₁.toClause vars₁ = c₁ := by
    exact (eqiuv_SuperClause c₁ sc₁).mpr rfl
  have h_1_vars : sc₁.vars = vars₁ := by
    trivial
  let sc₂ := c₂.toSuperClause
  have h_2 : sc₂.toClause vars₂ = c₂ := by
    exact (eqiuv_SuperClause c₂ sc₂).mpr rfl
  have h_2_vars : sc₂.vars = vars₂ := by
    trivial
  let sc₃ := c₃.toSuperClause
  have h_3 : sc₃.toClause vars₃ = c₃ := by
    exact (eqiuv_SuperClause c₃ sc₃).mpr rfl
  have h_3_vars : sc₃.vars = vars₃ := by
    trivial

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


@[simp]
lemma Clause.convert_equiv {vars₁} {vars₂} (c : Clause vars₁) {h}
: ClauseEquiv (c.convert vars₂ h) c := by
  constructor
  · constructor
    intro l h_l
    unfold Clause.convert at *
    aesop
  · constructor
    intro l h_l
    use l.convert vars₂ (h l h_l)
    constructor
    · unfold Clause.convert
      aesop
    · constructor
      aesop

def SuperClause.convert (cl : SuperClause) (vars : Variables)
    (h_mem : ∀ l ∈ cl.clause, l.variable ∈ vars) : SuperClause :=
  SuperClause.mk vars (cl.clause.convert vars h_mem)

@[simp]
lemma SuperClause.convert_equivalence (sc : SuperClause) (vars : Variables) {h}
: SuperClauseEquiv sc (sc.convert vars h) := by
  unfold SuperClause.convert
  constructor
  constructor
  case h_equiv.h_mp =>
    constructor
    intro l h_l
    let l' := l.convert vars (h l h_l)
    use l'
    constructor
    · unfold Clause.convert
      aesop
    · constructor
      aesop
  case h_equiv.h_mpr =>
    constructor
    intro l h_l
    unfold Clause.convert at *
    aesop

@[simp]
lemma Clause.ClauseEquiv_iff_eq {vars} (c₁ : Clause vars) (c₂ : Clause vars)
: ClauseEquiv c₁ c₂ ↔ c₁ = c₂ := by
  aesop

@[simp]
lemma Clause.convert_convert {vars₁ vars₂ vars₃ : Variables} (c : Clause vars₁) {h₁ h₂ h₃}
: (c.convert vars₂ h₁).convert vars₃ h₂ = c.convert vars₃ h₃ := by
  let c₁ := c.convert vars₂ h₁
  let c₂ := c₁.convert vars₃ h₂
  let c₃ := c.convert vars₃ h₃

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
    exact equiv_trans c₂ c₁ c h_21 h_10
  apply Clause.equiv_trans c₂ c c₃
  · assumption
  · assumption

class Agree {vars₁} {vars₂} (ρ₁ : Assignment vars₁) (ρ₂ : Assignment vars₂) : Prop where
  h_agree : ∀ v ∈ vars₁ ∩ vars₂, ∀ h₁ h₂, (ρ₁ v h₁) = (ρ₂ v h₂)

lemma Assignment.restrict_agree {vars} (ρ : Assignment vars) (sub_vars : Variables) {h}
: Agree ρ (ρ.restrict sub_vars h) := by
  constructor
  aesop

lemma Assignment.agree_iff_eq {vars} (ρ₁ : Assignment vars) (ρ₂ : Assignment vars)
: Agree ρ₁ ρ₂ ↔ ρ₁ = ρ₂ := by
  constructor
  case mp =>
    intro h_agree
    replace h_agree := h_agree.h_agree
    aesop
  case mpr =>
    intro h_eq
    constructor
    aesop

lemma Agree.sym {vars₁} {vars₂} (ρ₁ : Assignment vars₁) (ρ₂ : Assignment vars₂)
: Agree ρ₁ ρ₂ → Agree ρ₂ ρ₁ := by
  intro h
  replace h := h.h_agree
  constructor
  aesop

@[simp]
lemma Clause.convert_eval {vars sub_vars : Variables}
    (c : Clause vars) (h_subset : sub_vars ⊆ vars) {h}
: ∀ ρ : Assignment vars, (c.convert sub_vars h).eval (ρ.restrict sub_vars h_subset) = c.eval ρ := by
  intro ρ

  induction c using Finset.induction_on'
  case empty =>
    aesop
  case insert l c' h_l h_subset h_l_c' h_ind =>
    unfold Clause.eval
    have : convert (insert l c') sub_vars h =
      insert (l.convert sub_vars (by aesop)) (convert c' sub_vars (by aesop))  := by
      unfold Clause.convert
      aesop
    rw [this]
    simp only [Finset.fold_insert_idem, Literal.convert_eval]
    tauto


@[simp]
lemma convert_agree_eval {vars₁ vars₂} (c₁ : Clause vars₁) (ρ₁ : Assignment vars₁)
    (c₂ : Clause vars₂) (ρ₂ : Assignment vars₂)
: ClauseEquiv c₁ c₂ → Agree ρ₁ ρ₂ → c₁.eval ρ₁ = c₂.eval ρ₂ := by
  intro h_equiv h_agree
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
      have := h_l'.right.h_equiv
      aesop

  let c₁' := (c₁.convert sub_vars h_sub₁)
  let ρ₁' := (ρ₁.restrict sub_vars Finset.inter_subset_left)

  have h_c₁_eq : c₁.eval ρ₁ = c₁'.eval ρ₁' := by
    rw [Clause.convert_eval]

  have h_sub₂ : ∀ l ∈ c₂, l.variable ∈ sub_vars := by
    intro l h_l_c₂
    unfold sub_vars
    rw [@Finset.mem_inter]
    constructor
    · have : ∃ l' ∈ c₁, LiteralEquiv l l' := by
        apply h_equiv.h_mpr.h_subset l
        assumption
      obtain ⟨l', h_l'⟩ := this
      have := h_l'.right.h_equiv
      aesop
    · exact Literal.variable_mem_vars l

  let c₂' := (c₂.convert sub_vars h_sub₂)
  let ρ₂' := (ρ₂.restrict sub_vars Finset.inter_subset_right)

  have h_c₂_eq : c₂.eval ρ₂ = c₂'.eval ρ₂' := by
    rw [Clause.convert_eval]

  have : c₁' = c₂' := by
    refine (Clause.equiv_equiv c₁' c₂').mp ?_
    have h₁ : ClauseEquiv c₁ c₁' := by
      unfold c₁'
      apply Clause.equiv_sym
      exact Clause.convert_equiv c₁
    have h₂ : ClauseEquiv c₂' c₂ := by
      unfold c₂'
      apply Clause.equiv_sym
      apply Clause.equiv_sym
      exact Clause.convert_equiv c₂
    apply Clause.equiv_trans c₁' c₁ c₂'
    · apply Clause.equiv_sym
      assumption
    · apply Clause.equiv_trans c₁ c₂ c₂'
      · assumption
      · apply Clause.equiv_sym
        assumption

  rw [h_c₁_eq]
  rw [h_c₂_eq]
  rw [←this]

  suffices h: ρ₁' = ρ₂' by
    rw [h]
  rw [←Assignment.agree_iff_eq]
  constructor
  simp only [Finset.inter_self]
  intro v h_v _ _
  unfold ρ₁'
  unfold ρ₂'
  unfold Assignment.restrict
  (expose_names;
    exact
      Agree.h_agree v h_v ((fun v a ↦ Finset.inter_subset_left a) v h₁)
        ((fun v a ↦ Finset.inter_subset_right a) v h₂))

@[simp]
lemma Clause.convert_trivial_subset {vars₁ : Variables} (c₁ : Clause vars₁) (c₂ : Clause vars₁)
    (vars₂ : Variables) {h} : c₁ ⊆ c₂ → c₁.convert_trivial vars₂ h ⊆ c₂.convert_trivial vars₂ h
    := by
  unfold convert_trivial
  aesop

@[simp]
lemma Clause.convert_trivial_subset_insert {vars₁ : Variables} (c₁ : Clause vars₁)
    (c₂ : Clause vars₁) (vars₂ : Variables) (l : Literal vars₂) {h} :
    c₁ ⊆ insert (l.convert vars₁ (by aesop)) c₂ →
    c₁.convert_trivial vars₂ h ⊆ insert l (c₂.convert_trivial vars₂ h) := by
  unfold convert_trivial
  aesop

lemma Clause.convert_maintains_subset_insert {vars₁ : Variables} (c₁ : Clause vars₁)
    (c₂ : Clause vars₁) (vars₂ : Variables) (l : Literal vars₂) (h : l.variable ∈ vars₁) {h₁} {h₂} :
    c₁ ⊆ insert (l.convert vars₁ h) c₂ →
    c₁.convert vars₂ h₁ ⊆ insert l (c₂.convert vars₂ h₂) := by
  intro h_c
  sorry

def Clause.combine {vars₁} {vars₂} (c₁ : Clause vars₁) (c₂ : Clause vars₂)
    (h : Disjoint vars₁ vars₂) : Clause (vars₁.disjUnion vars₂ h) :=
    let vars := (vars₁.disjUnion vars₂ h)
    let c₁' := c₁.convert vars (by aesop)
    let c₂' := c₂.convert vars (by aesop)

    c₁' ∪ c₂'

lemma Clause.substitute_combine {vars} {sub_vars} (c : Clause vars) (ρ : Assignment sub_vars)
    (h_subset : sub_vars ⊆ vars) (h : (c.substitute ρ).isSome)
: c ⊆ (Clause.combine ((c.substitute ρ).get h)
                       ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop) := by
  sorry
