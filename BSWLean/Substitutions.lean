import BSWLean.CNF

def Literal.restrict {vars} (l : Literal vars)
    (sub_vars : Variables) (h_mem : l.variable ∈ sub_vars)
    : Literal sub_vars :=
  match l with
  | .pos v _ => Literal.pos v h_mem
  | .neg v _ => Literal.neg v h_mem

def Clause.shrink {vars} (c : Clause vars)
    (keep_vars : Variables) (h_mem : ∀ l, l ∈ c → l.variable ∈ keep_vars)
    : Clause keep_vars :=
  sorry

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

def Clause.substitute {vars} (c : Clause vars)
    (sub_vars : Variables) (ρ : Assignment sub_vars)
    : Option (Clause (vars \ sub_vars)) :=
  let (c_in, c_out) := Clause.split c sub_vars

  if c_in.eval (ρ.restrict (vars ∩ sub_vars) Finset.inter_subset_right) then
    none
  else
    some c_out

lemma Clause.substitute_eq_none_iff_eval_subclause_true {vars} (c : Clause vars)
    (sub_vars : Variables) (ρ : Assignment sub_vars)
: c.substitute sub_vars ρ = none ↔
  (c.split sub_vars).1.eval (ρ.restrict (vars ∩ sub_vars) Finset.inter_subset_right) := by
  unfold Clause.substitute
  constructor
  case mp =>
    simp_all only [ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false,
      implies_true]
  case mpr =>
    simp_all only [↓reduceIte, implies_true]

@[simp]
lemma Assignment.restrict_correctness {vars} {h} (ρ : Assignment vars)
    : ρ.restrict vars h = ρ := by
  rfl

lemma Clause.split_correctness {vars} (c : Clause vars)
    (sub_vars : Variables) (ρ : Assignment vars) (h₁) (h₂) :
    c.eval ρ = (c.split sub_vars).1.eval (ρ.restrict (vars ∩ sub_vars) h₁)
            || (c.split sub_vars).2.eval (ρ.restrict (vars \ sub_vars) h₂) := by
  sorry


def CNFFormula.substitute {vars} (φ : CNFFormula vars)
    (sub_vars : Variables) (ρ : Assignment sub_vars)
    : CNFFormula (vars \ sub_vars) :=
  let f := fun c : Clause vars => c.substitute sub_vars ρ

  let φ' := (φ.image f).filterMap id

  φ' (by exact fun a a' b a_1 a_2 ↦ Option.eq_of_mem_of_mem a_1 a_2)

class Agree {vars₁} {vars₂} (ρ₁ : Assignment vars₁) (ρ₂ : Assignment vars₂) : Prop where
  h_agree : ∀ v ∈ vars₁ ∩ vars₂, ∀ h₁ h₂, (ρ₁ v h₁) = (ρ₂ v h₂)
