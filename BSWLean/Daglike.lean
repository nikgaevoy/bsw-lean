import BSWLean.CNF
import BSWLean.Conversion
import BSWLean.Substitutions
import BSWLean.SuperCNF
import BSWLean.Treelike

abbrev Blackboard (vars : Variables) := CNFFormula vars

inductive DagLikeResolutionStep {vars} (φ : CNFFormula vars) : Blackboard vars → Type
  | axioms : DagLikeResolutionStep φ φ
  | resolve
      {b : Blackboard vars}
      (π : DagLikeResolutionStep φ b)
      (c c₁ c₂ : Clause vars) (v : Variable)
      (h_v_mem_vars : v ∈ vars)
      (h_v_not_mem_c : v ∉ c.variables)
      (h₁ : c₁ ∈ b)
      (h₂ : c₂ ∈ b)
      (h_resolve : (c₁ ⊆ c ∪ { v.toLiteral h_v_mem_vars }) ∧
                   (c₂ ⊆ c ∪ { v.toNegLiteral h_v_mem_vars }))
      : DagLikeResolutionStep φ (insert c b)

@[aesop safe [constructors, cases]]
inductive DagLikeResolution {vars} (φ : CNFFormula vars) : Clause vars → Type
  | intro {c}
      (b : Blackboard vars)
      (π : DagLikeResolutionStep φ b)
      (h_c_in_b : c ∈ b)
      : DagLikeResolution φ c

abbrev DagLikeRefutation {vars} (φ : CNFFormula vars) :=
  DagLikeResolution φ (BotClause vars)

def DagLikeResolutionStep.size {vars} {φ : CNFFormula vars}
    {b : Blackboard vars} (π : DagLikeResolutionStep φ b) : Nat :=
  match π with
  | .axioms => 0
  | .resolve π' _ _ _ _ _ _ _ _ _ =>
    1 + DagLikeResolutionStep.size π'

@[aesop safe]
def DagLikeResolution.size {vars} {φ : CNFFormula vars}
    {c : Clause vars} (π : DagLikeResolution φ c) : Nat :=
  match π with
  | .intro _ π' _ => π'.size

@[aesop safe]
def DagLikeResolution.Blackboard {vars} {φ : CNFFormula vars}
    {c : Clause vars} (π : DagLikeResolution φ c) : Blackboard vars :=
  match π with
  | .intro b _ _ => b

@[aesop safe]
def DagLikeResolution.toStep {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : DagLikeResolution φ c) : DagLikeResolutionStep φ (DagLikeResolution.Blackboard π) :=
  match π with
  | .intro _ π' _ => π'

def DagLikeResolutionStep.blackboard {vars} {φ : CNFFormula vars}
    {b : Blackboard vars} (_ : DagLikeResolutionStep φ b) : Blackboard vars :=
  b

@[aesop unsafe]
lemma DagLikeResolutionStep.size_leq_blackboard_card {vars} {φ : CNFFormula vars}
      {b : Blackboard vars} (π : DagLikeResolutionStep φ b) :
    π.blackboard.card ≤ π.size + φ.card := by
    induction π
    case axioms =>
      simp [DagLikeResolutionStep.size, DagLikeResolutionStep.blackboard]
    case resolve _ π' _ _ _ _ _ _ _ _ _ ih =>
      simp [DagLikeResolutionStep.size, DagLikeResolutionStep.blackboard]
      trans Finset.card π'.blackboard + 1
      · unfold blackboard
        apply Finset.card_insert_le
      · omega

lemma DagLikeResolution.exists_blackboard_size_proof {vars} {φ : CNFFormula vars} {b}
    (π : DagLikeResolutionStep φ b) :
    ∃ π' : DagLikeResolutionStep φ b, π'.blackboard.card = π'.size + φ.card := by
  induction π
  case axioms =>
    use DagLikeResolutionStep.axioms
    unfold DagLikeResolutionStep.size DagLikeResolutionStep.blackboard
    simp
  case resolve b _ c c₁ c₂ v h_v_mem_vars h_in h₁ h₂ h_resolve ih =>
    if h_trivial : c ∈ b then
      have : insert c b = b := by
        rw [Finset.insert_eq_of_mem h_trivial]
      rw [this]
      assumption
    else
      obtain ⟨π', h_eq⟩ := ih
      use DagLikeResolutionStep.resolve π' c c₁ c₂ v h_v_mem_vars h_in h₁ h₂ h_resolve
      unfold DagLikeResolutionStep.size DagLikeResolutionStep.blackboard
      rw [Finset.card_insert_of_notMem h_trivial]
      unfold DagLikeResolutionStep.blackboard at h_eq
      grind

@[aesop unsafe]
lemma DagLikeResolutionStep.blackboard_subset {vars} {φ : CNFFormula vars}
    {b : Blackboard vars} (π : DagLikeResolutionStep φ b) : φ ⊆ b := by
  induction π
  case axioms =>
    rfl
  case resolve =>
    grind

lemma DagLikeResolutionStep.concat {vars} {φ : CNFFormula vars}
    {b₁ b₂ : Blackboard vars} (π₁ : DagLikeResolutionStep φ b₁) (π₂ : DagLikeResolutionStep φ b₂) :
    ∃ (π : DagLikeResolutionStep φ (b₁ ∪ b₂)), π.size = π₁.size + π₂.size := by
  induction π₂
  case axioms =>
    have : b₁ ∪ φ = b₁ := by
      rw [Finset.union_eq_left.mpr (DagLikeResolutionStep.blackboard_subset π₁)]
    rw [this]
    use π₁
    simp [DagLikeResolutionStep.size]
  case resolve b₂' π₂' c c₁ c₂ v h_v_mem_vars h_in h₁ h₂ h_resolve ih =>
    obtain ⟨π, h_size⟩ := ih
    let q := DagLikeResolutionStep.resolve π c c₁ c₂ v h_v_mem_vars
        h_in (by aesop) (by aesop) h_resolve
    have : insert c (b₁ ∪ b₂') = (b₁ ∪ insert c b₂') := by aesop
    rw [←this]
    use q
    unfold q
    simp [DagLikeResolutionStep.size]
    omega

def TreeLikeResolution.toBlackboard {vars} {φ : CNFFormula vars}
    {c : Clause vars} (π : TreeLikeResolution φ c) : Blackboard vars :=
  match π with
  | .axiom_clause _ => φ
  | .resolve _ _ _ _ _ π₁ π₂ _ => insert c (π₁.toBlackboard ∪ π₂.toBlackboard)

lemma TreeLikeResolution.toBlackboard_subset {vars} {φ : CNFFormula vars}
    {c : Clause vars} (π : TreeLikeResolution φ c) : c ∈ π.toBlackboard := by
  unfold TreeLikeResolution.toBlackboard
  induction π
  case axiom_clause h =>
    grind
  case resolve =>
    grind

noncomputable def TreeLikeResolution.toDagLike {vars} {c : Clause vars} {φ : CNFFormula vars}
    (π : TreeLikeResolution φ c) : ∃ π_dag : DagLikeResolution φ c, π_dag.size ≤ π.size := by
  induction π
  case axiom_clause c h =>
    use DagLikeResolution.intro φ (DagLikeResolutionStep.axioms) h
    simp [TreeLikeResolution.size, DagLikeResolution.size, DagLikeResolutionStep.size]
  case resolve c c₁ c₂ x h_x_in h_x_out π₁ π₂ h ih₁ ih₂ =>
    obtain ⟨π_dag₁, h_size₁⟩ := ih₁
    obtain ⟨π_dag₂, h_size₂⟩ := ih₂
    obtain ⟨π_resolve_step, h_size_resolve⟩ :=
      (DagLikeResolutionStep.concat π_dag₁.toStep π_dag₂.toStep)
    let π_resolve :=
      DagLikeResolutionStep.resolve π_resolve_step c c₁ c₂ x (by aesop)
        (by aesop) (by aesop) (by aesop) (by aesop)
    use DagLikeResolution.intro π_resolve.blackboard π_resolve
        (by unfold DagLikeResolutionStep.blackboard; aesop)
    unfold DagLikeResolution.size π_resolve TreeLikeResolution.size DagLikeResolutionStep.size
    simp only
    rw [h_size_resolve]
    unfold DagLikeResolution.toStep
    simp only
    unfold DagLikeResolution.size at h_size₁ h_size₂
    simp only at h_size₁ h_size₂
    omega

theorem DagLikeRefutation.completeness {vars} {φ : CNFFormula vars}
    (h_unsat : Unsat φ) : ∃ π : DagLikeRefutation φ, π.size ≤ 2 * 2 ^ vars.card - 1 := by
  obtain ⟨π_tree, h_refutes⟩ := unsat_implies_tree_like_refutation h_unsat
  obtain ⟨π_dag, h_size⟩ := TreeLikeResolution.toDagLike π_tree
  use π_dag
  trans π_tree.size
  all_goals assumption

def DagLikeResolutionStep.toTreeLike {vars} {φ : CNFFormula vars} {b : Blackboard vars}
    (π : DagLikeResolutionStep φ b) (c : Clause vars) (h_c_in_b : c ∈ b) :
    TreeLikeResolution φ c :=
  match π with
  | .axioms =>
    TreeLikeResolution.axiom_clause h_c_in_b
  | .resolve π' c' c₁ c₂ v h_v_mem_vars h_v_not_mem_c h₁ h₂ h_resolve =>
    if h : c = c' then
      let left_subproof := π'.toTreeLike c₁ h₁
      let right_subproof := π'.toTreeLike c₂ h₂
      TreeLikeResolution.resolve c₁ c₂ v h_v_mem_vars (by aesop)
          left_subproof right_subproof (by aesop)
    else
      π'.toTreeLike c (by aesop)

theorem DagLikeRefutation.correctness {vars} {φ : CNFFormula vars} (π : DagLikeRefutation φ) :
    Unsat φ := by
  let π' := π.toStep.toTreeLike (BotClause vars) (by aesop)
  exact tree_like_refutation_implies_unsat π'
