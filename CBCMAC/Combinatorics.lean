import Probability.Counting
import Mathlib.Data.List.GetD

/-!
# Carrier-independent CBC combinatorics

The proof of CR18, Theorem 6.1 (printed pp. 126--127), uses prefix-freeness to
exclude trivial round-input collisions and applies Lemma 4.18.

This module formalizes the algebraic CBC fold, the distinct-input condition,
the shift action on good functions, finite fibre counting, and the scalar
collision budget. These statements depend only on finite algebra and
probability counting.
-/

namespace CBCMAC.CBCCombinatorics

open Classical
open Probability

universe u

variable {X M : Type u}

/-- Digest a block sequence using the CBC recurrence of CR18, Section 6.2.3,
with public initial state zero. -/
def cbc [Zero X] [Add X] (f : X → X) (blocks : List X) : X :=
  blocks.foldl (fun chaining block => f (chaining + block)) 0

@[simp]
lemma cbc_append [Zero X] [Add X]
    (f : X → X) (blocks : List X) (block : X) :
    cbc f (blocks ++ [block]) = f (cbc f blocks + block) := by
  -- Appending one block performs one further feedback-function call.
  simp [cbc]

/-- The canonical uniform block bound when the message alphabet is finite. -/
noncomputable def blockBound [Fintype M] (blockForm : M → List X) : Nat :=
  Finset.univ.sup fun message => (blockForm message).length

lemma length_le_blockBound [Fintype M] (blockForm : M → List X)
    (message : M) :
    (blockForm message).length ≤ blockBound blockForm := by
  classical
  -- The message length is one term in the finite supremum.
  exact Finset.le_sup
    (f := fun candidate : M => (blockForm candidate).length)
    (Finset.mem_univ message)

/-- Prefix-freeness forces every encoding to be nonempty when the message
alphabet has at least two elements. -/
lemma blockForm_ne_nil_of_prefixFree [Nontrivial M]
    {blockForm : M → List X}
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (message : M) :
    blockForm message ≠ [] := by
  -- An empty encoding would be a prefix of a different message's encoding.
  intro empty
  obtain ⟨other, different⟩ := exists_ne message
  exact prefixFree message other different.symm
    (by rw [empty]; exact List.nil_prefix)

/-- The total number of encoded blocks in a finite message history. -/
def totalBlocks (blockForm : M → List X) (messages : List M) : Nat :=
  (messages.map fun message => (blockForm message).length).sum

lemma totalBlocks_mono (blockForm : M → List X)
    {initial final : List M} (isPrefix : initial <+: final) :
    totalBlocks blockForm initial ≤ totalBlocks blockForm final := by
  -- Split the final history into the initial prefix and its suffix.
  obtain ⟨suffix, rfl⟩ := isPrefix
  simp [totalBlocks, List.map_append]

/-- The input made to the round function at one block position. -/
def cbcInput [Zero X] [Add X] (f : X → X) (blocks : List X)
    (position : Nat) : X :=
  cbc f (blocks.take position) + blocks.getD position 0

/-! ## CR18 collision condition and counting -/

section SecurityCore

section CollisionGeometry

variable [Zero X] [Add X]

/-- A nontrivial collision between distinct CBC call sites, as in the proof of
CR18, Theorem 6.1. Shared encoded prefixes denote one call site and are
excluded. -/
def cbcBad (f : X → X) (blockForm : M → List X)
    (messages : List M) : Prop :=
  ∃ message ∈ messages, ∃ other ∈ messages,
    ∃ position < (blockForm message).length,
      ∃ otherPosition < (blockForm other).length,
        (blockForm message).take (position + 1) ≠
            (blockForm other).take (otherPosition + 1) ∧
          cbcInput f (blockForm message) position =
            cbcInput f (blockForm other) otherPosition

instance [DecidableEq M] [DecidableEq X]
    (f : X → X) (blockForm : M → List X) (messages : List M) :
    Decidable (cbcBad f blockForm messages) := by
  unfold cbcBad
  infer_instance

lemma cbcBad_monotone (f : X → X) (blockForm : M → List X)
    {initial final : List M} (isPrefix : initial <+: final)
    (bad : cbcBad f blockForm initial) : cbcBad f blockForm final := by
  -- Reuse the two colliding call sites under prefix inclusion.
  obtain ⟨message, member, other, otherMember, position, positionBound,
    otherPosition, otherPositionBound, different, equal⟩ := bad
  exact ⟨message, isPrefix.subset member, other, isPrefix.subset otherMember,
    position, positionBound, otherPosition, otherPositionBound, different, equal⟩

lemma cbcInput_append_of_lt (f : X → X) (blocks : List X) (block : X)
    {position : Nat} (bound : position < blocks.length) :
    cbcInput f (blocks ++ [block]) position = cbcInput f blocks position := by
  -- Earlier call sites depend only on the unchanged prefix.
  unfold cbcInput
  rw [List.take_append_of_le_length (Nat.le_of_lt bound),
    List.getD_append blocks [block] 0 position bound]

lemma cbcInput_append_length (f : X → X) (blocks : List X) (block : X) :
    cbcInput f (blocks ++ [block]) blocks.length = cbc f blocks + block := by
  -- The new last call uses the previous state and appended block.
  unfold cbcInput
  rw [List.take_left,
    List.getD_append_right blocks [block] 0 blocks.length (le_refl _)]
  simp

lemma cbc_eq_apply_lastInput (f : X → X) (blocks : List X)
    (nonempty : blocks ≠ []) :
    cbc f blocks = f (cbcInput f blocks (blocks.length - 1)) := by
  -- Decompose a nonempty list into its initial segment and final block.
  rcases blocks.eq_nil_or_concat with empty | ⟨initial, block, rfl⟩
  · exact absurd empty nonempty
  · rw [List.concat_eq_append, cbc_append]
    -- The last call position is the length of the initial segment.
    congr 1
    have length : (initial ++ [block]).length - 1 = initial.length := by simp
    rw [length, cbcInput_append_length]

lemma not_cbcBad_inputs_ne (f : X → X) (blockForm : M → List X)
    {messages : List M} (good : ¬ cbcBad f blockForm messages)
    {message other : M} (member : message ∈ messages)
    (otherMember : other ∈ messages) {position otherPosition : Nat}
    (positionBound : position < (blockForm message).length)
    (otherPositionBound : otherPosition < (blockForm other).length)
    (different : (blockForm message).take (position + 1) ≠
      (blockForm other).take (otherPosition + 1)) :
    cbcInput f (blockForm message) position ≠
      cbcInput f (blockForm other) otherPosition :=
  -- Equality of the two distinct call sites would witness the bad event.
  fun equal => good ⟨message, member, other, otherMember, position,
    positionBound, otherPosition, otherPositionBound, different, equal⟩

lemma cbc_congr_of_agree_on_inputs (f g : X → X)
    (blocks : List X)
    (agree : ∀ position < blocks.length,
      f (cbcInput f blocks position) = g (cbcInput f blocks position)) :
    cbc f blocks = cbc g blocks := by
  -- Induct over successive final blocks of the CBC fold.
  induction blocks using List.reverseRecOn with
  | nil => rfl
  | append_singleton initial block inductionHypothesis =>
      rw [cbc_append, cbc_append]
      have earlier : ∀ position < initial.length,
          f (cbcInput f initial position) =
            g (cbcInput f initial position) := by
        -- Agreement on the extended list restricts to every earlier call site.
        intro position bound
        have extended : position < (initial ++ [block]).length := by
          -- Appending a block preserves every earlier valid position.
          simp
          omega
        simpa [cbcInput_append_of_lt f initial block bound] using
          agree position extended
      have stateEqual := inductionHypothesis earlier
      -- Use agreement at the final call after identifying the prior states.
      have last := agree initial.length (by simp)
      rw [cbcInput_append_length] at last
      rw [last, stateEqual]

def cbcLastInput (f : X → X) (blockForm : M → List X)
    (message : M) : X :=
  cbcInput f (blockForm message) ((blockForm message).length - 1)

omit [Zero X] [Add X] in
lemma take_last_key {blocks : List X} (nonempty : blocks ≠ []) :
    blocks.take (blocks.length - 1 + 1) = blocks := by
  -- Nonemptiness turns the predecessor-successor length back into the full length.
  rw [Nat.sub_add_cancel (List.length_pos_of_ne_nil nonempty)]
  exact List.take_length

def cbcFresh (f : X → X) (blockForm : M → List X)
    (messages : List M) : Prop :=
  ∀ message ∈ messages, ∀ other ∈ messages,
    ∀ position < (blockForm other).length,
      blockForm message ≠ (blockForm other).take (position + 1) →
        cbcLastInput f blockForm message ≠
          cbcInput f (blockForm other) position

lemma cbcFresh_of_not_cbcBad (f : X → X) (blockForm : M → List X)
    {messages : List M} (nonempty : ∀ message, blockForm message ≠ [])
    (good : ¬ cbcBad f blockForm messages) :
    cbcFresh f blockForm messages := by
  -- Instantiate the good-event distinctness property at a terminal call site.
  intro message member other otherMember position positionBound different
  refine not_cbcBad_inputs_ne f blockForm good member otherMember
    (by have := List.length_pos_of_ne_nil (nonempty message); omega)
    positionBound ?_
  rw [take_last_key (nonempty message)]
  exact different

lemma cbcLastInput_injOn (f : X → X) (blockForm : M → List X)
    {messages : List M} (nonempty : ∀ message, blockForm message ≠ [])
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (fresh : cbcFresh f blockForm messages) :
    Set.InjOn (cbcLastInput f blockForm) {message | message ∈ messages} := by
  -- Equal terminal inputs of distinct messages contradict freshness and prefix-freeness.
  intro message member other otherMember equal
  by_contra differentMessages
  have differentKeys : blockForm message ≠
      (blockForm other).take ((blockForm other).length - 1 + 1) := by
    -- A shared complete encoding would make one distinct message a prefix of the other.
    rw [take_last_key (nonempty other)]
    exact fun equalEncoding =>
      prefixFree message other differentMessages
        (equalEncoding ▸ List.prefix_refl (blockForm message))
  exact fresh message member other otherMember _
    (by have := List.length_pos_of_ne_nil (nonempty other); omega)
    differentKeys equal

lemma cbcInput_take_of_lt (f : X → X) (blocks : List X)
    {position limit : Nat} (bound : position < limit) :
    cbcInput f (blocks.take limit) position = cbcInput f blocks position := by
  -- A call below the truncation point sees the same state prefix and block.
  unfold cbcInput
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  congr 1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt bound]

lemma cbcInput_congr_of_agree_below (f g : X → X) (blocks : List X)
    {position : Nat}
    (agree : ∀ prior < position,
      g (cbcInput f blocks prior) = f (cbcInput f blocks prior)) :
    cbcInput g blocks position = cbcInput f blocks position := by
  -- The state before this call agrees because all earlier function answers agree.
  unfold cbcInput
  congr 1
  refine (cbc_congr_of_agree_on_inputs f g (blocks.take position) ?_).symm
  intro prior lengthBound
  -- Translate a position in the taken prefix to a position below the target call.
  have bound : prior < position := by
    rw [List.length_take] at lengthBound
    omega
  rw [cbcInput_take_of_lt f blocks bound]
  exact (agree prior bound).symm

lemma cbcInput_ne_lastInput (f : X → X) (blockForm : M → List X)
    {messages : List M}
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (fresh : cbcFresh f blockForm messages)
    {message : M} (member : message ∈ messages) {position : Nat}
    (proper : position + 1 < (blockForm message).length)
    {terminal : M} (terminalMember : terminal ∈ messages) :
    cbcInput f (blockForm message) position ≠
      cbcLastInput f blockForm terminal := by
  -- A proper prefix cannot equal the terminal encoding under prefix-freeness.
  have different : blockForm terminal ≠
      (blockForm message).take (position + 1) := by
    -- Equality would exhibit the terminal encoding as a prefix.
    intro equal
    have encodingPrefix : blockForm terminal <+: blockForm message :=
      equal ▸ List.take_prefix (position + 1) (blockForm message)
    by_cases same : terminal = message
    -- Equal messages contradict the strict proper-prefix length.
    · subst same
      have lengths := congrArg List.length equal
      rw [List.length_take] at lengths
      omega
    -- Distinct messages contradict prefix-freeness directly.
    · exact prefixFree terminal message same encodingPrefix
  -- Freshness separates the proper call site from the terminal one.
  exact (fresh terminal terminalMember message member position
    (by omega) different).symm

end CollisionGeometry

section Shifts

variable [AddCommGroup X] [DecidableEq M] [DecidableEq X]

noncomputable def cbcShift (f : X → X) (blockForm : M → List X)
    (messages : List M) (delta : ↑messages.toFinset → X) : X → X :=
  Counting.multiShift
    (fun message : ↑messages.toFinset => cbcLastInput f blockForm message.1)
    delta f

lemma cbcShift_eq_of_not_terminal (f : X → X)
    (blockForm : M → List X) (messages : List M)
    (delta : ↑messages.toFinset → X) {input : X}
    (different : ∀ message ∈ messages.toFinset,
      cbcLastInput f blockForm message ≠ input) :
    cbcShift f blockForm messages delta input = f input :=
  -- The multi-shift changes only the designated terminal inputs.
  Counting.multiShift_apply_of_ne delta f fun message =>
    different message.1 message.2

lemma cbcShift_lastInput (f : X → X) (blockForm : M → List X)
    (messages : List M) (delta : ↑messages.toFinset → X)
    (injective : Set.InjOn (cbcLastInput f blockForm)
      {message | message ∈ messages}) (message : ↑messages.toFinset) :
    cbcShift f blockForm messages delta (cbcLastInput f blockForm message.1) =
      f (cbcLastInput f blockForm message.1) + delta message :=
  -- Injectivity of terminal sites lets the multi-shift select this unique coordinate.
  Counting.multiShift_apply_site delta f
    (fun left right equal => Subtype.ext
      (injective (List.mem_toFinset.mp left.2)
        (List.mem_toFinset.mp right.2) equal)) message

lemma cbcInput_cbcShift (f : X → X) (blockForm : M → List X)
    {messages : List M} (delta : ↑messages.toFinset → X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (fresh : cbcFresh f blockForm messages)
    {message : M} (member : message ∈ messages) {position : Nat}
    (bound : position < (blockForm message).length) :
    cbcInput (cbcShift f blockForm messages delta) (blockForm message) position =
      cbcInput f (blockForm message) position := by
  -- Inductively, all earlier call inputs avoid the terminal shift sites.
  refine cbcInput_congr_of_agree_below f _ (blockForm message) fun prior lower => ?_
  refine cbcShift_eq_of_not_terminal f blockForm messages delta fun terminal ht => ?_
  exact (cbcInput_ne_lastInput f blockForm prefixFree fresh member
    (by omega) (List.mem_toFinset.mp ht)).symm

lemma not_cbcBad_cbcShift (f : X → X) (blockForm : M → List X)
    {messages : List M} (delta : ↑messages.toFinset → X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (nonempty : ∀ message, blockForm message ≠ [])
    (good : ¬ cbcBad f blockForm messages) :
    ¬ cbcBad (cbcShift f blockForm messages delta) blockForm messages := by
  -- Goodness supplies freshness of all terminal inputs.
  have fresh := cbcFresh_of_not_cbcBad f blockForm nonempty good
  -- A shifted collision reduces to the same collision before shifting.
  rintro ⟨message, member, other, otherMember, position, positionBound,
    otherPosition, otherPositionBound, different, equal⟩
  rw [cbcInput_cbcShift f blockForm delta prefixFree fresh member positionBound,
    cbcInput_cbcShift f blockForm delta prefixFree fresh otherMember
      otherPositionBound] at equal
  exact good ⟨message, member, other, otherMember, position, positionBound,
    otherPosition, otherPositionBound, different, equal⟩

lemma cbc_cbcShift (f : X → X) (blockForm : M → List X)
    {messages : List M} (delta : ↑messages.toFinset → X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (nonempty : ∀ message, blockForm message ≠ [])
    (fresh : cbcFresh f blockForm messages) {message : M}
    (member : message ∈ messages.toFinset) :
    cbc (cbcShift f blockForm messages delta) (blockForm message) =
      cbc f (blockForm message) + delta ⟨message, member⟩ := by
  -- Good terminal inputs are distinct, so the shift at this message is isolated.
  have injective := cbcLastInput_injOn f blockForm nonempty prefixFree fresh
  have listMember : message ∈ messages := List.mem_toFinset.mp member
  have shifted := cbcShift_lastInput f blockForm messages delta injective
    ⟨message, member⟩
  -- Earlier CBC inputs are unchanged and the final function answer receives the shift.
  rw [cbc_eq_apply_lastInput _ _ (nonempty message),
    cbcInput_cbcShift f blockForm delta prefixFree fresh listMember
      (by have := List.length_pos_of_ne_nil (nonempty message); omega),
    show cbcInput f (blockForm message) ((blockForm message).length - 1) =
      cbcLastInput f blockForm message from rfl, shifted]
  congr 1
  -- Reidentify the unshifted final function answer with the CBC state.
  exact (cbc_eq_apply_lastInput f _ (nonempty message)).symm

lemma cbcShift_zero (f : X → X) (blockForm : M → List X)
    (messages : List M) : cbcShift f blockForm messages 0 = f :=
  -- Zero displacement leaves every function value unchanged.
  Counting.multiShift_zero _ f

lemma cbcShift_cbcShift (f : X → X) (blockForm : M → List X)
    {messages : List M} (first second : ↑messages.toFinset → X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (nonempty : ∀ message, blockForm message ≠ [])
    (fresh : cbcFresh f blockForm messages) :
    cbcShift (cbcShift f blockForm messages first) blockForm messages second =
      cbcShift f blockForm messages (first + second) := by
  -- The first shift leaves all terminal call-site inputs unchanged.
  have sites :
      (fun message : ↑messages.toFinset =>
        cbcLastInput (cbcShift f blockForm messages first) blockForm message.1) =
      fun message => cbcLastInput f blockForm message.1 :=
    funext fun message =>
      cbcInput_cbcShift f blockForm first prefixFree fresh
        (List.mem_toFinset.mp message.2)
        (by have := List.length_pos_of_ne_nil (nonempty message.1); omega)
  show Counting.multiShift _ second (cbcShift f blockForm messages first) = _
  rw [sites]
  -- Successive shifts at fixed sites add their displacements.
  exact Counting.multiShift_multiShift _ first second f

end Shifts

section UniformFibers

variable [AddCommGroup X] [Fintype M] [DecidableEq M]
  [Fintype X] [DecidableEq X] [Nonempty X]

namespace Security

omit [Nonempty X] in
lemma cbc_fiber_card (blockForm : M → List X) {messages : List M}
    (nonempty : ∀ message, blockForm message ≠ [])
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (Good : (X → X) → Prop)
    [DecidablePred Good]
    (fresh : ∀ f, Good f → cbcFresh f blockForm messages)
    (shiftClosed : ∀ (delta : ↑messages.toFinset → X) f,
      Good f → Good (cbcShift f blockForm messages delta))
    (answers : ↑messages.toFinset → X) :
    (Finset.univ.filter (fun f : X → X =>
        (∀ message : ↑messages.toFinset,
          cbc f (blockForm message.1) = answers message) ∧ Good f)).card *
        Fintype.card X ^ messages.toFinset.card =
      (Finset.univ.filter Good).card := by
  classical
  -- Apply the free transitive shift-action counting theorem to the CBC outputs.
  have key := Counting.card_filter_shift_univ
    (A := ↑messages.toFinset → X) Good
    (fun f message => cbc f (blockForm message.1))
    (fun delta f => cbcShift f blockForm messages delta)
    (fun delta f good => shiftClosed delta f good)
    (fun delta f good => funext fun message => by
      change cbc (cbcShift f blockForm messages delta)
          (blockForm message.1) =
        cbc f (blockForm message.1) + delta message
      rw [cbc_cbcShift f blockForm delta prefixFree nonempty
        (fresh f good) message.2])
    (fun first second f good =>
      cbcShift_cbcShift f blockForm first second prefixFree nonempty
        (fresh f good))
    (fun f _ => cbcShift_zero f blockForm messages) answers
  -- Rewrite the displacement-space cardinality as one alphabet factor per message.
  rw [Fintype.card_fun, Fintype.card_coe] at key
  rw [← key]
  congr 2
  ext f
  simp [funext_iff, and_comm]

end Security

/-- Outside the collision condition, CBC's transcript law is uniform. This is
the finite-law form of CR18, Equation (6.2). -/
lemma mass_cbc_outputs_and_not_cbcBad_eq [Nontrivial M]
    (blockForm : M → List X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (messages : List M) (answers : ↑messages.toFinset → X) :
    (Distribution.uniform (X → X)).mass (fun f =>
        (∀ message : ↑messages.toFinset,
          cbc f (blockForm message.1) = answers message) ∧
          ¬ cbcBad f blockForm messages) =
      (Distribution.uniform (M → X)).mass (fun g =>
        ∀ message : ↑messages.toFinset, g message.1 = answers message) *
      (Distribution.uniform (X → X)).mass
        (fun f => ¬ cbcBad f blockForm messages) := by
  classical
  let Good : (X → X) → Prop := fun f => ¬ cbcBad f blockForm messages
  -- Convert equal good fibres into factorization of the two uniform masses.
  apply Distribution.uniform_mass_eq_mass_mul_mass_of_card_mul_eq
  -- Prefix-freeness provides nonempty encodings and freshness outside the bad event.
  have nonempty : ∀ message, blockForm message ≠ [] :=
    blockForm_ne_nil_of_prefixFree prefixFree
  have fiber := Security.cbc_fiber_card blockForm nonempty prefixFree Good
    (fun f good => cbcFresh_of_not_cbcBad f blockForm nonempty good)
    (fun delta f good =>
      not_cbcBad_cbcShift f blockForm delta prefixFree nonempty good) answers
  have cardBound : messages.toFinset.card ≤ Fintype.card M :=
    Finset.card_le_univ _
  dsimp only [Good] at fiber
  rw [Fintype.card_fun,
    Counting.card_function_fiber_finset messages.toFinset answers]
  rw [← fiber]
  -- Split the full message-function exponent into queried and unqueried messages.
  conv_lhs =>
    rw [show Fintype.card M =
      (Fintype.card M - messages.toFinset.card) + messages.toFinset.card from
        (Nat.sub_add_cancel cardBound).symm, pow_add]
  ac_rfl

/-- List-indexed form of the conditional equivalence in CR18, Equation (6.2). -/
lemma mass_cbc_outputs_and_not_cbcBad_on_list_eq [Nontrivial M]
    (blockForm : M → List X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (messages : List M) (answers : M → X) :
    (Distribution.uniform (X → X)).mass (fun f =>
        (∀ message ∈ messages,
          cbc f (blockForm message) = answers message) ∧
          ¬ cbcBad f blockForm messages) =
      (Distribution.uniform (M → X)).mass (fun g =>
        ∀ message ∈ messages, g message = answers message) *
      (Distribution.uniform (X → X)).mass
        (fun f => ¬ cbcBad f blockForm messages) := by
  -- Rewrite message-list quantification as quantification over its finite set.
  have realRewrite :
      (Distribution.uniform (X → X)).mass (fun f =>
          (∀ message ∈ messages,
            cbc f (blockForm message) = answers message) ∧
            ¬ cbcBad f blockForm messages) =
        (Distribution.uniform (X → X)).mass (fun f =>
        (∀ message : ↑messages.toFinset,
          cbc f (blockForm message.1) = answers message.1) ∧
          ¬ cbcBad f blockForm messages) := by
    -- List membership and membership in its finite set have the same elements.
    apply Distribution.mass_congr
    intro f
    apply and_congr _ Iff.rfl
    constructor
    · intro h message
      exact h message.1 (List.mem_toFinset.mp message.2)
    · intro h message member
      exact h ⟨message, List.mem_toFinset.mpr member⟩
  have idealRewrite :
      (Distribution.uniform (M → X)).mass (fun g =>
          ∀ message ∈ messages, g message = answers message) =
        (Distribution.uniform (M → X)).mass (fun g =>
          ∀ message : ↑messages.toFinset,
            g message.1 = answers message.1) := by
    -- Perform the same list-to-finset rewrite for the ideal function.
    apply Distribution.mass_congr
    intro g
    constructor
    · intro h message
      exact h message.1 (List.mem_toFinset.mp message.2)
    · intro h message member
      exact h ⟨message, List.mem_toFinset.mpr member⟩
  rw [realRewrite, idealRewrite,
    -- Apply the uniform-output factorization on the finite message set.
    mass_cbc_outputs_and_not_cbcBad_eq blockForm prefixFree messages
      (fun message => answers message.1)]

end UniformFibers

section SiteGeometry

variable [Zero X] [Add X] [DecidableEq X]

/-- The set of CBC call sites reached by a message history, represented by
nonempty encoded prefixes. -/
def cbcSites (blockForm : M → List X) (messages : List M) :
    Finset (List X) :=
  (messages.flatMap fun message =>
    (List.range (blockForm message).length).map fun position =>
      (blockForm message).take (position + 1)).toFinset

def cbcSiteBlock (site : List X) : X :=
  site.getD (site.length - 1) 0

def cbcSiteInput (f : X → X) (site : List X) : X :=
  cbcInput f site (site.length - 1)

omit [Zero X] [Add X] in
lemma mem_cbcSites {blockForm : M → List X} {messages : List M}
    {site : List X} :
    site ∈ cbcSites blockForm messages ↔
      ∃ message ∈ messages, ∃ position < (blockForm message).length,
        site = (blockForm message).take (position + 1) := by
  -- Expand membership through `flatMap`, `range`, and `toFinset`.
  simp only [cbcSites, List.mem_toFinset, List.mem_flatMap, List.mem_map,
    List.mem_range]
  constructor <;> rintro ⟨message, member, position, bound, rfl⟩ <;>
    exact ⟨message, member, position, bound, rfl⟩

omit [Zero X] [Add X] in
lemma cbcSites_ne_nil {blockForm : M → List X} {messages : List M}
    {site : List X} (member : site ∈ cbcSites blockForm messages) :
    site ≠ [] := by
  -- A reached site is a taken prefix of positive length.
  obtain ⟨message, _, position, bound, rfl⟩ := mem_cbcSites.mp member
  intro empty
  have lengthZero : ((blockForm message).take (position + 1)).length = 0 := by
    -- The assumed empty site has length zero.
    simp [empty]
  rw [List.length_take] at lengthZero
  omega

omit [Zero X] [Add X] in
lemma dropLast_mem_cbcSites {blockForm : M → List X}
    {messages : List M} {site : List X}
    (member : site ∈ cbcSites blockForm messages)
    (nonempty : site.dropLast ≠ []) :
    site.dropLast ∈ cbcSites blockForm messages := by
  -- Represent the site as a reached prefix at a positive position.
  obtain ⟨message, messageMember, position, bound, rfl⟩ :=
    mem_cbcSites.mp member
  have length : ((blockForm message).take (position + 1)).length =
      position + 1 := by rw [List.length_take]; omega
  have drop : ((blockForm message).take (position + 1)).dropLast =
      (blockForm message).take position := by
    -- Removing the last block from a positive taken prefix decrements its length.
    rw [List.dropLast_eq_take, length, List.take_take]
    congr 1
    omega
  -- The predecessor position witnesses membership of the parent prefix.
  rw [drop] at nonempty ⊢
  have positive : position ≠ 0 := by intro zero; exact nonempty (by simp [zero])
  refine mem_cbcSites.mpr ⟨message, messageMember, position - 1, by omega, ?_⟩
  congr 1
  omega

omit [Zero X] [Add X] in
lemma card_cbcSites_le (blockForm : M → List X) (messages : List M) :
    (cbcSites blockForm messages).card ≤ totalBlocks blockForm messages := by
  -- Deduplication cannot increase the length of the enumerated site list.
  refine le_trans (List.toFinset_card_le _) (le_of_eq ?_)
  simp [totalBlocks, List.length_flatMap]

omit [DecidableEq X] in
lemma cbcSiteInput_take (f : X → X) (blocks : List X)
    {position : Nat} (bound : position < blocks.length) :
    cbcSiteInput f (blocks.take (position + 1)) =
      cbcInput f blocks position := by
  -- The site prefix has exactly the length of the selected position plus one.
  have length : (blocks.take (position + 1)).length = position + 1 := by
    -- The requested prefix length is within the block list.
    rw [List.length_take]
    omega
  unfold cbcSiteInput cbcInput
  rw [length]
  have first : (blocks.take (position + 1)).take (position + 1 - 1) =
      blocks.take position := by
    -- The parent of the site is the prefix ending one position earlier.
    rw [List.take_take]
    congr 1
    omega
  -- The site's final block is the original block at the selected position.
  have second : (blocks.take (position + 1)).getD (position + 1 - 1) 0 =
      blocks.getD position 0 := by
    -- The site's final element is the selected block.
    simp only [Nat.add_sub_cancel]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take]
    simp
  rw [first, second]

omit [DecidableEq X] in
lemma cbcSiteInput_eq (f : X → X) (site : List X) :
    cbcSiteInput f site =
      cbc f site.dropLast + cbcSiteBlock site := by
  -- Separate the site into its parent prefix and final block.
  rw [cbcSiteInput, cbcInput, cbcSiteBlock, List.dropLast_eq_take]

omit [Add X] [DecidableEq X] in
lemma cbcSiteBlock_ne {left right : List X} (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ []) (different : left ≠ right)
    (sameParent : left.dropLast = right.dropLast) :
    cbcSiteBlock left ≠ cbcSiteBlock right := by
  -- A nonempty site is reconstructed from its parent and final block.
  have rebuild : ∀ (site : List X), site ≠ [] →
      site.dropLast ++ [cbcSiteBlock site] = site := by
    intro site nonempty
    have block : cbcSiteBlock site = site.getLast nonempty := by
      -- The defaulted final-block projection is exact on a nonempty site.
      rw [cbcSiteBlock, List.getLast_eq_getElem, List.getD_eq_getElem]
    rw [block]
    exact List.dropLast_append_getLast nonempty
  intro equalBlock
  -- Equal parents and equal final blocks would reconstruct equal sites.
  exact different (by
    rw [← rebuild left leftNonempty, ← rebuild right rightNonempty,
      sameParent, equalBlock])

def cbcParent (blockForm : M → List X) (messages : List M)
    (site : ↑(cbcSites blockForm messages)) :
    Option ↑(cbcSites blockForm messages) :=
  if member : site.val.dropLast ∈ cbcSites blockForm messages then
    some ⟨site.val.dropLast, member⟩
  else none

end SiteGeometry

section CollisionMass

variable [AddCommGroup X] [DecidableEq M] [Fintype X]
  [DecidableEq X] [Nonempty X]

omit [DecidableEq M] in
/-- Fixed-list collision estimate used in CR18, Theorem 6.1, via Lemma 4.18. -/
lemma mass_cbcBad_le (blockForm : M → List X) (limit : Nat)
    (messages : List M) (admitted : totalBlocks blockForm messages ≤ limit) :
    (Distribution.uniform (X → X)).mass
        (fun f => cbcBad f blockForm messages) ≤
      (limit : Real) * ((limit : Real) - 1) /
        (2 * Fintype.card X) := by
  classical
  -- Every reached call site is a nonempty encoded prefix.
  have siteNonempty : ∀ site : ↑(cbcSites blockForm messages),
      site.val ≠ [] := fun site => cbcSites_ne_nil site.2
  have parentValue : ∀ site parent : ↑(cbcSites blockForm messages),
      cbcParent blockForm messages site = some parent →
        parent.val = site.val.dropLast := by
    -- A present parent is definitionally the site's dropped-last prefix.
    intro site parent equal
    unfold cbcParent at equal
    split_ifs at equal with member
    exact congrArg Subtype.val (Option.some.inj equal).symm
  have noParent : ∀ site : ↑(cbcSites blockForm messages),
      cbcParent blockForm messages site = none → site.val.dropLast = [] := by
    -- Any nonempty dropped-last prefix would itself be a reached site.
    intro site equal
    unfold cbcParent at equal
    split_ifs at equal with member
    by_contra nonempty
    exact member (dropLast_mem_cbcSites site.2 nonempty)
  have sameParents : ∀ left right : ↑(cbcSites blockForm messages),
      cbcParent blockForm messages left = cbcParent blockForm messages right →
        left.val.dropLast = right.val.dropLast := by
    -- Equal optional parents give equal parent prefixes in both option cases.
    intro left right equal
    rcases leftParent : cbcParent blockForm messages left with _ | parent
    · rw [leftParent] at equal
      rw [noParent left leftParent, noParent right equal.symm]
    · rw [leftParent] at equal
      rw [← parentValue left parent leftParent,
        parentValue right parent equal.symm]
  have rankDecreases : ∀ site parent : ↑(cbcSites blockForm messages),
      cbcParent blockForm messages site = some parent →
        parent.val.length < site.val.length := by
    -- Dropping the final block strictly shortens every nonempty site.
    intro site parent equal
    rw [parentValue site parent equal, List.length_dropLast]
    have := List.length_pos_of_ne_nil (siteNonempty site)
    omega
  have stepInjective : ∀ site : ↑(cbcSites blockForm messages),
      Function.Injective (fun state : X => state + cbcSiteBlock site.val) :=
    -- Translation by a fixed block is injective in the additive group.
    fun _ => add_left_injective _
  have siblingsDifferent :
      ∀ left right : ↑(cbcSites blockForm messages), left ≠ right →
        cbcParent blockForm messages left = cbcParent blockForm messages right →
          ∀ state : X,
            state + cbcSiteBlock left.val ≠
              state + cbcSiteBlock right.val := by
    -- Distinct siblings have distinct final blocks, hence distinct translated states.
    intro left right different sameParent state
    have differentBlock := cbcSiteBlock_ne (siteNonempty left)
      (siteNonempty right) (fun equal => different (Subtype.ext equal))
      (sameParents left right sameParent)
    exact fun equal => differentBlock (add_left_cancel equal)
  have recursiveInput : ∀ (f : X → X)
      (site : ↑(cbcSites blockForm messages)),
      cbcSiteInput f site.val =
        ((cbcParent blockForm messages site).elim 0
          (fun parent => f (cbcSiteInput f parent.val))) +
            cbcSiteBlock site.val := by
    -- Express each site input from its parent state and final block.
    intro f site
    rw [cbcSiteInput_eq]
    congr 1
    rcases parentEq : cbcParent blockForm messages site with _ | parent
    -- A root site starts from the public zero state.
    · simp only [Option.elim]
      rw [noParent site parentEq]
      simp [cbc]
    -- A non-root site chains from the function answer at its parent input.
    · simp only [Option.elim]
      have equalParent := parentValue site parent parentEq
      rw [← equalParent]
      exact cbc_eq_apply_lastInput f parent.val (siteNonempty parent)
  have walkBound := Probability.Counting.uniform_mass_walk_repeat_le
    (cbcParent blockForm messages)
    (fun site => fun state : X => state + cbcSiteBlock site.val) (0 : X)
    (fun site => site.val.length) rankDecreases stepInjective
    siblingsDifferent (fun f site => cbcSiteInput f site.val) recursiveInput
  have badImpliesRepeat : ∀ f : X → X, cbcBad f blockForm messages →
      ¬ Function.Injective
        (fun site : ↑(cbcSites blockForm messages) =>
      cbcSiteInput f site.val) := by
    -- A bad event supplies two distinct reached sites with the same input.
    rintro f ⟨message, member, other, otherMember, position, positionBound,
      otherPosition, otherPositionBound, different, equal⟩ injective
    have leftMember : (blockForm message).take (position + 1) ∈
        cbcSites blockForm messages :=
      mem_cbcSites.mpr ⟨message, member, position, positionBound, rfl⟩
    have rightMember : (blockForm other).take (otherPosition + 1) ∈
        cbcSites blockForm messages :=
      mem_cbcSites.mpr
        ⟨other, otherMember, otherPosition, otherPositionBound, rfl⟩
    have sitesEqual :
        (⟨_, leftMember⟩ : ↑(cbcSites blockForm messages)) =
          ⟨_, rightMember⟩ := by
      -- Injectivity would identify the two site subtypes.
      refine injective ?_
      change cbcSiteInput f ((blockForm message).take (position + 1)) =
        cbcSiteInput f ((blockForm other).take (otherPosition + 1))
      rw [cbcSiteInput_take f _ positionBound,
        cbcSiteInput_take f _ otherPositionBound]
      exact equal
    exact different (congrArg Subtype.val sitesEqual)
  refine le_trans
    -- The bad-event mass is at most the mass of a repeated walk input.
    (Distribution.mass_mono Distribution.uniform_nonNeg badImpliesRepeat) ?_
  obtain ⟨siteCount, countEq⟩ :
      ∃ count, Fintype.card ↑(cbcSites blockForm messages) = count :=
    ⟨_, rfl⟩
  rw [countEq] at walkBound
  -- Apply the generic random-function walk collision bound.
  refine le_trans walkBound ?_
  have countBound : siteCount ≤ limit := by
    -- The number of distinct sites is at most the admitted total block count.
    rw [← countEq, Fintype.card_coe]
    exact (card_cbcSites_le blockForm messages).trans admitted
  have productBound : (siteCount : Real) * ((siteCount : Real) - 1) ≤
      (limit : Real) * ((limit : Real) - 1) := by
    -- The birthday numerator is monotone on natural counts within the limit.
    have castBound : (siteCount : Real) ≤ limit := by exact_mod_cast countBound
    rcases Nat.eq_zero_or_pos limit with zero | positive
    · have siteZero : siteCount = 0 := by omega
      rw [siteZero, zero]
    · nlinarith [mul_nonneg
        (show (0 : Real) ≤ limit - siteCount by linarith)
        (show (0 : Real) ≤ limit + siteCount - 1 by
          have : (1 : Real) ≤ limit := by exact_mod_cast positive
          linarith)]
  have denominatorPositive : (0 : Real) < 2 * Fintype.card X := by
    -- The finite nonempty alphabet gives a positive collision denominator.
    have : (0 : Real) < Fintype.card X := by exact_mod_cast Fintype.card_pos
    positivity
  gcongr

end CollisionMass

end SecurityCore

end CBCMAC.CBCCombinatorics
