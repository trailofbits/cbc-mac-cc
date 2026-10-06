import CBCMAC.CBC
import Probability.Counting
import Mathlib.Data.List.GetD

/-!
# Collisions of CBC under a uniform round function

The proof of CR18, Theorem 6.1 (printed pp. 126--127), uses prefix-freeness to
exclude trivial round-input collisions and applies Lemma 4.18.

This module formalizes the distinct-input condition, the shift action on good
functions, finite fibre counting, and the scalar collision budget. These statements depend only on finite algebra and
probability counting.
-/

namespace CBCMAC.Collisions

open Classical
open Probability

universe u

variable {X M : Type u}

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

/-- The input made to the round function at one block position. -/
def cbcInput [Zero X] [Add X] (f : X → X) (blocks : List X)
    (position : Nat) : X :=
  cbcFunction f (blocks.take position) + blocks.getD position 0

/-- The distinct nonempty encoded prefixes reached by a message history. -/
noncomputable def cbcSites (blockForm : M → List X) (messages : List M) :
    Finset (List X) := by
  classical
  exact (messages.flatMap fun message =>
    (List.range (blockForm message).length).map fun position =>
      (blockForm message).take (position + 1)).toFinset

lemma mem_cbcSites {blockForm : M → List X} {messages : List M}
    {site : List X} :
    site ∈ cbcSites blockForm messages ↔
      ∃ message ∈ messages, ∃ position < (blockForm message).length,
        site = (blockForm message).take (position + 1) := by
  classical
  simp [cbcSites, eq_comm]

/-- The primitive input at the final block of an encoded prefix. -/
def cbcSiteInput [Zero X] [Add X] (f : X → X) (site : List X) : X :=
  cbcInput f site (site.length - 1)

/-! ## CR18 collision condition and counting -/

section SecurityCore

section CollisionGeometry

variable [Zero X] [Add X]

/-- A nontrivial collision between distinct CBC call sites, as in the proof of
CR18, Theorem 6.1. Shared encoded prefixes denote one call site and are
excluded. -/
def cbcBad (f : X → X) (blockForm : M → List X)
    (messages : List M) : Prop :=
  ¬ Set.InjOn (cbcSiteInput f) (cbcSites blockForm messages)

lemma cbcBad_monotone (f : X → X) (blockForm : M → List X)
    {initial final : List M} (isPrefix : initial <+: final)
    (bad : cbcBad f blockForm initial) : cbcBad f blockForm final := by
  -- The earlier sites form a subset of the later sites.
  apply mt (Set.InjOn.mono ?_) bad
  intro site member
  obtain ⟨message, messageMember, position, bound, rfl⟩ := mem_cbcSites.mp member
  exact mem_cbcSites.mpr ⟨message, isPrefix.subset messageMember, position, bound, rfl⟩

lemma cbcInput_append_of_lt (f : X → X) (blocks : List X) (block : X)
    {position : Nat} (bound : position < blocks.length) :
    cbcInput f (blocks ++ [block]) position = cbcInput f blocks position := by
  -- Earlier call sites depend only on the unchanged prefix.
  unfold cbcInput
  rw [List.take_append_of_le_length (Nat.le_of_lt bound),
    List.getD_append blocks [block] 0 position bound]

lemma cbcInput_append_length (f : X → X) (blocks : List X) (block : X) :
    cbcInput f (blocks ++ [block]) blocks.length = cbcFunction f blocks + block := by
  -- The new last call uses the previous state and appended block.
  unfold cbcInput
  rw [List.take_left,
    List.getD_append_right blocks [block] 0 blocks.length (le_refl _)]
  simp

lemma cbcFunction_eq_apply_lastInput (f : X → X) (blocks : List X)
    (nonempty : blocks ≠ []) :
    cbcFunction f blocks = f (cbcInput f blocks (blocks.length - 1)) := by
  -- Decompose a nonempty list into its initial segment and final block.
  rcases blocks.eq_nil_or_concat with empty | ⟨initial, block, rfl⟩
  · exact absurd empty nonempty
  · rw [List.concat_eq_append, cbcFunction_append]
    -- The last call position is the length of the initial segment.
    congr 1
    have length : (initial ++ [block]).length - 1 = initial.length := by simp
    rw [length, cbcInput_append_length]

lemma cbcInput_take_of_lt (f : X → X) (blocks : List X)
    {position limit : Nat} (bound : position < limit) :
    cbcInput f (blocks.take limit) position = cbcInput f blocks position := by
  -- A call below the truncation point sees the same state prefix and block.
  unfold cbcInput
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  congr 1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt bound]

lemma cbcSiteInput_take (f : X → X) (blocks : List X)
    {position : Nat} (bound : position < blocks.length) :
    cbcSiteInput f (blocks.take (position + 1)) =
      cbcInput f blocks position := by
  unfold cbcSiteInput
  rw [List.length_take_of_le (Nat.succ_le_of_lt bound), Nat.succ_sub_one]
  exact cbcInput_take_of_lt f blocks (Nat.lt_succ_self position)

lemma cbcFunction_congr_of_agree_on_inputs (f g : X → X)
    (blocks : List X)
    (agree : ∀ position < blocks.length,
      f (cbcInput f blocks position) = g (cbcInput f blocks position)) :
    cbcFunction f blocks = cbcFunction g blocks := by
  -- Induct over successive final blocks of the CBC fold.
  induction blocks using List.reverseRecOn with
  | nil => rfl
  | append_singleton initial block inductionHypothesis =>
      rw [cbcFunction_append, cbcFunction_append]
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
  -- A terminal encoding and any different reached prefix are distinct sites.
  intro message member other otherMember position positionBound different equal
  apply different
  refine (not_not.mp good) ?_
    (mem_cbcSites.mpr ⟨other, otherMember, position, positionBound, rfl⟩) ?_
  · exact mem_cbcSites.mpr ⟨message, member, (blockForm message).length - 1,
      by have := List.length_pos_of_ne_nil (nonempty message); omega,
      (take_last_key (nonempty message)).symm⟩
  · rw [cbcSiteInput_take f _ positionBound]
    exact equal

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

lemma cbcInput_congr_of_agree_below (f g : X → X) (blocks : List X)
    {position : Nat}
    (agree : ∀ prior < position,
      g (cbcInput f blocks prior) = f (cbcInput f blocks prior)) :
    cbcInput g blocks position = cbcInput f blocks position := by
  -- The state before this call agrees because all earlier function answers agree.
  unfold cbcInput
  congr 1
  refine (cbcFunction_congr_of_agree_on_inputs f g (blocks.take position) ?_).symm
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
  -- Shifting terminal replies preserves every site input.
  have inputs : Set.EqOn (cbcSiteInput (cbcShift f blockForm messages delta))
      (cbcSiteInput f) (cbcSites blockForm messages) := by
    intro site member
    obtain ⟨message, messageMember, position, bound, rfl⟩ := mem_cbcSites.mp member
    rw [cbcSiteInput_take _ _ bound, cbcSiteInput_take _ _ bound]
    exact cbcInput_cbcShift f blockForm delta prefixFree
      (cbcFresh_of_not_cbcBad f blockForm nonempty good) messageMember bound
  exact not_not.mpr ((not_not.mp good).congr inputs.symm)


lemma cbcFunction_cbcShift (f : X → X) (blockForm : M → List X)
    {messages : List M} (delta : ↑messages.toFinset → X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (nonempty : ∀ message, blockForm message ≠ [])
    (fresh : cbcFresh f blockForm messages) {message : M}
    (member : message ∈ messages.toFinset) :
    cbcFunction (cbcShift f blockForm messages delta) (blockForm message) =
      cbcFunction f (blockForm message) + delta ⟨message, member⟩ := by
  -- Inputs stay fixed; the final function answer receives the designated shift.
  rw [cbcFunction_eq_apply_lastInput _ _ (nonempty message),
    cbcFunction_eq_apply_lastInput f _ (nonempty message),
    cbcInput_cbcShift f blockForm delta prefixFree fresh (List.mem_toFinset.mp member)
      (by have := List.length_pos_of_ne_nil (nonempty message); omega)]
  exact cbcShift_lastInput f blockForm messages delta
    (cbcLastInput_injOn f blockForm nonempty prefixFree fresh) ⟨message, member⟩

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


omit [Nonempty X] [Fintype M] in
lemma cbcFunction_fiber_card (blockForm : M → List X) {messages : List M}
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
          cbcFunction f (blockForm message.1) = answers message) ∧ Good f)).card *
        Fintype.card X ^ messages.toFinset.card =
      (Finset.univ.filter Good).card := by
  classical
  -- Apply the free transitive shift-action counting theorem to the CBC outputs.
  have key := Counting.card_filter_shift_univ
    (A := ↑messages.toFinset → X) Good
    (fun f message => cbcFunction f (blockForm message.1))
    (fun delta f => cbcShift f blockForm messages delta)
    shiftClosed
    (fun delta f good => funext fun message =>
      cbcFunction_cbcShift f blockForm delta prefixFree nonempty (fresh f good) message.2)
    (fun first second f good =>
      cbcShift_cbcShift f blockForm first second prefixFree nonempty
        (fresh f good))
    (fun f _ => Counting.multiShift_zero _ f) answers
  simpa only [Fintype.card_fun, Fintype.card_coe, funext_iff, and_comm] using key


/-- Outside the collision condition, CBC's transcript law is uniform. This is
the finite-law form of CR18, Equation (6.2). -/
lemma mass_cbcFunction_outputs_and_not_cbcBad_eq [Nontrivial M]
    (blockForm : M → List X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (messages : List M) (answers : M → X) :
    (Distribution.uniform (X → X)).mass (fun f =>
        (∀ message ∈ messages, cbcFunction f (blockForm message) = answers message) ∧
          ¬ cbcBad f blockForm messages) =
      (Distribution.uniform (M → X)).mass (fun g =>
        ∀ message ∈ messages, g message = answers message) *
      (Distribution.uniform (X → X)).mass
        (fun f => ¬ cbcBad f blockForm messages) := by
  classical
  let Good : (X → X) → Prop := fun f => ¬ cbcBad f blockForm messages
  -- Convert equal good fibres into factorization of the two uniform masses.
  apply Distribution.uniform_mass_eq_mass_mul_mass_of_card_mul_eq
  -- Prefix-freeness provides nonempty encodings and freshness outside the bad event.
  have nonempty : ∀ message, blockForm message ≠ [] :=
    blockForm_ne_nil_of_prefixFree prefixFree
  have fiber := cbcFunction_fiber_card blockForm nonempty prefixFree Good
    (fun f good => cbcFresh_of_not_cbcBad f blockForm nonempty good)
    (fun delta f good =>
      not_cbcBad_cbcShift f blockForm delta prefixFree nonempty good) (fun m => answers m.1)
  have cardBound : messages.toFinset.card ≤ Fintype.card M :=
    Finset.card_le_univ _
  simp only [Good, Subtype.forall, List.mem_toFinset] at fiber
  rw [Fintype.card_fun,
    show (Finset.univ.filter (fun g : M → X => ∀ m ∈ messages, g m = answers m)).card =
      Fintype.card X ^ (Fintype.card M - messages.toFinset.card) by
      simpa only [Subtype.forall, List.mem_toFinset] using
        Counting.card_function_fiber_finset messages.toFinset (fun m => answers m.1)]
  rw [← fiber]
  -- Split the full message-function exponent into queried and unqueried messages.
  conv_lhs =>
    rw [show Fintype.card M =
      (Fintype.card M - messages.toFinset.card) + messages.toFinset.card from
        (Nat.sub_add_cancel cardBound).symm, pow_add]
  ac_rfl

end UniformFibers

section SiteGeometry

variable [Zero X] [Add X]

omit [Zero X] [Add X] in
lemma cbcSites_ne_nil {blockForm : M → List X} {messages : List M}
    {site : List X} (member : site ∈ cbcSites blockForm messages) :
    site ≠ [] := by
  obtain ⟨message, _, position, bound, rfl⟩ := mem_cbcSites.mp member
  apply List.ne_nil_of_length_pos
  rw [List.length_take_of_le (Nat.succ_le_of_lt bound)]
  exact Nat.succ_pos _

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

def cbcSiteBlock (site : List X) : X :=
  site.getD (site.length - 1) 0

lemma cbcSiteInput_eq (f : X → X) (site : List X) :
    cbcSiteInput f site =
      cbcFunction f site.dropLast + cbcSiteBlock site := by
  -- Separate the site into its parent prefix and final block.
  rw [cbcSiteInput, cbcInput, cbcSiteBlock, List.dropLast_eq_take]

omit [Add X] in
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

noncomputable def cbcParent (blockForm : M → List X) (messages : List M)
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
  -- Erasing the optional parent gives exactly the preceding encoded prefix.
  have parentPrefix (site : ↑(cbcSites blockForm messages)) :
      (cbcParent blockForm messages site).elim [] Subtype.val = site.val.dropLast := by
    unfold cbcParent
    split_ifs with member
    · rfl
    · exact (Classical.by_contradiction fun nonempty =>
        member (dropLast_mem_cbcSites site.2 (Ne.symm nonempty)))
  have rankDecreases : ∀ site parent : ↑(cbcSites blockForm messages),
      cbcParent blockForm messages site = some parent →
        parent.val.length < site.val.length := by
    -- Dropping the final block strictly shortens every nonempty site.
    intro site parent equal
    have parentValue := parentPrefix site
    simp only [equal, Option.elim] at parentValue
    rw [parentValue, List.length_dropLast]
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
      (by rw [← parentPrefix left, ← parentPrefix right, sameParent])
    exact fun equal => differentBlock (add_left_cancel equal)
  have recursiveInput : ∀ (f : X → X)
      (site : ↑(cbcSites blockForm messages)),
      cbcSiteInput f site.val =
        ((cbcParent blockForm messages site).elim 0
          (fun parent => f (cbcSiteInput f parent.val))) +
            cbcSiteBlock site.val := by
    -- Express each site input from its parent state and final block.
    intro f site
    rw [cbcSiteInput_eq, ← parentPrefix site]
    cases parentEq : cbcParent blockForm messages site with
    | none => simp [Option.elim, cbcFunction]
    | some parent =>
      simpa only [Option.elim, cbcSiteInput] using
        congrArg (· + cbcSiteBlock site.val)
          (cbcFunction_eq_apply_lastInput f parent.val (siteNonempty parent))
  let siteCount := (cbcSites blockForm messages).card
  have countBound : siteCount ≤ limit :=
    (card_cbcSites_le blockForm messages).trans admitted
  calc
    -- Apply the birthday bound directly to the reached encoded prefixes.
    _ ≤ (siteCount : ℝ) * ((siteCount : ℝ) - 1) / (2 * Fintype.card X) := by
      have event (f : X → X) : cbcBad f blockForm messages ↔
          ¬ Function.Injective (fun site : ↑(cbcSites blockForm messages) =>
            cbcSiteInput f site.val) := not_congr Set.injOn_iff_injective
      rw [Distribution.mass_congr _ event]
      simpa only [Fintype.card_coe] using
        Counting.uniform_mass_walk_repeat_le (cbcParent blockForm messages)
          (fun site state => state + cbcSiteBlock site.val) (0 : X)
          (fun site => site.val.length) rankDecreases stepInjective
          siblingsDifferent (fun f site => cbcSiteInput f site.val) recursiveInput
    -- Distinct sites cannot outnumber the admitted blocks.
    _ ≤ (limit : ℝ) * ((limit : ℝ) - 1) / (2 * Fintype.card X) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have castBound : (siteCount : ℝ) ≤ limit := by exact_mod_cast countBound
      rcases Nat.eq_zero_or_pos limit with zero | positive
      · have siteZero : siteCount = 0 := by omega
        rw [siteZero, zero]
      · nlinarith [mul_nonneg
          (show (0 : ℝ) ≤ limit - siteCount by linarith)
          (show (0 : ℝ) ≤ limit + siteCount - 1 by
            have : (1 : ℝ) ≤ limit := by exact_mod_cast positive
            linarith)]

end CollisionMass

end SecurityCore

end CBCMAC.Collisions
