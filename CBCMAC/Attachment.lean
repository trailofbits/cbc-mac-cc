import CBCMAC.Tactics
import RandomSystems.Converter.QueryLimit

set_option autoImplicit false

namespace CBCMAC

noncomputable section

open RandomSystems.Ambient
open RandomSystems.Ambient.DDC
open Probability (Distribution)
open CategoryTheory
open scoped RandomSystems.Ambient.DDC

universe u

variable {X M : Type u}

/-- The bounded CBC recurrence computes the digest and emits exactly one inner
query for each encoded block.  Keeping both conclusions in one invariant
avoids proving the same recursive exchange twice. -/
lemma boundedInnerQueryResult_cbc_and_length
    [Fintype M] [AddMonoid X]
    (function : X → X) (blockForm : M → List X) (message : M) :
    DDC.boundedInnerQueryResult (CBCCombinatorics.blockBound blockForm)
        (fun message answers _ => response blockForm message answers)
        closeResponse (fun input => some (function input)) message [] =
        some (CBCCombinatorics.cbc function (blockForm message)) ∧
      (DDC.innerQueriesWithinBound
        (CBCCombinatorics.blockBound blockForm)
        (fun message answers _ => response blockForm message answers)
        (fun input => some (function input)) message []).length =
        (blockForm message).length := by
  let blocks := blockForm message
  -- Induct once on the number of encoded blocks still to be processed.
  have digest : ∀ distance count : Nat,
      count + distance = blocks.length →
        DDC.boundedInnerQueryResult (CBCCombinatorics.blockBound blockForm)
            (fun message answers _ => response blockForm message answers)
            closeResponse (fun input => some (function input)) message
            (successfulReplies function blocks count) =
            some (CBCCombinatorics.cbc function blocks) ∧
          (DDC.innerQueriesWithinBound
            (CBCCombinatorics.blockBound blockForm)
            (fun message answers _ => response blockForm message answers)
            (fun input => some (function input)) message
            (successfulReplies function blocks count)).length = distance := by
    -- Fix the number of blocks still to be processed.
    intro distance
    induction distance with
    | zero =>
        intro count countLength
        have countEqual : count = blocks.length := by cbc_grind
        subst count
        -- At the last block, both recursive functions close in either bound branch.
        by_cases below : blocks.length <
            CBCCombinatorics.blockBound blockForm
        · have repliesBelow :
              (successfulReplies function blocks blocks.length).length <
                CBCCombinatorics.blockBound blockForm := by
            simpa only [successfulReplies_length] using below
          rw [DDC.boundedInnerQueryResult, dif_pos repliesBelow,
            DDC.innerQueriesWithinBound, dif_pos repliesBelow,
            response_successfulReplies_length function blockForm message]
          constructor <;> rfl
        · have repliesNotBelow : ¬
              (successfulReplies function blocks blocks.length).length <
                CBCCombinatorics.blockBound blockForm := by
            simpa only [successfulReplies_length] using below
          rw [DDC.boundedInnerQueryResult, dif_neg repliesNotBelow,
            DDC.innerQueriesWithinBound, dif_neg repliesNotBelow]
          constructor
          · simp [closeResponse, successfulReplies, answerValues_map_some,
              successfulValues_getLastD, blocks]
          · rfl
    | succ distance inductionHypothesis =>
        intro count countLength
        have countBelow : count < blocks.length := by cbc_grind
        -- The message-specific remaining block also lies below the uniform bound.
        have belowBound : count < CBCCombinatorics.blockBound blockForm :=
          countBelow.trans_le
            (CBCCombinatorics.length_le_blockBound blockForm message)
        have repliesBelow :
            (successfulReplies function blocks count).length <
              CBCCombinatorics.blockBound blockForm := by
          simpa only [successfulReplies_length] using belowBound
        have messageBelow : count < (blockForm message).length := by
          simpa only [blocks] using countBelow
        rw [DDC.boundedInnerQueryResult, dif_pos repliesBelow,
          DDC.innerQueriesWithinBound, dif_pos repliesBelow,
          response_successfulReplies_of_lt function blockForm message
            messageBelow]
        simp only
        -- The emitted query returns the next CBC state and extends both recurrences.
        rw [← cbc_take_succ function (blockForm message) messageBelow,
          ← successfulReplies_succ]
        have next := inductionHypothesis (count + 1) (by cbc_grind)
        constructor
        · exact next.1
        · cbc_grind [next.2]
  -- Start the joint recurrence with no processed blocks.
  simpa [blocks, successfulReplies, successfulValues] using
    digest (blockForm message).length 0 (by simp [blocks])

lemma boundedInnerQueryResult_cbc [Fintype M] [AddMonoid X]
    (function : X → X) (blockForm : M → List X) (message : M) :
    DDC.boundedInnerQueryResult (CBCCombinatorics.blockBound blockForm)
        (fun message answers _ => response blockForm message answers)
        closeResponse (fun input => some (function input)) message [] =
      some (CBCCombinatorics.cbc function (blockForm message)) :=
  (boundedInnerQueryResult_cbc_and_length function blockForm message).1

/-- Against a stateless round function, attachment implements the CBC recurrence
of CR18, Section 6.2.3, on the final requested message. -/
lemma applySystem_cbc_ofFunction [Fintype M] [AddMonoid X]
    (function : X → X) (blockForm : M → List X) :
    applySystem (cbc blockForm) (DDS.ofFunction function) =
      DDS.ofFunction (fun message =>
        CBCCombinatorics.cbc function (blockForm message)) := by
  -- Expand CBC as a bounded-inner-query DDC against the stateless function.
  rw [cbc]
  calc
    applySystem
        (DDC.ofBoundedInnerQueries (CBCCombinatorics.blockBound blockForm)
          (fun message answers _ => response blockForm message answers)
          closeResponse)
        (DDS.ofFunction function) =
      fun outerHistory =>
        DDC.boundedInnerQueryResult
          (CBCCombinatorics.blockBound blockForm)
          (fun message answers _ => response blockForm message answers)
          closeResponse (fun input => some (function input))
          (History.last outerHistory) [] :=
      -- The generic attachment theorem reduces to the recursive bounded result.
      DDC.applySystem_ofBoundedInnerQueries_eq _ _ _ function
    _ = DDS.ofFunction (fun message =>
        CBCCombinatorics.cbc function (blockForm message)) := by
      -- Compare the resulting deterministic systems on each history.
      apply DDS.ext
      intro outerHistory
      -- The recurrence evaluates the bounded queries to the ordinary CBC fold.
      rw [boundedInnerQueryResult_cbc]
      rfl

/-- Attaching CBC to a random function gives its induced CBC law. -/
lemma apply_cbc_randomFunction [Fintype M] [AddMonoid X]
    (blockForm : M → List X)
    (roundFunction : RandomSystems.RandomFunction X X) :
    DDC.asHom (cbc blockForm) • roundFunction.toAmbientPDS =
      cbcPDS blockForm roundFunction := by
  apply Subtype.ext
  change Distribution.fTransform (applySystem (cbc blockForm))
      (Distribution.fTransform DDS.ofFunction roundFunction.law.1) =
    Distribution.fTransform
      (fun function : X → X =>
        DDS.ofFunction (fun message =>
          CBCCombinatorics.cbc function (blockForm message)))
      roundFunction.law.1
  rs_probability
  apply Distribution.fTransform_congr
  intro function _
  simpa only [Function.comp_apply] using
    applySystem_cbc_ofFunction function blockForm

lemma response_eq_inl_implies_length_lt [AddMonoid X]
    (blockForm : M → List X) (message : M) (answers : List (Option X))
    (query : X) (equal : response blockForm message answers = Sum.inl query) :
    answers.length < (blockForm message).length := by
  unfold response at equal
  cases valuesEqual : answerValues answers with
  | none => simp only [valuesEqual] at equal; cases equal
  | some values =>
      simp only [valuesEqual] at equal
      split at equal
      next below =>
        have answersEqual := answerValues_eq_some_iff.mp valuesEqual
        rw [answersEqual, List.length_map]
        exact below
      next notBelow => cases equal

lemma cbc_mem_query_implies_latestReplies_length_lt
    [Fintype M] [AddMonoid X]
    (blockForm : M → List X)
    (history : DDC.History
      (Interface.single M X) (Interface.single X X)) (query : X)
    (responds : Sum.inl query ∈ cbc blockForm history) :
    (DDC.latestReplies history).length <
      (blockForm history.lastOuter).length := by
  rw [cbc, DDC.mem_ofBoundedInnerQueries_iff] at responds
  have responseEqual := responds.2
  unfold DDC.boundedInnerQueryResponse DDC.responseWithInnerQueryBound at responseEqual
  split at responseEqual
  next below =>
    exact response_eq_inl_implies_length_lt blockForm history.lastOuter
      (DDC.latestReplies history) query responseEqual.symm
  next notBelow => cases responseEqual

lemma totalBlocks_eq_dropLast_add_last
    (blockForm : M → List X)
    (history : DDC.History
      (Interface.single M X) (Interface.single X X)) :
    CBCCombinatorics.totalBlocks blockForm history.outer.queries =
      CBCCombinatorics.totalBlocks blockForm history.outer.queries.dropLast +
        (blockForm history.lastOuter).length := by
  have split := List.dropLast_append_getLast history.outer.nonempty
  unfold CBCCombinatorics.totalBlocks
  rw [show history.outer.queries =
      history.outer.queries.dropLast ++ [history.lastOuter] by
    change history.outer.queries = history.outer.queries.dropLast ++
      [history.outer.queries.getLast history.outer.nonempty]
    exact split.symm]
  simp

lemma cbc_admissible_query_count
    [Fintype M] [AddMonoid X]
    (blockForm : M → List X)
    (history : DDC.History
      (Interface.single M X) (Interface.single X X))
    (admissible : DDC.Raw.Admissible (cbc blockForm).toFun history) :
    ∃ completed,
      history.receivedInnerQueries.length =
          completed + (DDC.latestReplies history).length ∧
        completed ≤ CBCCombinatorics.totalBlocks blockForm
          history.outer.queries.dropLast ∧
        (DDC.latestReplies history).length ≤
          (blockForm history.lastOuter).length := by
  induction admissible with
  | start message =>
      exact ⟨0, by simp [CBCCombinatorics.totalBlocks]⟩
  | @afterInner history query prior responds reply inductionHypothesis =>
      obtain ⟨completed, countEqual, completedBound, latestBound⟩ :=
        inductionHypothesis
      have latestStrict :=
        cbc_mem_query_implies_latestReplies_length_lt blockForm history query responds
      refine ⟨completed, ?_, ?_, ?_⟩
      · simp only [DDC.History.receivedInnerQueries_snocInner,
          List.length_append, List.length_singleton,
          DDC.latestReplies_snoc_inner]
        omega
      · simpa [DDC.History.snocInner] using completedBound
      · simp only [DDC.latestReplies_snoc_inner, List.length_append,
          List.length_singleton, DDC.History.lastOuter_snocInner]
        omega
  | @afterOuter history prior reply responds message inductionHypothesis =>
      obtain ⟨completed, countEqual, completedBound, latestBound⟩ :=
        inductionHypothesis
      refine ⟨history.receivedInnerQueries.length, ?_, ?_, ?_⟩
      · simp
      · rw [DDC.History.snocOuter]
        change history.receivedInnerQueries.length ≤
          CBCCombinatorics.totalBlocks blockForm
            (history.outer.queries ++ [message]).dropLast
        rw [List.dropLast_concat,
          totalBlocks_eq_dropLast_add_last blockForm history]
        omega
      · simp

lemma cbc_mem_query_implies_count_lt_totalBlocks
    [Fintype M] [AddMonoid X]
    (blockForm : M → List X)
    (history : DDC.History
      (Interface.single M X) (Interface.single X X)) (query : X)
    (responds : Sum.inl query ∈ cbc blockForm history) :
    history.receivedInnerQueries.length <
      CBCCombinatorics.totalBlocks blockForm history.outer.queries := by
  have admissible : DDC.Raw.Admissible (cbc blockForm).toFun history :=
    ((cbc blockForm).exactDomain history).mp responds.1
  obtain ⟨completed, countEqual, completedBound, latestBound⟩ :=
    cbc_admissible_query_count blockForm history admissible
  have latestStrict :=
    cbc_mem_query_implies_latestReplies_length_lt blockForm history query responds
  rw [totalBlocks_eq_dropLast_add_last blockForm history]
  omega

lemma theta_mem_query_implies_receivedInnerQueries_append
    (blockForm : M → List X) (q : Nat)
    (history : DDC.History
      (Interface.single M X) (Interface.single M X)) (query : M)
    (responds : Sum.inl query ∈ (theta blockForm q).toDDC (Y := X) history) :
    history.receivedInnerQueries ++ [query] = history.outer.queries := by
  classical
  unfold RandomSystems.DomainFilter.toDDC at responds
  obtain ⟨_, queryEqual, queryHistory⟩ := DDC.filter_query_history
    (theta blockForm q).predicate
    (fun {_ _} isPrefix accepted =>
      (theta blockForm q).prefixClosed isPrefix accepted)
    history responds
  rw [queryEqual]
  exact queryHistory

lemma cbc_inner_query_within_limit
    [Fintype M] [AddMonoid X]
    (blockForm : M → List X) (q : Nat)
    (history : DDC.History
      (Interface.single M X) (Interface.single X X)) (query : X)
    (responds : Sum.inl query ∈
      DDC.serial ((theta blockForm q).toDDC (Y := X))
        (cbc blockForm) history) :
    history.receivedInnerQueries.length < q := by
  classical
  rw [DDC.mem_serial_iff, DDC.Internal.mem_serialRaw_iff] at responds
  obtain ⟨attempted, historyEqual, outerHistory, innerHistory,
    factorization⟩ := responds
  obtain ⟨cbcHistory, innerHistoryEqual, cbcResponds, thetaResponds⟩ :=
    factorization.endpointValid.exposedInner query rfl
  subst innerHistory
  have cbcMessages : cbcHistory.outer.queries = outerHistory.outer.queries := by
    obtain ⟨currentInner, innerEqual, queryHistory⟩ :=
      factorization.exists_innerHistory_outerQueries_eq_of_query
    cases Option.some.inj innerEqual
    rw [queryHistory]
    exact theta_mem_query_implies_receivedInnerQueries_append
      blockForm q outerHistory cbcHistory.lastOuter thetaResponds
  have cbcCount :=
    cbc_mem_query_implies_count_lt_totalBlocks
      blockForm cbcHistory query cbcResponds
  have serialCount := factorization.receivedInnerQueries_length_eq
  change cbcHistory.receivedInnerQueries.length =
    attempted.toReceived.receivedInnerQueries.length at serialCount
  have admitted : CBCCombinatorics.totalBlocks blockForm
      outerHistory.outer.queries ≤ q := by
    unfold RandomSystems.DomainFilter.toDDC at thetaResponds
    exact (DDC.filter_query_history
      (theta blockForm q).predicate
      (fun {_ _} isPrefix accepted =>
        (theta blockForm q).prefixClosed isPrefix accepted)
      outerHistory thetaResponds).1
  rw [← historyEqual, ← serialCount]
  rw [cbcMessages] at cbcCount
  omega


end

end CBCMAC
