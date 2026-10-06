import ConstructiveCryptography.DSL.Programs

/-!
# Upstream candidates: loops against a function

Candidates for `ConstructiveCryptography.DSL.Programs`. A loop making one call per element, run
against a fixed function, has a determined inside transcript: each call queries on the
accumulator and the element, and the function's reply advances the accumulator. On that
transcript the loop makes exactly those calls itself, then returns the ordinary fold.

## Main definitions

* `DSL.foldTranscript j ask advance f ts c`: the inside transcript of a loop against `f`

## Main results

* `DSL.foldr_call_const`: a binding the loop does not change can be held fixed
* `DSL.exchangesOf_foldTranscript`: on its transcript, the loop makes its calls itself
* `DSL.foldr_call_foldTranscript`: after its transcript, the loop returns the fold
-/

namespace SystemAlgebra.DSL

open Program (ExchangesOf)

variable {J C T A : Type} {X Y : J → Type}

/-- A binding the loop does not change can be held fixed. -/
theorem foldr_call_const {P : Type} (j : J) (ask : P → C → T → X j)
    (advance : P → C → T → Y j → C) (finish : P → C → A) (ts : List T) (p : P) (c : C) :
    ts.foldr (fun t k (pc : P × C) => callProg j (ask pc.1 pc.2 t)
        (fun y => k (pc.1, advance pc.1 pc.2 t y)))
      (fun pc => returnProg (finish pc.1 pc.2)) (p, c) =
    ts.foldr (fun t k c => callProg j (ask p c t) (fun y => k (advance p c t y)))
      (fun c => returnProg (finish p c)) c := by
  induction ts generalizing c with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldr_cons]
    congr 1
    funext y
    exact ih _

/-- The inside transcript of a loop against the function `f`. -/
def foldTranscript (j : J) (ask : C → T → X j) (advance : C → T → Y j → C) (f : X j → Y j) :
    List T → C → List ((Σ j, X j) × (Σ j, Y j))
  | [], _ => []
  | t :: ts, c =>
    (⟨j, ask c t⟩, ⟨j, f (ask c t)⟩) :: foldTranscript j ask advance f ts (advance c t (f (ask c t)))

theorem foldTranscript_length (j : J) (ask : C → T → X j) (advance : C → T → Y j → C)
    (f : X j → Y j) (ts : List T) (c : C) :
    (foldTranscript j ask advance f ts c).length = ts.length := by
  induction ts generalizing c with
  | nil => rfl
  | cons t ts ih => simp only [foldTranscript, List.length_cons, ih]

theorem foldTranscript_answers (j : J) (ask : C → T → X j) (advance : C → T → Y j → C)
    (f : ∀ j, X j → Y j) (ts : List T) (c : C) :
    ∀ z ∈ foldTranscript j ask advance (f j) ts c, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩ := by
  induction ts generalizing c with
  | nil => simp [foldTranscript]
  | cons t ts ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · rfl
    · exact ih _ z hz

/-- On its transcript against `f`, the loop makes its calls itself. -/
theorem exchangesOf_foldTranscript (j : J) (ask : C → T → X j) (advance : C → T → Y j → C)
    (f : X j → Y j) (finish : C → A) (ts : List T) (c : C) :
    ExchangesOf (ts.foldr (fun t k c => callProg j (ask c t) (fun y => k (advance c t y)))
      (fun c => returnProg (finish c)) c) (foldTranscript j ask advance f ts c) := by
  induction ts generalizing c with
  | nil => intro i hi; simp [foldTranscript] at hi
  | cons t ts ih =>
    intro i hi
    cases i with
    | zero => exact ⟨rfl, rfl⟩
    | succ i =>
      have he := ih (advance c t (f (ask c t))) i (by simpa [foldTranscript] using hi)
      simpa [foldTranscript, callProg] using he

/-- After its transcript against `f`, the loop returns the ordinary fold. -/
theorem foldr_call_foldTranscript (j : J) (ask : C → T → X j) (advance : C → T → Y j → C)
    (f : X j → Y j) (finish : C → A) (ts : List T) (c : C) :
    (ts.foldr (fun t k c => callProg j (ask c t) (fun y => k (advance c t y)))
      (fun c => returnProg (finish c)) c) (foldTranscript j ask advance f ts c) =
        .inl (finish (ts.foldl (fun c t => advance c t (f (ask c t))) c)) := by
  induction ts generalizing c with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldr_cons, foldTranscript, callProg, List.foldl_cons, dite_true]
    exact ih _

end SystemAlgebra.DSL
