import RandomSystems.Converter.ProgramAttachment

/-!
# Upstream candidates: a program attached to a function

Candidates for `RandomSystems.Converter.ProgramAttachment`, beside `inline_automatonSystem`. The
system of a function `g` answers each nonempty history with `g` at its last query. An invocation
run against `g` answers each inside query of the body with its value under `g`; feeding the
attached program is running the invocation. So if, against `g`, every invocation on `u` returns
`f u` from every state of the program, the program attached to the system of `g` is the system
of `f`, and on domains the converter of the program on `F` attached to `g` on `E` is `f` on `F`.

## Main definitions

* `functionSystem g`: the system of the function `g`
* `Program.answer P g s o u n h`: an invocation run against `g`

## Main results

* `Program.answer_of_exchanges`: an invocation whose body makes its exchanges itself, answered by
  `g`, returns what the body returns after them
* `Program.feed_function`, `Program.inline_function`: the program attached to the system of `g`
* `Program.trim_apply_ofProgramOn_function`: the same on domains
-/

namespace SystemAlgebra

open Classical

variable {S O J : Type} {U V : O → Type} {X Y : J → Type}

/-- **The system of the function `g`**: it answers each nonempty history with `g` at its last
query. -/
def functionSystem (g : ∀ j, X j → Y j) : InterfaceSystem J X Y := fun h =>
  (h.getLast?.map fun x => (⟨x.1, g x.1 x.2⟩ : Σ j, Y j) : Part _)

@[simp] theorem functionSystem_snoc (g : ∀ j, X j → Y j) (h : List (Σ j, X j)) (x : Σ j, X j) :
    functionSystem g (h ++ [x]) = Part.some ⟨x.1, g x.1 x.2⟩ := by
  simp [functionSystem]

theorem functionSystem_dom (g : ∀ j, X j → Y j) (h : List (Σ j, X j)) :
    (functionSystem g h).Dom ↔ h ≠ [] := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, x, rfl⟩
  · simp [functionSystem]
  · simp [List.concat_eq_append]

theorem functionSystem_isDDS (g : ∀ j, X j → Y j) : IsDDS (functionSystem g) :=
  ⟨by simp [SilentAtEmpty, functionSystem], fun p _ _ hne _ => (functionSystem_dom g p).mpr hne⟩

theorem functionSystem_replies (g : ∀ j, X j → Y j) :
    RepliesAtQueriedInterface (functionSystem g) := by
  intro h a y hy
  rw [functionSystem_snoc] at hy
  obtain rfl := Part.mem_some_iff.mp hy
  rfl

namespace Program

/-- **An invocation run against the function `g`**: the body runs from the exchanges `h`, each
inside query answered by its value under `g`, with at most `n` more of them. -/
def answer (P : Program S O J U V X Y) (g : ∀ j, X j → Y j) (s : S) (o : O) (u : U o) :
    ℕ → List ((Σ j, X j) × (Σ j, Y j)) → Option (S × V o)
  | 0, h => (P s o u h).elim some fun _ => none
  | n + 1, h =>
    match P s o u h with
    | .inl a => some a
    | .inr q => answer P g s o u n (h ++ [(q, ⟨q.1, g q.1 q.2⟩)])

variable {P : Program S O J U V X Y}

/-- The exchanges of an invocation before its last one are the invocation's own, and the body
made the last query itself. -/
theorem Consistent.of_snoc {t : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {z : (Σ j, X j) × (Σ j, Y j)} (hc : P.Consistent t o u (h ++ [z])) :
    P.Consistent t o u h ∧ P t o u h = .inr z.1 ∧ z.2.1 = z.1.1 := by
  refine ⟨fun i hi => ?_, by simpa using hc h.length (by simp)⟩
  have he := hc i (by simp; omega)
  rwa [List.take_append_of_le_length hi.le, List.getElem_append_left hi] at he

/-- An invocation of a program making at most `b` inside queries makes its own exchanges at most
`b` times. -/
theorem Consistent.length_le {b : ℕ} (hP : P.Bounded b) {t : S} {o : O} {u : U o}
    {h : List ((Σ j, X j) × (Σ j, Y j))} (hc : P.Consistent t o u h) : h.length ≤ b := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
  · simp
  · rw [List.concat_eq_append] at hc ⊢
    obtain ⟨hc, hz, -⟩ := hc.of_snoc
    have := hP t o u h z.1 hc hz
    simp only [List.length_append, List.length_singleton]
    omega

/-- **An invocation whose body makes its exchanges itself**, each answered by `g`, and then returns
`a`, returns `a` against `g` with at least as many inside queries allowed. -/
theorem answer_of_exchanges {g : ∀ j, X j → Y j} {t : S} {o : O} {u : U o} {a : S × V o}
    {h : List ((Σ j, X j) × (Σ j, Y j))} (hc : P.Consistent t o u h)
    (hg : ∀ z ∈ h, z.2 = ⟨z.1.1, g z.1.1 z.1.2⟩) (ha : P t o u h = .inl a) :
    ∀ n, h.length ≤ n → P.answer g t o u n [] = some a := by
  have key : ∀ (suf pre : List ((Σ j, X j) × (Σ j, Y j))), pre ++ suf = h →
      ∀ n, suf.length ≤ n → P.answer g t o u n pre = some a := by
    intro suf
    induction suf with
    | nil =>
      intro pre hpre n _
      rw [List.append_nil] at hpre
      subst hpre
      cases n <;> simp [answer, ha]
    | cons z suf ih =>
      intro pre hpre n hn
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
      subst hpre
      have hz := hc pre.length (by simp)
      simp only [List.take_left', List.getElem_append_right (le_refl _), Nat.sub_self,
        List.getElem_cons_zero] at hz
      have hzg := hg z (by simp)
      simp only [answer, hz.1]
      rw [show ((z.1, ⟨z.1.1, g z.1.1 z.1.2⟩) : (Σ j, X j) × (Σ j, Y j)) = z from
        Prod.ext rfl hzg.symm]
      exact ih (pre ++ [z]) (by simp) n (by simpa using hn)
  exact key h [] (by simp)

variable (P) in
/-- **An invocation fed by the system of a function is the invocation run against it.** -/
theorem feed_function (g : ∀ j, X j → Y j) :
    ∀ (n : ℕ) (s : S) (o : O) (u : U o) (h : List ((Σ j, X j) × (Σ j, Y j)))
      (rh : List (Σ j, X j)) (m : Mode S O J U X Y) (x : Σ l, twoFam U Y l),
      P.step m x = some (P.emit s o u h) →
      (P.feed (functionSystem g) (n + 1) m x rh).map (fun t => (t.1, t.2.2)) =
        (P.answer g s o u n h).map (fun a => (.idle a.1, ⟨o, a.2⟩)) := by
  intro n
  induction n with
  | zero =>
    intro s o u h rh m x hs
    rw [feed, hs]
    cases hq : P s o u h with
    | inl a => simp [emit, hq, answer]
    | inr q =>
      simp only [emit, hq]
      simp [feed, answer, hq]
  | succ n ih =>
    intro s o u h rh m x hs
    rw [feed, hs]
    cases hq : P s o u h with
    | inl a => simp [emit, hq, answer]
    | inr q =>
      simp only [emit, hq]
      have hd : (functionSystem g (rh ++ [⟨q.1, q.2⟩])).Dom :=
        (functionSystem_dom g _).mpr (by simp)
      rw [dif_pos hd]
      have hget : (functionSystem g (rh ++ [⟨q.1, q.2⟩])).get hd = ⟨q.1, g q.1 q.2⟩ := by
        simp
      rw [hget]
      dsimp only
      refine (ih s o u (h ++ [(q, ⟨q.1, g q.1 q.2⟩)]) (rh ++ [⟨q.1, q.2⟩]) (.busy o s u h q)
        ⟨⟨some (), q.1⟩, g q.1 q.2⟩ (by simp [step])).trans ?_
      simp only [answer, hq]

variable (P) in
/-- **A program attached to the system of a function**: if, against `g`, every invocation on `u`
returns `f u` from every state, the inlined program is the system of `f`. -/
theorem inline_function {b : ℕ} (g : ∀ j, X j → Y j) (f : ∀ o, U o → V o) (s : S)
    (answers : ∀ t o u, ∃ t', P.answer g t o u b [] = some (t', f o u)) :
    P.inline (functionSystem g) b s = functionSystem f := by
  have after : ∀ us : List (Σ o, U o),
      ∃ t rh, P.inlineAfter (functionSystem g) b s us = some (.idle t, rh) := by
    intro us
    induction us using List.reverseRecOn with
    | nil => exact ⟨s, [], rfl⟩
    | append_singleton us a ih =>
      obtain ⟨t, rh, hst⟩ := ih
      obtain ⟨t', ht'⟩ := answers t a.1 a.2
      have hf := P.feed_function g b t a.1 a.2 [] rh (.idle t) ⟨⟨none, a.1⟩, a.2⟩ rfl
      rw [ht'] at hf
      obtain ⟨⟨m', rh', w⟩, hfeed, heq⟩ := Option.map_eq_some_iff.mp hf
      simp only [Prod.mk.injEq] at heq
      refine ⟨t', rh', ?_⟩
      rw [inlineAfter_snoc, hst, Option.bind_some, hfeed, Option.map_some, heq.1]
  funext us
  rcases List.eq_nil_or_concat us with rfl | ⟨us, a, rfl⟩
  · simp [inline, functionSystem]
  rw [List.concat_eq_append, inline_snoc, functionSystem_snoc]
  obtain ⟨t, rh, hst⟩ := after us
  obtain ⟨t', ht'⟩ := answers t a.1 a.2
  have hf := P.feed_function g b t a.1 a.2 [] rh (.idle t) ⟨⟨none, a.1⟩, a.2⟩ rfl
  rw [ht'] at hf
  obtain ⟨⟨m', rh', w⟩, hfeed, heq⟩ := Option.map_eq_some_iff.mp hf
  simp only [Prod.mk.injEq] at heq
  rw [hst, Option.bind_some, hfeed, Option.map_some, heq.2]
  rfl

/-- **A program on the outside domain `F` attached to a function on the inside domain `E`** is
the function the program computes, on `F`, when the program is a DDC from `E`. -/
theorem trim_apply_ofProgramOn_function {b : ℕ} (hP : P.Bounded b) (g : ∀ j, X j → Y j)
    (f : ∀ o, U o → V o) (s : S)
    (answers : ∀ t o u, ∃ t', P.answer g t o u b [] = some (t', f o u))
    {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (hα : IsDDCFrom E F b (DDC.ofProgramOn s P F)) :
    trim (apply (DDC.ofProgramOn s P F) (filterDom E (functionSystem g))) =
      filterDom F (functionSystem f) := by
  have hsub : ∀ h y, y ∈ filterDom E (functionSystem g) h → y ∈ functionSystem g h :=
    fun h y hy => ((filterDom_mem_iff E _ h y).mp hy).2
  have hdomE : ∀ h, (filterDom E (functionSystem g) h).Dom ↔ E h := by
    intro h
    rw [filterDom_dom, functionSystem_dom]
    exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => hE.1 (he ▸ hd)⟩⟩
  obtain ⟨-, hdom⟩ := hα.mapsDomain hF _ ((functionSystem_isDDS g).filterDom E hE.2)
    (fun h x y hy => functionSystem_replies g h x y (hsub _ _ hy)) hdomE
  have hfull : trim (apply (DDC.ofProgramOn s P F) (functionSystem g)) =
      filterDom F (functionSystem f) := by
    rw [trim_apply_ofProgramOn s hP F hF.2, inline_function P g f s answers]
  rw [← hfull]
  apply IsDDS.eq_of_replies_iff (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]))
    (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]))
  apply replies_iff_of_dom_iff
  · intro h
    rw [hdom, hfull, filterDom_dom, functionSystem_dom]
    exact ⟨fun hd => ⟨hd, fun he => hF.1 (he ▸ hd)⟩, fun hd => hd.1⟩
  · intro xs ys hr
    rw [replies_trim_iff, apply_eq] at hr ⊢
    exact hr.interconnect_mono (pair_mono (fun _ _ h => h) hsub)

end Program

end SystemAlgebra
