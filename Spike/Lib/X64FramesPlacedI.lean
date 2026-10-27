/-
**The suspended frames placed in stack slots or immediates** (x86-64, H7a
calls, the call bracket at depth): `FramesPlacedIn`
(`Spike/Lib/X64PlacedS.lean`) forbids a whole-word immediate, but a
caller's live words at a call may be the layout's immediates (a literal
bound before the call, read after it). `FramesPlacedInI` lets a word be an
immediate where the layout's table has it at the frame's body, every other
place a slot of `A`; an immediate is represented alike in every state, so a
callee's run keeping the caller's cells keeps the frames placed.

- `InSlotsI`, `FramesPlacedInI`, `.nil`, `.toFramesPlaced`, `.mono`,
  `.of_eq`: the placement, kept by a state whose private memory agrees on
  `A` (`wordPlaceRep_of_eqI`); `.of_cKept`, by a callee's state keeping
  the caller's cells outside its region (`CKept`), the slots among them.
- `SlotPlacedI`: the caller's control placed in the slots of `A` or at
  immediates the layout has at the continuation `t`.
- `FramesPlacedInI.push`: the caller's frame pushed at a call.
- `slotPlacedI_of_srep`: `SlotPlacedI` from the lowering's node invariant
  at the call (`SRep` of the symbolic environment, `EnvNum`, every free
  variable symbolic), each IR register's cell loading its slot in `s`
  (`hcell`) at an address of `A` (`hA`), the immediates the layout's at the
  continuation (`himm`); the place map is `envmOf`
  (`Spike/Lib/X64AbortPlace.lean`).
- `framesPlaced_callTo`: the frames at the callee's entry `fr :: fs`
  placed, from the call's `SlotPlacedI` and the caller's frames.
-/
import Spike.Lib.X64PlacedS
import Spike.Lib.X64AbortPlace
import Spike.Lib.DepthFactsS
import Spike.Lib.X64Call

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64Consumer
open Spike.Lib.Form (opdVal SEnv lookupS WordPl SRep)
open Spike.Lib.LowerNode (EnvNum)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s s' : State} {c : Ctl} {fs : List TermRun.Frame}

/-! ## Placed in slots or immediates -/

/-- **A word place in the slots of `A`**, or an immediate: each of its
places a slot of `A`. -/
def InSlotsI (A : Nat → Prop) (wp : WordPlace (machine (kernel 1)).I.RegId) : Prop :=
  ∀ pl ∈ wp.places, ∃ a, pl = .slot a ∧ A a

/-- **The suspended frames placed in the slots of `A` or at immediates**:
`FramesPlaced` with every place a slot of `A`. -/
def FramesPlacedInI (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (fs : List TermRun.Frame) (A : Nat → Prop) :
    Prop :=
  ∃ envm : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
    (∀ d f, fs[d]? = some f → ∀ x ty ws, TermRun.lookupE f.env x = some (ty, ws) →
      ∀ k wd wp, ws[k]? = some wd → envm d x k = some wp → WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
    (∀ d f, fs[d]? = some f → ∀ x ∈ (exprFv f.body).filter (· != f.x), ∀ ty ws,
      TermRun.lookupE f.env x = some (ty, ws) → ∀ k < ws.length, ∃ pl, envm d x k = some pl) ∧
    (∀ d x k wp, envm d x k = some wp → InSlotsI A wp) ∧
    (∀ d f x k n, fs[d]? = some f → envm d x k = some (.imm n) → Λ.imms f.body x k = some n)

/-- No suspended frame is placed anywhere. -/
theorem FramesPlacedInI.nil (A : Nat → Prop) : FramesPlacedInI Λ lbl s [] A :=
  ⟨fun _ _ _ => none, fun _ _ hf => by simp at hf, fun _ _ hf => by simp at hf, fun _ _ _ _ h => (by cases h),
    fun _ _ _ _ _ hf => by simp at hf⟩

/-- **Placed in slots or immediates is placed.** -/
theorem FramesPlacedInI.toFramesPlaced {A : Nat → Prop} (h : FramesPlacedInI Λ lbl s fs A) :
    FramesPlaced Λ lbl s fs := by
  obtain ⟨envm, hrep, htot, -, himm⟩ := h
  exact ⟨envm, hrep, htot, himm⟩

/-- **Placed in the slots of `A` is placed in the slots of a larger `B`.** -/
theorem FramesPlacedInI.mono {A B : Nat → Prop} (h : FramesPlacedInI Λ lbl s fs A) (hAB : ∀ a, A a → B a) :
    FramesPlacedInI Λ lbl s fs B := by
  obtain ⟨envm, hrep, htot, hin, himm⟩ := h
  refine ⟨envm, hrep, htot, fun d x k wp hwp pl hpl => ?_, himm⟩
  obtain ⟨a, rfl, ha⟩ := hin d x k wp hwp pl hpl
  exact ⟨a, rfl, hAB a ha⟩

/-- A word in the slots of `A` or an immediate is represented alike in two
states whose private memory agrees on `A`. -/
theorem wordPlaceRep_of_eqI {A : Nat → Prop}
    (hA : ∀ a, A a → (machine (kernel 1)).privLoad s' (BitVec.ofNat 64 a) =
      (machine (kernel 1)).privLoad s (BitVec.ofNat 64 a))
    {wp : WordPlace (machine (kernel 1)).I.RegId} (hwp : InSlotsI A wp) {v : WeakMem.Val}
    (h : WordPlaceRep (machine (kernel 1)) lbl s wp v) : WordPlaceRep (machine (kernel 1)) lbl s' wp v := by
  have hpv : ∀ pl ∈ wp.places, placeVal (machine (kernel 1)) s' pl = placeVal (machine (kernel 1)) s pl := by
    intro pl hm
    obtain ⟨a, rfl, ha⟩ := hwp pl hm
    simp only [placeVal, hA a ha]
  match wp, hpv, h with
  | .one pl, hpv, ⟨w, hw, hr⟩ => exact ⟨w, by rw [hpv pl (by simp [WordPlace.places]), hw], hr⟩
  | .loc pb (.at po), hpv, ⟨vb, vo, hb, ho, hr⟩ =>
    refine ⟨vb, vo, by rw [hpv pb (by simp [WordPlace.places]), hb], ?_, hr⟩
    show placeVal _ _ po = _
    rw [hpv po (by simp [WordPlace.places])]; exact ho
  | .loc pb (.imm n), hpv, ⟨vb, vo, hb, ho, hr⟩ =>
    exact ⟨vb, vo, by rw [hpv pb (by simp [WordPlace.places]), hb], ho, hr⟩
  | .imm n, _, h => exact h

/-- **Placed in slots or immediates is kept** by a state whose private
memory agrees on `A` (a callee's run keeping the caller's cells). -/
theorem FramesPlacedInI.of_eq {A : Nat → Prop} (h : FramesPlacedInI Λ lbl s fs A)
    (hA : ∀ a, A a → (machine (kernel 1)).privLoad s' (BitVec.ofNat 64 a) =
      (machine (kernel 1)).privLoad s (BitVec.ofNat 64 a)) :
    FramesPlacedInI Λ lbl s' fs A := by
  obtain ⟨envm, hrep, htot, hin, himm⟩ := h
  exact ⟨envm, fun d f hf x ty ws hx k wd wp hwd hwp =>
    wordPlaceRep_of_eqI hA (hin d x k wp hwp) (hrep d f hf x ty ws hx k wd wp hwd hwp), htot, hin, himm⟩

/-- **Placed in slots or immediates is kept by a callee** whose state keeps
the caller's cells outside its region (`CKept`, `Spike/Lib/X64Call.lean`),
every slot of `A` such a cell. -/
theorem FramesPlacedInI.of_cKept {A : Nat → Prop} {R : Spike.Lib.Region} {kb lo' hi' : Int}
    (h : FramesPlacedInI Λ lbl s fs A) (hk : Spike.Lib.X64.CKept R kb lo' hi' s.st.1 s'.st.1)
    (hA : ∀ a, A a → ∃ k, R.Off k ∧ ¬ (R.callee kb lo' hi').Off (k - kb) ∧ a = (R.addr k).toNat) :
    FramesPlacedInI Λ lbl s' fs A :=
  h.of_eq fun a ha => by
    obtain ⟨k, hk1, hk2, rfl⟩ := hA a ha
    show Scc.Sem.X64.privLoad s' _ = Scc.Sem.X64.privLoad s _
    simp only [Scc.Sem.X64.privLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq, hk k hk1 hk2]

/-! ## The caller's frame pushed -/

/-- **A control placed in the slots of `A` or at immediates** the layout
has at the term `t` (at a call, the continuation): the caller at a call, its
words in its frame's slots. -/
def SlotPlacedI (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (c : Ctl) (A : Nat → Prop) (t : Expr) : Prop :=
  ∃ envm : String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
    (∀ x ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k wd wp, ws[k]? = some wd → envm x k = some wp →
      WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
    (∀ x ∈ exprFv c.term, ∀ ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k < ws.length,
      ∃ pl, envm x k = some pl) ∧
    (∀ x k wp, envm x k = some wp → InSlotsI A wp) ∧
    (∀ x k n, envm x k = some (.imm n) → Λ.imms t x k = some n)

/-- **The caller's frame pushed at a call**: a control placed in the slots
of `A` or at the immediates of its continuation `e` at `let x = op in e`,
and the suspended frames placed there, place the frames with the caller's
continuation (in the caller's environment, returning into `x`) pushed. -/
theorem FramesPlacedInI.push {A : Nat → Prop} {x : String} {op : Op} {e : Expr}
    (hc : SlotPlacedI Λ lbl s c A e) (hf : FramesPlacedInI Λ lbl s fs A)
    (ht : c.term = .let_ x op e) {fr : TermRun.Frame} (hx : fr.x = x) (hb : fr.body = e) (he : fr.env = c.env) :
    FramesPlacedInI Λ lbl s (fr :: fs) A := by
  obtain ⟨envc, hrepc, htotc, hinc, himc⟩ := hc
  obtain ⟨envf, hrepf, htotf, hinf, himf⟩ := hf
  refine ⟨fun d => match d with | 0 => envc | d + 1 => envf d, ?_, ?_, ?_, ?_⟩
  · intro d f hfd y ty ws hy k wd wp hwd hwp
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      rw [he] at hy
      exact hrepc y ty ws hy k wd wp hwd hwp
    · exact hrepf d f (by simpa using hfd) y ty ws hy k wd wp hwd hwp
  · intro d f hfd y hy ty ws hl k hk
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      rw [he] at hl
      refine htotc y ?_ ty ws hl k hk
      rw [ht, exprFv]
      rw [hb, hx] at hy
      exact List.mem_append_right _ hy
    · exact htotf d f (by simpa using hfd) y hy ty ws hl k hk
  · intro d y k wp hwp
    rcases d with _ | d
    · exact hinc y k wp hwp
    · exact hinf d y k wp hwp
  · intro d f y k n hfd hwp
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      rw [hb]
      exact himc y k n hwp
    · exact himf d f y k n (by simpa using hfd) hwp

/-- **The frames at the callee's entry placed**: at a source call
(`SrcCallTo`, either ISA's `CallTo`) from a control placed in the slots of
`A` or at its continuation's immediates, with the caller's frames placed
there. -/
theorem framesPlaced_callTo {p : Prog} {A : Nat → Prop} {cE : Ctl} {fr : TermRun.Frame}
    (h : SrcCallTo p c cE fr) (hc : SlotPlacedI Λ lbl s c A fr.body) (hf : FramesPlacedInI Λ lbl s fs A) :
    FramesPlacedInI Λ lbl s (fr :: fs) A := by
  obtain ⟨x, f, a, e, d, t, ws, ht, -, -, -, rfl⟩ := h
  exact FramesPlacedInI.push hc hf ht rfl rfl rfl

/-! ## From the lowering's node invariant -/

/-- **The caller placed in its frame's slots or at immediates** from the
lowering's node invariant at the call: the symbolic environment `senv`
represents the source's in the slot file `sl`, every bound word is a
number, every free variable of the term is symbolic, each IR register's
cell loads its slot in `s` (`hcell`) at an address of `A` (`hA`), and the
immediates are the layout's at the continuation `t` (`himm`). -/
theorem slotPlacedI_of_srep {rs : Scc.IR.Reg → Option Int} {senv : SEnv} {sl : Int → BitVec 64}
    {addr : Int → BitVec 64} {A : Nat → Prop} {t : Expr}
    (hsr : SRep lbl (opdVal rs sl) senv c.env) (hnum : EnvNum c.env)
    (htot : ∀ y ∈ exprFv c.term, (lookupS senv y).isSome)
    (hcell : ∀ r k, rs r = some k → privLoad s (addr k) = some (sl k))
    (hA : ∀ r k, rs r = some k → A (addr k).toNat)
    (himm : ∀ x k v, (lookupS senv x).bind (·.2[k]?) = some (.one (.imm v)) → Λ.imms t x k = some v.toNat) :
    SlotPlacedI Λ lbl s c A t := by
  refine ⟨envmOf rs addr senv, fun x ty ws hl k wd wp hwd hem => ?_, fun x hx ty ws hl k hk => ?_,
    fun x k wp hem => ?_, fun x k n hem => ?_⟩
  · unfold envmOf at hem
    split at hem
    · next v hb =>
      cases hem
      obtain ⟨t, pls, hs, hpk⟩ : ∃ t pls, lookupS senv x = some (t, pls) ∧ pls[k]? = some (.one (.imm v)) := by
        cases h : lookupS senv x with
        | none => rw [h] at hb; cases hb
        | some p => rw [h] at hb; exact ⟨p.1, p.2, rfl, hb⟩
      obtain ⟨ws', hl', hW⟩ := hsr x t pls hs
      rw [hl] at hl'; cases hl'
      obtain ⟨v', hv', hR⟩ := wordsRep_get hW hwd hpk
      cases hv'; exact hR
    · next r hb =>
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hem
      obtain ⟨t, pls, hs, hpk⟩ : ∃ t pls, lookupS senv x = some (t, pls) ∧ pls[k]? = some (.one (.reg r)) := by
        cases h : lookupS senv x with
        | none => rw [h] at hb; cases hb
        | some p => rw [h] at hb; exact ⟨p.1, p.2, rfl, hb⟩
      obtain ⟨ws', hl', hW⟩ := hsr x t pls hs
      rw [hl] at hl'; cases hl'
      obtain ⟨v', hv', hR⟩ := wordsRep_get hW hwd hpk
      simp only [opdVal, hk', Option.map_some] at hv'
      cases hv'
      refine ⟨(sl k').toNat, ?_, hR⟩
      show (privLoad s (BitVec.ofNat 64 (addr k').toNat)).map (·.toNat) = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hcell r k' hk']; rfl
    · cases hem
  · obtain ⟨⟨t, pls⟩, hs⟩ := Option.isSome_iff_exists.mp (htot x hx)
    obtain ⟨ws', hl', hW⟩ := hsr x t pls hs
    rw [hl] at hl'; cases hl'
    have hlen := hW.length
    obtain ⟨pl, hpk⟩ : ∃ pl, pls[k]? = some pl := ⟨pls[k], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨wd, hwd⟩ : ∃ wd, ws[k]? = some wd := ⟨ws[k], List.getElem?_eq_getElem hk⟩
    have hR := wordsRep_get hW hwd hpk
    obtain ⟨n, hn, -⟩ := hnum _ (mem_of_lookupE hl) wd (List.mem_of_getElem? hwd)
    unfold envmOf
    rw [hs]
    simp only [Option.bind_some, hpk]
    cases pl with
    | one o =>
      cases o with
      | imm v => exact ⟨_, rfl⟩
      | reg r =>
        obtain ⟨v, hv, -⟩ := hR
        simp only [opdVal] at hv
        obtain ⟨k', hk', -⟩ := Option.map_eq_some_iff.mp hv
        simp only [hk', Option.map_some]
        exact ⟨_, rfl⟩
    | loc b off =>
      obtain ⟨vb, vo, -, -, hL⟩ := hR
      rw [hn] at hL
      cases hL
  · unfold envmOf at hem
    split at hem
    · cases hem; intro pl hpl; simp [WordPlace.places] at hpl
    · next r hb =>
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hem
      intro pl hpl
      simp only [WordPlace.places, List.mem_singleton] at hpl
      exact ⟨_, hpl, hA r k' hk'⟩
    · cases hem
  · unfold envmOf at hem
    split at hem
    · next v hb => cases hem; exact himm x k v hb
    · next r hb =>
      obtain ⟨k', -, he⟩ := Option.map_eq_some_iff.mp hem
      cases he
    · cases hem

end Spike.Lib.X64ConsumerS
