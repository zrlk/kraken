/-
**hello.w: main's source before its `spawn`** (the source part of the
pre-spawn main, `ClonePre`'s twin): from the setup block's return into
`main` (`SrcCalls.setup_ret_src`, landing at `mainC`) through `split a sl
me`, `let z = zero int`, to the box's `new` (`c0H`, the allocation's
control as in `WakeC0.c0W`); past the `new`, the publication `c = publish
o`, then `p0 = (sl, c)` and `p = (p0, me)` to the `spawn` (`spawnTermH`).

- `slTy`, `pktTy`, `mainArgTy`: the slice's, the spawn packet's and
  `main`'s argument types; `spawnTermH` … `mainBodyH`: `main`'s body and
  its tails; `main_find`: `main` in `helloSrc`.
- `SlRep lbl ws w0 w1 w2 w3`: the slice's three source words `ws` against
  the four registers the lowered code passes (`wc_rodata`'s `x0`–`x3`:
  the buffer's address, the constant `0`, `2`, `13`; the `0` is no source
  word, as in `A64Hello1RodataSetup.rdPostS`); `SlRep.valRep`.
- `mainC`, `c0H`, `c0H_run`: `main`'s entry on the slice and `me`, and
  the local run to the `new` (`split`, `zero`); `c0H_term`, `c0H_z`,
  `c0H_me`, `c0H_sl`.
- `boxPubCtlH`, `boxPubH`: the publication at `boxTermH` (`PubStep .st`).
- `SpawnSrcH l ws c`: main at `spawnTermH` with `c`, `me`, `sl` and the
  packet `p` bound; `src_spawnH`: from `boxTermH` the fence's run
  (`FenceRun.pub`) reaches it.
-/
import Spike.Lib.HelloRodataSrc
import Spike.Lib.SrcFrames

namespace Spike.Lib.HelloMainPreSrc

open CoreLang CoreTerm TermRun
open Spike.Lib (Ctl LocalStepS LocalRunS PubStep FenceRun)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloRodataSrc (sliceTyP)
open Spike.Lib.WakeT1 (mainTidLbl)
open Scc.Sem (ValRep)

/-! ## The terms -/

/-- The slice's type, `∃ m. (([u8; m] pub, m), Int)`. -/
abbrev slTy : Ty := .iex sliceTyP

/-- The spawn packet's type, `((slice, flag), ThreadId)`. -/
abbrev pktTy : Ty := .prod (.prod slTy (.ptr .pub .int)) .tid

/-- `main`'s argument type, `(slice, ThreadId)`. -/
abbrev mainArgTy : Ty := .prod slTy .tid

/-- **main's term at the `spawn`**: `let t = spawn worker p in tail waitLoop c`. -/
def spawnTermH : Expr :=
  .let_ "t" (.spawn "worker" (.var "p") pktTy []) (.tail "waitLoop" [] (.var "c") [])

def pTerm : Expr := .let_ "p" (.pair (.var "p0") (.var "me")) spawnTermH
def p0Term : Expr := .let_ "p0" (.pair (.var "sl") (.var "c")) pTerm

/-- **main's term past the box's `new`**: `let c = publish o in …`. -/
def boxTermH : Expr := .let_ "c" (.publish (.var "o")) p0Term

/-- **main's term at the box's `new`**. -/
def newTerm : Expr := .let_ "o" (.new (.var "z") (some .int)) boxTermH

def zTerm : Expr := .let_ "z" (.zero .int) newTerm

/-- `main`'s body in hello.w. -/
def mainBodyH : Expr := .split (.var "a") "sl" "me" zTerm

/-- `main` in `helloSrc`. -/
def mainD : Decl :=
  { name := "main", tparams := [], idx := [], arg := "a", argTy := mainArgTy, retTy := .int, body := mainBodyH }

theorem main_find : helloSrc.find? (·.name == "main") = some mainD := rfl

/-! ## The slice's words against the registers -/

/-- **The slice's words at the four registers**: the source slice `ws` is
`[b, 2, 13]`, `b` the start of a label `l` placed at `w0`; the registers
are `w0`, `0`, `2`, `13` (`wc_rodata`'s return, `movz x1, #0`: the `0` is no
source word). -/
def SlRep (lbl : WeakMem.AllocLabel → Option Nat) (ws : List Word) (w0 w1 w2 w3 : Nat) : Prop :=
  ∃ l, ws = [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)] ∧ lbl l = some w0 ∧ w1 = 0 ∧ w2 = 2 ∧ w3 = 13

/-- **`SlRep`'s word representations**: the buffer at `w0`, `m` at `w2`,
`n` at `w3`. -/
theorem SlRep.valRep {lbl : WeakMem.AllocLabel → Option Nat} {ws : List Word} {w0 w1 w2 w3 : Nat}
    (h : SlRep lbl ws w0 w1 w2 w3) :
    ∃ b m n, ws = [b, m, n] ∧ ValRep lbl b.val w0 ∧ ValRep lbl m.val w2 ∧ ValRep lbl n.val w3 := by
  obtain ⟨l, rfl, hl, -, rfl, rfl⟩ := h
  refine ⟨_, _, _, rfl, ⟨by decide, w0, ?_, rfl⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩
  simp [Scc.Sem.wordAddr, hl]

/-! ## From `main`'s entry to the `new` -/

/-- **`main`'s entry** on the slice's words `w0 w1 w2` and `me`'s word `mw`
(the setup block's return, `SrcCalls.setup_ret_src`'s landing). -/
def mainC (w0 w1 w2 mw : Word) : Ctl := ⟨mainBodyH, [("a", mainArgTy, [w0, w1, w2, mw])], none⟩

/-- The environment after `split a sl me`. -/
def envS (w0 w1 w2 mw : Word) : Env :=
  [("me", .tid, [mw]), ("sl", slTy, [w0, w1, w2]), ("a", mainArgTy, [w0, w1, w2, mw])]

/-- **main's control at the box's `new`**: `let o = new z in boxTermH`, `z`
the zero word (the allocation's control, as `WakeC0.c0W`). -/
def c0H (w0 w1 w2 mw : Word) : Ctl := ⟨newTerm, ("z", .int, [cst (.num 0)]) :: envS w0 w1 w2 mw, none⟩

theorem c0H_term (w0 w1 w2 mw : Word) : (c0H w0 w1 w2 mw).term = .let_ "o" (.new (.var "z") (some .int)) boxTermH := rfl

theorem c0H_z (w0 w1 w2 mw : Word) : lookupE (c0H w0 w1 w2 mw).env "z" = some (.int, [cst (.num 0)]) := rfl

theorem c0H_me (w0 w1 w2 mw : Word) : evalAt (c0H w0 w1 w2 mw).env (.var "me") = some (.tid, [mw]) := rfl

theorem c0H_sl (w0 w1 w2 mw : Word) : evalAt (c0H w0 w1 w2 mw).env (.var "sl") = some (slTy, [w0, w1, w2]) := rfl

theorem step_split (w0 w1 w2 mw : Word) {p : Prog} :
    LocalStepS p (mainC w0 w1 w2 mw) ⟨zTerm, envS w0 w1 w2 mw, none⟩ :=
  localStepS_split (c := mainC w0 w1 w2 mw) (x := "sl") (y := "me") (e := zTerm) (a := .var "a") (u := slTy)
    (v := .tid) (ws := [w0, w1, w2, mw]) (us := [.one, .one, .one]) rfl rfl rfl

theorem step_z (w0 w1 w2 mw : Word) {p : Prog} : LocalStepS p ⟨zTerm, envS w0 w1 w2 mw, none⟩ (c0H w0 w1 w2 mw) := by
  refine ⟨rfl, fun g mem pairs th hg ht he hσ => ?_⟩
  obtain ⟨t, e, σs⟩ := th
  simp only at ht he hσ; subst ht he hσ
  rw [TermLocal.tstep_let_gen rfl rfl]
  simp [TermRun.evalOp, TermRun.ol, TermRun.close, TermRun.zeroWords, TermRun.withS, TermRun.stOf, c0H,
    TermStep.substTs_nil']

/-- **`main`'s entry runs locally to the `new`**: the `split`, then `let z =
zero int`. -/
theorem c0H_run {p : Prog} (w0 w1 w2 mw : Word) : LocalRunS p (mainC w0 w1 w2 mw) (c0H w0 w1 w2 mw) :=
  .step (step_split w0 w1 w2 mw) (.step (step_z w0 w1 w2 mw) (.refl _))

/-! ## From the box to the `spawn` -/

/-- The source past the publication at `boxTermH`: `c` bound to the box's
published locative. -/
def boxPubCtlH (c : Ctl) (ty : Ty) (l : WeakMem.AllocLabel) : Ctl :=
  ⟨p0Term, ("c", .ptr .pub ty, [cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩

/-- **The publication step at `boxTermH`** (`PubStep .st`): `o` bound to the
box's owned locative, no hold. -/
theorem boxPubH {c : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} (ht : c.term = boxTermH) (hh : c.hold = none)
    (ho : evalAt c.env (.var "o") = some (.ptr .own ty, [cst (.loc ⟨l, 0⟩ 0)])) :
    PubStep .st c (boxPubCtlH c ty l) :=
  ⟨.inl rfl, hh, "c", .var "o", _, .ptr .own ty, .ptr .pub ty, _, .inl ⟨ht, rfl⟩, ho, rfl⟩

/-- **main's source at the `spawn`**: `c` the box's published locative, `me`
main's `ThreadId`, `sl` the slice's words `ws` and the packet `p` their
concatenation. -/
def SpawnSrcH (l : WeakMem.AllocLabel) (ws : List Word) (c : Ctl) : Prop :=
  c.term = spawnTermH ∧ c.hold = none ∧
    evalAt c.env (.var "c") = some (.ptr .pub .int, [cst (.loc ⟨l, 0⟩ 0)]) ∧
    evalAt c.env (.var "me") = some (.tid, [cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) ∧
    evalAt c.env (.var "sl") = some (slTy, ws) ∧
    evalAt c.env (.var "p") = some (pktTy, ws ++ [cst (.loc ⟨l, 0⟩ 0), cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])

/-- **main's source from the box to the `spawn`**: at `boxTermH` with `o`
bound to `l`'s owned locative, `me` to main's id and `sl` to the slice's
words, the fence's publication (`c = publish o`) and the two pairs reach
`spawnTermH`. -/
theorem src_spawnH {p : Prog} {P : Prop} (hP : P) {c : Ctl} {l : WeakMem.AllocLabel} {ws : List Word}
    (ht : c.term = boxTermH) (hh : c.hold = none)
    (ho : evalAt c.env (.var "o") = some (.ptr .own .int, [cst (.loc ⟨l, 0⟩ 0)]))
    (hme : evalAt c.env (.var "me") = some (.tid, [cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (hsl : evalAt c.env (.var "sl") = some (slTy, ws)) :
    ∃ c', FenceRun p P .st c c' ∧ SpawnSrcH l ws c' := by
  have hc : evalAt (boxPubCtlH c .int l).env (.var "c") = some (.ptr .pub .int, [cst (.loc ⟨l, 0⟩ 0)]) := by
    simp [boxPubCtlH, evalAt, lookupE]
  have hs1 : evalAt (boxPubCtlH c .int l).env (.var "sl") = some (slTy, ws) := by
    simpa [boxPubCtlH, evalAt, lookupE] using hsl
  have hm1 : evalAt (boxPubCtlH c .int l).env (.var "me") = some (.tid, [cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := by
    simpa [boxPubCtlH, evalAt, lookupE] using hme
  have s1 := Spike.Lib.Form.localStep_pair (p := p) (c := boxPubCtlH c .int l) rfl hs1 hc
  have hp0 : evalAt (("p0", .prod slTy (.ptr .pub .int), ws ++ [cst (.loc ⟨l, 0⟩ 0)]) ::
      (boxPubCtlH c .int l).env) (.var "p0") = some (.prod slTy (.ptr .pub .int), ws ++ [cst (.loc ⟨l, 0⟩ 0)]) := by
    simp [evalAt, lookupE]
  have hm2 : evalAt (("p0", .prod slTy (.ptr .pub .int), ws ++ [cst (.loc ⟨l, 0⟩ 0)]) ::
      (boxPubCtlH c .int l).env) (.var "me") = some (.tid, [cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := by
    simpa [evalAt, lookupE] using hm1
  have s2 := Spike.Lib.Form.localStep_pair (p := p) (c := ⟨pTerm, ("p0", .prod slTy (.ptr .pub .int),
    ws ++ [cst (.loc ⟨l, 0⟩ 0)]) :: (boxPubCtlH c .int l).env, none⟩) rfl hp0 hm2
  refine ⟨_, .pub hP (boxPubH ht hh ho) (.step s1 (.single s2)), rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [evalAt, lookupE] using hc
  · simpa [evalAt, lookupE] using hm1
  · simpa [evalAt, lookupE] using hs1
  · simp [evalAt, lookupE]

end Spike.Lib.HelloMainPreSrc

/-- info: 'Spike.Lib.HelloMainPreSrc.c0H_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainPreSrc.c0H_run

/-- info: 'Spike.Lib.HelloMainPreSrc.src_spawnH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainPreSrc.src_spawnH

/-- info: 'Spike.Lib.HelloMainPreSrc.SlRep.valRep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainPreSrc.SlRep.valRep
