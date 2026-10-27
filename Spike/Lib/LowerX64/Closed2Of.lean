/-
**The x86-64 `Accepted2` compiler theorem from its remaining obligations**
(`x64_scc_correctE_text_closedAt2_of`): `Closed2Stmt` from `Closed2Rest`,
the premises of the start-generic arena consumer (`correctKOnA'`) that the
placement check, the lowering and the acceptance do not already give,
at each instance and admissible entry state.

The start is the program's (`start2`): before the setup block
(`setupStart 1 meW`) with a setup block, else `main` on a unit argument;
`me`'s word is the first TCB, `scc_rt_pinned + 8` (`meW2`). The rest is
discharged here at any layout passing `placeOKAt`: the parse, the image,
the load, no static label, the wide encodings, the hooks (`hookOK_srcP1o`),
the start (`startOk2`, `progInit2`), the arena `arOf` (`hok`, `hsub`, `hal`;
zero at load, `hz0`, `hc0`), and the source's safety at every start
(`srcSafeS_srcP1oX`).

- `meW2`, `start2`, `th02`: the start, its word for `me`, its thread.
- `startOk2`, `progInit2`: `StartOk` and the source's start.
- `Obl2X`: the remaining premises at a frame invariant `I`, a value
  invariant `G`, owned words `own`, the take's range and phase `rS`/`Tk`
  and the abort phase `Ab`, and the node obligations' abort predicate `ab`
  (`none` without `print`, else `some` with `Print2X`).
- `Rest2X`: some such seven at an output and entry state; `Closed2Rest`: at
  every instance.
- `Print2X`: the `print` premises at a fragment with an abort
  predicate for the node obligations (the extern present, `correctKOnAEP`'s `hsv`).
- `hnum2`: the printed cells hold numbers, from `placeOKAt` and `Accepted2`.
- `hd2`: with the extern, `printL` is `printLD`, from `placeOKAt` and `Accepted2`.
- `correct2_of`: `Correct` on the parsed output from `Rest2X`, at any
  output passing `placeOKAt` with `CtrZ`.
- `x64_scc_correctE_text_closedAt2_of`: `Closed2Rest → Closed2Stmt`.
-/
import Spike.Lib.LowerX64.Closed2Stmt
import Spike.Lib.X64ConsumerAStart
import Spike.Lib.X64WriteDead
import Spike.Lib.X64ConsumerAEPrint
import Spike.Lib.Src.Accepted2Out
import Spike.Lib.Src.SrcNumStart
import Spike.Lib.Src.PrintCallSrc
import Spike.Lib.LowerX64.NumQOfPlaceOK
import Spike.Lib.Src.NJLS
import Spike.Lib.Src.SrcSafe2X
import Spike.Lib.Rt.X64ArenaOfPlaceOK
import Spike.Lib.Rt.X64CtrZOfEmitted
import Spike.Lib.X64Ret0
import Spike.Lib.X64Correct
import Spike.Lib.X64StartOfPlaceOK

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA

/-! ## The start -/

/-- **`me`'s word at the start**: the first TCB, `scc_rt_pinned + 8` in the
canonical link, as a number. -/
def meW2 (Λ : Scc.Sem.Layout) (o : Scc.Cert.PlaceOK.X64.Out) : TermRun.Word :=
  Spike.Lib.LowerNode.meNum
    (Spike.Lib.X64.Flow.Ret0.tpOf (Scc.Cert.Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned" + 8#64)).toNat

/-- **The program's start**: before the setup block with one, else `main`
on a unit argument; one label stripe. -/
def start2 (p : Prog) (meW : TermRun.Word) : TermRun.Cfg :=
  match Scc.Lower.setupOf p with
  | some _ => SrcSem.setupStart 1 meW
  | none => { SrcSem.mainStart with cap := 1 }

/-- The start's thread. -/
def th02 (p : Prog) (meW : TermRun.Word) : TermRun.TTh :=
  match Scc.Lower.setupOf p with
  | some _ => { term := SrcSem.setupTerm, env := [("me", .ptr .pub .void, [meW]), ("u", .unit, [])] }
  | none => { term := c0.term, env := c0.env }

/-- The program's start is a start (`StartOk`) at its thread. -/
theorem startOk2 (p : Prog) (meW : TermRun.Word) : StartOk (start2 p meW) (th02 p meW) := by
  unfold start2 th02
  cases Scc.Lower.setupOf p <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The program's start is the source's (`progInit`), for an `Accepted2`
program. -/
theorem progInit2 {p : Prog} (hA : Scc.Lower.Accepted2 p = true) (meW : TermRun.Word) :
    SrcSem.progInit p 1 (start2 p meW) := by
  unfold start2
  cases hs : Scc.Lower.setupOf p with
  | some _ => rw [Spike.Lib.LowerNode.progInit_of_setupOf_some hs]; exact ⟨meW, rfl⟩
  | none => rw [Spike.Lib.LowerNode.progInit_of_setupOf_none hA hs]; rfl

/-- With a setup block, every start of `srcP1o arch p` is before it. -/
theorem init_setup2 {p : Prog} {s : Ty} (hs : Scc.Lower.setupOf p = some s) (arch : WeakMem.Arch) :
    ∀ c, (SrcSem.srcP1o arch p).init c → ∃ meW, c = SrcSem.setupStart (SrcSem.srcP1o arch p).cap meW := by
  intro c hc
  change SrcSem.progInit p 1 c at hc
  rw [Spike.Lib.LowerNode.progInit_of_setupOf_some hs] at hc
  exact hc

/-! ## The remaining obligations -/

/-- **The `print` premises** of `correctKOnAEP` at source parameters `P`,
program `p` and frame invariant `I`, for node obligations at an abort
predicate `ab`: `ab` is some predicate, the program has the output extern
(`hext`), the source is at `print`'s loop top at every pair at an output
`write(1, …)` (`hsv`, `Svc1S I`). `hnum` and `hd` are not ones:
`correct2_of` takes them (`hd` under `hext`), `closedAt2_of` gives them
(`hnum2`, `hd2`). -/
structure Print2X (P : SrcSem.SrcParams) (p : Prog) (I : InvS) (ab : Option (State → Prop)) : Prop where
  /-- The node obligations carry an abort predicate. -/
  hsome : ab.isSome = true
  /-- The program has the output extern. -/
  hext : Scc.Lower.hasPrint p = true
  /-- The source at `print`'s loop top at every output `write(1, …)` (`Svc1S I`). -/
  hsv : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true → ∀ b n,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 b n) → Spike.Lib.PrintSvc.PrintSvc c fs

/-- **The premises of `correctKOnA'` / `correctKOnAEP` left open** at a layout `Λ`, source
parameters `P`, program `p`, marks `μ`, loaded thread `s`, start thread
`th0` and arena `ar`, for a frame invariant `I`, a value
invariant `G`, owned words `own`, the take's range and phase `rS`/`Tk`
and the abort phase `Ab`, the node obligations at the abort predicate
`ab`: `none` (`correctKOnA'`) or `some` with the `print` premises
(`Print2X`, `correctKOnAEP`). -/
structure Obl2X (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (μ : Marks) (s : State)
    (th0 : TermRun.TTh) (ar : Arena) (I : InvS) (G : Loc → Val → Prop) (own : OwnS)
    (rS : Range) (Tk Ab : State → Prop) (ab : Option (State → Prop)) : Prop where
  /-- The loaded thread at the start's pair, no hold, no frame. -/
  hst : I Λ.static (fun _ => 0) s ⟨th0.term, th0.env, none⟩ []
  /-- The nodes of the run. -/
  hN : NodesA Λ p μ Spike.Lib.LowerNode.IsNum G own ar I ab
  /-- Without `print`, or the `print` premises. -/
  hpr : ab = none ∨ Print2X P p I ab
  /-- The take's path. -/
  hT : TakePathS Λ p μ I rS Tk
  /-- The loaded thread is off the take. -/
  htk0 : ¬ Tk s
  /-- The abort's path. -/
  hA : AbortPathS μ I Ab ar.cells ar.ctr
  /-- The loaded thread is off the abort. -/
  hab0 : ¬ Ab s

/-- The layout of the theorem: no static label, the lowering's immediates
with the first TCB for `me` at the setup start (`imms2Me`). -/
abbrev lay2 (Λ : Scc.Sem.Layout) (p : Prog) : Scc.Sem.Layout :=
  { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p }

/-- The parsed output, as the target on parsed texts takes it. -/
abbrev asm2 (o : Scc.Cert.PlaceOK.X64.Out) : List (Directive × Nat) × DataSecs × List (String × Nat) :=
  (o.prog, o.secs, o.labelOffs)

/-- **The value invariant** at an output `o` passing `placeOKAt` at `Λ`: the
first TCB's limit word holds its loaded value or the limit (`GOf` at the
runtime's layout at the lowering's immediates). -/
def G2 {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}
    (h : placeOKAt pcfg Λ o = true) (p : Prog) : Loc → Val → Prop :=
  Spike.Lib.X64.PhRec.GOf (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (LowerNode.imms2Me Λ p))
    (Spike.Lib.X64.PhRec.m0Of (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (LowerNode.imms2Me Λ p)).Λ o.prog o.secs)

/-- **The owned words**: the runtime's counters its pc's phase owns
(`PhRec.own`), independent of the frames. -/
def own2 {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}
    (h : placeOKAt pcfg Λ o = true) (p : Prog) : OwnS :=
  fun s _ => Spike.Lib.X64.PhRec.own (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (LowerNode.imms2Me Λ p)) s

/-- **The open premises at an output `o` passing `placeOKAt` (`h`) and an
entry state `E`**: some `I`, `rS`/`Tk`, `Ab`, `ab` with `Obl2X` at the layout `Λ`,
`srcP1o arch p`, the marks of the parsed output at `E`, its loaded
thread, the program's start (`th02` at `meW2`), the allocator's arena
`arOf`, the value invariant `G2` and the owned words `own2`. -/
def Rest2X {pcfg : Scc.Cert.PlaceOK.Config} (Λ : Scc.Sem.Layout) (p : Prog) {o : Scc.Cert.PlaceOK.X64.Out}
    (h : placeOKAt pcfg Λ o = true) (arch : WeakMem.Arch) (E : Entry) : Prop :=
  ∃ (I : InvS) (rS : Range) (Tk Ab : State → Prop) (ab : Option (State → Prop)),
    Obl2X Λ (SrcSem.srcP1o arch p) p ((TParE E).marks (asm2 o) Λ)
      (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)) (th02 p (meW2 Λ o))
      (Spike.Lib.X64.Rt.arOf Λ) I (G2 h p) (own2 h p) rS Tk Ab ab

/-- **The open premises of the `Accepted2` theorem**: `Rest2X` at every
instance of `Closed2Stmt` and every admissible entry state. -/
def Closed2Rest : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true → ∀ (arch : WeakMem.Arch) (E : Entry), E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    Rest2X (lay2 Λ p) p h' arch E

open Scc.Cert.Link Scc.Cert.Link.X64 in
/-- **`Correct` on the parsed output from the open premises**, at an
output `o` passing `placeOKAt` at `Λ` with the counter's zero word
(`CtrZ`), for an `Accepted2` program whose printed cells hold numbers
(`hnum`) and whose extern's loop, with the extern, is `printLD` (`hd`),
whose reads are numbers (`hrdN`, the world's `rd`; see `hrd2`), at
an admissible entry state:
`correctKOnA'` (no abort predicate for the node obligations) or
`correctKOnAEP` (with one, the `print` premises `Print2X`) at the start
`start2` at `meW2`, the arena `arOf`. -/
theorem correct2_of {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
    {o : Scc.Cert.PlaceOK.X64.Out} (hp : Scc.Lower.Accepted2 p = true) (h : placeOKAt pcfg Λ o = true)
    (hc : Spike.Lib.X64.Rt.CtrZ o) {B : Budget} (hB : B.cells = allocCells) {arch : WeakMem.Arch} {E : Entry}
    (hE : E.Ok (lay2 Λ p))
    (hnum : Spike.Lib.LowerNode.SrcNumSP (SrcSem.srcP1o arch p) p Spike.Lib.LowerNode.PrintLd)
    (hd : Scc.Lower.hasPrint p = true → p.find? (·.name == "printL") = some Spike.Lib.PrintSrc.printLD)
    (hrdN : SrcRd (SrcSem.srcP1o arch p) p Spike.Lib.LowerNode.IsNum)
    (R : Rest2X (lay2 Λ p) p h arch E) :
    Correct (TParE E) (SrcSem.source (SrcSem.srcP1o arch p) p) (lay2 Λ p) B (asm2 o) := by
  obtain ⟨I, rS, Tk, Ab, ab, R⟩ := R
  have h' : placeOKAt pcfg (lay2 Λ p) o = true := h
  have hpc := Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h' (LowerNode.imms2Me Λ p) E
  have he := loadParsed_of_loadOk (H := kernel 1) (loadOk_link_of_placeOKAt (i := LowerNode.imms2Me Λ p) h') hE.1
  cases ab with
  | none =>
    exact correctKOnA' (ld := (TParE E).load) (rs := (TParE E).resolve) (asm := asm2 o)
      (lsize := fun _ => 0) (name := fun _ => "") (rd := Spike.Lib.LowerNode.IsNum) hB rfl
      (imageIn_link_of_placeOKAt (i := LowerNode.imms2Me Λ p) h') (StaticSyms.of_none fun _ => rfl)
      (wideIn_of_placeOKAt h') (startOk2 p _) R.hst (AllocInv.FreshInv.init _ _ 0) ⟨_, he⟩
      (Spike.Lib.LowerNode.hookOK_srcP1o hp arch) (progInit2 hp _) R.hN
      (Spike.Lib.LowerNode.srcSafeS_srcP1oX hp arch I) R.hT R.htk0
      (Spike.Lib.X64.PhRec.hown0_ofPlaceOKE h' _ hE.1
        (Spike.Lib.X64.PhRec.hph0_of h' _ hpc (Spike.Lib.X64.PhRec.hph0_ofPlaceOK h' _))) (writeNoPromA_b R.hN R.hT)
      hrdN (wf_link_of_placeOKAt (i := LowerNode.imms2Me Λ p) h')
      (Spike.Lib.X64.PhRec.G0_ofPlaceOKE h' _ hE.1)
      (Spike.Lib.X64.PhRec.hGpl_ofPlaceOK h' _ (Spike.Lib.X64.PhRec.hclr_ofPlaceOK h' _)) R.hA R.hab0
      (Spike.Lib.X64.Rt.arOf_ok h' hc) rfl (Spike.Lib.X64.Rt.arOf_sub h') (Spike.Lib.X64.Rt.arOf_al h')
      (fun t0 hl a ha => by
        change loadParsed (kernel 1) E (lay2 Λ p) o.prog o.secs o.labelOffs = some t0 at hl
        rw [he] at hl; cases hl; exact Spike.Lib.X64.Rt.arOf_z0 h' hc rfl ha)
      (fun t0 hl => by
        change loadParsed (kernel 1) E (lay2 Λ p) o.prog o.secs o.labelOffs = some t0 at hl
        rw [he] at hl; cases hl; exact Spike.Lib.X64.Rt.arOf_c0 h' hc rfl)
  | some Ab' =>
    have hq : Print2X _ _ I (some Ab') := R.hpr.resolve_left nofun
    exact correctKOnAEP (ld := (TParE E).load) (rs := (TParE E).resolve) (asm := asm2 o)
      (lsize := fun _ => 0) (name := fun _ => "") (rd := Spike.Lib.LowerNode.IsNum) hB rfl
      (imageIn_link_of_placeOKAt (i := LowerNode.imms2Me Λ p) h') (StaticSyms.of_none fun _ => rfl)
      (wideIn_of_placeOKAt h') (startOk2 p _) R.hst (AllocInv.FreshInv.init _ _ 0) ⟨_, he⟩
      (Spike.Lib.LowerNode.hookOK_srcP1o hp arch) (Spike.Lib.LowerNode.usesWc_srcP1o arch p) hnum
      (progInit2 hp _) R.hN (hd hq.hext) hq.hsv
      (Spike.Lib.LowerNode.srcSafeS_srcP1oX hp arch I) R.hT R.htk0
      (Spike.Lib.X64.PhRec.hown0_ofPlaceOKE h' _ hE.1
        (Spike.Lib.X64.PhRec.hph0_of h' _ hpc (Spike.Lib.X64.PhRec.hph0_ofPlaceOK h' _)))
      hrdN (wf_link_of_placeOKAt (i := LowerNode.imms2Me Λ p) h')
      (Spike.Lib.X64.PhRec.G0_ofPlaceOKE h' _ hE.1)
      (Spike.Lib.X64.PhRec.hGpl_ofPlaceOK h' _ (Spike.Lib.X64.PhRec.hclr_ofPlaceOK h' _)) R.hA R.hab0
      (Spike.Lib.X64.Rt.arOf_ok h' hc) rfl (Spike.Lib.X64.Rt.arOf_sub h') (Spike.Lib.X64.Rt.arOf_al h')
      (fun t0 hl a ha => by
        change loadParsed (kernel 1) E (lay2 Λ p) o.prog o.secs o.labelOffs = some t0 at hl
        rw [he] at hl; cases hl; exact Spike.Lib.X64.Rt.arOf_z0 h' hc rfl ha)
      (fun t0 hl => by
        change loadParsed (kernel 1) E (lay2 Λ p) o.prog o.secs o.labelOffs = some t0 at hl
        rw [he] at hl; cases hl; exact Spike.Lib.X64.Rt.arOf_c0 h' hc rfl)
      hE.1

/-- **The printed cells hold numbers** (`correct2_of`'s `hnum`) for an
`Accepted2` program whose lowering's output passes `placeOKAt` at some
layout: `srcNumS_of_accepted2P` with `numQ` and the setup result's words
from the placement check (`numQ_of_placeOK`, `setupValWords_of_placeOK`),
the start `progInit` and WeakCore's output hook (`usesWc_srcP1o`). -/
theorem hnum2 {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
    {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout} (hp : Scc.Lower.Accepted2 p = true)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (arch : WeakMem.Arch) :
    Spike.Lib.LowerNode.SrcNumSP (SrcSem.srcP1o arch p) p Spike.Lib.LowerNode.PrintLd :=
  Spike.Lib.LowerNode.srcNumS_of_accepted2P hp (numQ_of_placeOK h hp) (setupValWords_of_placeOK h hp)
    (fun _ hc => hc) (.inr (Spike.Lib.LowerNode.usesWc_srcP1o arch p))

/--
info: 'Spike.Lib.LowerX64.hnum2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hnum2

/-- **The source's reads are numbers** (`correct2_of`'s `hrdN`, the read
side of the world at `rd := IsNum`) for an `Accepted2` program whose
lowering's output passes `placeOKAt` at some layout: `srcRd_isNumP` with
`numQ` and the setup result's words from the placement check, the start
`progInit` and WeakCore's output hook, as `hnum2`. -/
theorem hrd2 {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
    {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout} (hp : Scc.Lower.Accepted2 p = true)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (arch : WeakMem.Arch) :
    SrcRd (SrcSem.srcP1o arch p) p Spike.Lib.LowerNode.IsNum :=
  Spike.Lib.LowerNode.srcRd_isNumP hp (numQ_of_placeOK h hp) (setupValWords_of_placeOK h hp)
    (fun _ hc => hc) (.inr (Spike.Lib.LowerNode.usesWc_srcP1o arch p))

/--
info: 'Spike.Lib.LowerX64.hrd2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hrd2

/-- **The extern's loop is `printLD`** (`correct2_of`'s `hd`) for an
`Accepted2` program with the output extern whose lowering's output passes
`placeOKAt` at some layout: `printL_of_accepted2` (`decl2` at `printL` with
the extern), the setup result's layout from the placement check
(`hset_of_valWords`, `setupValWords_of_placeOK`). -/
theorem hd2 {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
    {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (hp : Scc.Lower.Accepted2 p = true)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    Scc.Lower.hasPrint p = true → p.find? (·.name == "printL") = some Spike.Lib.PrintSrc.printLD :=
  Spike.Lib.LowerNode.printL_of_accepted2 hp
    (Spike.Lib.LowerNode.hset_of_valWords hp (setupValWords_of_placeOK h hp))

/--
info: 'Spike.Lib.LowerX64.hd2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hd2

open Scc.Cert.Link.X64 in
/-- **The x86-64 compiler theorem for an `Accepted2` program from its open
premises**: `Closed2Stmt` from `Closed2Rest`, by `correct2_of` on the
parsed output at each admissible entry state (`correct_of_parsed`), the
counter's zero word by `ctrZ_ofPlaceOK`, the printed cells by `hnum2`,
the extern's loop by `hd2`, the source's reads by `hrd2`. -/
theorem x64_scc_correctE_text_closedAt2_of (H : Closed2Rest) : Closed2Stmt := by
  intro cfg pcfg p sizes labelOffs Λ hp hR h hcfg text hpa B hB arch E hE
  obtain ⟨h1, h2⟩ := parsed_of_parsesTo hpa
  exact correct_of_parsed _ E h1 h2
    (correct2_of hp h (Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h) hB hE
      (hnum2 hp h arch) (hd2 hp h) (hrd2 hp h arch) (H cfg pcfg p sizes labelOffs Λ hp hR h hcfg arch E hE h))

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt2_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_text_closedAt2_of

end Spike.Lib.LowerX64
