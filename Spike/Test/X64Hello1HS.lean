/-
**`hello1`'s setup call `hS` at the setup call's known frame condition,
the pieces named** (x86-64; the twin of `Spike/Test/A64Hello1HS.lean`):
`hS_assembledB` (`Spike/Lib/LowerX64/HSAssembledB.lean`) with every input
the library gives filled in, for the `hS` the assembled start segment under
`h0In_setup_assembledBVB` needs (`HSBV`, `Spike/Test/X64Hello1ClosedBVB.lean`:
`SetupCallWSB` at `SetupGF`), at every choice of the bounds (`Bounds2`).

Closed here: the setup block's compiled index and return type
(`rodata_of_setupOf`, `rodata_compiled2`), its label, the start's call of
it (`callTo_setupTerm`, `CallTo.unique`), the limit word's facts (`hms`,
`hmr`, `hun`), `me`'s word (`hv`, `valRep_meW2_of_placeOKAt`), the stack's
range, `ProgNoS`; and in the callee's precondition: the context's stack
records at the bottom frame (`CxOkS.bot` from `SetupBot`, `setupBot_ofGF`),
the region's facts (`hF`, `hR`, `hlo`, `hhi`, `hR8`, `hl`, `hh`, `hFO` by
`stackOff_callee` twice: the switch region's callee, then the setup call's),
the ghosts (the controls a frame run reaches from the callee's entry), the
aborts (the abort node's states), the callee's `FrOk2` (`FrOk2.step` at the
call), the prologue edge (`CalleePre2R`'s `hedge`, `hS_assembledB`'s
premise).

Open (`SetupOpen`, at the setup block's compiled index `j` and a base context
`CxOk0`, the bottom keys the setup frame's `SetupBot`): the setup function's
segment `FnSpecC2` at `CxOkS … CxOk0 (SetupBot …) j`, the base context, the
setup function's construct blocks' jump and call targets off the write abort
(`hTg`), the buffer allocations' heap aborts' segment (`habA`), all at the
placement check's code facts at the theorem's immediates `imms2Me Λ p`
(`fnCode2OfPMe`, the `W2` instance's). Its parameter count, frame
(`Bounds2`'s frame row) and overflow stub (`posOff_proL_of_fnOk1`) come from
`fnCode2OfPMe_spec2`; the call by `hS_assembledBC` at `fnCode2OfPMe`. The
aborts' segment at the setup frame is closed for an addition-free setup block
(`hno`, `addFreeT`): no state is at its abort node (`abOf2_seg_addFree`).
The body's blocks inside `W2` (`CalleePre2R`'s `hW`, `hWp`) are
`cxBlk2_ofFn` in the rebased callee region (`rbR_facts`, `rbR_base`,
`stackOff_rbR`), the suspended start frame placed (`framesPlaced_setup`: its
only live word `me`'s at the immediate `imms2Me_setupK`), the ghosts'
`FrOk2` by `FrOk2.runM`, the return address
`scc_rt_main`'s marshalling block at `sp0` (`posOff_of_blockAtB`).

Unlike the AArch64 twin: the callee region is
`(RS v).callee (-8 - Z - 8 - 0) (-D1) 8` (the return address and the saved
`%rbp` pushed) and the body's blocks and abort node are at its rebased
`rbR` (`CalleePre2R`'s `hW`, `hWp`, `hab`); `hpre` has no alignment
premise, so the callee region's base's 8-alignment is derived from the
first stack's top and `setupMC_Z`; the bounds' room is `fS + 48 ≤ D1`
(`Bounds2`'s), not the need's.

- `CxBlk2`, `AbOf2`: a context's blocks inside `W` (`CalleePre2R`'s `hW`,
  `hWp`) and its abort node's states;
- `abOf2_seg_addFree`: at an addition-free block, the abort node's states
  are a segment to anything;
- `AbAl2`, `AbU2`: a context's buffer allocations' heap abort exits
  (`CxLB.hAb`'s premise), and its aborts, both kinds;
- `framesPlaced_setup`: the setup frame `[fr]` placed at any state;
- `cxBlk2_ofFn`: `CxBlk2` at `W2` from `cxBlk2_ofW2`
  (`Spike/Lib/LowerX64/CxBlk2Of.lean`);
- `SetupOpen`, `OpenS`: the open premises, at one choice and at every
  choice of the bounds;
- `hS_ofOpen`, `hSBV_ofOpenS`: `hS` from the open premises (`HSBV`);
- `hello1_hu`, `hello1_rodata_addFree`, `hello1_hS`: at `hello1o`.
-/
import Spike.Lib.LowerX64.HSAssembledB
import Spike.Lib.LowerX64.Start2C0
import Spike.Lib.LowerX64.SetupHCall
import Spike.Lib.LowerX64.SetupSw
import Spike.Lib.LowerX64.SetupTailOf
import Spike.Lib.LowerX64.StkOf
import Spike.Lib.LowerX64.UserLabs
import Spike.Lib.LowerX64.MainCode1
import Spike.Lib.LowerX64.HproOf
import Spike.Lib.LowerX64.FnCode2Me
import Spike.Lib.LowerX64.NewBufC2
import Spike.Lib.Src.AddFree
import Spike.Lib.LowerX64.CxBlk2Of
import Spike.Test.X64Hello1ClosedBVB

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open A9NoSpawn Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (LimOk WcG CallerCells limA)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2 addFreeT tailOf_addFree TailAt2)
open Spike.Lib.X64.Rt (SetupCode SetupCallWSB SetupGF SetupArgs swFSL rS0 rtF setupMC arOf)

section Ctx

variable {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}

/-- **A context's body blocks inside `W` at the frames `fs`**
(`CalleePre2R`'s `hW`, `hWp`, at the rebased region): every body and
pending node's block at a ghost in `G0`. -/
def CxBlk2 (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (c : FnCode2 exe cells endPc RaOk Cd i T d) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (G0 : Ctl → Prop) : Prop :=
  (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk →
    (fs = [] → ∀ a, t ≠ .ret a) →
    BlkW (fun s c => W s c fs) K exe endPc R F (bodyN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs) blk) ∧
  (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
    (fs = [] → ∀ a, t ≠ .ret a) →
    BlkW (fun s c => W s c fs) K exe endPc R F (pendN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs k) blk)

/-- **A context's abort node's states** at the frames `fs`, at a ghost in
`G0` (`CalleePre2R`'s `hab` by construction). -/
def AbOf2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (c : FnCode2 exe cells endPc RaOk Cd i T d)
    (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (G0 : Ctl → Prop) :
    FragS isa := fun s c' fs' =>
  fs' = fs ∧ ∃ c0, G0 c0 ∧
    Spike.Lib.X64.At exe endPc R F (abortN2 i T p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c'

/-- **A context's buffer allocations' heap abort exits** at the frames
`fs`: the states at the allocator's heap abort exit (`nbX … .abort`, the
jump to `scc_rt_abort`) from the context's region `R` at its frame, at any
call node invariant placing its controls (`NbJcOf`) and landing pc
(`CxLB.hAb`'s premise). -/
def AbAl2 (ms : List TermRun.Frame → MemSide isa) (lbl : WeakMem.AllocLabel → Option Nat)
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) :
    FragS isa := fun s c' fs' =>
  fs' = fs ∧ ∃ (Jc : Spike.Lib.X64.AS → Ctl → Prop) (pcR : Int64), NbJcOf i lbl c.fr Jc ∧
    Spike.Lib.X64.At exe endPc R F
      (Spike.Lib.X64.Flow.NewBuf.nbX (ms fs) (_root_.Executable.labels exe).label lbl R c.fr.size pcR Jc .abort)
      s c'

/-- **A context's aborts**: its abort node's states (`AbOf2`) and its buffer
allocations' heap abort exits (`AbAl2`). -/
def AbU2 (p : Prog) (ms : List TermRun.Frame → MemSide isa) (lbl : WeakMem.AllocLabel → Option Nat)
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (G0 : Ctl → Prop) : FragS isa := fun s c' fs' =>
  AbOf2 p lbl c R F fs fp ra G0 s c' fs' ∨ AbAl2 ms lbl c R F fs s c' fs'

/-- **A context's aborts at an addition-free block never end**: at the
`j`th compiled block, its body `addFreeT` (`hno`), no state is at its
abort node (its source controls are at an addition, `OvfReady`, on the
walk, `TailAt2`), so they are a segment to any `Q`. -/
theorem abOf2_seg_addFree {p : Prog} {j : Nat} (hno : addFreeT d.body = true)
    {c : FnCode2 exe cells endPc RaOk Cd i (TailAt2 p j) d} (hd : (compiled2 p)[j]? = some d)
    {W : FragS isa} {K : State → State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isa} {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {G0 : Ctl → Prop} {Q : FragS isa} :
    SegWS W K p lbl ms (AbOf2 p lbl c R F fs fp ra G0) Q := by
  refine SegWS.empty ?_
  rintro s c' fs' ⟨-, c0, -, -, -, -, -, σ, -, -, ⟨⟨sv, lits, hAb, -, -, -, hT⟩, -⟩, -⟩
  obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
  exact tailOf_addFree (hT d hd) hno x a b e he

open Spike.Lib.X64Consumer (Own Lbl Lsize) in
open Spike.Lib.X64ConsumerS (InvS) in
/-- **`CxBlk2` at `W2`** (`cxBlk2_ofW2` at `c`'s frame): the code facts'
blocks at `ra` inside `CdCLE` (`hCd`), at the write abort `Ab lab` and the
immediates `Λ.imms`. -/
theorem cxBlk2_ofFn [Kraken.Executable.ValidLayout exe] {lab : Label → Int64} {μ : Marks} {own : Own}
    {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    {Λ : Scc.Sem.Layout} {rS : Range} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    (hI : Spike.Lib.X64.Rt.InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hp : ProgNoS ZBad p) {RaOk' : BitVec 64 → Prop} {Cd' : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {T' : Expr → Prop} {d' : Decl} (c : FnCode2 exe cells endPc RaOk' Cd' Λ.imms T' d')
    {R : Region} {F : MachineData → Prop} (hFS : FStable R F) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -(c.fr.size : Int)) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64}
    (hCd : ∀ pc blk, Cd' ra pc blk → CdCLE cells okPc ph lab (Int64.ofBitVec ra) pc blk)
    (hraP : PosOff cells lab (Int64.ofBitVec ra))
    (hTg : ∀ pc blk, SubCd (Cd' ra) pc blk → Kind2 c.fr blk → ∀ k (hk : k < blk.length) L,
      (Spike.Lib.X64.classify blk[k].1 = some (.jmp L) ∨ Spike.Lib.X64.classify blk[k].1 = some (.call L) ∨
        ∃ cc, Spike.Lib.X64.classify blk[k].1 = some (.jcc cc L)) → PosOff cells lab (lab L)) :
    CxBlk2 (fun s c fs => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize s c fs) K p
      lbl lsize c R F fs fp ra G0 :=
  cxBlk2_ofW2 hI hpr habt hp c.hf c.h1 hFS hR hR8 hlo hhi hl hh hsub hfit hFO hfp hG0F hCd hraP hTg

end Ctx

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt
  (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
  (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s code facts'). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The setup call's segment's premises at the callee's frame condition
`F'`, ghost `g` and frame `fr` (`hS_assembledB`'s `hpre`'s), all of them. -/
local notation "PRE" F':max g:max fr:max => (RC).OK ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option hygiene false in
/-- The ghosts at the setup frame: the controls a frame run reaches from
the callee's entry `g.c0` at the frames `[fr]`. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
/-- The stack records' bottom keys at the setup frame: the setup frame's
(`SetupBot`), the only bottom the setup function's segment sees. -/
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
    ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec k fs

/-- **The setup frame is placed** at any state: the start's call of the
setup block leaves the frame `fr` (`callTo_setupTerm`), whose only live
word, `me`'s, is at the immediate `imms2Me_setupK` (the first TCB, which
the start's `me` word is, `valRep_meW2_of_placeOKAt`). The twin of the
AArch64 `framesPlaced_setup` (`Spike/Test/A64Hello1CxLBOf.lean`). -/
theorem framesPlaced_setup (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {cE : Ctl} {fr : TermRun.Frame} (hct : Spike.Lib.X64.Flow.CallTo p C0 cE fr) (s : State) :
    ∃ B, FramesPlacedInI (Ly).Λ (fun _ => none) s [fr] B := by
  obtain ⟨dr, hf, -⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hty
  have hc0 : C0 = Spike.Lib.Ctl.mk Scc.Sem.SrcSem.setupTerm [("me", .ptr .pub .void,
      [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)]), ("u", .unit, [])]
      none := by
    simp only [th02, hty]
  have hcall := callTo_setupTerm (p := p) (c0 := C0) (by rw [hc0]) (by rw [hc0]; rfl) hf
  obtain ⟨-, rfl⟩ := CallTo.unique hct hcall
  refine ⟨fun _ => False, fun d x k => if d = 0 ∧ x = "me" ∧ k = 0 then some (.imm ((lay2 Λ p).pinned.lo + 8))
    else none, ?_, ?_, ?_, ?_⟩
  · intro d f hfd y ty' ws hy k wd wp hwd hwp
    by_cases hc : d = 0 ∧ y = "me" ∧ k = 0
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      simp only [and_self, ite_true, Option.some.injEq] at hwp
      subst hwp
      simp [th02, hty, TermRun.lookupE] at hy
      obtain ⟨-, rfl⟩ := hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hwd
      subst hwd
      exact valRep_meW2_of_placeOKAt h (fun _ => none)
    · simp only [hc, ite_false] at hwp
      exact absurd hwp (by simp)
  · intro d f hfd y hy ty' ws hl k hk
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      have hme : y = "me" := by
        revert hy
        simp [Spike.Lib.LowerNode.setupRest, Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, Scc.Sem.atVars]
      subst hme
      simp [th02, hty, TermRun.lookupE] at hl
      obtain ⟨-, rfl⟩ := hl
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      exact ⟨_, if_pos ⟨rfl, rfl, rfl⟩⟩
    · simp at hfd
  · intro d x k wp hwp
    by_cases hc : d = 0 ∧ x = "me" ∧ k = 0
    · simp only [hc, and_self, ite_true, Option.some.injEq] at hwp
      subst hwp
      intro pl hpl
      simp [Scc.Sem.WordPlace.places] at hpl
    · simp only [hc, ite_false] at hwp
      exact absurd hwp (by simp)
  · intro d f x k n hfd hwp
    by_cases hc : d = 0 ∧ x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq, Scc.Sem.WordPlace.imm.injEq] at hwp
      subst hwp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      exact Spike.Lib.LowerNode.imms2Me_setupK hty
    · simp only [hc, ite_false] at hwp
      exact absurd hwp (by simp)

/-- **The setup frame's open premises** at the bounds `L`, `D1`, `fS`, the
invariant `J`, the top `v`, the setup block's compiled index `j` and a base
context `CxOk0`, the stack records' bottom keys the setup frame's (`SB`,
`SetupBot`, which `SetupGF` gives: `setupBot_ofGF`). Each names its
producer. -/
structure SetupOpen (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (CxOk0 : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop) : Prop where
  /-- The setup function's segment at the contexts with their stack records (from the program-wide
  `fnSpecC2_allI` at `CxOkS … CxOk0 (SB …)`, its construct premises: plain calls, lane stores, buffers
  through the allocator's `W2` instance, prints). -/
  hs : FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J)
    (CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ) CxOk0 (SB J v D1 fS) j)
    (fnCode2OfPMe hp h Λ j d hd)
  /-- The base context at the setup frame (the program-wide base context's producer). -/
  hcx : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    CxOk0 j (RC) F' [fr] g.fp g.ra TP0 (GR g fr)
      (AbU2 p (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr] g.fp g.ra (GR g fr))
  /-- The buffer allocations' heap aborts' segment at the setup frame (the jump to `scc_rt_abort` never
  ends inside `W2`). -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr]) (fun _ _ _ => False)
  /-- Every label a construct block of the setup function at the setup call's return address jumps or calls
  to is off the write abort (`cxBlk2_ofFn`'s `hTg`; decided at a concrete output). -/
  hTg : ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
      (Int64.ofBitVec ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec)) pc blk →
    Kind2 (fnCode2OfPMe hp h Λ j d hd).fr blk → ∀ k (hk : k < blk.length) L,
      (Spike.Lib.X64.classify blk[k].1 = some (.jmp L) ∨ Spike.Lib.X64.classify blk[k].1 = some (.call L) ∨
        ∃ cc, Spike.Lib.X64.classify blk[k].1 = some (.jcc cc L)) → PosOff OP (Ly).lab ((Ly).lab L)

/-- **The setup call's `hS` from the open premises** (`hS_assembledBC` at
`fnCode2OfPMe`) at one choice of the bounds: the setup block `rodata` at its compiled index
(`rodata_of_setupOf`, `rodata_compiled2`), the open premises there
(`SetupOpen`), the rest from the library (see the module docstring). -/
theorem hS_ofOpen {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) (hu : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit)
    {L D1 : Int} {fS : Nat} (hfD : (fS : Int) + 48 ≤ D1) (hL0 : 8 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD0 : 0 ≤ D1) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hrow : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS)
    (hno : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → addFreeT d.body = true)
    (J : InvS) (v : BitVec 64)
    (H : ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpen h Dt hp J (TOP) L D1 fS hd CxOk0) :
    SetupCallWSB (W2S J) (KT) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt fS) (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0
      (SetupGF p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
        ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec) := by
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    intro F' _ _ hFF _ _ _ _ _ _
    refine ⟨fun _ _ _ => False, fun s c fs hP => ?_, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨⟨-, -, -, -, σ, -, hF, -⟩, -⟩ := hP
    exact hv (hFF _ hF).1.1.1.1
  subst hv
  obtain ⟨dr, hf, hrt⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hty
  obtain ⟨j, hd, hn⟩ := Spike.Lib.LowerNode.rodata_compiled2 hf
  obtain ⟨CxOk0, HO⟩ := H j dr hd hn
  obtain ⟨w, hLw, hna, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j dr hd
  have hframe : (fnCode2OfPMe hp h Λ j dr hd).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user dr.name = _; rw [hn])
  have hna0 : (fnCode2OfPMe hp h Λ j dr hd).na = 0 := by
    have h1 := hLw.1
    rw [hu dr hf] at h1
    exact hna.trans (Option.some.inj (h1.symm.trans rfl))
  have hL : PosOff (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog (Ly).lab
      ((Ly).lab (proL (fnCode2OfPMe hp h Λ j dr hd).fr)) := by
    obtain ⟨n, hst⟩ := mem_starts (Scc.Lower.X64.lowerAll cfg p).low.ir 0 hmem
    have hok := Scc.Cert.Code1X64.fnOk1_of_fnCode1Ok
      (Scc.Cert.PlaceOK.X64.fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p sizes labelOffs)) hst rfl
    rw [hcx]
    exact posOff_proL_of_fnOk1 hok (labelOf_user_not_abLabs _ _) _
  have hc0 : C0 = Spike.Lib.Ctl.mk Scc.Sem.SrcSem.setupTerm [("me", .ptr .pub .void,
      [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)]), ("u", .unit, [])]
      none := by
    simp only [th02, hty]
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  -- the setup call's return point (`scc_rt_main`'s marshalling block at `sp0`) is off the write abort
  have hraP : PosOff OP (Ly).lab ((Ly).lab (setupMC (setupWords2 p)).sp0) := by
    have hin := Spike.Lib.X64.Rt.mainSIn_of_okS (rtCodeOkS_setupWords2 h hp hs')
    simp only [Spike.Lib.X64.Rt.mainSIn, Bool.and_eq_true] at hin
    have h0 := posOff_of_blockAtB (lab := (Ly).lab) hin.1.1.2 (by simp only [setupMC]; decide)
      (by simp [Spike.Lib.X64.Rt.marshal] <;> omega)
    rwa [Spike.Lib.X64.Flow.ofNat_zero'] at h0
  refine hS_assembledBC h hty J (TOP) hrt (fnCode2OfPMe hp h Λ j dr hd) (fnCode2OfPMe_spec hp h Λ j dr hd).2.2
    (raOk_setup _ _) HO.hs (hu dr hf) hna0
    (by rw [(fnCode2OfPMe hp h Λ j dr hd).hfn, hn]; rfl) (by rw [hframe]) ?_ ?_ hL
    (valRep_meW2_of_placeOKAt h _) ?_ (fun _ hm => hm.1.1.2) (Spike.Lib.X64.Rt.rS0_sub _)
    (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) hpN ?_
  · intro cE fr hct
    have hcall := callTo_setupTerm (p := p) (c0 := C0) (by rw [hc0]) (by rw [hc0]; rfl) hf
    exact (CallTo.unique hct hcall).1
  · intro _ _ _ hl
    revert hl
    dsimp only [MSAt]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hl => ⟨hl.rt, hl.mp, hl.unmapped, hl.room⟩
  · rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  · intro F' hR0 hF' hFF g fr hra htp hct hSB hbase
    -- the regions: the switch region, its callee `RS v`, the setup call's `RC`
    have hok : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
    have htop8 : (TOP).toNat % 8 = 0 := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
    have hR1 : (RS (TOP)).OK :=
      Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by show _ ≤ (0 : Int); omega)
    have hb1 : ((RS (TOP)).base.toNat : Int) = (TOP).toNat - 8 :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have hb8 : (RS (TOP)).base.toNat % 8 = 0 := by omega
    have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
      (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
    have hlo0 : ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).lo ≤
        -8 - ((fnCode2OfPMe hp h Λ j dr hd).fr.size : Int) := by
      show -D1 ≤ _; rw [hframe]; omega
    have hhi0 : (8 : Int) ≤ ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).hi := by
      show (8 : Int) ≤ 8; exact Int.le_refl _
    have hFO0 : ∀ m, F' m → StackOff (rS0 (Ly))
        ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8) m := fun m hm =>
      Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
        (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
        (by show _ < (8 : Int); omega) (by omega)
        (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
          (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
          (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2 (hFF m hm).1.2)
        (hFF m hm).2
    -- the body's blocks inside `W2` in the rebased region (`cxBlk2_ofFn`)
    obtain ⟨hF2, hR2, hlo2, hhi2⟩ := rbR_facts hF' hR0 hlo0 hhi0
    have hb2 := rbR_base hR0 (by omega) (by omega)
    have hblk : CxBlk2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j dr hd)
        (rbR ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)) F' [fr] g.fp g.ra
        (GR g fr) :=
      cxBlk2_ofFn (Λ := (Ly).Λ) (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly)))
      (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hpN (fnCode2OfPMe hp h Λ j dr hd) hF2 hR2
      (by omega) hlo2 hhi2 (by show (-D1 + 8) % 8 = 0; omega) (by show ((8 : Int) + 8) % 8 = 0; decide)
      (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _))
      (fun m hm => stackOff_rbR hR0 (by omega) (by omega) (hFO0 m hm))
      (fun s _ => framesPlaced_setup h hp hty hct s)
      (G0 := GR g fr) (fun _ hc => FrOk2.runM hpN hc (FrOk2.step hpN (hct.step []) (hf0_start2 hty _)))
      (fp := g.fp) (ra := g.ra) (fun _ _ h => h) (by rw [hra, Int64.ofBitVec_toBitVec]; exact hraP)
      (by rw [hra]; exact HO.hTg)
    refine ⟨GR g fr,
      AbU2 p (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j dr hd) _ F' [fr] g.fp g.ra (GR g fr),
      fun he => {
        hcx := CxOkS.bot (HO.hcx F' g fr ⟨hR0, hF', hFF, hra, htp, hct, hbase⟩) (htp ▸ hSB j (GR g fr))
        hF := hF'
        hR := hR0
        hlo := by
          show -D1 ≤ -8 - ((fnCode2OfPMe hp h Λ j dr hd).fr.size : Int)
          rw [hframe]; omega
        hhi := by show (8 : Int) ≤ 8; exact Int.le_refl _
        hG0 := fun _ _ h1 h2 => h1.trans h2
        hW := hblk.1
        hWp := hblk.2
        hab := fun c0 hc0' _ _ hA => .inl ⟨rfl, c0, hc0', hA⟩
        hg0 := .refl _
        hedge := he
        hR8 := by omega
        hl := by show (-D1) % 8 = 0; omega
        hh := by show (8 : Int) % 8 = 0; rfl
        hFO := fun m hm =>
          Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
            (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
            (by show _ < (8 : Int); omega) (by omega)
            (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
              (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
              (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2 (hFF m hm).1.2)
            (hFF m hm).2 },
      FrOk2.step hpN (hct.step []) (hf0_start2 hty _),
      SegWS.or_pre (abOf2_seg_addFree (hno j dr hd hn) hd) 
        (HO.habA F' g fr ⟨hR0, hF', hFF, hra, htp, hct, hbase⟩)⟩

/-- **The open premises at every choice of the bounds** (`SetupOpen` at
`Bounds2`'s `L`, `D1`, `fS`, every invariant holding at the starts, the
first stack's top and the setup block's compiled index). -/
def OpenS (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpen h Dt hp J (TOP) L D1 fS hd CxOk0

/-- **`HSBV` from the open premises** (`hS_ofOpen` at each choice of the
bounds). -/
theorem hSBV_ofOpenS (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hu : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (hno : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → addFreeT d.body = true)
    (H : OpenS h hp E El Dt) : HSBV h ty E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v
  obtain ⟨-, -, -, -, hfD, -, -, -, -, -, hrow, -, hL0, hLm, hL8, hD0, hD18, -, -, -, hL1, -⟩ := id hB
  exact hS_ofOpen h hp hty hu hfD hL0 hLm hL8 hD0 hD18 hL1 hrow hno J v
    fun j d hd hn => H L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn

end Assembled

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "Le" => Λx

/-- **`hello1o`'s setup block takes `Unit`.** -/
theorem hello1_hu : ∀ dr, (P1).find? (·.name == "rodata") = some dr → dr.argTy = .unit := by
  have hm : ((P1).find? (·.name == "rodata")).map (·.argTy) = some .unit := by decide
  intro dr hf
  rw [hf] at hm
  exact Option.some.inj hm

/-- **`hello1o`'s setup block `rodata` is addition-free.** -/
theorem hello1_rodata_addFree : ∀ (j : Nat) (d : Decl), (compiled2 P1)[j]? = some d → d.name = "rodata" →
    addFreeT d.body = true := by
  have hall : (compiled2 P1).all (fun d => d.name != "rodata" || addFreeT d.body) = true := by decide
  intro j d hd hn
  have hm := List.all_eq_true.mp hall d (List.mem_of_getElem? hd)
  simpa [hn] using hm

/-- **`hello1`'s setup call `hS` on x86-64, the open premises named**: at
every admissible output and entry, `HSBV` (the `hS` of the assembled start
segment at the setup call's known frame condition) from `OpenS`. -/
theorem hello1_hS
    (h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenS h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    HSBV h' hello1_hty.choose E El Dt :=
  hSBV_ofOpenS h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec hello1_hu hello1_rodata_addFree H

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.abOf2_seg_addFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms abOf2_seg_addFree

/-- info: 'Spike.Lib.LowerX64.framesPlaced_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms framesPlaced_setup

/-- info: 'Spike.Lib.LowerX64.hS_ofOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hS_ofOpen

/-- info: 'Spike.Lib.LowerX64.hSBV_ofOpenS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hSBV_ofOpenS

/-- info: 'Spike.Lib.LowerX64.hello1_hu' does not depend on any axioms -/
#guard_msgs in #print axioms hello1_hu

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_addFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello1_rodata_addFree

/-- info: 'Spike.Lib.LowerX64.hello1_hS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_hS

/-- info: 'Spike.Lib.LowerX64.cxBlk2_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cxBlk2_ofFn

end Spike.Lib.LowerX64
