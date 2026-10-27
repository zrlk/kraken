/-
**An output call of an `Accepted2` body** (AArch64): `printCallC_of`, the
obligation `PrintCallC` (`Body2.lean`) at the node with buffers and slices
(`bodyN2`), from `printInsts`' code (`print_code`), the states of its block
and of `scc_rt_print` inside the frame's fragment (`PrintW`, `PrintWE`), and
where an abort of `print` lands (`hAb`). The twin of
`Spike/Lib/LowerX64/PrintCallC2.lean`.

The source's call is taken first (`SegWS.pre_run`): at the `let` the
source runs locally to the call site `c1`, calls `print` (the frame
`printFrame x e c1` pushed) and runs to the top of `printL`
(`printCall_enter`), or, for an empty slice, to `print`'s `ret ()`. The
argument block with its `bl`, and `print`'s run, are then one segment at
the frames with `print`'s, the thread pointer kept (`print_call_segW_tp`,
`print_call_emptyW_tp`; `print`'s system call is a `svc`); after the
return the source binds `x` to `()` and pops the frame (`printCall_exit`,
`printCall_ret`; `SegWS.post_run`). The ghost run passes the call as a
memory let (`FrameRunM.mem1`). `bl` keeps the frame's offsets and the
return lands at the body's offsets: no frame-pointer bookkeeping.

- `PrintCode`, `print_code`: `InstsC2`'s cells of `printInsts`, the block
  and its `bl` one code segment;
- `rsOf_bounds`, `callSt_tpidr`: a slot's offset in the frame; the block
  keeps `tpidr_el0`;
- `NodeJE.unitBind`, `NJB.printUnit`, `printCall_emptyR`: the source after
  the call, `x` bound to `()` with no words;
- `printJL`, `printJ`, `PrintBlkW`, `PrintW`, `PrintWE`, `printSys_src`,
  `printNR`, `printNA` (`printNAS` with the caller's slots,
  `At.printNA_of_S`): the caller's facts at the call site, the block's
  invariant, the states inside the frame's fragment, the landings;
- `PrintSlots`: the caller's control placed in the slots at the call
  states (`printCallC_of'` gives it to its `hPW'`, `hPWE'`);
- `PrintSlotsA`, `PrintLen`: the caller's control placed in every slot file
  agreeing with the block's entry off its fresh registers, the count below
  `2 ^ 63` at the call states (`printCallC_ofA` gives them);
- `PrintBlkW'`, `PrintW'`, `PrintWE'` (`.primed` from the unprimed):
  `print`'s states asked only under frame conditions that know the call
  (`pFJ` at `callN`);
- `printCallC_ofA` (at `PrintW'`, `PrintWE'`, given `PrintSlotsA`,
  `PrintLen`), `printCallC_of'` and `printCallC_of`, its wrappers.
-/
import Spike.Lib.LowerA64.LaneC2
import Spike.Lib.LowerA64.CallC2
import Spike.Lib.LowerA64.PrintCall
import Spike.Lib.A64PrintTP
import Spike.Lib.Src.PrintCallSrc
import Spike.Lib.Src.PrintSite
import Spike.Lib.LowerA64.CtxC

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv opdVal_upd WordsRep SRep lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName atomV)
open Scc.Sem (ValRep)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD)
open Spike.Lib.A64.Flow.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.A64.PrintA (PrintAW)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.LowerShape (printInsts)

set_option linter.unusedSimpArgs false

/-! ## The code -/

/-- **`printInsts`' cells** (`print_code`'s data): the four computations'
cells into the fresh registers `lo`, `s`, `cap`, `k` and the two
arguments' loads, concatenated in `L`. -/
def PrintCode (cx : FnCtx) (n : Nat) (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand)
    (L : List Item) : Prop :=
  ∃ (i1 i2 i3 i4 : Nat) (l1 l2 l3 l4 l5 : List Item),
    cx.inst i1 (.ext false .w32 (regName "lo" n) (.reg o)) = .ok l1 ∧
    cx.inst i2 (.bin .add (regName "s" (n + 1)) b (.reg (regName "lo" n))) = .ok l2 ∧
    cx.inst i3 (.bin .mul (regName "cap" (n + 2)) m (Scc.Lower.imm 8)) = .ok l3 ∧
    cx.inst i4 (.select .ult (regName "k" (n + 3)) cw (.reg (regName "cap" (n + 2))) cw
      (.reg (regName "cap" (n + 2)))) = .ok l4 ∧
    cx.getArgs [.reg (regName "s" (n + 1)), .reg (regName "k" (n + 3))] = .ok l5 ∧
    L = l1 ++ l2 ++ l3 ++ l4 ++ l5

section Code

variable {exe : _root_.Executable} {endPc : Int64}

/-- **`InstsC2` of `printInsts`**: its cells (`PrintCode`), the block and
its `bl scc_rt_print` one code segment from `pc`, the pc after them. -/
theorem print_code {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc') :
    ∃ L, PrintCode cx n b o m cw L ∧ CdOf exe endPc pc (directives L ++ blPrintD) ∧
      pc' = pc + Int64.ofNat (4 * (directives L).length) + 4 := by
  unfold printInsts at hi
  rw [InstsC2] at hi
  rcases hi with ⟨-, l1, c1, hc1, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨-, l2, c2, hc2, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨-, l3, c3, hc3, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨-, l4, c4, hc4, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨hc, -⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨a0, a1, l5, he, c5, hc5, hb5, hp⟩
  · simp [Spike.Lib.LowerShape.isCall] at hc
  · simp at he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  simp only [Scc.IR.Inst.call.injEq, List.cons.injEq, and_true, true_and] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨l1 ++ l2 ++ l3 ++ l4 ++ l5, ⟨_, _, _, _, l1, l2, l3, l4, l5, c1, c2, c3, c4, c5, rfl⟩, ?_, ?_⟩
  · simp only [directives_append]
    refine CdOf.append (CdOf.append (CdOf.append (CdOf.append (CdOf.append (hCd _ _ hc1) (hCd _ _ hc2)) ?_) ?_) ?_)
      ?_
    · simp only [List.length_append, ← pc_add4]; exact hCd _ _ hc3
    · simp only [List.length_append, ← pc_add4]; exact hCd _ _ hc4
    · simp only [List.length_append, ← pc_add4]; exact hCd _ _ hc5
    · simp only [List.length_append, ← pc_add4]; exact hBl _ _ _ hb5
  · rw [InstsC2] at hp
    rw [hp]
    simp only [directives_append, List.length_append, ← pc_add4]

end Code

/-! ## The frame's cells -/

/-- **A register's slot lies in the frame below the saved pair**. -/
theorem rsOf_bounds {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {r : Scc.IR.Reg} {k : Int}
    (h : rsOf cx r = some k) : -(cx.frame : Int) ≤ k ∧ k % 8 = 0 ∧ k + 24 ≤ 0 := by
  unfold rsOf at h
  split at h
  · rename_i o ho
    cases h
    obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho
    omega
  · cases h

/-- **At `print`'s entry `tpidr_el0` is the block's entry's** (`arun_tpidr`). -/
theorem callSt_tpidr (lab : Label → Int64) (cx : FnCtx) (pc : Int64) (L : List Item) (σ0 : AS) :
    (callSt lab cx pc L σ0).regs.TPIDR_EL0 = σ0.regs.TPIDR_EL0 :=
  arun_tpidr lab _ _

/-! ## The source after the call -/

section Src

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {rs : Scc.IR.Reg → Option Int}

/-- **`x` bound to `()` after a call** (the node part): `NodeJE` at the
call site `c1`, the cells of the bindings' operands kept (`hsl`). Then
`NodeJE` at `e` with `x` bound to no words. -/
theorem NodeJE.unitBind {x : String} {op : Op} {e : Expr} {s : SEnv} {sl sl' : Int → BitVec 64} {c1 : Ctl}
    (hj : NodeJE lbl rs (.let_ x op e) s sl c1)
    (hsl : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, opdVal rs sl' o = opdVal rs sl o) :
    NodeJE lbl rs e ((x, .unit, []) :: s) sl' ⟨e, (x, .unit, []) :: c1.env, none⟩ :=
  ⟨rfl, rfl, (hj.2.2.congr hsl).bind x rfl trivial⟩

/-- **`let x = g(a)` of a call of `print`**: the node's parts at the call
site `c1` (`NodeJE`, `EnvLit`, `EnvB`, `MemB`, `EnvSmall`), the cells of the
bindings' operands kept (`hsl`). Then `NJB` at `e` with `x` bound to `()`,
the walk's next state at `()`'s layout `.nil`. -/
theorem NJB.printUnit {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {B : Nat}
    {x g : String} {is : List String} {a : At} {ts : List Ty} {e : Expr} {s : SEnv} {sl sl' : Int → BitVec 64}
    {c1 : Ctl} (hj : NodeJE lbl rs (.let_ x (.call g is a ts) e) s sl c1) (hn : EnvLit lits c1.env)
    (hb : EnvB lits cs bufs L sm lsize c1.env) (hm : MemB L sm B) (hS : EnvSmall c1.env)
    (hsl : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, opdVal rs sl' o = opdVal rs sl o) :
    NJB p lbl rs ((x, .nil) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
      (Scc.Lower.bufsAfter x cs bufs (.call g is a ts)) L sm lsize B e ((x, .unit, []) :: s) sl'
      ⟨e, (x, .unit, []) :: c1.env, none⟩ :=
  ⟨_, .refl _, NodeJE.unitBind hj hsl, hn.cons rfl (fun _ _ h _ => by simp at h),
    hb.cons (SliceL.nil _) (fun _ h => by rcases h with h | h <;> cases h) (fun _ _ h => by cases h), hm,
    EnvSmall.cons hS (fun _ h => by simp at h)⟩

/-- **An empty slice, the call**: the call and `print`'s body to its
`ret ()` (`printCall_empty` before the return). -/
theorem printCall_emptyR {c : Ctl} {fs : List TermRun.Frame} {x : String} {is : List String} {a : At} {e : Expr}
    {t : Ty} {pw wm wn : TermRun.Word}
    (hp : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (ht : c.term = .let_ x (.call "print" is a []) e) (ha : TermRun.evalAt c.env a = some (t, [pw, wm, wn]))
    (hwm : wm.val = .num 0) :
    ∃ env, FrameRun p (c, fs) (⟨.ret .unit, env, none⟩, printFrame x e c :: fs) := by
  have hr : ∃ env, LocalRunS p ⟨Spike.Lib.PrintSrc.printBody, [("a", Spike.Lib.Hello1Src.sliceTy, [pw, wm, wn])], none⟩
      ⟨.ret .unit, env, none⟩ :=
    ⟨_, .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
      .single (localStepS_ifeq_eq rfl rfl rfl hwm rfl)⟩
  obtain ⟨env, hr⟩ := hr
  exact ⟨env, .step (printCall_step hp ht ha) (FrameRun.ofLocalS hr _)⟩

end Src

/-! ## The nodes and the states inside the frame's fragment -/

/-- **The caller's facts at a call of `print`**, at the call site `c1`:
the node invariant at the `let` (`t`, `env`) with the walk's literal, buffer
and size facts, the saved pair, the ghost `c0`'s local run to `c1`, the
thread pointer `tp`. -/
def printJL (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cx : FnCtx)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (t : Expr) (env : Scc.Lower.Env)
    (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (c1 : Ctl) (σ : AS) : Prop :=
  (∃ L sm B, NodeJE lbl (rsOf cx) t (ofEnv2 env) σ.slot c1 ∧ EnvLit lits c1.env ∧ EnvB lits cs bufs L sm lsize c1.env ∧
    MemB L sm B ∧ EnvSmall c1.env) ∧ FrJ fp ra σ.slot ∧ LocalRun p c0 c1 ∧ σ.regs.TPIDR_EL0 = tp

/-- **The argument block's invariant**: the source at `print`'s control
`cE` (the call taken), the caller's facts at `c1` (`printJL`). -/
def printJ (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cx : FnCtx)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (t : Expr) (env : Scc.Lower.Env)
    (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (c1 cE : Ctl) : AS → Ctl → Prop :=
  fun σ c => c = cE ∧ printJL p lbl lsize cx fp ra tp c0 t env lits cs bufs c1 σ

/-- **The argument block's and `print`'s states in `W₀`**, not moved by
`K`, at the block's cells `L` from `pc` and the invariant `J`: along the
block with its `bl`, and `print`'s blocks (`PrintAW` at `print`'s source
predicates `P`, `Q`) for every call state (`callN`). -/
def PrintBlkW (W₀ : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (cx : FnCtx) (pc : Int64) (L : List Item) (J : AS → Ctl → Prop)
    (P Q : Nat → Ctl → Prop) : Prop :=
  BlkW W₀ K exe endPc R F ⟨pc, oF cx, J⟩ (directives L ++ blPrintD) ∧
    ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L J).J σC c →
      PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec σC.regs.X1.toBitVec.toNat P Q W₀ K exe
        endPc (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F)

/-- **A call of `print` of a nonempty slice inside `W₀`** (`print_call_segW_tp`'s
premises at the call): for `printInsts`' cells (`PrintCode`), the block's
and `print`'s states (`PrintBlkW` at `PrintC pw wn nv mv`), and at
`print`'s system call (for every call state, under any frame condition
`F'` inside `print`'s, `pF`) the states in `W₀` not moved by `K`, the memory
side's byte steps and output words. -/
def PrintW (W₀ : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isaLSE2) (cx : FnCtx) (pc : Int64) (n : Nat) (b : Scc.IR.Operand)
    (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) (pw wn : TermRun.Word) (nv mv : Nat) : Prop :=
  ∀ L, PrintCode cx n b o m cw L →
    PrintBlkW W₀ K exe endPc R F cx pc L J (PrintC pw wn nv mv) (PrintC pw wn nv mv) ∧
    ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L J).J σC c →
      σC.regs.X1.toBitVec.toNat = printN nv mv →
      ∀ (F' : MachineData → Prop), (∀ md, F' md → pF (-(cx.frame : Int)) R F md) → ∀ s c',
      At exe endPc (pR (-(cx.frame : Int)) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' →
      (W₀ s c' ∧ ∀ s', ¬ K s s') ∧
      (∀ k j, k + j < printN nv mv →
        ms.bo s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC pw wn mv (k + j))
          (fun c0 => ∃ mw b, c0 = nextC pw wn mv (k + j) mw b)) ∧
      ∀ k c1, PrintC pw wn nv mv k c1 → ms.we s c1

/-- **The source at `print`'s system call** (`PrintW`'s `.svc` states): the
loop at some byte `k` below the count, `PrintC pw wn nv mv k`, when the call
state's `x1` is the count `printN nv mv`. -/
theorem printSys_src {exe : _root_.Executable} {endPc : Int64} {R' : Region} {F' : MachineData → Prop}
    {lab : Label → Int64} {σC : AS} {pw wn : TermRun.Word} {nv mv : Nat} {s : State} {c' : Ctl}
    (hAt : At exe endPc R' F' (pN lab (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c')
    (hN : σC.regs.X1.toBitVec.toNat = printN nv mv) :
    ∃ k, PrintC pw wn nv mv k c' ∧ k < printN nv mv := by
  obtain ⟨-, -, -, -, σ, -, -, ⟨k, -, hlt, hP⟩, -⟩ := hAt
  exact ⟨k, hP, hN ▸ hlt⟩

/-- **A call of `print` of an empty slice inside `W₀`**: for `printInsts`'
cells, the block's and `print`'s states (`PrintBlkW`, `print`'s source at
`cE`, its `ret ()`). -/
def PrintWE (W₀ : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (cx : FnCtx) (pc : Int64) (n : Nat) (b : Scc.IR.Operand)
    (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) (cE : Ctl) : Prop :=
  ∀ L, PrintCode cx n b o m cw L → PrintBlkW W₀ K exe endPc R F cx pc L J (fun _ c => c = cE) (fun _ _ => False)

/-- **The caller's slots at a call of `print`**: at every call state the
caller's control `c1` with `x` bound to `()` before its continuation `e`
placed in the state's slots, at `e`'s immediates `i e`
(`printCallC_of'` gives it to `PrintW'`, `PrintWE'`; with the cells kept by
`print`, the caller's frame placed under `pFJ`). -/
def PrintSlots (lbl : WeakMem.AllocLabel → Option Nat) (i : Expr → String → Nat → Option Nat) (cx : FnCtx)
    (lab : Label → Int64) (pc : Int64) (n : Nat) (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand)
    (J : AS → Ctl → Prop) (x : String) (e : Expr) (c1 : Ctl) : Prop :=
  ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN lab cx pc L J).J σC c →
    SlotRepAt (fun _ => i e) lbl (rsOf cx) σC.slot { c1 with term := .let_ x (.atom .unit) e }

/-- **The caller's slots along a call of `print`'s argument block**: at
every entry state `σ0` of the block's invariant, the caller's control `c1`
with `x` bound to `()` before `e` placed in every slot file `sl` that agrees
with `σ0`'s off the block's fresh registers' slots (`PrintSlots` at every
state of the block, where only those slots are written; `printCallC_ofA`
gives it). -/
def PrintSlotsA (lbl : WeakMem.AllocLabel → Option Nat) (i : Expr → String → Nat → Option Nat) (cx : FnCtx)
    (n : Nat) (J : AS → Ctl → Prop) (x : String) (e : Expr) (c1 : Ctl) : Prop :=
  ∀ σ0 c, J σ0 c → ∀ sl : Int → BitVec 64,
    (∀ r j, rsOf cx r = some j → r ≠ regName "lo" n ∧ r ≠ regName "s" (n + 1) ∧ r ≠ regName "cap" (n + 2) ∧
      r ≠ regName "k" (n + 3) → sl j = σ0.slot j) →
    SlotRepAt (fun _ => i e) lbl (rsOf cx) sl { c1 with term := .let_ x (.atom .unit) e }

/-- **The count passed to `print` below `2 ^ 63`** at every call state
(`printCallC_ofA` gives it, from the slice's length at the call site). -/
def PrintLen (cx : FnCtx) (lab : Label → Int64) (pc : Int64) (n : Nat) (b : Scc.IR.Operand) (o : Scc.IR.Reg)
    (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) : Prop :=
  ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN lab cx pc L J).J σC c → σC.regs.X1.toBitVec.toNat < 2 ^ 63

/-- **`PrintBlkW` with `print`'s blocks asked only under frame conditions
that know the call** (`pFJ` at `callN`): the argument block as in
`PrintBlkW`, `print`'s blocks under every `F'` with `pFJ`, so their states
may use the caller's cells kept at the call. -/
def PrintBlkW' (W₀ : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (cx : FnCtx) (pc : Int64) (L : List Item) (J : AS → Ctl → Prop)
    (P Q : Nat → Ctl → Prop) : Prop :=
  BlkW W₀ K exe endPc R F ⟨pc, oF cx, J⟩ (directives L ++ blPrintD) ∧
    ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L J).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (callN (_root_.Executable.labels exe).label cx pc L J) σC F' →
      PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec σC.regs.X1.toBitVec.toNat P Q W₀ K exe
        endPc (pR (-(cx.frame : Int)) R) F'

/-- **`PrintW` under frame conditions that know the call**: `PrintBlkW'`,
and the system call's states under every `F'` with `pFJ` at `callN`. -/
def PrintW' (W₀ : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isaLSE2) (cx : FnCtx) (pc : Int64) (n : Nat) (b : Scc.IR.Operand)
    (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) (pw wn : TermRun.Word) (nv mv : Nat) : Prop :=
  ∀ L, PrintCode cx n b o m cw L →
    PrintBlkW' W₀ K exe endPc R F cx pc L J (PrintC pw wn nv mv) (PrintC pw wn nv mv) ∧
    ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L J).J σC c →
      σC.regs.X1.toBitVec.toNat = printN nv mv →
      ∀ (F' : MachineData → Prop), pFJ R F (callN (_root_.Executable.labels exe).label cx pc L J) σC F' → ∀ s c',
      At exe endPc (pR (-(cx.frame : Int)) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' →
      (W₀ s c' ∧ ∀ s', ¬ K s s') ∧
      (∀ k j, k + j < printN nv mv →
        ms.bo s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC pw wn mv (k + j))
          (fun c0 => ∃ mw b, c0 = nextC pw wn mv (k + j) mw b)) ∧
      ∀ k c1, PrintC pw wn nv mv k c1 → ms.we s c1

/-- **`PrintWE` under frame conditions that know the call**: `PrintBlkW'`
at `print`'s `ret ()`. -/
def PrintWE' (W₀ : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (cx : FnCtx) (pc : Int64) (n : Nat) (b : Scc.IR.Operand)
    (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (J : AS → Ctl → Prop) (cE : Ctl) : Prop :=
  ∀ L, PrintCode cx n b o m cw L → PrintBlkW' W₀ K exe endPc R F cx pc L J (fun _ c => c = cE) (fun _ _ => False)

/-- `PrintBlkW` gives `PrintBlkW'` (`pFJ` is inside `pF`). -/
theorem PrintBlkW.primed {W₀ : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {cx : FnCtx} {pc : Int64} {L : List Item} {J : AS → Ctl → Prop}
    {P Q : Nat → Ctl → Prop} (h : PrintBlkW W₀ K exe endPc R F cx pc L J P Q) :
    PrintBlkW' W₀ K exe endPc R F cx pc L J P Q :=
  ⟨h.1, fun σC c hJ _ hJF => (h.2 σC c hJ).mono fun m hm => (hJF.2 m hm).1⟩

/-- `PrintW` gives `PrintW'`. -/
theorem PrintW.primed {W₀ : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {cx : FnCtx} {pc : Int64} {n : Nat}
    {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {J : AS → Ctl → Prop} {pw wn : TermRun.Word}
    {nv mv : Nat} (h : PrintW W₀ K exe endPc R F ms cx pc n b o m cw J pw wn nv mv) :
    PrintW' W₀ K exe endPc R F ms cx pc n b o m cw J pw wn nv mv := fun L hL =>
  ⟨(h L hL).1.primed, fun σC c hJ hN F' hJF => (h L hL).2 σC c hJ hN F' fun md hm => (hJF.2 md hm).1⟩

/-- `PrintWE` gives `PrintWE'`. -/
theorem PrintWE.primed {W₀ : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {cx : FnCtx} {pc : Int64} {n : Nat} {b : Scc.IR.Operand}
    {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {J : AS → Ctl → Prop} {cE : Ctl}
    (h : PrintWE W₀ K exe endPc R F cx pc n b o m cw J cE) : PrintWE' W₀ K exe endPc R F cx pc n b o m cw J cE :=
  fun L hL => (h L hL).primed

/-- **Where a call of `print` returns**: the node after the `bl` at `pc'`
(the body's offsets); the source runs to `c2` at the caller's frames `fs`
(the return), the ghost `c0` runs to `c2` there, and `bodyN2` holds at
`c2`. -/
def printNR (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat) (cx : FnCtx) (fp ra : BitVec 64) (c0 : Ctl)
    (fs fs1 : List TermRun.Frame) (pc' : Int64) (e : Expr) (env' : Scc.Lower.Env)
    (lits' : List (String × Scc.Lower.LitV)) (cs' bufs' : List (String × Nat)) (c2 : Ctl) : ND :=
  ⟨pc', oF cx, fun σ c => FrameRun p (c, fs1) (c2, fs) ∧ FrameRunM p (c0, fs) (c2, fs) ∧
    (bodyN2 p lbl lsize i cx fp ra c2 pc' e (ofEnv2 env') lits' cs' bufs').J σ c2⟩

/-- **Where an abort of `print` lands**: `scc_rt_abort` with `x0 = 4`
(`print_call_segW_tp`'s abort, `sp` 48 bytes below the frame's floor), the
source inside `print`'s loop. -/
def printNA (lab : Label → Int64) (cx : FnCtx) : ND :=
  ⟨lab "scc_rt_abort", ⟨-(cx.frame : Int) + -48, []⟩, fun σ c => σ.regs.X0 = 4 ∧
    ∃ pw wn nv mv k, PrintC pw wn nv mv k c⟩

/-- **`print`'s abort node with the caller's slots**: `printNA`, the
abstract state's slots holding the caller's control `c1` with `x` bound to
`()` before `e` (`SlotRepAt` at the table `i`): `print`'s code keeps the
caller's frame cells, so its abort lands here (`printCallC_ofA`). -/
def printNAS (lab : Label → Int64) (cx : FnCtx) (lbl : WeakMem.AllocLabel → Option Nat)
    (i : Expr → String → Nat → Option Nat) (x : String) (e : Expr) (c1 : Ctl) : ND :=
  ⟨lab "scc_rt_abort", ⟨-(cx.frame : Int) + -48, []⟩, fun σ c => (printNA lab cx).J σ c ∧
    SlotRepAt (fun _ => i e) lbl (rsOf cx) σ.slot { c1 with term := .let_ x (.atom .unit) e }⟩

/-- **A state at `printNAS` is at `printNA`.** -/
theorem At.printNA_of_S {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {cx : FnCtx} {lbl : WeakMem.AllocLabel → Option Nat} {i : Expr → String → Nat → Option Nat}
    {x : String} {e : Expr} {c1 : Ctl} {s : State} {c : Ctl}
    (h : At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl i x e c1) s c) :
    At exe endPc R F (printNA (_root_.Executable.labels exe).label cx) s c :=
  let ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  ⟨he, hn, hdc, hpc, σ, hA, hD, hJ.1⟩

/-! ## The construct -/

section Main

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

/-- **`printCallC_of'` with the caller's slots at every state of the argument
block and the count's bound** (`PrintSlotsA`, `PrintLen`, given to `hPW`,
`hPWE` besides `PrintSlots`), so the frames along the block and
`PrintCallOkR.len` need no premise per call. -/
theorem printCallC_ofA {W : FragS isaLSE2} {K : State → State → Prop} {cx : FnCtx} (hf : FrameOk cx)
    (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48)
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hpin : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.A64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some σC.regs.X0.toBitVec.toNat) →
      PrintSlotsA lbl i cx n (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs
        bufs c1 (printTop0 pw wn mv)) x e c1 →
      PrintLen cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) →
      PrintSlots lbl i cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) cx pc n b o
        m cw (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl)
      (envR : TermRun.Env) (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      PrintSlotsA lbl i cx n (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs
        bufs c1 ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintLen cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) →
      PrintSlots lbl i cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F cx pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk env n x g is a ts e xe dg t b o m cw lits cs bufs hG0 hT hfresh hLP _ hgrp _ hsh hxe hdg hrt
    hav hI hIt hIc hLb
  obtain ⟨rfl, rfl⟩ := hTp _ _ _ _ _ _ _ hT hxe
  have h16' := frame_ge16 hf
  obtain ⟨_, ⟨i1, i2, i3, i4, l1, l2, l3, l4, l5, q1, q2, q3, q4, q5, rfl⟩, hcode, hpc'⟩ := print_code hCd hBl hI
  let lab := (_root_.Executable.labels exe).label
  have hPC : PrintCode cx n b o m cw (l1 ++ l2 ++ l3 ++ l4 ++ l5) :=
    ⟨i1, i2, i3, i4, l1, l2, l3, l4, l5, q1, q2, q3, q4, q5, rfl⟩
  -- the block's fresh registers are off the slice's operands and each other
  have hfw : ∀ o' ∈ [b, .reg o, m, cw], ∀ r, o' = .reg r → ∀ (y : String) k, n ≤ k → r ≠ regName y k :=
    fun o' ho r hr y k hk => atomV_fresh (hfresh.mono hk) hav y o' ho r hr
  have hb : ∀ r, b = .reg r → r ≠ regName "lo" n := fun r hr => hfw b (by simp) r hr "lo" n (by omega)
  have hm : ∀ r, m = .reg r → r ≠ regName "lo" n ∧ r ≠ regName "s" (n + 1) := fun r hr =>
    ⟨hfw m (by simp) r hr "lo" n (by omega), hfw m (by simp) r hr "s" (n + 1) (by omega)⟩
  have hn : ∀ r, cw = .reg r → r ≠ regName "lo" n ∧ r ≠ regName "s" (n + 1) ∧ r ≠ regName "cap" (n + 2) :=
    fun r hr => ⟨hfw cw (by simp) r hr "lo" n (by omega), hfw cw (by simp) r hr "s" (n + 1) (by omega),
      hfw cw (by simp) r hr "cap" (n + 2) (by omega)⟩
  have hsc : regName "s" (n + 1) ≠ regName "cap" (n + 2) := Scc.Lower.Inv.regName_ne (by omega)
  have hsk : regName "s" (n + 1) ≠ regName "k" (n + 3) := Scc.Lower.Inv.regName_ne (by omega)
  have fx := fun σ0 => callSt_facts hf h1 q1 q2 q3 q4 q5 hb hm hn hsc hsk lab pc σ0
  -- the frame's cells are outside `print`'s region
  have hout : ∀ k, -(cx.frame : Int) ≤ k → k % 8 = 0 → k + 8 ≤ 0 →
      R.Off k ∧ ¬ (pR (-(cx.frame : Int)) R).Off (k - -(cx.frame : Int)) :=
    fun k hk1 hk2 hk3 => frame_outC (D := 48) (by decide) hlo hhi hk2 hk1 hk3
  -- the block's coverage
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD) = true := by
    simp only [oF, directives_append, List.append_assoc]
    rw [okBlk_inst_ext32 hf h1 h16 q1, okBlk_inst_bin hf h1 h16 (.inl rfl) q2,
      okBlk_inst_bin hf h1 h16 (.inr rfl) q3, okBlk_inst_select hf h1 h16 q4, okBlk_args2 hf h1 h16 q5]
    rfl
  -- the source's names
  let t0 : Expr := .let_ x (.call "print" is a []) e
  let env' : Scc.Lower.Env := (x, .unit, []) :: env
  let lits' := (x, Scc.Lower.opLit lcx.prog lits (.call "print" is a [])) :: lits
  let cs' := Scc.Lower.csAfter x cs (.call "print" is a [])
  let bufs' := Scc.Lower.bufsAfter x cs bufs (.call "print" is a [])
  have hop : Scc.Lower.opLit lcx.prog lits (.call "print" is a []) = .nil := by
    simp only [Scc.Lower.opLit, Scc.Lower.retShape, hdg, hrt, Scc.Lower.shapeOf]
  have henv' : ofEnv2 env' = (x, .unit, []) :: ofEnv2 env := ofEnv2_cons (x := x) (env := env) rfl
  -- the entries, by the call site `c1`
  let P1 : Ctl → FragS isaLSE2 := fun c1 => (At exe endPc R F ⟨pc, oF cx, fun σ c =>
      printJL p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 σ ∧ LocalRun p c c1 ∧
      ((bodyN2 p lbl lsize i cx fp ra c0 pc t0 (ofEnv2 env) lits cs bufs).withTp tp).J σ c⟩).at fs
  refine (SegWS.exists_pre (P := P1) fun c1 => ?_).mono_pre ?_
  rotate_left
  · rintro s c fs' ⟨⟨he, hn', hdc, hpc, σ, hA, hD, hJ⟩, hfs⟩
    subst fs'
    obtain ⟨⟨⟨L, sm, Bm, c1, hr, hj, hl, hbB, hmB, hS⟩, hfj, hc0, -⟩, htp⟩ := id hJ
    exact ⟨c1, ⟨he, hn', hdc, hpc, σ, hA, hD, ⟨⟨L, sm, Bm, hj, hl, hbB, hmB, hS⟩, hfj, hc0.trans hr, htp⟩, hr, hJ⟩,
      rfl⟩
  by_cases hex : ∃ σ, printJL p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 σ
  rotate_left
  · exact SegWS.empty fun s c fs' ⟨⟨_, _, _, _, σ, _, _, hJ, _⟩, _⟩ => hex ⟨σ, hJ⟩
  obtain ⟨σx, hσx⟩ := hex
  obtain ⟨⟨Lx, smx, Bx, hjx, hlx, hBx, -⟩, -⟩ := hσx
  have hsh' : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf Scc.Frontend.ownSliceTy := by
    subst hprog; rw [hpd] at hdg; cases hdg; exact hsh
  obtain ⟨hgr, t', pw, wm, wn, mv, nv, hev, hwm, hwn, hm8⟩ :=
    printSite_of hjx hlx hBx.1 hgrp hav (hLP.1 a (by simp [headAtoms])) hsh'
  have hsa : Spike.Lib.Form.sevalAt (ofEnv2 env) a = some (t, [.loc b (.reg o), .one m, .one cw]) := by
    obtain ⟨pls, hpl, hs⟩ := sevalAt_ofEnv2L hgrp hav
    rw [hgr] at hpl; cases hpl; exact hs
  -- the length's and the count's operands at the call site
  have hval : ∀ σ0, printJL p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 σ0 →
      opdVal (rsOf cx) σ0.slot m = some mv ∧ opdVal (rsOf cx) σ0.slot cw = some nv := by
    rintro σ0 ⟨⟨_, _, _, hj0, -⟩, -⟩
    obtain ⟨_, ws, hev', -, hwr⟩ := hj0.2.2.evalAt (fun _ => rfl) hsa
    rw [hev] at hev'
    simp only [Option.some.injEq, Prod.mk.injEq] at hev'
    obtain ⟨-, rfl⟩ := hev'
    obtain ⟨-, ⟨v1, hv1, hr1⟩, ⟨v2, hv2, hr2⟩, -⟩ := hwr
    rw [hwm] at hr1
    rw [hwn] at hr2
    exact ⟨hv1.trans (congrArg some hr1.2), hv2.trans (congrArg some hr2.2)⟩
  -- the frames with `print`'s, the source after the return
  let fs1 := printFrame x e c1 :: fs
  let c2 : Ctl := ⟨e, (x, .unit, []) :: c1.env, none⟩
  let N := fun _ : Unit => printNR p lbl lsize i cx fp ra c0 fs fs1 pc' e env' lits' cs' bufs' c2
  let E := fun _ : Unit => printNAS lab cx lbl i x e c1
  -- the return lands at `N`
  have landR : ∀ σ0, printJL p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 σ0 → ∀ σR c',
      FrameRun p (c', fs1) (c2, fs) →
      (∀ k, R.Off k → ¬ (pR (-(cx.frame : Int)) R).Off (k - -(cx.frame : Int)) →
        σR.slot k = (callSt lab cx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0).slot k) →
      Hit (N ()) ⟨Int64.ofBitVec (callSt lab cx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0).regs.X30.toBitVec,
        ⟨-(cx.frame : Int), []⟩, σR⟩ c' := by
    intro σ0 hJL σR c' hrun hsl
    obtain ⟨⟨L, sm, Bm, hj, hl, hbB, hmB, hS⟩, hfj, hc0, -⟩ := hJL
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hra, hslC⟩ := fx σ0
    -- a cell of the frame is kept from the block's entry
    have hkeep : ∀ k, -(cx.frame : Int) ≤ k → k % 8 = 0 → k + 8 ≤ 0 →
        (∀ q, rsOf cx q = some k → q ≠ regName "lo" n ∧ q ≠ regName "s" (n + 1) ∧ q ≠ regName "cap" (n + 2) ∧
          q ≠ regName "k" (n + 3)) → σR.slot k = σ0.slot k := by
      intro k hk1 hk2 hk3 hq
      obtain ⟨ho1, ho2⟩ := hout k hk1 hk2 hk3
      rw [hsl k ho1 ho2]
      exact hslC k hq
    have hnone : ∀ k, -16 ≤ k → ∀ q, rsOf cx q = some k → q ≠ regName "lo" n ∧ q ≠ regName "s" (n + 1) ∧
        q ≠ regName "cap" (n + 2) ∧ q ≠ regName "k" (n + 3) := by
      intro k hk q hq; have := (rsOf_bounds hf h16 hq).2.2; omega
    have hsl' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds,
        opdVal (rsOf cx) σR.slot o' = opdVal (rsOf cx) σ0.slot o' := by
      intro q hq pl hpl o' ho'
      refine opdVal_upd fun r k hor hr => ?_
      obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf h16 hr
      refine hkeep k hk1 hk2 (by omega) fun q' hq' => ?_
      have hqr := rsOf_inj hq' hr
      subst hqr
      exact ⟨Fresh.ofEnv2 hfresh "lo" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 1)) "s" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 2)) "cap" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 3)) "k" q hq pl hpl o' ho' _ hor⟩
    have hjE := NodeJE.unitBind hj hsl'
    refine ⟨?_, ?_, hrun, (FrameRunM.ofLocal hc0 fs).trans (FrameRunM.mem1 hj.2.1 hj.1 rfl),
      ⟨L, sm, Bm, ?_⟩, ?_, .refl _, ?_⟩
    · show pc' = Int64.ofBitVec _
      rw [hra, int64_ofBitVec_toBitVec, hpc']
    · show SO.le (oF cx) ⟨-(cx.frame : Int), []⟩ = true
      simp [SO.le, oF]
    · show NJB p lbl (rsOf cx) ((x, Scc.Lower.opLit lcx.prog lits (.call "print" is a [])) :: lits) cs' bufs' L sm
        lsize Bm e (ofEnv2 env') σR.slot c2
      rw [henv', hop]
      exact NJB.printUnit hj hl hbB hmB hS hsl'
    · exact ⟨(hkeep (-16) (by omega) (by decide) (by decide) (hnone (-16) (Int.le_refl _))).trans hfj.1,
        (hkeep (-8) (by omega) (by decide) (by decide) (hnone (-8) (by decide))).trans hfj.2⟩
    · refine SlotRepAt.of_nodeJE hjE ?_ ?_ ?_
      · rw [← henv']; exact hIt
      · rw [← henv']; exact hLb
      · rw [← henv']; exact hIc
  -- the caller's slots at the call states
  have hcons : ∀ y, y ≠ x → lookupS (ofEnv2 env') y = lookupS (ofEnv2 env) y := by
    intro y hy
    rw [henv']
    simp [lookupS, List.find?_cons, Ne.symm hy]
  have hfv : ∀ y ∈ Scc.Sem.exprFv (Expr.let_ x (.atom .unit) e), y ∈ Scc.Sem.exprFv e ∧ y ≠ x := by
    intro y hy
    simpa [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, Scc.Sem.atVars] using hy
  have hslotsA : ∀ cE, PrintSlotsA lbl i cx n (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE) x e
      c1 := by
    intro cE σ0 c hc sl hsl
    obtain ⟨-, hJL⟩ := hc
    obtain ⟨⟨_, _, _, hj, -⟩, -⟩ := hJL
    have hsl' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds,
        opdVal (rsOf cx) sl o' = opdVal (rsOf cx) σ0.slot o' := by
      intro q hq pl hpl o' ho'
      refine opdVal_upd fun r k hor hr => ?_
      exact hsl r k hr ⟨Fresh.ofEnv2 hfresh "lo" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 1)) "s" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 2)) "cap" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 3)) "k" q hq pl hpl o' ho' _ hor⟩
    have hs := hj.2.2.congr hsl'
    refine SlotRepAt.of_srepE (s := (ofEnv2 env).filter (·.1 != x)) ?_ ?_ ?_ ?_
    · intro y ty' pls hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy] at hl
        exact hs y ty' pls hl
    · intro y hy
      have hy := hfv y hy
      rw [lookupS_filter_ne _ hy.2, ← hcons y hy.2]
      exact hIt y hy.1
    · intro y hy ty' pls hl b' o' hb'
      have hy := hfv y hy
      rw [lookupS_filter_ne _ hy.2, ← hcons y hy.2] at hl
      exact hLb y hy.1 ty' pls hl b' o' hb'
    · intro y k v hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy, ← hcons y hy] at hl
        exact hIc y k v hl
  have hslots : ∀ cE, PrintSlots lbl i cx lab pc n b o m cw
      (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE) x e c1 := by
    rintro cE L ⟨i1', i2', i3', i4', l1', l2', l3', l4', l5', q1', q2', q3', q4', q5', rfl⟩ σC c
      ⟨σ0, hJ0, rfl⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hslC⟩ :=
      callSt_facts hf h1 q1' q2' q3' q4' q5' hb hm hn hsc hsk lab pc σ0
    refine hslotsA cE σ0 c hJ0 _ fun r k hr hne => hslC k fun q' hq' => ?_
    have hqr := rsOf_inj hq' hr
    subst hqr
    exact hne
  have hlenA : ∀ cE, PrintLen cx lab pc n b o m cw (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE) := by
    rintro cE L ⟨i1', i2', i3', i4', l1', l2', l3', l4', l5', q1', q2', q3', q4', q5', rfl⟩ σC c
      ⟨σ0, ⟨-, hJL⟩, rfl⟩
    obtain ⟨vb, vo, vm, vn, -, -, hvm, hvn, -, -, hx1, -, -⟩ :=
      callSt_facts hf h1 q1' q2' q3' q4' q5' hb hm hn hsc hsk lab pc σ0
    have hm' := (hval σ0 hJL).1
    rw [hvm] at hm'
    have em : vm.toNat = mv := Option.some.inj hm'
    have h8m : (vm * 8#64).toNat = mv * 8 := by
      rw [BitVec.toNat_mul, em]; simp only [BitVec.toNat_ofNat]; omega
    rw [hx1]
    split
    · omega
    · rw [h8m]; omega
  -- the frames: the call taken at the entry, the return at the exit
  have plumb : ∀ cE : Ctl, FrameRun p (c1, fs) (cE, fs1) →
      SegW (fun s c => W s c fs1) K p lbl (ms fs1)
        (At exe endPc R F ⟨pc, oF cx, printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE⟩)
        (fun s c => Next exe endPc R F N E s c ∧ TP tp s) →
      SegWS W K p lbl ms (P1 c1) (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e env' lits' cs' bufs') :=
        by
    intro cE hrun hseg
    refine SegWS.post_run ((SegWS.pre_run (P := P1 c1) (SegWS.liftS fs1 hseg fun _ _ h => h) ?_).mono_post ?_)
    · rintro s c fs' ⟨⟨he, hn', hdc, hpc, σ, hA, hD, hJL, hr, hJ⟩, hfs⟩
      subst fs'
      exact ⟨hWL c0 pc env lits cs bufs n x is a e b o m cw kk pc' s c hG0 hT hI
        ⟨⟨he, hn', hdc, hpc, σ, hA, hD, hJ⟩, rfl⟩, cE, fs1,
        (FrameRun.ofLocal hr fs).trans hrun, ⟨he, hn', hdc, hpc, σ, hA, hD, rfl, hJL⟩, rfl⟩
    · rintro s c fs' ⟨⟨⟨_, he, hn', hdc, hpc, σ, hA, hD, hrun2, hgh, hJ2⟩ | ⟨_, hat⟩, htp⟩, hfs⟩ <;> subst fs'
      · exact ⟨c2, fs, hrun2, .inl ⟨rfl, c2, hgh, he, hn', hdc, hpc, σ, hA, hD, hJ2, hA.regs ▸ htp⟩⟩
      · exact ⟨c, fs1, .refl _, .inr (hAb c0 x is a e c1 s c hG0 hT hat)⟩
  -- the block and its `bl`, the thread pointer kept
  have mkS1 : ∀ (cE : Ctl) (P Q : Nat → Ctl → Prop),
      PrintBlkW' (fun s c => W s c fs1) K exe endPc R F cx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5)
        (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE) P Q →
      SegW (fun s c => W s c fs1) K p lbl (ms fs1)
        (At exe endPc R F ⟨pc, oF cx, printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE⟩)
        (fun s c => At exe endPc R F (callN lab cx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5)
          (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE)) s c ∧ TP tp s) := by
    rintro cE P Q ⟨hWb, -⟩
    refine (seg_ndW (W := fun s c => W s c fs1) (K := K) (p := p) (lbl := lbl) (ms := ms fs1)
      (n := ⟨pc, oF cx, printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE⟩)
      (N := fun _ : Unit => callN lab cx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5)
        (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE))
      (E := fun e : Empty => e.elim) (by simp [blPrintD_eq]) hok hF hR hal (by omega) hhi
      (fun s he hn => hcode s he hn) hWb
      fun σ c' hJ => ⟨c', .refl c', .inl ⟨(), ?_⟩⟩).mono_post fun s c h => ?_
    · obtain ⟨-, -, -, -, -, -, -, -, he, -⟩ := fx σ
      refine ⟨?_, ?_, σ, hJ, ?_⟩
      · show lab "scc_rt_print" = (arun lab _ _).pc
        rw [he]
      · show SO.le (oF cx) (arun lab _ _).so = true
        rw [he]; simp [SO.le, oF]
      · show (arun lab _ _).σ = _
        rfl
    · have hA := h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
      refine ⟨hA, ?_⟩
      obtain ⟨-, -, -, -, σ, hAb, -, σ0, ⟨-, hJL⟩, hσ⟩ := hA
      show s.st.1.regs.TPIDR_EL0 = tp
      rw [hAb.regs, hσ, callSt_tpidr]
      exact hJL.2.2.2
  by_cases hm0 : mv = 0
  · -- an empty slice: `print`'s body to `ret ()`
    obtain ⟨envR, hrunE⟩ := printCall_emptyR (fs := fs) hpd hjx.1 hev (by rw [hwm, hm0])
    let cE : Ctl := ⟨.ret .unit, envR, none⟩
    refine plumb cE hrunE ?_
    have hBW := hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hI (hslotsA _) (hlenA _)
      (hslots _) _ hPC
    refine (mkS1 cE _ _ hBW).seq ?_
    refine print_call_emptyW_tp' (nC := callN lab cx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5)
        (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 cE))
      (Pe := fun _ c => c = cE) hp hend hpin hF hR hal (by show R.lo ≤ -(cx.frame : Int) + -48; omega)
      (by show -(cx.frame : Int) < R.hi; omega) (by show (-(cx.frame : Int)) % 16 = 0; omega) rfl
      (fun σ c ⟨σ0, ⟨hc, _⟩, _⟩ => hc) ?_ (fun σC c h F' hJF => hBW.2 σC c h F' hJF) (hK fs1) ?_
    · rintro σ c ⟨σ0, ⟨-, hJL⟩, rfl⟩
      obtain ⟨vb, vo, vm, vn, -, -, hvm, -, -, -, hx1, -, -⟩ := fx σ0
      have hvm' : vm.toNat = 0 := by
        have := (hval σ0 hJL).1; rw [hvm, hm0] at this; exact Option.some.inj this
      have hv0 : vm = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hvm')
      rw [hx1, hv0]
      simp
    · rintro σC c σR c' ⟨σ0, ⟨-, hJL⟩, rfl⟩ - - hc' hsl
      subst hc'
      exact .inl ⟨(), landR σ0 hJL σR _ (.single (printCall_ret rfl)) hsl⟩
  · -- a nonempty slice: `print`'s loop
    have hen := printCall_enter (p := p) (fs := fs) hpd hd hjx.1 hev hwm hm0 hwn
    refine plumb _ hen.1 ?_
    -- the buffer word the start of a location placed at `x0`
    have hpwX : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN lab cx pc L
        (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some σC.regs.X0.toBitVec.toNat := by
      rintro L ⟨i1', i2', i3', i4', l1', l2', l3', l4', l5', q1', q2', q3', q4', q5', rfl⟩ σC c ⟨σ0, ⟨-, hJL⟩, rfl⟩
      obtain ⟨l, -, hpw0, -, -⟩ := print_arg_slAt hBx.1 hev hsh'
      obtain ⟨vb, vo, -, -, hvb, hvo, -, -, -, hx0, -, -, -⟩ :=
        callSt_facts hf h1 q1' q2' q3' q4' q5' hb hm hn hsc hsk lab pc σ0
      obtain ⟨⟨_, _, _, hj0, -⟩, -⟩ := hJL
      obtain ⟨_, ws, hev', -, hwr⟩ := hj0.2.2.evalAt (fun _ => rfl) hsa
      rw [hev] at hev'
      simp only [Option.some.injEq, Prod.mk.injEq] at hev'
      obtain ⟨-, rfl⟩ := hev'
      obtain ⟨⟨vb', vo', hb', ho', hloc⟩, -⟩ := hwr
      rw [hpw0] at hloc
      obtain ⟨-, hl', hoff⟩ := hloc
      rw [hvb] at hb'
      rw [hvo] at ho'
      have e1 : vb.toNat = vb' := Option.some.inj hb'
      have e2 : vo.toNat = vo' := Option.some.inj ho'
      have ho0 : vo' = 0 := by simpa using hoff
      have hv0 : vo = 0#64 := BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)
      have hx0' : (callSt lab cx pc (l1' ++ l2' ++ l3' ++ l4' ++ l5') σ0).regs.X0.toBitVec = vb := by
        rw [hx0, hv0]; simp [BitVec.take]
      refine ⟨l, hpw0, ?_⟩
      rw [hx0', e1]
      exact hl'
    obtain ⟨hBW, hsys⟩ :=
      hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hI hpwX (hslotsA _) (hlenA _)
        (hslots _) _ hPC
    refine (mkS1 _ _ _ hBW).seq ?_
    -- the count passed to `print`
    have hcnt : ∀ σ c, (callN lab cx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5)
        (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 (printTop0 pw wn mv))).J σ c →
        σ.regs.X1.toBitVec.toNat = printN nv mv := by
      rintro σ c ⟨σ0, ⟨-, hJL⟩, rfl⟩
      obtain ⟨vb, vo, vm, vn, -, -, hvm, hvn, -, -, hx1, -, -⟩ := fx σ0
      obtain ⟨hm', hn'⟩ := hval σ0 hJL
      rw [hvm] at hm'
      rw [hvn] at hn'
      have em : vm.toNat = mv := Option.some.inj hm'
      have en : vn.toNat = nv := Option.some.inj hn'
      rw [hx1, printN_of_x1 (by rw [em]; exact hm8), em, en]
    refine print_call_segW_tp' (nC := callN lab cx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5)
        (printJ p lbl lsize cx fp ra tp c0 t0 env lits cs bufs c1 (printTop0 pw wn mv))) (N := N) (E := E)
      (pw := fun _ => pw) (wn := fun _ => wn) (n := fun _ => nv) (m := fun _ => mv) hp hend hpin hF hR hal
      (by show R.lo ≤ -(cx.frame : Int) + -48; omega) (by show -(cx.frame : Int) < R.hi; omega)
      (by show (-(cx.frame : Int)) % 16 = 0; omega) rfl
      (fun σ c ⟨σ0, ⟨hc, _⟩, _⟩ => hc ▸ hen.2) hcnt (fun _ _ _ => hm8)
      (fun σC c h F' hJF => hBW.2 σC c h F' hJF) hd (hK fs1) (hcl fs1)
      (fun σC c h F' hJF s c' hAt => (hsys σC c h (hcnt σC c h) F' hJF s c' hAt).1)
      (fun σC c h F' hJF s c' hAt => (hsys σC c h (hcnt σC c h) F' hJF s c' hAt).2.1)
      (fun σC c h F' hJF s c' hAt => (hsys σC c h (hcnt σC c h) F' hJF s c' hAt).2.2) ?_ ?_
    · rintro σC c σR c' ⟨σ0, ⟨-, hJL⟩, rfl⟩ - - hc' hsl
      exact .inl ⟨(), landR σ0 hJL σR c' (printCall_exit hc') hsl⟩
    · rintro σC c σR c' k ⟨σ0, hJ0, rfl⟩ hr0 hc' hkS
      refine .inr ⟨(), rfl, ?_, ⟨hr0, pw, wn, nv, mv, k, hc'⟩, hslotsA _ σ0 c hJ0 σR.slot fun r j hr hne => ?_⟩
      · show SO.le ⟨-(cx.frame : Int) + -48, []⟩ ⟨-(cx.frame : Int) + -48, []⟩ = true
        simp [SO.le]
      · -- the caller's slots kept from the call (off `print`'s region), there off the block's fresh registers
        obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf h16 hr
        obtain ⟨ho1, ho2⟩ := hout j hk1 hk2 (by omega)
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hslC⟩ := fx σ0
        rw [hkS j ho1 ho2]
        exact hslC j fun q' hq' => by rw [rsOf_inj hq' hr]; exact hne

/-- **`printCallC_of` with `print`'s states asked only under frame
conditions that know the call** (`PrintW'`, `PrintWE'`: `pFJ` at `callN`,
through `print_call_segW_tp'`, `print_call_emptyW_tp'`), so they may use
the caller's cells kept at the call (e.g. the frames placed). -/
theorem printCallC_of' {W : FragS isaLSE2} {K : State → State → Prop} {cx : FnCtx} (hf : FrameOk cx)
    (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48)
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hpin : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.A64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some σC.regs.X0.toBitVec.toNat) →
      PrintSlots lbl i cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) cx pc n b o
        m cw (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl)
      (envR : TermRun.Env) (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      PrintSlots lbl i cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F cx pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  printCallC_ofA hf h1 h16 hF hR hal hlo hhi hCd hBl hp hend hpin hpd hd hprog hK hcl hTp hWL
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hI hpw _ _ hS =>
      hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hI hpw hS)
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hI _ _ hS =>
      hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hI hS) hAb

/-- **An output call of an `Accepted2` body** (`PrintCallC`), in the
frame's region (`hlo`: `print`'s 48 bytes below it) of a layout with
`scc_rt_print` (`printIn`): the code predicates give code (`hCd`, `hBl`);
the externs called are `print` with no type arguments (`hTp`), the call's
program `p` (`hprog`; at the call site the slice's words a locative, its
length and the count by `printSite_of`); the states at the `let` (`hWL`), along the argument
block and in `print` (`PrintW`, `PrintWE` at `printJ`, the latter at `print`'s `ret ()`, inside `W` at
`print`'s frames, given the block's code `InstsC2`) lie in `W`; an abort of `print` is one of `Ab` (`hAb`). -/
theorem printCallC_of {W : FragS isaLSE2} {K : State → State → Prop} {cx : FnCtx} (hf : FrameOk cx)
    (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48)
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hpin : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.A64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some σC.regs.X0.toBitVec.toNat) →
      PrintW (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) cx pc n b o
        m cw (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl)
      (envR : TermRun.Env) (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      PrintWE (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F cx pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  printCallC_of' hf h1 h16 hF hR hal hlo hhi hCd hBl hp hend hpin hpd hd hprog hK hcl hTp hWL
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hI hpw _ =>
      (hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hI hpw).primed)
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hI _ =>
      (hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hI).primed) hAb

end Main

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.print_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.print_code

/-- info: 'Spike.Lib.LowerA64.printCallC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallC_of

/-- info: 'Spike.Lib.LowerA64.printCallC_ofA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallC_ofA

/-- info: 'Spike.Lib.LowerA64.printCallC_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallC_of'

/-- info: 'Spike.Lib.LowerA64.At.printNA_of_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.At.printNA_of_S

/-- info: 'Spike.Lib.LowerA64.PrintW.primed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.PrintW.primed
