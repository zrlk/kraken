-- Conditional form: both results hold given the run's facts at the node; the invariant is proved, not assumed.
import Spike.Lib.X64HelloRootL0X

/-!
# `hello.w` on x86-64: level 0's context and counter-add landing at the self words are inhabited

Non-vacuity of the two level-0 pieces `X64HelloRootL0X` states at main's owned words with both TCB self words
(`ownGHXW`, written `OX`):

- `ctxU_OX_inh`: `CtxU (CtxRdHg … OX)`, the root's level-0 context (`RootInv`'s `CR`): it holds at every state
  of `wc_rodata`'s counter add under main's frame and thread pointer with the child's stack unmapped
  (`LandRU.hctx_rdRHg` at `OX`, the memory side exactly `refHg … OX [FR]`).
- `landRdUg_OX_inh`: the antecedent of `RootL0X.HLandRdUg … OX` (the memory side, `GcRdH`, `CtrOkS`, a state at
  the allocator's `c2` node, `U r1Of`, `TP`): from every state in `CtxRdHg … OX` with `TP` and `U r1Of`, the
  counter add's row (`RootUL.ctrRow_ofFTU`) reaches states in it.

Each result takes only the facts the real run supplies at those states (`LandRU.hctx_rdRHg`'s and
`RootUL.ctrRow_ofFTU`'s premises, the loader's two parses `hpa`, `hhp`, the counter's zeroed item `hc`).

**Unlike AArch64**: AArch64 has no counterpart, because main owns no TCB word there and level 0 is stated at
`ownGH` (`LandRU`'s `CtxRdH` example is the `ownGH` instance).
-/

namespace Spike.Test.HelloRootL0XInh

variable {asm : Scc.Sem.X64.Asm}

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib (PlaceWX MemSide)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Alloc (Call N)
open Spike.Lib.X64.KeepUn (U)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.Flow.Hello1 (mR mF mRdJ0 aR)
open Spike.Lib.X64.Flow.HelloRd (RdCtx)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.Land (CtrOkS CtrAtF GcRdH)
open Spike.Lib.X64.HelloPh.LandRU (refHg CtxRdHg)
open Spike.Lib.X64.HelloPh.RootUL (CtxU)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
/-- main's owned words before the spawn, both TCB self words included. -/
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- The allocator's labels. -/
local notation "LBL" => (_root_.Executable.labels (Ly).exe).label

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at `scc_rt_main`'s region `RS helloLsw v`. -/
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

/-- **Non-vacuity: the root's level-0 context at `OX` holds at the real counter add**: a state of `scc_rt_alloc`'s
`rmw` node for `wc_rodata`'s buffer call (returning to `.Lwc_rodata.x0`) under main's frame at a switch base `v`,
at the memory side `refHg … OX [FR]`, with main's thread pointer and the child's stack unmapped, is in
`CtxU (CtxRdHg … OX)` at the frames `[FR]`. -/
theorem ctxU_OX_inh (hc : Spike.Lib.X64.Rt.CtrZ o) (v : BitVec 64) (m0 : MachineData) (σC : FAS) (q : Call)
    (hq : q.OK (refHg (asm := asm) hpw i0 E rd ls (OX) [FR]) (Ly).lab)
    (hra : q.ra = ((Ly).lab ".Lwc_rodata.x0").toBitVec) (s : State) (c : Spike.Lib.Ctl)
    (hAt : At (Ly).exe (Ly).endPc (aR (mR (RS helloLsw v)))
      (fun m => mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m ∧
        CallerCells (mR (RS helloLsw v)) (-48) (-160) 8 m ∧
        RdCtx (refHg (asm := asm) hpw i0 E rd ls (OX) [FR]) (Ly).lab (mR (RS helloLsw v))
          (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC) q m)
      (N (Ly).lab (refHg (asm := asm) hpw i0 E rd ls (OX) [FR]) q .rmw) s c)
    (htp : TP (TV) s) (hu : U (R1) s) :
    CtxU hpw i0 (CtxRdHg (asm := asm) hpw i0 E rd ls (OX)) s c [FR] :=
  ⟨Spike.Lib.X64.HelloPh.LandRU.hctx_rdRHg hpw i0 E rd ls (OX) hc rfl v m0 σC q hq hra s c hAt htp, hu⟩

set_option hygiene false in
/-- **The antecedent of `HLandRdUg … OX`** at the frames `fs`: a memory side that is `refHg … OX fs` but for `xa`,
`wc_rodata`'s counter add's call facts (`GcRdH`, `CtrOkS`) and a state at the allocator's `c2` node with
`U r1Of` and main's thread pointer. -/
local notation "ANT" => fun (fs : List TermRun.Frame) (s : State) (c : Spike.Lib.Ctl) =>
  ∃ (ms0 : MemSide isa) (R : Spike.Lib.Region) (F : MachineData → Prop) (q : Call),
    ms0 = { refHg (asm := asm) hpw i0 E rd ls (OX) fs with xa := ms0.xa } ∧ GcRdH hpw i0 fs ms0 R F q ∧
      CtrOkS ms0 (LBL) R F q ∧ At (Ly).exe (Ly).endPc R F (N (LBL) ms0 q .c2) s c ∧ U (R1) s ∧ TP (TV) s

/-- **Non-vacuity: the antecedent of `HLandRdUg … OX` is reached**: from every state of the root's level-0 context
`CtxRdHg … OX` (the counter add's `rmw` node) with main's thread pointer and the child's stack unmapped, the counter
add's row (`RootUL.ctrRow_ofFTU`, the landing clause the antecedent itself) lands in states satisfying it. -/
theorem landRdUg_OX_inh (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (hC : CtrAtF (refHg (asm := asm) hpw i0 E rd ls (OX)) (Ly).exe (Ly).endPc (GcRdH hpw i0) s c fs)
    (htp : TP (TV) s) (hu : U (R1) s) :
    Spike.Lib.X64ConsumerA.CtrRow (refHg (asm := asm) hpw i0 E rd ls (OX) fs)
      (fun s' c' => Spike.Lib.X64ConsumerA.PendA helloSrc (fun _ _ s c fs => (ANT) fs s c)
        (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (Spike.Lib.X64WakeLoadT.ls0T ls) s' c' fs) s c := by
  haveI := (Ly).valid
  obtain ⟨hp, hend, hin⟩ := Spike.Lib.X64.HelloPh.LandR.hcode_H hpw i0 hpa hhp
  exact Spike.Lib.X64.HelloPh.RootUL.ctrRow_ofFTU hp hend hin (fun _ => rfl)
    (fun _ ms0 R F q h1 h2 h3 s c hAt htp hu => ⟨ms0, R, F, q, h1, h2, h3, hAt, hu, htp⟩) hC htp hu (.refl _)

end Spike.Test.HelloRootL0XInh

/-- info: 'Spike.Test.HelloRootL0XInh.ctxU_OX_inh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XInh.ctxU_OX_inh

/-- info: 'Spike.Test.HelloRootL0XInh.landRdUg_OX_inh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XInh.landRdUg_OX_inh
