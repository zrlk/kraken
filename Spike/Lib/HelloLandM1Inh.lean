/-
**The box counter add's `n4` states are reached** (AArch64; the non-vacuity of `LandR1U.HLandM1U`'s hypotheses,
the twin of `JpInh.chain_of_rdLandH` at `wc_main`'s box call): `HLandM1U Q` asks `Q` at every state at the
allocator's `n4` after `wc_main`'s box counter add (`Land.GcM1H` of `A64HelloLand1`, the pinned `GcMH`), under
main's thread pointer with the child's stack unmapped (`TP`, `U r1Of`). Here those hypotheses are shown to be the
one-step successors of level 1's real counter-add states, not an uninhabitable conjunction:

- the states stepped from are the level's at its box call: `wc_main`'s `hWp` (`WcWfR.wcPreW_WSgH`'s `hctx`,
  `MainWcL1Wi.hWp_L1` inside `MainWcL1A.hP_level1`) asks the context at the add's `rmw` node for a box call
  returning to `.sp0` from the caller `σC` whose slot `-80` holds main's TCB (`Level1I.slot80_rdJ`), under main's
  thread pointer — `Land1.hctx_main1H`'s premises, met at the level's memory sides (`Land1.hctx_main1U`, `GcM1H`'s
  inhabitation `example` there); `U r1Of` is level 1's context's (`RootUL.CtxU`, `RootL1U.W1RU`, from the landing's
  `RootL1U.rdLand_U`). Such a state is `CtxR1H`'s counter disjunct (`ctrAt_main1H`, `hctx_main1H`'s first case);
- from it the counter add's row (`RootUL.ctrRow_ofFTU`, the add's `rmw` at the allocator's code `LandR.hcode_H`)
  lands, for every old count the arena allows, in the allocator's `n4` with `TP` and `U r1Of` kept
  (`KeepTP.exec_tp`, `KeepUn.exec_un`) — i.e. in `N4M1`, `HLandM1U`'s hypothesis set (`n4M1_row`, `n4M1_call`).

- `N4M1`: `HLandM1U`'s hypotheses at a state, as a fragment; `hLandM1U_iff`: `HLandM1U Q` is `N4M1 ⊆ Q`.
- `ctrAt_main1H`: `hctx_main1H`'s counter-add states.
- `n4M1_row`, `n4M1_call`: the add's row lands in `N4M1`, from `CtxR1H`'s counter states and from the level's
  call facts.
-/
import Spike.Lib.A64HelloLand1
import Spike.Lib.A64HelloLandR1U
import Spike.Lib.A64HelloRootUL

namespace Spike.Lib.A64.HelloPh.LandM1Inh

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib (Region MemSide FragS)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Ret0 (CallerCells pinA)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0 JrT)
open Spike.Lib.A64.Flow.HelloWc (wARH WcCtxH)
open Spike.Lib.A64.Flow.HelloJr1 (JrRL)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.Alloc (Call N)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.KeepUn (U)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.Land (CtrAtF CtrOkS ref1H GcM1H CtxR1H Jr1LH)
open Spike.Lib.A64.HelloPh.LandR1U (HLandM1U)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize) (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- The allocator's labels. -/
local notation "LBL" => (_root_.Executable.labels (Ly).exe).label

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The level's reference memory sides. -/
local notation "REF" => ref1H (asm := asm) hpw i0 E rd ls l b n

/-- **`HLandM1U`'s hypotheses at a state** (module doc): the allocator's `n4` after `wc_main`'s box counter add at
`GcM1H`, at a memory side that is the level's reference side but for `xa`, under main's thread pointer with the
child's stack unmapped. -/
def N4M1 : FragS isaLSE2 := fun s c fs =>
  ∃ (ms0 : MemSide isaLSE2) (R : Region) (F : MachineData → Prop) (q : Call),
    ms0 = { (REF) fs with xa := ms0.xa } ∧ GcM1H hpw i0 l b fs ms0 R F q ∧ CtrOkS ms0 (LBL) R F q ∧
    At (Ly).exe (Ly).endPc R F (N (LBL) ms0 q .n4) s c ∧ TP (TV) s ∧ U (R1) s

/-- **`HLandM1U Q` is `N4M1 ⊆ Q`.** -/
theorem hLandM1U_iff (Q : FragS isaLSE2) :
    HLandM1U (asm := asm) hpw i0 E rd ls l b n Q ↔ ∀ s c fs, N4M1 (asm := asm) hpw i0 E rd ls l b n s c fs → Q s c fs :=
  ⟨fun h _ _ _ ⟨_, _, _, _, hms, hG, hok, hA, ht, hu⟩ => h _ _ _ _ _ hms hG hok _ _ hA ht hu,
    fun h fs ms0 R F q hms hG hok s c hA ht hu => h s c fs ⟨ms0, R, F, q, hms, hG, hok, hA, ht, hu⟩⟩

/-- **`hctx_main1H`'s counter-add states** (its first case): at the level's box call (the caller's slot `-80` main's
TCB, a box call returning to `.sp0`, the `rmw` node under main's thread pointer) the state is `CtxR1H`'s counter
disjunct, `CtrAtF … (GcM1H l b)` (`CtrOkS` by `fstable_wARH` at the first stack's top and the counter word
unloaded under the start's `FS`, `ctr_none_FS`). -/
theorem ctrAt_main1H (hc : Spike.Lib.A64.Rt.CtrZ o) {ms : MemSide isaLSE2}
    (hms : ms = { (REF) [] with xa := ms.xa }) (σC : FAS)
    (hslot : σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64) (m1 : MachineData) (σ1 : FAS) :
    ∀ q : Call, q.OKB ms (Ly).lab → q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (wARH (wcR (swR (TOP) (-helloLsw) 0) helloD))
        (fun m => wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) m1 σ1 m ∧
          CallerCells (wcR (swR (TOP) (-helloLsw) 0) helloD) (-144) (-160) 0 m ∧
          WcCtxH ms (Ly).lab (wcR (swR (TOP) (-helloLsw) 0) helloD)
            (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) Spike.Lib.A64.HelloPh.C0S.c0S.env l)
              (TV) (swR (TOP) (-helloLsw) 0))).J σ1)
            (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m)
        (N (Ly).lab ms q .rmw) s c → CtrAtF (REF) (Ly).exe (Ly).endPc (GcM1H hpw i0 l b) s c [] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { (REF) [] with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt
  refine ⟨_, _, _, q, rfl, ⟨rfl, hq, σC, m1, σ1, hslot, rfl, rfl, hra⟩, ⟨hq.toS, ?_, fun m hm => ?_⟩, hAt⟩
  · obtain ⟨hok, hal, hF0⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
    obtain ⟨hR, -, hF⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hal hF0
      (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
    exact Spike.Lib.A64.HelloPh.Land.fstable_wARH hR hF (by show (-helloD : Int) ≤ -304; decide)
      (by show (0 : Int) ≤ 0; decide)
  · exact Spike.Lib.A64.HelloPh.Land.ctr_none_FS (asm := asm) hpw i0 E rd ls hc (fs := []) (X := X) m hm.1.1

/-- **The counter add's row from `CtxR1H`'s counter states lands in `N4M1`** (module doc): at a state at the add's
`rmw` node for `wc_main`'s box call (`CtrAtF … (GcM1H l b)`) under main's thread pointer with the child's stack
unmapped, the add (`RootUL.ctrRow_ofFTU` at the allocator's code) is the counter row at the level's reference side
whose landings, for every old count the arena allows, are `N4M1` states (after the frame run of the call). -/
theorem n4M1_row (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok SccCode.helloProg)
    {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (hC : CtrAtF (REF) (Ly).exe (Ly).endPc (GcM1H hpw i0 l b) s c fs) (htp : TP (TV) s) (hu : U (R1) s)
    {c' : Spike.Lib.Ctl} {fs' : List TermRun.Frame} (hr : Spike.Lib.FrameRun helloSrc (c, fs) (c', fs')) :
    Spike.Lib.A64ConsumerA.CtrRow ((REF) fs')
      (fun s' c'' => Spike.Lib.A64ConsumerA.PendA helloSrc (fun _ _ => N4M1 (asm := asm) hpw i0 E rd ls l b n)
        (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.WakeLoadT.ls0T ls) s' c'' fs') s c' :=
  Spike.Lib.A64.HelloPh.RootUL.ctrRow_ofFTU (Spike.Lib.A64.HelloPh.LandR.hcode_H hpw i0 hpa hhp) (fun _ => rfl)
    (fun _ ms0 R F q hms hG hok _ _ hA ht hu => ⟨ms0, R, F, q, hms, hG, hok, hA, ht, hu⟩) hC htp hu hr

/-- **The real run reaches `N4M1`** (module doc): from the level's call facts at its box call (`hctx_main1H`'s
premises, under main's thread pointer with the child's stack unmapped) the counter add's row lands in `N4M1`. -/
theorem n4M1_call (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok SccCode.helloProg)
    (hc : Spike.Lib.A64.Rt.CtrZ o) {ms : MemSide isaLSE2} (hms : ms = { (REF) [] with xa := ms.xa }) (σC : FAS)
    (hslot : σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64) (m1 : MachineData) (σ1 : FAS)
    (q : Call) (hq : q.OKB ms (Ly).lab) (hra : q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec)
    {s : State} {c : Spike.Lib.Ctl}
    (hAt : At (Ly).exe (Ly).endPc (wARH (wcR (swR (TOP) (-helloLsw) 0) helloD))
      (fun m => wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) m1 σ1 m ∧
        CallerCells (wcR (swR (TOP) (-helloLsw) 0) helloD) (-144) (-160) 0 m ∧
        WcCtxH ms (Ly).lab (wcR (swR (TOP) (-helloLsw) 0) helloD)
          (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) Spike.Lib.A64.HelloPh.C0S.c0S.env l)
            (TV) (swR (TOP) (-helloLsw) 0))).J σ1)
          (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m)
      (N (Ly).lab ms q .rmw) s c)
    (htp : TP (TV) s) (hu : U (R1) s) {c' : Spike.Lib.Ctl} {fs' : List TermRun.Frame}
    (hr : Spike.Lib.FrameRun helloSrc (c, []) (c', fs')) :
    Spike.Lib.A64ConsumerA.CtrRow ((REF) fs')
      (fun s' c'' => Spike.Lib.A64ConsumerA.PendA helloSrc (fun _ _ => N4M1 (asm := asm) hpw i0 E rd ls l b n)
        (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.WakeLoadT.ls0T ls) s' c'' fs') s c' :=
  n4M1_row hpw i0 E rd ls l b n hpa hhp (ctrAt_main1H hpw i0 E rd ls l b n hc hms σC hslot m1 σ1 q hq hra s c hAt)
    htp hu hr

/-- `ctrAt_main1H`'s states are `CtxR1H`'s counter disjunct (level 1's context at its counter add). -/
example {s : State} {c : Spike.Lib.Ctl}
    (hC : CtrAtF (REF) (Ly).exe (Ly).endPc (GcM1H hpw i0 l b) s c []) (htp : TP (TV) s) :
    CtxR1H (asm := asm) hpw i0 E rd ls l b n s c [] := .inl ⟨hC, htp⟩

end Spike.Lib.A64.HelloPh.LandM1Inh

/-- info: 'Spike.Lib.A64.HelloPh.LandM1Inh.hLandM1U_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandM1Inh.hLandM1U_iff

/-- info: 'Spike.Lib.A64.HelloPh.LandM1Inh.ctrAt_main1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandM1Inh.ctrAt_main1H

/-- info: 'Spike.Lib.A64.HelloPh.LandM1Inh.n4M1_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandM1Inh.n4M1_row

/-- info: 'Spike.Lib.A64.HelloPh.LandM1Inh.n4M1_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandM1Inh.n4M1_call
