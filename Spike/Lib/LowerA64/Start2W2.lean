/-
**The start's segment inside `W2`** (AArch64, the consumer's `h0`): the
twin of the planned x86-64 `Start2W2`.

- `rtX_w2G`: `rtX_w2` at any source start control `c0` free of `ZBad`, not
  at an overflow (`¬ OvfReady c0`, so no abort site is a pc of its states);
- `msOfAX_K_abi`: the rows' memory side has the kernel's ABI;
- `startEW_w2G`: `startEW_w2A` at any such `c0` (`startEW_sfacts`,
  `startEW_rtX`, `rtX_w2G`);
- `h0_of_startS`: `startS_segWS` inside `W2` at `L0`, `ls0` over `IN … J`
  under the rows' memory side, from `_start` at `c0` (the consumer's `h0` of
  `nodes2_of_starts`); the start's states from `startEW_w2G`, the rest of
  `startS_segWS`'s premises named (`scc_rt_main`'s: `hS`, `hU`, `hexit`,
  `hW`; the rows' memory facts: `hhdr`, `htcb`, `hfld`, `htk`, `hlim*`);
- `stOk_toAX` … `takeOk_toAX`: the runtime's access facts under `msOf` are
  ones under the rows' memory side at the empty frames;
- discharging `h0_of_startS`'s premises at a placed output:
  `mainSIn_of_placeOKAt` (`hin`, a `.setup` tail, some `setupMC sw`),
  `rows_ofPlaceOK` (`hhdr`, `htcb`, `hfld`, `htk` at `n0 = k0 = 0`, no label
  placed, `G = GOf`), `limOk_ofPlaceOK` (`hlim*` at any bound past the
  limit), `hun_ofPlaceOK` (`hun`);
- `h0_ofPlaceOK`: `h0_of_startS` at an entry state's region, the first TCB
  and stack, a switch region of any depth up to `16384`, in the world
  `W2At` under `MSAt` (no label placed, `GOf`), the region's, the stack's
  and the rows' facts discharged.
-/
import Spike.Lib.LowerA64.StartEW2
import Spike.Lib.LowerA64.Levels2
import Spike.Lib.Rt.A64MainSS
import Spike.Lib.A64StartOfPlaceOK
import Spike.Lib.LowerA64.Correct
import Spike.Lib.Rt.A64StartArith

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.AllocReach (IN)
open Scc.Sem.A64 (abi pcOf)

section RtX

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl lbl0 : Lbl}
  {lsize : Lsize} {lab : Label → Int64} {c0 : Ctl}

/-- At a control not at an overflow, `SFacts` puts no abort site at the
state's pc. -/
theorem noAbort_of_sfacts {Dt' : State → Prop} {s : State} (hov : ¬ OvfReady c0)
    (h : SFacts Λ μ own rS Tk lbl0 s c0 Dt') : ∀ k a, μ.abortAt k = some a → pcOf s ≠ a :=
  fun k a ha hpc => hov (h.abortOk k a ha hpc).2.1

/-- **`W2` at a runtime state at no frame, at any start control**: `rtX_w2`
at `c0` (`hf0`), not at an overflow (`hov`). -/
theorem rtX_w2G (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0) {s : State} {c : Ctl}
    (hS : SFacts Λ μ own rS Tk lbl0 s c0) (hX : RtX Λ μ ar lbl lab c0 s c) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c [] := by
  obtain ⟨hab, hpl, hwr, rfl⟩ := hX
  have hP := w2Part_of_wrOff (J := J) (rd := rd) (G := G) (p := p) (lsize := lsize) hab hpl hwr hS
  exact w2_of hp hf0 (hS.toSt.dt_mono fun _ h => h.elim) hP.1 (fun _ => hS.noRet) (.of_placedS hP.2.1) hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts hov hS)) hP.2.2.2

/-- **The rows' memory side has the kernel's ABI** (`h0_of_startS`'s `hK`
at `msOfAX`). -/
theorem msOfAX_K_abi {ar : Arena} {own' : OwnS} {ab : Option (State → Prop)} {fs : List TermRun.Frame} :
    (msOfAX Λ μ p rd G own' ar J ab lbl lsize fs).K = some Scc.Sem.A64.abi := by
  cases ab <;> rfl

open Spike.Lib.A64.Flow.Ret0 (StOk LdOk LimOk OwnAt TcbOk TakeOk) in
/-- **A runtime store's facts under `msOf` are ones under the rows' memory
side** at the empty frames (`msOfAX` shares `rt`, `mp`, `G` with it). -/
theorem stOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {a v : BitVec 64} (h : StOk (msOf Λ μ rd G own lbl lsize) F exe endPc a v) :
    StOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F exe endPc a v := by
  cases ab <;> exact ⟨h.rt, h.mp, h.G, h.unmapped⟩

open Spike.Lib.A64.Flow.Ret0 (StOk LdOk LimOk OwnAt TcbOk TakeOk) in
/-- `stOk_toAX` for a load. -/
theorem ldOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {a : BitVec 64} (h : LdOk (msOf Λ μ rd G own lbl lsize) F exe endPc a) :
    LdOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F exe endPc a := by
  cases ab <;> exact ⟨h.rt, h.mp, h.unmapped⟩

open Spike.Lib.A64.Flow.Ret0 (StOk LdOk LimOk OwnAt TcbOk TakeOk) in
/-- `stOk_toAX` for the limit word. -/
theorem limOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {a Z : BitVec 64} (h : LimOk (msOf Λ μ rd G own lbl lsize) F exe endPc a Z) :
    LimOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F exe endPc a Z := by
  cases ab <;> exact ⟨h.rt, h.mp, h.unmapped, h.room⟩

open Spike.Lib.A64.Flow.Ret0 (StOk LdOk LimOk OwnAt TcbOk TakeOk) in
/-- `stOk_toAX` for an owned word. -/
theorem ownAt_toAX {ar : Arena} {ab : Option (State → Prop)} {exe : _root_.Executable} {endPc pc : Int64}
    {a v : BitVec 64} (h : OwnAt (msOf Λ μ rd G own lbl lsize) exe endPc pc a v) :
    OwnAt (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) exe endPc pc a v := by
  cases ab <;> exact h

open Spike.Lib.A64.Flow.Ret0 (StOk LdOk LimOk OwnAt TcbOk TakeOk) in
/-- `stOk_toAX` for `scc_rt_alloc_tcb`'s facts. -/
theorem tcbOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {n0 : BitVec 64} (h : TcbOk (msOf Λ μ rd G own lbl lsize) F exe endPc n0) :
    TcbOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F exe endPc n0 :=
  ⟨stOk_toAX h.next, ownAt_toAX h.own⟩

open Spike.Lib.A64.Flow.Ret0 (StOk LdOk LimOk OwnAt TcbOk TakeOk) in
/-- `stOk_toAX` for `scc_rt_stack_take`'s facts. -/
theorem takeOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {k0 : BitVec 64} (h : TakeOk (msOf Λ μ rd G own lbl lsize) F exe endPc k0) :
    TakeOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F exe endPc k0 :=
  ⟨stOk_toAX h.lock1, ldOk_toAX h.freeN, stOk_toAX h.lock0, stOk_toAX h.next, ownAt_toAX h.ownLock,
    ownAt_toAX h.ownFreeN, ownAt_toAX h.ownNext⟩

end RtX

/-! ## At a placed output -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i

open Spike.Lib.A64.Flow.Ret0 (StackM stacksA)
open Spike.Lib.A64.Rt (arOf StartEW)

/-- **`scc_rt_start`'s states are inside `W2` at any start control**
(`startEW_w2A` at `c0`): `c0` free of `ZBad` and not at an overflow (`hf0`,
`hov`), its facts (`hC0`), placed at no frame (`hpl0`). -/
theorem startEW_w2G {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS}
    {Dt : State → Prop} {lbl lbl0 : Lbl} {lsize : Lsize} {rS : Range} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {k0 : BitVec 64} {L : Int} (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0)
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).Λ.stackPool)
    (hSM : FStable R (StackM rS))
    (hSMi : FStable (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee
      Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0) (StackM rS))
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (h16 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL8 : L % 8 = 0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hpl0 : ∀ s, PlacedS (Ly).Λ lbl s c0 []) :
    StartEW (Spike.Lib.A64.Rt.nilW (W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd G (Spike.Lib.A64.PhRec.own (Ly))
        rS (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ) J Dt (Ab (Ly).lab) lbl lsize))
      (Spike.Lib.A64.PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS 0#64 k0 c0 L :=
  StartEW.imp (startEW_sfacts h i hC0 hR hal hlo hhi hFr rfl hrS hsub hSM hSMi hSMt hfit h16 hok hL8)
    (startEW_rtX h i (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ) (rS := rS) hR hal hlo hhi hFr rfl hk
      (fun a ha => ⟨Spike.Lib.A64.Rt.RuntimeLayout.hctr_of_placeOKAt h i a ha, rtWords_offArena h i a ha⟩)
      (mainPosOff_of_placeOKAt h i) h16 hok hpl0)
    fun _ _ hS hX => by
      obtain rfl := hX.2.2.2
      exact rtX_w2G hp hf0 hov hS hX

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (SetupCode SetupCallWS MainCallWS MainSW SetupArgs swFSL mainSIn) in
/-- **The consumer's `h0` at a placed output** (`startS_segWS` inside `W2`
at `L0`, `ls0` over `IN … J`): from `_start` at the empty frames, at the
source start control `c0`, under any memory side `ms` with the kernel's ABI
(`hK`; `msOfAX`'s, `msOfAX_K_abi`), `scc_rt_start`'s states from
`startEW_w2G` (its premises, the first TCB at `0`), the rest of
`startS_segWS`'s premises named: the rows' memory facts (`hhdr`, `htcb`,
`hfld`, `htk`, `hlimM`, `hlimS`, `hlimU`), the region's (`hsubR`, `hun`,
`hRS`, `houtS`, `hFt`), and `scc_rt_main`'s after a setup block at `sc`
(`hin` … `hL2`, `hS`, `hU`, `hexit`, `hW`). -/
theorem h0_of_startS {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS}
    {Dt : State → Prop} {L0 lbl0 : Lbl} {ls0 : Lsize} {ms : List TermRun.Frame → MemSide isaLSE2}
    {rS : Range} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {k0 : BitVec 64} {L : Int}
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0)
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hF : FStable R F) (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).Λ.stackPool)
    (hSM : FStable R (StackM rS))
    (hSMi : FStable (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee ThreadInit.oI.sp (-208) 0)
      (StackM rS))
    (h16t : (stacksA (Ly).lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL8 : L % 8 = 0)
    (hk0 : k0.toNat + 16384 ≤ 536870912)
    (hpl0 : ∀ s, PlacedS (Ly).Λ L0 s c0 [])
    (hK : (ms []).K = some Scc.Sem.A64.abi)
    (hhdr : StOk (ms []) F (Ly).exe (Ly).endPc (pinA (Ly).lab + 0#64) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F (Ly).exe (Ly).endPc 0#64)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (Ly).lab + 0#64 + 8#64) (stacksA (Ly).lab + k0),
      StOk (ms []) F (Ly).exe (Ly).endPc (pinA (Ly).lab + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F (Ly).exe (Ly).endPc k0)
    (hsubR : ∀ k, (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (Ly).lab + k0 + 16384#64).toNat + -L ∨
      ((stacksA (Ly).lab + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))).toNat)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    {sc : SetupCode} (hin : mainSIn (Ly).prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hL1 : sc.Z.toInt + D1 ≤ L) (hL2 : sc.Z.toInt + D2 ≤ L) {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ (Ly).exe (Ly).endPc (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
      (stacksA (Ly).lab + k0 + 16384#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ (Ly).exe (Ly).endPc (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
      (stacksA (Ly).lab + k0 + 16384#64 - sc.Z.toBitVec - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ (Ly).exe (Ly).endPc (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
      (stacksA (Ly).lab + k0 + 16384#64 - sc.Z.toBitVec - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWS (fun s c fs => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd G
        (Spike.Lib.A64.PhRec.own (Ly)) rS (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J)
        Dt (Ab (Ly).lab) L0 ls0 s c fs) (TakeK ((Ly).lab StackTake.siteL) rS) p L0 ms (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L rS (stacksA (Ly).lab + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      sc.setup sc.Z D1 ZU1 PostR ((Ly).lab sc.e0 + 4).toBitVec c0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.A64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.A64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (swR v (-L) 0)
      (swFSL L rS (stacksA (Ly).lab + k0 + 16384#64) (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (Spike.Lib.A64.Rt.mainSC (Ly).lab sc
        ⟨stacksA (Ly).lab + k0 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (pinA (Ly).lab + 0#64 + 8#64)) s c →
      W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd G (Spike.Lib.A64.PhRec.own (Ly)) rS (Spike.Lib.A64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J) Dt (Ab (Ly).lab) L0 ls0 s c [])
    (hU : ∀ v, MainCallWS (fun s c fs => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd G
        (Spike.Lib.A64.PhRec.own (Ly)) rS (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J)
        Dt (Ab (Ly).lab) L0 ls0 s c fs) (TakeK ((Ly).lab StackTake.siteL) rS) p L0 ms (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L rS (stacksA (Ly).lab + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (pinA (Ly).lab + 0#64 + 8#64)) Post ((Ly).lab sc.sp1).toBitVec
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R' F' ⟨(Ly).lab sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hW : ∀ v, MainSW (Spike.Lib.A64.Rt.nilW (fun s c fs => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd G
        (Spike.Lib.A64.PhRec.own (Ly)) rS (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J)
        Dt (Ab (Ly).lab) L0 ls0 s c fs)) (TakeK ((Ly).lab StackTake.siteL) rS) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L rS (stacksA (Ly).lab + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (ms [])
      sc PostS Post ⟨stacksA (Ly).lab + k0 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (pinA (Ly).lab + 0#64 + 8#64)) :
    SegWS (fun s c fs => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd G (Spike.Lib.A64.PhRec.own (Ly)) rS
        (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J) Dt (Ab (Ly).lab) L0 ls0 s c fs)
      (TakeK ((Ly).lab StackTake.siteL) rS) p L0 ms
      ((Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R F (entryN (Ly).lab c0)).at [])
      fun _ _ _ => False :=
  Spike.Lib.A64.Rt.startS_segWS (Ly).lays rfl (Spike.Lib.A64.Rt.rtCode0_of_placeOKAt h) hK hF hR hal hlo hhi
    0#64 k0 c0 (by decide) hhdr htcb hk0 hfld htk h16t hok hsubR hfit hout hun hRS hfitS houtS hFt
    (startEW_w2G h i hp hf0 hov hC0 hR hal hlo hhi hFr hrS hsub hSM hSMi hSMt hfitS h16t hok hL8 hk0 hpl0)
    hin h16 hZ hsw hZw hk hD10 hD18 hD20 hD28 hL1 hL2 hlimM hlimS hlimU hS hcall hPS hWC hU hexit hW

/-- **`scc_rt_main` after a setup block at a placed output** (A11 on a
`.setup` tail): its code at `setupMC sw` for some `sw < 8` (`h0_of_startS`'s
`hin`). -/
theorem mainSIn_of_placeOKAt (hs : o.place.tail = .setup) :
    ∃ sw < 8, Spike.Lib.A64.Rt.mainSIn (Ly).prog (Spike.Lib.A64.Rt.setupMC sw) = true := by
  obtain ⟨sw, hsw, hw⟩ := List.any_eq_true.mp (Scc.Cert.PlaceOK.A64.setupOk_of_placeOKAt h hs)
  exact ⟨sw, List.mem_range.mp hsw, Spike.Lib.A64.Rt.mainSIn_of_okS (Bool.and_eq_true _ _ ▸ hw).1⟩

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i).Λ o.prog o.secs

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.PhRec (GOf) in
/-- **The rows' memory facts of the start at a placed output** (`h0_of_startS`'s
`hhdr`, `htcb`, `hfld`, `htk` at the first TCB and stack, `n0 = k0 = 0`):
under the rows' memory side at no label placed and the consumer's value
invariant `GOf` (`rt_*` with `Spike/Lib/A64StartOfPlaceOK.lean`'s facts,
moved to `msOfAX` by `*_toAX`), for any frame condition giving the
runtime's words unloaded (`hFr`). -/
theorem rows_ofPlaceOK {p : Prog} {rd : TermRun.Word → Prop} {ar : Arena} {J : InvS} {ab : Option (State → Prop)}
    {lsize : Lsize} {F : MachineData → Prop} (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m) :
    StOk (msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s)
        ar J ab (fun _ => none) lsize []) F (Ly).exe (Ly).endPc (pinA (Ly).lab + 0#64)
        (AllocTcb.hdr0 ||| 1#64 <<< 36) ∧
      TcbOk (msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd (GOf Ly M0)
        (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) ar J ab (fun _ => none) lsize []) F (Ly).exe (Ly).endPc 0#64 ∧
      (∀ e ∈ ThreadInit.fields (pinA (Ly).lab + 0#64 + 8#64) (stacksA (Ly).lab + 0#64),
        StOk (msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd (GOf Ly M0)
          (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) ar J ab (fun _ => none) lsize []) F (Ly).exe (Ly).endPc
          (pinA (Ly).lab + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2) ∧
      TakeOk (msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd (GOf Ly M0)
        (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) ar J ab (fun _ => none) lsize []) F (Ly).exe (Ly).endPc 0#64 := by
  have hfree := Spike.Lib.A64.PhRec.rtFree_ofPlaceOK h i (lsize := lsize)
  rw [(Ly).lab_pin, (Ly).lab_stacks]
  refine ⟨stOk_toAX ((Spike.Lib.A64.Rt.rt_hhdr hfree (Spike.Lib.A64.PhRec.hGh_ofPlaceOK h i)).mono hFr),
    tcbOk_toAX ((Spike.Lib.A64.Rt.rt_tcbOk hfree (Spike.Lib.A64.PhRec.hGt_ofPlaceOK h i)
      (Spike.Lib.A64.PhRec.hownT_ofPlaceOK h i)).mono hFr),
    fun e he => stOk_toAX ((Spike.Lib.A64.Rt.rt_hfld hfree (Spike.Lib.A64.PhRec.hGf_ofPlaceOK h i) e he).mono hFr),
    takeOk_toAX ((Spike.Lib.A64.Rt.rt_takeOk hfree (Spike.Lib.A64.PhRec.hG1_ofPlaceOK h i)
      (Spike.Lib.A64.PhRec.hG0_ofPlaceOK h i) (Spike.Lib.A64.PhRec.hGn_ofPlaceOK h i)
      (Spike.Lib.A64.PhRec.hownL_ofPlaceOK h i) (Spike.Lib.A64.PhRec.hownF_ofPlaceOK h i)
      (Spike.Lib.A64.PhRec.hownN_ofPlaceOK h i)).mono hFr)⟩

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.PhRec (GOf) in
/-- **The limit word's facts at a placed output** (`h0_of_startS`'s `hlimM`,
`hlimS`, `hlimU`): at any bound `Z` at least the limit (the first stack's
base plus the guard), under the rows' memory side as in `rows_ofPlaceOK`,
at the runtime's frame condition. -/
theorem limOk_ofPlaceOK {p : Prog} {rd : TermRun.Word → Prop} {ar : Arena} {J : InvS} {ab : Option (State → Prop)}
    {lsize : Lsize} {Z : BitVec 64} (hZ : (Ly).stacksA.toNat + 4096 ≤ Z.toNat) :
    LimOk (msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s)
        ar J ab (fun _ => none) lsize []) (Spike.Lib.A64.Rt.rtF (Ly)) (Ly).exe (Ly).endPc
      (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) Z := by
  rw [(Ly).lab_pin]
  exact limOk_toAX (Spike.Lib.A64.Rt.rt_limOk (Spike.Lib.A64.PhRec.rtFree_ofPlaceOK h i (lsize := lsize))
    (Spike.Lib.A64.PhRec.room_of_le h i hZ))

open Spike.Lib.A64.Flow.Ret0 in
/-- **The limit word is unloaded** under a frame condition giving the
runtime's words unloaded (`h0_of_startS`'s `hun`; the first TCB's field
`1`). -/
theorem hun_ofPlaceOK {F : MachineData → Prop} (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m) :
    ∀ m, F m → Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) 8 = none := by
  intro m hm
  rw [(Ly).lab_pin, Spike.Lib.A64.Rt.limA_tcb0]
  exact hFr m hm _ ((Ly).fld_mem (by decide))

open Spike.Lib.A64.PhRec (GOf) in
/-- **`W2` at the start's placement** (no label placed, `ls0`) over
`IN … J` at the output's arena, the value invariant `GOf` and the record's
owned words: `h0_ofPlaceOK`'s world. -/
abbrev W2At (p : Prog) (rd : TermRun.Word → Prop) (rS : Range) (J : InvS) (Dt : State → Prop) (ls0 : Lsize) :
    FragS isaLSE2 := fun s c fs =>
  W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd (GOf Ly M0) (Spike.Lib.A64.PhRec.own (Ly)) rS
    (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) ls0 J) Dt (Ab (Ly).lab)
    (fun _ => none) ls0 s c fs

open Spike.Lib.A64.PhRec (GOf) in
/-- **The rows' memory side at the start's placement** (`msOfAX` as in
`W2At`, abort `ab`). -/
abbrev MSAt (p : Prog) (rd : TermRun.Word → Prop) (J : InvS) (ab : Option (State → Prop)) (ls0 : Lsize) :
    List TermRun.Frame → MemSide isaLSE2 :=
  msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s)
    (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) ls0 J) ab (fun _ => none) ls0

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (SetupCode SetupCallWS MainCallWS MainSW SetupArgs swFSL mainSIn rS0 entryR rtF) in
/-- **The consumer's `h0` at a placed output and an entry state**
(`h0_of_startS` at `E`'s region `entryR E`, the first TCB and stack
`n0 = k0 = 0`, the first stack `rS0`, the switch region of any depth
`L ≤ 16384`, no label placed, `GOf`, the rows' memory side `MSAt`): the
region's, the stack's and the rows' memory facts discharged
(`Spike/Lib/Rt/A64StartArith.lean`, `rows_ofPlaceOK`, `limOk_ofPlaceOK`,
`hun_ofPlaceOK`); left: the start control's facts (`hp`, `hf0`, `hov`,
`hC0`, `hpl0`), the frame condition
(`hFE`, `hFEs`, `hFEk`), and `scc_rt_main`'s after a setup block at `sc`
(`hin` … `hL2`, the limit's room past each frame `hZM`, `hZS`, `hZU`, `hS`,
`hU`, `hexit`, `hW`). -/
theorem h0_ofPlaceOK {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (takeMem pm (rS0 (Ly)) m))
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0) (hC0 : CFacts (Ly).Λ lbl0 c0)
    (hpl0 : ∀ s, PlacedS (Ly).Λ (fun _ => none) s c0 [])
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sc : SetupCode} (hin : mainSIn (Ly).prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hL1 : sc.Z.toInt + D1 ≤ L) (hL2 : sc.Z.toInt + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - sc.Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - sc.Z.toBitVec - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - sc.Z.toBitVec - ZU2.toBitVec).toNat)
    (hS : ∀ v, SetupCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      sc.setup sc.Z D1 ZU1 PostR ((Ly).lab sc.e0 + 4).toBitVec c0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.A64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.A64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (swR v (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64) (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (Spike.Lib.A64.Rt.mainSC (Ly).lab sc
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (pinA (Ly).lab + 0#64 + 8#64)) s c → W2At h i p rd (rS0 (Ly)) J Dt ls0 s c [])
    (hU : ∀ v, MainCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (pinA (Ly).lab + 0#64 + 8#64)) Post ((Ly).lab sc.sp1).toBitVec
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R' F' ⟨(Ly).lab sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (MSAt h i p rd J ab ls0 []).abortAt s →
        MainExitS p (MSAt h i p rd J ab ls0 []) s c v.toNat)
    (hW : ∀ v, MainSW (Spike.Lib.A64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (MSAt h i p rd J ab ls0 [])
      sc PostS Post ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (pinA (Ly).lab + 0#64 + 8#64)) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (entryR E) FE (entryN (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hSM := stackM_rS0 (Ly) hE
  obtain ⟨hhdr, htcb, hfld, htk⟩ := rows_ofPlaceOK h i (p := p) (rd := rd) (ar := arOf (Ly).Λ)
    (J := IN (arOf (Ly).Λ) (fun _ => none) ls0 J) (ab := ab) (lsize := ls0) hFE
  refine h0_of_startS h i (k0 := 0#64) hp hf0 hov hC0 (Spike.Lib.A64.Rt.entryR_ok hE)
    (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide)
    hFEs hFE (rS0_eq_lab _) hsub hSM.1 hSM.2.1 hSM.2.2
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _)
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL) hL8 (by simp) hpl0
    msOfAX_K_abi hhdr htcb hfld htk
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ hL0 hL)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_houtD _ hL0 hL)
    (hun_ofPlaceOK h i hFE) (Spike.Lib.A64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
    (Spike.Lib.A64.Rt.outS_of_sub _ hE hsub) hFEk hin h16 hZ hsw hZw hk hD10 hD18 hD20 hD28 hL1 hL2
    (limOk_ofPlaceOK h i hZM) (limOk_ofPlaceOK h i hZS) (limOk_ofPlaceOK h i hZU) hS hcall hPS hWC hU hexit
    hW

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.rtX_w2G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtX_w2G

/-- info: 'Spike.Lib.LowerA64.startEW_w2G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_w2G

/-- info: 'Spike.Lib.LowerA64.h0_of_startS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_of_startS

/-- info: 'Spike.Lib.LowerA64.rows_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rows_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.limOk_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms limOk_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.hun_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hun_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.h0_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK

end Spike.Lib.LowerA64
