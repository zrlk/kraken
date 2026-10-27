/-
**The start's segment inside `W2`** (x86-64, the consumer's `h0`): the twin
of `Spike/Lib/LowerA64/Start2W2.lean`.

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
- `MainSW.imp`, `MainSW.ofFalse`: `scc_rt_main`'s obligations from two, and
  under an unsatisfiable frame condition;
- `h0_of_startS_setup`: `h0_of_startS` at an output with a setup block,
  `scc_rt_main`'s code and phase facts at the `sw < 6` of A11
  (`mainPhS_of_placeOKAt`), its frame's facts decided, its obligations
  inside `nilW W2` from ones inside any `W1` (`hW1`) and `mainSW_rtM`, `W1`
  and `RtM` together giving `W2` (`hw`);
- `rows_ofPlaceOK` (`hhdr`, `htcb`, `hfld`, `htk` at `n0 = k0 = 0`, no label
  placed, `G = GOf`), `limOk_ofPlaceOK` (`hlim*` at any bound past the
  limit), `hun_ofPlaceOK` (`hun`);
- `h0_ofPlaceOK`: `h0_of_startS` at a placed output and an entry state `E`
  (`entryR E`, `rS0`, `W2At`, `MSAt`), the region's, stack's and rows'
  memory facts discharged;
- `MainCtl`, `rtM_w2`: the source control's facts `scc_rt_main` keeps, and
  `W2` at a runtime state from `SFacts`, `RtM` and them;
- `BlkW.ofCtl`, `NodeW.ofCtl`, `MainSW.ofCtl`: obligations inside `W ∧ Q`
  from ones inside `W`, `Q` of each node's control;
- `h0_ofPlaceOK_setup`: `h0_ofPlaceOK` at `setupMC sw`, `scc_rt_main`'s own
  obligations discharged (`mainSW_sfacts`, `MainSW.ofCtl`, `mainSW_rtM`,
  `rtM_w2`) from `CFacts ∧ MainCtl` of the controls back from the setup
  block and the user function (`hPostS`, `hPost`), the setup call's node
  from `hWC_ofPlaceOK`;
- `hWC_ofPlaceOK`: the setup call's node inside `W2At` at a placed output
  (`h0_ofPlaceOK`'s `hWC`), from `rtM_sfacts_setupEntry` and `rtM_w2`.
-/
import Spike.Lib.LowerX64.StartEW2
import Spike.Lib.LowerX64.Levels2
import Spike.Lib.LowerX64.RtMainX
import Spike.Lib.LowerX64.RtMainSX
import Spike.Lib.Rt.X64MainSS
import Spike.Lib.X64StartOfPlaceOK
import Spike.Lib.X64PhPinsOfPlaceOK
import Spike.Lib.Rt.X64StartArith

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND swR FStable)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Scc.Sem.X64 (abi pcOf)

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
    (msOfAX Λ μ p rd G own' ar J ab lbl lsize fs).K = some Scc.Sem.X64.abi := by
  cases ab <;> rfl

open Spike.Lib.X64.Flow.Ret0 (StOk LdOk LimOk TcbOk TakeOk) in
/-- **A runtime store's facts under `msOf` are ones under the rows' memory
side** at the empty frames (`msOfAX` shares `rt`, `mp`, `G` with it). -/
theorem stOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {a v : BitVec 64}
    (h : StOk (msOf Λ μ rd G own lbl lsize) F a v) :
    StOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F a v := by
  cases ab <;> exact ⟨h.rt, h.mp, h.G, h.unmapped⟩

open Spike.Lib.X64.Flow.Ret0 (StOk LdOk LimOk TcbOk TakeOk) in
/-- `stOk_toAX` for a load. -/
theorem ldOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {a : BitVec 64}
    (h : LdOk (msOf Λ μ rd G own lbl lsize) F a) :
    LdOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F a := by
  cases ab <;> exact ⟨h.rt, h.mp, h.unmapped⟩

open Spike.Lib.X64.Flow.Ret0 (StOk LdOk LimOk TcbOk TakeOk) in
/-- `stOk_toAX` for the limit word. -/
theorem limOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {a Z : BitVec 64}
    (h : LimOk (msOf Λ μ rd G own lbl lsize) F a Z) :
    LimOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F a Z := by
  cases ab <;> exact ⟨h.rt, h.mp, h.unmapped, h.room⟩

/-- `stOk_toAX` for an owned word. -/
theorem ownAt_toAX {ar : Arena} {ab : Option (State → Prop)} {exe : _root_.Executable} {endPc pc : Int64}
    {a v : BitVec 64} (h : Spike.Lib.X64.OwnAt (msOf Λ μ rd G own lbl lsize) exe endPc pc a v) :
    Spike.Lib.X64.OwnAt (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) exe endPc pc a v := by
  cases ab <;> exact h

open Spike.Lib.X64.Flow.Ret0 (StOk LdOk LimOk TcbOk TakeOk) in
/-- `stOk_toAX` for `scc_rt_alloc_tcb`'s facts. -/
theorem tcbOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {n0 : BitVec 64} (h : TcbOk (msOf Λ μ rd G own lbl lsize) F exe endPc n0) :
    TcbOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F exe endPc n0 :=
  ⟨stOk_toAX h.next, ownAt_toAX h.own⟩

open Spike.Lib.X64.Flow.Ret0 (StOk LdOk LimOk TcbOk TakeOk) in
/-- `stOk_toAX` for `scc_rt_stack_take`'s facts. -/
theorem takeOk_toAX {ar : Arena} {ab : Option (State → Prop)} {F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {k0 : BitVec 64} (h : TakeOk (msOf Λ μ rd G own lbl lsize) F exe endPc k0) :
    TakeOk (msOfAX Λ μ p rd G (fun s _ => own s) ar J ab lbl lsize []) F exe endPc k0 :=
  ⟨stOk_toAX h.lock1, ldOk_toAX h.freeN, stOk_toAX h.lock0, stOk_toAX h.next, ownAt_toAX h.ownLock,
    ownAt_toAX h.ownFreeN, ownAt_toAX h.ownNext⟩

/-- **The source control's facts `scc_rt_main` keeps**: free of `ZBad` at
no frame, not at an overflow, placed at no frame at `L0` in every state
(`rtM_w2`'s, the start control's `hf0`, `hov`, `hpl0`). -/
def MainCtl (Λ : Scc.Sem.Layout) (L0 : Lbl) (c : Ctl) : Prop :=
  FrOk2 c [] ∧ ¬ OvfReady c ∧ ∀ s, PlacedS Λ L0 s c []

/-- **`W2` at a runtime state at no frame, at a control with `MainCtl`**:
`rtX_w2G` with `RtM` in place of `RtX`, the control's placement and its
facts from `MainCtl`. -/
theorem rtM_w2 (hp : ProgNoS ZBad p) {s : State} {c : Ctl} (hS : SFacts Λ μ own rS Tk lbl0 s c)
    (hM : RtM μ ar lab s c) (hQ : MainCtl Λ lbl c) : W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c [] := by
  have hP := w2Part_of_wrOff (J := J) (rd := rd) (G := G) (p := p) (lsize := lsize) hM.1 (hQ.2.2 s) hM.2 hS
  exact w2_of hp hQ.1 (hS.toSt.dt_mono fun _ h => h.elim) hP.1 (fun _ => hS.noRet) (.of_placedS hP.2.1) hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts hQ.2.1 hS)) hP.2.2.2

end RtX

/-! ## `scc_rt_main`'s obligations from two -/

section MainW

open Spike.Lib.X64.Rt (MainSW SetupCode)
open Spike.Lib.X64.AllocG (BlkW.imp NodeW.imp)

variable {W W1 W2 : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {sc : SetupCode} {PostS : Ctl → Reg64s → Prop}
  {Post : Ctl → BitVec 64 → Prop} {g : Spike.Lib.X64.Flow.Ret0.MainG} {x0 : BitVec 64}

/-- **`scc_rt_main`'s own states inside `W`** from ones inside `W1` not
moved by `K` and ones inside `W2`, `W1 ∧ W2` inside `W`. -/
theorem MainSW.imp (h1 : MainSW W1 K exe endPc R F ms sc PostS Post g x0)
    (h2 : MainSW W2 (fun _ _ => False) exe endPc R F ms sc PostS Post g x0)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : MainSW W K exe endPc R F ms sc PostS Post g x0 :=
  ⟨⟨BlkW.imp h1.pro.w0 h2.pro.w0 hw, BlkW.imp h1.pro.w1 h2.pro.w1 hw, NodeW.imp h1.pro.w2 h2.pro.w2 hw,
      BlkW.imp h1.pro.w3 h2.pro.w3 hw, BlkW.imp h1.pro.w4 h2.pro.w4 hw⟩,
    BlkW.imp h1.call0 h2.call0 hw, BlkW.imp h1.sp0 h2.sp0 hw,
    ⟨BlkW.imp h1.exit.w0 h2.exit.w0 hw, NodeW.imp h1.exit.w1 h2.exit.w1 hw⟩⟩

/-- `scc_rt_main`'s own obligations under an unsatisfiable frame condition. -/
theorem MainSW.ofFalse (h : ∀ m, ¬ F m) : MainSW W K exe endPc R F ms sc PostS Post g x0 :=
  ⟨⟨Spike.Lib.X64.Rt.blkW_ofFalse h, Spike.Lib.X64.Rt.blkW_ofFalse h, Spike.Lib.X64.Rt.nodeW_ofFalse h,
      Spike.Lib.X64.Rt.blkW_ofFalse h, Spike.Lib.X64.Rt.blkW_ofFalse h⟩,
    Spike.Lib.X64.Rt.blkW_ofFalse h, Spike.Lib.X64.Rt.blkW_ofFalse h,
    ⟨Spike.Lib.X64.Rt.blkW_ofFalse h, Spike.Lib.X64.Rt.nodeW_ofFalse h⟩⟩

/-- **A block node inside `W ∧ Q`** from one inside `W`, `Q` of the
node's control. -/
theorem BlkW.ofCtl {Q : Ctl → Prop} {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk)
    (hQ : ∀ σ c, n.J σ c → Q c) : BlkW (fun s c => W s c ∧ Q c) K exe endPc R F n blk :=
  fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD =>
    ⟨⟨(h s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1, hQ σ c hJ⟩, (h s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2⟩

/-- **A node inside `W ∧ Q`** from one inside `W`, `Q` of the node's
control. -/
theorem NodeW.ofCtl {Q : Ctl → Prop} {n : ND} (h : NodeW W K exe endPc R F n) (hQ : ∀ σ c, n.J σ c → Q c) :
    NodeW (fun s c => W s c ∧ Q c) K exe endPc R F n := fun s c hA =>
  ⟨⟨(h s c hA).1, hQ _ c hA.2.2.2.2.choose_spec.2.2⟩, (h s c hA).2⟩

/-- **`scc_rt_main`'s own states inside `W ∧ Q`** from ones inside `W`, `Q`
of the entry's control (`hC0`), of the control back from the setup block
(`hPS`) and back from the user function (`hP`). -/
theorem MainSW.ofCtl {Q : Ctl → Prop} (h : MainSW W K exe endPc R F ms sc PostS Post g x0) (hC0 : Q g.c0)
    (hPS : ∀ c rs, PostS c rs → Q c) (hP : ∀ c v, Post c v → Q c) :
    MainSW (fun s c => W s c ∧ Q c) K exe endPc R F ms sc PostS Post g x0 :=
  ⟨⟨BlkW.ofCtl h.pro.w0 fun _ _ hJ => hJ.1.1 ▸ hC0, BlkW.ofCtl h.pro.w1 fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ hC0,
      NodeW.ofCtl h.pro.w2 fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ hC0,
      BlkW.ofCtl h.pro.w3 fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0,
      BlkW.ofCtl h.pro.w4 fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0⟩,
    BlkW.ofCtl h.call0 fun _ _ hJ => hJ.1.1 ▸ hC0, BlkW.ofCtl h.sp0 fun _ _ hJ => hPS _ _ hJ.1.1,
    ⟨BlkW.ofCtl h.exit.w0 fun _ _ hJ => hP _ _ hJ.1, NodeW.ofCtl h.exit.w1 fun _ _ ⟨_, _, hJ, _⟩ => hP _ _ hJ.1⟩⟩

end MainW

/-! ## At a placed output -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i

open Spike.Lib.X64.Flow.Ret0 (stacksA)
open Spike.Lib.X64.Rt (arOf StartEW)

/-- **`scc_rt_start`'s states are inside `W2` at any start control**
(`startEW_w2A` at `c0`): `c0` free of `ZBad` and not at an overflow (`hf0`,
`hov`), its facts (`hC0`), placed at no frame (`hpl0`). -/
theorem startEW_w2G {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS}
    {Dt : State → Prop} {lbl lbl0 : Lbl} {lsize : Lsize} {rS : Range} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {k0 : BitVec 64} {L : Int} (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0)
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hR : R.OK) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (h8 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hpl0 : ∀ s, PlacedS (Ly).Λ lbl s c0 []) :
    StartEW (Spike.Lib.X64.Rt.nilW (W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G (Spike.Lib.X64.PhRec.own (Ly))
        rS (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) J Dt (Ab (Ly).lab) lbl lsize))
      (Spike.Lib.X64.PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS 0#64 k0 c0 L
      (Spike.Lib.X64.Rt.tiOf o.place.tail) :=
  StartEW.imp (startEW_sfacts h i hC0 hR hlo hhi hFr hrS hsub hout h8 hok hL hL8)
    (startEW_rtX h i (ar := Spike.Lib.X64.Rt.arOf (Ly).Λ) (rS := rS) hR hlo hhi hFr hk
      (fun a ha => ⟨Spike.Lib.X64.Rt.RuntimeLayout.hctr_of_placeOKAt h i a ha, rtWords_offArena h i a ha⟩)
      (mainPosOff_of_placeOKAt h i) hL hok hpl0)
    fun _ _ hS hX => by
      obtain rfl := hX.2.2.2
      exact rtX_w2G hp hf0 hov hS hX

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWS MainSW SetupArgs swFSL mainSIn oU) in
open Spike.Lib.AllocReach (IN) in
/-- **The consumer's `h0` at a placed output** (`startS_segWS` inside `W2`
at `L0`, `ls0` over `IN … J`): from `_start` at the empty frames, at the
source start control `c0`, under any memory side `ms` with the kernel's ABI
(`hK`; `msOfAX`'s, `msOfAX_K_abi`), `scc_rt_start`'s states from
`startEW_w2G` (its premises, the first TCB at `0`), the rest of
`startS_segWS`'s premises named: the rows' memory facts (`hhdr`, `htcb`,
`hfld`, `htk`, `hlimM`, `hlimS`, `hlimU`), the region's (`hal`, `hsubR`,
`hun`, `hRS`, `houtS`, `hFt`), and `scc_rt_main`'s after a setup block at
`sc` (`hin` … `hL2`, `hS`, `hU`, `hexit`, `hW`). -/
theorem h0_of_startS {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS}
    {Dt : State → Prop} {L0 lbl0 : Lbl} {ls0 : Lsize} {ms : List TermRun.Frame → MemSide isa}
    {rS : Range} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {k0 : BitVec 64} {L : Int}
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0)
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hF : FStable R F) (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (h8 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hk0 : k0.toNat + 16384 ≤ 536870912)
    (hpl0 : ∀ s, PlacedS (Ly).Λ L0 s c0 [])
    (hK : (ms []).K = some Scc.Sem.X64.abi)
    (hhdr : StOk (ms []) F (pinA (Ly).lab + 0#64) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F (Ly).exe (Ly).endPc 0#64)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (Ly).lab + 0#64 + 8#64) (stacksA (Ly).lab + k0),
      StOk (ms []) F (pinA (Ly).lab + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F (Ly).exe (Ly).endPc k0)
    (hsubR : ∀ k, (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (Ly).lab + k0 + 16384#64).toNat + -L ∨
      ((stacksA (Ly).lab + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    {sc : SetupCode} (hin : mainSIn (Ly).prog sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hL1 : 8 + 8 + sc.Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + sc.Z.toInt + 8 + D2 ≤ L)
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
      (stacksA (Ly).lab + k0 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
      (stacksA (Ly).lab + k0 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
      (stacksA (Ly).lab + k0 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWS (fun s c fs => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G
        (Spike.Lib.X64.PhRec.own (Ly)) rS (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J)
        Dt (Ab (Ly).lab) L0 ls0 s c fs) (TakeK ((Ly).lab StackTake.siteL) rS) p L0 ms (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (Ly).lab + k0 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.setup sc.Z D1 ZU1 PostR ((Ly).lab sc.sp0).toBitVec c0 (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.X64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, Spike.Lib.X64.At (Ly).exe (Ly).endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (Ly).lab + k0 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (Spike.Lib.X64.Rt.mainSC (Ly).lab sc
        ⟨stacksA (Ly).lab + k0 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) s c →
      W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G (Spike.Lib.X64.PhRec.own (Ly)) rS (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J) Dt (Ab (Ly).lab) L0 ls0 s c [])
    (hU : ∀ v, MainCallWS (fun s c fs => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G
        (Spike.Lib.X64.PhRec.own (Ly)) rS (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J)
        Dt (Ab (Ly).lab) L0 ls0 s c fs) (TakeK ((Ly).lab StackTake.siteL) rS) p L0 ms (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (Ly).lab + k0 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) Post
      ((Ly).lab sc.sp1).toBitVec (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F' ⟨(Ly).lab sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hW : ∀ v, MainSW (Spike.Lib.X64.Rt.nilW (fun s c fs => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G
        (Spike.Lib.X64.PhRec.own (Ly)) rS (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J)
        Dt (Ab (Ly).lab) L0 ls0 s c fs)) (TakeK ((Ly).lab StackTake.siteL) rS) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (Ly).lab + k0 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (ms [])
      sc PostS Post ⟨stacksA (Ly).lab + k0 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) :
    SegWS (fun s c fs => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G (Spike.Lib.X64.PhRec.own (Ly)) rS
        (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J) Dt (Ab (Ly).lab) L0 ls0 s c fs)
      (TakeK ((Ly).lab StackTake.siteL) rS) p L0 ms
      ((Spike.Lib.X64.At (Ly).exe (Ly).endPc R F (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [])
      fun _ _ _ => False :=
  Spike.Lib.X64.Rt.startS_segWS (Ly).lays rfl (Spike.Lib.X64.Rt.rtCodeTi_of_placeOKAt h) hK hF hR hal hlo hhi
    0#64 k0 c0 (by decide) hhdr htcb hk0 hfld htk hok hsubR hfit hout hun hRS hfitS houtS hFt
    (startEW_w2G h i hp hf0 hov hC0 hR hlo hhi hFr hrS hsub houtS h8 hok hL hL8 hk0 hpl0)
    hin hZ8 hsw hZw hk hD10 hD18 hD20 hD28 hL1 hL2 hL8 hlimM hlimS hlimU hS hcall hPS hWC hU hexit hW

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWS MainSW SetupArgs swFSL mainSIn oU setupMC rtCodeOkS) in
open Spike.Lib.AllocReach (IN) in
/-- **The consumer's `h0` at a placed output with a setup block**
(`h0_of_startS` at `setupMC sw`): `scc_rt_main`'s code and phase facts at
the `sw < 6` of A11 (`hc`, `hph`, from `mainPhS_of_placeOKAt`), its frame's
facts decided, its obligations inside `W2` from ones inside `W1` (`hW1`)
and `mainSW_rtM` (the growth path, the setup block and the user function
positioned off the write abort: `hgrow`, `hset`, `hfn`), `W1` and `RtM`
giving `W2` (`hw`). -/
theorem h0_of_startS_setup {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS}
    {Dt : State → Prop} {L0 lbl0 : Lbl} {ls0 : Lsize} {ms : List TermRun.Frame → MemSide isa}
    {rS : Range} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {k0 : BitVec 64} {L : Int}
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0)
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hF : FStable R F) (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (h8 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hk0 : k0.toNat + 16384 ≤ 536870912)
    (hpl0 : ∀ s, PlacedS (Ly).Λ L0 s c0 [])
    (hK : (ms []).K = some Scc.Sem.X64.abi)
    (hhdr : StOk (ms []) F (pinA (Ly).lab + 0#64) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F (Ly).exe (Ly).endPc 0#64)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (Ly).lab + 0#64 + 8#64) (stacksA (Ly).lab + k0),
      StOk (ms []) F (pinA (Ly).lab + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F (Ly).exe (Ly).endPc k0)
    (hsubR : ∀ k, (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (Ly).lab + k0 + 16384#64).toNat + -L ∨
      ((stacksA (Ly).lab + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hL1 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D2 ≤ L)
    {F₀ : MachineData → Prop} {W1 : Frag isa}
    (hlimM : LimOk (ms []) F₀ (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
      (stacksA (Ly).lab + k0 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
      (stacksA (Ly).lab + k0 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec - 8#64 - 8#64 - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
      (stacksA (Ly).lab + k0 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWS (fun s c fs => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G
        (Spike.Lib.X64.PhRec.own (Ly)) rS (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J)
        Dt (Ab (Ly).lab) L0 ls0 s c fs) (TakeK ((Ly).lab StackTake.siteL) rS) p L0 ms (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (Ly).lab + k0 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).sp0).toBitVec c0
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.X64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, Spike.Lib.X64.At (Ly).exe (Ly).endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (Ly).lab + k0 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (Spike.Lib.X64.Rt.mainSC (Ly).lab (setupMC sw)
        ⟨stacksA (Ly).lab + k0 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) s c →
      W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G (Spike.Lib.X64.PhRec.own (Ly)) rS (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J) Dt (Ab (Ly).lab) L0 ls0 s c [])
    (hU : ∀ v, MainCallWS (fun s c fs => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G
        (Spike.Lib.X64.PhRec.own (Ly)) rS (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J)
        Dt (Ab (Ly).lab) L0 ls0 s c fs) (TakeK ((Ly).lab StackTake.siteL) rS) p L0 ms (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (Ly).lab + k0 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2
      (SetupArgs PostS (setupMC sw).sw (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F' ⟨(Ly).lab (setupMC sw).sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU (setupMC sw).Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hW1 : ∀ v, MainSW W1 (TakeK ((Ly).lab StackTake.siteL) rS) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (Ly).lab + k0 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (ms [])
      (setupMC sw) PostS Post ⟨stacksA (Ly).lab + k0 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
    (hw : ∀ s c, W1 s c → RtM (Spike.Lib.X64.PhRec.μ (Ly)) (arOf (Ly).Λ) (Ly).lab s c →
      W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G
        (Spike.Lib.X64.PhRec.own (Ly)) rS (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J)
        Dt (Ab (Ly).lab) L0 ls0 s c []) :
    SegWS (fun s c fs => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G (Spike.Lib.X64.PhRec.own (Ly)) rS
        (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) L0 ls0 J) Dt (Ab (Ly).lab) L0 ls0 s c fs)
      (TakeK ((Ly).lab StackTake.siteL) rS) p L0 ms
      ((Spike.Lib.X64.At (Ly).exe (Ly).endPc R F (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  refine h0_of_startS h i hp hf0 hov hC0 hR hal hlo hhi hF hFr hrS hsub h8 hok hL hL8 hk0 hpl0 hK hhdr htcb
    hfld htk hsubR hfit hout hun hRS hfitS houtS hFt (Spike.Lib.X64.Rt.mainSIn_of_okS hc)
    (by rw [hZ]; omega) (show sw ≤ 5 by omega) (by show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega)
    (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, hk]; refine ⟨?_, ?_, ?_⟩ <;> omega)
    hD10 hD18 hD20 hD28 hL1 hL2 hlimM hlimS hlimU hS hcall hPS hWC hU hexit fun v => ?_
  by_cases hv : v = stacksA (Ly).lab + k0 + 16384#64
  · subst hv
    obtain ⟨hR', -⟩ := Spike.Lib.X64.Rt.mainE_ok (rS := rS) (tcb := pinA (Ly).lab + 0#64 + 8#64)
      (top := stacksA (Ly).lab + k0 + 16384#64) hL hL8 hok hfit hout hfitS
    exact MainSW.imp (hW1 _)
      (mainSW_rtM hI (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
        hsw (Spike.Lib.X64.Rt.mainSIn_of_okS hc)
        hph hgrow hset hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide))
      fun s c h1 h2 => hw s c h1 h2
  · exact MainSW.ofFalse fun m hm => hv hm.1.1.1

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i).Λ o.prog o.secs

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.PhRec (GOf) in
/-- **The rows' memory facts of the start at a placed output** (`h0_of_startS`'s
`hhdr`, `htcb`, `hfld`, `htk` at the first TCB and stack, `n0 = k0 = 0`):
under the rows' memory side at no label placed and the consumer's value
invariant `GOf` (`rt_*` with `Spike/Lib/X64StartOfPlaceOK.lean`'s facts and
`Spike/Lib/X64PhPinsOfPlaceOK.lean`'s phases, moved to `msOfAX` by
`*_toAX`), for any frame condition giving the runtime's words unloaded
(`hFr`). -/
theorem rows_ofPlaceOK {p : Prog} {rd : TermRun.Word → Prop} {ar : Arena} {J : InvS} {ab : Option (State → Prop)}
    {lsize : Lsize} {F : MachineData → Prop} (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) :
    StOk (msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
        ar J ab (fun _ => none) lsize []) F (pinA (Ly).lab + 0#64) (AllocTcb.hdr0 ||| 1#64 <<< 36) ∧
      TcbOk (msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0)
        (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) ar J ab (fun _ => none) lsize []) F (Ly).exe (Ly).endPc 0#64 ∧
      (∀ e ∈ ThreadInit.fields (pinA (Ly).lab + 0#64 + 8#64) (stacksA (Ly).lab + 0#64),
        StOk (msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0)
          (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) ar J ab (fun _ => none) lsize []) F
          (pinA (Ly).lab + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2) ∧
      TakeOk (msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0)
        (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) ar J ab (fun _ => none) lsize []) F (Ly).exe (Ly).endPc 0#64 := by
  have hfree := Spike.Lib.X64.PhRec.rtFree_ofPlaceOK h i (lsize := lsize)
  rw [(Ly).lab_pin, (Ly).lab_stacks]
  refine ⟨stOk_toAX ((Spike.Lib.X64.Rt.rt_hhdr hfree (Spike.Lib.X64.PhRec.hGh_ofPlaceOK h i)).mono hFr),
    tcbOk_toAX ((Spike.Lib.X64.Rt.rt_tcbOk hfree (Spike.Lib.X64.PhRec.hGt_ofPlaceOK h i)
      (Spike.Lib.X64.PhRec.hownT_of_ph h i (by rw [Spike.Lib.X64.PhRec.hphT_ofPlaceOK h i]))).mono hFr),
    fun e he => stOk_toAX ((Spike.Lib.X64.Rt.rt_hfld hfree (Spike.Lib.X64.PhRec.hGf_ofPlaceOK h i) e he).mono hFr),
    takeOk_toAX ((Spike.Lib.X64.Rt.rt_takeOk hfree (Spike.Lib.X64.PhRec.hG1_ofPlaceOK h i)
      (Spike.Lib.X64.PhRec.hG0_ofPlaceOK h i) (Spike.Lib.X64.PhRec.hGn_ofPlaceOK h i)
      (Spike.Lib.X64.PhRec.hownL_of_ph h i (by rw [Spike.Lib.X64.PhRec.hphL_ofPlaceOK h i]))
      (Spike.Lib.X64.PhRec.hownF_ofPlaceOK h i)
      (Spike.Lib.X64.PhRec.hownN_of_ph h i (by rw [Spike.Lib.X64.PhRec.hphN_ofPlaceOK h i]))).mono hFr)⟩

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.PhRec (GOf) in
/-- **The limit word's facts at a placed output** (`h0_of_startS`'s `hlimM`,
`hlimS`, `hlimU`): at any bound `Z` at least the limit (the first stack's
base plus the guard), under the rows' memory side as in `rows_ofPlaceOK`,
at the runtime's frame condition. -/
theorem limOk_ofPlaceOK {p : Prog} {rd : TermRun.Word → Prop} {ar : Arena} {J : InvS} {ab : Option (State → Prop)}
    {lsize : Lsize} {Z : BitVec 64} (hZ : (Ly).stacksA.toNat + 4096 ≤ Z.toNat) :
    LimOk (msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
        ar J ab (fun _ => none) lsize []) (Spike.Lib.X64.Rt.rtF (Ly))
      (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) Z := by
  rw [(Ly).lab_pin]
  exact limOk_toAX (Spike.Lib.X64.Rt.rt_limOk (Spike.Lib.X64.PhRec.rtFree_ofPlaceOK h i (lsize := lsize))
    (Spike.Lib.X64.PhRec.room_of_le h i hZ))

open Spike.Lib.X64.Flow.Ret0 in
/-- **The limit word is unloaded** under a frame condition giving the
runtime's words unloaded (`h0_of_startS`'s `hun`; the first TCB's field
`1`). -/
theorem hun_ofPlaceOK {F : MachineData → Prop} (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) :
    ∀ m, F m → Mem.loadInt m.dmem (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) 8 = none := by
  intro m hm
  rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]
  exact hFr m hm _ ((Ly).fld_mem (by decide))

open Spike.Lib.AllocReach (IN) in
open Spike.Lib.X64.PhRec (GOf) in
/-- **`W2` at the start's placement** (no label placed, `ls0`) over
`IN … J` at the output's arena, the value invariant `GOf` and the record's
owned words: `h0_ofPlaceOK`'s world. -/
abbrev W2At (p : Prog) (rd : TermRun.Word → Prop) (rS : Range) (J : InvS) (Dt : State → Prop) (ls0 : Lsize) :
    FragS isa := fun s c fs =>
  W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) rS
    (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) ls0 J) Dt (Ab (Ly).lab)
    (fun _ => none) ls0 s c fs

open Spike.Lib.AllocReach (IN) in
open Spike.Lib.X64.PhRec (GOf) in
/-- **The rows' memory side at the start's placement** (`msOfAX` as in
`W2At`, abort `ab`). -/
abbrev MSAt (p : Prog) (rd : TermRun.Word → Prop) (J : InvS) (ab : Option (State → Prop)) (ls0 : Lsize) :
    List TermRun.Frame → MemSide isa :=
  msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
    (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) ls0 J) ab (fun _ => none) ls0

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWS MainSW SetupArgs swFSL mainSIn oU rS0 entryR rtF) in
open Spike.Lib.AllocReach (IN) in
/-- **The consumer's `h0` at a placed output and an entry state**
(`h0_of_startS` at `E`'s region `entryR E`, the first TCB and stack
`n0 = k0 = 0`, the first stack `rS0`, the switch region of any depth
`8 ≤ L ≤ 16384`, no label placed, `GOf`, the rows' memory side `MSAt`): the
region's, the stack's and the rows' memory facts discharged
(`Spike/Lib/Rt/X64StartArith.lean`, `rows_ofPlaceOK`, `limOk_ofPlaceOK`,
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
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sc : SetupCode} (hin : mainSIn (Ly).prog sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hL1 : 8 + 8 + sc.Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + sc.Z.toInt + 8 + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec).toNat)
    (hS : ∀ v, SetupCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.setup sc.Z D1 ZU1 PostR ((Ly).lab sc.sp0).toBitVec c0 (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.X64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, Spike.Lib.X64.At (Ly).exe (Ly).endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (Spike.Lib.X64.Rt.mainSC (Ly).lab sc
        ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) s c → (W2At h i p rd (rS0 (Ly)) J Dt ls0) s c [])
    (hU : ∀ v, MainCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) Post
      ((Ly).lab sc.sp1).toBitVec (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F' ⟨(Ly).lab sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ (MSAt h i p rd J ab ls0 []).abortAt s → MainExitS p (MSAt h i p rd J ab ls0 []) s c v.toNat)
    (hW : ∀ v, MainSW (Spike.Lib.X64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (MSAt h i p rd J ab ls0 [])
      sc PostS Post ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.X64.At (Ly).exe (Ly).endPc (entryR E) FE (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hL0 : (0 : Int) ≤ L := by omega
  obtain ⟨hhdr, htcb, hfld, htk⟩ := rows_ofPlaceOK h i (p := p) (rd := rd) (ar := arOf (Ly).Λ)
    (J := IN (arOf (Ly).Λ) (fun _ => none) ls0 J) (ab := ab) (lsize := ls0) hFE
  refine h0_of_startS h i (k0 := 0#64) hp hf0 hov hC0 (Spike.Lib.X64.Rt.entryR_ok hE)
    (Spike.Lib.X64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide)
    hFEs hFE (by rw [Spike.Lib.X64.Rt.stacksA_lab0]) hsub
    (by rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega)
    (by rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm) hL hL8 (by decide)
    hpl0 msOfAX_K_abi hhdr htcb hfld htk
    (by rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ hL0 hLm)
    (by rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _)
    (by rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hLm)
    (hun_ofPlaceOK h i hFE) (Spike.Lib.X64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub) hFEk hin hZ8 hsw hZw hk hD10 hD18 hD20 hD28 hL1 hL2
    (limOk_ofPlaceOK h i hZM) (limOk_ofPlaceOK h i hZS) (limOk_ofPlaceOK h i hZU) hS hcall hPS hWC hU hexit hW

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (swFSL rS0 setupMC) in
/-- **The setup block's call node inside `W2At`** (`h0_ofPlaceOK`'s `hWC`
at `setupMC sw`) at a placed output: `rtM_sfacts_setupEntry` at the record
in `scc_rt_main`'s region, joined by `rtM_w2` with the entry's control's
`MainCtl` (`hQ0`); left: the setup function's prologue (`hpro`), its
head's phase facts (`hph`), its label and stack check label off the write
abort (`hl`, `hlc`), the entry's control's `CFacts` (`hC0`), and the
setup block's room `D1` holding the head's push (`hD8`). -/
theorem hWC_ofPlaceOK {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p) (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) {D1 : Int} (hD8 : 8 ≤ D1) (hL1 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D1 ≤ L)
    {chk entry : Label} {Z lim : Int64} {Lg : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hpro : Spike.Lib.X64.Flow.prologueIn (Ly).prog (setupMC sw).setup chk entry Z lim Lg zl zf z1 z2 zs ps = true)
    (hph : blkPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab (setupMC sw).setup + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true)
    (hl : (setupMC sw).setup ∉ Spike.Lib.X64.AllocG.abLabs) (hlc : chk ∉ Spike.Lib.X64.AllocG.abLabs)
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hQ0 : MainCtl (Ly).Λ (fun _ => none) c0) :
    ∀ v s c, Spike.Lib.X64.At (Ly).exe (Ly).endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (Spike.Lib.X64.Rt.mainSC (Ly).lab (setupMC sw)
        ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) s c → (W2At h i p rd (rS0 (Ly)) J Dt ls0) s c [] := by
  intro v
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hZ := setupMC_Z sw hsw
    have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
    have hL0 : (0 : Int) ≤ L := by omega
    have h8 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm
    have hfit : (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64 := by
      rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
    have hout : ((limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
          (stacksA (Ly).lab + 0#64 + 16384#64).toNat + -L ∨
        ((stacksA (Ly).lab + 0#64 + 16384#64).toNat : Int) + 0 ≤
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat := by
      rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hLm
    obtain ⟨hR', -⟩ := Spike.Lib.X64.Rt.mainE_ok (rS := rS0 (Ly)) (tcb := pinA (Ly).lab + 0#64 + 8#64)
      (top := stacksA (Ly).lab + 0#64 + 16384#64) hL hL8 hok hfit hout (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    have hb0 : ((((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) =
        (stacksA (Ly).lab + 0#64 + 16384#64).toNat + (-8 - 0)) :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    intro s c hA
    obtain ⟨hM, hS⟩ := rtM_sfacts_setupEntry (ar := arOf (Ly).Λ) (lbl := lbl0) hI
      (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h) hpro hph hl hlc
      (by rw [hZ]; omega) (by rw [hZ]; omega) hR' (by omega) (by show 8 - L ≤ _; omega)
      (by show (0 : Int) ≤ 8; decide) (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide)
      hsub (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
      (fun _ h => Spike.Lib.X64.Rt.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by decide) h.1.2 h.2) hC0 s c hA
    obtain ⟨-, -, -, -, _, -, -, hJ⟩ := hA
    exact rtM_w2 hp hS hM (hJ.1.1 ▸ hQ0)
  · rintro s c ⟨-, -, -, -, _, -, hD, -⟩
    exact (hv hD.1.1.1).elim

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWS MainSW SetupArgs swFSL mainSIn oU rS0 entryR rtF setupMC
  rtCodeOkS) in
open Spike.Lib.AllocReach (IN) in
/-- **The consumer's `h0` at a placed output, an entry state and a setup
block** (`h0_ofPlaceOK` at `setupMC sw`): `scc_rt_main`'s code and phase
facts at the `sw < 6` of A11 (`hc`, `hph`), its frame's facts decided, its
own obligations inside `W2At` (`hW`) from `mainSW_sfacts` (inside
`SFacts`, the source control's facts `CFacts` at the entry `hC0`, back from
the setup block and the user function under `hPostS`, `hPost`),
`MainSW.ofCtl` (the control's `MainCtl`: `hf0`, `hov`, `hpl0` at the entry,
`hPostS`, `hPost` back), `mainSW_rtM` (inside `RtM`; `hgrow`, `hset`,
`hfn`) and `rtM_w2`; the setup call's node (`hWC`) from `hWC_ofPlaceOK`
(the setup function's prologue `hproS`, its head's phase facts `hphS`, its
labels off the write abort `hlS`, `hlcS`, its room holding the head's push
`hD8`); left: the setup call's target and frame pop (`hcall`, `hPS`). -/
theorem h0_ofPlaceOK_setup {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (takeMem pm (rS0 (Ly)) m))
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0) (hC0 : CFacts (Ly).Λ lbl0 c0)
    (hpl0 : ∀ s, PlacedS (Ly).Λ (fun _ => none) s c0 [])
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hPostS : ∀ c rs, PostS c rs → CFacts (Ly).Λ lbl0 c ∧ MainCtl (Ly).Λ (fun _ => none) c)
    (hPost : ∀ c v, Post c v → CFacts (Ly).Λ lbl0 c ∧ MainCtl (Ly).Λ (fun _ => none) c)
    (hL1 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU2.toBitVec).toNat)
    (hS : ∀ v, SetupCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).sp0).toBitVec c0
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.X64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hD8 : 8 ≤ D1) {chk entry : Label} {Zs lim : Int64} {Lg : Label} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)}
    (hproS : Spike.Lib.X64.Flow.prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg zl zf z1 z2 zs ps = true)
    (hphS : blkPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab (setupMC sw).setup + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true)
    (hlS : (setupMC sw).setup ∉ Spike.Lib.X64.AllocG.abLabs) (hlcS : chk ∉ Spike.Lib.X64.AllocG.abLabs)
    (hU : ∀ v, MainCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2
      (SetupArgs PostS (setupMC sw).sw (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F' ⟨(Ly).lab (setupMC sw).sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU (setupMC sw).Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ (MSAt h i p rd J ab ls0 []).abortAt s → MainExitS p (MSAt h i p rd J ab ls0 []) s c v.toNat) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.X64.At (Ly).exe (Ly).endPc (entryR E) FE (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  have hin := Spike.Lib.X64.Rt.mainSIn_of_okS hc
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hL0 : (0 : Int) ≤ L := by omega
  have h8 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm
  have hfit : (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64 := by
    rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
  have hout : ((limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (Ly).lab + 0#64 + 16384#64).toNat + -L ∨
      ((stacksA (Ly).lab + 0#64 + 16384#64).toNat : Int) + 0 ≤ (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat := by
    rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hLm
  have hmr : Scc.Sem.Kernel.mapped (K0 (Ly).Λ) false ⟨limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
    rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]; exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  refine h0_ofPlaceOK h i hE hFE hFEs hFEk hp hf0 hov hC0 hpl0 hL hLm hL8 hin
    (by rw [hZ]; omega) (show sw ≤ 5 by omega) (by show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega)
    (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, hk]; refine ⟨?_, ?_, ?_⟩ <;> omega)
    hD10 hD18 hD20 hD28 hL1 hL2 hZM hZS hZU hS hcall hPS
    (hWC_ofPlaceOK h i hp hL hLm hL8 hsw hD8 hL1 hproS hphS hlS hlcS hC0 ⟨hf0, hov, hpl0⟩) hU hexit fun v => ?_
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    obtain ⟨hR', -⟩ := Spike.Lib.X64.Rt.mainE_ok (rS := rS0 (Ly)) (tcb := pinA (Ly).lab + 0#64 + 8#64)
      (top := stacksA (Ly).lab + 0#64 + 16384#64) hL hL8 hok hfit hout (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    have hb0 : ((((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) =
        (stacksA (Ly).lab + 0#64 + 16384#64).toNat + (-8 - 0)) :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have hS1 := mainSW_sfacts (ms := MSAt h i p rd J ab ls0 []) (lbl := lbl0) hI hsw hin (Post := Post)
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) hC0 (fun c rs hc => (hPostS c rs hc).1)
      (fun c v hc => (hPost c v hc).1) hph hR' (by omega) (by show 8 - L ≤ _; omega)
      (by show (0 : Int) ≤ 8; decide) (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide) hmr
      (fun _ h => h.1.1.2) hsub (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
      (fun _ h => Spike.Lib.X64.Rt.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by decide) h.1.2 h.2)
    exact MainSW.imp (MainSW.ofCtl hS1 (Q := MainCtl (Ly).Λ (fun _ => none)) ⟨hf0, hov, hpl0⟩
        (fun c rs hc => (hPostS c rs hc).2) (fun c v hc => (hPost c v hc).2))
      (mainSW_rtM hI (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
        hsw hin hph hgrow hset hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide))
      fun s c h1 h2 => rtM_w2 hp h1.1 h2 h1.2
  · exact MainSW.ofFalse fun m hm => hv hm.1.1.1

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.rtX_w2G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtX_w2G

/-- info: 'Spike.Lib.LowerX64.startEW_w2G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_w2G

/-- info: 'Spike.Lib.LowerX64.h0_of_startS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_of_startS

/-- info: 'Spike.Lib.LowerX64.MainSW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MainSW.imp

/-- info: 'Spike.Lib.LowerX64.h0_of_startS_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_of_startS_setup

/-- info: 'Spike.Lib.LowerX64.rows_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rows_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.limOk_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms limOk_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.h0_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.rtM_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_w2

/-- info: 'Spike.Lib.LowerX64.MainSW.ofCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MainSW.ofCtl

/-- info: 'Spike.Lib.LowerX64.h0_ofPlaceOK_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK_setup

/-- info: 'Spike.Lib.LowerX64.hWC_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWC_ofPlaceOK

end Spike.Lib.LowerX64
