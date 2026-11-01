/-
**The level-1 counter rows at `CtxR1H`** (AArch64; the level-1 twin of
`Spike/Lib/A64HelloLandR.lean`'s `hctr0_RH`/`hnew0_RH`): the counter row and the box store's premises at every
state of the level-1 context `CtxR1H l b n`, and from them the level's per-state facts (`HelloO.OPremH.hW1`'s
`SFactsACH`, by `WakeWf.hW0` at the level's labels).

After rodata's allocation of `l` at `b` (`n` cells), the level's labels are `upd LB l b` and sizes `updN (ls0T ls)
l n`. `CtxR1H`'s two disjuncts are `wc_main`'s box counter add (`GcMH`, at no frames, under main's thread pointer)
and the box's store (`StAt … GsH1`). The add's row is `CtrF.ctrRow_ofFT`; the store's premises are
`CtrF.newStM_ofSt`. The store writes no counter (`WakeCtr.stAt_noWr`: the counter word lies below the heap,
`HrdArena.hlt_U`), and the add does (`CtrF.ctrAtF_wr`).

What is carried is where the level continues after each write:
- the allocator's next node `n4` after the box counter add, in the level's fragment (`HLandM1`, `LandR.HLandM`'s
  twin);
- the store's landings, for labels fresh at the level (now `LandR1U.HLand2U`, with `U r1Of`).

- `HLandM1`: the carried tail of the box counter add (used by `LandR1U.hLandM1U_of`).

CLEANUP-boxM removed the off-chain `HLand2`, `hctr1_RH`, `hnew1_RH`, `hW1_RH`, `hW1_RHμ` and `hland2_of`; their
on-chain twins are `LandR1U`'s `HLand2U`, `hctr1_RU`, `hnew1_RU`, `hW1_RU`, `hW1_RUμ` and `hland2_ofU`.
-/
import Spike.Lib.A64HelloLand1
import Spike.Lib.A64HelloLandR
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.LandR

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (CtrRow PendA WrAt ArenaW SFactsACH)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib (FragS Frag MemSide FrameRun)
open Spike.Lib.A64.Flow (At)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Alloc (Call N)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.HelloPh.Land (CtrOkS GcMH ref1H GsH1 CtxR1H)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize) (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
local notation "TI" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw TI

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The level's labels. -/
local notation "L1" => Spike.Lib.A64ConsumerA.upd (LB) l b

set_option hygiene false in
/-- The level's sizes. -/
local notation "S1" => Spike.Lib.A64ConsumerA.updN (ls0T ls) l n

set_option hygiene false in
/-- The allocator's labels. -/
local notation "LBL" => (_root_.Executable.labels (Ly).exe).label

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
local notation "μE" => (Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
/-- The level's memory sides at a fragment `J`, the frames `fs`. -/
local notation "MS1" => fun (J : InvS) (fs : List TermRun.Frame) => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ (μE) rd
    (Spike.Lib.HelloGOf2H.gWH hpw TI (Spike.Lib.WakeHG.cTW hpw TI))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AR) J (L1) (S1) fs

/-! ## The carried landings -/

/-- **`wc_main`'s box counter add's tail at level 1** (`CtrF.ctrRow_ofFT`'s `hland` at `GcMH`, `ref1H`): from the
allocator's next node `n4` after a counter add of `wc_main`'s box call, under main's thread pointer, `Q` at the
add's frames. -/
def HLandM1 (Q : FragS isaLSE2) : Prop :=
  ∀ fs (ms0 : MemSide isaLSE2) R F q, ms0 = { ref1H (asm := asm) hpw i0 E rd ls l b n fs with xa := ms0.xa } →
    GcMH hpw i0 fs ms0 R F q → CtrOkS ms0 LBL R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (N LBL ms0 q .n4) s c → TP (TV) s → Q s c fs

end Spike.Lib.A64.HelloPh.LandR
