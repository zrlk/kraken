/-
**The refusal path's obligations inside `h1`'s fragment** (x86-64, wake.w;
the twin of `Spike/Lib/A64WakeRefStub.lean`): `WakeRefSeg.RefObl` from its
pieces. The threads abort path's `StubTW` below main's frame is
`TPathW.stub` of one `TPathW` inside `W1X` under `K1W`, itself the
pointwise map (`RefMap`) of six component paths joined by `TPathW.and`:

- `RefAC`: the state's facts `SFactsAC` at `own2b`'s phase (the frames `[]`,
  the write tail `DtW`, no write abort, `ClW`, the threads abort `AcW`), under
  the take's move `PhRec.K`;
- `RefAg`: `ownG` agrees with `own2b` (`AgW`);
- `RefAbSt`: the write abort's phase kept (`AbSt`);
- `RefNoWr`: no write to the arena or the counter (`NoWrC`);
- `RefAbW`: the states in `scc_rt_abort`'s code with the return address
  (`AbW`);
- `RefLft`: `SFactsSt2` at `ownG` lifting to `ownGXW` (`Lft2`);

with the exit call at an abort site of `ms1W` (`RefEx`) and the refusal
path's test and three blocks (`RefBlk`).

- `Pre`: `RefObl`'s premises on the region, the source and the slots.
- `TObl`: a path obligation for every caller's state of the call `fE`.
- `RefBlk`, `RefAC`, `RefAg`, `RefAbSt`, `RefNoWr`, `RefAbW`, `RefLft`,
  `RefMap`, `RefEx`: the pieces.
- `refObl_of`: `RefObl` from the pieces.

**Unlike AArch64**: `RefBlk` is the refusal path's test node `ts` and its
blocks `je`, `x22`, `fl` (A64's blocks `cb`, `cl`, `fl`); the dispatcher's
region is `R.callee (-72 - 8) (-24) 16` with the frame condition at
`⟨-72, [(.rbp, 0)]⟩` (A64's `R.callee (-80) (-48) 0` at `oP`), the return
address `raT lab ".Lwc_main"`; `Pre` is `RefObl`'s x86-64 shape (no
alignment, `R.lo ≤ -320`, `16 ≤ R.hi`, base `64` below stack 0's top); the
fragment is `WakeBoxW.W1X … []`; wake's cells laid out in the executable
are a premise `hl` (as `WakeRefSeg.seg_refB`'s); `TPathW.mapWK` is in
`X64WakeRefTP`; the assembly is a parameter `asm`; `W1X`'s state facts own
`ownGXW` (main's and the worker's control words), so a sixth path `RefLft`
(`Lft2`, no A64 counterpart) lifts `SFactsSt2` from `ownG` to it.
-/
import Spike.Lib.X64WakeRefSeg
import Spike.Lib.X64WakeRefTP
import Spike.Lib.X64WakeTake2
import Spike.Lib.X64WriteAb
import Spike.Lib.X64WakeWfN
import Spike.Lib.X64WakeOwnLft2

namespace Spike.Lib.X64.WakeRefStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region FragS MemSide PlaceWX)
open Spike.Lib.X64 (At AS BlkW NodeW DFrame CKept Abs FStable)
open Spike.Lib.X64.WakePh.SpawnFail (fN fE flB)
open Spike.Lib.X64.WakePh.Parent (jeB x22B)
open Spike.Lib.X64.ThreadsAb (raT)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64.WakeH1Inv (K1W ms1W endR)
open Spike.Lib.X64.WakeBoxW (SpawnSrc W1X)
open Spike.Lib.X64.WakeRefSeg (RefObl)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsAC)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.WakeWf (DtW NoWrC)
open SccCode (wakeCells)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- The layout's labels. -/
local notation "lbW" => (_root_.Executable.labels (RuntimeLayout.ofPlaceWX hp i).exe).label

/-- **`RefObl`'s premises** on the region `R`, the source control `cP` and
main's slots `cA`, `mT`. -/
def Pre (l : WeakMem.AllocLabel) (b : Nat) (R : Region) (cP : Ctl) (cA mT : BitVec 64) : Prop :=
  SpawnSrc l cP ∧ cA.toNat = b ∧ mT.toNat = Spike.Lib.X64WakeLoadT.tcb0 (Ly).Λ ∧ R.OK ∧
    R.lo ≤ -320 ∧ 16 ≤ R.hi ∧ R.base.toNat + 64 = (Ly).stacksA.toNat + 16384

/-- **A threads abort path obligation** inside `W` (at the callee's region)
under `K`, below main's frame, for every caller's state and control of the
call `fE` (`RefObl`'s last conjunct's shape). -/
def TObl (l : WeakMem.AllocLabel) (b : Nat) (W : Region → Frag isa) (K : State → State → Prop) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (cA mT : BitVec 64) (m1 : MachineData) (σC : AS) (c0 : Ctl),
    Pre hp i l b R cP cA mT → (fE lbW cP cA mT).J σC c0 →
    TPathW (W (R.callee (-72 - 8) (-24) 16)) K (Ly).exe (endR hp i) (R.callee (-72 - 8) (-24) 16)
      (fun m => DFrame R m0 m ∧ CKept R (-72 - 8) (-24) 16 m1 m ∧ Abs R ⟨-72, [(.rbp, 0)]⟩ m1 σC) c0
      (raT lbW ".Lwc_main")

/-- **The refusal path's test and three blocks** inside `W1X` (`RefObl`'s
first four conjuncts). -/
def RefBlk (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (cA mT : BitVec 64), Pre hp i l b R cP cA mT →
    NodeW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN lbW cP cA mT .ts) ∧
      BlkW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN lbW cP cA mT .je) jeB ∧
      BlkW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN lbW cP cA mT .x22) x22B ∧
      BlkW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN lbW cP cA mT .fl) flB

/-- The take's range of the path's `SFactsAC`: empty, at the pool's base. -/
def rSW : Range := ⟨(Ly).Λ.stackPool.lo, 0⟩

/-- The words the path's states own: `own2b` at the state's phase. -/
def ownW (s : State) : List (Loc × Val) :=
  Spike.Lib.X64.WakePh.own2b (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)
    (Spike.Lib.X64.WakePh.ph2b (pcOf s))

/-- **The path's state facts** at `own2b`'s phase, the frames `[]`. -/
def ACW (l : WeakMem.AllocLabel) (b n : Nat) : Frag isa := fun s c =>
  SFactsAC (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) wakeSrc (fun _ => True) (fun _ _ => True)
    (fun s _ => ownW hp i s) (rSW hp i) (fun s => Spike.Lib.X64.WakePh.ph2b (pcOf s) / 8 % 2 = 0)
    (Spike.Lib.X64.WakeOD.arW hp i) (fun _ _ _ _ _ => False)
    (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
    (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) s c [] DtW (fun _ => False)
    (Spike.Lib.X64.WakeOD.ClW hp i) (Spike.Lib.X64.WakeOD.AcW hp i)

/-- **No write to the arena or the counter** (the frames `[]`, no context). -/
def NoWrW (l : WeakMem.AllocLabel) (b n : Nat) : Frag isa :=
  NoWrC (Spike.Lib.X64.WakeOD.arW hp i) wakeSrc (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
    (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) (fun _ _ _ => False) []

/-- **`SFactsAC` along the path** under the take's move. -/
def RefAC (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  TObl hp i l b (fun _ => ACW hp i ls0 l b n) (Spike.Lib.X64.PhRec.K (Ly) (rSW hp i))

/-- **`ownG` agrees with `own2b`** along the path. -/
def RefAg (l : WeakMem.AllocLabel) (b : Nat) : Prop :=
  TObl hp i l b (fun _ => Spike.Lib.X64.WakePh.AgW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) (ownW hp i)
    (Spike.Lib.X64.PhRec.μ (Ly))) (fun _ _ => False)

/-- **The write abort's phase kept** along the path. -/
def RefAbSt (l : WeakMem.AllocLabel) (b : Nat) : Prop :=
  TObl hp i l b (fun _ s _ => Spike.Lib.X64ConsumerA.AbSt (Spike.Lib.X64.PhRec.μ (Ly))
    (Spike.Lib.X64.WriteAb.Ab (Ly).lab) s) (fun _ _ => False)

/-- **No write to the arena or the counter** along the path. -/
def RefNoWr (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  TObl hp i l b (fun _ => NoWrW hp i ls0 l b n) (fun _ _ => False)

/-- **The states in `scc_rt_abort`'s code** with the return address, along the
path. -/
def RefAbW (l : WeakMem.AllocLabel) (b : Nat) : Prop :=
  TObl hp i l b (fun R' => Spike.Lib.X64.WakePh.AbW (Ly) R' (raT lbW ".Lwc_main") (Spike.Lib.X64.PhRec.μ (Ly)))
    (fun _ _ => False)

/-- **`SFactsSt2` at `ownG` lifts to `ownGXW`** along the path (`W1W`'s
state facts own main's and the worker's control words too). -/
def RefLft (l : WeakMem.AllocLabel) (b : Nat) : Prop :=
  TObl hp i l b (fun _ => Spike.Lib.X64.WakePh.Lft2 (Ly).Λ (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) DtW)
    (fun _ _ => False)

/-- **The components give `W1X` and no `K1W` move** at a state. -/
def RefMap (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  ∀ (R' : Region) (s : State) (c : Ctl), ACW hp i ls0 l b n s c →
    Spike.Lib.X64.WakePh.AgW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) (ownW hp i)
      (Spike.Lib.X64.PhRec.μ (Ly)) s c →
    Spike.Lib.X64ConsumerA.AbSt (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.WriteAb.Ab (Ly).lab) s →
    NoWrW hp i ls0 l b n s c →
    Spike.Lib.X64.WakePh.AbW (Ly) R' (raT lbW ".Lwc_main") (Spike.Lib.X64.PhRec.μ (Ly)) s c →
    Spike.Lib.X64.WakePh.Lft2 (Ly).Λ (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) DtW s c →
    W1X asm hp i E Dt Ctx ls0 l b n s c [] ∧ ∀ s', ¬ K1W hp i E s s'

/-- **The exit call is an abort site of `ms1W`.** -/
def RefEx (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  ∀ s : State, s.st.2 = lbW Spike.Lib.X64.Abort.threads.exit → (ms1W asm hp i E cT ls0 l b n []).abortAt s

/-- **`RefObl` from its pieces**: the test and three blocks (`hblk`); the
threads abort path's `StubTW` from the six component paths joined and
mapped into `W1X` under `K1W` (`hmap`), the exit an abort site (`hex`), in
the callee's region at `-80` under `fstable_enter`'s frame condition, wake's
cells laid out in the executable (`hl`). -/
theorem refObl_of (hl : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx) {l : WeakMem.AllocLabel} {b n : Nat}
    (hblk : RefBlk asm hp i E Dt Ctx ls0 l b n) (hac : RefAC hp i ls0 l b n) (hag : RefAg hp i l b)
    (habs : RefAbSt hp i l b) (hnw : RefNoWr hp i ls0 l b n) (habw : RefAbW hp i l b) (hlft : RefLft hp i l b)
    (hmap : RefMap asm hp i E Dt Ctx ls0 l b n) (hex : RefEx asm hp i E cT ls0 l b n) :
    RefObl asm hp i E cT Dt Ctx ls0 l b n := by
  haveI := (Ly).valid
  intro R m0 cP cA mT hsrc hcA hmT hR hlo hhi hst
  have hpre : Pre hp i l b R cP cA mT := ⟨hsrc, hcA, hmT, hR, hlo, hhi, hst⟩
  obtain ⟨hts, hje, hx22, hfl⟩ := hblk R m0 cP cA mT hpre
  refine ⟨hts, hje, hx22, hfl, fun m1 σC c0 hE => ?_⟩
  have h1 := TPathW.and (hac R m0 cP cA mT m1 σC c0 hpre hE) (hag R m0 cP cA mT m1 σC c0 hpre hE)
    fun s c h₁ h₂ => And.intro h₁ h₂
  have h2 := TPathW.and h1 (habs R m0 cP cA mT m1 σC c0 hpre hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := TPathW.and h2 (hnw R m0 cP cA mT m1 σC c0 hpre hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := TPathW.and h3 (habw R m0 cP cA mT m1 σC c0 hpre hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h5 := TPathW.and h4 (hlft R m0 cP cA mT m1 σC c0 hpre hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h6 := TPathW.mapWK (W' := fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (K' := K1W hp i E) h5
    fun s c h _ => hmap _ s c h.1.1.1.1.1 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2
  exact TPathW.stub h6 hl rfl SccCode.wake_abort rfl
    (Spike.Lib.X64.fstable_enter hR (Spike.Lib.X64.FStable.dframe R m0) (by omega) (by decide) (by omega)
      (by omega) (by decide) (by decide) (by decide))
    fun s _ ⟨_, _, _, hpc, _⟩ => hex s hpc

end Inst

end Spike.Lib.X64.WakeRefStub

/-- info: 'Spike.Lib.X64.WakeRefStub.refObl_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refObl_of
