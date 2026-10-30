/-
**The refusal path's obligations inside `h1`'s fragment** (AArch64, wake.w):
`WakeRefSeg.RefObl` from its pieces. The threads abort path's `StubTW`
below main's frame is `TPathW.stub` of one `TPathW` inside `W1X` under
`K1W`, itself the pointwise map (`RefMap`) of five component paths joined by
`TPathW.and`:

- `RefAC`: the state's facts `SFactsAC` at `own2b`'s phase (the frames `[]`,
  the write tail `DtW`, no write abort, `ClW`, the threads abort `AcW`), under
  the take's move `PhRec.K`;
- `RefAg`: `ownG` agrees with `own2b` (`AgW`);
- `RefAbSt`: the write abort's phase kept (`AbSt`);
- `RefNoWr`: no write to the arena or the counter (`NoWrC`);
- `RefAbW`: the states in `scc_rt_abort`'s code with the return address
  (`AbW`);

with the exit call at an abort site of `ms1W` (`RefEx`) and the refusal
path's three blocks (`RefBlk`).

- `Pre`: `RefObl`'s premises on the region, the source and the slots.
- `TObl`: a path obligation for every caller's state of the call `fE`.
- `RefBlk`, `RefAC`, `RefAg`, `RefAbSt`, `RefNoWr`, `RefAbW`, `RefMap`,
  `RefEx`: the pieces.
- `TPathW.mapWK`: a path obligation under a pointwise change.
- `refObl_of`: `RefObl` from the pieces.
-/
import Spike.Lib.A64WakeRefSeg
import Spike.Lib.A64WakeRefAb
import Spike.Lib.A64WakeRefPh
import Spike.Lib.A64WakeOwnGAbT
import Spike.Lib.A64WakeTake2
import Spike.Lib.A64WakeSrcCtl
import Spike.Lib.A64WakeWcK1
import Spike.Lib.A64WakeWfN

namespace Spike.Lib.WakeRefStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region FragS Frag MemSide)
open Spike.Lib.A64.Flow (At AS BlkW NodeW ND DFrame CKept Abs FStable)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (oP cl)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.SpawnFail (fN fE flB)
open Spike.Lib.A64.ThreadsAb (raT)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeH1Inv (K1W ms1W)
open Spike.Lib.WakeSpawnR (endR)
open Spike.Lib.WakeBoxW (SpawnSrc)
open Spike.Lib.WakeRefSeg (W1X RefObl)
open Spike.Lib.WakeRefTP (TPathW)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (SFactsAC)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.A64.WakeWf (DtW NoWrC)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-- **A path obligation under a pointwise change** of the predicate and the
outside move. -/
theorem TPathW.mapWK {W W' : Frag isaLSE2} {K K' : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (h : TPathW W K exe endPc R F c0 ra) (hf : ∀ s c, W s c → (∀ s', ¬ K s s') → W' s c ∧ ∀ s', ¬ K' s s') :
    TPathW W' K' exe endPc R F c0 ra :=
  ⟨Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.de, Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dt1,
    Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dj1, Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dt2,
    Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dj2, Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dt3,
    Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dj3, Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dt4,
    Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dj4, Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dt5,
    Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.dg5, Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.se,
    Spike.Lib.A64.Flow.WakeWc.nodeW_mapWK hf h.sn1, Spike.Lib.A64.Flow.WakeWc.nodeW_mapWK hf h.sn1b,
    Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.sn2, Spike.Lib.A64.Flow.WakeWc.nodeW_mapWK hf h.ssvc,
    Spike.Lib.A64.Flow.WakeWc.blkW_mapWK hf h.sn5, Spike.Lib.A64.Flow.WakeWc.nodeW_mapWK hf h.sex⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- The layout's labels. -/
local notation "lbW" => (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label

/-- **`RefObl`'s premises** on the region `R`, the source control `cP` and
main's slots `cA`, `mT`. -/
def Pre (l : WeakMem.AllocLabel) (b : Nat) (R : Region) (cP : Ctl) (cA mT : BitVec 64) : Prop :=
  SpawnSrc l cP ∧ cA.toNat = b ∧ mT.toNat = Spike.Lib.WakeLoadT.tcb0 (Ly).Λ ∧ R.OK ∧ R.base.toNat % 16 = 0 ∧
    R.lo ≤ -336 ∧ 0 ≤ R.hi ∧ R.base.toNat + 48 = (Ly).stacksA.toNat + 16384

/-- **A threads abort path obligation** inside `W` (at the callee's region)
under `K`, below main's frame, for every caller's state and control of the
call `fE` (`RefObl`'s last conjunct's shape). -/
def TObl (l : WeakMem.AllocLabel) (b : Nat) (W : Region → Frag isaLSE2) (K : State → State → Prop) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (cA mT : BitVec 64) (m1 : MachineData) (σC : AS) (c0 : Ctl),
    Pre hp i l b R cP cA mT → (fE pfxM lbW cP cA mT).J σC c0 →
    TPathW (W (R.callee (-80) (-48) 0)) K (Ly).exe (endR hp i) (R.callee (-80) (-48) 0)
      (fun m => DFrame R m0 m ∧ CKept R (-80) (-48) 0 m1 m ∧ Abs R oP m1 σC) c0 (raT lbW pfxM)

/-- **The refusal path's three blocks** inside `W1X` (`RefObl`'s first three
conjuncts). -/
def RefBlk (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (cA mT : BitVec 64), Pre hp i l b R cP cA mT →
    BlkW (W1X hp i E Dt Ctx ls0 l b n) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN pfxM lbW cP cA mT .cb) (cb pfxM) ∧
      BlkW (W1X hp i E Dt Ctx ls0 l b n) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN pfxM lbW cP cA mT .cl) (cl pfxM) ∧
      BlkW (W1X hp i E Dt Ctx ls0 l b n) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN pfxM lbW cP cA mT .fl) flB

/-- The take's range of the path's `SFactsAC`: empty, at the pool's base. -/
def rSW : Range := ⟨(Ly).Λ.stackPool.lo, 0⟩

/-- The words the path's states own: `own2b` at the state's phase. -/
def ownW (s : State) : List (Loc × Val) :=
  Spike.Lib.A64.WakePh.own2b (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
    (Spike.Lib.A64.WakePh.ph2b (pcOf s))

/-- **The path's state facts** at `own2b`'s phase, the frames `[]`. -/
def ACW (l : WeakMem.AllocLabel) (b n : Nat) : Frag isaLSE2 := fun s c =>
  SFactsAC (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) wakeSrc (fun _ => True) (fun _ _ => True)
    (fun s _ => ownW hp i s) (rSW hp i) (fun s => Spike.Lib.A64.WakePh.ph2b (pcOf s) / 8 % 2 = 0)
    (WakeOD.arW hp i) (fun _ _ _ _ _ => False)
    (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b)
    (Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls0) l n) s c [] DtW (fun _ => False)
    (WakeOD.ClW hp i) (WakeOD.AcW hp i)

/-- **No write to the arena or the counter** (the frames `[]`, no context). -/
def NoWrW (l : WeakMem.AllocLabel) (b n : Nat) : Frag isaLSE2 :=
  NoWrC (WakeOD.arW hp i) wakeSrc (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b)
    (Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls0) l n) (fun _ _ _ => False) []

/-- **`SFactsAC` along the path** under the take's move. -/
def RefAC (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  TObl hp i l b (fun _ => ACW hp i ls0 l b n) (Spike.Lib.A64.PhRec.K (Ly) (rSW hp i))

/-- **`ownG` agrees with `own2b`** along the path. -/
def RefAg (l : WeakMem.AllocLabel) (b : Nat) : Prop :=
  TObl hp i l b (fun _ => Spike.Lib.A64.WakePh.AgW (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (ownW hp i)
    (Spike.Lib.A64.PhRec.μ (Ly))) (fun _ _ => False)

/-- **The write abort's phase kept** along the path. -/
def RefAbSt (l : WeakMem.AllocLabel) (b : Nat) : Prop :=
  TObl hp i l b (fun _ s _ => Spike.Lib.A64ConsumerA.AbSt (Spike.Lib.A64.PhRec.μ (Ly))
    (Spike.Lib.A64.WriteAb.Ab (Ly).lab) s) (fun _ _ => False)

/-- **No write to the arena or the counter** along the path. -/
def RefNoWr (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  TObl hp i l b (fun _ => NoWrW hp i ls0 l b n) (fun _ _ => False)

/-- **The states in `scc_rt_abort`'s code** with the return address, along the
path. -/
def RefAbW (l : WeakMem.AllocLabel) (b : Nat) : Prop :=
  TObl hp i l b (fun R' => Spike.Lib.A64.WakePh.AbW (Ly) R' (raT lbW pfxM) (Spike.Lib.A64.PhRec.μ (Ly)))
    (fun _ _ => False)

/-- **The components give `W1X` and no `K1W` move** at a state. -/
def RefMap (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  ∀ (R' : Region) (s : State) (c : Ctl), ACW hp i ls0 l b n s c →
    Spike.Lib.A64.WakePh.AgW (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (ownW hp i)
      (Spike.Lib.A64.PhRec.μ (Ly)) s c →
    Spike.Lib.A64ConsumerA.AbSt (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.WriteAb.Ab (Ly).lab) s →
    NoWrW hp i ls0 l b n s c →
    Spike.Lib.A64.WakePh.AbW (Ly) R' (raT lbW pfxM) (Spike.Lib.A64.PhRec.μ (Ly)) s c →
    W1X hp i E Dt Ctx ls0 l b n s c ∧ ∀ s', ¬ K1W hp i E s s'

/-- **The exit call is an abort site of `ms1W`.** -/
def RefEx (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  ∀ s : State, s.st.2 = lbW Spike.Lib.A64.Abort.threads.exit → (ms1W hp i E cT ls0 l b n []).abortAt s

/-- **`RefObl` from its pieces**: the three blocks (`hblk`); the threads abort
path's `StubTW` from the five component paths joined and mapped into `W1X`
under `K1W` (`hmap`), the exit an abort site (`hex`), in the callee's region
at `-80` under `fstable_enter`'s frame condition. -/
theorem refObl_of (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) {l : WeakMem.AllocLabel} {b n : Nat}
    (hblk : RefBlk hp i E Dt Ctx ls0 l b n) (hac : RefAC hp i ls0 l b n) (hag : RefAg hp i l b)
    (habs : RefAbSt hp i l b) (hnw : RefNoWr hp i ls0 l b n) (habw : RefAbW hp i l b)
    (hmap : RefMap hp i E Dt Ctx ls0 l b n) (hex : RefEx hp i E cT ls0 l b n) :
    RefObl hp i E cT Dt Ctx ls0 l b n := by
  intro R m0 cP cA mT hsrc hcA hmT hR hal hlo hhi hst
  have hpre : Pre hp i l b R cP cA mT := ⟨hsrc, hcA, hmT, hR, hal, hlo, hhi, hst⟩
  obtain ⟨hcb, hcl, hfl⟩ := hblk R m0 cP cA mT hpre
  refine ⟨hcb, hcl, hfl, fun m1 σC c0 hE => ?_⟩
  have hkc : (-80 : Int) < R.hi := by omega
  have h1 := TPathW.and (hac R m0 cP cA mT m1 σC c0 hpre hE) (hag R m0 cP cA mT m1 σC c0 hpre hE)
    fun s c h₁ h₂ => And.intro h₁ h₂
  have h2 := TPathW.and h1 (habs R m0 cP cA mT m1 σC c0 hpre hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := TPathW.and h2 (hnw R m0 cP cA mT m1 σC c0 hpre hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := TPathW.and h3 (habw R m0 cP cA mT m1 σC c0 hpre hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h5 := TPathW.mapWK (W' := W1X hp i E Dt Ctx ls0 l b n) (K' := K1W hp i E) h4
    fun s c h _ => hmap _ s c h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2
  have hlays : Scc.Cert.Rt.A64.Lays (Ly).exe wakeProg (Ly).pfx := by
    rw [← Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp]; exact (Ly).lays
  exact TPathW.stub h5 hlays rfl Spike.Lib.A64.WakePh.abortIn_wakeR rfl
    (Spike.Lib.A64.Flow.fstable_enter hR (Spike.Lib.A64.Flow.FStable.dframe R m0) (by omega) (by decide) hkc
      (by decide) (by decide) (by decide) (by decide))
    fun s _ ⟨_, _, _, hpc, _⟩ => hex s hpc

end Inst

end Spike.Lib.WakeRefStub

/-- info: 'Spike.Lib.WakeRefStub.refObl_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefStub.refObl_of
