/-
**The refusal path's obligations at hello's level 2, from pieces** (AArch64; piece R1;
the hello twin of wake's `WakeRefStub` interface and `refObl_of`): `RefH.RefOblH` from the refusal
path's three blocks and the threads abort path's `StubTW` below main's frame (`R.callee (-144) (-48) 0`), the latter
`TPathW.stub` of one `TPathW` inside the level under its outside move, the pointwise map (`MapH`) of five
component paths joined by `TPathW.and`:

- `ACH`: `SFactsAC` at `own2bH`'s phase (`ACWH`: the frames `[]`, the write tail `DtW`, no write abort, the
  `clone` phase `ClH`, the threads abort `HelloWf.AcH`), under the take's move `PhRec.K`;
- `AgH`: `ownGH` agrees with `own2bH` (`AgWH`);
- `AbStH`: the write abort's phase kept (`AbSt`);
- `NoWrH`: no write to the arena or the counter (`NoWrC`);
- `AbWH`: the states in `scc_rt_abort`'s code with the return address (`WakePh.AbW`);

with the exit call at an abort site of the memory side (`ExH`) and the three blocks (`BlkH`).

- `PreH`: the pieces' premises on the region, the source and the slots (the slice's words, the placement of the
  box's label and of main's thread id read off the placement `lbl`, so no layout fact is carried).
- `TOblH`: a path obligation for every caller's state of the call `fES`.
- `BlkH`, `ACH`, `AgH`, `AbStH`, `NoWrH`, `AbWH`, `MapH`, `ExH`: the pieces.
- `mapWKH`: a path obligation under a pointwise change (wake's `WakeRefStub.TPathW.mapWK`).
- `callee144`: the callee's region of a region of `PreH`'s shape.
- `raT_sp15H`: the refusal's return address is `.L22_wc_main.sp15`.
- `refOblH_of`: `RefOblH` from the pieces, given `RefPreH ⊆ PreH` (`hpre`) and the kernel (`hK`).

No absolute address appears in a statement here.
-/
import Spike.Lib.A64HelloRefH
import Spike.Lib.A64WakeRefTP
import Spike.Lib.A64WakeWcK1
import Spike.Lib.A64HelloOwnGAbT
import Spike.Lib.A64HelloTake2
import Spike.Lib.A64HelloWfPh
import Spike.Lib.A64HelloClH

namespace Spike.Lib.A64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region FragS Frag MemSide)
open Spike.Lib.A64.Flow (BlkW)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (oP cl)
open Spike.Lib.A64.Flow.Worker.Hello.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.SpawnFail (fNS fES flB)
open Spike.Lib.A64.ThreadsAb (raT)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH SlRep)
open Spike.Lib.WakeRefTP (TPathW)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (SFactsAC)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (DtW NoWrC)
open Spike.Lib.A64.HelloPh.RefH (RefPreH RefOblH)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Cert.Link.A64 (codeOf)

/-- **A path obligation under a pointwise change** of the predicate and the outside move (wake's
`WakeRefStub.TPathW.mapWK`). -/
theorem mapWKH {W W' : Frag isaLSE2} {K K' : State → State → Prop} {exe : _root_.Executable}
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

/-- **The callee's region at `-144`** of a region with room below main's frame is `OK`, 16-aligned, with offsets
`[-48, 0]`. -/
theorem callee144 {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) :
    (R.callee (-144) (-48) 0).OK ∧ (R.callee (-144) (-48) 0).base.toNat % 16 = 0 ∧
      (R.callee (-144) (-48) 0).lo ≤ -48 ∧ 0 ≤ (R.callee (-144) (-48) 0).hi := by
  have hkc : (-144 : Int) < R.hi := by omega
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -144 + -48 by omega) (by decide) hkc
  refine ⟨Region.callee_ok hR (by omega) (by decide) hkc (by omega), ?_, by simp [Region.callee],
    by simp [Region.callee]⟩
  have : (((R.callee (-144) (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **The return address of the refusal's call is `.sp15`'s**: `raT` is `.1_spawnfail5 + 8`, the instruction
after the call. -/
theorem raT_sp15H {L : RuntimeLayout}
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    raT L.lab pfxM = (L.lab ".L22_wc_main.sp15").toBitVec := by
  have h5 : L.lab (pfxM ++ ".1_spawnfail5") = Int64.ofNat 2169872 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have h15 : L.lab ".L22_wc_main.sp15" = Int64.ofNat 2169880 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  unfold raT
  rw [h5, h15]
  decide

section Pieces

variable (L : RuntimeLayout) (lbl : Lbl) (l : WeakMem.AllocLabel) (ws : List TermRun.Word)

set_option hygiene false in
/-- The callee's frame condition at the call of `scc_rt_abort` (`RefOblH`'s). -/
local notation "FC" => fun (R : Region) (m0 m1 : MachineData) (σC : Spike.Lib.A64.Flow.AS) (m : MachineData) =>
  Spike.Lib.A64.Flow.DFrame R m0 m ∧ Spike.Lib.A64.Flow.CKept R (-144) (-48) 0 m1 m ∧ Spike.Lib.A64.Flow.Abs R oP m1 σC

/-- **The pieces' premises** on the region `R`, the source control `cP` and main's slots `sl` (the slice), `cA`
(the box) and `me` (main's thread id): the source at `SpawnSrcH l ws`, the slice's words `ws` represented by `sl`
(`SlRep`), the box's label and main's thread id placed at the slots' words, `R` `OK`, 16-aligned, with room for
main's frame and the abort path below it, its base `80` below stack 0's top. -/
def PreH (R : Region) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (cA me : BitVec 64) : Prop :=
  SpawnSrcH l ws cP ∧ SlRep lbl ws sl.1.toNat sl.2.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat ∧
    lbl l = some cA.toNat ∧ lbl (Spike.Lib.WakeT1.mainTidLbl 2) = some me.toNat ∧ R.OK ∧
    R.base.toNat % 16 = 0 ∧ R.lo ≤ -400 ∧ 0 ≤ R.hi ∧ R.base.toNat + 80 = L.stacksA.toNat + 16384

/-- **A threads abort path obligation** inside `W` (at the callee's region) under `K`, below main's frame, for
every caller's state and control of the call `fES` (`RefOblH`'s last conjunct's shape). -/
def TOblH (W : Region → Frag isaLSE2) (K : State → State → Prop) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (cA me : BitVec 64) (m1 : MachineData) (σC : Spike.Lib.A64.Flow.AS) (c0 : Ctl),
    PreH L lbl l ws R cP sl cA me → (fES pfxM L.lab cP sl cA me).J σC c0 →
    TPathW (W (R.callee (-144) (-48) 0)) K L.exe L.endPc (R.callee (-144) (-48) 0) (FC R m0 m1 σC) c0
      (raT L.lab pfxM)

/-- **The refusal path's three blocks** inside `Wn` under `K` (`RefOblH`'s first three conjuncts). -/
def BlkH (Wn : Frag isaLSE2) (K : State → State → Prop) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (cA me : BitVec 64), PreH L lbl l ws R cP sl cA me →
    BlkW Wn K L.exe L.endPc R (Spike.Lib.A64.Flow.DFrame R m0) (fNS pfxM L.lab cP sl cA me .cb) (cb pfxM) ∧
      BlkW Wn K L.exe L.endPc R (Spike.Lib.A64.Flow.DFrame R m0) (fNS pfxM L.lab cP sl cA me .cl) (cl pfxM) ∧
      BlkW Wn K L.exe L.endPc R (Spike.Lib.A64.Flow.DFrame R m0) (fNS pfxM L.lab cP sl cA me .fl) flB

/-- The take's range of the path's `SFactsAC`: empty, at the pool's base. -/
def rSH : Range := ⟨L.Λ.stackPool.lo, 0⟩

/-- The words the path's states own: `own2bH` at the state's phase. -/
def ownWH (s : State) : List (Loc × Val) :=
  Spike.Lib.A64.HelloPh.own2bH L (Spike.Lib.A64.Rt.Reserve.ntA L.lab) (Spike.Lib.A64.HelloPh.ph2bH (pcOf s))

/-- **The path's state facts** at `own2bH`'s phase, the frames `[]`, the arena `ar` and sizes `lsize`. -/
def ACWH (ar : Spike.Lib.Arena) (lsize : Lsize) : Frag isaLSE2 := fun s c =>
  SFactsAC L.Λ (Spike.Lib.A64.PhRec.μ L) helloSrc (fun _ => True) (fun _ _ => True) (fun s _ => ownWH L s)
    (rSH L) (fun s => Spike.Lib.A64.HelloPh.ph2bH (pcOf s) / 8 % 2 = 0) ar (fun _ _ _ _ _ => False) lbl lsize s c []
    DtW (fun _ => False) (Spike.Lib.A64.HelloPh.ClH L) (Spike.Lib.A64.HelloWf.AcH L.lab pfxM)

/-- **`SFactsAC` along the path** under the take's move. -/
def ACH (ar : Spike.Lib.Arena) (lsize : Lsize) : Prop :=
  TOblH L lbl l ws (fun _ => ACWH L lbl ar lsize) (Spike.Lib.A64.PhRec.K L (rSH L))

/-- **`ownGH` agrees with `own2bH`** along the path. -/
def AgH : Prop :=
  TOblH L lbl l ws (fun _ => Spike.Lib.A64.HelloPh.AgWH L (Spike.Lib.A64.Rt.Reserve.ntA L.lab) (ownWH L)
    (Spike.Lib.A64.PhRec.μ L)) (fun _ _ => False)

/-- **The write abort's phase kept** along the path. -/
def AbStH : Prop :=
  TOblH L lbl l ws (fun _ s _ => Spike.Lib.A64ConsumerA.AbSt (Spike.Lib.A64.PhRec.μ L)
    (Spike.Lib.A64.WriteAb.Ab L.lab) s) (fun _ _ => False)

/-- **No write to the arena or the counter** along the path (the frames `[]`, the context `Ctx`). -/
def NoWrH (ar : Spike.Lib.Arena) (lsize : Lsize) (Ctx : FragS isaLSE2) : Prop :=
  TOblH L lbl l ws (fun _ => NoWrC ar helloSrc lbl lsize Ctx []) (fun _ _ => False)

/-- **The states in `scc_rt_abort`'s code** with the return address, along the path. -/
def AbWH : Prop :=
  TOblH L lbl l ws (fun R' => Spike.Lib.A64.WakePh.AbW L R' (raT L.lab pfxM) (Spike.Lib.A64.PhRec.μ L))
    (fun _ _ => False)

/-- **The components give `Wn` and no `K` move** at a state. -/
def MapH (ar : Spike.Lib.Arena) (lsize : Lsize) (Ctx : FragS isaLSE2) (Wn : Frag isaLSE2)
    (K : State → State → Prop) : Prop :=
  ∀ (R' : Region) (s : State) (c : Ctl), ACWH L lbl ar lsize s c →
    Spike.Lib.A64.HelloPh.AgWH L (Spike.Lib.A64.Rt.Reserve.ntA L.lab) (ownWH L) (Spike.Lib.A64.PhRec.μ L) s c →
    Spike.Lib.A64ConsumerA.AbSt (Spike.Lib.A64.PhRec.μ L) (Spike.Lib.A64.WriteAb.Ab L.lab) s →
    NoWrC ar helloSrc lbl lsize Ctx [] s c →
    Spike.Lib.A64.WakePh.AbW L R' (raT L.lab pfxM) (Spike.Lib.A64.PhRec.μ L) s c →
    Wn s c ∧ ∀ s', ¬ K s s'

/-- **The exit call is an abort site of the memory side `ms`.** -/
def ExH (ms : MemSide isaLSE2) : Prop :=
  ∀ s : State, s.st.2 = L.lab Spike.Lib.A64.Abort.threads.exit → ms.abortAt s

end Pieces

section Of

variable {L : RuntimeLayout} {F0 : MachineData → Prop}
  {G : Region → (MachineData → Prop) → (Spike.Lib.A64.Flow.AS → Ctl → Prop) → UInt64 → Prop}
  {l : WeakMem.AllocLabel} {b : Nat}
  {ws : List TermRun.Word} {n : Nat} {Ws : FragS isaLSE2} {K : State → State → Prop}
  {lbl : Lbl} {ms : List TermRun.Frame → MemSide isaLSE2} {ar : Spike.Lib.Arena} {lsize : Lsize}
  {Ctx : FragS isaLSE2}

/-- **`RefOblH` from its pieces** (wake's `refObl_of`): the three blocks (`hblk`); the threads abort path's
`StubTW` from the five component paths joined and mapped into the level at no frames under `K` (`hmap`), the exit
an abort site (`hex`), in the callee's region at `-144` under `fstable_enter`'s frame condition; `RefPreH`'s facts
give `PreH`'s (`hpre`), the kernel at no frames is `abi` (`hK`), the layout's program is hello's (`hp`). -/
theorem refOblH_of (hp : L.prog = SccCode.helloProg) (hK : (ms []).K = some abi)
    (hpre : ∀ R cP sl cA me, RefPreH L F0 G l b ws n R cP sl cA me → PreH L lbl l ws R cP sl cA me)
    (hblk : BlkH L lbl l ws (fun s c => Ws s c []) K) (hac : ACH L lbl l ws ar lsize) (hag : AgH L lbl l ws)
    (habs : AbStH L lbl l ws) (hnw : NoWrH L lbl l ws ar lsize Ctx) (habw : AbWH L lbl l ws)
    (hmap : MapH L lbl ar lsize Ctx (fun s c => Ws s c []) K) (hex : ExH L (ms [])) :
    RefOblH L F0 G l b ws n Ws K lbl ms := by
  intro R m0 cP sl cA me hR0
  have hpre' := hpre R cP sl cA me hR0
  obtain ⟨-, -, -, -, hR, -, hlo, hhi, -⟩ := id hpre'
  obtain ⟨hcb, hcl, hfl⟩ := hblk R m0 cP sl cA me hpre'
  refine ⟨hcb, hcl, hfl, fun m1 σC c0 hE => ?_⟩
  have hkc : (-144 : Int) < R.hi := by omega
  have h1 := TPathW.and (hac R m0 cP sl cA me m1 σC c0 hpre' hE) (hag R m0 cP sl cA me m1 σC c0 hpre' hE)
    fun s c h₁ h₂ => And.intro h₁ h₂
  have h2 := TPathW.and h1 (habs R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := TPathW.and h2 (hnw R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := TPathW.and h3 (habw R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h5 := mapWKH (W' := fun s c => Ws s c []) (K' := K) h4
    fun s c h _ => hmap _ s c h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2
  have hlays : Scc.Cert.Rt.A64.Lays L.exe SccCode.helloProg L.pfx := hp ▸ L.lays
  have hend : L.endPc = Scc.Cert.Rt.A64.endOf L.exe SccCode.helloProg L.pfx := by
    show Scc.Cert.Rt.A64.endOf L.exe L.prog L.pfx = _; rw [hp]
  exact TPathW.stub h5 hlays hend SccCode.hello_abort hK
    (Spike.Lib.A64.Flow.fstable_enter hR (Spike.Lib.A64.Flow.FStable.dframe R m0) (by omega) (by decide) hkc
      (by decide) (by decide) (by decide) (by decide))
    fun s _ ⟨_, _, _, hpc, _⟩ => hex s hpc

end Of

end Spike.Lib.A64.HelloPh.RefO

/-- info: 'Spike.Lib.A64.HelloPh.RefO.mapWKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.mapWKH

/-- info: 'Spike.Lib.A64.HelloPh.RefO.callee144' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.callee144

/-- info: 'Spike.Lib.A64.HelloPh.RefO.raT_sp15H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.raT_sp15H

/-- info: 'Spike.Lib.A64.HelloPh.RefO.refOblH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.refOblH_of
