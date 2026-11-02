/-
**The refusal path's obligations at hello's level 2, from pieces** (x86-64; the twin of
`Spike/Lib/A64HelloRefPre.lean`, the hello twin of wake's `X64WakeRefStub.refObl_of`): `RefH.RefOblH` from the
refusal path's test node and three blocks and the threads abort path's `StubTW` below main's frame
(`R.callee (-136 - 8) (-24) 16`), the latter `TPathW.stub` of one `TPathW` inside the level under its outside
move, the pointwise map (`MapH`) of five component paths joined by `TPathW.and`:

- `ACH`: `SFactsAC` at `own2bH`'s phase (`ACWH`: the frames `[]`, the write tail `DtW`, no write abort, the
  `clone` phase `ClH`, the threads abort `Hello.ThreadsAb.AcH`), under the take's move `PhRec.K`;
- `AgH`: `ownGH` agrees with `own2bH` (`AgWH`);
- `AbStH`: the write abort's phase kept (`AbSt`);
- `NoWrH`: no write to the arena or the counter (`NoWrC`);
- `AbWH`: the states in `scc_rt_abort`'s code with the return address (`WakePh.AbW`);

with the exit call at an abort site of the memory side (`ExH`) and the test and three blocks (`BlkH`).

- `PreH`: the pieces' premises on the region, the source and the slots (the slice's words, the placement of the
  box's label and of main's thread id read off the placement `lbl`, so no layout fact is carried).
- `TOblH`: a path obligation for every caller's state of the call `fES`.
- `BlkH`, `ACH`, `AgH`, `AbStH`, `NoWrH`, `AbWH`, `MapH`, `ExH`: the pieces.
- `mapWKH`: a path obligation under a pointwise change (`TPathW.mapWK`).
- `callee144`: the callee's region of a region of `PreH`'s shape.
- `raT_x27H`: the refusal's return address is `.Lwc_main.x27`.
- `refOblH_of`: `RefOblH` from the pieces, given `RefPreH ⊆ PreH` (`hpre`) and the kernel (`hK`).

No absolute address appears in a statement here.

## Differences from the AArch64 version

- `BlkH` is the refusal path's test node `.ts` (a `NodeW`) and its blocks `.je`, `.x26`, `.fl` (AArch64: the
  blocks `.cb`, `.cl`, `.fl`).
- The callee's region is `R.callee (-136 - 8) (-24) 16`, the frame condition at the call's offset
  `⟨-136, [(.rbp, 0)]⟩`, the return address `raT lab ".Lwc_main"` (AArch64: `R.callee (-144) (-48) 0` at `oP`,
  `raT lab pfxM`); `callee144` has no alignment conclusion.
- `PreH`'s region facts are `BoxPureH`'s x86-64 ones: `R.lo ≤ -384`, `16 ≤ R.hi`, the base `96` below stack
  0's top (AArch64: `-400`, `0`, `80`).
- The refusal's return address is `.Lwc_main.x27` (`raT_x27H`, the label of the `ud2` after `.spawnfail5`'s
  `call`; AArch64: `.L22_wc_main.sp15`).
-/
import Spike.Lib.X64HelloRefH
import Spike.Lib.X64WakeRefTP
import Spike.Lib.X64WakeWcK1
import Spike.Lib.X64HelloOwnGAbT
import Spike.Lib.X64HelloTake2
import Spike.Lib.X64HelloWfPh
import Spike.Lib.X64HelloClH
import Spike.Lib.X64WriteAb
import Spike.Lib.X64WakeWfN
import Spike.Lib.X64HelloThreadsAb

namespace Spike.Lib.X64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region FragS Frag MemSide)
open Spike.Lib.X64 (At AS BlkW NodeW DFrame CKept Abs FStable)
open Spike.Lib.X64.Flow.Worker.Hello.SpawnFail (fNS fES flB)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (jeB x26B)
open Spike.Lib.X64.ThreadsAb (raT)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH SlRep)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsAC)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.WakeWf (DtW NoWrC)
open Spike.Lib.X64.HelloPh.RefH (RefPreH RefOblH)
open Scc.Sem.X64 (codeLabel)
open Scc.Cert.Rt.X64 (codeT_eq)

/-- **A path obligation under a pointwise change** of the predicate and the outside move
(`TPathW.mapWK`). -/
theorem mapWKH {W W' : Frag isa} {K K' : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (h : TPathW W K exe endPc R F c0 ra) (hf : ∀ s c, W s c → (∀ s', ¬ K s s') → W' s c ∧ ∀ s', ¬ K' s s') :
    TPathW W' K' exe endPc R F c0 ra :=
  TPathW.mapWK h hf

/-- **The callee's region at `-144`** of a region with room below main's frame is `OK`, with offsets
`[-24, 16]`. -/
theorem callee144 {R : Region} (hR : R.OK) (hlo : R.lo ≤ -168) (hhi : 16 ≤ R.hi) :
    (R.callee (-136 - 8) (-24) 16).OK ∧ (R.callee (-136 - 8) (-24) 16).lo ≤ -24 ∧
      16 ≤ (R.callee (-136 - 8) (-24) 16).hi := by
  have hkc : (-136 - 8 : Int) < R.hi := by omega
  exact ⟨Region.callee_ok hR (by omega) (by decide) hkc (by omega), by simp [Region.callee],
    by simp [Region.callee]⟩

/-- **The return address of the refusal's call is `.x27`'s**: `raT` is `.spawnfail5 + 12`, the label of the
`ud2` after the call. -/
theorem raT_x27H {L : RuntimeLayout}
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x) :
    raT L.lab ".Lwc_main" = (L.lab ".Lwc_main.x27").toBitVec := by
  have h5 : L.lab (".Lwc_main" ++ ".spawnfail5") = Int64.ofNat 4203897 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have h27 : L.lab ".Lwc_main.x27" = Int64.ofNat 4203909 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  unfold raT
  rw [h5, h27]
  decide

section Pieces

variable (L : RuntimeLayout) (lbl : Lbl) (l : WeakMem.AllocLabel) (ws : List TermRun.Word)

set_option hygiene false in
/-- The callee's frame condition at the call of `scc_rt_abort` (`RefOblH`'s). -/
local notation "FC" => fun (R : Region) (m0 m1 : MachineData) (σC : AS) (m : MachineData) =>
  DFrame R m0 m ∧ CKept R (-136 - 8) (-24) 16 m1 m ∧ Abs R ⟨-136, [(.rbp, 0)]⟩ m1 σC

/-- **The pieces' premises** on the region `R`, the source control `cP` and main's slots `sl` (the slice), `cA`
(the box) and `me` (main's thread id): the source at `SpawnSrcH l ws`, the slice's words `ws` represented by `sl`
(`SlRep`), the box's label and main's thread id placed at the slots' words, `R` `OK`, 16-aligned, with room for
main's frame and the abort path below it, its base `96` below stack 0's top. -/
def PreH (R : Region) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (cA me : BitVec 64) : Prop :=
  SpawnSrcH l ws cP ∧ SlRep lbl ws sl.1.toNat sl.2.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat ∧
    lbl l = some cA.toNat ∧ lbl (Spike.Lib.X64WakeSrcDefs.mainTidLbl 2) = some me.toNat ∧ R.OK ∧
    R.base.toNat % 16 = 0 ∧ R.lo ≤ -384 ∧ 16 ≤ R.hi ∧ R.base.toNat + 96 = L.stacksA.toNat + 16384

/-- **A threads abort path obligation** inside `W` (at the callee's region) under `K`, below main's frame, for
every caller's state and control of the call `fES` (`RefOblH`'s last conjunct's shape). -/
def TOblH (W : Region → Frag isa) (K : State → State → Prop) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (cA me : BitVec 64) (m1 : MachineData) (σC : AS) (c0 : Ctl),
    PreH L lbl l ws R cP sl cA me → (fES L.lab cP sl cA me).J σC c0 →
    TPathW (W (R.callee (-136 - 8) (-24) 16)) K L.exe L.endPc (R.callee (-136 - 8) (-24) 16) (FC R m0 m1 σC) c0
      (raT L.lab ".Lwc_main")

/-- **The refusal path's test and three blocks** inside `Wn` under `K` (`RefOblH`'s first four conjuncts). -/
def BlkH (Wn : Frag isa) (K : State → State → Prop) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (cA me : BitVec 64), PreH L lbl l ws R cP sl cA me →
    NodeW Wn K L.exe L.endPc R (DFrame R m0) (fNS L.lab cP sl cA me .ts) ∧
      BlkW Wn K L.exe L.endPc R (DFrame R m0) (fNS L.lab cP sl cA me .je) jeB ∧
      BlkW Wn K L.exe L.endPc R (DFrame R m0) (fNS L.lab cP sl cA me .x26) x26B ∧
      BlkW Wn K L.exe L.endPc R (DFrame R m0) (fNS L.lab cP sl cA me .fl) flB

/-- The take's range of the path's `SFactsAC`: empty, at the pool's base. -/
def rSH : Range := ⟨L.Λ.stackPool.lo, 0⟩

/-- The words the path's states own: `own2bH` at the state's phase. -/
def ownWH (s : State) : List (Loc × Val) :=
  Spike.Lib.X64.HelloPh.own2bH L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) (Spike.Lib.X64.HelloPh.ph2bH (pcOf s))

/-- **The path's state facts** at `own2bH`'s phase, the frames `[]`, the arena `ar` and sizes `lsize`. -/
def ACWH (ar : Spike.Lib.Arena) (lsize : Lsize) : Frag isa := fun s c =>
  SFactsAC L.Λ (Spike.Lib.X64.PhRec.μ L) helloSrc (fun _ => True) (fun _ _ => True) (fun s _ => ownWH L s)
    (rSH L) (fun s => Spike.Lib.X64.HelloPh.ph2bH (pcOf s) / 8 % 2 = 0) ar (fun _ _ _ _ _ => False) lbl lsize s c []
    DtW (fun _ => False) (Spike.Lib.X64.HelloPh.ClH L) (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab ".Lwc_main")

/-- **`SFactsAC` along the path** under the take's move. -/
def ACH (ar : Spike.Lib.Arena) (lsize : Lsize) : Prop :=
  TOblH L lbl l ws (fun _ => ACWH L lbl ar lsize) (Spike.Lib.X64.PhRec.K L (rSH L))

/-- **`ownGH` agrees with `own2bH`** along the path. -/
def AgH : Prop :=
  TOblH L lbl l ws (fun _ => Spike.Lib.X64.HelloPh.AgWH L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) (ownWH L)
    (Spike.Lib.X64.PhRec.μ L)) (fun _ _ => False)

/-- **The write abort's phase kept** along the path. -/
def AbStH : Prop :=
  TOblH L lbl l ws (fun _ s _ => Spike.Lib.X64ConsumerA.AbSt (Spike.Lib.X64.PhRec.μ L)
    (Spike.Lib.X64.WriteAb.Ab L.lab) s) (fun _ _ => False)

/-- **No write to the arena or the counter** along the path (the frames `[]`, the context `Ctx`). -/
def NoWrH (ar : Spike.Lib.Arena) (lsize : Lsize) (Ctx : FragS isa) : Prop :=
  TOblH L lbl l ws (fun _ => NoWrC ar helloSrc lbl lsize Ctx []) (fun _ _ => False)

/-- **The states in `scc_rt_abort`'s code** with the return address, along the path. -/
def AbWH : Prop :=
  TOblH L lbl l ws (fun R' => Spike.Lib.X64.WakePh.AbW L R' (raT L.lab ".Lwc_main") (Spike.Lib.X64.PhRec.μ L))
    (fun _ _ => False)

/-- **The components give `Wn` and no `K` move** at a state. -/
def MapH (ar : Spike.Lib.Arena) (lsize : Lsize) (Ctx : FragS isa) (Wn : Frag isa)
    (K : State → State → Prop) : Prop :=
  ∀ (R' : Region) (s : State) (c : Ctl), ACWH L lbl ar lsize s c →
    Spike.Lib.X64.HelloPh.AgWH L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) (ownWH L) (Spike.Lib.X64.PhRec.μ L) s c →
    Spike.Lib.X64ConsumerA.AbSt (Spike.Lib.X64.PhRec.μ L) (Spike.Lib.X64.WriteAb.Ab L.lab) s →
    NoWrC ar helloSrc lbl lsize Ctx [] s c →
    Spike.Lib.X64.WakePh.AbW L R' (raT L.lab ".Lwc_main") (Spike.Lib.X64.PhRec.μ L) s c →
    Wn s c ∧ ∀ s', ¬ K s s'

/-- **The exit call is an abort site of the memory side `ms`.** -/
def ExH (ms : MemSide isa) : Prop :=
  ∀ s : State, s.st.2 = L.lab Spike.Lib.X64.Abort.threads.exit → ms.abortAt s

end Pieces

section Of

variable {L : RuntimeLayout} {F0 : MachineData → Prop}
  {G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop}
  {l : WeakMem.AllocLabel} {b : Nat}
  {ws : List TermRun.Word} {n : Nat} {Ws : FragS isa} {K : State → State → Prop}
  {lbl : Lbl} {ms : List TermRun.Frame → MemSide isa} {ar : Spike.Lib.Arena} {lsize : Lsize}
  {Ctx : FragS isa}

/-- **`RefOblH` from its pieces**: the test and three blocks (`hblk`); the threads abort path's `StubTW` from
the five component paths joined and mapped into the level at no frames under `K` (`hmap`), the exit an abort
site (`hex`), in the callee's region at `-144` under `fstable_enter`'s frame condition; `RefPreH`'s facts give
`PreH`'s (`hpre`), the kernel at no frames is `abi` (`hK`), the layout's program is hello's cells (`hp`). -/
theorem refOblH_of (hp : L.prog = SccCode.helloCells) (hK : (ms []).K = some abi)
    (hpre : ∀ R cP sl cA me, RefPreH L F0 G l b ws n R cP sl cA me → PreH L lbl l ws R cP sl cA me)
    (hblk : BlkH L lbl l ws (fun s c => Ws s c []) K) (hac : ACH L lbl l ws ar lsize) (hag : AgH L lbl l ws)
    (habs : AbStH L lbl l ws) (hnw : NoWrH L lbl l ws ar lsize Ctx) (habw : AbWH L lbl l ws)
    (hmap : MapH L lbl ar lsize Ctx (fun s c => Ws s c []) K) (hex : ExH L (ms [])) :
    RefOblH L F0 G l b ws n Ws K lbl ms := by
  haveI := L.valid
  intro R m0 cP sl cA me hR0
  have hpre' := hpre R cP sl cA me hR0
  obtain ⟨-, -, -, -, hR, -, hlo, hhi, -⟩ := id hpre'
  obtain ⟨hts, hje, hx26, hfl⟩ := hblk R m0 cP sl cA me hpre'
  refine ⟨hts, hje, hx26, hfl, fun m1 σC c0 hE => ?_⟩
  have h1 := TPathW.and (hac R m0 cP sl cA me m1 σC c0 hpre' hE) (hag R m0 cP sl cA me m1 σC c0 hpre' hE)
    fun s c h₁ h₂ => And.intro h₁ h₂
  have h2 := TPathW.and h1 (habs R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := TPathW.and h2 (hnw R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := TPathW.and h3 (habw R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h5 := mapWKH (W' := fun s c => Ws s c []) (K' := K) h4
    fun s c h _ => hmap _ s c h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2
  have hlays : Scc.Cert.Rt.X64.Lays L.exe SccCode.helloCells L.pfx := hp ▸ L.lays
  have hend : L.endPc = Scc.Cert.Rt.X64.endOf L.exe SccCode.helloCells L.pfx := by
    show Scc.Cert.Rt.X64.endOf L.exe L.prog L.pfx = _; rw [hp]
  exact TPathW.stub h5 hlays hend SccCode.hello_abort hK
    (Spike.Lib.X64.fstable_enter hR (Spike.Lib.X64.FStable.dframe R m0) (by omega) (by decide) (by omega)
      (by omega) (by decide) (by decide) (by decide))
    fun s _ ⟨_, _, _, hpc, _⟩ => hex s hpc

end Of

end Spike.Lib.X64.HelloPh.RefO

/-- info: 'Spike.Lib.X64.HelloPh.RefO.mapWKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.mapWKH

/-- info: 'Spike.Lib.X64.HelloPh.RefO.callee144' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.callee144

/-- info: 'Spike.Lib.X64.HelloPh.RefO.raT_x27H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.raT_x27H

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refOblH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refOblH_of
