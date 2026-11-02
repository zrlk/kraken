/-
**hello.w on x86-64: main back from a refused `clone` at level 2** (the twin of
`Spike/Lib/A64HelloRefH.lean`): the refusal half of the level-2 box, its premises `hret` (a refusal's return
lands in `Ref`) and `hseg` (`Ref` never leaves), the twins of wake's `X64WakeRefuse` at hello's `wc_main`
(frame 128, `CloneMidH`'s `wcNSH`).

- `refuse_atH`: main at `wcNSH` (the clone's `syscall`), once the kernel returns a refusal `r`, is at the
  refusal path's first node `SpawnFail.fNS … .ts` (hello's; `MSS sl cA me` from `FrWH`'s slots `-8`, `-24`,
  `-32`, `-48` and `-40`) in the frame condition its memory outside the region (wake's `refuse_at`).
- `RefH`: the refusal's returns from `CloneMidH`.
- `RefPreH`: `CloneMidH`'s facts of the region, the source control and the slots' words that the obligations
  use.
- `RefOblH`: the refusal path's obligations inside a level `Ws` at no frames: the four nodes and the threads
  abort path's `StubTW` below main's frame, for every region and source control of `RefPreH`'s.
- `hret_H`: the box's `hret` at `Ref := RefH` (no source step).
- `seg_refH`: the box's `hseg` at `Ref := RefH` from `RefOblH` (`SpawnFail.seg_spawnFailWS_hello`,
  `R.lo ≤ -168` from `BoxPureH`).

No absolute address appears in this file.

## Differences from the AArch64 version

- The refusal path's nodes are `X64HelloSpawnFailS.fNS`'s four (`.ts`, a `NodeW`; `.je`, `.x26`, `.fl`
  blocks; AArch64: three blocks `.cb`, `.cl`, `.fl`); the threads abort path's region is
  `R.callee (-136 - 8) (-24) 16` at the call's offset `⟨-136, [(.rbp, 0)]⟩` (AArch64:
  `R.callee (-144) (-48) 0` at `oP`).
- The returned registers are `retRegs64`'s (`syscallStep`, as `X64WakeRefuse.refuse_at`).
- `seg_refH` lifts the one-frame segment with `SegWS.liftS` and drops the empty exit (no `liftS_noret` on
  this side, as `X64AbortHeapS`).
-/
import Spike.Lib.X64HelloHMid
import Spike.Lib.X64HelloSpawnFailS
import Spike.Lib.X64HelloChildAt
import Spike.Lib.X64WakeRefuse
import Spike.Lib.X64AbortHeapS
import Spike.Lib.X64HelloSrc

namespace Spike.Lib.X64.HelloPh.RefH

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (Lays endOf codeAt_blockAt_lays)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh.WcClone (svcB)
open Spike.Lib.X64.Flow.Worker.Hello.Child (hello_svcIn)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (oP jeB x26B)
open Spike.Lib.X64.Flow.Worker.Hello.SpawnFail (fNS fES flB seg_spawnFailWS_hello)
open Spike.Lib.X64.WakePh.SpawnFail (ret_eq)
open Spike.Lib.X64.ThreadsAb (CloneRef raT)
open Spike.Lib.X64HelloPreA (cloneAtH)
open Spike.Lib.X64HelloHMid (BoxPureH CloneMidH)
open Spike.Lib.X64.Flow.HelloWc (FrMGH)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64.HelloPh.WcSp6 (wcNSH)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {s : State} {c c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} {r : BitVec 64}

/-- **Main back from a refused clone is at `fNS .ts`** (wake's `refuse_at`): main at the clone's `syscall`
(`hcode`) at `wcNSH` in region `R` gives, once the kernel returns the refusal `r`, a state in `At` of hello's
`fNS … .ts` at the same control, for the frame condition its memory outside the region; `MSS sl cA me` from
`FrWH`'s slots. -/
theorem refuse_atH
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (cloneAtH exe) svcB)
    (hat : At exe endPc R F (wcNSH (_root_.Executable.labels exe).label c0 t k sl me cA fr) s c)
    (hr : CloneRef r) :
    At exe endPc R (DFrame R (abi.ret s r).st.1)
      (fNS (_root_.Executable.labels exe).label c sl cA me .ts)
      (abi.ret s r) c := by
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := hat
  change s.st.2 = cloneAtH exe at hpc
  have hcell : CellAt s (op64 .syscall) 2 := (hcode s he hn).cell0 rfl rfl hpc
  have hnext := nextPc_of_cellAt hcell
  rw [ret_eq]
  refine ⟨he, hn, hd, ?_, ⟨syscallStep (nextPc s) r σ, ⟨?_, hA.zmms, hA.status, ?_, hA.slot⟩,
    DFrame.refl _ _, ?_⟩⟩
  · show nextPc s = _
    rw [hnext, hpc]
    show (_root_.Executable.labels exe).label Spike.Lib.X64.HelloPh.WcSp6.x25L + 94 + Int64.ofNat 2 =
      (_root_.Executable.labels exe).label Spike.Lib.X64.HelloPh.WcSp6.x25L + 96
    rw [Int64.add_assoc]; rfl
  · show retRegs64 s r = syscallRegs (nextPc s) (rflags σ.status) r σ.regs
    simp only [retRegs64, syscallRegs, hA.regs, hA.status]
  · exact syscallSO_rel hA.so (nextPc s) (rflags σ.status) r
  · obtain ⟨⟨⟨-, -, -, -, h8, -, h24, h32, h40, h48, -, -⟩, -⟩, -⟩ := hJ
    have hX : (UInt64.ofNat r.toNat).toBitVec = r := by show BitVec.ofNat 64 r.toNat = r; simp
    refine ⟨rfl, ?_, h8, h24, h32, h48, h40⟩
    show CloneRef (UInt64.ofNat r.toNat).toBitVec
    rw [hX]; exact hr

section Seg

variable (L : RuntimeLayout) (F0 : MachineData → Prop)
  (G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop) (W : FragS isa)
  (Wc : Frag isa) (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (n : Nat)

/-- **The refusal's returns**: no frames, `abi.ret s0 r` of a state `s0` of `CloneMidH` at the same control for
a refusal `r`. -/
def RefH : FragS isa := fun s c fs =>
  fs = [] ∧ ∃ s0 r, s = abi.ret s0 r ∧ CloneRef r ∧ CloneMidH L F0 G W Wc l b ws n s0 c []

/-- **`CloneMidH`'s facts that the refusal path uses**: in region `R`, `BoxPureH` and `G` at some ghosts, the
caller's saves `FrMGH` with the slice `sl` and `me`, the source control `cP` at `SpawnSrcH l ws` (`CloneMidH`'s
slice words `ws`), the box word `cA` at `b`. -/
def RefPreH (R : Region) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (cA me : BitVec 64) :
    Prop :=
  (∃ (F : MachineData → Prop) (J1 : AS → Ctl → Prop) (t : UInt64) (fr : BitVec 64 × BitVec 64),
      BoxPureH L F0 n R F J1 t ∧ G R F J1 t ∧ FrMGH J1 fr sl me ∧ SpawnSrcH l ws cP) ∧ cA.toNat = b

variable (Ws : FragS isa) (K : State → State → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
  (ms : List TermRun.Frame → MemSide isa)

/-- **The refusal path's obligations inside `Ws` at no frames**, for every region `R`, frame condition
`DFrame R m0`, source control `cP` and slot words `sl`, `cA`, `me` of `RefPreH`'s: the refusal path's four
nodes (`SpawnFail.fNS`) and the threads abort path's obligations below main's frame (`StubTW` in
`R.callee (-136 - 8) (-24) 16` at the return address `raT … ".Lwc_main"`) for every caller's state and control
of the call (`SpawnFail.fES`). -/
def RefOblH : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (cA me : BitVec 64), RefPreH L F0 G l b ws n R cP sl cA me →
    NodeW (fun s c => Ws s c []) K L.exe L.endPc R (DFrame R m0) (fNS L.lab cP sl cA me .ts) ∧
      BlkW (fun s c => Ws s c []) K L.exe L.endPc R (DFrame R m0) (fNS L.lab cP sl cA me .je) jeB ∧
      BlkW (fun s c => Ws s c []) K L.exe L.endPc R (DFrame R m0) (fNS L.lab cP sl cA me .x26) x26B ∧
      BlkW (fun s c => Ws s c []) K L.exe L.endPc R (DFrame R m0) (fNS L.lab cP sl cA me .fl) flB ∧
      ∀ m1 σC c0, (fES L.lab cP sl cA me).J σC c0 →
        Abort.Disp.StubTW (fun s c => Ws s c []) K helloSrc lbl (ms []) L.exe L.endPc
          (R.callee (-136 - 8) (-24) 16)
          (fun m => DFrame R m0 m ∧ CKept R (-136 - 8) (-24) 16 m1 m ∧ Abs R ⟨-136, [(.rbp, 0)]⟩ m1 σC) c0
          (raT L.lab ".Lwc_main")

variable {L F0 G W Wc l b ws n}

/-- **The box's `hret` at `RefH`**: a refusal's return from `CloneMidH` is in `RefH` at the same control and
no frames, by no source step. -/
theorem hret_H {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : CloneMidH L F0 G W Wc l b ws n s c fs)
    (r : BitVec 64) (hr : r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) :
    ∃ c' fs', FrameRun helloSrc (c, fs) (c', fs') ∧ RefH L F0 G W Wc l b ws n (abi.ret s r) c' fs' := by
  obtain rfl := h.1
  exact ⟨c, [], .refl _, rfl, s, r, rfl, hr, h⟩

variable {Ws K lbl ms}

/-- **Main back from a refused clone does not return** (the box's `hseg` at `RefH`): from `RefH`, a segment
inside `Ws` into nothing, given hello's cells as the layout's program (`hp`), the kernel at no frames (`hK`)
and the path's obligations (`hobl`). -/
theorem seg_refH (hp : L.prog = SccCode.helloCells) (hK : (ms []).K = some abi)
    (hobl : RefOblH L F0 G l b ws n Ws K lbl ms) :
    SegWS Ws K helloSrc lbl ms (RefH L F0 G W Wc l b ws n) (fun _ _ _ => False) := by
  have hpS : Lays L.exe SccCode.helloCells L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe SccCode.helloCells L.pfx := by
    show endOf L.exe L.prog L.pfx = _; rw [hp]
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s (cloneAtH L.exe) svcB :=
    fun s he hn => codeAt_blockAt_lays hpS he (hn.trans hendS) hello_svcIn
  let P : Region × MachineData × Ctl × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) × BitVec 64 × BitVec 64 →
      FragS isa := fun g s c fs =>
    RefPreH L F0 G l b ws n g.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 ∧
      (At L.exe L.endPc g.1 (DFrame g.1 g.2.1)
        (fNS L.lab g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 .ts)).at [] s c fs
  refine (SegWS.exists_pre (P := P) fun g => ?_).mono_pre ?_
  · by_cases hg : RefPreH L F0 G l b ws n g.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2
    · obtain ⟨hts, hje, hx26, hfl, hstub⟩ := hobl g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 hg
      obtain ⟨⟨F, J1, t, fr, ⟨hR, -, -, hlo, hhi, -⟩, -⟩, -⟩ := hg
      have h := seg_spawnFailWS_hello hpS hendS (Q := fun _ _ => False)
        (FStable.dframe g.1 g.2.1) hR (by omega) hhi hK hts hje hx26 hfl hstub
      exact ((SegWS.liftS [] h fun _ _ h => h).mono_post fun _ _ _ h => h.1.elim).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hg h.1
  · rintro s c fs ⟨rfl, s0, r, rfl, hr, -, -, -, R, F, J1, t, sl, me, cA, fr, hB, hG, hFr, hcA, hsrc, hA, -, -⟩
    refine ⟨(R, (abi.ret s0 r).st.1, c, sl, cA, me), ⟨⟨F, J1, t, fr, hB, hG, hFr, hsrc⟩, hcA⟩, ?_, rfl⟩
    exact refuse_atH hcode hA hr

end Seg

end Spike.Lib.X64.HelloPh.RefH

/-- info: 'Spike.Lib.X64.HelloPh.RefH.refuse_atH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefH.refuse_atH

/-- info: 'Spike.Lib.X64.HelloPh.RefH.hret_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefH.hret_H

/-- info: 'Spike.Lib.X64.HelloPh.RefH.seg_refH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefH.seg_refH
