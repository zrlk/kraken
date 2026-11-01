/-
**hello.w on AArch64: main back from a refused `clone` at level 2**: the refusal half of
`HelloH2Box.h2Stmt_box`, its premises `hret` (a refusal's return lands in
`Ref`) and `hseg` (`Ref` never leaves), the twins of wake's `WakeRefuse` /
`WakeBoxW.RefB` / `WakeRefSeg.seg_refB` at hello's `wc_main` (frame 144,
`CloneMidH`'s `wcNSH`).

- `refuse_atH`: main at `wcNSH` (the clone's `svc`), once the kernel
  returns a refusal `r`, is at the refusal path's first node
  `SpawnFail.fNS pfxM … .cb` (hello's; `MSS sl cA me` from `FrWH`'s slots
  `-144`, `-128`, `-120`, `-104` and `-112`) in the frame condition its memory
  outside the region (wake's `refuse_at`).
- `RefH`: the refusal's returns from `CloneMidH` (wake's `RefB`).
- `RefPreH`: `CloneMidH`'s facts of the region, the source control and the
  slots' words that the obligations use.
- `RefOblH`: the refusal path's obligations inside a level `Ws` at no
  frames (wake's `RefObl`): the three blocks and the threads abort path's
  `StubTW` below main's frame, for every region and source control of
  `RefPreH`'s.
- `hret_H`: `h2Stmt_box`'s `hret` at `Ref := RefH` (no source step).
- `seg_refH`: `h2Stmt_box`'s `hseg` at `Ref := RefH` from `RefOblH` (wake's
  `seg_refB`; `SpawnFail.seg_spawnFailWS_hello`, `R.lo ≤ -400` from
  `BoxPureH`).

`RefOblH`'s instance at hello's `W2 ∧ X2H` waits on row B8-W2H. No absolute
address appears in this file.
-/
import Spike.Lib.A64HelloHMid
import Spike.Lib.A64HelloSpawnFailS
import Spike.Lib.A64HelloChildAt
import Spike.Lib.A64WakeRefuse
import Spike.Lib.A64AbortHeapS
import Spike.Lib.HelloSrc

namespace Spike.Lib.A64.HelloPh.RefH

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib (FragS SegWS FrameRun Region)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow.Worker.Wake.Child (svcB)
open Spike.Lib.A64.Flow.Worker.Hello.Child (cb pfxM hello_svcIn)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (oP cl)
open Spike.Lib.A64.Flow.Worker.Hello.SpawnFail (fNS fES flB seg_spawnFailWS_hello)
open Spike.Lib.A64.Flow.Worker.Wake.SpawnFail (ret_eq)
open Spike.Lib.A64.ThreadsAb (CloneRef raT)
open Spike.Lib.HelloPreA (cloneAtH)
open Spike.Lib.HelloHMid (BoxPureH CloneMidH)
open Spike.Lib.A64.Flow.HelloWc (FrMGH)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.HelloSrc (helloSrc)
open SccCode (helloProg)
open Spike.Lib.A64.HelloPh.WcSp6 (wcNSH)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {s : State} {c c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} {r : BitVec 64}

/-- **Main back from a refused clone is at `fNS .cb`** (wake's `refuse_at`):
main at the clone's `svc` (`hcode`) at `wcNSH` in region `R` gives, once the
kernel returns the refusal `r`, a state in `At` of hello's `fNS pfxM … .cb` at
the same control, for the frame condition its memory outside the region;
`MSS sl cA me` from `FrWH`'s slots. -/
theorem refuse_atH
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (cloneAtH pfxM exe) svcB)
    (hat : At exe endPc R F (wcNSH (_root_.Executable.labels exe).label c0 t k sl me cA fr) s c)
    (hr : CloneRef r) :
    At exe endPc R (Spike.Lib.A64.Flow.DFrame R (abi.ret s r).st.1)
      (fNS pfxM (_root_.Executable.labels exe).label c sl cA me .cb)
      (abi.ret s r) c := by
  obtain ⟨he, hn, hd, hpc, σ, hA, -, hJ⟩ := hat
  change s.st.2 = cloneAtH pfxM exe at hpc
  obtain ⟨d0, hd0⟩ : ∃ d, svcB[0]? = some d := ⟨_, rfl⟩
  have hcell : CellAt s d0 4 := by
    have := hcode s he hn 0 d0 hd0
    rw [ofNat4_zero, ← hpc] at this
    exact this
  have hnext := nextPc_of_cellAt hcell
  have hX0 : (UInt64.ofNat r.toNat).toBitVec = r := by
    show BitVec.ofNat 64 r.toNat = r
    simp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h144, -, h128, h120, h112, h104, -, -⟩ := hJ
  rw [ret_eq]
  refine ⟨he, hn, hd, ?_, ⟨{ σ with regs := { σ.regs with X0 := UInt64.ofNat r.toNat } }, ⟨?_, hA.status, ?_, ?_⟩,
    Spike.Lib.A64.Flow.DFrame.refl _ _, ?_⟩⟩
  · show nextPc s = _
    rw [hnext, hpc]; rfl
  · show { s.st.1.regs with X0 := UInt64.ofNat r.toNat } = { σ.regs with X0 := UInt64.ofNat r.toNat }
    rw [hA.regs]
  · intro rr k hk
    cases rr with
    | SP => exact hA.so .SP k hk
    | reg xr => simp [SO.get, fNS, oP, lk] at hk
  · exact hA.slot
  · exact ⟨rfl, by simp only [hX0]; exact hr, h144, h128, h120, h104, h112⟩

section Seg

variable (L : RuntimeLayout) (F0 : MachineData → Prop)
  (G : Region → (MachineData → Prop) → (Spike.Lib.A64.Flow.AS → Ctl → Prop) → UInt64 → Prop) (W : FragS isaLSE2)
  (Wc : Frag isaLSE2) (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (n : Nat)

/-- **The refusal's returns** (wake's `RefB`): no frames, `abi.ret s0 r` of
a state `s0` of `CloneMidH` at the same control for a refusal `r`. -/
def RefH : FragS isaLSE2 := fun s c fs =>
  fs = [] ∧ ∃ s0 r, s = abi.ret s0 r ∧ CloneRef r ∧ CloneMidH L F0 G W Wc l b ws n s0 c []

/-- **`CloneMidH`'s facts that the refusal path uses**: in region `R`,
`BoxPureH` and `G` at some ghosts, the caller's saves `FrMGH` with the slice
`sl` and `me`, the source control `cP` at `SpawnSrcH l ws` (`CloneMidH`'s slice
words `ws`), the box word `cA` at `b`. -/
def RefPreH (R : Region) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (cA me : BitVec 64) :
    Prop :=
  (∃ (F : MachineData → Prop) (J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop) (t : UInt64) (fr : BitVec 64 × BitVec 64),
      BoxPureH L F0 n R F J1 t ∧ G R F J1 t ∧ FrMGH J1 fr sl me ∧ SpawnSrcH l ws cP) ∧ cA.toNat = b

variable (Ws : FragS isaLSE2) (K : State → State → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
  (ms : List TermRun.Frame → MemSide isaLSE2)

/-- **The refusal path's obligations inside `Ws` at no frames** (wake's
`RefObl`), for every region `R`, frame condition `DFrame R m0`, source
control `cP` and slot words `sl`, `cA`, `me` of `RefPreH`'s: the refusal path's
three blocks (`SpawnFail.fNS`) and the threads abort path's obligations below
main's frame (`StubTW` in `R.callee (-144) (-48) 0` at the return address
`raT`) for every caller's state and control of the call (`SpawnFail.fES`). -/
def RefOblH : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (cA me : BitVec 64), RefPreH L F0 G l b ws n R cP sl cA me →
    BlkW (fun s c => Ws s c []) K L.exe L.endPc R (Spike.Lib.A64.Flow.DFrame R m0)
        (fNS pfxM L.lab cP sl cA me .cb) (cb pfxM) ∧
      BlkW (fun s c => Ws s c []) K L.exe L.endPc R (Spike.Lib.A64.Flow.DFrame R m0)
        (fNS pfxM L.lab cP sl cA me .cl) (cl pfxM) ∧
      BlkW (fun s c => Ws s c []) K L.exe L.endPc R (Spike.Lib.A64.Flow.DFrame R m0)
        (fNS pfxM L.lab cP sl cA me .fl) flB ∧
      ∀ m1 σC c0, (fES pfxM L.lab cP sl cA me).J σC c0 →
        Spike.Lib.A64.Abort.Disp.StubTW (fun s c => Ws s c []) K helloSrc lbl (ms []) L.exe L.endPc
          (R.callee (-144) (-48) 0)
          (fun m => Spike.Lib.A64.Flow.DFrame R m0 m ∧ Spike.Lib.A64.Flow.CKept R (-144) (-48) 0 m1 m ∧
            Spike.Lib.A64.Flow.Abs R oP m1 σC) c0
          (raT L.lab pfxM)

variable {L F0 G W Wc l b ws n}

/-- **`h2Stmt_box`'s `hret` at `RefH`**: a refusal's return from
`CloneMidH` is in `RefH` at the same control and no frames, by no source
step. -/
theorem hret_H {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : CloneMidH L F0 G W Wc l b ws n s c fs)
    (r : BitVec 64) (hr : r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) :
    ∃ c' fs', FrameRun helloSrc (c, fs) (c', fs') ∧ RefH L F0 G W Wc l b ws n (abi.ret s r) c' fs' := by
  obtain rfl := h.1
  exact ⟨c, [], .refl _, rfl, s, r, rfl, hr, h⟩

variable {Ws K lbl ms}

/-- **Main back from a refused clone does not return** (`h2Stmt_box`'s
`hseg` at `RefH`; wake's `seg_refB`): from `RefH`, a segment inside `Ws`
into nothing, given hello's program as the layout's (`hp`), the kernel at no
frames (`hK`) and the path's obligations (`hobl`). -/
theorem seg_refH (hp : L.prog = helloProg) (hK : (ms []).K = some abi)
    (hobl : RefOblH L F0 G l b ws n Ws K lbl ms) :
    SegWS Ws K helloSrc lbl ms (RefH L F0 G W Wc l b ws n) (fun _ _ _ => False) := by
  have hpS : Lays L.exe helloProg L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe helloProg L.pfx := by
    show endOf L.exe L.prog L.pfx = _; rw [hp]
  have hcode := Spike.Lib.A64.Flow.code_of hpS hendS hello_svcIn (q := cloneAtH pfxM L.exe) rfl
  let P : Region × MachineData × Ctl × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) × BitVec 64 × BitVec 64 →
      FragS isaLSE2 := fun g s c fs =>
    RefPreH L F0 G l b ws n g.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 ∧
      (At L.exe L.endPc g.1 (Spike.Lib.A64.Flow.DFrame g.1 g.2.1)
        (fNS pfxM L.lab g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 .cb)).at [] s c fs
  refine (SegWS.exists_pre (P := P) fun g => ?_).mono_pre ?_
  · by_cases hg : RefPreH L F0 G l b ws n g.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2
    · obtain ⟨hcb, hcl, hfl, hstub⟩ := hobl g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 hg
      obtain ⟨⟨F, J1, t, fr, ⟨hR, hal, -, hlo, hhi, -⟩, -⟩, -⟩ := hg
      refine (SegWS.liftS_noret [] (seg_spawnFailWS_hello hpS hendS (Q := fun _ _ => False)
        (Spike.Lib.A64.Flow.FStable.dframe g.1 g.2.1) hR hal (by omega) hhi hK hcb hcl hfl hstub)
        (fun _ _ h => h) _).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hg h.1
  · rintro s c fs ⟨rfl, s0, r, rfl, hr, -, -, -, R, F, J1, t, sl, me, cA, fr, hB, hG, hFr, hcA, hsrc, hA, -, -⟩
    refine ⟨(R, (abi.ret s0 r).st.1, c, sl, cA, me), ⟨⟨F, J1, t, fr, hB, hG, hFr, hsrc⟩, hcA⟩, ?_, rfl⟩
    exact refuse_atH hcode hA hr

end Seg

end Spike.Lib.A64.HelloPh.RefH

/-- info: 'Spike.Lib.A64.HelloPh.RefH.refuse_atH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefH.refuse_atH

/-- info: 'Spike.Lib.A64.HelloPh.RefH.hret_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefH.hret_H

/-- info: 'Spike.Lib.A64.HelloPh.RefH.seg_refH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefH.seg_refH
