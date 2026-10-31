/-
**`wc_main`'s nodes inside `SFactsSt2` at `ownG`** (x86-64; twin of
`Spike/Lib/A64WakeWcPreWN.lean`): the single-instruction part of
`X64WakeWcPreW`. Each node lemma is proved at the first instance
(`instOkW`) at the entry control `c0`, then moved to `ownG`, which picks
`ownW` at the node's pc and at the next one (both free, `freeN`).

- `nodeW_mfence_pre`: a node at `mfence` inside `SFacts`, for any cells
  (no `SFacts` lemma for `mfence` existed).
- `c0N`, `c0N_cfacts`, `nodeW_wcG`: a node's obligation at `ownG` from the
  instance's, proved at the entry control `c0`.
- `NodeW.ofAll`: a node's obligation, split over a function of the state.

**Where this differs from AArch64**: the fence is `mfence` (3 bytes,
`Out.fence .sy`; A64's `dmb`, 4 bytes, any kind), named `nodeW_mfence_pre`
(A64's `nodeW_dmb_pre`); wc_main has no fence before `.x20` (scc's
`# fence st` emits no code under TSO), its one `mfence` is at
`.Lwc_main.x21 + 12`, the lemma's use being the `.x20`–`.x21` part
(`WcSp4W`). `succ_pc` and `nodeAgreeW` are `X64WakeFree`'s, at a cell of
any size `z` off `syscall` (A64's `succ_pc4`, `nodeAgreeW` at 4 bytes off
`svc`, this file's), and so `nodeW_wcG` takes the size `z` (`hfz`,
`hstep`).
-/
import Spike.Lib.X64WakeWcPreW

namespace Spike.Lib.X64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (blockAtB)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl CFacts SFacts)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At)
open Kraken.Promising.Lower.X64 (CellAt after op64)

/-! ## A fence node inside `SFacts` -/

section Fence

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Spike.Lib.X64Consumer.Own}
  {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout}
  {rS : Range} {lbl : Lbl} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A node at `mfence`** before the take, its next pc in its phase: the
fence touches no location and keeps the owned words. -/
theorem nodeW_mfence_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(op64 .mfence, 3)] = true) (he : lab l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat 3).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  Spike.Lib.X64.Rt.nodeW_pre hI hp hok hT fun s c σ hs hn _ hpc _ _ hJ hP hO => by
    have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
    have hsm := Spike.Lib.X64.Rt.next_same hI hpc hph s.st.1
    refine Spike.Lib.X64Consumer.sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h)
      (Kraken.Promising.Lower.X64.exec_mfence hc) ?_ (.inl ⟨fun _ => hsm.1, fun _ => trivial⟩) (fun _ => hsm.2) hO
    intro h
    cases h with
    | fence h => cases h

end Fence

/-! ## A node at `ownG` from the instance's -/

/-- **A node at the entry control `c0`**: same pc and offsets, the
control `c0` with one of `n`'s at the same state. -/
def c0N (n : ND) : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.X64Consumer.c0 ∧ ∃ c', n.J σ c'⟩

/-- `c0N`'s controls have the consumer's facts. -/
theorem c0N_cfacts {Λ : Scc.Sem.Layout} {lbl : Lbl} {n : ND} :
    ∀ σ c, (c0N n).J σ c → CFacts Λ lbl c :=
  fun _ _ hJ => hJ.1 ▸ Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0

section Move

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {rS : Range} {TkW : Nat → Prop}
  {lbl : Lbl} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A node of `wc_main` inside `SFactsSt2` at `ownG`** from the
instance's `SFacts` at `c0N n` (`h`), its pc and next pc free (`hf0`,
`hfz`), each state at a cell of size `z` off `syscall` whose leaves are `z`
bytes on (`hstep`). -/
theorem nodeW_wcG (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) {K : State → State → Prop} {n : ND}
    (h : NodeW (fun s c => SFacts Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS
      (fun s => TkW (phW (pcOf s))) lbl s c) K L.exe L.endPc R F (c0N n)) {z : Nat}
    (hf0 : freeN n.pc.toBitVec.toNat = true) (hfz : freeN (n.pc + Int64.ofNat z).toBitVec.toNat = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n := by
  have hag := nodeAgreeW (a := a) (n := c0N n) (exe := L.exe) (endPc := L.endPc) (R := R) (F := F) hlab hsite
    hf0 hfz fun s c ⟨h1, h2, h3, h4, σ, hA, hF, _, c', hJ⟩ => hstep s c' ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩
  have h2 := Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.nodeW_toSt2 h) hag
  exact nodeW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

end Move

/-! ## A node split over a function of the state -/

/-- **A node's obligation from its restrictions** to each value `x` of a
function `f` of the abstract state. -/
theorem NodeW.ofAll {W : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {β : Type} (f : Spike.Lib.X64.AS → β)
    (h : ∀ x, NodeW W K exe endPc R F ⟨n.pc, n.o, fun σ c => n.J σ c ∧ f σ = x⟩) : NodeW W K exe endPc R F n :=
  fun s c ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩ => h (f σ) s c ⟨h1, h2, h3, h4, σ, hA, hF, hJ, rfl⟩

end Spike.Lib.X64.WakePh.WcW

/-- info: 'Spike.Lib.X64.WakePh.WcW.nodeW_mfence_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.nodeW_mfence_pre

/-- info: 'Spike.Lib.X64.WakePh.WcW.nodeW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.nodeW_wcG
