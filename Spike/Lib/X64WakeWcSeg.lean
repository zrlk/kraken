/-
**wc_main's segment end at main's `clone`** (wake.w, x86-64; the
layout-level half of `Spike/Lib/A64WakeWcSeg.lean`): the state at main's
`clone` that the pre-spawn segment leaves (`ClonePost`: the end of
`WakeWc.wake_wc_mid_hatW` with the caller's saved pair, main's stack and the
thread pointer's value), and from it with `X64WakePreA.ClonePre` the facts
`MainSeg`'s twin will ask (`hra`, `hA`, `hZ`).

- `ClonePost L endPc J t s c`: at the clone's `syscall` (`wcNS`, and main's
  parent node `JS` in the region `⟨R.base, -64, 16⟩`), the saved pair the
  one `scc_rt_main`'s call of `wc_main` left (`FrG` at `wJ0 (wNC lab J)`),
  `%rsp` 128 below stack 0's top, the thread pointer `pinA + 8`, the
  caller's `%rsp` at the call `R.base + 8`.
- `clonePost_of`: `ClonePost` from `wake_wc_mid_hatW`'s exit at
  `wJ0 (wNC lab J) σC` with the stack and thread pointer facts.
- `hra_of_frG`: the saved return address is `scc_rt_main`'s `.x2`.
- `hA_of_clone`: `c`'s label is placed at the cell `%r12` holds
  (`ClonePre`'s `ValRep`).
- `hZ_of`: every slot of main's frame `⟨R.base, -64, 16⟩` is above stack
  0's guard page.

**Where this differs from AArch64**: main's parent region is
`⟨R.base, -64, 16⟩` with `R.base = %rsp + 64` (A64: `-96`, `sp + 80`); the
return point is `.Lscc_rt_main.x0` (the label after the `call`; A64's
`.sp0`, `x30`), read from the slot `wNC` pins (`σC.slot (-48)`); the cell
register is `%r12` (A64 `x9`). There is no alignment conjunct: the x86-64
`wake_wc_mid_hatW` exit carries none and `parent_at_pre` asks none. `hZ_of`
is stated for any frame offset, since the x86-64 wait loop's limit slot is
fixed by `MainSeg`'s twin. **Not here**: A64's `mainSeg_of` and `hpc_of`
need the x86-64 twins of `WakeMainHRD.MainSeg` and
`WakeSpawnR.{PreR, endR, QG, ιR}`, which do not exist yet.
-/
import Spike.Lib.X64WakeWcMain
import Spike.Lib.Rt.X64Layout

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range ValRep)
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh.WcClone (oW wcNS)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64WakePreA (cloneAt ClonePre)
open Spike.Lib.X64.KeepTP (TP)

/-- **The state at main's `clone`** that the pre-spawn segment leaves: the
end of `wake_wc_mid_hatW` (`wcNS` in `wc_main`'s landing region `R`, main's
parent node in `⟨R.base, -64, 16⟩`, `R`'s base 64 above `%rsp`) with its
saved pair `fr` the one `scc_rt_main`'s call left (`FrG` at
`wJ0 (wNC lab J) σC`), `%rsp` 128 below stack 0's top (`scc_rt_main`'s 48
bytes and `wc_main`'s 80 on the stack the start switches to), the thread
pointer `pinA + 8`, and the caller's `%rsp` at the call (`σC`) `8` above
`R`'s base (pinning `fr.1`, `scc_rt_main`'s saved `%rbp`). -/
def ClonePost (L : RuntimeLayout) (endPc : Int64) (J : AS → Ctl → Prop) (t : UInt64) (s : State) (c : Ctl) :
    Prop :=
  ∃ (R : Region) (F₂ : MachineData → Prop) (σC : AS) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64),
    FrG (WakeM.wJ0 (WakeM.wNC (_root_.Executable.labels L.exe).label J).J σC) fr ∧
    At L.exe endPc R F₂ (wcNS (_root_.Executable.labels L.exe).label c (t2 (_root_.Executable.labels L.exe).label)
      (kOf (_root_.Executable.labels L.exe).label) cA m fr) s c ∧
    (⟨R.base, -64, 16⟩ : Region).OK ∧
    At L.exe endPc ⟨R.base, -64, 16⟩ F₂ ⟨cloneAt L.exe, oW, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
    (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 64 ∧
    (s.st.1.regs.get64 .rsp).toNat + 128 = L.stacksA.toNat + 16384 ∧ t.toBitVec = L.pinA + 0#64 + 8#64 ∧
    σC.regs.get64 .rsp = R.base + 8#64

/-- **`ClonePost` from `wake_wc_mid_hatW`'s exit** at `wc_main`'s entry
`wJ0 (wNC lab J) σC`, `%rsp` 128 below stack 0's top (`hsp`), the thread
pointer `pinA + 8` (`htp`) and `σC`'s `%rsp` at `R.base + 8` (`hσ`). -/
theorem clonePost_of {L : RuntimeLayout} {endPc : Int64} {J : AS → Ctl → Prop} {σC : AS} {t : UInt64}
    {R : Region} {F₂ : MachineData → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {s : State} {c : Ctl}
    (h : ∃ c0 ty l cA m fr, c = Spike.Lib.X64WakeBoxDefs.boxPubCtl c0 ty l ∧ MidPG Q c0 ty l cA ∧
      FrG (WakeM.wJ0 (WakeM.wNC (_root_.Executable.labels L.exe).label J).J σC) fr ∧
      FrMG (WakeM.wJ0 (WakeM.wNC (_root_.Executable.labels L.exe).label J).J σC) fr m ∧
      At L.exe endPc R F₂ (wcNS (_root_.Executable.labels L.exe).label c
        (t2 (_root_.Executable.labels L.exe).label) (kOf (_root_.Executable.labels L.exe).label) cA m fr) s c ∧
      (⟨R.base, -64, 16⟩ : Region).OK ∧
      At L.exe endPc ⟨R.base, -64, 16⟩ F₂ ⟨cloneAt L.exe, oW, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
      (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 64 ∧ TP t s)
    (hsp : (s.st.1.regs.get64 .rsp).toNat + 128 = L.stacksA.toNat + 16384)
    (htp : t.toBitVec = L.pinA + 0#64 + 8#64) (hσ : σC.regs.get64 .rsp = R.base + 8#64) :
    ClonePost L endPc J t s c := by
  obtain ⟨-, -, -, cA, m, fr, -, -, hfr, -, hS, hok, hat, hb, -⟩ := h
  exact ⟨R, F₂, σC, cA, m, fr, hfr, hS, hok, hat, hb, hsp, htp, hσ⟩

/-- **The saved return address is `scc_rt_main`'s `.x2`**: `wc_main`'s
entry is `scc_rt_main`'s call node (`wNC`, the return address `.x2` in the
slot at `-48`), entered at that slot (`enter (-48)`). -/
theorem hra_of_frG {lab : Label → Int64} {J : AS → Ctl → Prop} {σC : AS} {fr : BitVec 64 × BitVec 64}
    (h : FrG (WakeM.wJ0 (WakeM.wNC lab J).J σC) fr) : Int64.ofBitVec fr.2 = lab ".Lscc_rt_main.x0" := by
  obtain ⟨σe, c, ⟨rfl, -, -, h48, -⟩, rfl⟩ := h
  show Int64.ofBitVec (σC.slot (-48 + 0)) = _
  rw [show (-48 : Int) + 0 = -48 from rfl, h48]; rfl

/-- **`c`'s label is placed at the cell `%r12` holds** at the clone:
`ClonePre`'s `ValRep` of `c`'s locative at its `%r12`, `c` bound in main's
source thread to the locative of `l`. -/
theorem hA_of_clone {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {d : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} {th : Thread isa}
    {th0 : TermRun.TTh} {l : WeakMem.AllocLabel} {cA : BitVec 64}
    (hC : ClonePre Λ r0 r1 X lbl d s) (hs : s.ths = #[th0])
    (hc : TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (ht : d.1.threads = #[th]) (h12 : th.st.st.1.regs.get64 .r12 = cA) : lbl l = some cA.toNat := by
  obtain ⟨th', th0', -, cA', -, l', ht', hs', -, -, -, -, -, -, h12', -, -, -, -, -, -, -, -, -, -, -, hc', -, -,
    hv, -⟩ := hC
  rw [ht] at ht'
  obtain rfl : th = th' := by simpa using ht'
  rw [hs] at hs'
  obtain rfl : th0 = th0' := by simpa using hs'
  rw [hc] at hc'
  have e := congrArg (fun w : TermRun.Word => w.val) (by simpa using hc')
  obtain rfl : l = l' := by simpa [Promises.TVal.mk0] using e
  obtain ⟨-, x, hx, rfl⟩ := hv
  simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [Nat.mul_zero, Nat.add_zero] at h12'
  rw [hy, ← h12, ← h12']

/-- **Main's frame is above stack 0's guard page**: every offset `k` of
`⟨Rb, -64, 16⟩` is at `%rsp + 64 + k ≥ %rsp`, and `%rsp` is 128 below
stack 0's top (16 KiB). -/
theorem hZ_of {L : RuntimeLayout} {Rb : BitVec 64} {sp : Nat} (hok : (⟨Rb, -64, 16⟩ : Region).OK)
    (hb : (Rb.toNat : Int) = sp + 64) (hs : sp + 128 = L.stacksA.toNat + 16384) {k : Int} (h1 : -64 ≤ k)
    (h2 : k < 16) : L.stacksA.toNat + 4096 ≤ ((⟨Rb, -64, 16⟩ : Region).addr k).toNat := by
  have := Region.addr_toNat_of hok (k := k) h1 h2
  simp only at this
  omega

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.clonePost_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.clonePost_of

/-- info: 'Spike.Lib.X64.Flow.WakeWc.hra_of_frG' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.hra_of_frG

/-- info: 'Spike.Lib.X64.Flow.WakeWc.hA_of_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.hA_of_clone

/-- info: 'Spike.Lib.X64.Flow.WakeWc.hZ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.hZ_of
