/-
**main's segment-end fields at its `clone`** (wake.w, x86-64):
the x64 twin of `Spike/Lib/WakeMainHRD.lean`'s `MainSeg`, the fields of
`MainPieces` the pre-spawn segment supplies (`X64.Flow.WakeWc.ClonePost`
gives them: `mainSeg_of`).

- `MainSeg L endPc th c Rm F₂ cA fp ra tp`: main's thread `th` at the
  clone's `syscall` (`cloneAt`, offsets `oW`, `JS c cA fp ra tp`) in
  `wc_main`'s frame `⟨Rm.base, -64, 16⟩` (`hhat`), its base 64 above
  `%rsp` (`hRb`), the region not wrapping (`hRok`), `%rsp` 128 below stack
  0's top (`hsp`, `ClonePost`'s), the thread pointer `pinA + 8` (`htp`) and
  the saved return address `scc_rt_main`'s `.x2` (`hra`).
- `js_slotsOnly`, `hat_wide`, `MainSeg.base8`, `MainSeg.wideOK`,
  `MainSeg.hat`: `hhat` widened to main's post-spawn region `[-80, 40)`
  (`X64AtWiden.At.widen`; see the section doc for why only x86-64 needs it).

**Deviations from A64.** `MainSeg` is stated at any runtime layout `L` and
end of text `endPc` (A64: at `RuntimeLayout.ofPlaceW hp i` and
`WakeSpawnR.endR hp i`), so that it does not wait for the x64 `WakeSpawnR`
twin; the instance takes `L := RuntimeLayout.ofPlaceWX hp i` and its
`endR`. The region is `⟨Rm.base, -64, 16⟩` with `Rm.base = %rsp + 64` (A64
`-96`, `SP + 80`); there is no alignment field (`hal`: the x64
`parent_at_pre` and `wake_wc_mid_hatW` ask none); the return point is
`.Lscc_rt_main.x2` (`MainPost.mainX2`; A64 `mainSp0`); the parent's frame
pointer is `fp` (A64 `x29`); `hsp` is an extra field (A64 has `hal`
instead), feeding `base8`/`wideOK`. **Not here yet**: `hMainR_ofD` needs
the x64 twins of `WakeMainHR.hMainR_of`/`MainPieces`, `WakeSpawnR.{PreR, QG, ιR,
endR, HMainR}`, `WakeMainSrcR.src_pieces_R` and `WakeMainInstD`.
-/
import Spike.Lib.X64WakeMainPost
import Spike.Lib.X64WakePreA
import Spike.Lib.Rt.X64Layout
import Spike.Lib.X64AtWiden

namespace Spike.Lib.X64WakeMainHRD

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakePreA (cloneAt)
open Spike.Lib.X64.WakePh.WcClone (oW)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64.WakePh.MainPost (mainX2)

/-- **The pre-spawn segment's end fields of `MainPieces`** (see the module
doc): main's thread at the clone in `wc_main`'s frame `⟨Rm.base, -64, 16⟩`,
its base `%rsp + 64`, the thread pointer `pinA + 8`, the saved return
address `scc_rt_main`'s `.x2`. -/
structure MainSeg (L : RuntimeLayout) (endPc : Int64) (th : Thread isa) (c : Ctl) (Rm : Region)
    (F₂ : MachineData → Prop) (cA fp ra tp : BitVec 64) : Prop where
  hhat : At L.exe endPc ⟨Rm.base, -64, 16⟩ F₂ ⟨cloneAt L.exe, oW, JS c cA fp ra tp⟩ th.st c
  hRb : (Rm.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64
  hRok : (⟨Rm.base, -64, 16⟩ : Region).OK
  hsp : (th.st.st.1.regs.get64 .rsp).toNat + 128 = L.stacksA.toNat + 16384
  htp : tp = L.pinA + 0#64 + 8#64
  hra : Int64.ofBitVec ra = (_root_.Executable.labels L.exe).label mainX2

/-- **main's frame base is 8-aligned**: `%rsp + 64`, `%rsp` 128 below the
16-aligned stack 0's top (`RuntimeLayout.stacks_al`). -/
theorem MainSeg.base8 {L : RuntimeLayout} {endPc : Int64} {th : Thread isa} {c : Ctl} {Rm : Region}
    {F₂ : MachineData → Prop} {cA fp ra tp : BitVec 64} (h : MainSeg L endPc th c Rm F₂ cA fp ra tp) :
    Rm.base.toNat % 8 = 0 := by
  have h1 := h.hRb
  have h2 := h.hsp
  have h3 := L.stacks_al
  omega

/-- **main's post-spawn region `[-80, 40)` does not wrap**: stack 0 lies in
the pool (`stacks_sub`), which fits the address space (`pool_fit`). -/
theorem MainSeg.wideOK {L : RuntimeLayout} {endPc : Int64} {th : Thread isa} {c : Ctl} {Rm : Region}
    {F₂ : MachineData → Prop} {cA fp ra tp : BitVec 64} (h : MainSeg L endPc th c Rm F₂ cA fp ra tp) :
    (⟨Rm.base, -80, 40⟩ : Region).OK := by
  have h1 := h.hRb
  have h2 := h.hsp
  have h3 := L.pool_fit
  obtain ⟨h4, h5⟩ := L.stacks_sub
  simp only at h4 h5
  exact ⟨by simp only; omega, by simp only; omega⟩

/-! ## Widening main's region at the clone

**Why x86-64 widens and AArch64 does not.** On AArch64 main's region at
the clone and after it is the same `[-96, 16)`. On x86-64 the clone's
`At` (`hhat`, from `wake_wc_mid_hatW`) is on `wc_main`'s frame `[-64, 16)`,
but main's post-spawn path (`X64WakeMainClosedW`) runs the wait loop and the
`exit_group` tail on `R.fp 8`, which needs `lo ≤ -88` (the loop's frame) and
`hi ≥ 32` (the tail's `%rbp` at offset `40`): `R = [-80, 40)`. The clone's
node `JS` reads only the slots `-16`, `0`, `8` (and `fsBase`), so its `At`
widens (`At.widen`) once every new slot is mapped: they lie in
`[%rsp - 16, %rsp + 104)`, inside main's owned stack `r0` (`ClonePre`:
`Owned Λ r0`, `%rsp + 128` its top, 16 KiB), at 8-aligned addresses
(`MainSeg.base8`). The new slots' values are the loaded words; nothing else
is claimed about them. -/

/-- **The clone's node reads only `wc_main`'s slots `-16`, `0`, `8`.** -/
theorem js_slotsOnly {cP : Ctl} {A fp ra tp : BitVec 64} (b : BitVec 64) :
    SlotsOnly (JS cP A fp ra tp) (⟨b, -64, 16⟩ : Region).Off := by
  rintro σ σ' c hr - - hs ⟨hc, h16, h0, h8, htp⟩
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · rw [← hs (-16) ⟨by decide, by show (-64:Int) ≤ _; decide, by show _ ≤ (16:Int); decide⟩]; exact h16
  · rw [← hs 0 ⟨by decide, by show (-64:Int) ≤ _; decide, by show _ ≤ (16:Int); decide⟩]; exact h0
  · rw [← hs 8 ⟨by decide, by show (-64:Int) ≤ _; decide, by show _ ≤ (16:Int); decide⟩]; exact h8
  · rw [← hr]; exact htp

/-- **main's region at the clone widens to `[-80, 40)`**: the clone's `At`
on `⟨b, -64, 16⟩` (`hat`), `b = %rsp + 64` (`hRb`) 8-aligned (`hb8`), the
wide region not wrapping (`hok`), main's stack `r0` owned with `%rsp` 128
below its top (`ClonePre`). -/
theorem hat_wide {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakePreA.ClonePre Λ r0 r1 X lbl t s) {th : Thread isa} (hth : t.1.threads = #[th])
    {exe : _root_.Executable} {endPc : Int64} {b : BitVec 64} {F : MachineData → Prop} {c : Ctl}
    {A fp ra tp : BitVec 64}
    (hat : At exe endPc ⟨b, -64, 16⟩ F ⟨cloneAt exe, oW, JS c A fp ra tp⟩ th.st c)
    (hRb : (b.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64) (hb8 : b.toNat % 8 = 0)
    (hok : (⟨b, -80, 40⟩ : Region).OK) :
    At exe endPc ⟨b, -80, 40⟩ F ⟨cloneAt exe, oW, JS c A fp ra tp⟩ th.st c := by
  obtain ⟨th', -, -, -, -, -, ht', -, -, -, -, -, -, -, -, -, -, -, hown, -, -, -, -, htop, hsz, -⟩ := h
  rw [hth] at ht'
  obtain rfl : th = th' := by simpa using ht'
  refine At.widen hat rfl (js_slotsOnly b) fun k hk _ => ?_
  have ha := Region.addr_toNat hok hk
  obtain ⟨hk8, hk1, hk2⟩ := hk
  simp only at hk1 hk2 ha
  have hl := hown.2 (Region.addr ⟨b, -80, 40⟩ k).toNat (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  simpa [Scc.Sem.X64.privLoad, Option.isSome_map] using hl

/-- **`MainSeg`'s clone `At` on main's post-spawn region `[-80, 40)`**:
`hat_wide` with the base's alignment and the region's fit from the layout
(`MainSeg.base8`, `MainSeg.wideOK`). -/
theorem MainSeg.hat {L : RuntimeLayout} {endPc : Int64} {th : Thread isa} {c : Ctl} {Rm : Region}
    {F₂ : MachineData → Prop} {cA fp ra tp : BitVec 64} (hM : MainSeg L endPc th c Rm F₂ cA fp ra tp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakePreA.ClonePre Λ r0 r1 X lbl t s) (hth : t.1.threads = #[th]) :
    At L.exe endPc ⟨Rm.base, -80, 40⟩ F₂ ⟨cloneAt L.exe, oW, JS c cA fp ra tp⟩ th.st c :=
  hat_wide h hth hM.hhat hM.hRb hM.base8 hM.wideOK

end Spike.Lib.X64WakeMainHRD

/-- info: 'Spike.Lib.X64WakeMainHRD.hat_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainHRD.hat_wide

/-- info: 'Spike.Lib.X64WakeMainHRD.MainSeg.hat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainHRD.MainSeg.hat
