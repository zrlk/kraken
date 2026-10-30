/-
**wake.w on AArch64: main's permit, limit and exit pieces past the clone**: the fields `hS`, `htls`, `hexit` of
`WakeMainHR.MainPieces` at the instance (`L := RuntimeLayout.ofPlaceW hp i`,
the record `g`, its memory side `wakeMs`, main's TCB `tp = L.pinA + 0 + 8`),
at the one frame `⟨Rm.base, -96, 16⟩` with frame condition `DFrame` of it
from main's memory `m0` after the clone (`WakeMainHR.m0`):

- `locIn_tp16_I`, `locIn_tp8_I`: main's permit word `tp + 16` (`pinA + 24`)
  and limit word `tp + 8` (`pinA + 16`) are shared (in `pinned`), for
  `WakeMainFlag.hA0_of`/`hAoff_of`, which give the per-word premises `hA0`,
  `hoff` below (as `hMainR_of` does for the flag's word `cA`);
- `unmapped_I`: a word shared, off the region and unloadable in `m0` is
  unloadable under the frame condition (`WakeMainFrames.frames_unit`'s `hdm`);
- `hS_I` (`hS`): the park's store of `0` to `tp + 16` (`WakeHS.permit_free`,
  `WakeChildSt.mapped_K0_pinned`, `WakeGOf2.gOf2_ne`);
- `limOk_I`: the limit load's `LimOk` at `tp + 8` with room up to the frame's
  `x9` address (`hZ`; `WakeHS.lim_free`, `PlaceW.room_of_le`), the limit word
  not the flag's target `g.cT` (`cT_ne_I`: `cT` is in a placed label, `tp + 8`
  in none);
- `htls_I` (`htls`): `AbOffAt.seg_waitTlsW` with `hW` from
  `A64WakeMainS.tlsW_mainR` and the landing from `limOk_I` (as
  `Htls.htls_of`, at the instance's labels `LoopCode.loopLabs_wake`);
- `hexit_I` (`hexit`): past the wait loop's load the word read is the number
  `1` (`WakeInst.rd_num`), so the source's test takes `wlRet` (one
  `LowerNode.localStep_ifeq`), which returns `0` (`SrcSem.mainExit`).

Open premises (dischargers): `hA0`/`hoff` per word (`hMainR_of`, by
`hA0_of`/`hAoff_of` at `locIn_tp16_I`/`locIn_tp8_I`), `hm` (the memory
relation at the spawn, `PreR`'s `hS.inv1.mem`), `hZ` (the segment
end: main's frame above stack 0's guard), the rest the `MainPieces` fields
(`htp`, `hval`, `hwc`, `hloc`, `hin`) and the instance's
(`hprog`, `hw`, `GhOK`).

**`preMs`** (for the mid segment through the `new`;
not stated here): `{ wakeMs hp i g with newOk := True, pub := True,
own := ownG L (ntA L.lab), xa := fun l b n s c => AllocLand heap cells b n ∧
I lbl' lsize' s c fs }` (`A64ConsumerA.msOfA`-shaped); the mid segment at
`A64KeepTP.tpXa preMs tp`; its only use is `wake_wc_sp0_segW`'s `hxa`
(the post-`new` `I` contains the `bX` states), an instance-side obligation.
Past the clone main stays at `wakeMs`; structure-typed facts (`StOk`, `OKB`,
`ResOkA`, `TcbOkGA`) cross the record update by `{ h with }`.
-/
import Spike.Lib.WakeMainHR
import Spike.Lib.WakeHS
import Spike.Lib.WakeChildSt
import Spike.Lib.LowerNode1
import Spike.Lib.A64WakeAbOffL
import Spike.Lib.A64WakeLoopCode
import Spike.Lib.A64WakeMainS
import Spike.Lib.A64WakeMainClosedWS
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeMainInstD

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (ValRep LocRep MemRelP Range)
open Spike.Lib.A64.Flow
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeSpawnR
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeInst (Gh wakeMs mainWR)
open Spike.Lib.WakeInstFields (GhOK)
open Spike.Lib.A64.Flow.Worker.Wake.MainPost (mainSp0)
open Spike.Lib.WakeMainSrc (waitC)
open Spike.Lib.WakeM0 (wlIf)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-- **A word shared, off the region and unloadable in `m0`** is unloadable
under `DFrame` of the region from `m0`. -/
theorem unmapped_I {R : Region} {m0 : MachineData} {a : BitVec 64} (hA0 : Mem.loadInt m0.dmem a 8 = none)
    (hoff : a.toNat + 8 ≤ 2 ^ 64 ∧
      ((a.toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a.toNat)) :
    ∀ m, DFrame R m0 m → Mem.loadInt m.dmem a 8 = none :=
  fun _ hm => (hm a hoff.1 hoff.2).trans hA0

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- The first TCB's word `j` (`0 < j < 7`) has its bytes in `pinned`, at
`pinA + 8j`. -/
theorem pinned_j {j : Nat} (hj : j < 7) (hj0 : 0 < j) :
    ∀ k < 8, (RuntimeLayout.ofPlaceW hp i).Λ.pinned.contains
      (((RuntimeLayout.ofPlaceW hp i).pinA + BitVec.ofNat 64 (8 * j)).toNat + k) := by
  intro k hk
  rw [WakeChildSt.pinA_add hp i (by omega)]
  exact WakeChildSt.tcb_pinned hp i hj hj0 k hk

/-- **main's permit word is shared** (`pinned`). -/
theorem locIn_tp16_I :
    Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared
      ⟨(RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 16#64, 8⟩ := by
  intro k hk
  rw [WakeHS.permit_eq]
  exact .inr (.inr (pinned_j hp i (j := 3) (by decide) (by decide) k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))

/-- **main's limit word is shared** (`pinned`). -/
theorem locIn_tp8_I :
    Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared
      ⟨(RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64, 8⟩ := by
  intro k hk
  rw [WakeHS.lim_eq]
  exact .inr (.inr (pinned_j hp i (j := 2) (by decide) (by decide) k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))

/-- **`hS` at the instance**: the park's store of `0` to main's permit word
`tp + 16` under `wakeMs`, in main's frame after the clone, given the word
unloadable there (`hA0`, `hoff`: `WakeMainFlag.hA0_of`/`hAoff_of` at
`locIn_tp16_I`). -/
theorem hS_I (g : Gh) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ g.lbl g.lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 16#64) 8 = none)
    (hoff : (tp + 16#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 16#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 16#64).toNat))
    {exe : _root_.Executable} {endPc : Int64} :
    Ret0.StOk (wakeMs hp i g) (DFrame R m0) exe endPc (tp + 16#64) 0#64 := by
  have hu := unmapped_I hA0 hoff
  subst htp
  have hfree := WakeHS.permit_free hp i hm
  have ha := pinned_j hp i (j := 3) (by decide) (by decide)
  rw [← WakeHS.permit_eq] at ha
  refine ⟨hfree, ⟨WakeChildSt.stOk_pinned.mapped_K0_pinned hp i ha, fun _ => ⟨fun k hk => ?_, ?_⟩⟩, .inr ?_, hu⟩
  · exact .inr (.inr (ha k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))
  · rintro ⟨l, b, hl, hx⟩
    exact hfree ⟨l, b, hl, by simpa using hx⟩
  · rw [WakeHS.permit_eq]
    exact WakeGOf2.gOf2_ne (Spike.Lib.A64.PhRec.pin_ne (by decide)) (WakeGOf2.pin_ne2 (by decide)) _

/-- **The flag's target word is not main's limit word**: `GhOK` puts `cT`
in a placed label, `tp + 8` is in none (`WakeHS.lim_free`). -/
theorem cT_ne_I {g : Gh} (hg : GhOK (RuntimeLayout.ofPlaceW hp i).Λ g)
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ g.lbl g.lsize ts tm sm tq0 tq sp) :
    (⟨(RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64, 8⟩ : Loc) ≠ g.cT := by
  intro h
  obtain ⟨-, -, -, ⟨b, hl, ho, hT⟩, -⟩ := hg
  have hx : (Scc.Sem.lrange g.lsize g.cS.label b).contains (b + 8 * g.cS.offset) := by
    have h1 : @LT.lt Nat _ g.cS.offset (g.lsize g.cS.label) := ho
    simp only [Scc.Sem.lrange, Range.contains]; omega
  have hs := Spike.Lib.WakeGOf.heapData_of_placed hm hl hx
  have hw := (PlaceW.wf_link_of_placeW i hp).inSpace
  have hd := (hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hp i).Λ.data ∈ (RuntimeLayout.ofPlaceW hp i).Λ.regions)).2
  have hh := (hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hp i).Λ.heap ∈ (RuntimeLayout.ofPlaceW hp i).Λ.regions)).2
  have hlt : b + 8 * g.cS.offset < 2 ^ 64 := by
    simp only [Range.contains] at hs; omega
  refine WakeHS.lim_free hp i hm ⟨g.cS.label, b, hl, ?_⟩
  rw [show (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64 = g.cT.addr by rw [← h], hT]
  simp only [Scc.Sem.wordLoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact hx

/-- **The limit load's `LimOk` at the instance**: main's limit word `tp + 8`
under `wakeMs`, in main's frame after the clone (`hA0`, `hoff` as `hS_I`'s at
`locIn_tp8_I`), with room up to any `Z` at least stack 0's limit (`hZ`). -/
theorem limOk_I {g : Gh} (hg : GhOK (RuntimeLayout.ofPlaceW hp i).Λ g)
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ g.lbl g.lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 8#64).toNat))
    {Z : BitVec 64} (hZ : (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ Z.toNat)
    {exe : _root_.Executable} {endPc : Int64} :
    Ret0.LimOk (wakeMs hp i g) (DFrame R m0) exe endPc (tp + 8#64) Z := by
  have hu := unmapped_I hA0 hoff
  subst htp
  have ha := pinned_j hp i (j := 2) (by decide) (by decide)
  rw [← WakeHS.lim_eq] at ha
  refine ⟨WakeHS.lim_free hp i hm, ⟨Spike.Lib.A64Consumer.mapped_K0_of_mem fun k hk => .inr (ha k hk), nofun⟩,
    hu, fun v hv => ?_⟩
  have hg' := Spike.Lib.WakeG.wakeG_off hv (cT_ne_I hp i hg hm)
  rw [WakeHS.lim_eq, ← Spike.Lib.A64.Rt.limA_tcb0] at hg'
  exact PlaceW.room_of_le hp i hZ v (WakeGOf2.gOf_of_gOf2 hg')

/-- **`htls` at the instance**: `wc_waitLoop`'s limit load from `.tls` to
`.n1` inside `mainWR`, in main's frame `R` after the clone, `x9`'s address
`R.addr (-32)` at least stack 0's limit (`hZ`), given `limOk_I`'s premises and
the source side's (`hwc`, `hval`, `hloc`, `hin`). -/
theorem htls_I (hprog : o.prog = wakeProg) (hw : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    {g : Gh} (hg : GhOK (RuntimeLayout.ofPlaceW hp i).Λ g)
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ g.lbl g.lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 8#64).toNat))
    (hZ : (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ (R.addr (-32)).toNat)
    {w : TermRun.Word} {cA x29 ra : BitVec 64} (hwc : w.val = .loc g.cS 0) (hval : ValRep g.lbl w.val cA.toNat)
    (hloc : LocRep g.lbl w.val cA.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < g.lsize sa.label) :
    SegW (mainWR (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
        (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ g.lbl g.lsize) (fun _ _ => False)
      Spike.Lib.WakeT1.wakeSrc g.lbl (wakeMs hp i g)
      (At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) R (DFrame R m0)
        (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
          Spike.Lib.A64.WakeLabels.pfx (waitC w) "d" wlIf (.ptr .pub .int)
          (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) cA x29 ra tp .tls))
      (At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) R (DFrame R m0)
        (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
          Spike.Lib.A64.WakeLabels.pfx (waitC w) "d" wlIf (.ptr .pub .int)
          (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) cA x29 ra tp .n1)) := by
  haveI := (RuntimeLayout.ofPlaceW hp i).valid
  have hl : Scc.Cert.Rt.A64.Lays (RuntimeLayout.ofPlaceW hp i).exe wakeProg (RuntimeLayout.ofPlaceW hp i).pfx := by
    rw [← hprog]; exact (RuntimeLayout.ofPlaceW hp i).lays
  have hL := limOk_I hp i hg hm htp hA0 hoff hZ (exe := (RuntimeLayout.ofPlaceW hp i).exe) (endPc := endR hp i)
  have hrt8 := WakeInst.hrt8_of_limOk hp i g hL
  have hpc : (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
      Spike.Lib.A64.WakeLabels.pfx (waitC w) "d" wlIf (.ptr .pub .int)
      (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) cA x29 ra tp .tls).pc =
      (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
        (Spike.Lib.A64.WakeLabels.pfx ++ ".stack_check") + Int64.ofNat (4 * 2) := by
    rw [(Spike.Lib.A64.Flow.Worker.Wake.LoopCode.loopLabs_wake hl).2.1]
    show _ + 4 + 4 = _
    rw [Int64.add_assoc]; rfl
  have hruns : Spike.Lib.A64WakeOff.RunsOffA (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
      (Spike.Lib.A64WakeMainW.waitRuns Spike.Lib.A64.WakeLabels.pfx) :=
    (Spike.Lib.A64.WakeRunsOff.wake_mainRuns_off hl).mono fun _ hq =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hq))
  have hc0 : (waitC w).term ≠ WakeMLive.wlRet := by
    simp [waitC, Spike.Lib.WakeMainSrc.waitBody, WakeMLive.wlRet]
  have hfv0 : ∀ y ∈ Scc.Sem.exprFv (waitC w).term, y = "c" := by
    simp [waitC, Spike.Lib.WakeMainSrc.waitBody, Scc.Sem.exprFv, Scc.Sem.atVars, Scc.Sem.opVars, Scc.Sem.opAts]
  have hm0 := Spike.Lib.A64WakeMainL.labMapped_c0 (c0 := waitC w) rfl (Spike.Lib.WakeMainSrc.waitC_ev w) hval
    (hin.imp fun _ h => h.1) (WakeMainInst.hmA_I hg (hwc ▸ hval))
  refine Spike.Lib.A64.Flow.Worker.Wake.AbOffAt.seg_waitTlsW hl rfl hpc (FStable.dframe _ _)
    (fun s c h => (Spike.Lib.A64WakeMainS.tlsW_mainR hl rfl hpc hruns (WakeMainInst.hwide_I hp i hw) hc0 hfv0
      (by simp [waitC, TermRun.lookupE]) hloc hm0 (Spike.Lib.A64.WakeRunsOff.wake_flag_ne hl) hrt8 rfl rfl
      (Spike.Lib.WakeMainSrc.waitC_ev w) hin s c h).1) ?_
  intro m σ c hA hD hJ
  have ha : rAddr σ.regs .X10 8 = tp + 8#64 := Ret0.rAddr_x10 hJ.2 8
  rw [ha]
  refine ⟨hL.rt, hL.mp, hL.unmapped m hD, c, .refl c, fun v hv => ⟨rfl, ?_, ?_⟩⟩
  · show SO.le Spike.Lib.A64.WaitLoop.oX (Spike.Lib.A64.WaitLoop.oX.kill .X10) = true; decide
  · have hroom := hL.room v hv
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, -⟩ := hJ
    have h9 := hA.so (.reg .X9) (-32) rfl
    refine ⟨⟨h1, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64] using h2
    · simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64] using h3
    · simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64] using h4
    · rw [show (ldStep .X10 (v.setWidth 64) σ).regs.TPIDR_EL0 = σ.regs.TPIDR_EL0 from
        Spike.Lib.A64.KeepTP.setRegOrZr_tp _ _ _]; exact h5
    · simp only [Reg64s.getRegOrSp64, Reg64s.getXReg] at h9
      simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, h9] using hroom

/-- **`hexit` at the instance**: past the wait loop's load, the word read is
the number `1` (`WakeInst.rd_num`), so the source's test takes `wlRet`, a
placed control whose return is `exit` with code `0`; for any state predicate
`X` (`MainPieces.hexit`'s `At` at the exit tail). -/
theorem hexit_I (g : Gh) {w : TermRun.Word} {X : State → Ctl → Prop} :
    ∀ s c', Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
      (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) c' → X s c' →
      ¬ (wakeMs hp i g).abortAt s → MainExit Spike.Lib.WakeT1.wakeSrc (wakeMs hp i g) s c' 0 := by
  rintro s c' ⟨w', ⟨hr, hv⟩, rfl⟩ - -
  have h1 := WakeInst.rd_num hp i g w' hr hv
  have ha : TermRun.evalAt (("d", loadTy (.ptr .pub .int), [w']) :: (waitC w).env) (.var "d")
      = some (loadTy (.ptr .pub .int), [w']) := by
    simp [TermRun.evalAt, TermRun.lookupE, List.find?]
  have hs := LowerNode.localStep_ifeq (p := Spike.Lib.WakeT1.wakeSrc) (n := 1) (m := 1)
    (c := ⟨wlIf, ("d", loadTy (.ptr .pub .int), [w']) :: (waitC w).env, none⟩)
    (ta := loadTy (.ptr .pub .int)) (tb := .intS (.lit 1)) (wb := TermRun.cst (.num 1))
    rfl ha rfl h1 rfl
  rw [ite_eq_left rfl] at hs
  refine ⟨_, .single hs, ⟨fun _ _ => none, ?_, ?_, ?_⟩, ?_⟩
  · intro x ty ws hl k wd wp hk hp
    cases hp
  · intro x hx
    simp [WakeMLive.wlRet, Scc.Sem.exprFv, Scc.Sem.atVars] at hx
  · intro x k n h
    cases h
  · intro s0 th h0 ht he hst
    unfold Scc.Sem.SrcSem.mainExit
    simp only [h0, ht, hst, he]
    rfl

end Inst

/-- info: 'Spike.Lib.WakeMainInstD.unmapped_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unmapped_I

/-- info: 'Spike.Lib.WakeMainInstD.pinned_j' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pinned_j

/-- info: 'Spike.Lib.WakeMainInstD.locIn_tp16_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locIn_tp16_I

/-- info: 'Spike.Lib.WakeMainInstD.locIn_tp8_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locIn_tp8_I

/-- info: 'Spike.Lib.WakeMainInstD.hS_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hS_I

/-- info: 'Spike.Lib.WakeMainInstD.cT_ne_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cT_ne_I

/-- info: 'Spike.Lib.WakeMainInstD.limOk_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms limOk_I

/-- info: 'Spike.Lib.WakeMainInstD.htls_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms htls_I

/-- info: 'Spike.Lib.WakeMainInstD.hexit_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hexit_I

end Spike.Lib.WakeMainInstD
