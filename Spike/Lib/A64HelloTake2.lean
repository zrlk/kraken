/-
**hello.w's second `scc_rt_thread_init` call** (AArch64, the
`hti` chain): the twin of `Spike/Lib/A64WakeTake2.lean` at helloProg. The
instance of `own2bH` (`Spike/Lib/A64HelloOwn2.lean`) at the phase
projection `ph2bH := phH % 16` with the canonical take's phase (bit `3`
clear), and the phase facts of `scc_rt_thread_init` (`TiPh`, returning to
`wc_main`'s `.sp6`, hello.w's `.L22_wc_main`) and `scc_rt_stack_take`
(`TakePh`) there. hello.w's take site is at `2165980`, its release site at
`2166036`.

- `take2TabH`, `ti2TabH`: `takePhTab` with its pins' phases, `tiPhTab`
  returning to `.sp6`; decided at `ph2bHC` (`decide +kernel`).
- `noTk2H`: no take at a pc of a phase with bit `3` set.
- `instOk2bPH`, `tiPh2bH`, `takePh2bH`.
-/
import Spike.Lib.A64HelloTcb2
import Spike.Lib.A64WakeTake2

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (InstOk RuntimeLayout ownUpdB)
open Spike.Lib.A64.Rt.PhOfTab
open Spike.Lib.A64.WakePh (ownV)

open Spike.Lib.A64.Rt.Code in
/-- **The second `scc_rt_stack_take` call's facts**: `takePhTab` and the
phases at its pins. -/
def take2TabH : List PhFact :=
  Rt.takePhTab ++ [.ph Take.bumpL 0 14,
    .ph Take.bumpL 1 14,
    .ph Take.bumpL 11 12,
    .ph Take.bumpL 12 8,
    .ph Take.bumpL 2 14,
    .ph Take.bumpL 21 8,
    .ph Take.bumpL 5 14,
    .ph Take.bumpL 6 12,
    .ph Take.bumpL 7 12,
    .ph Take.bumpL 8 12,
    .ph Take.clsL 0 12,
    .ph Take.clsL 4 12,
    .ph Take.doneL 0 12,
    .ph Take.doneL 1 12,
    .ph Take.doneL 14 12,
    .ph Take.doneL 15 12,
    .ph Take.doneL 16 12,
    .ph Take.doneL 2 12,
    .ph Take.doneL 7 12,
    .ph Take.doneL 8 12,
    .ph Take.doneL 9 12,
    .ph Take.entryL 0 12,
    .ph Take.fnL 0 12,
    .ph Take.lockedL 0 14,
    .ph Take.lockedL 1 14,
    .ph Take.lockedL 2 14,
    .ph Take.okL 0 8,
    .ph Take.okL 1 8,
    .ph Take.okL 2 8,
    .ph Take.siteL 0 8,
    .ph Take.siteL 1 0,
    .ph Take.spinL 0 12,
    .ph Take.spinL 2 12,
    .ph Take.spinL 3 14,
    .ph Take.takenL 0 8]

open Spike.Lib.A64.Rt.Code in
/-- **The second `scc_rt_thread_init` call's facts**: `tiPhTab` returning to
`wc_main`'s `.sp6`. -/
def ti2TabH : List PhFact :=
  [.blk Ti.fnL 0 Ti.tiPro none none, .blk Ti.entryL 0 Ti.tiCall none none, .blk Ti.spL 0 Ti.tiSp none none,
    .blk Ti.spL 12 Ti.tiF1 none none, .blk Ti.spL 15 Ti.tiF2 none none, .blk Ti.spL 18 Ti.tiF3 none none,
    .blk Ti.spL 21 Ti.tiF4 none none, .blk Ti.spL 24 Ti.tiF5 none none,
    .blk Ti.spL 27 Ti.tiRet (some ".L22_wc_main.sp6") none,
    .step Ti.spL 11, .step Ti.spL 14, .step Ti.spL 17, .step Ti.spL 20, .step Ti.spL 23, .step Ti.spL 26,
    .ph Ti.fnL 0 12, .ph Ti.entryL 0 12]

theorem take2FactsH : take2TabH.all (factOk (codeT lo SccCode.helloProg) okC ph2bHC) = true := by
  decide +kernel

theorem ti2FactsH : ti2TabH.all (factOk (codeT lo SccCode.helloProg) okC ph2bHC) = true := by
  decide +kernel

theorem take2_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ take2TabH) : factOk (codeOf lo SccCode.helloProg) (okPcOf lo SccCode.helloProg Λ) ph2bH f = true := by
  have := List.all_eq_true.mp take2FactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← ph2bH_eq] at this
  exact this

theorem ti2_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ ti2TabH) : factOk (codeOf lo SccCode.helloProg) (okPcOf lo SccCode.helloProg Λ) ph2bH f = true := by
  have := List.all_eq_true.mp ti2FactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← ph2bH_eq] at this
  exact this

/-- **No take at a pc of a phase with bit `3` set.** -/
theorem noTk2H {lab : Label → Int64} (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x)
    {Λ : Scc.Sem.Layout} {l : String} {k v : Nat}
    (h : factOk (codeOf lo SccCode.helloProg) (okPcOf lo SccCode.helloProg Λ) ph2bH (.ph l k v) = true)
    (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = (lab l + Int64.ofNat (4 * k)).toBitVec.toNat → ¬ ph2bH (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, ph_of_factOk hlab h] at hT
  omega

/-- **The instance's facts of the second `scc_rt_thread_init` call**:
`own2bH` through `ph2bH`, the canonical take's phase. -/
theorem instOk2bPH {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => own2bH L a (ph2bH (pcOf s)))
      (fun s => ph2bH (pcOf s) / 8 % 2 = 0) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo SccCode.helloProg L.Λ) ph2bH
      L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (own2bH L a) h, by simp only [h]⟩
  off := (instOkH hp hlo 0#64 (fun _ => True) hsite (rS := rS)).off

section Ti

open Spike.Lib.A64.Rt.Ti (TiPh stPcs)
open Spike.Lib.A64.Flow.Ret0.ThreadInit

/-- **The second `scc_rt_thread_init` call's phase facts** at `ph2bH`
(`tiPh_ofPlaceOK`), returning to `wc_main`'s `.sp6`. -/
theorem tiPh2bH {L : RuntimeLayout} (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    TiPh (okPcOf lo SccCode.helloProg L.Λ) ph2bH (fun s => ph2bH (pcOf s) / 8 % 2 = 0) L.lab
      (fun _ => L.lab ".L22_wc_main.sp6") := by
  have hf : ∀ f ∈ ti2TabH, _ := fun f hf => ti2_factH hΛ (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → L.lab ".L22_wc_main.sp6" = L.lab r := fun _ h => nomatch h
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Ti.fnL 0 Rt.Code.Ti.tiPro none none)
      (by simp [ti2TabH]))
    entry := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Ti.entryL 0 Rt.Code.Ti.tiCall none none)
      (by simp [ti2TabH]))
    sp := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Ti.spL 0 Rt.Code.Ti.tiSp none none)
      (by simp [ti2TabH]))
    f1 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Ti.spL 12 Rt.Code.Ti.tiF1 none none)
      (by simp [ti2TabH]))
    f2 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Ti.spL 15 Rt.Code.Ti.tiF2 none none)
      (by simp [ti2TabH]))
    f3 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Ti.spL 18 Rt.Code.Ti.tiF3 none none)
      (by simp [ti2TabH]))
    f4 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Ti.spL 21 Rt.Code.Ti.tiF4 none none)
      (by simp [ti2TabH]))
    f5 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Ti.spL 24 Rt.Code.Ti.tiF5 none none)
      (by simp [ti2TabH]))
    ret := blkPh_of_factOk hlab (fun _ h => by cases h; rfl) hn
      (hf (.blk Rt.Code.Ti.spL 27 Rt.Code.Ti.tiRet (some ".L22_wc_main.sp6") none) (by simp [ti2TabH]))
    st := by
      intro p hp
      simp only [stPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step Rt.Code.Ti.spL 11) (by simp [ti2TabH]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Ti.spL 14) (by simp [ti2TabH]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Ti.spL 17) (by simp [ti2TabH]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Ti.spL 20) (by simp [ti2TabH]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Ti.spL 23) (by simp [ti2TabH]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Ti.spL 26) (by simp [ti2TabH]))
    noTk := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact noTk2H hlab (hf (.ph Rt.Code.Ti.fnL 0 12) (by simp [ti2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Ti.entryL 0 12) (by simp [ti2TabH])) (by decide) }


end Ti

section Take

open Spike.Lib.A64.Rt.Take (TakePh siPcs takePcs)
open Spike.Lib.A64.Flow.Ret0.StackTake

/-- **The second `scc_rt_stack_take` call's phase facts** at `ph2bH`
(`takePh_ofPlaceOK` with `own2bH`), returning into `scc_rt_thread_init`,
given the counters distinct (`c1`-`c8`). -/
theorem takePh2bH {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {a : BitVec 64}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (c1 : L.pnA ≠ L.nextA) (c2 : L.pnA ≠ L.lockA) (c3 : L.pnA ≠ L.freeNA) (c4 : L.nextA ≠ L.lockA)
    (c5 : L.nextA ≠ L.freeNA) (c6 : L.lockA ≠ L.freeNA) (c7 : L.lockA ≠ a) (c8 : L.nextA ≠ a) :
    TakePh (okPcOf lo SccCode.helloProg L.Λ) ph2bH (fun s => ph2bH (pcOf s) / 8 % 2 = 0) (own2bH L a)
      (Spike.Lib.A64.PhRec.μ L) L.lab (fun _ => L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL) := by
  have hf : ∀ f ∈ take2TabH, _ := fun f hf => take2_factH hΛ (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r →
      L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL = L.lab r := fun _ h => nomatch h
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hnx : Spike.Lib.A64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  have hsite : (L.lab siteL).toBitVec.toNat = 2165980 :=
    pcAt0_eq hlab (by unfold Scc.Cert.Rt.A64.pcAt; rw [← codeT_eq]; decide +kernel)
  have hs12 := ph_of_factOk hlab (hf (.ph Rt.Code.Take.spinL 2 12) (by simp [take2TabH]))
  have hs14 := ph_of_factOk hlab (hf (.ph Rt.Code.Take.spinL 3 14) (by simp [take2TabH]))
  have hb14 := ph_of_factOk hlab (hf (.ph Rt.Code.Take.bumpL 5 14) (by simp [take2TabH]))
  have hb12 := ph_of_factOk hlab (hf (.ph Rt.Code.Take.bumpL 6 12) (by simp [take2TabH]))
  have hn12 := ph_of_factOk hlab (hf (.ph Rt.Code.Take.bumpL 11 12) (by simp [take2TabH]))
  have hn8 := ph_of_factOk hlab (hf (.ph Rt.Code.Take.bumpL 12 8) (by simp [take2TabH]))
  have ht8 : ph2bH (L.lab siteL).toBitVec.toNat = 8 := by
    have := ph_of_factOk hlab (hf (.ph Rt.Code.Take.siteL 0 8) (by simp [take2TabH]))
    rwa [Spike.Lib.A64.Flow.ofNat4_zero] at this
  have ht0 : ph2bH (L.lab siteL + Int64.ofNat 4).toBitVec.toNat = 0 := by
    have := ph_of_factOk hlab (hf (.ph Rt.Code.Take.siteL 1 0) (by simp [take2TabH]))
    rwa [show Int64.ofNat (4 * 1) = Int64.ofNat 4 from rfl] at this
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.fnL 0 Rt.Code.Take.stPro none none)
      (by simp [take2TabH, Rt.takePhTab]))
    entry := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.entryL 0 Rt.Code.Take.stInit none none)
      (by simp [take2TabH, Rt.takePhTab]))
    cls := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.clsL 0 Rt.Code.Take.stCls none none)
      (by simp [take2TabH, Rt.takePhTab]))
    j1 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.clsL 4 Rt.Code.Take.stJ1 none none)
      (by simp [take2TabH, Rt.takePhTab]))
    d2 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.doneL 2 Rt.Code.Take.stFreeN none none)
      (by simp [take2TabH, Rt.takePhTab]))
    d9 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.doneL 9 Rt.Code.Take.stFree none none)
      (by simp [take2TabH, Rt.takePhTab]))
    d16 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.doneL 16 Rt.Code.Take.stLock none none)
      (by simp [take2TabH, Rt.takePhTab]))
    sp0 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.spinL 0 Rt.Code.Take.stSwp none none)
      (by simp [take2TabH, Rt.takePhTab]))
    sp3 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.spinL 3 Rt.Code.Take.stSpin none none)
      (by simp [take2TabH, Rt.takePhTab]))
    lk0 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.lockedL 0 Rt.Code.Take.stLdN none none)
      (by simp [take2TabH, Rt.takePhTab]))
    lk2 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.lockedL 2 Rt.Code.Take.stEmpty none none)
      (by simp [take2TabH, Rt.takePhTab]))
    b2 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.bumpL 2 Rt.Code.Take.stUnl none none)
      (by simp [take2TabH, Rt.takePhTab]))
    b8 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.bumpL 8 Rt.Code.Take.stAdd none none)
      (by simp [take2TabH, Rt.takePhTab]))
    b12 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.bumpL 12 Rt.Code.Take.stBnd none none)
      (by simp [take2TabH, Rt.takePhTab]))
    b21 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.bumpL 21 Rt.Code.Take.stJ2 none none)
      (by simp [take2TabH, Rt.takePhTab]))
    ok2 := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.okL 2 Rt.Code.Take.stOk none none)
      (by simp [take2TabH, Rt.takePhTab]))
    tk := blkPh_of_factOk hlab hr hn (hf (.blk Rt.Code.Take.takenL 0 Rt.Code.Take.stSite none none)
      (by simp [take2TabH, Rt.takePhTab]))
    ret := blkPh_of_factOk hlab (fun _ h => by cases h; rfl) hn
      (hf (.blk Rt.Code.Take.siteL 1 Rt.Code.Take.stRet (some Rt.Code.Ti.spL) none) (by simp [take2TabH, Rt.takePhTab]))
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.doneL 0) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.doneL 1) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.doneL 7) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.doneL 8) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.doneL 14) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.doneL 15) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.bumpL 0) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.bumpL 1) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.bumpL 6) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.bumpL 7) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.okL 0) (by simp [take2TabH, Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Rt.Code.Take.okL 1) (by simp [take2TabH, Rt.takePhTab]))
    swpOk := ok_of_factOk hlab (hf (.ok Rt.Code.Take.spinL 2) (by simp [take2TabH, Rt.takePhTab]))
    ldnOk := (step_of_factOk hlab (hf (.step Rt.Code.Take.lockedL 1) (by simp [take2TabH, Rt.takePhTab]))).1
    unlOk := ok_of_factOk hlab (hf (.ok Rt.Code.Take.bumpL 5) (by simp [take2TabH, Rt.takePhTab]))
    nxtOk := ok_of_factOk hlab (hf (.ok Rt.Code.Take.bumpL 11) (by simp [take2TabH, Rt.takePhTab]))
    ldnPh := (step_of_factOk hlab (hf (.step Rt.Code.Take.lockedL 1) (by simp [take2TabH, Rt.takePhTab]))).2
    noTk := by
      intro p hp
      simp only [takePcs, siPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.fnL 0 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.entryL 0 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.clsL 0 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.clsL 4 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.doneL 2 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.doneL 9 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.doneL 16 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.spinL 0 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.spinL 2 12) (by simp [take2TabH])) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk2H hlab (hf (.ph Rt.Code.Take.spinL 3 14) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.spinL 3 14) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.lockedL 0 14) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.lockedL 1 14) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.lockedL 2 14) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 2 14) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 5 14) (by simp [take2TabH])) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 6 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 8 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 11 12) (by simp [take2TabH])) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 12 8) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 12 8) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 21 8) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.okL 2 8) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.takenL 0 8) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.siteL 0 8) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.doneL 0 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.doneL 1 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.doneL 7 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.doneL 8 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.doneL 14 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.doneL 15 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 0 14) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 1 14) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 6 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.bumpL 7 12) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.okL 0 8) (by simp [take2TabH])) (by decide)
      · exact noTk2H hlab (hf (.ph Rt.Code.Take.okL 1 8) (by simp [take2TabH])) (by decide)
    swpIn := ⟨(0#64).setWidth 128, by rw [swpPc, hs12, hlk]; simp [own2bH, ownV]⟩
    swpUpd := by
      rw [swpPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hs12, hs14, hlk]
      simp [ownUpdB, own2bH, ownV, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    unlIn := ⟨(1#64).setWidth 128, by rw [unlPc, hb14, hlk]; simp [own2bH, ownV]⟩
    unlUpd := by
      rw [unlPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hb14, hb12, hlk]
      simp [ownUpdB, own2bH, ownV, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    nxtIn := ⟨(16384#64).setWidth 128, by rw [nextPc, hn12, hnx]; simp [own2bH, ownV]⟩
    nxtUpd := by
      rw [nextPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hn12, hn8, hnx]
      simp [ownUpdB, own2bH, ownV, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
      rfl
    siteRel := fun a ha => by
      have e : (Spike.Lib.A64.PhRec.μ L).site .release = some 2166036 := by
        show codeOf L.Λ.code.lo L.prog "scc_rt_release_site" = _; rw [hp, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha; rw [hsite]; decide
    siteAb := fun k a ha => by
      have e : (Spike.Lib.A64.PhRec.μ L).abortAt k = codeOf lo SccCode.helloProg (Scc.Cert.Link.abortName k) := by
        show codeOf L.Λ.code.lo L.prog (L.Λ.abortLbl k) = _; rw [hp, hlo, hΛ]
      rw [e, ← codeT_eq] at ha; rw [hsite]
      cases k <;> (rintro rfl; revert ha; decide +kernel)
    siteAt := by
      show codeOf L.Λ.code.lo L.prog "scc_rt_take_site" = _
      rw [hp, hlo, hsite, ← codeT_eq]; decide +kernel
    siteOwn := by rw [ht8, ht0]; rfl
    tk4 := fun s hs => by show ph2bH (pcOf s) / 8 % 2 = 0; rw [hs, ht0] }


end Take

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.tiPh2bH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.tiPh2bH

/-- info: 'Spike.Lib.A64.HelloPh.takePh2bH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.takePh2bH

/-- info: 'Spike.Lib.A64.HelloPh.instOk2bPH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.instOk2bPH
