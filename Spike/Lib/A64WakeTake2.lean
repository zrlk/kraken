/-
**wake.w's second `scc_rt_thread_init` call** (AArch64): the instance of
`own2b` (`Spike/Lib/A64WakeOwn2.lean`) at the phase projection
`ph2b := phW % 16` (the canonical phase: `phOf < 16`) with the canonical
take's phase (bit `3` clear, relative to the second thread's range), and
the phase facts of `scc_rt_thread_init` (`TiPh`, returning to `wc_main`'s
`.sp6`) and `scc_rt_stack_take` (`TakePh`) there.

Per-call phase projection; generic multi-spawn wants a reserve/post-take
phase bit (trusted, cleanup list). `own2b` reads the bits `1`
(`scc_rt_stack_lock`) and `2` (`scc_rt_stack_next`) only, the take's phase
bit `3`; `scc_rt_thread_init`'s return (phase `0`) and `.sp6` (`16`) have
the same projection `0`.

- `ph2b`, `ph2bC`, `ph2b_eq`: the projection, through the resolved tables.
- `take2Tab`, `ti2Tab`: `takePhTab` with its pins' phases, `tiPhTab`
  returning to `.sp6`; decided at `ph2bC` (`decide +kernel`).
- `noTk2`: no take at a pc of a phase with bit `3` set.
- `own2a_own2b_ph`: the second switch at the two phase maps (`ph2a` at the
  caller's `bl`, `ph2b` at the callee's entry).
- `instOk2bP`, `tiPh2b`, `takePh2b`.
-/
import Spike.Lib.A64WakeTcb2
import Spike.Lib.Rt.A64RtTi

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (InstOk RuntimeLayout ownUpdB)
open Spike.Lib.A64.Rt.PhOfTab

/-- **The second `scc_rt_thread_init` call's phase projection**: the
canonical bits `0`-`3` of `phW`. -/
def ph2b (pc : Nat) : Nat := phW pc % 16

/-- The projection through the resolved tables. -/
def ph2bC (pc : Nat) : Nat := phC pc % 16

theorem ph2b_eq : ph2b = ph2bC := by
  funext pc; unfold ph2b ph2bC; rw [phW_eq]

open Spike.Lib.A64.Rt.Code in
/-- **The second `scc_rt_stack_take` call's facts**: `takePhTab` and the
phases at its pins. -/
def take2Tab : List PhFact :=
  Spike.Lib.A64.Rt.takePhTab ++ [.ph Take.bumpL 0 14,
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
def ti2Tab : List PhFact :=
  [.blk Ti.fnL 0 Ti.tiPro none none, .blk Ti.entryL 0 Ti.tiCall none none, .blk Ti.spL 0 Ti.tiSp none none,
    .blk Ti.spL 12 Ti.tiF1 none none, .blk Ti.spL 15 Ti.tiF2 none none, .blk Ti.spL 18 Ti.tiF3 none none,
    .blk Ti.spL 21 Ti.tiF4 none none, .blk Ti.spL 24 Ti.tiF5 none none,
    .blk Ti.spL 27 Ti.tiRet (some ".L21_wc_main.sp6") none,
    .step Ti.spL 11, .step Ti.spL 14, .step Ti.spL 17, .step Ti.spL 20, .step Ti.spL 23, .step Ti.spL 26,
    .ph Ti.fnL 0 12, .ph Ti.entryL 0 12]

theorem take2Facts : take2Tab.all (factOk (codeT lo wakeProg) okC ph2bC) = true := by
  decide +kernel

theorem ti2Facts : ti2Tab.all (factOk (codeT lo wakeProg) okC ph2bC) = true := by
  decide +kernel

theorem take2_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ take2Tab) : factOk (codeOf lo wakeProg) (okPcOf lo wakeProg Λ) ph2b f = true := by
  have := List.all_eq_true.mp take2Facts f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← ph2b_eq] at this
  exact this

theorem ti2_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ ti2Tab) : factOk (codeOf lo wakeProg) (okPcOf lo wakeProg Λ) ph2b f = true := by
  have := List.all_eq_true.mp ti2Facts f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← ph2b_eq] at this
  exact this

/-- **No take at a pc of a phase with bit `3` set.** -/
theorem noTk2 {lab : Label → Int64} (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x)
    {Λ : Scc.Sem.Layout} {l : String} {k v : Nat}
    (h : factOk (codeOf lo wakeProg) (okPcOf lo wakeProg Λ) ph2b (.ph l k v) = true) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = (lab l + Int64.ofNat (4 * k)).toBitVec.toNat → ¬ ph2b (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, ph_of_factOk hlab h] at hT
  omega

/-- `own2b` reads the bits `1` and `2` of the phase only. -/
theorem own2b_mod16 (L : RuntimeLayout) (a : BitVec 64) (i : Nat) : own2b L a (i % 16) = own2b L a i := by
  have h1 : i % 16 / 2 % 2 = i / 2 % 2 := by omega
  have h2 : i % 16 / 4 % 2 = i / 4 % 2 := by omega
  unfold own2b ownV
  rw [h1, h2]
  simp

/-- **The second switch at the two phase maps**: past `wc_main`'s second
`bl scc_rt_thread_init` (`ph2a`, the second instance) at the callee's entry
(`ph2b`, this one) the lists agree. -/
theorem own2a_own2b_ph (L : RuntimeLayout) (a : BitVec 64) :
    own2a L a (ph2a 2169288) = own2b L a (ph2b 2165244) := by
  have h1 : ph2a 2169288 = 0 := by rw [ph2a_eq]; unfold ph2aC; rw [threadInit2_ph.1]
  have h2 : ph2b 2165244 = 12 := by rw [ph2b_eq]; unfold ph2bC; rw [threadInit2_ph.2.2]
  rw [h1, h2]; unfold own2a own2b ownV; simp

/-- **The instance's facts of the second `scc_rt_thread_init` call**:
`own2b` through `ph2b`, the canonical take's phase. -/
theorem instOk2bP {L : RuntimeLayout} (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s)))
      (fun s => ph2b (pcOf s) / 8 % 2 = 0) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo wakeProg L.Λ) ph2b L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (own2b L a) h, by simp only [h]⟩
  off := (instOkW hp hlo 0#64 (fun _ => True) hsite (rS := rS)).off

section Ti

open Spike.Lib.A64.Rt.Ti (TiPh stPcs)
open Spike.Lib.A64.Flow.Ret0.ThreadInit

/-- **The second `scc_rt_thread_init` call's phase facts** at `ph2b`
(`tiPh_ofPlaceOK`), returning to `wc_main`'s `.sp6`. -/
theorem tiPh2b {L : RuntimeLayout} (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    TiPh (okPcOf lo wakeProg L.Λ) ph2b (fun s => ph2b (pcOf s) / 8 % 2 = 0) L.lab
      (fun _ => L.lab ".L21_wc_main.sp6") := by
  have hf : ∀ f ∈ ti2Tab, _ := fun f hf => ti2_fact hΛ (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo wakeProg) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → L.lab ".L21_wc_main.sp6" = L.lab r := fun _ h => nomatch h
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Ti.fnL 0 Spike.Lib.A64.Rt.Code.Ti.tiPro none none)
      (by simp [ti2Tab]))
    entry := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Ti.entryL 0 Spike.Lib.A64.Rt.Code.Ti.tiCall none none)
      (by simp [ti2Tab]))
    sp := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Ti.spL 0 Spike.Lib.A64.Rt.Code.Ti.tiSp none none)
      (by simp [ti2Tab]))
    f1 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Ti.spL 12 Spike.Lib.A64.Rt.Code.Ti.tiF1 none none)
      (by simp [ti2Tab]))
    f2 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Ti.spL 15 Spike.Lib.A64.Rt.Code.Ti.tiF2 none none)
      (by simp [ti2Tab]))
    f3 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Ti.spL 18 Spike.Lib.A64.Rt.Code.Ti.tiF3 none none)
      (by simp [ti2Tab]))
    f4 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Ti.spL 21 Spike.Lib.A64.Rt.Code.Ti.tiF4 none none)
      (by simp [ti2Tab]))
    f5 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Ti.spL 24 Spike.Lib.A64.Rt.Code.Ti.tiF5 none none)
      (by simp [ti2Tab]))
    ret := blkPh_of_factOk hlab (fun _ h => by cases h; rfl) hn
      (hf (.blk Spike.Lib.A64.Rt.Code.Ti.spL 27 Spike.Lib.A64.Rt.Code.Ti.tiRet (some ".L21_wc_main.sp6") none) (by simp [ti2Tab]))
    st := by
      intro p hp
      simp only [stPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Ti.spL 11) (by simp [ti2Tab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Ti.spL 14) (by simp [ti2Tab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Ti.spL 17) (by simp [ti2Tab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Ti.spL 20) (by simp [ti2Tab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Ti.spL 23) (by simp [ti2Tab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Ti.spL 26) (by simp [ti2Tab]))
    noTk := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Ti.fnL 0 12) (by simp [ti2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Ti.entryL 0 12) (by simp [ti2Tab])) (by decide) }


end Ti

section Take

open Spike.Lib.A64.Rt.Take (TakePh siPcs takePcs)
open Spike.Lib.A64.Flow.Ret0.StackTake

/-- **The second `scc_rt_stack_take` call's phase facts** at `ph2b`
(`takePh_ofPlaceOK` with `own2b`), returning into `scc_rt_thread_init`,
given the counters distinct (`c1`-`c8`). -/
theorem takePh2b {L : RuntimeLayout} (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {a : BitVec 64}
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (c1 : L.pnA ≠ L.nextA) (c2 : L.pnA ≠ L.lockA) (c3 : L.pnA ≠ L.freeNA) (c4 : L.nextA ≠ L.lockA)
    (c5 : L.nextA ≠ L.freeNA) (c6 : L.lockA ≠ L.freeNA) (c7 : L.lockA ≠ a) (c8 : L.nextA ≠ a) :
    TakePh (okPcOf lo wakeProg L.Λ) ph2b (fun s => ph2b (pcOf s) / 8 % 2 = 0) (own2b L a)
      (Spike.Lib.A64.PhRec.μ L) L.lab (fun _ => L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL) := by
  have hf : ∀ f ∈ take2Tab, _ := fun f hf => take2_fact hΛ (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo wakeProg) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r →
      L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL = L.lab r := fun _ h => nomatch h
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hnx : Spike.Lib.A64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  have hsite : (L.lab siteL).toBitVec.toNat = 2165940 :=
    pcAt0_eq hlab (by unfold Scc.Cert.Rt.A64.pcAt; rw [← codeT_eq]; decide +kernel)
  have hs12 := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.spinL 2 12) (by simp [take2Tab]))
  have hs14 := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.spinL 3 14) (by simp [take2Tab]))
  have hb14 := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 5 14) (by simp [take2Tab]))
  have hb12 := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 6 12) (by simp [take2Tab]))
  have hn12 := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 11 12) (by simp [take2Tab]))
  have hn8 := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 12 8) (by simp [take2Tab]))
  have ht8 : ph2b (L.lab siteL).toBitVec.toNat = 8 := by
    have := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.siteL 0 8) (by simp [take2Tab]))
    rwa [Spike.Lib.A64.Flow.ofNat4_zero] at this
  have ht0 : ph2b (L.lab siteL + Int64.ofNat 4).toBitVec.toNat = 0 := by
    have := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.siteL 1 0) (by simp [take2Tab]))
    rwa [show Int64.ofNat (4 * 1) = Int64.ofNat 4 from rfl] at this
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.fnL 0 Spike.Lib.A64.Rt.Code.Take.stPro none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    entry := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.entryL 0 Spike.Lib.A64.Rt.Code.Take.stInit none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    cls := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.clsL 0 Spike.Lib.A64.Rt.Code.Take.stCls none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    j1 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.clsL 4 Spike.Lib.A64.Rt.Code.Take.stJ1 none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    d2 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.doneL 2 Spike.Lib.A64.Rt.Code.Take.stFreeN none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    d9 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.doneL 9 Spike.Lib.A64.Rt.Code.Take.stFree none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    d16 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.doneL 16 Spike.Lib.A64.Rt.Code.Take.stLock none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    sp0 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.spinL 0 Spike.Lib.A64.Rt.Code.Take.stSwp none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    sp3 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.spinL 3 Spike.Lib.A64.Rt.Code.Take.stSpin none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    lk0 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.lockedL 0 Spike.Lib.A64.Rt.Code.Take.stLdN none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    lk2 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.lockedL 2 Spike.Lib.A64.Rt.Code.Take.stEmpty none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    b2 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.bumpL 2 Spike.Lib.A64.Rt.Code.Take.stUnl none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    b8 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.bumpL 8 Spike.Lib.A64.Rt.Code.Take.stAdd none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    b12 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.bumpL 12 Spike.Lib.A64.Rt.Code.Take.stBnd none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    b21 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.bumpL 21 Spike.Lib.A64.Rt.Code.Take.stJ2 none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    ok2 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.okL 2 Spike.Lib.A64.Rt.Code.Take.stOk none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    tk := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Take.takenL 0 Spike.Lib.A64.Rt.Code.Take.stSite none none)
      (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    ret := blkPh_of_factOk hlab (fun _ h => by cases h; rfl) hn
      (hf (.blk Spike.Lib.A64.Rt.Code.Take.siteL 1 Spike.Lib.A64.Rt.Code.Take.stRet (some Spike.Lib.A64.Rt.Code.Ti.spL) none) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.doneL 0) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.doneL 1) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.doneL 7) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.doneL 8) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.doneL 14) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.doneL 15) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.bumpL 0) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.bumpL 1) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.bumpL 6) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.bumpL 7) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.okL 0) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.okL 1) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    swpOk := ok_of_factOk hlab (hf (.ok Spike.Lib.A64.Rt.Code.Take.spinL 2) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    ldnOk := (step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.lockedL 1) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))).1
    unlOk := ok_of_factOk hlab (hf (.ok Spike.Lib.A64.Rt.Code.Take.bumpL 5) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    nxtOk := ok_of_factOk hlab (hf (.ok Spike.Lib.A64.Rt.Code.Take.bumpL 11) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))
    ldnPh := (step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Take.lockedL 1) (by simp [take2Tab, Spike.Lib.A64.Rt.takePhTab]))).2
    noTk := by
      intro p hp
      simp only [takePcs, siPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.fnL 0 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.entryL 0 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.clsL 0 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.clsL 4 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.doneL 2 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.doneL 9 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.doneL 16 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.spinL 0 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.spinL 2 12) (by simp [take2Tab])) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.spinL 3 14) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.spinL 3 14) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.lockedL 0 14) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.lockedL 1 14) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.lockedL 2 14) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 2 14) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 5 14) (by simp [take2Tab])) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 6 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 8 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 11 12) (by simp [take2Tab])) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 12 8) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 12 8) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 21 8) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.okL 2 8) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.takenL 0 8) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.siteL 0 8) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.doneL 0 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.doneL 1 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.doneL 7 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.doneL 8 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.doneL 14 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.doneL 15 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 0 14) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 1 14) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 6 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.bumpL 7 12) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.okL 0 8) (by simp [take2Tab])) (by decide)
      · exact noTk2 hlab (hf (.ph Spike.Lib.A64.Rt.Code.Take.okL 1 8) (by simp [take2Tab])) (by decide)
    swpIn := ⟨(0#64).setWidth 128, by rw [swpPc, hs12, hlk]; simp [own2b, ownV]⟩
    swpUpd := by
      rw [swpPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hs12, hs14, hlk]
      simp [ownUpdB, own2b, ownV, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    unlIn := ⟨(1#64).setWidth 128, by rw [unlPc, hb14, hlk]; simp [own2b, ownV]⟩
    unlUpd := by
      rw [unlPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hb14, hb12, hlk]
      simp [ownUpdB, own2b, ownV, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    nxtIn := ⟨(16384#64).setWidth 128, by rw [nextPc, hn12, hnx]; simp [own2b, ownV]⟩
    nxtUpd := by
      rw [nextPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hn12, hn8, hnx]
      simp [ownUpdB, own2b, ownV, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
      rfl
    siteRel := fun a ha => by
      have e : (Spike.Lib.A64.PhRec.μ L).site .release = some 2165996 := by
        show codeOf L.Λ.code.lo L.prog "scc_rt_release_site" = _; rw [hp, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha; rw [hsite]; decide
    siteAb := fun k a ha => by
      have e : (Spike.Lib.A64.PhRec.μ L).abortAt k = codeOf lo wakeProg (Scc.Cert.Link.abortName k) := by
        show codeOf L.Λ.code.lo L.prog (L.Λ.abortLbl k) = _; rw [hp, hlo, hΛ]
      rw [e, ← codeT_eq] at ha; rw [hsite]
      cases k <;> (rintro rfl; revert ha; decide +kernel)
    siteAt := by
      show codeOf L.Λ.code.lo L.prog "scc_rt_take_site" = _
      rw [hp, hlo, hsite, ← codeT_eq]; decide +kernel
    siteOwn := by rw [ht8, ht0]; rfl
    tk4 := fun s hs => by show ph2b (pcOf s) / 8 % 2 = 0; rw [hs, ht0] }


end Take

end Spike.Lib.A64.WakePh

/-- info: 'Spike.Lib.A64.WakePh.tiPh2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.tiPh2b

/-- info: 'Spike.Lib.A64.WakePh.takePh2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.takePh2b

/-- info: 'Spike.Lib.A64.WakePh.instOk2bP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.instOk2bP
