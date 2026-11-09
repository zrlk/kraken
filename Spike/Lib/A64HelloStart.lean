/-
**hello.w's `scc_rt_start` at `phH`** (AArch64): the
twin of `Spike/Lib/A64WakeStart.lean` at hello.w's listing
(`SccCode.helloProg`) and its extended phase `phH`
(`Spike/Lib/A64HelloPh.lean`), with the owned words `ownH` (the thread
counter at `a`) and the canonical take's phase (bit `3` of `phH`), for a
layout of helloProg at the canonical base: `startEW_sfacts`
(`Spike/Lib/LowerA64/StartEW2.lean`) with the facts decided on helloProg's
labels (`decide +kernel` through `codeT`). The pcs of `scc_rt_start` and
its callees lie outside `helloR`, so `phH` is the canonical phase there and
the thread counter's word stays at `0` throughout.

The program-independent parts are wake's (`WakePh.pinTab`,
`WakePh.startTabW`, `WakePh.pin_memW`, `WakePh.WSep`,
`WakePh.tcb_not_ownW`); hello.w's take site is at `2165980` and its release
site at `2166036` (wake.w's `2165944`, `2166000`).

- `startFactsH`, `startH_fact`: the start's, the callees' and A6's pinned
  facts, decided at `phC`.
- `hello_rtCodeIn0`: the start's code checks of helloProg.
- `ph_pinH`, `noTk_pinH`, `noTk_phH`: a pin's phase at `phH`; no take at a
  pin (a pc) with bit `3` set.
- `siteH`: the take site at its label.
- `tcbPhH`, `tiPhH`, `takePhH`, `swPhH`: the callees' and the switch's phase
  facts at `phH`, `ownH`.
- `entryW_hello`, `startSpH`, `startEW_hello`: `_start`'s block, the start
  up to the switch, and `StartEW`.
-/
import Spike.Lib.A64HelloPh
import Spike.Lib.A64WakeStart

namespace Spike.Lib.A64.HelloPh

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk blockAt)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (TN TK TI TcbG TiG TakeG TcbW TiW TakeW StackM pinA pnA lockA freeNA nextA stacksA)
open Spike.Lib.A64.Rt (InstOk RuntimeLayout StartEW)
open Spike.Lib.A64.Rt.PhOfTab
open Spike.Lib.A64.WakePh (startTabW pin_memW WSep tcb_not_ownW ownW)

/-! ## The facts -/

/-- **The start's facts hold** at `phC`. -/
theorem startFactsH : startTabW.all (factOk (codeT lo SccCode.helloProg) okC phC) = true := by
  decide +kernel

theorem startH_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ startTabW) : factOk (codeOf lo SccCode.helloProg) (okPcOf lo SccCode.helloProg Λ) phH f = true := by
  have := List.all_eq_true.mp startFactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

/-- **The start's code checks** of SccCode.helloProg. -/
theorem hello_rtCodeIn0 : Spike.Lib.A64.Rt.RtCodeIn0 SccCode.helloProg :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

/-- **A pin's phase index** at `phH`. -/
theorem ph_pinH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hm : (l, k, v) ∈ Scc.Cert.Rt.A64.phPins) : phH (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = v :=
  ph_of_factOk hlab (startH_fact (Λ := Λ) hΛ (pin_memW hm))

/-- **No take at a pin with bit `3` set.** -/
theorem noTk_pinH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hm : (l, k, v) ∈ Scc.Cert.Rt.A64.phPins) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = (lab l + Int64.ofNat (4 * k)).toBitVec.toNat → ¬ phH (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, ph_pinH hΛ hlab hm] at hT
  omega

/-- **No take at a pc of a phase with bit `3` set.** -/
theorem noTk_phH {p : Int64} {v : Nat} (hp : phH p.toBitVec.toNat = v) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ phH (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, hp] at hT
  omega

/-! ## The words -/

/-- **The take site at its label.** -/
theorem siteH {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have hsite : (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat = 2165980 :=
    pcAt0_eq hlab (by unfold Scc.Cert.Rt.A64.pcAt; rw [← codeT_eq]; decide +kernel)
  show codeOf L.Λ.code.lo L.prog "scc_rt_take_site" = _
  rw [hp, hlo, hsite, ← codeT_eq]; decide +kernel

/-! ## The callees' phase facts -/

section Tcb

open Spike.Lib.A64.Rt.Tcb (TcbPh tcbDead tcbPcs siPcs)
open Spike.Lib.A64.Flow.Ret0.AllocTcb

/-- **`scc_rt_alloc_tcb`'s phase facts at `phH`** with `ownH`, returning to
`.sp2`, the header at `scc_rt_pinned`. -/
theorem tcbPhH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {a : BitVec 64}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a) :
    TcbPh (okPcOf lo SccCode.helloProg Λ) phH (fun s => phH (pcOf s) / 8 % 2 = 0) (ownH L a) L.lab
      (fun _ => L.lab Spike.Lib.A64.Flow.Ret0.sp2L) 0#64 := by
  have hf : ∀ f ∈ Spike.Lib.A64.Rt.tcbPhTab, _ := fun f hf => startH_fact hΛ (f := f) (by simp [startTabW, hf])
  have hl := hlab
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r →
      L.lab Spike.Lib.A64.Flow.Ret0.sp2L = L.lab r := fun _ h => nomatch h
  have hpn : Spike.Lib.A64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.A64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have h13 := ph_pinH hΛ hlab (l := lenL) (k := 37) (v := 13) (by decide)
  have h12 := ph_pinH hΛ hlab (l := lenL) (k := 38) (v := 12) (by decide)
  exact {
    e := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.fnL 0 Rt.Code.Tcb.atPro none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    entry := blkPh_of_factOk hl hr
      (fun t ht => by
        simp only [Scc.Cert.Rt.A64.deadN] at ht
        split at ht
        · next d hd =>
          simp only [tcbDead, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht ⊢
          rw [pcAt0_eq hl hd]; exact ht
        · cases ht)
      (hf (.blk Rt.Code.Tcb.entryL 0 Rt.Code.Tcb.atChk none (some ".L3_scc_rt_alloc_tcb.2_full"))
        (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    j1 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.entryL 4 Rt.Code.Tcb.atJ1 none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    len := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 0 Rt.Code.Tcb.atLen none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    arg := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 34 Rt.Code.Tcb.atArg none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    bnd := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 38 Rt.Code.Tcb.atBnd none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    j2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 48 Rt.Code.Tcb.atJ2 none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    ok2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.okL 2 Rt.Code.Tcb.atOk none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    ret := blkPh_of_factOk hl (fun _ h => by cases h; rfl) hn
      (hf (.blk Rt.Code.Tcb.okL 30 Rt.Code.Tcb.atRet (some Rt.Code.Start.sp2L) none)
        (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    fullNe := by
      have := ne_of_factOk hl (hf (.ne Rt.Code.Tcb.entryL 4 ".L3_scc_rt_alloc_tcb.2_full" 0)
        (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      rw [Spike.Lib.A64.Flow.ofNat4_zero] at this
      exact this
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.lenL 32) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.lenL 33) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.okL 0) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.okL 1) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.okL 29) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    rmwOk := ok_of_factOk hl (hf (.ok Rt.Code.Tcb.lenL 37) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    noTk := by
      intro p hp
      simp only [tcbPcs, siPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact noTk_pinH hΛ hlab (l := fnL) (k := 0) (v := 13) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := entryL) (k := 0) (v := 13) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := entryL) (k := 4) (v := 13) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := lenL) (k := 0) (v := 13) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := lenL) (k := 34) (v := 13) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := lenL) (k := 37) (v := 13) (by decide) (by decide)
      · rw [rmwPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk_pinH hΛ hlab (l := lenL) (k := 38) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := lenL) (k := 38) (v := 12) (by decide) (by decide)
      · -- `.1_len` + 48 is not a pin (A6 pins the bound's branch at + 47): the table's `.ph` fact.
        have h48 : phH (L.lab lenL + Int64.ofNat (4 * 48)).toBitVec.toNat = 12 :=
          ph_of_factOk hl (hf (.ph Rt.Code.Tcb.lenL 48 12) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
        exact noTk_phH h48 (by decide)
      · exact noTk_pinH hΛ hlab (l := okL) (k := 2) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := okL) (k := 30) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := lenL) (k := 32) (v := 13) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := lenL) (k := 33) (v := 13) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := okL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := okL) (k := 1) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := okL) (k := 29) (v := 12) (by decide) (by decide)
    rmwIn := ⟨(0#64).setWidth 128, by rw [rmwPc, h13, hpn]; simp [ownH, ownW, Spike.Lib.A64.PhRec.ownOf]⟩
    rmwUpd := by
      rw [rmwPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', h13, h12, hpn]
      simp [Spike.Lib.A64.Rt.ownUpdB, ownH, ownW, Spike.Lib.A64.PhRec.ownOf, hs.pn_lock, hs.pn_freeN, hs.pn_next,
        hs.pn_a, Ne.symm hs.pn_lock, Ne.symm hs.pn_freeN, Ne.symm hs.pn_next, Ne.symm hs.pn_a]
      decide
    hdrNo := fun j w => by
      rw [hpin]
      exact tcb_not_ownW hs ⟨0, by decide, by simp⟩ j w }

end Tcb

section Ti

open Spike.Lib.A64.Rt.Ti (TiPh stPcs)
open Spike.Lib.A64.Flow.Ret0.ThreadInit

/-- **`scc_rt_thread_init`'s phase facts at `phH`**, returning to `.sp3`. -/
theorem tiPhH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    TiPh (okPcOf lo SccCode.helloProg Λ) phH (fun s => phH (pcOf s) / 8 % 2 = 0) L.lab
      (fun _ => L.lab Spike.Lib.A64.Flow.Ret0.sp3L) := by
  have hf : ∀ f ∈ Spike.Lib.A64.Rt.tiPhTab, _ := fun f hf => startH_fact hΛ (f := f) (by simp [startTabW, hf])
  have hl := hlab
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r →
      L.lab Spike.Lib.A64.Flow.Ret0.sp3L = L.lab r := fun _ h => nomatch h
  exact {
    e := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Ti.fnL 0 Rt.Code.Ti.tiPro none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    entry := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Ti.entryL 0 Rt.Code.Ti.tiCall none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    sp := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Ti.spL 0 Rt.Code.Ti.tiSp none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f1 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Ti.spL 12 Rt.Code.Ti.tiF1 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Ti.spL 15 Rt.Code.Ti.tiF2 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f3 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Ti.spL 18 Rt.Code.Ti.tiF3 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f4 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Ti.spL 21 Rt.Code.Ti.tiF4 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f5 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Ti.spL 24 Rt.Code.Ti.tiF5 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    ret := blkPh_of_factOk hl (fun _ h => by cases h; rfl) hn
      (hf (.blk Rt.Code.Ti.spL 27 Rt.Code.Ti.tiRet (some Rt.Code.Start.sp3L) none) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    st := by
      intro p hp
      simp only [stPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hl (hf (.step Rt.Code.Ti.spL 11) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Ti.spL 14) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Ti.spL 17) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Ti.spL 20) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Ti.spL 23) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Ti.spL 26) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    noTk := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact noTk_phH (ph_of_factOk hl (hf (.ph Rt.Code.Ti.fnL 0 12) (by simp [Spike.Lib.A64.Rt.tiPhTab])))
          (by decide)
      · exact noTk_phH (ph_of_factOk hl (hf (.ph Rt.Code.Ti.entryL 0 12) (by simp [Spike.Lib.A64.Rt.tiPhTab])))
          (by decide) }

end Ti

section Take

open Spike.Lib.A64.Rt.Take (TakePh takePcs siPcs)
open Spike.Lib.A64.Flow.Ret0.StackTake

/-- **`scc_rt_stack_take`'s phase facts at `phH`** with `ownH`, returning
to `scc_rt_thread_init`'s `.sp0`. -/
theorem takePhH {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {a : BitVec 64}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a) :
    TakePh (okPcOf lo SccCode.helloProg L.Λ) phH (fun s => phH (pcOf s) / 8 % 2 = 0) (ownH L a)
      (Spike.Lib.A64.PhRec.μ L) L.lab (fun _ => L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL) := by
  have hf : ∀ f ∈ Spike.Lib.A64.Rt.takePhTab, _ := fun f hf => startH_fact hΛ (f := f) (by simp [startTabW, hf])
  have hl := hlab
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r →
      L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL = L.lab r := fun _ h => nomatch h
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hnx : Spike.Lib.A64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  have c1 := hs.pn_next
  have c2 := hs.pn_lock
  have c3 := hs.pn_freeN
  have c4 := hs.next_lock
  have c5 := hs.next_freeN
  have c6 := hs.lock_freeN
  have c7 := hs.lock_a
  have c8 := hs.next_a
  have hsite : (L.lab siteL).toBitVec.toNat = 2165980 :=
    pcAt0_eq hlab (by unfold Scc.Cert.Rt.A64.pcAt; rw [← codeT_eq]; decide +kernel)
  have hs12 := ph_pinH hΛ hlab (l := spinL) (k := 2) (v := 12) (by decide)
  have hs14 := ph_pinH hΛ hlab (l := spinL) (k := 3) (v := 14) (by decide)
  have hb14 := ph_pinH hΛ hlab (l := bumpL) (k := 5) (v := 14) (by decide)
  have hb12 := ph_pinH hΛ hlab (l := bumpL) (k := 6) (v := 12) (by decide)
  have hn12 := ph_pinH hΛ hlab (l := bumpL) (k := 11) (v := 12) (by decide)
  have hn8 := ph_pinH hΛ hlab (l := bumpL) (k := 12) (v := 8) (by decide)
  have ht8 : phH (L.lab siteL).toBitVec.toNat = 8 := by
    have := ph_pinH hΛ hlab (l := siteL) (k := 0) (v := 8) (by decide)
    rwa [Spike.Lib.A64.Flow.ofNat4_zero] at this
  have ht0 : phH (L.lab siteL + Int64.ofNat 4).toBitVec.toNat = 0 := by
    have := ph_pinH hΛ hlab (l := siteL) (k := 1) (v := 0) (by decide)
    rwa [show Int64.ofNat (4 * 1) = Int64.ofNat 4 from rfl] at this
  exact {
    e := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.fnL 0 Rt.Code.Take.stPro none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    entry := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.entryL 0 Rt.Code.Take.stInit none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    cls := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.clsL 0 Rt.Code.Take.stCls none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    j1 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.clsL 4 Rt.Code.Take.stJ1 none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    d2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.doneL 2 Rt.Code.Take.stFreeN none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    d9 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.doneL 9 Rt.Code.Take.stFree none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    d16 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.doneL 16 Rt.Code.Take.stLock none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    sp0 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.spinL 0 Rt.Code.Take.stSwp none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    sp3 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.spinL 3 Rt.Code.Take.stSpin none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    lk0 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.lockedL 0 Rt.Code.Take.stLdN none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    lk2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.lockedL 2 Rt.Code.Take.stEmpty none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    b2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.bumpL 2 Rt.Code.Take.stUnl none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    b8 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.bumpL 8 Rt.Code.Take.stAdd none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    b12 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.bumpL 12 Rt.Code.Take.stBnd none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    b21 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.bumpL 21 Rt.Code.Take.stJ2 none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    ok2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.okL 2 Rt.Code.Take.stOk none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    tk := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Take.takenL 0 Rt.Code.Take.stSite none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    ret := blkPh_of_factOk hl (fun _ h => by cases h; rfl) hn
      (hf (.blk Rt.Code.Take.siteL 1 Rt.Code.Take.stRet (some Rt.Code.Ti.spL) none)
        (by simp [Spike.Lib.A64.Rt.takePhTab]))
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.doneL 0) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.doneL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.doneL 7) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.doneL 8) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.doneL 14) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.doneL 15) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.bumpL 0) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.bumpL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.bumpL 6) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.bumpL 7) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.okL 0) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Take.okL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))
    swpOk := ok_of_factOk hl (hf (.ok Rt.Code.Take.spinL 2) (by simp [Spike.Lib.A64.Rt.takePhTab]))
    ldnOk := (step_of_factOk hl (hf (.step Rt.Code.Take.lockedL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))).1
    unlOk := ok_of_factOk hl (hf (.ok Rt.Code.Take.bumpL 5) (by simp [Spike.Lib.A64.Rt.takePhTab]))
    nxtOk := ok_of_factOk hl (hf (.ok Rt.Code.Take.bumpL 11) (by simp [Spike.Lib.A64.Rt.takePhTab]))
    ldnPh := (step_of_factOk hl (hf (.step Rt.Code.Take.lockedL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))).2
    noTk := by
      intro p hp
      simp only [takePcs, siPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact noTk_pinH hΛ hlab (l := fnL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := entryL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := clsL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := clsL) (k := 4) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := doneL) (k := 2) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := doneL) (k := 9) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := doneL) (k := 16) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := spinL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := spinL) (k := 2) (v := 12) (by decide) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk_pinH hΛ hlab (l := spinL) (k := 3) (v := 14) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := spinL) (k := 3) (v := 14) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := lockedL) (k := 0) (v := 14) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := lockedL) (k := 1) (v := 14) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := lockedL) (k := 2) (v := 14) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 2) (v := 14) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 5) (v := 14) (by decide) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk_pinH hΛ hlab (l := bumpL) (k := 6) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 8) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 11) (v := 12) (by decide) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk_pinH hΛ hlab (l := bumpL) (k := 12) (v := 8) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 12) (v := 8) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 21) (v := 8) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := okL) (k := 2) (v := 8) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := takenL) (k := 0) (v := 8) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := siteL) (k := 0) (v := 8) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := doneL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := doneL) (k := 1) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := doneL) (k := 7) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := doneL) (k := 8) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := doneL) (k := 14) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := doneL) (k := 15) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 0) (v := 14) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 1) (v := 14) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 6) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := bumpL) (k := 7) (v := 12) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := okL) (k := 0) (v := 8) (by decide) (by decide)
      · exact noTk_pinH hΛ hlab (l := okL) (k := 1) (v := 8) (by decide) (by decide)
    swpIn := ⟨(0#64).setWidth 128, by rw [swpPc, hs12, hlk]; simp [ownH, ownW, Spike.Lib.A64.PhRec.ownOf]⟩
    swpUpd := by
      rw [swpPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hs12, hs14, hlk]
      simp [Spike.Lib.A64.Rt.ownUpdB, ownH, ownW, Spike.Lib.A64.PhRec.ownOf, c1, c2, c3, c4, c5, c6, c7, c8,
        Ne.symm c1, Ne.symm c2, Ne.symm c3, Ne.symm c4, Ne.symm c5, Ne.symm c6, Ne.symm c7, Ne.symm c8]
    unlIn := ⟨(1#64).setWidth 128, by rw [unlPc, hb14, hlk]; simp [ownH, ownW, Spike.Lib.A64.PhRec.ownOf]⟩
    unlUpd := by
      rw [unlPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hb14, hb12, hlk]
      simp [Spike.Lib.A64.Rt.ownUpdB, ownH, ownW, Spike.Lib.A64.PhRec.ownOf, c1, c2, c3, c4, c5, c6, c7, c8,
        Ne.symm c1, Ne.symm c2, Ne.symm c3, Ne.symm c4, Ne.symm c5, Ne.symm c6, Ne.symm c7, Ne.symm c8]
    nxtIn := ⟨(0#64).setWidth 128, by rw [nextPc, hn12, hnx]; simp [ownH, ownW, Spike.Lib.A64.PhRec.ownOf]⟩
    nxtUpd := by
      rw [nextPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hn12, hn8, hnx]
      simp [Spike.Lib.A64.Rt.ownUpdB, ownH, ownW, Spike.Lib.A64.PhRec.ownOf, c1, c2, c3, c4, c5, c6, c7, c8,
        Ne.symm c1, Ne.symm c2, Ne.symm c3, Ne.symm c4, Ne.symm c5, Ne.symm c6, Ne.symm c7, Ne.symm c8]
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
    siteAt := siteH hp hlo hlab
    siteOwn := by rw [ht8, ht0]; rfl
    tk4 := fun s hs => by show phH (pcOf s) / 8 % 2 = 0; rw [hs, ht0] }

end Take

/-- **The switch's phase facts at `phH`.** -/
theorem swPhH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) :
    Spike.Lib.A64.Rt.MainU.SwPh (okPcOf lo SccCode.helloProg Λ) phH lab where
  sw := step_of_factOk hlab
    (startH_fact hΛ (f := .step Spike.Lib.A64.Rt.Code.Start.sp3L 5) (by simp [startTabW, Spike.Lib.A64.Rt.swPhTab]))
  main := blkPh_of_factOk (ra := none) (dead := none) hlab (fun _ h => nomatch h)
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h)
    (startH_fact hΛ (f := .blk Spike.Lib.A64.Rt.Code.Start.sp3L 6 Spike.Lib.A64.Rt.Code.Start.startMain none none)
      (by simp [startTabW, Spike.Lib.A64.Rt.swPhTab]))


/-! ## The start -/

section Start

open Spike.Lib.A64.Rt Spike.Lib.A64.Rt.StartU

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {lbl : Lbl}

/-- The instance at `phH` with `ownH` and the canonical take's phase. -/
theorem instOkHS (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s)))
      (fun s => phH (pcOf s) / 8 % 2 = 0) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo SccCode.helloProg L.Λ) phH L.pfx :=
  instOkH hp hlo a (fun i => i / 8 % 2 = 0) (siteH hp hlo hlab)

/-- **`_start`'s block inside `SFacts … Dt`** at `phH`
(`entryW_ofPlaceOK`). -/
theorem entryW_hello (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {Dt : State → Prop} {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo0 : R.lo ≤ 0) (hhi : 0 ≤ R.hi) {c0 : Ctl}
    (hC0 : CFacts L.Λ lbl c0) :
    BlkW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
        (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c Dt) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc
      R F (Ret0.entryN L.lab c0) Ret0.entryB := by
  have hrc : RtCodeIn0 L.prog := hp ▸ hello_rtCodeIn0
  have hb := blkPh_of_factOk hlab (l := "_start") (k := 0) (b := Rt.Code.Start.entryB) (ra := none)
    (dead := none) (rapc := 0) (dset := fun _ => false) (fun _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h)
    (startH_fact hΛ (f := .blk "_start" 0 Rt.Code.Start.entryB none none) (by simp [startTabW, startPhTab]))
  have hp0 := ph_of_factOk hlab (startH_fact hΛ (f := .ph "_start" 0 13) (by simp [startTabW, startPhTab]))
  have hW := blkW_pre (instOkHS (a := a) (rS := rS) hp hlo hlab) (lbl := lbl)
    (F := F) (rS := rS) (n := Ret0.entryN L.lab c0) (l := "_start") (k := 0) (dead := fun _ => false) (ra := 0)
    hrc.entry (ofNat4_zero _) Ret0.entryB_ok hR hal hlo0 hhi
    (fun _ _ hJ => hJ ▸ hC0) hb (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim)
    (fun _ _ _ => rfl) (noTk_phH hp0 (by decide))
  intro s σ c he hn hd hpc hA hF hJn k hk m hA' hD
  obtain ⟨h1, h2⟩ := hW s σ c he hn hd hpc hA hF hJn k hk m hA' hD
  exact ⟨h1.dt_mono fun _ h => h.elim, h2⟩

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_start`'s states up to the switch are inside `SFacts … Dt`**
at `phH` with `ownH` (`Sp0W`, `Sp2W`; `startSp_gen`), the words separated
(`hs`) and `.rodata` off the pool (`hro`). -/
theorem startSpH (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    {Dt : State → Prop} {c0 : Ctl} {R : Region} {F : MachineData → Prop} {n0 k0 : BitVec 64}
    (hC0 : CFacts L.Λ lbl c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → rtF L m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : FStable R (StackM rS)) (hSMi : FStable (R.callee Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Abort.oI.sp (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0) (StackM rS)) :
    Ret0.Sp0W (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
        (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c Dt) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F n0 c0 ∧
      Ret0.Sp2W (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
        (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c Dt) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F rS n0 k0
        c0 := by
  subst hn0
  have hI := instOkHS (a := a) (rS := rS) hp hlo hlab
  have hrc : RtCodeIn0 L.prog := hp ▸ hello_rtCodeIn0
  have hl := hlab
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startH_fact hΛ (f := f) (by simp [startTabW, hf])
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = L.lab r := fun _ h => nomatch h
  have hW : ∀ s c, SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
      (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c →
      SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
        (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c Dt :=
    fun _ _ hs => hs.dt_mono fun _ h => h.elim
  have hpn : pnA L.lab = L.pnA := L.lab_pn
  have hpin : pinA L.lab = L.pinA := L.lab_pin
  have hlk : lockA L.lab = L.lockA := L.lab_lock
  have hfr : freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : nextA L.lab = L.nextA := L.lab_next
  have h0 : ∃ j < 7, L.pinA + 0#64 = L.pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hst := hrc.start
  simp only [startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨⟨-, cb0⟩, cb1⟩, cb2⟩, cb3⟩, cb4⟩ := hst
  have hcl := hrc.call
  simp only [Ret0.startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  have htl := hrc.tail
  simp only [Ret0.startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨t0, -⟩, t2⟩, t3⟩, -⟩, -⟩ := htl
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun g hg j => ?_⟩, ⟨?_, fun g hg j => ?_, ?_, ?_⟩⟩
  · -- The frame's setup.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cb0 (ofNat4_zero _) Abort.b0_ok hR hal
      (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk "scc_rt_start" 0 Abort.b0 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false b0_noRet k hk r hr).elim) (fun _ _ _ => rfl)
      (noTk_phH (ph_of_factOk hl (hf (.ph "scc_rt_start" 0 13) (by simp [startPhTab]))) (by decide)))
  · -- The `adrp`.
    have hs := step_of_factOk hl (hf (.step startE 0) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_si_pre (si := SI.adrp .X9 sigign) (p := L.lab startE + Int64.ofNat (4 * 0))
      hI cb1 rfl (ofNat4_zero _).symm (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_phH (ph_of_factOk hl (hf (.ph startE 0 13) (by simp [startPhTab]))) (by decide)) hs.2)
  · -- The `add`.
    have hs := step_of_factOk hl (hf (.step startE 1) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_si_pre (si := SI.addLo12 .X9 .X9 sigign)
      (p := L.lab startE + Int64.ofNat (4 * 1)) hI cb2 rfl rfl (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_phH (ph_of_factOk hl (hf (.ph startE 1 13) (by simp [startPhTab]))) (by decide)) hs.2)
  · -- The arguments.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cb3
      (startE2 L.lab).symm
      startArgs_ok hR hal (by omega) (by omega)
      (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 2 startArgs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false startArgs_noRet k hk r hr).elim) (fun _ _ _ => rfl)
      (noTk_phH (ph_of_factOk hl (hf (.ph startE 2 13) (by simp [startPhTab]))) (by decide)))
  · -- The system call.
    have hs := step_of_factOk hl (hf (.step startE 8) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_svc_pre (p := L.lab startE + Int64.ofNat (4 * 8)) hI cb4 rfl
      (startE8 L.lab)
      (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_phH (ph_of_factOk hl (hf (.ph startE 8 13) (by simp [startPhTab]))) (by decide)) hs.2
      (fun _ _ ⟨_, _, he⟩ => by rw [he, startS2_x8]; decide))
  · -- The call block.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cc rfl Ret0.startCall_ok hR hal
      (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 9 Rt.Code.Start.startCall none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false startCall_noRet k hk r hr).elim) (fun _ _ _ => rfl)
      (noTk_phH (ph_of_factOk hl (hf (.ph startE 9 13) (by simp [startPhTab]))) (by decide)))
  · -- `scc_rt_alloc_tcb`.
    obtain ⟨hR', hal'⟩ := callee_facts (kc := Abort.oI.sp) (lo' := -192) hR hal
      (by show R.lo ≤ -48 + -192; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
    exact tcbW_wmono hW (tcbW_gen hI (fun _ => rfl) hrc.tcb hC0 hR' hal' (by show (-192 : Int) ≤ -192; omega)
      (by show (0 : Int) ≤ 0; omega) ⟨g, 0#64, c0⟩ rfl hg (tcbPhH hΛ hlab hs)
      (by rw [hpn]; exact (L.words_mapped _ L.pn_mem).1)
      (by rw [hpin]; exact Spike.Lib.A64.PhRec.mapped_tcb h0)
      (fun m hm => by rw [hpn]; exact Spike.Lib.A64.PhRec.rtF_pn (hFr m hm))
      (fun m hm => by rw [hpin]; exact Spike.Lib.A64.PhRec.rtF_tcb (hFr m hm) h0) j)
  · -- `.sp2`'s block.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI t0 (ofNat4_zero _) Ret0.startCall2_ok
      hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn
        (hf (.blk Rt.Code.Start.sp2L 0 Rt.Code.Start.startCall2 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false startCall2_noRet k hk r hr).elim) (fun _ _ _ => rfl)
      (noTk_phH (ph_of_factOk hl (hf (.ph Rt.Code.Start.sp2L 0 12) (by simp [startPhTab]))) (by decide)))
  · -- `scc_rt_thread_init`.
    obtain ⟨hR', hal'⟩ := callee_facts (kc := Abort.oI.sp) (lo' := -256) hR hal
      (by show R.lo ≤ -48 + -256; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
    exact tiW_wmono hW (tiW_gen hI (fun _ => rfl) hrc.ti hC0 hR' hal' (by show (-256 : Int) ≤ -256; omega)
      (by show (0 : Int) ≤ 0; omega) ⟨g, pinA L.lab + 0#64 + 8#64, k0, c0⟩ rfl hg (tiPhH hΛ hlab)
      (fun _ ha => Spike.Lib.A64.PhRec.mapped_tcb (tcb_fld ha))
      (fun _ ha m hm => Spike.Lib.A64.PhRec.rtF_tcb (hFr m hm) (tcb_fld ha))
      (fun _ ha => tcb_not_ownW hs (tcb_fld ha))
      hsub hSMi hSMt hrc.take (takePhH hp hlo hΛ hlab hs)
      (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
      (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
      (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
      (fun m hm => by rw [hlk]; exact Spike.Lib.A64.PhRec.rtF_lock (hFr m hm))
      (fun m hm => by rw [hfr]; exact Spike.Lib.A64.PhRec.rtF_freeN (hFr m hm))
      (fun m hm => by rw [hnx]; exact Spike.Lib.A64.PhRec.rtF_next (hFr m hm))
      hrS hro j)
  · -- `.sp3`'s block.
    exact blkW_wmono hW (blkW_post (dead := fun _ => false) (ra := 0) hI t2 (ofNat4_zero _) Ret0.startSw0_ok
      hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn
        (hf (.blk Rt.Code.Start.sp3L 0 Rt.Code.Start.startSw0 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r hr => (noRet_false startSw0_noRet k hk r hr).elim) (fun _ _ _ => rfl) hsub hSM)
  · -- The `msr`.
    have hs := step_of_factOk hl (hf (.step Rt.Code.Start.sp3L 4) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_si_post (si := SI.msr .X10) (p := L.lab Ret0.sp3L + Int64.ofNat (4 * 4))
      hI t3 rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0) hs.1 hs.2 hsub)

/-- **`scc_rt_start`'s states are inside `SFacts`** (`StartEW`, from
`_start` to `bl scc_rt_main`) at `phH` with `ownH` (`startEW_sfacts`): the
start up to the switch (`startSpH`), `_start`'s block (`entryW_hello`) and
the switch (`swEW_gen`, `swPhH`). -/
theorem startEW_hello (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    {c0 : Ctl} {R : Region} {F : MachineData → Prop} {n0 k0 : BitVec 64} {D : Int}
    (hC0 : CFacts L.Λ lbl c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → rtF L m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : FStable R (StackM rS)) (hSMi : FStable (R.callee Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Abort.oI.sp (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0) (StackM rS))
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (h16 : (stacksA L.lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA L.lab + k0 + 16384#64) (-D) 0).OK) (hL8 : D % 8 = 0) :
    StartEW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
        (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F rS n0 k0
      c0 D := by
  have hI := instOkHS (a := a) (rS := rS) hp hlo hlab
  have hsp := startSpH hp hlo hΛ hlab hs hro hC0 hR hal hlo' hhi hFr hn0 hrS hsub hSM hSMi hSMt
    (Dt := fun _ => False)
  refine ⟨entryW_hello hp hlo hΛ hlab hR hal (by omega) hhi hC0, hsp.1, hsp.2, ?_⟩
  exact Spike.Lib.LowerA64.swEW_gen hI (hp ▸ hello_rtCodeIn0 : RtCodeIn0 L.prog).tail hC0 (swPhH hΛ hlab)
    (by rw [hI.labOk]; exact h16) (by rw [hI.labOk]; exact hok) hL8 hsub hfit

end Start

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.startH_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.startH_fact

/-- info: 'Spike.Lib.A64.HelloPh.hello_rtCodeIn0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.hello_rtCodeIn0

/-- info: 'Spike.Lib.A64.HelloPh.tcbPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.tcbPhH

/-- info: 'Spike.Lib.A64.HelloPh.tiPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.tiPhH

/-- info: 'Spike.Lib.A64.HelloPh.takePhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.takePhH

/-- info: 'Spike.Lib.A64.HelloPh.swPhH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.swPhH

/-- info: 'Spike.Lib.A64.HelloPh.entryW_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.entryW_hello

/-- info: 'Spike.Lib.A64.HelloPh.startSpH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.startSpH

/-- info: 'Spike.Lib.A64.HelloPh.startEW_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.startEW_hello

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-! ## The values at `wc_main`'s spawn

The assumptions `n0 = 80` (the pinned bump's offset at `scc_rt_alloc_tcb`'s
second call, `HelloWc.tcb2QH`) and `k0 = 16384` (the stack bump's at
`scc_rt_thread_init`'s, `hti`) are the values `ownH` gives at `wc_main`'s
`.sp3`, `.sp4` and `.sp6` (phase `16`: bits `0` and `2` clear, after the
start's first TCB of header `3331`, of length `112`, and its first stack of
`16384`). The discharge of `hti`/`htcb` at helloProg (the `Tcb2W`/`Ti2`
chain) is elsewhere. -/

/-- **The start's first TCB is `112` bytes** (header `3331`, `scc_rt_start`). -/
theorem lenOf_start : Spike.Lib.A64.Flow.Ret0.AllocTcb.lenOf 3331#64 =
    Spike.Lib.A64.Flow.Ret0.AllocTcb.tcbLen := by decide

/-- `wc_main`'s spawn points at helloProg and their phase `16`. -/
theorem spawn_ph : codeOf lo SccCode.helloProg ".L22_wc_main.sp3" = some 2169728 ∧
    codeOf lo SccCode.helloProg ".L22_wc_main.sp4" = some 2169748 ∧
    codeOf lo SccCode.helloProg ".L22_wc_main.sp6" = some 2169772 ∧
    phC 2169728 = 16 ∧ phC 2169748 = 16 ∧ phC 2169772 = 16 := by
  rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

/-- **The owned words at phase `16`**: `scc_rt_pinned_next` at `80`
(`tcb2QH`'s `n0`), the lock free, no free stacks, `scc_rt_stack_next` at
`16384` (`hti`'s `k0`) and one thread reserved. -/
theorem ownH_16 (L : RuntimeLayout) (a : BitVec 64) :
    ownH L a 16 = [(⟨L.pnA, 8⟩, (112#64).setWidth 128), (⟨L.lockA, 8⟩, (0#64).setWidth 128),
      (⟨L.freeNA, 8⟩, (0#64).setWidth 128), (⟨L.nextA, 8⟩, (16384#64).setWidth 128),
      (⟨a, 8⟩, (1#64).setWidth 128)] := by
  simp [ownH, Spike.Lib.A64.WakePh.ownW, Spike.Lib.A64.PhRec.ownOf]

/-- **At `wc_main`'s spawn points** the owned words are `ownH_16`'s. -/
theorem ownH_spawn (L : RuntimeLayout) (a : BitVec 64) {p : Nat} (hp : p = 2169728 ∨ p = 2169748 ∨ p = 2169772) :
    ownH L a (phH p) = ownH L a 16 := by
  obtain ⟨-, -, -, h3, h4, h6⟩ := spawn_ph
  rw [phH_eq]; rcases hp with rfl | rfl | rfl <;> simp only [h3, h4, h6]

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.lenOf_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.lenOf_start

/-- info: 'Spike.Lib.A64.HelloPh.spawn_ph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.spawn_ph

/-- info: 'Spike.Lib.A64.HelloPh.ownH_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ownH_spawn
