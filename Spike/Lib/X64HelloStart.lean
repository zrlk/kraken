/-
**hello.w's `scc_rt_start` at `phH`** (x86-64; the twin of `Spike/Lib/A64HelloStart.lean`'s live part): the
runtime's start from `_start` to `call scc_rt_main` inside `SFacts` at hello.w's extended phase `phH`
(`Spike/Lib/X64HelloPh.lean`) with the owned words `ownH` (the thread counter at `a`) and the canonical take's
phase (bit `3` of `phH`), for a layout of helloCells at the linked base: `X64WakeStartEWF`/`X64WakeStartPhW`/
`X64WakeStartEW` restated at helloCells, the facts decided on helloCells' labels (`decide +kernel` through
`codeT`). The pcs of `scc_rt_start` and its callees lie outside `helloR`, so `phH` is the canonical phase there
and the thread counter's word stays at `0` throughout.

The program-independent parts are wake's (`WakePh.startTabW`, `WakePh.takeWTab`, `WakePh.WSep`,
`WakePh.tcb_not_ownW`, the membership lemmas); hello.w's take site is at `4200314` and its release site at
`4200354` (wake.w's `4200277`, `4200317`).

- `startFactsH`, `startH_fact`: the start's, `scc_rt_alloc_tcb`'s and the switch's facts, decided at `phC`.
- `hello_rtCodeIn0`, `hello_tiIn`, `hello_rtCodeInTi`: the start's code checks of helloCells
  (`scc_rt_thread_init` returning to `.x8`).
- `ph_tcbH`, `noTk_tcbH`, `noTk_phH`: a pin's phase at `phH`; no take at a pc with bit `3` set.
- `siteH`: the take site at its label.
- `tcbPhH`, `swPhH`: `scc_rt_alloc_tcb`'s and the switch's phase facts at `phH`, `ownH`.
- `tiTabH`, `tiFactsH`, `take_factH`, `ti_factH`, `noTkH`, `tiPhH`, `ph_rowTH`, `noTk_rowTH`, `takePhH`: the
  first `scc_rt_thread_init` call's (`TiPhAt` at `.x8`, returning to `.x1`) and its `scc_rt_stack_take`'s
  (returning to `.x8`) phase facts.
- `instOkHS`, `entryW_hello`, `startSpH`, `startEW_hello`: the instance, `_start`'s nodes, the start up to the
  switch, and `StartEW` (return point `.x8`).

## Differences from the AArch64 version

- The x86-64 facts are wake's x86-64 tables (no `phPins`: the pins are `tcbTkRows`' and `takeTkRows`' rows), so
  `ph_pinH`/`noTk_pinH` become `ph_tcbH`/`noTk_tcbH`, and `scc_rt_thread_init`'s/`scc_rt_stack_take`'s tables
  are separate (`tiTabH`; `WakePh.takeWTab`).
- hello's `scc_rt_main` has a setup block, so `scc_rt_thread_init`'s return point is `.x8` (wake: `.x7`):
  `tiPhH` is `TiPhAt … x8L`, `startSpH` gives `X0WAt … x8L` by `tiWAt_gen`, and `startEW_hello` is
  `StartEW … x8L`.
- The regions are x86-64's (`8 ≤ R.hi` for the callees, no 16-alignment, `hout` instead of `hSM`/`hSMi`/`hSMt`,
  the new stack's depth `8 ≤ D`), as `X64WakeStartEW`.
- `lenOf_start`, `spawn_ph`, `ownH_16`, `ownH_spawn` are not twinned: they are dead in hello.
-/
import Spike.Lib.X64HelloPh
import Spike.Lib.X64WakeStartEW

namespace Spike.Lib.X64.HelloPh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64Consumer
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (TN TK TI TcbG TiG TakeG TcbW TiW TakeW StackM pinA pnA lockA freeNA nextA stacksA
  St0W X0W x0L x1L startCall startCall2 startFs startSw startCall_ok startCall2_ok startFs_ok startSw_ok
  startCallIn startCall2In startTailIn stackM_stable)
open Spike.Lib.X64.Rt (InstOk RuntimeLayout ownUpdB StartEW X0WAt rtF tcbPhTab swPhTab startPhTab tcbTkRows
  tcbFullL takePhTab takeTkRows x8L)
open Spike.Lib.X64.Rt.PhOfTab
open Spike.Lib.X64.WakePh (startTabW tcb_memW sw_memW start_memW takeWTab WSep tcb_not_ownW)

set_option linter.unusedSimpArgs false

/-! ## The facts -/

/-- **The start's facts hold** at `phC`. -/
theorem startFactsH : startTabW.all (factOk (codeT lo helloCells) okC phC) = true := by
  decide +kernel

theorem startH_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ startTabW) : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH f = true := by
  have := List.all_eq_true.mp startFactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

/-- **The start's code checks** of helloCells. -/
theorem hello_rtCodeIn0 : Spike.Lib.X64.Rt.RtCodeIn0 helloCells :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- `scc_rt_thread_init`'s code check of helloCells, returning to `.x8`. -/
theorem hello_tiIn : Spike.Lib.X64.Flow.Ret0.ThreadInit.threadInitInAt helloCells x8L = true := by
  decide +kernel

/-- **The start's code checks with `scc_rt_thread_init`'s** at `.x8`. -/
theorem hello_rtCodeInTi : Spike.Lib.X64.Rt.RtCodeInTi helloCells x8L :=
  { hello_rtCodeIn0 with ti := hello_tiIn }

variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

/-- **A pin's phase index** at `phH` (a row of `tcbTkRows`). -/
theorem ph_tcbH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ tcbTkRows) : phH (lab l + Int64.ofNat k).toBitVec.toNat = v :=
  ph_of_factOk hlab (startH_fact (Λ := Λ) hΛ (List.mem_append_right _ (List.mem_map.mpr ⟨(l, k, v), hr, rfl⟩)))

/-- **No take at a pin with bit `3` set.** -/
theorem noTk_tcbH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ tcbTkRows) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = (lab l + Int64.ofNat k).toBitVec.toNat → ¬ phH (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, ph_tcbH hΛ hlab hr] at hT
  omega

/-- **No take at a pc of a phase with bit `3` set.** -/
theorem noTk_phH {p : Int64} {v : Nat} (hp : phH p.toBitVec.toNat = v) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ phH (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, hp] at hT
  omega

/-- **The take site at its label.** -/
theorem siteH {L : RuntimeLayout} (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have hsite : (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat = 4200314 :=
    pcAt0_eq hlab (by unfold Scc.Cert.Rt.X64.pcAt; rw [← codeT_eq]; decide +kernel)
  show codeLabel L.Λ.code.lo L.prog "scc_rt_take_site" = _
  rw [hp, hlo, hsite, ← codeT_eq]; decide +kernel

/-! ## The callees' phase facts -/

section Tcb

open Spike.Lib.X64.Rt.Tcb (TcbPh tcbDead tcbPcs blkPcs stepPcs)
open Spike.Lib.X64.Flow.Ret0.AllocTcb

/-- **`scc_rt_alloc_tcb`'s phase facts at `phH`** with `ownH`, returning to
`.x0`, the header at `scc_rt_pinned`. -/
theorem tcbPhH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {a : BitVec 64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a) :
    TcbPh (okPcOf lo helloCells Λ) phH (fun s => phH (pcOf s) / 8 % 2 = 0) (ownH L a) L.lab
      (fun _ => L.lab Rt.Code.Start.x0L) 0#64 := by
  have hf : ∀ f ∈ tcbPhTab, _ := fun f hf => startH_fact hΛ (f := f) (tcb_memW hf)
  have hl := hlab
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.X64.deadN (codeLabel lo helloCells) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      L.lab Rt.Code.Start.x0L = L.lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.X64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have h13 := ph_tcbH hΛ hlab (l := lenL) (k := 158) (v := 13) (by decide)
  have h12 := ph_tcbH hΛ hlab (l := lenL) (k := 163) (v := 12) (by decide)
  have e5 : rmwPc L.lab + Int64.ofNat 5 = L.lab lenL + Int64.ofNat 163 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 158 5).symm
  exact {
    e := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.fnL 0 Rt.Code.Tcb.atPro none none) (by simp [tcbPhTab]))
    entry := blkPh_of_factOk hl hr
      (fun t ht => by
        simp only [Scc.Cert.Rt.X64.deadN] at ht
        split at ht
        · next d hd =>
          simp only [tcbDead, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht ⊢
          exact ht.trans (pcAt0_eq hl hd).symm
        · cases ht)
      (hf (.blk Rt.Code.Tcb.entryL 0 Rt.Code.Tcb.atChk none (some tcbFullL)) (by simp [tcbPhTab]))
    j1 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.entryL 20 Rt.Code.Tcb.atJ1 none none) (by simp [tcbPhTab]))
    len := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 0 Rt.Code.Tcb.atL0 none none) (by simp [tcbPhTab]))
    l1 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 14 Rt.Code.Tcb.atL1 none none) (by simp [tcbPhTab]))
    l2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 32 Rt.Code.Tcb.atL2 none none) (by simp [tcbPhTab]))
    l3 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 50 Rt.Code.Tcb.atL3 none none) (by simp [tcbPhTab]))
    l4 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 68 Rt.Code.Tcb.atL4 none none) (by simp [tcbPhTab]))
    l5 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 99 Rt.Code.Tcb.atL5 none none) (by simp [tcbPhTab]))
    l6 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 135 Rt.Code.Tcb.atL6 none none) (by simp [tcbPhTab]))
    arg := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 146 Rt.Code.Tcb.atArg none none) (by simp [tcbPhTab]))
    bnd := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 163 Rt.Code.Tcb.atBnd none none) (by simp [tcbPhTab]))
    j2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.lenL 198 Rt.Code.Tcb.atJ2 none none) (by simp [tcbPhTab]))
    o1 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.okL 7 Rt.Code.Tcb.atO1 none none) (by simp [tcbPhTab]))
    o2 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.okL 38 Rt.Code.Tcb.atO2 none none) (by simp [tcbPhTab]))
    o3 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.okL 56 Rt.Code.Tcb.atO3 none none) (by simp [tcbPhTab]))
    o4 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.okL 77 Rt.Code.Tcb.atO4 none none) (by simp [tcbPhTab]))
    o5 := blkPh_of_factOk hl hr hn (hf (.blk Rt.Code.Tcb.okL 98 Rt.Code.Tcb.atO5 none none) (by simp [tcbPhTab]))
    ret := blkPh_of_factOk hl (fun _ _ h => by cases h; exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm) hn
      (hf (.blk Rt.Code.Tcb.okL 143 Rt.Code.Tcb.atRet (some (Rt.Code.Start.x0L, 0)) none) (by simp [tcbPhTab]))
    fullNe := by
      have := ne_of_factOk hl (hf (.ne Rt.Code.Tcb.entryL 20 tcbFullL 0) (by simp [tcbPhTab]))
      rw [Spike.Lib.X64.Flow.ofNat_zero'] at this
      exact this
    step := by
      intro pz hp
      simp only [stepPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.lenL 11 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.lenL 29 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.lenL 47 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.lenL 65 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.lenL 95 4) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.lenL 132 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.lenL 139 7) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.okL 0 7) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.okL 34 4) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.okL 53 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.okL 74 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.okL 95 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Rt.Code.Tcb.okL 140 3) (by simp [tcbPhTab]))
    rmwOk := ok_of_factOk hl (hf (.ok Rt.Code.Tcb.lenL 158) (by simp [tcbPhTab]))
    noTk := by
      intro p hp
      simp only [tcbPcs, blkPcs, stepPcs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbH hΛ hlab (v := 13) (by decide) (by decide)
      · rw [e5]; exact noTk_tcbH hΛ hlab (v := 12) (by decide) (by decide)
    rmwIn := ⟨(0#64).setWidth 128, by rw [h13, hpn]; simp [ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf]⟩
    rmwUpd := by
      rw [e5, h13, h12, hpn]
      simp [ownUpdB, ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf, hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a,
        Ne.symm hs.pn_lock, Ne.symm hs.pn_freeN, Ne.symm hs.pn_next, Ne.symm hs.pn_a]
    hdrNo := fun j w => by
      rw [hpin]
      exact tcb_not_ownW hs ⟨0, by decide, by simp⟩ j w }

end Tcb

/-- **The switch's phase facts at `phH`.** -/
theorem swPhH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) :
    Spike.Lib.X64.Rt.MainU.SwPh (okPcOf lo helloCells Λ) phH lab where
  sw := step_of_factOk hlab
    (startH_fact hΛ (f := .step Spike.Lib.X64.Rt.Code.Start.x1L 28 3) (sw_memW (by simp [swPhTab])))
  xor := step_of_factOk hlab
    (startH_fact hΛ (f := .step Spike.Lib.X64.Rt.Code.Start.x1L 31 2) (sw_memW (by simp [swPhTab])))
  main := blkPh_of_factOk (ra := none) (dead := none) hlab (fun _ _ h => nomatch h)
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h)
    (startH_fact hΛ (f := .blk Spike.Lib.X64.Rt.Code.Start.x1L 33 Spike.Lib.X64.Rt.Code.Start.startMain none none)
      (sw_memW (by simp [swPhTab])))

open Spike.Lib.X64.Rt.Code in
/-- **The first `scc_rt_thread_init` call's facts**: `tiPhTab` named from
`.x8`, returning to `scc_rt_start`'s `.x1`. -/
def tiTabH : List PhFact :=
  [.blk Ti.fnL 0 Ti.tiPro none none, .blk Ti.entryL 0 Ti.tiArg none none, .blk Ti.entryL 7 Ti.callBlk none none,
    .blk x8L 0 Ti.tiSp none none, .blk x8L 51 Ti.tiF1 none none, .blk x8L 63 Ti.tiZ none none,
    .blk x8L 78 Ti.tiZ none none, .blk x8L 93 Ti.tiF4 none none, .blk x8L 105 Ti.tiF5 none none,
    .blk x8L 117 Ti.tiRet (some (".Lscc_rt_start.x1", 0)) none,
    .step x8L 48 3, .step x8L 59 4, .step x8L 74 4, .step x8L 89 4, .step x8L 101 4,
    .step x8L 113 4,
    .ph Ti.fnL 0 12, .ph Ti.entryL 0 12, .ph Ti.entryL 7 12]

theorem takeFactsH : takeWTab.all (factOk (codeT lo helloCells) okC phC) = true := by
  decide +kernel

theorem tiFactsH : tiTabH.all (factOk (codeT lo helloCells) okC phC) = true := by
  decide +kernel

theorem take_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ takeWTab) : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH f = true := by
  have := List.all_eq_true.mp takeFactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

theorem ti_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ tiTabH) : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH f = true := by
  have := List.all_eq_true.mp tiFactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

/-- **No take at a pc of a phase with bit `3` set.** -/
theorem noTkH {lab : Label → Int64} (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x)
    {Λ : Scc.Sem.Layout} {l : String} {k v : Nat}
    (h : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH (.ph l k v) = true) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = (lab l + Int64.ofNat k).toBitVec.toNat → ¬ phH (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, ph_of_factOk hlab h] at hT
  omega

section Ti

open Spike.Lib.X64.Rt.Ti (TiPhAt stPcsAt preTkPcs)

open Spike.Lib.X64.Rt in
/-- **The first `scc_rt_thread_init` call's phase facts** at `phH`
(`tiPh_of_tab`'s pattern), returning to `scc_rt_start`'s `.x1`. -/
theorem tiPhH {L : RuntimeLayout} (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    TiPhAt (okPcOf lo helloCells L.Λ) phH (fun s => phH (pcOf s) / 8 % 2 = 0) L.lab
      (fun _ => L.lab ".Lscc_rt_start.x1") x8L := by
  have hf : ∀ f ∈ tiTabH, _ := fun f hf => ti_factH hΛ (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (codeLabel lo helloCells) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      L.lab ".Lscc_rt_start.x1" = L.lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.fnL 0 Code.Ti.tiPro none none) (by simp [tiTabH]))
    entry := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.entryL 0 Code.Ti.tiArg none none) (by simp [tiTabH]))
    c7 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.entryL 7 Code.Ti.callBlk none none) (by simp [tiTabH]))
    x7 := blkPh_of_factOk hlab hr hn (hf (.blk x8L 0 Code.Ti.tiSp none none) (by simp [tiTabH]))
    f1 := blkPh_of_factOk hlab hr hn (hf (.blk x8L 51 Code.Ti.tiF1 none none) (by simp [tiTabH]))
    f2 := blkPh_of_factOk hlab hr hn (hf (.blk x8L 63 Code.Ti.tiZ none none) (by simp [tiTabH]))
    f3 := blkPh_of_factOk hlab hr hn (hf (.blk x8L 78 Code.Ti.tiZ none none) (by simp [tiTabH]))
    f4 := blkPh_of_factOk hlab hr hn (hf (.blk x8L 93 Code.Ti.tiF4 none none) (by simp [tiTabH]))
    f5 := blkPh_of_factOk hlab hr hn (hf (.blk x8L 105 Code.Ti.tiF5 none none) (by simp [tiTabH]))
    ret := blkPh_of_factOk hlab (fun _ _ h => by cases h; exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm) hn
      (hf (.blk x8L 117 Code.Ti.tiRet (some (".Lscc_rt_start.x1", 0)) none) (by simp [tiTabH]))
    st := by
      intro pz hp
      simp only [stPcsAt, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step x8L 48 3) (by simp [tiTabH]))
      · exact step_of_factOk hlab (hf (.step x8L 59 4) (by simp [tiTabH]))
      · exact step_of_factOk hlab (hf (.step x8L 74 4) (by simp [tiTabH]))
      · exact step_of_factOk hlab (hf (.step x8L 89 4) (by simp [tiTabH]))
      · exact step_of_factOk hlab (hf (.step x8L 101 4) (by simp [tiTabH]))
      · exact step_of_factOk hlab (hf (.step x8L 113 4) (by simp [tiTabH]))
    noTk := by
      intro p hp
      simp only [preTkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact noTkH hlab (hf (.ph Code.Ti.fnL 0 12) (by simp [tiTabH])) (by decide)
      · exact noTkH hlab (hf (.ph Code.Ti.entryL 0 12) (by simp [tiTabH])) (by decide)
      · exact noTkH hlab (hf (.ph Code.Ti.entryL 7 12) (by simp [tiTabH])) (by decide) }

end Ti

section Take

open Spike.Lib.X64.Rt.Take (TakePh siPcs takePcs)
open Spike.Lib.X64.Flow.Ret0.StackTake

/-- A pin's phase (a row of `takeTkRows`, or the site's next pc). -/
theorem ph_rowTH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {lab : Label → Int64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ takeTkRows ++ [(Spike.Lib.X64.Rt.Code.Take.siteL, 1, 0)]) :
    phH (lab l + Int64.ofNat k).toBitVec.toNat = v :=
  ph_of_factOk hlab (take_factH hΛ (List.mem_append_right _ (List.mem_map.mpr ⟨(l, k, v), hr, rfl⟩)))

/-- No take at a pin of a phase with bit `3` set. -/
theorem noTk_rowTH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {lab : Label → Int64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ takeTkRows ++ [(Spike.Lib.X64.Rt.Code.Take.siteL, 1, 0)]) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = (lab l + Int64.ofNat k).toBitVec.toNat → ¬ phH (pcOf s) / 8 % 2 = 0 :=
  noTkH (Λ := Λ) hlab (take_factH hΛ (List.mem_append_right _ (List.mem_map.mpr ⟨(l, k, v), hr, rfl⟩))) hv

open Spike.Lib.X64.Rt in
/-- **The first `scc_rt_stack_take` call's phase facts** at `phH`
(`takePhAt_ofPlaceOK` with `ownH`), returning into `scc_rt_thread_init`'s
`.x8`, given the counters distinct (`c1`-`c8`). -/
theorem takePhH {L : RuntimeLayout} (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {a : BitVec 64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (c1 : L.pnA ≠ L.nextA) (c2 : L.pnA ≠ L.lockA) (c3 : L.pnA ≠ L.freeNA) (c4 : L.nextA ≠ L.lockA)
    (c5 : L.nextA ≠ L.freeNA) (c6 : L.lockA ≠ L.freeNA) (c7 : L.lockA ≠ a) (c8 : L.nextA ≠ a) :
    TakePh (okPcOf lo helloCells L.Λ) phH (fun s => phH (pcOf s) / 8 % 2 = 0) (ownH L a)
      (Spike.Lib.X64.PhRec.μ L) L.lab (fun _ => L.lab x8L) := by
  have hf : ∀ f ∈ takeWTab, _ := fun f hf => take_factH hΛ (f := f) hf
  have hT : ∀ f ∈ takePhTab, f ∈ takeWTab := fun f hf => List.mem_append_left _ hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (codeLabel lo helloCells) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      L.lab x8L = L.lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  have hx7 : L.lab x8L = L.lab Code.Ti.entryL + Int64.ofNat 12 := by
    have e1 : codeLabel lo helloCells x8L = some (lo + 1206) := by rw [← codeT_eq]; decide +kernel
    have e2 : codeLabel lo helloCells Code.Ti.entryL = some (lo + 1194) := by rw [← codeT_eq]; decide +kernel
    rw [hlab _ _ e1, hlab _ _ e2, ← Int64.ofNat_add]
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  have hsite : (L.lab siteL).toBitVec.toNat = 4200314 :=
    pcAt0_eq hlab (by unfold Scc.Cert.Rt.X64.pcAt; rw [← codeT_eq]; decide +kernel)
  have hs12 := ph_rowTH hΛ hlab (l := spinL) (k := 11) (v := 12) (by decide)
  have hs14 := ph_rowTH hΛ hlab (l := spinL) (k := 14) (v := 14) (by decide)
  have hb14 := ph_rowTH hΛ hlab (l := bumpL) (k := 28) (v := 14) (by decide)
  have hb12 := ph_rowTH hΛ hlab (l := bumpL) (k := 31) (v := 12) (by decide)
  have hn12 := ph_rowTH hΛ hlab (l := bumpL) (k := 56) (v := 12) (by decide)
  have hn8 := ph_rowTH hΛ hlab (l := bumpL) (k := 61) (v := 8) (by decide)
  have ht8 : phH (L.lab siteL).toBitVec.toNat = 8 := by
    have := ph_rowTH hΛ hlab (l := siteL) (k := 0) (v := 8) (by decide)
    rwa [Spike.Lib.X64.Flow.ofNat_zero'] at this
  have ht0 := ph_rowTH hΛ hlab (l := siteL) (k := 1) (v := 0) (by decide)
  have es3 : swpPc L.lab + Int64.ofNat 3 = L.lab spinL + Int64.ofNat 14 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 11 3).symm
  have eu3 : unlPc L.lab + Int64.ofNat 3 = L.lab bumpL + Int64.ofNat 31 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 28 3).symm
  have en5 : nextPc L.lab + Int64.ofNat 5 = L.lab bumpL + Int64.ofNat 61 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 56 5).symm
  exact {
    e := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.fnL 0 Code.Take.stPro none none) (by simp [takePhTab])))
    entry := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.entryL 0 Code.Take.stInit none none) (by simp [takePhTab])))
    cls := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.clsL 0 Code.Take.stCls none none) (by simp [takePhTab])))
    j1 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.clsL 13 Code.Take.stJ1 none none) (by simp [takePhTab])))
    d7 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.doneL 7 Code.Take.stFreeN none none) (by simp [takePhTab])))
    d33 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.doneL 33 Code.Take.stFree none none) (by simp [takePhTab])))
    d59 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.doneL 59 Code.Take.stLock none none) (by simp [takePhTab])))
    sp0 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.spinL 0 Code.Take.stSwp none none) (by simp [takePhTab])))
    sp14 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.spinL 14 Code.Take.stSpin none none) (by simp [takePhTab])))
    lk0 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.lockedL 0 Code.Take.stLdN none none) (by simp [takePhTab])))
    lk7 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.lockedL 7 Code.Take.stEmpty none none) (by simp [takePhTab])))
    b7 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.bumpL 7 Code.Take.stUnl none none) (by simp [takePhTab])))
    b38 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.bumpL 38 Code.Take.stAdd none none) (by simp [takePhTab])))
    b61 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.bumpL 61 Code.Take.stBnd none none) (by simp [takePhTab])))
    b108 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.bumpL 108 Code.Take.stJ2 none none) (by simp [takePhTab])))
    ok7 := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.okL 7 Code.Take.stOk none none) (by simp [takePhTab])))
    tk := blkPh_of_factOk hlab hr hn
      (hf _ (hT (.blk Code.Take.takenL 0 Code.Take.stSite none none) (by simp [takePhTab])))
    ret := blkPh_of_factOk hlab (fun _ _ h => by cases h; exact hx7) hn
      (hf _ (hT (.blk Code.Take.siteL 1 Code.Take.stRet (some (Code.Ti.entryL, 12)) none) (by simp [takePhTab])))
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf _ (hT (.step Code.Take.doneL 0 7) (by simp [takePhTab])))
      · exact step_of_factOk hlab (hf _ (hT (.step Code.Take.doneL 26 7) (by simp [takePhTab])))
      · exact step_of_factOk hlab (hf _ (hT (.step Code.Take.doneL 52 7) (by simp [takePhTab])))
      · exact step_of_factOk hlab (hf _ (hT (.step Code.Take.bumpL 0 7) (by simp [takePhTab])))
      · exact step_of_factOk hlab (hf _ (hT (.step Code.Take.bumpL 31 7) (by simp [takePhTab])))
      · exact step_of_factOk hlab (hf _ (hT (.step Code.Take.okL 0 7) (by simp [takePhTab])))
    swpOk := ok_of_factOk hlab (hf _ (hT (.ok Code.Take.spinL 11) (by simp [takePhTab])))
    ldnOk := (step_of_factOk hlab (hf _ (hT (.step Code.Take.lockedL 4 3) (by simp [takePhTab])))).1
    unlOk := ok_of_factOk hlab (hf _ (hT (.ok Code.Take.bumpL 28) (by simp [takePhTab])))
    nxtOk := ok_of_factOk hlab (hf _ (hT (.ok Code.Take.bumpL 56) (by simp [takePhTab])))
    ldnPh := (step_of_factOk hlab (hf _ (hT (.step Code.Take.lockedL 4 3) (by simp [takePhTab])))).2
    noTk := by
      intro p hp
      simp only [takePcs, siPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · rw [es3]; exact noTk_rowTH hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 14) (by decide) (by decide)
      · rw [eu3]; exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · rw [en5]; exact noTk_rowTH hΛ hlab (v := 8) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 8) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 8) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 8) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 8) (by decide) (by decide)
      · intro s hs hT; rw [hs, ht8] at hT; omega
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowTH hΛ hlab (v := 8) (by decide) (by decide)
    swpIn := ⟨(0#64).setWidth 128, by rw [hs12, hlk]; simp [ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf]⟩
    swpUpd := by
      rw [es3, hs12, hs14, hlk]
      simp [ownUpdB, ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    unlIn := ⟨(1#64).setWidth 128, by rw [hb14, hlk]; simp [ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf]⟩
    unlUpd := by
      rw [eu3, hb14, hb12, hlk]
      simp [ownUpdB, ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    nxtIn := ⟨(0#64).setWidth 128, by rw [hn12, hnx]; simp [ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf]⟩
    nxtUpd := by
      rw [en5, hn12, hn8, hnx]
      simp [ownUpdB, ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    siteRel := fun a ha => by
      have e : (Spike.Lib.X64.PhRec.μ L).site .release = some 4200354 := by
        show codeLabel L.Λ.code.lo L.prog "scc_rt_release_site" = _; rw [hp, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha; rw [hsite]; decide
    siteAb := fun k a ha => by
      have e : (Spike.Lib.X64.PhRec.μ L).abortAt k = codeLabel lo helloCells (Scc.Cert.Link.abortName k) := by
        show codeLabel L.Λ.code.lo L.prog (L.Λ.abortLbl k) = _; rw [hp, hlo, hΛ]
      rw [e, ← codeT_eq] at ha; rw [hsite]
      cases k <;> (rintro rfl; revert ha; decide +kernel)
    siteAt := by
      show codeLabel L.Λ.code.lo L.prog "scc_rt_take_site" = _
      rw [hp, hlo, hsite, ← codeT_eq]; decide +kernel
    siteOwn := by rw [ht8, ht0]; rfl
    tk1 := fun s hs => by show phH (pcOf s) / 8 % 2 = 0; rw [hs, ht0] }

end Take
section Start

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {lbl : Lbl}

/-- The instance at `phH` with `ownH` and the canonical take's phase. -/
theorem instOkHS (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s)))
      (fun s => phH (pcOf s) / 8 % 2 = 0) (Spike.Lib.X64.PhRec.K L rS) (okPcOf lo helloCells L.Λ) phH L.pfx :=
  instOkH hp hlo a (fun i => i / 8 % 2 = 0) (siteH hp hlo hlab)

/-- **`_start`'s nodes inside `SFacts`** at `phH` (`entryW_of_instOk`, as
`entryW_ofPlaceOK`), in any region with room for the call's return
address. -/
theorem entryW_hello (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hlo8 : R.lo ≤ -8) (hhi : 0 ≤ R.hi) {c0 : Ctl} (hC0 : CFacts L.Λ lbl c0) :
    Spike.Lib.X64.Rt.EntryW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
        (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F L.lab c0 := by
  have hrc : Spike.Lib.X64.Rt.RtCodeIn0 L.prog := hp ▸ hello_rtCodeIn0
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startH_fact hΛ (f := f) (start_memW hf)
  have hs0 := step_of_factOk hlab (hf (.step "_start" 0 2) (by simp only [startPhTab, List.mem_cons, true_or]))
  have hs2 := step_of_factOk hlab (hf (.step "_start" 2 4)
    (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hb := blkPh_of_factOk hlab (l := "_start") (o := 6) (b := Spike.Lib.X64.Rt.Code.Start.entryCall)
    (ra := none) (dead := none) (rapc := 0) (dset := fun _ => false) (fun _ _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h)
    (hf (.blk "_start" 6 Spike.Lib.X64.Rt.Code.Start.entryCall none none)
      (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hp0 := ph_of_factOk hlab (hf (.ph "_start" 0 13) (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hp2 := ph_of_factOk hlab (hf (.ph "_start" 2 13) (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hp6 := ph_of_factOk hlab (hf (.ph "_start" 6 13) (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  exact Spike.Lib.X64.Rt.entryW_of_instOk (instOkHS (a := a) (rS := rS) hp hlo hlab) hrc.start0 hR hlo8 hhi hC0
    hs0.1 hs0.2 hs2.1 hs2.2 hb (noTk_phH hp0 (by decide)) (noTk_phH hp2 (by decide)) (noTk_phH hp6 (by decide))

set_option maxHeartbeats 1600000 in
open Spike.Lib.X64.Rt Spike.Lib.X64.Rt.StartU in
/-- **`scc_rt_start`'s states up to the switch are inside `SFacts`** at
`phH` with `ownH` (`St0W`, `X0WAt` at `.x8`; `st0W_gen`'s and
`x0WAt_gen`'s bodies), the words separated (`hs`), `.rodata` off the pool
(`hro`), in any region holding its frame and its callees' below and the
return address above (`hR` … `hhi`), the stack range off it (`hout`). -/
theorem startSpH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    {c0 : Ctl} {R : Region} {F : MachineData → Prop} {n0 k0 : BitVec 64}
    (hC0 : CFacts L.Λ lbl c0) (hR : R.OK) (hlo' : R.lo ≤ -296)
    (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → rtF L m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) :
    St0W (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
        (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F n0 c0 ∧
      X0WAt (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
        (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F rS n0 k0
        c0 x8L := by
  subst hn0
  have hI := instOkHS (a := a) (rS := rS) hp hlo hlab
  have hrc : RtCodeIn0 L.prog := hp ▸ hello_rtCodeIn0
  have hti : Flow.Ret0.ThreadInit.threadInitInAt L.prog x8L = true := hp ▸ hello_tiIn
  have hl := hlab
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startH_fact hΛ (f := f) (start_memW hf)
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (codeLabel lo helloCells) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = L.lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hpn : pnA L.lab = L.pnA := L.lab_pn
  have hpin : pinA L.lab = L.pinA := L.lab_pin
  have hlk : lockA L.lab = L.lockA := L.lab_lock
  have hfr : freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : nextA L.lab = L.nextA := L.lab_next
  have h0 : ∃ j < 7, L.pinA + 0#64 = L.pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hfit := fitS_of_sub L hsub
  have hR1 := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR (by omega) (by decide) (by omega)
    (by omega)
  have ho1 := Flow.Ret0.Inst.out_callee hR (kc := -48 - 0) (lo' := -248) (hi' := 8) (by omega) (by decide)
    (by omega) (by omega) hout
  have ho2 := Flow.Ret0.Inst.out_callee hR1 (kc := -48 - 0) (lo' := -200) (hi' := 8)
    (by show (-248 : Int) ≤ _; omega) (by decide) (by show (-48 - 0 : Int) < 8; omega)
    (by show (-48 - 0 + 8 : Int) ≤ 8; omega) ho1
  have hSM := stackM_stable hfit hout
  have hst := hrc.start
  simp only [startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨-, cb0⟩, cbSi⟩, cbArgs⟩, cbSys⟩ := hst
  have hcl := hrc.call
  simp only [startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  have hcl2 := hrc.call2
  simp only [startCall2In, Bool.and_eq_true] at hcl2
  obtain ⟨cc2, -⟩ := hcl2
  have htl := hrc.tail
  simp only [startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨tFs, tSys⟩, tSw⟩, -⟩, -⟩, -⟩ := htl
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun g hg j => ?_⟩, ⟨?_, fun g hg j => ?_, ?_, ?_, ?_⟩⟩
  · -- The frame's setup.
    exact blkW_pre (dead := fun _ => false) (ra := 0) hI cb0 (ofNat_zero' _) xStart0_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk "scc_rt_start" 0 xStart0 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false xStart0_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_phH (ph_of_factOk hl (hf (.ph "scc_rt_start" 0 13) (by simp [startPhTab]))) (by decide))
  · -- The handler's `lea`.
    have hs := step_of_factOk hl (hf (.step startE 0 7) (by simp [startPhTab]))
    exact nodeW_si_pre (si := siSig) (p := L.lab startE + Int64.ofNat 0) hI cbSi rfl
      (ofNat_zero' _).symm (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_phH (ph_of_factOk hl (hf (.ph startE 0 13) (by simp [startPhTab]))) (by decide)) hs.2
  · -- The arguments.
    exact blkW_pre (dead := fun _ => false) (ra := 0) hI cbArgs rfl xStartArgs_ok hR
      (by omega) (by omega) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 7 xStartArgs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false xStartArgs_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_phH (ph_of_factOk hl (hf (.ph startE 7 13) (by simp [startPhTab]))) (by decide))
  · -- `rt_sigaction`'s `syscall`.
    have hs := step_of_factOk hl (hf (.step startE 41 2) (by simp [startPhTab]))
    exact nodeW_syscall_pre (p := L.lab startE + Int64.ofNat 41) hI cbSys rfl
      (startE41 L.lab) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_phH (ph_of_factOk hl (hf (.ph startE 41 13) (by simp [startPhTab]))) (by decide)) hs.2
      (fun _ _ ⟨_, _, he⟩ => by rw [he, Flow.Ret0.Inst.startS2_rax]; decide)
  · -- The call block.
    exact blkW_pre (dead := fun _ => false) (ra := 0) hI cc rfl startCall_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 43 Code.Start.startCall none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startCall_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_phH (ph_of_factOk hl (hf (.ph startE 43 13) (by simp [startPhTab]))) (by decide))
  · -- `scc_rt_alloc_tcb`.
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -184) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    exact tcbW_gen hI (fun _ => rfl) hrc.tcb hC0 hR' (by show (-184 : Int) ≤ -184; omega)
      (by show (8 : Int) ≤ 8; omega) ⟨g, 0#64, c0⟩ rfl hg (tcbPhH hΛ hlab hs)
      (by rw [hpn]; exact (L.words_mapped _ L.pn_mem).1)
      (by rw [hpin]; exact Spike.Lib.X64.PhRec.mapped_tcb h0)
      (fun m hm => by rw [hpn]; exact Spike.Lib.X64.PhRec.rtF_pn (hFr m hm))
      (fun m hm => by rw [hpin]; exact Spike.Lib.X64.PhRec.rtF_tcb (hFr m hm) h0) j
  · -- `.x0`'s block.
    exact blkW_pre (dead := fun _ => false) (ra := 0) hI cc2 (ofNat_zero' _) startCall2_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x0L 0 Code.Start.startCall2 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startCall2_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_phH (ph_of_factOk hl (hf (.ph Code.Start.x0L 0 12) (by simp [startPhTab]))) (by decide))
  · -- `scc_rt_thread_init`, returning to `.x1`, its take to `.x8`.
    exact tiWAt_gen hI (fun _ => rfl) hti hC0 hR1 (by show (-248 : Int) ≤ -248; omega)
      (by show (8 : Int) ≤ 8; omega) ⟨g, pinA L.lab + 0#64 + 8#64, k0, c0⟩ rfl hg (tiPhH hΛ hlab)
      (fun _ ha => Spike.Lib.X64.PhRec.mapped_tcb (tcb_fld ha))
      (fun _ ha m hm => Spike.Lib.X64.PhRec.rtF_tcb (hFr m hm) (tcb_fld ha))
      (fun _ ha => tcb_not_ownW hs (tcb_fld ha))
      hsub (stackM_stable hfit ho1) (stackM_stable hfit ho2) hrc.take
      (takePhH hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
        hs.lock_a hs.next_a)
      (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
      (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
      (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
      (fun m hm => by rw [hlk]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr m hm))
      (fun m hm => by rw [hfr]; exact Spike.Lib.X64.PhRec.rtF_freeN (hFr m hm))
      (fun m hm => by rw [hnx]; exact Spike.Lib.X64.PhRec.rtF_next (hFr m hm))
      hrS hro j
  · -- `.x1`'s block.
    exact blkW_post (dead := fun _ => false) (ra := 0) hI tFs (ofNat_zero' _) startFs_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x1L 0 Code.Start.startFs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startFs_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM
  · -- `arch_prctl`'s `syscall`.
    have hs := step_of_factOk hl (hf (.step Code.Start.x1L 18 2) (by simp [startPhTab]))
    exact nodeW_syscall_post (p := L.lab x1L + Int64.ofNat 18) hI tSys rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) hs.1 hs.2 hsub (fun _ _ hJ => by rw [hJ.2.1]; decide)
  · -- The block before the switch.
    exact blkW_post (dead := fun _ => false) (ra := 0) hI tSw rfl startSw_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x1L 20 Code.Start.startSw none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startSw_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM

/-- **`scc_rt_start`'s states are inside `SFacts`** (`StartEW`, from
`_start` to `call scc_rt_main`, the return point inside
`scc_rt_thread_init` `.x8`) at `phH` with `ownH` (`startEW_sfacts`):
`_start`'s nodes (`entryW_hello`), the start up to the switch (`startSpH`)
in the callee region, and the switch (`swEW_gen`, `swPhH`). -/
theorem startEW_hello (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    {c0 : Ctl} {R : Region} {F : MachineData → Prop} {n0 k0 : BitVec 64} {D : Int}
    (hC0 : CFacts L.Λ lbl c0) (hR : R.OK) (hlo' : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → rtF L m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (h8 : (stacksA L.lab + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA L.lab + k0 + 16384#64) (-D) 0).OK) (hL : 8 ≤ D) (hL8 : D % 8 = 0) :
    StartEW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
        (fun s => phH (pcOf s) / 8 % 2 = 0) lbl s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F rS n0 k0
      c0 D Spike.Lib.X64.Rt.x8L := by
  have hI := instOkHS (a := a) (rS := rS) hp hlo hlab
  have hR' := Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR (by omega) (by decide) (by omega)
    (by omega)
  have hout' := Spike.Lib.X64.Flow.Ret0.Inst.out_callee hR (kc := -8) (lo' := -296) (hi' := 8) (by omega)
    (by decide) (by omega) (by omega) hout
  refine ⟨entryW_hello hp hlo hΛ hlab hR (by omega) hhi hC0, fun F' _ _ hF' => ?_⟩
  have hsp := startSpH hp hlo hΛ hlab hs hro hC0 hR' (by show (-296 : Int) ≤ -296; omega)
    (by show (8 : Int) ≤ 8; omega) (fun m hm => hFr m (hF' m hm)) hn0 hrS hsub hout'
  refine ⟨hsp.1, hsp.2, ?_⟩
  subst hn0
  rw [hI.labOk]
  exact Spike.Lib.LowerX64.swEW_gen hI (hp ▸ hello_rtCodeIn0 : Spike.Lib.X64.Rt.RtCodeIn0 L.prog).tail hC0
    (swPhH hΛ hlab) h8 hok hL hL8 hsub (Spike.Lib.X64.Rt.fitS_of_sub L hsub)

end Start
end Spike.Lib.X64.HelloPh

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.startFactsH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.startFactsH

/-- info: 'Spike.Lib.X64.HelloPh.startH_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.startH_fact

/-- info: 'Spike.Lib.X64.HelloPh.hello_rtCodeIn0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.hello_rtCodeIn0

/-- info: 'Spike.Lib.X64.HelloPh.hello_tiIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.hello_tiIn

/-- info: 'Spike.Lib.X64.HelloPh.hello_rtCodeInTi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.hello_rtCodeInTi

/-- info: 'Spike.Lib.X64.HelloPh.ph_tcbH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ph_tcbH

/-- info: 'Spike.Lib.X64.HelloPh.noTk_tcbH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.noTk_tcbH

/-- info: 'Spike.Lib.X64.HelloPh.noTk_phH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.noTk_phH

/-- info: 'Spike.Lib.X64.HelloPh.siteH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.siteH

/-- info: 'Spike.Lib.X64.HelloPh.tcbPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.tcbPhH

/-- info: 'Spike.Lib.X64.HelloPh.swPhH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.swPhH

/-- info: 'Spike.Lib.X64.HelloPh.tiFactsH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.tiFactsH

/-- info: 'Spike.Lib.X64.HelloPh.take_factH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.take_factH

/-- info: 'Spike.Lib.X64.HelloPh.ti_factH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ti_factH

/-- info: 'Spike.Lib.X64.HelloPh.noTkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.noTkH

/-- info: 'Spike.Lib.X64.HelloPh.tiPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.tiPhH

/-- info: 'Spike.Lib.X64.HelloPh.ph_rowTH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ph_rowTH

/-- info: 'Spike.Lib.X64.HelloPh.noTk_rowTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.noTk_rowTH

/-- info: 'Spike.Lib.X64.HelloPh.takePhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.takePhH

/-- info: 'Spike.Lib.X64.HelloPh.instOkHS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.instOkHS

/-- info: 'Spike.Lib.X64.HelloPh.entryW_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.entryW_hello

/-- info: 'Spike.Lib.X64.HelloPh.startSpH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.startSpH

/-- info: 'Spike.Lib.X64.HelloPh.startEW_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.startEW_hello
