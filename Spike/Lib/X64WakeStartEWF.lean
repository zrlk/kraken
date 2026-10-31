/-
**wake.w's `scc_rt_start` at `phW`: the facts** (x86-64; the facts half of
`Spike/Lib/A64WakeStart.lean`): the start's, `scc_rt_alloc_tcb`'s
and the switch's phase facts at wake.w's extended phase `phW`
(`Spike/Lib/X64WakePh.lean`) with the owned words `ownW` (the thread
counter at `a`) and the canonical take's phase (bit `3` of `phW`), decided
on wakeCells' labels (`decide +kernel` through `codeT`) instead of A6's
table at a placed output. The pcs of `scc_rt_start` and its callees lie
outside `wakeR`, so `phW` is the canonical phase there. The obligations
from these facts are `Spike/Lib/X64WakeStartEW.lean`'s.

- `startTabW`, `startFactsW`, `startW_fact`: `scc_rt_alloc_tcb`'s
  (`tcbPhTab`, returning to `.Lscc_rt_start.x0`), the switch's
  (`swPhTab`), the start's (`startPhTab`) and `scc_rt_alloc_tcb`'s pcs'
  phases (`tcbTkRows`), decided at `phC`.
- `wake_rtCodeIn0`, `wake_tiIn`, `wake_rtCodeInTi`: the start's code checks
  of wakeCells (`scc_rt_thread_init` returning to `.x7`).
- `ph_tcbW`, `noTk_tcbW`, `noTk_phW`: a pin's phase at `phW`; no take at a
  pc of a phase with bit `3` set.
- `WSep`, `tcb_not_ownW`: the words' separation; a TCB word owned at no
  phase of `ownW`.
- `siteW`: the take site at its label.
- `tcbPhW`, `swPhW`: `scc_rt_alloc_tcb`'s and the switch's phase facts
  (`tcbPh_ofPlaceOK`, `swPh_ofPlaceOK` at `phW`, `ownW`).

**Unlike AArch64**: there is no `phPins` table; the pins are
`tcbTkRows`' rows (as `tcbPh_ofPlaceOK`), so `pinTab`, `pin_memW`,
`ph_pinW`, `noTk_pinW` become `ph_tcbW`, `noTk_tcbW`.
`scc_rt_thread_init`'s and `scc_rt_stack_take`'s tables and phase facts
are separate (`tiWTab`, `takeWTab`, `tiPhW`, `takePhW`,
`Spike/Lib/X64WakeStartPhW.lean`), not repeated in `startTabW`;
`takePhW` takes the counters' separation as `c1`-`c8` (from `WSep`).
`scc_rt_alloc_tcb` returns to `.x0` (AArch64's `.sp2`), the switch is at
`.x1` + 28.
-/
import Spike.Lib.X64WakeStartPhW
import Spike.Lib.Rt.X64RtCodeSetup
import Spike.Lib.Rt.X64RtMainU

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (InstOk RuntimeLayout ownUpdB tcbPhTab swPhTab startPhTab tcbTkRows tcbFullL)
open Spike.Lib.X64.Rt.PhOfTab

/-! ## The facts -/

/-- **The start's facts**: `scc_rt_alloc_tcb`'s (returning to `.x0`), the
switch's, the start's and `scc_rt_alloc_tcb`'s pins' phases. -/
def startTabW : List PhFact :=
  tcbPhTab ++ swPhTab ++ startPhTab ++ tcbTkRows.map fun (r : String × Nat × Nat) => .ph r.1 r.2.1 r.2.2

/-- **The start's facts hold** at `phC`. -/
theorem startFactsW : startTabW.all (factOk (codeT lo wakeCells) okC phC) = true := by
  decide +kernel

theorem startW_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ startTabW) : factOk (codeLabel lo wakeCells) (okPcOf lo wakeCells Λ) phW f = true := by
  have := List.all_eq_true.mp startFactsW f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at this
  exact this

theorem tcb_memW {f : PhFact} (hf : f ∈ tcbPhTab) : f ∈ startTabW :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hf))

theorem sw_memW {f : PhFact} (hf : f ∈ swPhTab) : f ∈ startTabW :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hf))

theorem start_memW {f : PhFact} (hf : f ∈ startPhTab) : f ∈ startTabW :=
  List.mem_append_left _ (List.mem_append_right _ hf)

/-- **The start's code checks** of wakeCells. -/
theorem wake_rtCodeIn0 : Spike.Lib.X64.Rt.RtCodeIn0 wakeCells :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- `scc_rt_thread_init`'s code check of wakeCells, returning to `.x7`. -/
theorem wake_tiIn : Spike.Lib.X64.Flow.Ret0.ThreadInit.threadInitIn wakeCells = true := by
  decide +kernel

/-- **The start's code checks with `scc_rt_thread_init`'s** at `.x7`. -/
theorem wake_rtCodeInTi : Spike.Lib.X64.Rt.RtCodeInTi wakeCells Spike.Lib.X64.Flow.Ret0.ThreadInit.x7L :=
  { wake_rtCodeIn0 with ti := by decide +kernel }

variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

/-- **A pin's phase index** at `phW` (a row of `tcbTkRows`). -/
theorem ph_tcbW (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ tcbTkRows) : phW (lab l + Int64.ofNat k).toBitVec.toNat = v :=
  ph_of_factOk hlab (startW_fact (Λ := Λ) hΛ (List.mem_append_right _ (List.mem_map.mpr ⟨(l, k, v), hr, rfl⟩)))

/-- **No take at a pin with bit `3` set.** -/
theorem noTk_tcbW (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ tcbTkRows) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = (lab l + Int64.ofNat k).toBitVec.toNat → ¬ phW (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, ph_tcbW hΛ hlab hr] at hT
  omega

/-- **No take at a pc of a phase with bit `3` set.** -/
theorem noTk_phW {p : Int64} {v : Nat} (hp : phW p.toBitVec.toNat = v) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ phW (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, hp] at hT
  omega

/-! ## The words -/

/-- **The words' separation**: the four counters distinct, the thread
counter's word `a` none of them, and the first TCB's words none of them. -/
structure WSep (L : RuntimeLayout) (a : BitVec 64) : Prop where
  pn_next : L.pnA ≠ L.nextA
  pn_lock : L.pnA ≠ L.lockA
  pn_freeN : L.pnA ≠ L.freeNA
  next_lock : L.nextA ≠ L.lockA
  next_freeN : L.nextA ≠ L.freeNA
  lock_freeN : L.lockA ≠ L.freeNA
  pn_a : L.pnA ≠ a
  next_a : L.nextA ≠ a
  lock_a : L.lockA ≠ a
  freeN_a : L.freeNA ≠ a
  tcb : Spike.Lib.X64.PhRec.TcbSep L
  tcb_a : ∀ j < 7, L.pinA + BitVec.ofNat 64 (8 * j) ≠ a

/-- **A TCB word is owned at no phase** of `ownW`. -/
theorem tcb_not_ownW {L : RuntimeLayout} {a : BitVec 64} (hs : WSep L a) {b : BitVec 64}
    (hb : ∃ j < 7, b = L.pinA + BitVec.ofNat 64 (8 * j)) : ∀ i w, (⟨b, 8⟩, w) ∉ ownW L a i := by
  intro i w hm
  unfold ownW at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact Spike.Lib.X64.PhRec.tcb_not_own hs.tcb hb i w hm
  · obtain ⟨j, hj, rfl⟩ := hb
    simp only [List.mem_singleton, Prod.mk.injEq, Loc.mk.injEq] at hm
    exact hs.tcb_a j hj hm.1.1

/-- **The take site at its label.** -/
theorem siteW {L : RuntimeLayout} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have hsite : (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat = 4200277 :=
    pcAt0_eq hlab (by unfold Scc.Cert.Rt.X64.pcAt; rw [← codeT_eq]; decide +kernel)
  show codeLabel L.Λ.code.lo L.prog "scc_rt_take_site" = _
  rw [hp, hlo, hsite, ← codeT_eq]; decide +kernel

/-! ## The callees' phase facts -/

section Tcb

open Spike.Lib.X64.Rt.Tcb (TcbPh tcbDead tcbPcs blkPcs stepPcs)
open Spike.Lib.X64.Flow.Ret0.AllocTcb

/-- **`scc_rt_alloc_tcb`'s phase facts at `phW`** with `ownW`, returning to
`.x0`, the header at `scc_rt_pinned`. -/
theorem tcbPhW (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {a : BitVec 64}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a) :
    TcbPh (okPcOf lo wakeCells Λ) phW (fun s => phW (pcOf s) / 8 % 2 = 0) (ownW L a) L.lab
      (fun _ => L.lab Rt.Code.Start.x0L) 0#64 := by
  have hf : ∀ f ∈ tcbPhTab, _ := fun f hf => startW_fact hΛ (f := f) (tcb_memW hf)
  have hl := hlab
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.X64.deadN (codeLabel lo wakeCells) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      L.lab Rt.Code.Start.x0L = L.lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.X64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have h13 := ph_tcbW hΛ hlab (l := lenL) (k := 158) (v := 13) (by decide)
  have h12 := ph_tcbW hΛ hlab (l := lenL) (k := 163) (v := 12) (by decide)
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
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_tcbW hΛ hlab (v := 13) (by decide) (by decide)
      · rw [e5]; exact noTk_tcbW hΛ hlab (v := 12) (by decide) (by decide)
    rmwIn := ⟨(0#64).setWidth 128, by rw [h13, hpn]; simp [ownW, Spike.Lib.X64.PhRec.ownOf]⟩
    rmwUpd := by
      rw [e5, h13, h12, hpn]
      simp [ownUpdB, ownW, Spike.Lib.X64.PhRec.ownOf, hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a,
        Ne.symm hs.pn_lock, Ne.symm hs.pn_freeN, Ne.symm hs.pn_next, Ne.symm hs.pn_a]
    hdrNo := fun j w => by
      rw [hpin]
      exact tcb_not_ownW hs ⟨0, by decide, by simp⟩ j w }

end Tcb

/-- **The switch's phase facts at `phW`.** -/
theorem swPhW (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x) :
    Spike.Lib.X64.Rt.MainU.SwPh (okPcOf lo wakeCells Λ) phW lab where
  sw := step_of_factOk hlab
    (startW_fact hΛ (f := .step Spike.Lib.X64.Rt.Code.Start.x1L 28 3) (sw_memW (by simp [swPhTab])))
  xor := step_of_factOk hlab
    (startW_fact hΛ (f := .step Spike.Lib.X64.Rt.Code.Start.x1L 31 2) (sw_memW (by simp [swPhTab])))
  main := blkPh_of_factOk (ra := none) (dead := none) hlab (fun _ _ h => nomatch h)
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h)
    (startW_fact hΛ (f := .blk Spike.Lib.X64.Rt.Code.Start.x1L 33 Spike.Lib.X64.Rt.Code.Start.startMain none none)
      (sw_memW (by simp [swPhTab])))

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.startFactsW' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.startFactsW

/-- info: 'Spike.Lib.X64.WakePh.startW_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.startW_fact

/-- info: 'Spike.Lib.X64.WakePh.tcb_memW' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcb_memW

/-- info: 'Spike.Lib.X64.WakePh.sw_memW' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.sw_memW

/-- info: 'Spike.Lib.X64.WakePh.start_memW' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.start_memW

/-- info: 'Spike.Lib.X64.WakePh.wake_rtCodeIn0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.wake_rtCodeIn0

/-- info: 'Spike.Lib.X64.WakePh.wake_tiIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.wake_tiIn

/-- info: 'Spike.Lib.X64.WakePh.wake_rtCodeInTi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.wake_rtCodeInTi

/-- info: 'Spike.Lib.X64.WakePh.ph_tcbW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ph_tcbW

/-- info: 'Spike.Lib.X64.WakePh.noTk_tcbW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.noTk_tcbW

/-- info: 'Spike.Lib.X64.WakePh.noTk_phW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.noTk_phW

/-- info: 'Spike.Lib.X64.WakePh.tcb_not_ownW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcb_not_ownW

/-- info: 'Spike.Lib.X64.WakePh.siteW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.siteW

/-- info: 'Spike.Lib.X64.WakePh.tcbPhW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcbPhW

/-- info: 'Spike.Lib.X64.WakePh.swPhW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.swPhW
