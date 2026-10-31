/-
**wake.w's first `scc_rt_thread_init` call's phase facts at `phW`**
(x86-64; the `TiPh` / `TakePh` halves of AArch64's `tiPhW` / `takePhW`,
`Spike/Lib/A64WakeStart.lean`, on the pattern of
`Spike/Lib/X64WakeTake2.lean`'s `tiPh2b` / `takePh2b`): the call from
`scc_rt_start` (returning to `.Lscc_rt_start.x1`) and its nested
`scc_rt_stack_take` call (returning to `.Lscc_rt_thread_init.x7`) at the
first instance's phase `phW` with `ownW`, the take's phase bit `3` clear.
Both callees lie outside `wakeR`, so `phW` is the canonical phase there.

- `takeWTab`, `tiWTab`: `takePhTab` with its pins' phases, `tiPhTab` named
  from `.x7` returning to `.x1`; decided at `phC` (`decide +kernel`).
- `noTkW`: no take at a pc of a phase with bit `3` set.
- `tiPhW`, `takePhW` (the counters distinct, `c1`-`c8`).
-/
import Spike.Lib.X64WakeTake2

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (InstOk RuntimeLayout ownUpdB takePhTab takeTkRows)
open Spike.Lib.X64.Rt.PhOfTab

open Spike.Lib.X64.Rt.Code in
/-- **The first `scc_rt_stack_take` call's facts**: `takePhTab` and the
phases at its pins. -/
def takeWTab : List PhFact :=
  takePhTab ++ (takeTkRows ++ [(Take.siteL, 1, 0)]).map fun (r : String × Nat × Nat) => .ph r.1 r.2.1 r.2.2

open Spike.Lib.X64.Rt.Code in
/-- **The first `scc_rt_thread_init` call's facts**: `tiPhTab` named from
`.x7`, returning to `scc_rt_start`'s `.x1`. -/
def tiWTab : List PhFact :=
  [.blk Ti.fnL 0 Ti.tiPro none none, .blk Ti.entryL 0 Ti.tiArg none none, .blk Ti.entryL 7 Ti.callBlk none none,
    .blk Ti.x7L 0 Ti.tiSp none none, .blk Ti.x7L 51 Ti.tiF1 none none, .blk Ti.x7L 63 Ti.tiZ none none,
    .blk Ti.x7L 78 Ti.tiZ none none, .blk Ti.x7L 93 Ti.tiF4 none none, .blk Ti.x7L 105 Ti.tiF5 none none,
    .blk Ti.x7L 117 Ti.tiRet (some (".Lscc_rt_start.x1", 0)) none,
    .step Ti.x7L 48 3, .step Ti.x7L 59 4, .step Ti.x7L 74 4, .step Ti.x7L 89 4, .step Ti.x7L 101 4,
    .step Ti.x7L 113 4,
    .ph Ti.fnL 0 12, .ph Ti.entryL 0 12, .ph Ti.entryL 7 12]

theorem takeWFacts : takeWTab.all (factOk (codeT lo wakeCells) okC phC) = true := by
  decide +kernel

theorem tiWFacts : tiWTab.all (factOk (codeT lo wakeCells) okC phC) = true := by
  decide +kernel

theorem takeW_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ takeWTab) : factOk (codeLabel lo wakeCells) (okPcOf lo wakeCells Λ) phW f = true := by
  have := List.all_eq_true.mp takeWFacts f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at this
  exact this

theorem tiW_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ tiWTab) : factOk (codeLabel lo wakeCells) (okPcOf lo wakeCells Λ) phW f = true := by
  have := List.all_eq_true.mp tiWFacts f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at this
  exact this

/-- **No take at a pc of a phase with bit `3` set.** -/
theorem noTkW {lab : Label → Int64} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x)
    {Λ : Scc.Sem.Layout} {l : String} {k v : Nat}
    (h : factOk (codeLabel lo wakeCells) (okPcOf lo wakeCells Λ) phW (.ph l k v) = true) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = (lab l + Int64.ofNat k).toBitVec.toNat → ¬ phW (pcOf s) / 8 % 2 = 0 := by
  intro s hs hT
  rw [hs, ph_of_factOk hlab h] at hT
  omega

section Ti

open Spike.Lib.X64.Rt.Ti (TiPh stPcs preTkPcs)

open Spike.Lib.X64.Rt in
/-- **The first `scc_rt_thread_init` call's phase facts** at `phW`
(`tiPh_of_tab`'s pattern), returning to `scc_rt_start`'s `.x1`. -/
theorem tiPhW {L : RuntimeLayout} (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    TiPh (okPcOf lo wakeCells L.Λ) phW (fun s => phW (pcOf s) / 8 % 2 = 0) L.lab
      (fun _ => L.lab ".Lscc_rt_start.x1") := by
  have hf : ∀ f ∈ tiWTab, _ := fun f hf => tiW_fact hΛ (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (codeLabel lo wakeCells) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      L.lab ".Lscc_rt_start.x1" = L.lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.fnL 0 Code.Ti.tiPro none none) (by simp [tiWTab]))
    entry := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.entryL 0 Code.Ti.tiArg none none) (by simp [tiWTab]))
    c7 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.entryL 7 Code.Ti.callBlk none none) (by simp [tiWTab]))
    x7 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.x7L 0 Code.Ti.tiSp none none) (by simp [tiWTab]))
    f1 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.x7L 51 Code.Ti.tiF1 none none) (by simp [tiWTab]))
    f2 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.x7L 63 Code.Ti.tiZ none none) (by simp [tiWTab]))
    f3 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.x7L 78 Code.Ti.tiZ none none) (by simp [tiWTab]))
    f4 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.x7L 93 Code.Ti.tiF4 none none) (by simp [tiWTab]))
    f5 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Ti.x7L 105 Code.Ti.tiF5 none none) (by simp [tiWTab]))
    ret := blkPh_of_factOk hlab (fun _ _ h => by cases h; exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm) hn
      (hf (.blk Code.Ti.x7L 117 Code.Ti.tiRet (some (".Lscc_rt_start.x1", 0)) none) (by simp [tiWTab]))
    st := by
      intro pz hp
      simp only [stPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step Code.Ti.x7L 48 3) (by simp [tiWTab]))
      · exact step_of_factOk hlab (hf (.step Code.Ti.x7L 59 4) (by simp [tiWTab]))
      · exact step_of_factOk hlab (hf (.step Code.Ti.x7L 74 4) (by simp [tiWTab]))
      · exact step_of_factOk hlab (hf (.step Code.Ti.x7L 89 4) (by simp [tiWTab]))
      · exact step_of_factOk hlab (hf (.step Code.Ti.x7L 101 4) (by simp [tiWTab]))
      · exact step_of_factOk hlab (hf (.step Code.Ti.x7L 113 4) (by simp [tiWTab]))
    noTk := by
      intro p hp
      simp only [preTkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact noTkW hlab (hf (.ph Code.Ti.fnL 0 12) (by simp [tiWTab])) (by decide)
      · exact noTkW hlab (hf (.ph Code.Ti.entryL 0 12) (by simp [tiWTab])) (by decide)
      · exact noTkW hlab (hf (.ph Code.Ti.entryL 7 12) (by simp [tiWTab])) (by decide) }

end Ti

section Take

open Spike.Lib.X64.Rt.Take (TakePh siPcs takePcs)
open Spike.Lib.X64.Flow.Ret0.StackTake

/-- A pin's phase (a row of `takeTkRows`, or the site's next pc). -/
theorem ph_rowW {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {lab : Label → Int64}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ takeTkRows ++ [(Spike.Lib.X64.Rt.Code.Take.siteL, 1, 0)]) :
    phW (lab l + Int64.ofNat k).toBitVec.toNat = v :=
  ph_of_factOk hlab (takeW_fact hΛ (List.mem_append_right _ (List.mem_map.mpr ⟨(l, k, v), hr, rfl⟩)))

/-- No take at a pin of a phase with bit `3` set. -/
theorem noTk_rowW {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {lab : Label → Int64}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x) {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ takeTkRows ++ [(Spike.Lib.X64.Rt.Code.Take.siteL, 1, 0)]) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = (lab l + Int64.ofNat k).toBitVec.toNat → ¬ phW (pcOf s) / 8 % 2 = 0 :=
  noTkW (Λ := Λ) hlab (takeW_fact hΛ (List.mem_append_right _ (List.mem_map.mpr ⟨(l, k, v), hr, rfl⟩))) hv

open Spike.Lib.X64.Rt in
/-- **The first `scc_rt_stack_take` call's phase facts** at `phW`
(`takePhAt_ofPlaceOK` with `ownW`), returning into `scc_rt_thread_init`'s
`.x7`, given the counters distinct (`c1`-`c8`). -/
theorem takePhW {L : RuntimeLayout} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {a : BitVec 64}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (c1 : L.pnA ≠ L.nextA) (c2 : L.pnA ≠ L.lockA) (c3 : L.pnA ≠ L.freeNA) (c4 : L.nextA ≠ L.lockA)
    (c5 : L.nextA ≠ L.freeNA) (c6 : L.lockA ≠ L.freeNA) (c7 : L.lockA ≠ a) (c8 : L.nextA ≠ a) :
    TakePh (okPcOf lo wakeCells L.Λ) phW (fun s => phW (pcOf s) / 8 % 2 = 0) (ownW L a)
      (Spike.Lib.X64.PhRec.μ L) L.lab (fun _ => L.lab Code.Ti.x7L) := by
  have hf : ∀ f ∈ takeWTab, _ := fun f hf => takeW_fact hΛ (f := f) hf
  have hT : ∀ f ∈ takePhTab, f ∈ takeWTab := fun f hf => List.mem_append_left _ hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (codeLabel lo wakeCells) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      L.lab Code.Ti.x7L = L.lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  have hx7 : L.lab Code.Ti.x7L = L.lab Code.Ti.entryL + Int64.ofNat 12 := by
    have e1 : codeLabel lo wakeCells Code.Ti.x7L = some (lo + 1169) := by rw [← codeT_eq]; decide +kernel
    have e2 : codeLabel lo wakeCells Code.Ti.entryL = some (lo + 1157) := by rw [← codeT_eq]; decide +kernel
    rw [hlab _ _ e1, hlab _ _ e2, ← Int64.ofNat_add]
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  have hsite : (L.lab siteL).toBitVec.toNat = 4200277 :=
    pcAt0_eq hlab (by unfold Scc.Cert.Rt.X64.pcAt; rw [← codeT_eq]; decide +kernel)
  have hs12 := ph_rowW hΛ hlab (l := spinL) (k := 11) (v := 12) (by decide)
  have hs14 := ph_rowW hΛ hlab (l := spinL) (k := 14) (v := 14) (by decide)
  have hb14 := ph_rowW hΛ hlab (l := bumpL) (k := 28) (v := 14) (by decide)
  have hb12 := ph_rowW hΛ hlab (l := bumpL) (k := 31) (v := 12) (by decide)
  have hn12 := ph_rowW hΛ hlab (l := bumpL) (k := 56) (v := 12) (by decide)
  have hn8 := ph_rowW hΛ hlab (l := bumpL) (k := 61) (v := 8) (by decide)
  have ht8 : phW (L.lab siteL).toBitVec.toNat = 8 := by
    have := ph_rowW hΛ hlab (l := siteL) (k := 0) (v := 8) (by decide)
    rwa [Spike.Lib.X64.Flow.ofNat_zero'] at this
  have ht0 := ph_rowW hΛ hlab (l := siteL) (k := 1) (v := 0) (by decide)
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
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · rw [es3]; exact noTk_rowW hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 14) (by decide) (by decide)
      · rw [eu3]; exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · rw [en5]; exact noTk_rowW hΛ hlab (v := 8) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 8) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 8) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 8) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 8) (by decide) (by decide)
      · intro s hs hT; rw [hs, ht8] at hT; omega
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 14) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 12) (by decide) (by decide)
      · exact noTk_rowW hΛ hlab (v := 8) (by decide) (by decide)
    swpIn := ⟨(0#64).setWidth 128, by rw [hs12, hlk]; simp [ownW, Spike.Lib.X64.PhRec.ownOf]⟩
    swpUpd := by
      rw [es3, hs12, hs14, hlk]
      simp [ownUpdB, ownW, Spike.Lib.X64.PhRec.ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    unlIn := ⟨(1#64).setWidth 128, by rw [hb14, hlk]; simp [ownW, Spike.Lib.X64.PhRec.ownOf]⟩
    unlUpd := by
      rw [eu3, hb14, hb12, hlk]
      simp [ownUpdB, ownW, Spike.Lib.X64.PhRec.ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    nxtIn := ⟨(0#64).setWidth 128, by rw [hn12, hnx]; simp [ownW, Spike.Lib.X64.PhRec.ownOf]⟩
    nxtUpd := by
      rw [en5, hn12, hn8, hnx]
      simp [ownUpdB, ownW, Spike.Lib.X64.PhRec.ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6, c7, c8, Ne.symm c7, Ne.symm c8]
    siteRel := fun a ha => by
      have e : (Spike.Lib.X64.PhRec.μ L).site .release = some 4200317 := by
        show codeLabel L.Λ.code.lo L.prog "scc_rt_release_site" = _; rw [hp, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha; rw [hsite]; decide
    siteAb := fun k a ha => by
      have e : (Spike.Lib.X64.PhRec.μ L).abortAt k = codeLabel lo wakeCells (Scc.Cert.Link.abortName k) := by
        show codeLabel L.Λ.code.lo L.prog (L.Λ.abortLbl k) = _; rw [hp, hlo, hΛ]
      rw [e, ← codeT_eq] at ha; rw [hsite]
      cases k <;> (rintro rfl; revert ha; decide +kernel)
    siteAt := by
      show codeLabel L.Λ.code.lo L.prog "scc_rt_take_site" = _
      rw [hp, hlo, hsite, ← codeT_eq]; decide +kernel
    siteOwn := by rw [ht8, ht0]; rfl
    tk1 := fun s hs => by show phW (pcOf s) / 8 % 2 = 0; rw [hs, ht0] }

end Take

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.takeWFacts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.takeWFacts

/-- info: 'Spike.Lib.X64.WakePh.tiWFacts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tiWFacts

/-- info: 'Spike.Lib.X64.WakePh.takeW_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.takeW_fact

/-- info: 'Spike.Lib.X64.WakePh.tiW_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tiW_fact

/-- info: 'Spike.Lib.X64.WakePh.noTkW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.noTkW

/-- info: 'Spike.Lib.X64.WakePh.tiPhW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tiPhW

/-- info: 'Spike.Lib.X64.WakePh.ph_rowW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ph_rowW

/-- info: 'Spike.Lib.X64.WakePh.noTk_rowW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.noTk_rowW

/-- info: 'Spike.Lib.X64.WakePh.takePhW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.takePhW
