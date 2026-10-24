/-
**The runtime's phase facts at a placed output** (AArch64): at the record
`RuntimeLayout.ofPlaceOK h i` of an output passing `placeOK`, a program
passing the decided table (`rtPhOk … (rtPhTab mc)`,
`Spike/Lib/Rt/A64RtPhTab.lean`) gives the hand proofs' phase structures at
the record's `okPc`/`ph` and labels:

- `hlab_ofPlaceOK`: the record's labels agree with `codeOf` where it
  resolves (the loader's, `label_threadAt_of_codeOf`);
- `swPh_ofPlaceOK`: the switch's (`SwPh`);
- `mainPh_ofPlaceOK`: `scc_rt_main`'s at `mc` (`MainPh`), from the table
  with `mainPhTab mc`;
- `tiPh_ofPlaceOK`: `scc_rt_thread_init`'s (`TiPh`), returning to `.sp3`;
  its prologue and call before the take (phase `12`);
- `tcbPh_ofPlaceOK`, `takePh_ofPlaceOK`: `scc_rt_alloc_tcb`'s (`TcbPh`,
  returning to `.sp2`) and `scc_rt_stack_take`'s (`TakePh`, returning to
  `.sp0`), their phases at the pinned pcs (A6's `phPins`, `ph_pin`), the
  owned counters distinct and the TCB off them (A8, `counters_ne`,
  `tcbSep`), the take site none of the other sites (`take_ne`);
- `rodata_stackPool_disjoint_ofPlaceOK`: the `.rodata` range off the stack
  pool (A1's `layoutOk`, `rodata_stackPool_of_placeOKAt`), the take's premise.
-/
import Spike.Lib.Rt.A64RtPhOfTab
import Spike.Lib.Rt.A64RtPhTab
import Spike.Lib.A64PhRec
import Spike.Lib.Rt.A64RtMainU

namespace Spike.Lib.A64.Rt.PhRecOf

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Sem (AbortKind)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Rt.A64 (factOk_of_rtPhOk rtPhOk)
open Spike.Lib.A64.Rt (RuntimeLayout rtPhTab mainPhTab swPhTab)
open Spike.Lib.A64.Rt.PhOfTab
open Spike.Lib.A64.PhRec (ph okPc)
open Spike.Lib.A64.Rt.MainU (MainPh SwPh)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The record's labels agree with `codeOf`** where it resolves. -/
theorem hlab_ofPlaceOK : ∀ l a, codeOf (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog l = some a →
    (RuntimeLayout.ofPlaceOK h i).lab l = Int64.ofNat a := fun _ _ ha =>
  Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below (E := Scc.Sem.Entry.linux)
    (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha

/-- **The switch's phase facts** of a program passing the table. -/
theorem swPh_ofPlaceOK {mc : Option MainCode}
    (hrt : rtPhOk (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog (RuntimeLayout.ofPlaceOK h i).Λ
      (rtPhTab mc) = true) :
    SwPh (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab where
  sw := step_of_factOk (hlab_ofPlaceOK h i)
    (factOk_of_rtPhOk (f := .step Code.Start.sp3L 5) hrt (by simp [rtPhTab, swPhTab]))
  main := blkPh_of_factOk (ra := none) (dead := none) (hlab_ofPlaceOK h i) (fun _ h => nomatch h)
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h)
    (factOk_of_rtPhOk (f := .blk Code.Start.sp3L 6 Code.Start.startMain none none) hrt
      (by simp [rtPhTab, swPhTab]))

/-- **`scc_rt_main`'s phase facts at `mc`** of a program passing the table
with `scc_rt_main`'s at `mc`. -/
theorem mainPh_ofPlaceOK {mc : MainCode}
    (hm : rtPhOk (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog (RuntimeLayout.ofPlaceOK h i).Λ
      (rtPhTab (some mc)) = true) :
    MainPh (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab mc := by
  have hf : ∀ f ∈ mainPhTab mc, _ := fun f hf => factOk_of_rtPhOk (f := f) hm (by simp [rtPhTab, hf])
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = (RuntimeLayout.ofPlaceOK h i).lab r :=
    fun _ h => nomatch h
  exact {
    hd := blkPh_of_factOk (hlab_ofPlaceOK h i) hr hn (hf _ (by simp [mainPhTab]))
    ld := step_of_factOk (hlab_ofPlaceOK h i) (hf (.step mc.sc 2) (by simp [mainPhTab]))
    br := blkPh_of_factOk (hlab_ofPlaceOK h i) hr hn (hf _ (by simp [mainPhTab]))
    fr := blkPh_of_factOk (hlab_ofPlaceOK h i) hr hn (hf _ (by simp [mainPhTab]))
    call := blkPh_of_factOk (hlab_ofPlaceOK h i) hr hn (hf _ (by simp [mainPhTab]))
    ex := blkPh_of_factOk (hlab_ofPlaceOK h i) hr hn (hf _ (by simp [mainPhTab]))
    svc := step_of_factOk (hlab_ofPlaceOK h i) (hf (.step mc.sp0 3) (by simp [mainPhTab])) }

open Spike.Lib.A64.Rt.Ti (TiPh stPcs) in
open Spike.Lib.A64.Flow.Ret0.ThreadInit in
/-- **`scc_rt_thread_init`'s phase facts** of a program passing the table,
returning to `.sp3`. -/
theorem tiPh_ofPlaceOK {mc : Option MainCode}
    (hrt : rtPhOk (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog (RuntimeLayout.ofPlaceOK h i).Λ
      (rtPhTab mc) = true) :
    TiPh (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) (RuntimeLayout.ofPlaceOK h i).lab
      (fun _ => (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.sp3L) := by
  have hf : ∀ f ∈ Spike.Lib.A64.Rt.tiPhTab, _ := fun f hf => factOk_of_rtPhOk (f := f) hrt
    (by simp [rtPhTab, hf])
  have hl := hlab_ofPlaceOK h i
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r →
      (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.sp3L = (RuntimeLayout.ofPlaceOK h i).lab r :=
    fun _ h => nomatch h
  have h12 : ∀ l, (l = fnL ∨ l = entryL) →
      ph (RuntimeLayout.ofPlaceOK h i) ((RuntimeLayout.ofPlaceOK h i).lab l + Int64.ofNat (4 * 0)).toBitVec.toNat
        = 12 := by
    rintro l (rfl | rfl)
    · exact ph_of_factOk hl (hf (.ph Code.Ti.fnL 0 12) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    · exact ph_of_factOk hl (hf (.ph Code.Ti.entryL 0 12) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
  exact {
    e := blkPh_of_factOk hl hr hn (hf (.blk Code.Ti.fnL 0 Code.Ti.tiPro none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    entry := blkPh_of_factOk hl hr hn (hf (.blk Code.Ti.entryL 0 Code.Ti.tiCall none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    sp := blkPh_of_factOk hl hr hn (hf (.blk Code.Ti.spL 0 Code.Ti.tiSp none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f1 := blkPh_of_factOk hl hr hn (hf (.blk Code.Ti.spL 12 Code.Ti.tiF1 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f2 := blkPh_of_factOk hl hr hn (hf (.blk Code.Ti.spL 15 Code.Ti.tiF2 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f3 := blkPh_of_factOk hl hr hn (hf (.blk Code.Ti.spL 18 Code.Ti.tiF3 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f4 := blkPh_of_factOk hl hr hn (hf (.blk Code.Ti.spL 21 Code.Ti.tiF4 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    f5 := blkPh_of_factOk hl hr hn (hf (.blk Code.Ti.spL 24 Code.Ti.tiF5 none none)
      (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    ret := blkPh_of_factOk hl (fun _ h => by cases h; rfl) hn
      (hf (.blk Code.Ti.spL 27 Code.Ti.tiRet (some Code.Start.sp3L) none) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    st := by
      intro p hp
      simp only [stPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hl (hf (.step Code.Ti.spL 11) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Ti.spL 14) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Ti.spL 17) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Ti.spL 20) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Ti.spL 23) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Ti.spL 26) (by simp [Spike.Lib.A64.Rt.tiPhTab]))
    noTk := by
      intro p hp s hs hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      unfold Spike.Lib.A64.PhRec.Tk at hT
      rcases hp with rfl | rfl
      · rw [hs, h12 fnL (.inl rfl)] at hT; cases hT
      · rw [hs, h12 entryL (.inr rfl)] at hT; cases hT }

/-! ## The pins and the words

A pin of A6 (`phPins`) gives the phase index at its pc of the record; A8's
words are pairwise disjoint, so the counters are distinct and the TCB's
words none of them (`TcbSep`). -/

/-- **A pin's phase index** at the record's labels. -/
theorem ph_pin {l : String} {k v : Nat} (hp : (l, k, v) ∈ Scc.Cert.Rt.A64.phPins) :
    ph (RuntimeLayout.ofPlaceOK h i)
      ((RuntimeLayout.ofPlaceOK h i).lab l + Int64.ofNat (4 * k)).toBitVec.toNat = v := by
  obtain ⟨a, ha, hv⟩ := pin_of_placeOKAt h hp
  rw [hlab_ofPlaceOK h i l a ha, toNat_add]
  exact hv

/-- **A pin in a phase with bit 3 set** (before the take): no take there. -/
theorem noTk_pin {l : String} {k v : Nat} (hp : (l, k, v) ∈ Scc.Cert.Rt.A64.phPins) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = ((RuntimeLayout.ofPlaceOK h i).lab l + Int64.ofNat (4 * k)).toBitVec.toNat →
      ¬ Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i) s := by
  intro s hs hT
  unfold Spike.Lib.A64.PhRec.Tk at hT
  rw [hs, ph_pin h i hp] at hT
  omega

/-- **The record's words are pairwise disjoint** (A8). -/
theorem words_disj :
    (Scc.Cert.Rt.A64.rtWords (RuntimeLayout.ofPlaceOK h i).pinA (RuntimeLayout.ofPlaceOK h i).pnA
      (RuntimeLayout.ofPlaceOK h i).nextA (RuntimeLayout.ofPlaceOK h i).lockA
      (RuntimeLayout.ofPlaceOK h i).freeNA).Pairwise Scc.Cert.Rt.A64.WordSep :=
  Scc.Cert.Rt.A64.words_disj_of_wordsOk (Scc.Cert.Rt.A64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeOKAt i h))

/-- **The counters are distinct.** -/
theorem counters_ne :
    let L := RuntimeLayout.ofPlaceOK h i
    L.pnA ≠ L.nextA ∧ L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.nextA ≠ L.lockA ∧ L.nextA ≠ L.freeNA ∧
      L.lockA ≠ L.freeNA := by
  have hd := words_disj h i
  simp only [Scc.Cert.Rt.A64.rtWords, List.cons_append, List.pairwise_cons, List.mem_cons, List.mem_append,
    forall_eq_or_imp] at hd
  have ne : ∀ {a b : BitVec 64}, Scc.Cert.Rt.A64.WordSep a b → a ≠ b := fun h e => by
    subst e; unfold Scc.Cert.Rt.A64.WordSep at h; omega
  exact ⟨ne hd.1.1, ne hd.1.2.1, ne hd.1.2.2.1, ne hd.2.1.1, ne hd.2.1.2.1, ne hd.2.2.1.1⟩

/-- **The TCB's words are none of the counters** (A8). -/
theorem tcbSep : Spike.Lib.A64.PhRec.TcbSep (RuntimeLayout.ofPlaceOK h i) :=
  Scc.Cert.Rt.A64.tcbSep_of_wordsOk (Scc.Cert.Rt.A64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeOKAt i h))

/-- **The `.rodata` range is off the stack pool** (A1's `layoutOk`,
`rodata_stackPool_of_placeOKAt`). -/
theorem rodata_stackPool_disjoint_ofPlaceOK :
    (RuntimeLayout.ofPlaceOK h i).Λ.rodata.Disjoint (RuntimeLayout.ofPlaceOK h i).Λ.stackPool :=
  rodata_stackPool_of_placeOKAt h

/-! ## `scc_rt_alloc_tcb`'s and `scc_rt_stack_take`'s phase facts -/

section Tcb

open Spike.Lib.A64.Rt.Tcb (TcbPh tcbDead tcbPcs siPcs)
open Spike.Lib.A64.Flow.Ret0.AllocTcb
open Spike.Lib.A64.PhRec (ownOf Tk)

/-- **`scc_rt_alloc_tcb`'s phase facts** of a program passing the table,
returning to `.sp2`, the header at `scc_rt_pinned`. -/
theorem tcbPh_ofPlaceOK {mc : Option MainCode}
    (hrt : rtPhOk (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog (RuntimeLayout.ofPlaceOK h i).Λ
      (rtPhTab mc) = true) :
    TcbPh (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (Tk (RuntimeLayout.ofPlaceOK h i)) (ownOf (RuntimeLayout.ofPlaceOK h i)) (RuntimeLayout.ofPlaceOK h i).lab
      (fun _ => (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.sp2L) 0#64 := by
  have hf : ∀ f ∈ Spike.Lib.A64.Rt.tcbPhTab, _ := fun f hf => factOk_of_rtPhOk (f := f) hrt
    (by simp [rtPhTab, hf])
  have hl := hlab_ofPlaceOK h i
  have hn : ∀ {d : Nat → Bool} t,
      Scc.Cert.Rt.A64.deadN (codeOf (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r →
      (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.sp2L = (RuntimeLayout.ofPlaceOK h i).lab r :=
    fun _ h => nomatch h
  have hpn : Spike.Lib.A64.Flow.Ret0.pnA (RuntimeLayout.ofPlaceOK h i).lab = (RuntimeLayout.ofPlaceOK h i).pnA :=
    (RuntimeLayout.ofPlaceOK h i).lab_pn
  have hpin : Spike.Lib.A64.Flow.Ret0.pinA (RuntimeLayout.ofPlaceOK h i).lab = (RuntimeLayout.ofPlaceOK h i).pinA :=
    (RuntimeLayout.ofPlaceOK h i).lab_pin
  obtain ⟨hnx, hnl, hnf, -, -, -⟩ := counters_ne h i
  have h13 := ph_pin h i (l := lenL) (k := 37) (v := 13) (by decide)
  have h12 := ph_pin h i (l := lenL) (k := 38) (v := 12) (by decide)
  exact {
    e := blkPh_of_factOk hl hr hn (hf (.blk Code.Tcb.fnL 0 Code.Tcb.atPro none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    entry := blkPh_of_factOk hl hr
      (fun t ht => by
        simp only [Scc.Cert.Rt.A64.deadN] at ht
        split at ht
        · next d hd =>
          simp only [tcbDead, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht ⊢
          rw [pcAt0_eq hl hd]; exact ht
        · cases ht)
      (hf (.blk Code.Tcb.entryL 0 Code.Tcb.atChk none (some ".L3_scc_rt_alloc_tcb.2_full"))
        (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    j1 := blkPh_of_factOk hl hr hn (hf (.blk Code.Tcb.entryL 4 Code.Tcb.atJ1 none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    len := blkPh_of_factOk hl hr hn (hf (.blk Code.Tcb.lenL 0 Code.Tcb.atLen none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    arg := blkPh_of_factOk hl hr hn (hf (.blk Code.Tcb.lenL 34 Code.Tcb.atArg none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    bnd := blkPh_of_factOk hl hr hn (hf (.blk Code.Tcb.lenL 38 Code.Tcb.atBnd none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    j2 := blkPh_of_factOk hl hr hn (hf (.blk Code.Tcb.lenL 47 Code.Tcb.atJ2 none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    ok2 := blkPh_of_factOk hl hr hn (hf (.blk Code.Tcb.okL 2 Code.Tcb.atOk none none)
      (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    ret := blkPh_of_factOk hl (fun _ h => by cases h; rfl) hn
      (hf (.blk Code.Tcb.okL 30 Code.Tcb.atRet (some Code.Start.sp2L) none) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    fullNe := by
      have := ne_of_factOk hl (hf (.ne Code.Tcb.entryL 4 ".L3_scc_rt_alloc_tcb.2_full" 0)
        (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      rw [Spike.Lib.A64.Flow.ofNat4_zero] at this
      exact this
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hl (hf (.step Code.Tcb.lenL 32) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.lenL 33) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.okL 0) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.okL 1) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.okL 29) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    rmwOk := ok_of_factOk hl (hf (.ok Code.Tcb.lenL 37) (by simp [Spike.Lib.A64.Rt.tcbPhTab]))
    noTk := by
      intro p hp
      simp only [tcbPcs, siPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact noTk_pin h i (l := fnL) (k := 0) (v := 13) (by decide) (by decide)
      · exact noTk_pin h i (l := entryL) (k := 0) (v := 13) (by decide) (by decide)
      · exact noTk_pin h i (l := entryL) (k := 4) (v := 13) (by decide) (by decide)
      · exact noTk_pin h i (l := lenL) (k := 0) (v := 13) (by decide) (by decide)
      · exact noTk_pin h i (l := lenL) (k := 34) (v := 13) (by decide) (by decide)
      · exact noTk_pin h i (l := lenL) (k := 37) (v := 13) (by decide) (by decide)
      · rw [rmwPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk_pin h i (l := lenL) (k := 38) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := lenL) (k := 38) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := lenL) (k := 47) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := okL) (k := 2) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := okL) (k := 30) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := lenL) (k := 32) (v := 13) (by decide) (by decide)
      · exact noTk_pin h i (l := lenL) (k := 33) (v := 13) (by decide) (by decide)
      · exact noTk_pin h i (l := okL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := okL) (k := 1) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := okL) (k := 29) (v := 12) (by decide) (by decide)
    rmwIn := ⟨(0#64).setWidth 128, by rw [rmwPc, h13, hpn]; simp [ownOf]⟩
    rmwUpd := by
      rw [rmwPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', h13, h12, hpn]
      simp [Spike.Lib.A64.Rt.ownUpdB, ownOf, hnl, hnf, hnx, Ne.symm hnl, Ne.symm hnf, Ne.symm hnx]
      rfl
    hdrNo := fun j w => by
      rw [hpin]
      exact Spike.Lib.A64.PhRec.tcb_not_own (tcbSep h i) ⟨0, by decide, by simp⟩ j w }

end Tcb

/-! ### The sites -/

/-- **The first of a mapped list's distinct values** is none of the rest's. -/
theorem ne_of_mapM_cons {f : String → Option Nat} {x : String} {rest : List String} {ss : List Nat}
    (h : (x :: rest).mapM f = some ss) (hnd : ss.Nodup) {a : Nat} (ha : f x = some a) {y : String}
    (hy : y ∈ rest) {b : Nat} (hb : f y = some b) : a ≠ b := by
  rw [List.mapM_cons, ha] at h
  cases hr : rest.mapM f with
  | none => rw [hr] at h; cases h
  | some ss' =>
    rw [hr] at h
    cases h
    rintro rfl
    exact (List.nodup_cons.mp hnd).1 (Spike.Lib.A64.PhRec.mem_of_mapM hr y hy a hb)

/-- **The take site is none of the other sites** of the record's marks. -/
theorem take_ne {y : String}
    (hy : y ∈ "scc_rt_release_site" :: [AbortKind.overflow, .heap, .stack, .writeErr, .threads].map
      Λ.abortLbl)
    {b : Nat} (hb : codeOf (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog y = some b) :
    ((RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat ≠ b := by
  obtain ⟨ss, hs, hnd⟩ := sites_nodup_of_placeOKAt h
  exact ne_of_mapM_cons hs hnd (Spike.Lib.A64.PhRec.site_ofPlaceOK h i) hy hb

section Take

open Spike.Lib.A64.Rt.Take (TakePh takePcs siPcs)
open Spike.Lib.A64.Flow.Ret0.StackTake
open Spike.Lib.A64.PhRec (ownOf Tk μ)

/-- **`scc_rt_stack_take`'s phase facts** of a program passing the table,
returning to `scc_rt_thread_init`'s `.sp0`. -/
theorem takePh_ofPlaceOK {mc : Option MainCode}
    (hrt : rtPhOk (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog (RuntimeLayout.ofPlaceOK h i).Λ
      (rtPhTab mc) = true) :
    TakePh (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (Tk (RuntimeLayout.ofPlaceOK h i)) (ownOf (RuntimeLayout.ofPlaceOK h i)) (μ (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab
      (fun _ => (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL) := by
  have hf : ∀ f ∈ Spike.Lib.A64.Rt.takePhTab, _ := fun f hf => factOk_of_rtPhOk (f := f) hrt
    (by simp [rtPhTab, hf])
  have hl := hlab_ofPlaceOK h i
  have hn : ∀ t,
      Scc.Cert.Rt.A64.deadN (codeOf (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog) none t = true →
        (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r →
      (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL =
        (RuntimeLayout.ofPlaceOK h i).lab r :=
    fun _ h => nomatch h
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA (RuntimeLayout.ofPlaceOK h i).lab = (RuntimeLayout.ofPlaceOK h i).lockA :=
    (RuntimeLayout.ofPlaceOK h i).lab_lock
  have hnx : Spike.Lib.A64.Flow.Ret0.nextA (RuntimeLayout.ofPlaceOK h i).lab = (RuntimeLayout.ofPlaceOK h i).nextA :=
    (RuntimeLayout.ofPlaceOK h i).lab_next
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := counters_ne h i
  have hs12 := ph_pin h i (l := spinL) (k := 2) (v := 12) (by decide)
  have hs14 := ph_pin h i (l := spinL) (k := 3) (v := 14) (by decide)
  have hb14 := ph_pin h i (l := bumpL) (k := 5) (v := 14) (by decide)
  have hb12 := ph_pin h i (l := bumpL) (k := 6) (v := 12) (by decide)
  have hn12 := ph_pin h i (l := bumpL) (k := 11) (v := 12) (by decide)
  have hn8 := ph_pin h i (l := bumpL) (k := 12) (v := 8) (by decide)
  have ht8 : ph (RuntimeLayout.ofPlaceOK h i) ((RuntimeLayout.ofPlaceOK h i).lab siteL).toBitVec.toNat = 8 := by
    have := ph_pin h i (l := siteL) (k := 0) (v := 8) (by decide)
    rwa [Spike.Lib.A64.Flow.ofNat4_zero] at this
  have ht0 : ph (RuntimeLayout.ofPlaceOK h i) ((RuntimeLayout.ofPlaceOK h i).lab siteL + Int64.ofNat 4).toBitVec.toNat
      = 0 := by
    have := ph_pin h i (l := siteL) (k := 1) (v := 0) (by decide)
    rwa [show Int64.ofNat (4 * 1) = Int64.ofNat 4 from rfl] at this
  exact {
    e := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.fnL 0 Code.Take.stPro none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    entry := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.entryL 0 Code.Take.stInit none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    cls := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.clsL 0 Code.Take.stCls none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    j1 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.clsL 4 Code.Take.stJ1 none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    d2 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.doneL 2 Code.Take.stFreeN none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    d9 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.doneL 9 Code.Take.stFree none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    d16 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.doneL 16 Code.Take.stLock none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    sp0 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.spinL 0 Code.Take.stSwp none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    sp3 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.spinL 3 Code.Take.stSpin none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    lk0 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.lockedL 0 Code.Take.stLdN none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    lk2 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.lockedL 2 Code.Take.stEmpty none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    b2 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.bumpL 2 Code.Take.stUnl none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    b8 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.bumpL 8 Code.Take.stAdd none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    b12 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.bumpL 12 Code.Take.stBnd none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    b21 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.bumpL 21 Code.Take.stJ2 none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    ok2 := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.okL 2 Code.Take.stOk none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    tk := blkPh_of_factOk hl hr hn (hf (.blk Code.Take.takenL 0 Code.Take.stSite none none)
      (by simp [Spike.Lib.A64.Rt.takePhTab]))
    ret := blkPh_of_factOk hl (fun _ h => by cases h; rfl) hn
      (hf (.blk Code.Take.siteL 1 Code.Take.stRet (some Code.Ti.spL) none) (by simp [Spike.Lib.A64.Rt.takePhTab]))
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hl (hf (.step Code.Take.doneL 0) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.doneL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.doneL 7) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.doneL 8) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.doneL 14) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.doneL 15) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.bumpL 0) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.bumpL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.bumpL 6) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.bumpL 7) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.okL 0) (by simp [Spike.Lib.A64.Rt.takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.okL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))
    swpOk := ok_of_factOk hl (hf (.ok Code.Take.spinL 2) (by simp [Spike.Lib.A64.Rt.takePhTab]))
    ldnOk := (step_of_factOk hl (hf (.step Code.Take.lockedL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))).1
    unlOk := ok_of_factOk hl (hf (.ok Code.Take.bumpL 5) (by simp [Spike.Lib.A64.Rt.takePhTab]))
    nxtOk := ok_of_factOk hl (hf (.ok Code.Take.bumpL 11) (by simp [Spike.Lib.A64.Rt.takePhTab]))
    ldnPh := (step_of_factOk hl (hf (.step Code.Take.lockedL 1) (by simp [Spike.Lib.A64.Rt.takePhTab]))).2
    noTk := by
      intro p hp
      simp only [takePcs, siPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact noTk_pin h i (l := fnL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := entryL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := clsL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := clsL) (k := 4) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := doneL) (k := 2) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := doneL) (k := 9) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := doneL) (k := 16) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := spinL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := spinL) (k := 2) (v := 12) (by decide) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk_pin h i (l := spinL) (k := 3) (v := 14) (by decide) (by decide)
      · exact noTk_pin h i (l := spinL) (k := 3) (v := 14) (by decide) (by decide)
      · exact noTk_pin h i (l := lockedL) (k := 0) (v := 14) (by decide) (by decide)
      · exact noTk_pin h i (l := lockedL) (k := 1) (v := 14) (by decide) (by decide)
      · exact noTk_pin h i (l := lockedL) (k := 2) (v := 14) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 2) (v := 14) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 5) (v := 14) (by decide) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk_pin h i (l := bumpL) (k := 6) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 8) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 11) (v := 12) (by decide) (by decide)
      · rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
        exact noTk_pin h i (l := bumpL) (k := 12) (v := 8) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 12) (v := 8) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 21) (v := 8) (by decide) (by decide)
      · exact noTk_pin h i (l := okL) (k := 2) (v := 8) (by decide) (by decide)
      · exact noTk_pin h i (l := takenL) (k := 0) (v := 8) (by decide) (by decide)
      · exact noTk_pin h i (l := siteL) (k := 0) (v := 8) (by decide) (by decide)
      · exact noTk_pin h i (l := doneL) (k := 0) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := doneL) (k := 1) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := doneL) (k := 7) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := doneL) (k := 8) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := doneL) (k := 14) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := doneL) (k := 15) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 0) (v := 14) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 1) (v := 14) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 6) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := bumpL) (k := 7) (v := 12) (by decide) (by decide)
      · exact noTk_pin h i (l := okL) (k := 0) (v := 8) (by decide) (by decide)
      · exact noTk_pin h i (l := okL) (k := 1) (v := 8) (by decide) (by decide)
    swpIn := ⟨(0#64).setWidth 128, by rw [swpPc, hs12, hlk]; simp [ownOf]⟩
    swpUpd := by
      rw [swpPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hs12, hs14, hlk]
      simp [Spike.Lib.A64.Rt.ownUpdB, ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6]
    unlIn := ⟨(1#64).setWidth 128, by rw [unlPc, hb14, hlk]; simp [ownOf]⟩
    unlUpd := by
      rw [unlPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hb14, hb12, hlk]
      simp [Spike.Lib.A64.Rt.ownUpdB, ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6]
    nxtIn := ⟨(0#64).setWidth 128, by rw [nextPc, hn12, hnx]; simp [ownOf]⟩
    nxtUpd := by
      rw [nextPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', hn12, hn8, hnx]
      simp [Spike.Lib.A64.Rt.ownUpdB, ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6]
      rfl
    siteRel := fun a ha => take_ne h i (List.mem_cons_self ..) ha
    siteAb := fun k a ha => take_ne h i (y := Λ.abortLbl k)
      (by cases k <;> simp) ha
    siteAt := Spike.Lib.A64.PhRec.site_ofPlaceOK h i
    siteOwn := by rw [ht8, ht0]; rfl
    tk4 := fun s hs => by unfold Tk; rw [hs, ht0] }

end Take

end Spike.Lib.A64.Rt.PhRecOf
