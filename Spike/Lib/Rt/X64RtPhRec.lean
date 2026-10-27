/-
**The runtime's phase structures at an output passing `placeOK`**
(x86-64): A6's table (`rtPh_of_placeOKAt`, `Spike/Lib/Rt/X64RtPhTab.lean`)
and A11's (`mainPh_of_placeOKAt`, `scc_rt_main`'s at `mcOf`) give the hand
proofs' phase structures at the record's `okPc`/`ph` and labels. The twin
of `Spike/Lib/Rt/A64RtPhRec.lean`; each structure is stated from any
checked table holding the function's facts (`…_of_tab`), and from
`placeOK` itself (`…_ofPlaceOK`):

- `hlab_ofPlaceOK`: the record's labels agree with `codeLabel` where it
  resolves (the loader's, `label_threadAt_of_codeLabel`);
- `swPh_ofPlaceOK`: the switch's (`SwPh`), from A6;
- `mainPh_ofPlaceOK`: `scc_rt_main`'s at `mc` (`MainPh`), from A11's
  `mainPhTab mc` (x86-64's A6 table is `rtPhTab none`);
- `tiPh_ofPlaceOK`: `scc_rt_thread_init`'s (`TiPh`), returning to `.x1`;
  the table names its pcs after the call from `.entry` + 12, `.x7` by
  A11's gap (`threadInitIn`); its prologue and call before the take
  (phase `12`); `tiPhAt_ofPlaceOK` the same whatever the tail, its return
  point at `tiOf` of the tail (`TiPhAt`: `.x7`, or `.x8` after a setup
  block);
- `tcbPh_ofPlaceOK`, `takePh_ofPlaceOK`: `scc_rt_alloc_tcb`'s (`TcbPh`,
  returning to `.Lscc_rt_start.x0`, the header at `scc_rt_pinned`) and
  `scc_rt_stack_take`'s (`TakePh`, returning to `.x7` = `.entry` + 12),
  their phases at the pcs before the take and at the atomic accesses' ends
  (A6's `tkPhTab`, `ph_tk`), the owned counters distinct and the TCB off
  them (A8, `counters_ne`, `tcbSep`), the take site none of the other sites
  (`take_ne`); `takePhAt_ofPlaceOK` the same whatever the tail, returning
  to `tiOf` of the tail;
- `rodata_stackPool_disjoint_ofPlaceOK`: the `.rodata` range off the stack
  pool (A1's `layoutOk`, `rodata_stackPool_of_placeOKAt`), the take's premise.
-/
import Spike.Lib.Rt.X64RtPhOfTab
import Spike.Lib.Rt.X64RtPhTab
import Spike.Lib.Rt.X64RtCode
import Spike.Lib.X64PhRec
import Spike.Lib.Rt.X64RtMainU
import Spike.Lib.Rt.X64RtCodeSetup

namespace Spike.Lib.X64.Rt.PhRecOf

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Sem.X64 (pcOf codeLabel)
open Scc.Cert.Rt.X64 (factOk_of_rtPhOk rtPhOk deadN)
open Spike.Lib.X64.Rt (RuntimeLayout MainCode rtPhTab mainPhTab swPhTab tiPhTab)
open Spike.Lib.X64.Rt.PhOfTab
open Spike.Lib.X64.PhRec (ph okPc Tk)
open Spike.Lib.X64.Rt.MainU (MainPh SwPh)
open Scc.Sem (AbortKind)
open Scc.Cert.Rt.X64 (PhFact)
open Spike.Lib.X64.Rt (tcbPhTab takePhTab tkPhTab tcbTkRows takeTkRows tcbFullL)

section Tab

variable (L : RuntimeLayout)
  (hlab : ∀ l a, codeLabel L.Λ.code.lo L.prog l = some a → L.lab l = Int64.ofNat a)
  {tab : List Scc.Cert.Rt.X64.PhFact} (hrt : rtPhOk L.Λ.code.lo L.prog L.Λ tab = true)

include hlab hrt

omit hlab hrt in
/-- No dead target: the empty set holds them. -/
private theorem dead_none : ∀ t, deadN (codeLabel L.Λ.code.lo L.prog) none t = true → (fun _ => false) t = true :=
  fun _ h => by simp [deadN] at h

omit hlab hrt in
/-- No return point: any `rapc`. -/
private theorem ra_none {rapc : Int64} :
    ∀ r o', (none : Option (String × Nat)) = some (r, o') → rapc = L.lab r + Int64.ofNat o' :=
  fun _ _ h => by cases h

/-- **The switch's phase facts** of a checked table holding `swPhTab`. -/
theorem swPh_of_tab (hsub : ∀ f ∈ swPhTab, f ∈ tab) : SwPh (okPc L) (ph L) L.lab where
  sw := step_of_factOk hlab (factOk_of_rtPhOk hrt (hsub (.step Code.Start.x1L 28 3) (by simp [swPhTab])))
  xor := step_of_factOk hlab (factOk_of_rtPhOk hrt (hsub (.step Code.Start.x1L 31 2) (by simp [swPhTab])))
  main := blkPh_of_factOk hlab (ra_none L) (dead_none L)
    (factOk_of_rtPhOk hrt (hsub (.blk Code.Start.x1L 33 Code.Start.startMain none none) (by simp [swPhTab])))

/-- **`scc_rt_main`'s phase facts at `mc`** of a checked table holding
`mainPhTab mc`. -/
theorem mainPh_of_tab {mc : MainCode} (hsub : ∀ f ∈ mainPhTab mc, f ∈ tab) : MainPh (okPc L) (ph L) L.lab mc := by
  have hf : ∀ f ∈ mainPhTab mc, _ := fun f hf => factOk_of_rtPhOk hrt (hsub f hf)
  have hn := dead_none L
  exact {
    hd := blkPh_of_factOk hlab (ra_none L) hn (hf _ (by simp [mainPhTab]))
    lea := blkPh_of_factOk hlab (ra_none L) hn (hf _ (by simp [mainPhTab]))
    ld := step_of_factOk hlab (hf (.step mc.sc mc.zl mc.zf) (by simp [mainPhTab]))
    cmp := blkPh_of_factOk hlab (ra_none L) hn (hf _ (by simp [mainPhTab]))
    fr := blkPh_of_factOk hlab (ra_none L) hn (hf _ (by simp [mainPhTab]))
    call := blkPh_of_factOk hlab (ra_none L) hn (hf _ (by simp [mainPhTab]))
    ex := blkPh_of_factOk hlab (ra_none L) hn (hf _ (by simp [mainPhTab]))
    svc := step_of_factOk hlab (hf (.step mc.sp0 (mc.ze0 + mc.ze1 + mc.ze2) 2) (by simp [mainPhTab])) }

open Spike.Lib.X64.Rt.Ti (TiPhAt stPcsAt preTkPcs) in
open Spike.Lib.X64.Flow.Ret0.ThreadInit in
/-- **`scc_rt_thread_init`'s phase facts with its return point at `x`** of
a checked table holding `tiPhTab` (its rows are named from `.entry`, so the
table is the same whatever the program numbers the return point),
returning to `.x1`, with `x` at `.entry` + 12 (`hx7`). -/
theorem tiPhAt_of_tab (x : Label) (hsub : ∀ f ∈ tiPhTab, f ∈ tab) (hx7 : L.lab x = L.lab entryL + Int64.ofNat 12) :
    TiPhAt (okPc L) (ph L) (Tk L) L.lab (fun _ => L.lab Code.Start.x1L) x := by
  have hf : ∀ f ∈ tiPhTab, _ := fun f hf => factOk_of_rtPhOk hrt (hsub f hf)
  have hn := dead_none L
  have e7 : ∀ o, L.lab x + Int64.ofNat o = L.lab entryL + Int64.ofNat (12 + o) := fun o => by
    rw [hx7, Spike.Lib.X64.Flow.ofNat_add']
  have h12 : ∀ p ∈ preTkPcs L.lab, ph L p.toBitVec.toNat = 12 := by
    intro p hp
    simp only [preTkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ph_of_factOk hlab (hf (.ph Code.Ti.fnL 0 12) (by simp [tiPhTab]))
    · exact ph_of_factOk hlab (hf (.ph Code.Ti.entryL 0 12) (by simp [tiPhTab]))
    · exact ph_of_factOk hlab (hf (.ph Code.Ti.entryL 7 12) (by simp [tiPhTab]))
  exact {
    e := blkPh_of_factOk hlab (ra_none L) hn (hf (.blk Code.Ti.fnL 0 Code.Ti.tiPro none none) (by simp [tiPhTab]))
    entry := blkPh_of_factOk hlab (ra_none L) hn
      (hf (.blk Code.Ti.entryL 0 Code.Ti.tiArg none none) (by simp [tiPhTab]))
    c7 := blkPh_of_factOk hlab (ra_none L) hn
      (hf (.blk Code.Ti.entryL 7 Code.Ti.callBlk none none) (by simp [tiPhTab]))
    x7 := by
      rw [e7]; exact blkPh_of_factOk hlab (ra_none L) hn
        (hf (.blk Code.Ti.entryL (12 + 0) Code.Ti.tiSp none none) (by simp [tiPhTab]))
    f1 := by
      rw [e7]; exact blkPh_of_factOk hlab (ra_none L) hn
        (hf (.blk Code.Ti.entryL (12 + 51) Code.Ti.tiF1 none none) (by simp [tiPhTab]))
    f2 := by
      rw [e7]; exact blkPh_of_factOk hlab (ra_none L) hn
        (hf (.blk Code.Ti.entryL (12 + 63) Code.Ti.tiZ none none) (by simp [tiPhTab]))
    f3 := by
      rw [e7]; exact blkPh_of_factOk hlab (ra_none L) hn
        (hf (.blk Code.Ti.entryL (12 + 78) Code.Ti.tiZ none none) (by simp [tiPhTab]))
    f4 := by
      rw [e7]; exact blkPh_of_factOk hlab (ra_none L) hn
        (hf (.blk Code.Ti.entryL (12 + 93) Code.Ti.tiF4 none none) (by simp [tiPhTab]))
    f5 := by
      rw [e7]; exact blkPh_of_factOk hlab (ra_none L) hn
        (hf (.blk Code.Ti.entryL (12 + 105) Code.Ti.tiF5 none none) (by simp [tiPhTab]))
    ret := by
      rw [e7]; exact blkPh_of_factOk hlab (fun _ _ h => by cases h; exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm)
        hn (hf (.blk Code.Ti.entryL (12 + 117) Code.Ti.tiRet (some (Code.Start.x1L, 0)) none) (by simp [tiPhTab]))
    st := by
      intro pz hp
      simp only [stPcsAt, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [e7]; exact step_of_factOk hlab (hf (.step Code.Ti.entryL (12 + 48) 3) (by simp [tiPhTab]))
      · rw [e7]; exact step_of_factOk hlab (hf (.step Code.Ti.entryL (12 + 59) 4) (by simp [tiPhTab]))
      · rw [e7]; exact step_of_factOk hlab (hf (.step Code.Ti.entryL (12 + 74) 4) (by simp [tiPhTab]))
      · rw [e7]; exact step_of_factOk hlab (hf (.step Code.Ti.entryL (12 + 89) 4) (by simp [tiPhTab]))
      · rw [e7]; exact step_of_factOk hlab (hf (.step Code.Ti.entryL (12 + 101) 4) (by simp [tiPhTab]))
      · rw [e7]; exact step_of_factOk hlab (hf (.step Code.Ti.entryL (12 + 113) 4) (by simp [tiPhTab]))
    noTk := fun p hp s hs hT => by
      unfold Tk at hT; rw [hs, h12 p hp] at hT; cases hT }

open Spike.Lib.X64.Rt.Ti (TiPh) in
open Spike.Lib.X64.Flow.Ret0.ThreadInit in
/-- **`scc_rt_thread_init`'s phase facts** of a checked table holding
`tiPhTab`, returning to `.x1`, with `.x7` at `.entry` + 12 (`hx7`). -/
theorem tiPh_of_tab (hsub : ∀ f ∈ tiPhTab, f ∈ tab) (hx7 : L.lab x7L = L.lab entryL + Int64.ofNat 12) :
    TiPh (okPc L) (ph L) (Tk L) L.lab (fun _ => L.lab Code.Start.x1L) :=
  (tiPhAt_of_tab L hlab hrt x7L hsub hx7).toTiPh

end Tab

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- **The record's labels agree with `codeLabel`** where it resolves. -/
theorem hlab_ofPlaceOK : ∀ l a, codeLabel (Ly).Λ.code.lo (Ly).prog l = some a → (Ly).lab l = Int64.ofNat a :=
  fun _ _ ha => @Scc.Cert.Rt.X64.label_threadAt_of_codeLabel_below Scc.Sem.Entry.linux _ _ _ (Ly).valid _ _
      (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha

/-- **The switch's phase facts** at an output passing `placeOK` (A6). -/
theorem swPh_ofPlaceOK : SwPh (okPc (Ly)) (ph (Ly)) (Ly).lab :=
  swPh_of_tab (Ly) (hlab_ofPlaceOK h i) (rtPh_of_placeOKAt h) fun _ hf => by
    simp only [rtPhTab, List.mem_append]; simp [hf]

/-- **`scc_rt_main`'s phase facts at `mc`** at an output passing
`placeOK` whose tail's shape gives `mc` (A11). -/
theorem mainPh_ofPlaceOK {mc : MainCode} (hs : mcOf o.place.tail = some mc) :
    MainPh (okPc (Ly)) (ph (Ly)) (Ly).lab mc :=
  mainPh_of_tab (Ly) (hlab_ofPlaceOK h i) (mainPh_of_placeOKAt h hs) fun _ hf => hf

/-- **`scc_rt_main`'s phase facts at `bareMC`**, on a bare tail. -/
theorem mainPh_bare_ofPlaceOK (hs : o.place.tail = .bare) :
    MainPh (okPc (Ly)) (ph (Ly)) (Ly).lab Spike.Lib.X64.Rt.bareMC :=
  mainPh_ofPlaceOK h i (by rw [hs]; rfl)

open Spike.Lib.X64.Rt.Ti (TiPh) in
/-- **`scc_rt_thread_init`'s phase facts** at an output passing `placeOK`,
returning to `.x1` (A6; `.x7`'s gap from A11). -/
theorem tiPh_ofPlaceOK (hs : o.place.tail = .bare) :
    TiPh (okPc (Ly)) (ph (Ly)) (Tk (Ly)) (Ly).lab (fun _ => (Ly).lab Code.Start.x1L) := by
  have hin := (Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)).ti
  simp only [Spike.Lib.X64.Flow.Ret0.ThreadInit.threadInitIn, Bool.and_eq_true] at hin
  exact tiPh_of_tab (Ly) (hlab_ofPlaceOK h i) (rtPh_of_placeOKAt h)
    (fun _ hf => by simp only [rtPhTab, List.mem_append]; simp [hf])
    (Scc.Cert.Rt.X64.label_labelGapB (Ly).lays hin.1.1.1.1.1.1.1.1.2)

open Spike.Lib.X64.Rt.Ti (TiPhAt) in
/-- **`scc_rt_thread_init`'s phase facts at an output passing `placeOK`,
whatever the tail**, its return point at `tiOf` of the tail (`.x7` or
`.x8`; A6, and the gap from A11's `threadInitInAt_of_placeOKAt`), returning
to `.x1`. At a bare tail it is `tiPh_ofPlaceOK` (`TiPhAt.toTiPh`). -/
theorem tiPhAt_ofPlaceOK :
    TiPhAt (okPc (Ly)) (ph (Ly)) (Tk (Ly)) (Ly).lab (fun _ => (Ly).lab Code.Start.x1L)
      (Spike.Lib.X64.Rt.tiOf o.place.tail) :=
  tiPhAt_of_tab (Ly) (hlab_ofPlaceOK h i) (rtPh_of_placeOKAt h) _
    (fun _ hf => by simp only [rtPhTab, List.mem_append]; simp [hf])
    (Scc.Cert.Rt.X64.label_labelGapB (Ly).lays
      (Spike.Lib.X64.Rt.gap_of_threadInitInAt (Spike.Lib.X64.Rt.threadInitInAt_of_placeOKAt h)))


/-! ## The phase indices, the words and the sites

A row of A6's `tkPhTab` gives the phase index at its pc of the record; A8's
words are pairwise disjoint, so the counters are distinct and the TCB's
words none of them (`TcbSep`). -/

/-- **A row of `tkPhTab`'s phase index** at the record's labels (A6). -/
theorem ph_tk {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ tcbTkRows ++ takeTkRows ++ [(Code.Take.siteL, 1, 0)]) :
    ph (Ly) ((Ly).lab l + Int64.ofNat k).toBitVec.toNat = v := by
  have hm : PhFact.ph l k v ∈ rtPhTab none :=
    List.mem_append.mpr (.inl (List.mem_append.mpr (.inr (List.mem_map.mpr ⟨(l, k, v), hr, rfl⟩))))
  exact ph_of_factOk (hlab_ofPlaceOK h i) (factOk_of_rtPhOk (rtPh_of_placeOKAt h) hm)

/-- **A row of `tkPhTab` in a phase with bit 3 set** (before the take): no
take there. -/
theorem noTk_tk {l : String} {k v : Nat}
    (hr : (l, k, v) ∈ tcbTkRows ++ takeTkRows ++ [(Code.Take.siteL, 1, 0)]) (hv : v / 8 % 2 = 1) :
    ∀ s : State, pcOf s = ((Ly).lab l + Int64.ofNat k).toBitVec.toNat → ¬ Tk (Ly) s := by
  intro s hs hT
  unfold Tk at hT
  rw [hs, ph_tk h i hr] at hT
  omega

/-- **The record's words are pairwise disjoint** (A8). -/
theorem words_disj :
    (Scc.Cert.Rt.X64.rtWords (Ly).pinA (Ly).pnA (Ly).nextA (Ly).lockA (Ly).freeNA).Pairwise
      Scc.Cert.Rt.X64.WordSep :=
  Scc.Cert.Rt.X64.words_disj_of_wordsOk (Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeOKAt i h))

/-- **The counters are distinct.** -/
theorem counters_ne :
    (Ly).pnA ≠ (Ly).nextA ∧ (Ly).pnA ≠ (Ly).lockA ∧ (Ly).pnA ≠ (Ly).freeNA ∧ (Ly).nextA ≠ (Ly).lockA ∧
      (Ly).nextA ≠ (Ly).freeNA ∧ (Ly).lockA ≠ (Ly).freeNA := by
  have hd := words_disj h i
  simp only [Scc.Cert.Rt.X64.rtWords, List.cons_append, List.pairwise_cons, List.mem_cons, List.mem_append,
    forall_eq_or_imp] at hd
  have ne : ∀ {a b : BitVec 64}, Scc.Cert.Rt.X64.WordSep a b → a ≠ b := fun h e => by
    subst e; unfold Scc.Cert.Rt.X64.WordSep at h; omega
  exact ⟨ne hd.1.1, ne hd.1.2.1, ne hd.1.2.2.1, ne hd.2.1.1, ne hd.2.1.2.1, ne hd.2.2.1.1⟩

/-- **The TCB's words are none of the counters** (A8). -/
theorem tcbSep : Spike.Lib.X64.PhRec.TcbSep (Ly) :=
  Scc.Cert.Rt.X64.tcbSep_of_wordsOk (Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeOKAt i h))

/-- **The `.rodata` range is off the stack pool** (A1's `layoutOk`,
`rodata_stackPool_of_placeOKAt`), the take's premise. -/
theorem rodata_stackPool_disjoint_ofPlaceOK : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool :=
  rodata_stackPool_of_placeOKAt h

/-! ## `scc_rt_alloc_tcb`'s and `scc_rt_stack_take`'s phase facts -/

open Spike.Lib.X64.Rt.Tcb (TcbPh tcbDead tcbPcs blkPcs stepPcs) in
open Spike.Lib.X64.Flow.Ret0.AllocTcb in
open Spike.Lib.X64.PhRec (ownOf) in
/-- **`scc_rt_alloc_tcb`'s phase facts** at an output passing `placeOK`
(A6, A8), returning to `.Lscc_rt_start.x0`, the header at `scc_rt_pinned`. -/
theorem tcbPh_ofPlaceOK :
    TcbPh (okPc (Ly)) (ph (Ly)) (Tk (Ly)) (ownOf (Ly)) (Ly).lab (fun _ => (Ly).lab Code.Start.x0L) 0#64 := by
  have hrt : rtPhOk (Ly).Λ.code.lo (Ly).prog (Ly).Λ (rtPhTab none) = true := rtPh_of_placeOKAt h
  have hf : ∀ f ∈ tcbPhTab, _ := fun f hf => factOk_of_rtPhOk hrt (f := f)
    (by simp only [rtPhTab, List.mem_append]; simp [hf])
  have hl := hlab_ofPlaceOK h i
  have hn : ∀ {d : Nat → Bool} t, deadN (codeLabel (Ly).Λ.code.lo (Ly).prog) none t = true → d t = true :=
    fun _ h => by simp [deadN] at h
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA (Ly).lab = (Ly).pnA := (Ly).lab_pn
  have hpin : Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab = (Ly).pinA := (Ly).lab_pin
  obtain ⟨hnx, hnl, hnf, -, -, -⟩ := counters_ne h i
  have h13 := ph_tk h i (l := lenL) (k := 158) (v := 13) (by decide)
  have h12 := ph_tk h i (l := lenL) (k := 163) (v := 12) (by decide)
  have e5 : rmwPc (Ly).lab + Int64.ofNat 5 = (Ly).lab lenL + Int64.ofNat 163 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 158 5).symm
  exact {
    e := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.fnL 0 Code.Tcb.atPro none none) (by simp [tcbPhTab]))
    entry := blkPh_of_factOk hl (ra_none (Ly))
      (fun t ht => by
        simp only [deadN] at ht
        split at ht
        · next d hd =>
          simp only [tcbDead, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht ⊢
          exact ht.trans (pcAt0_eq hl hd).symm
        · cases ht)
      (hf (.blk Code.Tcb.entryL 0 Code.Tcb.atChk none (some tcbFullL)) (by simp [tcbPhTab]))
    j1 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.entryL 20 Code.Tcb.atJ1 none none) (by simp [tcbPhTab]))
    len := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 0 Code.Tcb.atL0 none none) (by simp [tcbPhTab]))
    l1 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 14 Code.Tcb.atL1 none none) (by simp [tcbPhTab]))
    l2 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 32 Code.Tcb.atL2 none none) (by simp [tcbPhTab]))
    l3 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 50 Code.Tcb.atL3 none none) (by simp [tcbPhTab]))
    l4 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 68 Code.Tcb.atL4 none none) (by simp [tcbPhTab]))
    l5 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 99 Code.Tcb.atL5 none none) (by simp [tcbPhTab]))
    l6 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 135 Code.Tcb.atL6 none none) (by simp [tcbPhTab]))
    arg := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 146 Code.Tcb.atArg none none) (by simp [tcbPhTab]))
    bnd := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 163 Code.Tcb.atBnd none none) (by simp [tcbPhTab]))
    j2 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.lenL 198 Code.Tcb.atJ2 none none) (by simp [tcbPhTab]))
    o1 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.okL 7 Code.Tcb.atO1 none none) (by simp [tcbPhTab]))
    o2 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.okL 38 Code.Tcb.atO2 none none) (by simp [tcbPhTab]))
    o3 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.okL 56 Code.Tcb.atO3 none none) (by simp [tcbPhTab]))
    o4 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.okL 77 Code.Tcb.atO4 none none) (by simp [tcbPhTab]))
    o5 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Tcb.okL 98 Code.Tcb.atO5 none none) (by simp [tcbPhTab]))
    ret := blkPh_of_factOk hl (fun _ _ h => by cases h; exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm) hn
      (hf (.blk Code.Tcb.okL 143 Code.Tcb.atRet (some (Code.Start.x0L, 0)) none) (by simp [tcbPhTab]))
    fullNe := by
      have := ne_of_factOk hl (hf (.ne Code.Tcb.entryL 20 tcbFullL 0) (by simp [tcbPhTab]))
      rw [Spike.Lib.X64.Flow.ofNat_zero'] at this
      exact this
    step := by
      intro pz hp
      simp only [stepPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hl (hf (.step Code.Tcb.lenL 11 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.lenL 29 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.lenL 47 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.lenL 65 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.lenL 95 4) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.lenL 132 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.lenL 139 7) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.okL 0 7) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.okL 34 4) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.okL 53 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.okL 74 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.okL 95 3) (by simp [tcbPhTab]))
      · exact step_of_factOk hl (hf (.step Code.Tcb.okL 140 3) (by simp [tcbPhTab]))
    rmwOk := ok_of_factOk hl (hf (.ok Code.Tcb.lenL 158) (by simp [tcbPhTab]))
    noTk := by
      intro p hp
      simp only [tcbPcs, blkPcs, stepPcs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 13) (by decide) (by decide)
      · rw [e5]; exact noTk_tk h i (v := 12) (by decide) (by decide)
    rmwIn := ⟨(0#64).setWidth 128, by rw [h13, hpn]; simp [ownOf]⟩
    rmwUpd := by
      rw [e5, h13, h12, hpn]
      simp [Spike.Lib.X64.Rt.ownUpdB, ownOf, hnl, hnf, hnx, Ne.symm hnl, Ne.symm hnf, Ne.symm hnx]
    hdrNo := fun j w => by
      rw [hpin]
      exact Spike.Lib.X64.PhRec.tcb_not_own (tcbSep h i) ⟨0, by decide, by simp⟩ j w }

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
    exact (List.nodup_cons.mp hnd).1 (Spike.Lib.X64.PhRec.mem_of_mapM hr y hy a hb)

/-- **The take site is none of the other sites** of the record's marks. -/
theorem take_ne {y : String}
    (hy : y ∈ "scc_rt_release_site" :: [AbortKind.overflow, .heap, .stack, .writeErr, .threads].map
      Λ.abortLbl)
    {b : Nat} (hb : codeLabel (Ly).Λ.code.lo (Ly).prog y = some b) :
    ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat ≠ b := by
  obtain ⟨ss, hs, hnd⟩ := sites_nodup_of_placeOKAt h
  exact ne_of_mapM_cons hs hnd (Spike.Lib.X64.PhRec.site_ofPlaceOK h i) hy hb

open Spike.Lib.X64.Rt.Take (TakePh takePcs siPcs) in
open Spike.Lib.X64.Flow.Ret0.StackTake in
open Spike.Lib.X64.PhRec (ownOf μ) in
/-- **`scc_rt_stack_take`'s phase facts at an output passing `placeOK`,
whatever the tail** (A6, A8, the sites distinct), returning to
`scc_rt_thread_init`'s return point `tiOf` of the tail (`.x7` or `.x8`,
`.entry` + 12, A11's gap). -/
theorem takePhAt_ofPlaceOK :
    TakePh (okPc (Ly)) (ph (Ly)) (Tk (Ly)) (ownOf (Ly)) (μ (Ly)) (Ly).lab
      (fun _ => (Ly).lab (Spike.Lib.X64.Rt.tiOf o.place.tail)) := by
  have hrt : rtPhOk (Ly).Λ.code.lo (Ly).prog (Ly).Λ (rtPhTab none) = true := rtPh_of_placeOKAt h
  have hf : ∀ f ∈ takePhTab, _ := fun f hf => factOk_of_rtPhOk hrt (f := f)
    (by simp only [rtPhTab, List.mem_append]; simp [hf])
  have hl := hlab_ofPlaceOK h i
  have hn := dead_none (Ly)
  have hx7 : (Ly).lab (Spike.Lib.X64.Rt.tiOf o.place.tail) = (Ly).lab Code.Ti.entryL + Int64.ofNat 12 :=
    Scc.Cert.Rt.X64.label_labelGapB (Ly).lays
      (Spike.Lib.X64.Rt.gap_of_threadInitInAt (Spike.Lib.X64.Rt.threadInitInAt_of_placeOKAt h))
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA (Ly).lab = (Ly).lockA := (Ly).lab_lock
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA (Ly).lab = (Ly).nextA := (Ly).lab_next
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := counters_ne h i
  have hs12 := ph_tk h i (l := spinL) (k := 11) (v := 12) (by decide)
  have hs14 := ph_tk h i (l := spinL) (k := 14) (v := 14) (by decide)
  have hb14 := ph_tk h i (l := bumpL) (k := 28) (v := 14) (by decide)
  have hb12 := ph_tk h i (l := bumpL) (k := 31) (v := 12) (by decide)
  have hn12 := ph_tk h i (l := bumpL) (k := 56) (v := 12) (by decide)
  have hn8 := ph_tk h i (l := bumpL) (k := 61) (v := 8) (by decide)
  have ht8 : ph (Ly) ((Ly).lab siteL).toBitVec.toNat = 8 := by
    have := ph_tk h i (l := siteL) (k := 0) (v := 8) (by decide)
    rwa [Spike.Lib.X64.Flow.ofNat_zero'] at this
  have ht0 := ph_tk h i (l := siteL) (k := 1) (v := 0) (by decide)
  have es3 : swpPc (Ly).lab + Int64.ofNat 3 = (Ly).lab spinL + Int64.ofNat 14 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 11 3).symm
  have eu3 : unlPc (Ly).lab + Int64.ofNat 3 = (Ly).lab bumpL + Int64.ofNat 31 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 28 3).symm
  have en5 : nextPc (Ly).lab + Int64.ofNat 5 = (Ly).lab bumpL + Int64.ofNat 61 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 56 5).symm
  exact {
    e := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.fnL 0 Code.Take.stPro none none) (by simp [takePhTab]))
    entry := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.entryL 0 Code.Take.stInit none none) (by simp [takePhTab]))
    cls := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.clsL 0 Code.Take.stCls none none) (by simp [takePhTab]))
    j1 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.clsL 13 Code.Take.stJ1 none none) (by simp [takePhTab]))
    d7 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.doneL 7 Code.Take.stFreeN none none) (by simp [takePhTab]))
    d33 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.doneL 33 Code.Take.stFree none none) (by simp [takePhTab]))
    d59 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.doneL 59 Code.Take.stLock none none) (by simp [takePhTab]))
    sp0 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.spinL 0 Code.Take.stSwp none none) (by simp [takePhTab]))
    sp14 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.spinL 14 Code.Take.stSpin none none) (by simp [takePhTab]))
    lk0 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.lockedL 0 Code.Take.stLdN none none) (by simp [takePhTab]))
    lk7 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.lockedL 7 Code.Take.stEmpty none none) (by simp [takePhTab]))
    b7 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.bumpL 7 Code.Take.stUnl none none) (by simp [takePhTab]))
    b38 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.bumpL 38 Code.Take.stAdd none none) (by simp [takePhTab]))
    b61 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.bumpL 61 Code.Take.stBnd none none) (by simp [takePhTab]))
    b108 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.bumpL 108 Code.Take.stJ2 none none) (by simp [takePhTab]))
    ok7 := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.okL 7 Code.Take.stOk none none) (by simp [takePhTab]))
    tk := blkPh_of_factOk hl (ra_none (Ly)) hn
      (hf (.blk Code.Take.takenL 0 Code.Take.stSite none none) (by simp [takePhTab]))
    ret := blkPh_of_factOk hl (fun _ _ h => by cases h; exact hx7) hn
      (hf (.blk Code.Take.siteL 1 Code.Take.stRet (some (Code.Ti.entryL, 12)) none) (by simp [takePhTab]))
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hl (hf (.step Code.Take.doneL 0 7) (by simp [takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.doneL 26 7) (by simp [takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.doneL 52 7) (by simp [takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.bumpL 0 7) (by simp [takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.bumpL 31 7) (by simp [takePhTab]))
      · exact step_of_factOk hl (hf (.step Code.Take.okL 0 7) (by simp [takePhTab]))
    swpOk := ok_of_factOk hl (hf (.ok Code.Take.spinL 11) (by simp [takePhTab]))
    ldnOk := (step_of_factOk hl (hf (.step Code.Take.lockedL 4 3) (by simp [takePhTab]))).1
    unlOk := ok_of_factOk hl (hf (.ok Code.Take.bumpL 28) (by simp [takePhTab]))
    nxtOk := ok_of_factOk hl (hf (.ok Code.Take.bumpL 56) (by simp [takePhTab]))
    ldnPh := (step_of_factOk hl (hf (.step Code.Take.lockedL 4 3) (by simp [takePhTab]))).2
    noTk := by
      intro p hp
      simp only [takePcs, siPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · rw [es3]; exact noTk_tk h i (v := 14) (by decide) (by decide)
      · exact noTk_tk h i (v := 14) (by decide) (by decide)
      · exact noTk_tk h i (v := 14) (by decide) (by decide)
      · exact noTk_tk h i (v := 14) (by decide) (by decide)
      · exact noTk_tk h i (v := 14) (by decide) (by decide)
      · exact noTk_tk h i (v := 14) (by decide) (by decide)
      · exact noTk_tk h i (v := 14) (by decide) (by decide)
      · rw [eu3]; exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · rw [en5]; exact noTk_tk h i (v := 8) (by decide) (by decide)
      · exact noTk_tk h i (v := 8) (by decide) (by decide)
      · exact noTk_tk h i (v := 8) (by decide) (by decide)
      · exact noTk_tk h i (v := 8) (by decide) (by decide)
      · exact noTk_tk h i (v := 8) (by decide) (by decide)
      · intro s hs hT; unfold Tk at hT; rw [hs, ht8] at hT; omega
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 14) (by decide) (by decide)
      · exact noTk_tk h i (v := 12) (by decide) (by decide)
      · exact noTk_tk h i (v := 8) (by decide) (by decide)
    swpIn := ⟨(0#64).setWidth 128, by rw [hs12, hlk]; simp [ownOf]⟩
    swpUpd := by
      rw [es3, hs12, hs14, hlk]
      simp [Spike.Lib.X64.Rt.ownUpdB, ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6]
    unlIn := ⟨(1#64).setWidth 128, by rw [hb14, hlk]; simp [ownOf]⟩
    unlUpd := by
      rw [eu3, hb14, hb12, hlk]
      simp [Spike.Lib.X64.Rt.ownUpdB, ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6]
    nxtIn := ⟨(0#64).setWidth 128, by rw [hn12, hnx]; simp [ownOf]⟩
    nxtUpd := by
      rw [en5, hn12, hn8, hnx]
      simp [Spike.Lib.X64.Rt.ownUpdB, ownOf, c1, c2, c3, c4, c5, c6, Ne.symm c1, Ne.symm c2, Ne.symm c3,
        Ne.symm c4, Ne.symm c5, Ne.symm c6]
    siteRel := fun a ha => take_ne h i (List.mem_cons_self ..) ha
    siteAb := fun k a ha => take_ne h i (y := Λ.abortLbl k)
      (by cases k <;> simp) ha
    siteAt := Spike.Lib.X64.PhRec.site_ofPlaceOK h i
    siteOwn := by rw [ht8, ht0]; rfl
    tk1 := fun s hs => by unfold Tk; rw [hs, ht0] }

open Spike.Lib.X64.Rt.Take (TakePh) in
open Spike.Lib.X64.PhRec (ownOf μ) in
/-- **`scc_rt_stack_take`'s phase facts** at an output passing `placeOK`
(A6, A8, the sites distinct), returning to `scc_rt_thread_init`'s `.x7`
(`.entry` + 12, A11's gap). -/
theorem takePh_ofPlaceOK (hs : o.place.tail = .bare) :
    TakePh (okPc (Ly)) (ph (Ly)) (Tk (Ly)) (ownOf (Ly)) (μ (Ly)) (Ly).lab (fun _ => (Ly).lab Code.Ti.x7L) := by
  have h' := takePhAt_ofPlaceOK h i; rw [hs] at h'; exact h'

end Place

end Spike.Lib.X64.Rt.PhRecOf
