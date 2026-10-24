/-
**The start segment's runtime premises from `placeOK`** (x86-64, the twin
of `Spike/Lib/A64StartOfPlaceOK.lean`): the premises of `x64_start_segW`'s
instance at the runtime's layout of an output passing `placeOK`
(`RuntimeLayout.ofPlaceOK`), the memory side
`msOf Ly.Λ (μ Ly) rd G (own Ly) lbl lsize` (`Spike/Lib/X64PhRec.lean`):

- `rtFree_ofPlaceOK`: no label placed (`lbl = fun _ => none`) covers a
  runtime word (`RtFree`);
- the consumer's value invariant `GOf Ly m0 = FixG [(limW Ly, limV Ly)] m0`
  (the first TCB's limit word holds its initial value or the limit
  `scc_rt_thread_init` stores, the first stack's base plus the guard; any
  value elsewhere), `m0Of` the canonical load's memory:
  `G0_ofPlaceOK` (the invariant at load), `hGh_ofPlaceOK`, `hGf_ofPlaceOK`,
  `hGt_ofPlaceOK`, `hG1_ofPlaceOK`, `hG0_ofPlaceOK`, `hGn_ofPlaceOK` (the
  runtime's stores: off the limit word but the limit field's, which stores
  `limV`), `hroomM_ofPlaceOK`, `hroomU_ofPlaceOK` (the limit word's values
  below `scc_rt_main`'s and a user frame's bound, the two return addresses
  and saved `%rbp`s of x86-64's calls included; its initial value `0` by
  A8's `rtInitOk`);
- `hGpl_ofPlaceOK`: any value on the heap and the data, given the limit word
  is off them (`hclr`, A8's pending check of the runtime's words clear of
  data and heap);
- `htk0_ofPlaceOK`, `hown0_ofPlaceOK`: the loaded thread out of the take's
  phase, its owned words the load's, given its pc's phase is `13` (`hph0`:
  the counters at their initial values, out of the take; A6/A1's pending
  pin of `_start`'s phase);
- `ownAt_of_ph`: a counter owned at a pc whose phase owns it. The counters'
  ownership at the runtime's atomic accesses (`OwnAt`) follows from A6's
  phase pins, pending on x86-64.
-/
import Spike.Lib.X64PhRec
import Spike.Lib.X64Correct
import Scc.Sem.FixInv
import Spike.Lib.Rt.X64RtPhOfTab

namespace Spike.Lib.X64.PhRec

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (FixG)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer (msOf TPar TParE)
open Spike.Lib.X64.Rt (RuntimeLayout RtFree rtFree_none)
open Spike.Lib.X64 (OwnAt)
open Spike.Lib.X64.Flow.Ret0 (limA tpOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Link.X64 (linkOf)

/-! ## The value invariant -/

/-- **The canonical load's memory** of a text: its initial words
(`Rt.X64.initOf`), no message. -/
def m0Of (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (secs : Scc.Sem.DataSecs) : Memory :=
  { init := Scc.Cert.Rt.X64.initOf Λ cells secs, msgs := #[] }

/-- The first TCB's limit word (its field `1`). -/
abbrev limW (L : RuntimeLayout) : Nat := (L.pinA + 16#64).toNat

/-- The limit `scc_rt_thread_init` stores (`Ret0.ThreadInit.fields`' field
`1`): the first stack's base plus the guard. -/
abbrev limV (L : RuntimeLayout) : Val := (L.stacksA + 4096#64).setWidth 128

/-- **The consumer's value invariant**: the limit word holds its initial
value or the limit; any value elsewhere. -/
def GOf (L : RuntimeLayout) (m0 : Memory) : Loc → Val → Prop := FixG [(limW L, limV L)] m0

/-- Off the limit word, any value. -/
theorem gOf_ne {L : RuntimeLayout} {m0 : Memory} {a : BitVec 64} (ha : a ≠ L.pinA + 16#64) (v : Val) :
    GOf L m0 ⟨a, 8⟩ v := by
  unfold GOf FixG
  intro a' w hm hl
  simp only [List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  simp only [Loc.mk.injEq, BitVec.ofNat_toNat, BitVec.setWidth_eq, and_true] at hl
  exact (ha hl).elim

/-- At the limit word, its values. -/
theorem gOf_lim {L : RuntimeLayout} {m0 : Memory} {v : Val} (h : GOf L m0 ⟨L.pinA + 16#64, 8⟩ v) :
    v = limV L ∨ v = m0.initVal ⟨L.pinA + 16#64, 8⟩ := by
  unfold GOf FixG at h
  exact h _ _ (List.mem_singleton_self _) (by simp only [limW, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- A word `pinA + c` is the limit word only at `c = 16`. -/
theorem pin_ne {L : RuntimeLayout} {c : BitVec 64} (hc : c ≠ 16#64) : L.pinA + c ≠ L.pinA + 16#64 :=
  fun h => hc ((BitVec.add_right_inj _).mp h)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

set_option hygiene false in
/-- The layout of `ofPlaceOK`. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => m0Of (RuntimeLayout.ofPlaceOK h i).Λ o.prog o.secs

/-! ### B5 -/

/-- **No label placed covers a runtime word.** -/
theorem rtFree_ofPlaceOK {lsize : Spike.Lib.X64Consumer.Lsize} : RtFree Ly (fun _ => none) lsize :=
  rtFree_none _ fun _ => rfl

/-! ### B6 -/

/-- **The invariant at load**, at an entry state `E` clear of the layout. -/
theorem G0_ofPlaceOKE {E : Scc.Sem.Entry} (hE : E.clear (Ly).Λ = true) :
    ∀ t0, (TParE E).load (o.prog, o.secs, o.labelOffs) (Ly).Λ = some t0 → MemInv (GOf Ly M0) t0.1.mem := by
  intro t0 hl
  have he : (TParE E).load (o.prog, o.secs, o.labelOffs) (Ly).Λ = _ :=
    Scc.Cert.Link.X64.loadParsed_of_loadOk (H := Scc.Sem.X64.kernel 1) (loadOk_link_of_placeOKAt i h) hE
  rw [he] at hl
  cases hl
  exact Scc.Sem.memInv_fixG_load rfl rfl

/-- **The invariant at load.** -/
theorem G0_ofPlaceOK :
    ∀ t0, TPar.load (o.prog, o.secs, o.labelOffs) (Ly).Λ = some t0 → MemInv (GOf Ly M0) t0.1.mem :=
  G0_ofPlaceOKE h i (clear_link_of_placeOKAt i h)

/-- **A runtime word starts at `0`** in the load at an entry state `E`
clear of the layout (A8's `rtInitOk`). -/
theorem init_rtE {E : Scc.Sem.Entry} (hE : E.clear (Ly).Λ = true) {t0 : (TParE E).M.Cfg}
    (hl : (TParE E).load (o.prog, o.secs, o.labelOffs) (Ly).Λ = some t0)
    {a : BitVec 64} (ha : a ∈ (Ly).rtWords) : t0.1.mem.initVal ⟨a, 8⟩ = 0 := by
  have he : (TParE E).load (o.prog, o.secs, o.labelOffs) (Ly).Λ = _ :=
    Scc.Cert.Link.X64.loadParsed_of_loadOk (H := Scc.Sem.X64.kernel 1) (loadOk_link_of_placeOKAt i h) hE
  rw [he] at hl
  cases hl
  exact Scc.Cert.Rt.X64.initVal_rt_of_rtInitOk (rtInit_of_placeOKAt h) rfl ha

/-- **A runtime word starts at `0`** in the load (A8's `rtInitOk`). -/
theorem init_rt {t0 : TPar.M.Cfg} (hl : TPar.load (o.prog, o.secs, o.labelOffs) (Ly).Λ = some t0)
    {a : BitVec 64} (ha : a ∈ (Ly).rtWords) : t0.1.mem.initVal ⟨a, 8⟩ = 0 :=
  init_rtE h i (clear_link_of_placeOKAt i h) hl ha

/-- The counters are not the limit word (A8's `tcbSep`). -/
theorem ctr_ne {a : BitVec 64} (ha : a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA]) :
    a ≠ (Ly).pinA + 16#64 := by
  rintro rfl
  exact tcbSep_of_placeOKAt h 2 (by decide) ha

/-- The TCB's header store. -/
theorem hGh_ofPlaceOK :
    GOf Ly M0 ⟨(Ly).pinA + 0#64, 8⟩ ((Spike.Lib.X64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128) :=
  gOf_ne (pin_ne (by simp)) _

/-- The TCB's field stores: off the limit word, but the limit field's,
whose value is the limit. -/
theorem hGf_ofPlaceOK :
    ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      GOf Ly M0 ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128) := by
  intro e he
  have hq : ∀ k : Nat, (Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 k = (Ly).pinA + (8#64 + BitVec.ofNat 64 k) := by
    intro k; rw [BitVec.add_zero, BitVec.add_assoc]
  simp only [Spike.Lib.X64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hq]
  · exact gOf_ne (pin_ne (by simp)) _
  · unfold GOf FixG
    intro a' w hm _
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨-, rfl⟩ := hm
    left
    simp only [limV, BitVec.add_zero]
  all_goals exact gOf_ne (pin_ne (by simp)) _

/-- The store of `scc_rt_pinned_next`. -/
theorem hGt_ofPlaceOK :
    GOf Ly M0 ⟨(Ly).pnA, 8⟩ ((0#64 + Spike.Lib.X64.Flow.Ret0.AllocTcb.tcbLen).setWidth 128) :=
  gOf_ne (ctr_ne h i (by simp)) _

/-- The lock's store of `1`. -/
theorem hG1_ofPlaceOK : GOf Ly M0 ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128) :=
  gOf_ne (ctr_ne h i (by simp)) _

/-- The lock's store of `0`. -/
theorem hG0_ofPlaceOK : GOf Ly M0 ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128) :=
  gOf_ne (ctr_ne h i (by simp)) _

/-- The store of `scc_rt_stack_next`. -/
theorem hGn_ofPlaceOK :
    GOf Ly M0 ⟨(Ly).nextA, 8⟩ ((0#64 + Spike.Lib.X64.Flow.Ret0.StackTake.size0).setWidth 128) :=
  gOf_ne (ctr_ne h i (by simp)) _

/-- The limit word's initial value is `0` (A8's `rtInitOk`). -/
theorem limInit_ofPlaceOK : (M0).initVal ⟨(Ly).pinA + 16#64, 8⟩ = 0 :=
  Scc.Cert.Rt.X64.initVal_rt_of_rtInitOk (rtInit_of_placeOKAt h) rfl
    ((Ly).fld_mem (i := 1) (by decide))

/-- **The limit word's values are at most `b`**, for any `b` at least the
limit. -/
theorem room_of_le {b : Nat} (hb : (Ly).stacksA.toNat + 4096 ≤ b) :
    ∀ v : Val, GOf Ly M0 ⟨limA (tpOf ((Ly).pinA + 0#64 + 8#64)), 8⟩ v → (v.setWidth 64).toNat ≤ b := by
  intro v hv
  rw [Spike.Lib.X64.Rt.limA_tcb0 (RuntimeLayout.ofPlaceOK h i)] at hv
  rcases gOf_lim (show GOf Ly M0 ⟨(Ly).pinA + 16#64, 8⟩ v from hv) with rfl | rfl
  · have := (Ly).pool_fit
    obtain ⟨h1, h2⟩ := (Ly).stacks_sub
    simp only at h1 h2
    simp only [limV, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [limInit_ofPlaceOK h i]
    simp

/-- `scc_rt_stacks` at its label. -/
theorem stacksA_lab : Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab = (Ly).stacksA := (Ly).lab_stacks

/-- **`scc_rt_main`'s room**: the limit word's values below the first
stack's top less the return address, the saved `%rbp` and `scc_rt_main`'s
frame. -/
theorem hroomM_ofPlaceOK :
    ∀ v : Val, GOf Ly M0 ⟨limA (tpOf ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 -
        Spike.Lib.X64.Rt.bareMC.Z.toBitVec).toNat := by
  refine room_of_le h i ?_
  rw [stacksA_lab h i, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub,
    Spike.Lib.X64.Rt.top0_toNat (RuntimeLayout.ofPlaceOK h i)]
  have := (Ly).pool_fit
  obtain ⟨h1, h2⟩ := (Ly).stacks_sub
  simp only at h1 h2
  rw [show (Spike.Lib.X64.Rt.bareMC.Z.toBitVec).toNat = 32 from rfl]
  simp only [BitVec.toNat_ofNat]
  omega

/-- **A user frame's room**: the limit word's values below the first
stack's top less `scc_rt_main`'s and the user call's return addresses,
saved `%rbp`s and frames, any user frame up to `4096`. -/
theorem hroomU_ofPlaceOK :
    ∀ {frame : Int}, 0 ≤ frame → frame ≤ 4096 →
      ∀ v : Val, GOf Ly M0 ⟨limA (tpOf ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
        (v.setWidth 64).toNat ≤ (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 -
          Spike.Lib.X64.Rt.bareMC.Z.toBitVec - 8#64 - 8#64 - (Int64.ofInt frame).toBitVec).toNat := by
  intro frame h0 h1
  refine room_of_le h i ?_
  have hf : (Int64.ofInt frame).toBitVec.toNat = frame.toNat := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    omega
  rw [stacksA_lab h i]
  simp only [BitVec.toNat_sub, Spike.Lib.X64.Rt.top0_toNat (RuntimeLayout.ofPlaceOK h i), hf,
    show (Spike.Lib.X64.Rt.bareMC.Z.toBitVec).toNat = 32 from rfl, BitVec.toNat_ofNat]
  have := (Ly).pool_fit
  obtain ⟨h1', h2'⟩ := (Ly).stacks_sub
  simp only at h1' h2'
  omega

/-- **The TCB's limit word is off the heap and the data** (A8's
`rtOffOk` at the pinned TCB's third word, with the regions inside the
address space). -/
theorem hclr_ofPlaceOK :
    ∀ a, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → BitVec.ofNat 64 a ≠ (Ly).pinA + 16#64 := by
  intro a ha he
  have hc := Scc.Cert.Rt.X64.clear_of_rtOffOk (rtOff_of_placeOKAt h) (j := 2) (by decide)
  have hw := (wf_link_of_placeOKAt (i := i) h).inSpace
  have hd := hw _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have hh := hw _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  change Scc.Cert.Rt.X64.clearB (Ly).Λ.data ((Ly).pinA + 16#64) = true ∧
    Scc.Cert.Rt.X64.clearB (Ly).Λ.heap ((Ly).pinA + 16#64) = true at hc
  simp only [Scc.Cert.Rt.X64.clearB, Bool.or_eq_true, decide_eq_true_eq] at hc
  simp only [Scc.Sem.Range.InSpace] at hd hh
  simp only [Scc.Sem.Range.contains] at ha
  have hb := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat] at hb
  have : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  omega

/-- **The value invariant on the heap and the data**: any value, given the
limit word is off them (`hclr`, `hclr_ofPlaceOK`). -/
theorem hGpl_ofPlaceOK
    (hclr : ∀ a, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → BitVec.ofNat 64 a ≠ (Ly).pinA + 16#64) :
    ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → GOf Ly M0 (Scc.Sem.wordLoc a) v :=
  fun a v ha => gOf_ne (hclr a ha) v

/-! ### The loaded thread -/

/-- **The loaded thread is out of the take's phase**, given its pc's phase
is `13` (`hph0`). -/
theorem htk0_ofPlaceOK {s : State} (hph0 : ph Ly (pcOf s) = 13) : ¬ Tk Ly s := by
  unfold Tk; rw [hph0]; decide

/-- **The loaded thread's owned words are the load's**, given its pc's
phase is `13` (`hph0`): the counters at `0` (A8's `rtInitOk`). -/
theorem hown0_ofPlaceOKE {E : Scc.Sem.Entry} (hE : E.clear (Ly).Λ = true) {s : State}
    (hph0 : ph Ly (pcOf s) = 13) :
    ∀ t0, (TParE E).load (o.prog, o.secs, o.labelOffs) (Ly).Λ = some t0 →
      Spike.Lib.Consumer1.OwnInit (own Ly s) t0.1.mem := by
  intro t0 hl L v hm
  unfold own at hm
  rw [hph0] at hm
  simp only [ownOf, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, by rw [init_rtE h i hE hl (Ly).pn_mem]; decide⟩
  · exact ⟨rfl, by rw [init_rtE h i hE hl (Ly).lock_mem]; decide⟩
  · exact ⟨rfl, by rw [init_rtE h i hE hl (Ly).freeN_mem]; decide⟩
  · exact ⟨rfl, by rw [init_rtE h i hE hl (Ly).next_mem]; decide⟩

/-- **The loaded thread's owned words are the load's** (`hown0_ofPlaceOKE`
at `Entry.linux`). -/
theorem hown0_ofPlaceOK {s : State} (hph0 : ph Ly (pcOf s) = 13) :
    ∀ t0, TPar.load (o.prog, o.secs, o.labelOffs) (Ly).Λ = some t0 →
      Spike.Lib.Consumer1.OwnInit (own Ly s) t0.1.mem :=
  hown0_ofPlaceOKE h i (clear_link_of_placeOKAt i h) hph0

/-! ### B7 -/

/-- **A word owned at a pc** whose phase owns it. -/
theorem ownAt_of_ph {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Spike.Lib.X64Consumer.Lbl}
    {lsize : Spike.Lib.X64Consumer.Lsize} {pc : Int64} {a v : BitVec 64} {n : Nat}
    (hph : ph Ly pc.toBitVec.toNat = n) (hm : ((⟨a, 8⟩ : Loc), v.setWidth 128) ∈ ownOf Ly n) :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc pc a v := by
  intro s _ _ hpc
  show _ ∈ own Ly s
  unfold own
  rw [show pcOf s = pc.toBitVec.toNat by unfold pcOf; rw [hpc], hph]
  exact hm

variable {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Spike.Lib.X64Consumer.Lbl}
  {lsize : Spike.Lib.X64Consumer.Lsize}

/-- **`scc_rt_pinned_next` owned at its add**, given the add's phase has
bit `0` (the counter at `0`). -/
theorem hownT_of_ph (hp : ph Ly (Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc (Ly).lab).toBitVec.toNat % 2 = 1) :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc
      (Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc (Ly).lab) (Ly).pnA 0#64 := by
  generalize hn : ph Ly (Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc (Ly).lab).toBitVec.toNat = n at hp
  refine ownAt_of_ph h i hn ?_
  rw [ownOf, if_pos hp]
  exact List.mem_cons_self

/-- **The lock owned at its exchange**, given the exchange's phase has bit
`1` clear (the lock at `0`). -/
theorem hownL_of_ph (hp : ph Ly (Spike.Lib.X64.Flow.Ret0.StackTake.swpPc (Ly).lab).toBitVec.toNat / 2 % 2 = 0) :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc
      (Spike.Lib.X64.Flow.Ret0.StackTake.swpPc (Ly).lab) (Ly).lockA 0#64 := by
  generalize hn : ph Ly (Spike.Lib.X64.Flow.Ret0.StackTake.swpPc (Ly).lab).toBitVec.toNat = n at hp
  refine ownAt_of_ph h i hn ?_
  rw [ownOf, if_neg (show ¬ n / 2 % 2 = 1 by omega)]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **`scc_rt_stack_free_n` owned at its load**: owned at `0` in every
phase. -/
theorem hownF_ofPlaceOK :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc
      (Spike.Lib.X64.Flow.Ret0.StackTake.freeNPc (Ly).lab) (Ly).freeNA 0#64 :=
  ownAt_of_ph h i rfl (by simp [ownOf])

/-- **`scc_rt_stack_next` owned at its store**, given the store's phase has
bit `2` (the counter at `0`). -/
theorem hownN_of_ph (hp : ph Ly (Spike.Lib.X64.Flow.Ret0.StackTake.nextPc (Ly).lab).toBitVec.toNat / 4 % 2 = 1) :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc
      (Spike.Lib.X64.Flow.Ret0.StackTake.nextPc (Ly).lab) (Ly).nextA 0#64 := by
  generalize hn : ph Ly (Spike.Lib.X64.Flow.Ret0.StackTake.nextPc (Ly).lab).toBitVec.toNat = n at hp
  refine ownAt_of_ph h i hn ?_
  rw [ownOf, if_pos hp]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The loaded thread is at `_start`** (A1), at any entry state `E`. -/
theorem hpc_ofPlaceOKE (E : Scc.Sem.Entry) :
    (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)).st.2 = (Ly).lab "_start" :=
  haveI : Kraken.Executable.ValidLayout (Scc.Sem.X64.threadAt E (Λ).code.lo
      o.prog (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).exe :=
    (RuntimeLayout.ofPlaceOK h i).valid
  (Scc.Cert.Rt.X64.label_threadAt_of_codeLabel_below (E := E)
    (syms := Scc.Sem.loadSyms (Ly).Λ o.secs.rodata) 
      (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK_below h i (start_link_of_placeOKAt (i := i) h))
        (start_link_of_placeOKAt (i := i) h)).symm

/-- **The loaded thread is at `_start`** (A1). -/
theorem hpc_ofPlaceOK :
    (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (Ly).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)).st.2 = (Ly).lab "_start" :=
  hpc_ofPlaceOKE h i Scc.Sem.Entry.linux

/-- **The loaded thread's phase** from `_start`'s: the loaded pc is
`_start`'s (`hpc`, A1) and `_start`'s phase is `13` (`hp`, A6's pin). -/
theorem hph0_of {s : State} (hpc : s.st.2 = (Ly).lab "_start")
    (hp : ph Ly ((Ly).lab "_start").toBitVec.toNat = 13) : ph Ly (pcOf s) = 13 := by
  unfold pcOf; rw [hpc]; exact hp

/-- **`_start`'s phase is `13`** in an output passing `placeOK` (A6's runtime
phase table, `startPhTab`'s `.ph "_start" 0 13`). -/
theorem hph0_ofPlaceOK : ph Ly ((Ly).lab "_start").toBitVec.toNat = 13 := by
  haveI : Kraken.Executable.ValidLayout (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (Λ).code.lo
      o.prog (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).exe :=
    (RuntimeLayout.ofPlaceOK h i).valid
  have hf := Scc.Cert.Rt.X64.factOk_of_rtPhOk (rtPh_of_placeOKAt h) (f := .ph "_start" 0 13)
    (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.startPhTab])
  have := Spike.Lib.X64.Rt.PhOfTab.ph_of_factOk (lab := (Ly).lab) (fun _ _ ha =>
    Scc.Cert.Rt.X64.label_threadAt_of_codeLabel_below (E := Scc.Sem.Entry.linux)
      (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
          (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha) hf
  simp at this
  exact this

end Place

end Spike.Lib.X64.PhRec
