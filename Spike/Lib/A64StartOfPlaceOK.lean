/-
**The start segment's runtime premises from `placeOK`** (AArch64): the
premises of `start_segW`'s instance at the runtime's layout of an output
passing `placeOK` (`RuntimeLayout.ofPlaceOK`), the memory side
`msOf Ly.Λ (μ Ly) rd G (own Ly) lbl lsize` (`Spike/Lib/A64PhRec.lean`):

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
  below `scc_rt_main`'s and a user frame's bound; its initial value `0` by
  A8's `rtInitOk`);
- `hownT_ofPlaceOK`, `hownL_ofPlaceOK`, `hownF_ofPlaceOK`,
  `hownN_ofPlaceOK`: the counters owned at the runtime's atomic accesses,
  their phases pinned by A6 (`phPins`), for any `rd`, `G`, `lbl`, `lsize`;
- the loaded thread `S0Of`: at `_start` (`hpc_ofPlaceOK`, A1), not in the
  take's phase (`htk0_ofPlaceOK`), its owned words the load's
  (`hown0_ofPlaceOK`, A6's pin of `_start` and A8's `rtInitOk`); with an
  entry pc instead, `htk0_of_pc`, `hown0_of_pc`;
- `hGpl_ofPlaceOK`: the value invariant at any placed word of `.data` or
  the heap (not the limit word, A8's `rtOffOk`).
-/
import Spike.Lib.A64PhRec
import Spike.Lib.A64Correct
import Scc.Sem.FixInv
import Spike.Lib.Rt.A64RtPhRec

namespace Spike.Lib.A64.PhRec

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (FixG)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer (msOf TPar TParE)
open Spike.Lib.A64.Rt (RuntimeLayout RtFree rtFree_none)
open Spike.Lib.A64.Flow.Ret0 (OwnAt limA)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (linkOf codeOf)

/-! ## The value invariant -/

/-- **The canonical load's memory** of a text: its initial words
(`Rt.A64.initOf`), no message. -/
def m0Of (Λ : Scc.Sem.Layout) (prog : Program) (secs : Scc.Sem.DataSecs) : Memory :=
  { init := Scc.Cert.Rt.A64.initOf Λ prog secs, msgs := #[] }

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

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
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
theorem rtFree_ofPlaceOK {lsize : Spike.Lib.A64Consumer.Lsize} : RtFree Ly (fun _ => none) lsize :=
  rtFree_none _ fun _ => rfl

/-! ### B6 -/

/-- **The invariant at load**, at an entry state `E` clear of the layout. -/
theorem G0_ofPlaceOKE {E : Scc.Sem.Entry} (hE : E.clear (Ly).Λ = true) :
    ∀ t0, (TParE E).load (o.prog, o.secs) (Ly).Λ = some t0 → MemInv (GOf Ly M0) t0.1.mem := by
  intro t0 hl
  have he : (TParE E).load (o.prog, o.secs) (Ly).Λ = _ :=
    Scc.Cert.Link.A64.loadParsed_of_loadOk (H := Scc.Sem.A64.kernel 1) (loadOk_link_of_placeOKAt i h) hE
  rw [he] at hl
  cases hl
  exact Scc.Sem.memInv_fixG_load rfl rfl

/-- **The invariant at load.** -/
theorem G0_ofPlaceOK : ∀ t0, TPar.load (o.prog, o.secs) (Ly).Λ = some t0 → MemInv (GOf Ly M0) t0.1.mem :=
  G0_ofPlaceOKE h i (clear_link_of_placeOKAt i h)

/-- The counters and the TCB's words are not the limit word but its own
field (A8's `tcbSep`). -/
theorem ctr_ne {a : BitVec 64} (ha : a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA]) :
    a ≠ (Ly).pinA + 16#64 := by
  rintro rfl
  exact tcbSep_of_placeOKAt h 2 (by decide) ha

/-- The TCB's header store. -/
theorem hGh_ofPlaceOK :
    GOf Ly M0 ⟨(Ly).pinA + 0#64, 8⟩ ((Spike.Lib.A64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128) :=
  gOf_ne (pin_ne (by simp)) _

/-- The TCB's field stores: off the limit word, but the limit field's,
whose value is the limit. -/
theorem hGf_ofPlaceOK :
    ∀ e ∈ Spike.Lib.A64.Flow.Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      GOf Ly M0 ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128) := by
  intro e he
  have hq : ∀ k : Nat, (Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 k = (Ly).pinA + (8#64 + BitVec.ofNat 64 k) := by
    intro k; rw [BitVec.add_zero, BitVec.add_assoc]
  simp only [Spike.Lib.A64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
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
    GOf Ly M0 ⟨(Ly).pnA, 8⟩ ((0#64 + Spike.Lib.A64.Flow.Ret0.AllocTcb.tcbLen).setWidth 128) :=
  gOf_ne (ctr_ne h i (by simp)) _

/-- The lock's store of `1`. -/
theorem hG1_ofPlaceOK : GOf Ly M0 ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128) :=
  gOf_ne (ctr_ne h i (by simp)) _

/-- The lock's store of `0`. -/
theorem hG0_ofPlaceOK : GOf Ly M0 ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128) :=
  gOf_ne (ctr_ne h i (by simp)) _

/-- The store of `scc_rt_stack_next`. -/
theorem hGn_ofPlaceOK :
    GOf Ly M0 ⟨(Ly).nextA, 8⟩ ((0#64 + Spike.Lib.A64.Flow.Ret0.StackTake.size0).setWidth 128) :=
  gOf_ne (ctr_ne h i (by simp)) _

/-- The limit word's initial value is `0` (A8's `rtInitOk`). -/
theorem limInit_ofPlaceOK : (M0).initVal ⟨(Ly).pinA + 16#64, 8⟩ = 0 :=
  Scc.Cert.Rt.A64.initVal_rt_of_rtInitOk (rtInit_of_placeOKAt h) rfl
    ((Ly).fld_mem (i := 1) (by decide))

/-- **The limit word's values are at most `b`**, for any `b` at least the
limit. -/
theorem room_of_le {b : Nat} (hb : (Ly).stacksA.toNat + 4096 ≤ b) :
    ∀ v : Val, GOf Ly M0 ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v → (v.setWidth 64).toNat ≤ b := by
  intro v hv
  rw [Spike.Lib.A64.Rt.limA_tcb0 (RuntimeLayout.ofPlaceOK h i)] at hv
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
theorem stacksA_lab : Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab = (Ly).stacksA := (Ly).lab_stacks

/-- **`scc_rt_main`'s room**: the limit word's values below the first
stack's top less `scc_rt_main`'s frame. -/
theorem hroomM_ofPlaceOK :
    ∀ v : Val, GOf Ly M0 ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤
        (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - Spike.Lib.A64.Rt.bareMC.Z.toBitVec).toNat := by
  refine room_of_le h i ?_
  rw [stacksA_lab h i, BitVec.toNat_sub, Spike.Lib.A64.Rt.top0_toNat (RuntimeLayout.ofPlaceOK h i)]
  have := (Ly).pool_fit
  obtain ⟨h1, h2⟩ := (Ly).stacks_sub
  simp only at h1 h2
  rw [show (Spike.Lib.A64.Rt.bareMC.Z.toBitVec).toNat = 48 from rfl]
  omega

/-- **A user frame's room**: the limit word's values below the first
stack's top less `scc_rt_main`'s frame and any frame up to `4095`. -/
theorem hroomU_ofPlaceOK :
    ∀ {frame : Int}, 0 ≤ frame → frame ≤ 4095 →
      ∀ v : Val, GOf Ly M0 ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
        (v.setWidth 64).toNat ≤
          (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - Spike.Lib.A64.Rt.bareMC.Z.toBitVec -
            (Int64.ofInt frame).toBitVec).toNat := by
  intro frame h0 h1
  refine room_of_le h i ?_
  have hf : (Int64.ofInt frame).toBitVec.toNat = frame.toNat := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    omega
  rw [stacksA_lab h i, BitVec.toNat_sub, BitVec.toNat_sub, Spike.Lib.A64.Rt.top0_toNat (RuntimeLayout.ofPlaceOK h i),
    hf]
  have := (Ly).pool_fit
  obtain ⟨h1', h2'⟩ := (Ly).stacks_sub
  simp only at h1' h2'
  rw [show (Spike.Lib.A64.Rt.bareMC.Z.toBitVec).toNat = 48 from rfl]
  omega

/-! ### B7 -/

/-- **A pinned pc's phase** (A6's `phPins`) in the record. -/
theorem ph_pin {l : String} {k v : Nat} (hp : (l, k, v) ∈ Scc.Cert.Rt.A64.phPins) :
    ph Ly ((Ly).lab l + Int64.ofNat (4 * k)).toBitVec.toNat = v := by
  obtain ⟨a, ha, hph⟩ := pin_of_placeOKAt h hp
  have hlab : (Ly).lab l = Int64.ofNat a :=
    Scc.Cert.Rt.A64.label_threadAt_of_codeOf (E := Scc.Sem.Entry.linux)
      (syms := Scc.Sem.loadSyms (Ly).Λ o.secs.rodata) (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK_above h i) ha
  rw [hlab]
  have : (Int64.ofNat a + Int64.ofNat (4 * k)).toBitVec.toNat = (a + 4 * k) % 2 ^ 64 := by
    simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat', BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [this]
  exact hph

/-- **A word owned at a pc** whose phase owns it. -/
theorem ownAt_of_ph {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Spike.Lib.A64Consumer.Lbl}
    {lsize : Spike.Lib.A64Consumer.Lsize} {pc : Int64} {a v : BitVec 64} {n : Nat}
    (hph : ph Ly pc.toBitVec.toNat = n) (hm : ((⟨a, 8⟩ : Loc), v.setWidth 128) ∈ ownOf Ly n) :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc pc a v := by
  intro s _ _ hpc
  show _ ∈ own Ly s
  unfold own
  rw [show pcOf s = pc.toBitVec.toNat by unfold pcOf; rw [hpc], hph]
  exact hm

variable {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Spike.Lib.A64Consumer.Lbl}
  {lsize : Spike.Lib.A64Consumer.Lsize}

/-- **`scc_rt_pinned_next` owned at its add** (phase `13`). -/
theorem hownT_ofPlaceOK :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc
      (Spike.Lib.A64.Flow.Ret0.AllocTcb.rmwPc (Ly).lab) (Ly).pnA 0#64 :=
  ownAt_of_ph h i (ph_pin h i (l := ".L3_scc_rt_alloc_tcb.1_len") (k := 37) (v := 13) (by decide))
    (by simp [ownOf])

/-- **The lock owned at its swap** (phase `12`). -/
theorem hownL_ofPlaceOK :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc
      (Spike.Lib.A64.Flow.Ret0.StackTake.swpPc (Ly).lab) (Ly).lockA 0#64 :=
  ownAt_of_ph h i (ph_pin h i (l := ".L6_scc_rt_stack_take.4_spin14") (k := 2) (v := 12) (by decide))
    (by simp [ownOf])

/-- **`scc_rt_stack_free_n` owned at its load** (phase `14`). -/
theorem hownF_ofPlaceOK :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc
      (Spike.Lib.A64.Flow.Ret0.StackTake.freeNPc (Ly).lab) (Ly).freeNA 0#64 :=
  ownAt_of_ph h i (ph_pin h i (l := ".L6_scc_rt_stack_take.5_locked15") (k := 1) (v := 14) (by decide))
    (by simp [ownOf])

/-- **`scc_rt_stack_next` owned at its store** (phase `12`). -/
theorem hownN_ofPlaceOK :
    OwnAt (msOf (Ly).Λ (μ Ly) rd G (own Ly) lbl lsize) (Ly).exe (Ly).endPc
      (Spike.Lib.A64.Flow.Ret0.StackTake.nextPc (Ly).lab) (Ly).nextA 0#64 :=
  ownAt_of_ph h i (ph_pin h i (l := ".L6_scc_rt_stack_take.7_bump") (k := 11) (v := 12) (by decide))
    (by simp [ownOf])

omit h in
/-- A table's check splits over an append. -/
theorem rtPhOk_append {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {A B : List Scc.Cert.Rt.A64.PhFact} :
    Scc.Cert.Rt.A64.rtPhOk lo prog Λ (A ++ B) =
      (Scc.Cert.Rt.A64.rtPhOk lo prog Λ A && Scc.Cert.Rt.A64.rtPhOk lo prog Λ B) := by
  unfold Scc.Cert.Rt.A64.rtPhOk Scc.Cert.Rt.A64.rtPhOkBy
  split <;> simp [List.all_append]

/-- **The switch's phase facts** of an output passing `placeOK` (A6's table,
`swPh_ofPlaceOK`). -/
theorem hsw_ofPlaceOK : Spike.Lib.A64.Rt.MainU.SwPh (okPc Ly) (ph Ly) (Ly).lab :=
  Spike.Lib.A64.Rt.PhRecOf.swPh_ofPlaceOK h i (rtPh_of_placeOKAt h)

/-- **`scc_rt_main`'s phase facts at `bareMC`** of an output passing
`placeOK` (A6's table and A11's `mainPhTab` at the bare tail,
`mainPh_ofPlaceOK`). -/
theorem hmph_ofPlaceOK : Spike.Lib.A64.Rt.MainU.MainPh (okPc Ly) (ph Ly) (Ly).lab Spike.Lib.A64.Rt.bareMC := by
  refine Spike.Lib.A64.Rt.PhRecOf.mainPh_ofPlaceOK h i ?_
  have hm := mainPh_of_placeOKAt h (mc := Spike.Lib.A64.Rt.bareMC) (by rw [tail_of_placeOKAt h]; rfl)
  have hr := rtPh_of_placeOKAt h
  have he : Spike.Lib.A64.Rt.rtPhTab (some Spike.Lib.A64.Rt.bareMC) =
      Spike.Lib.A64.Rt.rtPhTab none ++ Spike.Lib.A64.Rt.mainPhTab Spike.Lib.A64.Rt.bareMC := by
    simp [Spike.Lib.A64.Rt.rtPhTab]
  rw [he, rtPhOk_append]
  exact Bool.and_eq_true_iff.mpr ⟨hr, hm⟩

/-! ### The loaded thread (`hpc`, `htk0`, `hown0`, `hGpl`)

The canonical loader's thread starts at the code base, `_start` by A1
(`start_link_of_placeOKAt`); there A6 pins the phase `13`: not in the take's
phase, and the owned words the four counters at `0`, their initial values
by A8's `rtInitOk`. A placed word of `.data` or the heap is not the limit
word (A8's `rtOffOk`), so the value invariant holds there for any value. -/

/-- The canonical loader's thread of the output, at the code base. -/
abbrev S0Of (L : RuntimeLayout) (prog : Program) (secs : Scc.Sem.DataSecs) : State :=
  Scc.Sem.A64.threadAt Scc.Sem.Entry.linux L.Λ.code.lo prog (Scc.Sem.loadSyms L.Λ secs.rodata)

/-- The loader's thread of the output at the entry state `E`, at the code
base (`S0Of` at `Entry.linux`). -/
abbrev S0OfE (E : Scc.Sem.Entry) (L : RuntimeLayout) (prog : Program) (secs : Scc.Sem.DataSecs) : State :=
  Scc.Sem.A64.threadAt E L.Λ.code.lo prog (Scc.Sem.loadSyms L.Λ secs.rodata)

/-- **The loaded thread is at `_start`** (A1), at any entry state `E`. -/
theorem hpc_ofPlaceOKE (E : Scc.Sem.Entry) : (S0OfE E Ly o.prog o.secs).st.2 = (Ly).lab "_start" :=
  (Scc.Cert.Rt.A64.label_threadAt_of_codeOf (E := E)
    (syms := Scc.Sem.loadSyms (Ly).Λ o.secs.rodata) (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK_above h i)
        (start_link_of_placeOKAt i h)).symm

/-- **The loaded thread is at `_start`** (A1). -/
theorem hpc_ofPlaceOK : (S0Of Ly o.prog o.secs).st.2 = (Ly).lab "_start" :=
  hpc_ofPlaceOKE h i Scc.Sem.Entry.linux

/-- **The phase at `_start`**, `13`, for any state there. -/
theorem ph_start {s : State} (hpc : s.st.2 = (Ly).lab "_start") : ph Ly (pcOf s) = 13 := by
  have hp := ph_pin h i (l := "_start") (k := 0) (v := 13) (by decide)
  have he : ((Ly).lab "_start" + Int64.ofNat (4 * 0)).toBitVec.toNat = pcOf s := by
    unfold pcOf; rw [hpc]; simp
  rw [← he]; exact hp

/-- **Not in the take's phase at `_start`** (`htk0` given the entry pc). -/
theorem htk0_of_pc {s : State} (hpc : s.st.2 = (Ly).lab "_start") : ¬ Tk Ly s := by
  unfold Tk; rw [ph_start h i hpc]; decide

/-- **The loaded thread is not in the take's phase** (`htk0`). -/
theorem htk0_ofPlaceOK : ¬ Tk Ly (S0Of Ly o.prog o.secs) :=
  htk0_of_pc h i (hpc_ofPlaceOK h i)

/-- **The owned words at `_start` are the load's** (`hown0` given the entry
pc), at an entry state `E` clear of the layout: the four counters, each at
`0`. -/
theorem hown0_of_pcE {E : Scc.Sem.Entry} (hE : E.clear (Ly).Λ = true) {s : State}
    (hpc : s.st.2 = (Ly).lab "_start") :
    ∀ t0, (TParE E).load (o.prog, o.secs) (Ly).Λ = some t0 →
      Spike.Lib.Consumer1.OwnInit (own Ly s) t0.1.mem := by
  intro t0 hl
  have he : (TParE E).load (o.prog, o.secs) (Ly).Λ = _ :=
    Scc.Cert.Link.A64.loadParsed_of_loadOk (H := Scc.Sem.A64.kernel 1) (loadOk_link_of_placeOKAt i h) hE
  rw [he] at hl
  cases hl
  intro L v hm
  unfold own at hm
  rw [ph_start h i hpc] at hm
  simp only [ownOf, Nat.reduceMod, Nat.reduceDiv, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hm
  have hz {a : BitVec 64} (ha : a ∈ (Ly).rtWords) : (M0).initVal ⟨a, 8⟩ = 0 :=
    Scc.Cert.Rt.A64.initVal_rt_of_rtInitOk (rtInit_of_placeOKAt h) rfl ha
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, (hz (Ly).pn_mem).trans (by decide)⟩
  · exact ⟨rfl, (hz (Ly).lock_mem).trans (by decide)⟩
  · exact ⟨rfl, (hz (Ly).freeN_mem).trans (by decide)⟩
  · exact ⟨rfl, (hz (Ly).next_mem).trans (by decide)⟩

/-- **The owned words at `_start` are the load's** (`hown0_of_pcE` at
`Entry.linux`). -/
theorem hown0_of_pc {s : State} (hpc : s.st.2 = (Ly).lab "_start") :
    ∀ t0, TPar.load (o.prog, o.secs) (Ly).Λ = some t0 → Spike.Lib.Consumer1.OwnInit (own Ly s) t0.1.mem :=
  hown0_of_pcE h i (clear_link_of_placeOKAt i h) hpc

/-- **The loaded thread's owned words are the load's** (`hown0`). -/
theorem hown0_ofPlaceOK :
    ∀ t0, TPar.load (o.prog, o.secs) (Ly).Λ = some t0 →
      Spike.Lib.Consumer1.OwnInit (own Ly (S0Of Ly o.prog o.secs)) t0.1.mem :=
  hown0_of_pc h i (hpc_ofPlaceOK h i)

/-- **The value invariant at a placed word** of `.data` or the heap
(`hGpl`): not the limit word (A8's `rtOffOk`), so any value. -/
theorem hGpl_ofPlaceOK :
    ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → GOf Ly M0 (Scc.Sem.wordLoc a) v := by
  intro a v ha
  have hc := Scc.Cert.Rt.A64.clear_of_rtOffOk (rtOff_of_placeOKAt h) (j := 2) (by decide)
  have hw := (wf_link_of_placeOKAt i h).inSpace
  have hd := hw _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have hh := hw _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  change Scc.Cert.Rt.A64.clearB (Ly).Λ.data ((Ly).pinA + 16#64) = true ∧
    Scc.Cert.Rt.A64.clearB (Ly).Λ.heap ((Ly).pinA + 16#64) = true at hc
  simp only [Scc.Cert.Rt.A64.clearB, Bool.or_eq_true, decide_eq_true_eq] at hc
  simp only [Scc.Sem.Range.InSpace] at hd hh
  simp only [Scc.Sem.Range.contains] at ha
  refine gOf_ne (fun he => ?_) v
  have hb := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat] at hb
  have : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  omega

end Place

end Spike.Lib.A64.PhRec
