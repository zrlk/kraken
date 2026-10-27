/-
**The AArch64 compiler theorem's assembly** (B8): for an `Accepted0`
program `[d]` whose lowering `lowerAll cfg [d]` passes `placeOK`, the output
is `Correct` over the canonical target on parsed texts, at the runtime's
layout with the lowering's immediates (`RuntimeLayout.ofPlaceOK h (immsOf d)`).

Every admissible entry state: `a64_lower_correctE` is the theorem at any
entry state `E` that `Entry.Ok` admits (the entry stack's region `entryR E`,
`entry_atE`, the load at `E`), `a64_scc_correctE_text` its release form
`Scc.Sem.A64.CorrectE 1`; `a64_lower_correct` and `a64_scc_correct{,_text}`
are them at `Entry.linux` (`linux_ok_ofPlaceOK`).

The proof composes the pieces: `mainPh_ofPlaceOK` (`main`'s code and phase
facts), `a64_start_segW` (the loaded thread's run as one segment inside
`SFacts … OvfDt`), `inst_of_segW` (the consumer's `Nodes`, `TakePath`, `AbortPath`,
`WrIn`), `tailNoFul_ovf` and `writeNoProm_of_tail` (`WriteNoProm`), and
`correctA64P'`.

The source parameters are `srcP1 arch` (`Spike/Lib/SrcP1.lean`): one thread
(`cap 1`) starting at `main` (`mainInit 1`), no hooks. They restrict the
source semantics to the single-threaded, hook-free programs `Accepted0`
admits.

Discharged here: the image and its static symbols (`imageIn_link_of_placeOKAt`,
`StaticSyms.of_none`), the write tail `hwr` (`ovfDt_of_at`), the immediates
(`himm`, `rfl`), the load (`loadParsed_of_loadOk`), the link's
well-formedness, `wideIn`, the marks, the abort path's start, and the
runtime's premises from `PlaceOK` (`Spike/Lib/A64StartOfPlaceOK.lean`: the
value invariant `GOf` at the loaded memory, `MemInv` at load, the runtime's
stores, the rooms, the counters' ownership, `RtFree` at `Λ.static`, which
is `fun _ => none`), `c0`'s facts (`cfacts_c0`), and the source's safety
(`safe_of_accepted0`: an `Accepted0` source has no memory operation), and the
runtime main's and the switch's phase records (`hmph_ofPlaceOK`,
`hsw_ofPlaceOK`, from A6's table and A11's `mainPhTab`), and the loaded
thread: at `_start` (`hpc_ofPlaceOK`, A1; then at `_start`'s node,
`entry_at`), out of the take's phase with its owned words the load's
(`htk0_ofPlaceOK`, `hown0_ofPlaceOK`), the value invariant on the heap and
the data (`hGpl_ofPlaceOK`, A8), and `_start`'s block (`entryW_ofPlaceOK`).

The theorems with an `hgen` premise keep it for their callers; it is no
longer open work: `hgen_ofPlaceOK` discharges it from the placement check
at every admissible entry state (`startAllUW_gen`,
`Spike/Lib/Rt/A64RtStartU.lean`). `a64_scc_correctE_closed` and
`a64_scc_correctE_text_closed` are `a64_scc_correctE{,_text}` without it,
at the static link; `a64_scc_correctE_closedAt` and
`a64_scc_correctE_text_closedAt` (the release statement) are them at any
layout `Λ` passing `placeOKAt`, with no static label.
-/
import Spike.Lib.LowerA64.StartSeg
import Spike.Lib.A64Accepted0Safe
import Spike.Lib.Rt.A64EntryOfPlaceOK
import Spike.Lib.LowerA64.OvfDt
import Spike.Lib.LowerA64.MainPh
import Spike.Lib.A64CorrectP
import Spike.Lib.SrcP1
import Spike.Lib.A64StartOfPlaceOK
import Spike.Lib.A64Ret0Correct
import Scc.Sem.CorrectEA64
import Spike.Lib.Rt.A64RtStartU
import Spike.Lib.LowerA64.TailBare

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64Consumer (CFacts SFacts Lbl Lsize msOf IOf TPar TParE)
open Spike.Lib.A64.Rt (RuntimeLayout SwUW StartAllUW bareMC rtF entryR)
open Spike.Lib.A64.Flow.Ret0 (StackM limA)
open Spike.Lib.A64.PhRec (μ K)
open Spike.Lib.LowerNode (immsOf)
open Spike.Lib.A64.PhRec (GOf m0Of rtFree_ofPlaceOK hGh_ofPlaceOK hGf_ofPlaceOK hGt_ofPlaceOK hG1_ofPlaceOK
  hG0_ofPlaceOK hGn_ofPlaceOK hroomM_ofPlaceOK hroomU_ofPlaceOK hownT_ofPlaceOK hownL_ofPlaceOK hownF_ofPlaceOK
  hownN_ofPlaceOK)
open Scc.Sem Scc.Sem.A64 Scc.Cert.Link Spike.Lib.Consumer1

section Entry

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option maxRecDepth 100000 in
/-- **The loaded thread is at `_start`'s node** on the entry stack
(`entryR E`) of an admissible entry state `E` (`hE`), the runtime's words
unloaded (`rtF_stackMem`), the source at `main`'s start, given the loaded
pc is `_start`'s (`hpc`). -/
theorem entry_atE {E : Entry} (hE : E.Ok (RuntimeLayout.ofPlaceOK h i).Λ)
    (hpc : (Scc.Sem.A64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceOK h i).lab "_start") :
    At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc (entryR E)
      (rtF (RuntimeLayout.ofPlaceOK h i)) (Ret0.entryN (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64Consumer.c0)
      (Scc.Sem.A64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) Spike.Lib.A64Consumer.c0 := by
  refine ⟨rfl, Scc.Cert.Rt.A64.endPc_threadAt_below _ _ _ _, rfl, hpc,
    ⟨{ SP := UInt64.ofNat E.sp }, _, fun k =>
    BitVec.ofInt 64 ((Mem.loadInt E.stackMem ((entryR E).addr k) 8).getD 0)⟩,
    ⟨rfl, rfl, ?_, ?_⟩, Spike.Lib.A64.Rt.rtF_stackMem _ hE rfl, rfl⟩
  · intro r k hr
    rcases r with x | _
    · simp [Ret0.entryN, A64.Abort.oE, SO.get, lk] at hr
    · simp only [Ret0.entryN, A64.Abort.oE, SO.get, Option.some.injEq] at hr
      subst hr
      dsimp only
      show (UInt64.ofNat E.sp).toBitVec = BitVec.ofNat 64 E.sp + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl
  · intro k hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (Spike.Lib.A64.Rt.stack_wordE hE hk)
    refine ⟨j, hj, ?_⟩
    show _ = BitVec.ofInt 64 ((Mem.loadInt E.stackMem _ 8).getD 0)
    rw [hj]; rfl

set_option maxRecDepth 100000 in
/-- **The loaded thread is at `_start`'s node** on the entry stack (`entryR`),
the runtime's words unloaded (`rtF_stackMem`), the source at `main`'s start:
`ret0_entry`'s generic form, given the loaded pc is `_start`'s (`hpc`). -/
theorem entry_at (hpc : (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceOK h i).lab "_start") :
    At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc (entryR Scc.Sem.Entry.linux)
      (rtF (RuntimeLayout.ofPlaceOK h i)) (Ret0.entryN (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64Consumer.c0)
      (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) Spike.Lib.A64Consumer.c0 :=
  entry_atE h i (RuntimeLayout.linux_ok_ofPlaceOK h i) hpc

end Entry

section StartPrems

open Spike.Lib.A64.Flow.Ret0.Inst (callee_facts out_callee)

/-- **The first stack's words are stable in `scc_rt_start`'s regions**: the
entry stack's region `entryR`, `scc_rt_alloc_tcb`'s callee region in it
and `scc_rt_thread_init`'s in that, at any runtime layout (the first stack
`rS0` in the pool, the pool below the entry stack: `outS_of_sub`,
`fitS_of_sub`). These are `startAllUW_gen`'s `hSM`, `hSMi`, `hSMt` at the
compiler theorem's `hgen`. -/
theorem stackM_rS0 (L : RuntimeLayout) {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) :
    FStable (entryR E) (StackM (Spike.Lib.A64.Rt.rS0 L)) ∧
      FStable ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-256) 0) (StackM (Spike.Lib.A64.Rt.rS0 L)) ∧
      FStable (((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0)
        (StackM (Spike.Lib.A64.Rt.rS0 L)) := by
  have hR := Spike.Lib.A64.Rt.entryR_ok hE
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub L (Spike.Lib.A64.Rt.rS0_sub L)
  have houtS := Spike.Lib.A64.Rt.outS_of_sub L hE (Spike.Lib.A64.Rt.rS0_sub L)
  have l1 : (entryR E).lo ≤ Spike.Lib.A64.Abort.oI.sp + -256 := by show (-65536 : Int) ≤ _; decide
  have h1 : Spike.Lib.A64.Abort.oI.sp < (entryR E).hi := by show _ < (0 : Int); decide
  have l2 : ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-256) 0).lo ≤ Ret0.ThreadInit.oI.sp + -208 := by
    show (-256 : Int) ≤ _; decide
  have h2 : Ret0.ThreadInit.oI.sp < ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-256) 0).hi := by
    show _ < (0 : Int); decide
  obtain ⟨hR1, -⟩ := callee_facts (kc := Spike.Lib.A64.Abort.oI.sp) (lo' := -256) hR (Spike.Lib.A64.Rt.entryR_al hE)
    l1 (by decide) h1 (by decide)
  have ho1 := out_callee hR (kc := Spike.Lib.A64.Abort.oI.sp) (lo' := -256) l1 (by decide) h1 houtS
  have ho2 := out_callee hR1 (kc := Ret0.ThreadInit.oI.sp) (lo' := -208) l2 (by decide) h2 ho1
  exact ⟨Ret0.stackM_stable hfit houtS, Ret0.stackM_stable hfit ho1, Ret0.stackM_stable hfit ho2⟩

/-- **The first stack's range is the take's at `k0 = 0`**, at the labels'
`scc_rt_stacks`: `startAllUW_gen`'s `hrS` at `hgen`. -/
theorem rS0_eq_lab (L : RuntimeLayout) :
    Spike.Lib.A64.Rt.rS0 L = ⟨(Ret0.stacksA L.lab + 0#64).toNat, 16384⟩ := by
  rw [Spike.Lib.A64.Rt.rS0, ← L.lab_stacks]

end StartPrems

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {d : Decl}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (immsOf d)

/-- The facts every state of the run carries, at the overflow stub's write
tail. -/
local notation "WS" h:max lbl:max => fun s c => SFacts (Ly h).Λ (μ (Ly h)) (Spike.Lib.A64.PhRec.own (Ly h))
  (Spike.Lib.A64.Rt.rS0 (Ly h)) (Spike.Lib.A64.PhRec.Tk (Ly h)) lbl s c (OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab)

/-- The placement's memory side. -/
local notation "MS" h:max G:max lbl:max lsize:max => msOf (Ly h).Λ (μ (Ly h)) (fun _ => True) G
  (Spike.Lib.A64.PhRec.own (Ly h)) lbl lsize

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.A64.PhRec.GOf (Ly h) (Spike.Lib.A64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The loaded thread. -/
local notation "S0" h => Scc.Sem.A64.threadAt Scc.Sem.Entry.linux (Ly h).Λ.code.lo (O).prog
  (Scc.Sem.loadSyms (Ly h).Λ (O).secs.rodata)

/-- **The AArch64 compiler theorem at an admissible entry state `E`**
(`hE`), with the runtime's start as a hypothesis (`hgen`) and no static
label (`hs`): `Correct` over the target on
parsed texts at `E`. -/
theorem a64_lower_correctE (hd : Scc.Lower.Accepted0 [d] = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg [d] = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (Ly h).Λ)
    -- Runtime: `startAllUW_gen`'s conclusion
    (hgen : ∀ cx : FnCtx, cx.frame ≤ 4095 →
      SwUW (WS h (Ly h).Λ.static) (K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))) [d] (Ly h).Λ.static (Ly h).exe
        (Ly h).endPc (entryR E) (fun m => rtF (Ly h) m ∧ StackM (Spike.Lib.A64.Rt.rS0 (Ly h)) m)
        (MS h (G0 h) (Ly h).Λ.static (fun _ => 0)) (Spike.Lib.A64.Rt.rS0 (Ly h))
        (Ret0.pinA (Ly h).lab + 0#64 + 8#64) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame)
        (UPost [d] (Ly h).Λ.static Spike.Lib.A64Consumer.c0) →
      StartAllUW (WS h (Ly h).Λ.static) (K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))) [d] (Ly h).Λ.static
        (Ly h).exe (Ly h).endPc (entryR E) (rtF (Ly h)) (MS h (G0 h) (Ly h).Λ.static (fun _ => 0))
        (Spike.Lib.A64.Rt.rS0 (Ly h)) 0#64 0#64 Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC
        (cx.frame + 48) (Int64.ofInt cx.frame) (UPost [d] (Ly h).Λ.static Spike.Lib.A64Consumer.c0)) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d]) (Ly h).Λ B
      ((O).prog, (O).secs) := by
  have hload : ∃ t0, (TParE E).load ((O).prog, (O).secs) (Ly h).Λ = some t0 :=
    ⟨_, Scc.Cert.Link.A64.loadParsed_of_loadOk (loadOk_link_of_placeOKAt (i := immsOf d) h) hE.1⟩
  obtain ⟨cx, r, -, entry, hr, -, -, hf, h1, h16, hpro, hbody, hphB, hphP, hab⟩ :=
    mainPh_ofPlaceOK hd hlow h (immsOf d)
  have hss0 : imageOk (Ly h).Λ (O).secs (Scc.Cert.Link.A64.codeOf (Ly h).Λ.code.lo (O).prog) = true :=
    imageIn_link_of_placeOKAt (i := immsOf d) h
  have hss : Scc.Sem.StaticSyms (Ly h).Λ (O).secs (Scc.Cert.Link.A64.codeOf (Ly h).Λ.code.lo (O).prog)
      (fun _ => 0) (fun _ => "") :=
    Scc.Sem.StaticSyms.of_none hs
  have hs' : (Ly h).Λ.static = fun _ => none := funext hs
  have htl := tail_bare_of_accepted0 hd hlow
  have hseg := a64_start_segW h (immsOf d) hd htl hf h1 h16 hpro hr hbody
    (Dt := OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab) (rd := fun _ => True) (G := G0 h) (hs' ▸ rtFree_ofPlaceOK h _) hE
    hphB hphP Ret0.Inst.cfacts_c0 hab rfl
    (fun _ _ hal hlo hhi _ _ _ hA => ovfDt_of_at hal hlo hhi hA)
    (hGh_ofPlaceOK h _) (hGf_ofPlaceOK h _) (hGt_ofPlaceOK h _) (hownT_ofPlaceOK h _) (hG1_ofPlaceOK h _)
    (hG0_ofPlaceOK h _) (hGn_ofPlaceOK h _) (hownL_ofPlaceOK h _) (hownF_ofPlaceOK h _) (hownN_ofPlaceOK h _)
    (hroomM_ofPlaceOK h _) (hroomU_ofPlaceOK h _ (Int.natCast_nonneg _) (by omega))
    (Spike.Lib.A64.PhRec.hmph_ofPlaceOK h _ htl)
    (Spike.Lib.A64.PhRec.hsw_ofPlaceOK h _)
    (Spike.Lib.A64.Rt.entryW_ofPlaceOK h _ (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE)
      (by show (-65536 : Int) ≤ 0; decide) (by show (0 : Int) ≤ 0; decide) Ret0.Inst.cfacts_c0) (hgen cx h1)
    (Q := fun _ _ => False)
  obtain ⟨inv, hP, hN, hT, hA, hWr⟩ :=
    Spike.Lib.A64Consumer.inst_of_segW hseg (Spike.Lib.A64.PhRec.site_ofPlaceOK h _) (fun _ _ h => h)
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (immsOf d) (rS := Spike.Lib.A64.Rt.rS0 (Ly h))
  exact Spike.Lib.A64Consumer.correctA64PE' (lsize := fun _ => 0) (name := fun _ => "") hss0 hss
    (wideIn_of_placeOKAt h) ⟨rfl, rfl, hP _ _ (entry_atE h _ hE (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E))⟩
    hload (.none (Spike.Lib.srcP1_hooks arch))
    (Spike.Lib.srcP1_init arch) hN (Spike.Lib.A64Consumer.safe_of_accepted0 hd arch _) hT
    (Spike.Lib.A64.PhRec.htk0_of_pc h _ (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E))
    (Spike.Lib.A64.PhRec.hown0_of_pcE h _ hE.1 (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E))
    (Spike.Lib.A64Consumer.writeNoProm_of_tail (tailNoFul_ovf hI (abortIn_of_placeOKAt h)
      (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h _) (hrel_ofPlaceOK h _) (htk_ofPlaceOK h _) hWr))
    (fun _ => trivial) (wf_link_of_placeOKAt (i := immsOf d) h) (Spike.Lib.A64.PhRec.G0_ofPlaceOKE h _ hE.1)
    (Spike.Lib.A64.PhRec.hGpl_ofPlaceOK h _) hA
    (fun h => h)

/-- **The AArch64 compiler theorem, with the runtime's start as a hypothesis** (`hgen`). -/
theorem a64_lower_correct (hd : Scc.Lower.Accepted0 [d] = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg [d] = .ok em) (h : placeOK pcfg (O) = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion
    (hgen : ∀ cx : FnCtx, cx.frame ≤ 4095 →
      SwUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static (Ly (atTables h)).exe
        (Ly (atTables h)).endPc (entryR Scc.Sem.Entry.linux) (fun m => rtF (Ly (atTables h)) m ∧ StackM
            (Spike.Lib.A64.Rt.rS0 (Ly (atTables h))) m)
        (MS (atTables h) (G0 (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0)) (Spike.Lib.A64.Rt.rS0 (Ly
            (atTables h)))
        (Ret0.pinA (Ly (atTables h)).lab + 0#64 + 8#64) (Ret0.stacksA (Ly (atTables h)).lab + 0#64 + 16384#64)
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame)
        (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0) →
      StartAllUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static
        (Ly (atTables h)).exe (Ly (atTables h)).endPc (entryR Scc.Sem.Entry.linux) (rtF (Ly (atTables h))) (MS
            (atTables h) (G0 (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0))
        (Spike.Lib.A64.Rt.rS0 (Ly (atTables h))) 0#64 0#64 Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC
        (cx.frame + 48) (Int64.ofInt cx.frame) (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0)) :
    Scc.Sem.Correct TPar (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d]) (Ly (atTables h)).Λ B
      ((O).prog, (O).secs) :=
  a64_lower_correctE hd hlow (atTables h) (fun _ => rfl) (RuntimeLayout.linux_ok_ofPlaceOK (atTables h) (immsOf d)) hgen

set_option maxRecDepth 100000 in
/-- **The lowering succeeds on an output passing `placeOK`**: where
`lowerAll?` fails, `lowerAll`'s output is empty and fails the check. -/
theorem lowerAll?_ok_of_placeOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    ∃ em, Scc.Lower.A64.lowerAll? cfg [d] = .ok em := by
  cases he : Scc.Lower.A64.lowerAll? cfg [d] with
  | ok em => exact ⟨em, rfl⟩
  | error _ =>
    unfold Scc.Lower.A64.lowerAll at h
    rw [he] at h
    have h0 : placeOKAt pcfg Λ (Out.ofEmitted (default : Scc.Lower.A64.Emitted)) = false := by
      simp [placeOKAt, Checks.ok, checks, show a11 (Out.ofEmitted (default : Scc.Lower.A64.Emitted)) ⟨Λ⟩ = false
        from rfl]
    exact absurd h (by rw [h0]; decide)

/-- **The AArch64 compiler theorem at a certificate's facts**: for a
program `[d]` that `scc` accepts (`hd`, the certificate's `prog_accepted`)
and whose output passes the placement check (`h`, its `prog_placeOK`), the
output is `Correct` over the canonical target, at the static link of the
output with the lowering's immediates, for every budget and architecture.
Its `hgen` premise is discharged by `hgen_ofPlaceOK` (`a64_scc_correctE_closed`). -/
theorem a64_scc_correct (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion
    (hgen : ∀ cx : FnCtx, cx.frame ≤ 4095 →
      SwUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static (Ly (atTables h)).exe
        (Ly (atTables h)).endPc (entryR Scc.Sem.Entry.linux) (fun m => rtF (Ly (atTables h)) m ∧ StackM
            (Spike.Lib.A64.Rt.rS0 (Ly (atTables h))) m)
        (MS (atTables h) (G0 (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0)) (Spike.Lib.A64.Rt.rS0 (Ly
            (atTables h)))
        (Ret0.pinA (Ly (atTables h)).lab + 0#64 + 8#64) (Ret0.stacksA (Ly (atTables h)).lab + 0#64 + 16384#64)
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame)
        (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0) →
      StartAllUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static
        (Ly (atTables h)).exe (Ly (atTables h)).endPc (entryR Scc.Sem.Entry.linux) (rtF (Ly (atTables h))) (MS
            (atTables h) (G0 (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0))
        (Spike.Lib.A64.Rt.rS0 (Ly (atTables h))) 0#64 0#64 Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC
        (cx.frame + 48) (Int64.ofInt cx.frame) (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0)) :
    Scc.Sem.Correct TPar (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { (tablesOf pcfg (O)).Λ with imms := immsOf d } B ((O).prog, (O).secs) :=
  have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK (atTables h)
  a64_lower_correct hd hlow h hgen

/-- **The AArch64 compiler theorem on the text**: `a64_scc_correct` carried
from the parsed pair to the assembler text `asm` by the parse check `hpa`
(`correct_of_parsed`). `hpa` is the certificate's
`#guard Scc.Cert.Link.A64.parsesTo asm out.prog out.secs`, evaluated by the
compiler, not checked by the kernel: the trust boundary.
The placement premise `h` is at any configuration `pcfg` (the
certificate's `placeCfg`), the layout its link. Its `hgen` premise is discharged by `hgen_ofPlaceOK`
(`a64_scc_correctE_text_closed`). -/
theorem a64_scc_correct_text (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {asm : String} (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion
    (hgen : ∀ cx : FnCtx, cx.frame ≤ 4095 →
      SwUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static (Ly (atTables h)).exe
        (Ly (atTables h)).endPc (entryR Scc.Sem.Entry.linux) (fun m => rtF (Ly (atTables h)) m ∧ StackM
            (Spike.Lib.A64.Rt.rS0 (Ly (atTables h))) m)
        (MS (atTables h) (G0 (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0)) (Spike.Lib.A64.Rt.rS0 (Ly
            (atTables h)))
        (Ret0.pinA (Ly (atTables h)).lab + 0#64 + 8#64) (Ret0.stacksA (Ly (atTables h)).lab + 0#64 + 16384#64)
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame)
        (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0) →
      StartAllUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static
        (Ly (atTables h)).exe (Ly (atTables h)).endPc (entryR Scc.Sem.Entry.linux) (rtF (Ly (atTables h))) (MS
            (atTables h) (G0 (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0))
        (Spike.Lib.A64.Rt.rS0 (Ly (atTables h))) 0#64 0#64 Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC
        (cx.frame + 48) (Int64.ofInt cx.frame) (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0)) :
    Scc.Sem.Correct Spike.Lib.A64Consumer.T (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { (tablesOf pcfg (O)).Λ with imms := immsOf d } B asm :=
  let ⟨h1, h2⟩ := Scc.Cert.Link.A64.parsed_of_parsesTo hpa
  Scc.Sem.A64.correct_of_parsed _ _ h1 h2 (a64_scc_correct hd h hgen)

/-- **The AArch64 compiler theorem at every admissible entry state**: for a
program `[d]` that `scc` accepts (`hd`) and whose output passes the
placement check (`h`), the output is `Correct` over the target on parsed
texts at every entry state `E` that `Entry.Ok` admits for the output's
static link. Its `hgen` premise is discharged by `hgen_ofPlaceOK`
(`a64_scc_correctE_closed`). -/
theorem a64_scc_correctE (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion, at every admissible entry state
    (hgen : ∀ E : Entry, E.Ok (Ly (atTables h)).Λ → ∀ cx : FnCtx, cx.frame ≤ 4095 →
      SwUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static (Ly (atTables h)).exe
        (Ly (atTables h)).endPc (entryR E) (fun m => rtF (Ly (atTables h)) m ∧ StackM (Spike.Lib.A64.Rt.rS0 (Ly
            (atTables h))) m)
        (MS (atTables h) (G0 (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0)) (Spike.Lib.A64.Rt.rS0 (Ly
            (atTables h)))
        (Ret0.pinA (Ly (atTables h)).lab + 0#64 + 8#64) (Ret0.stacksA (Ly (atTables h)).lab + 0#64 + 16384#64)
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame)
        (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0) →
      StartAllUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static
        (Ly (atTables h)).exe (Ly (atTables h)).endPc (entryR E) (rtF (Ly (atTables h))) (MS (atTables h) (G0
            (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0))
        (Spike.Lib.A64.Rt.rS0 (Ly (atTables h))) 0#64 0#64 Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC
        (cx.frame + 48) (Int64.ofInt cx.frame) (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0)) :
    ∀ E : Entry, E.Ok { (tablesOf pcfg (O)).Λ with imms := immsOf d } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { (tablesOf pcfg (O)).Λ with imms := immsOf d } B ((O).prog, (O).secs) :=
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK (atTables h)
    a64_lower_correctE hd hlow (atTables h) (fun _ => rfl) hE (hgen E hE)

/-- **The AArch64 compiler theorem on the text, at every admissible entry
state** (`Scc.Sem.A64.CorrectE`): `a64_scc_correctE` carried from the parsed
pair to the assembler text `asm` by the parse check `hpa`
(`correct_of_parsed` at each `E`). `hpa` is the certificate's compiled
`#guard`, the trust boundary. Its `hgen` premise is discharged by
`hgen_ofPlaceOK` (`a64_scc_correctE_text_closed`). -/
theorem a64_scc_correctE_text (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {asm : String} (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion, at every admissible entry state
    (hgen : ∀ E : Entry, E.Ok (Ly (atTables h)).Λ → ∀ cx : FnCtx, cx.frame ≤ 4095 →
      SwUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static (Ly (atTables h)).exe
        (Ly (atTables h)).endPc (entryR E) (fun m => rtF (Ly (atTables h)) m ∧ StackM (Spike.Lib.A64.Rt.rS0 (Ly
            (atTables h))) m)
        (MS (atTables h) (G0 (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0)) (Spike.Lib.A64.Rt.rS0 (Ly
            (atTables h)))
        (Ret0.pinA (Ly (atTables h)).lab + 0#64 + 8#64) (Ret0.stacksA (Ly (atTables h)).lab + 0#64 + 16384#64)
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame)
        (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0) →
      StartAllUW (WS (atTables h) (Ly (atTables h)).Λ.static) (K (Ly (atTables h)) (Spike.Lib.A64.Rt.rS0 (Ly
          (atTables h)))) [d] (Ly (atTables h)).Λ.static
        (Ly (atTables h)).exe (Ly (atTables h)).endPc (entryR E) (rtF (Ly (atTables h))) (MS (atTables h) (G0
            (atTables h)) (Ly (atTables h)).Λ.static (fun _ => 0))
        (Spike.Lib.A64.Rt.rS0 (Ly (atTables h))) 0#64 0#64 Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC
        (cx.frame + 48) (Int64.ofInt cx.frame) (UPost [d] (Ly (atTables h)).Λ.static Spike.Lib.A64Consumer.c0)) :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { (tablesOf pcfg (O)).Λ with imms := immsOf d } B asm :=
  fun E hE =>
    let ⟨h1, h2⟩ := Scc.Cert.Link.A64.parsed_of_parsesTo hpa
    Scc.Sem.A64.correct_of_parsed _ E h1 h2 (a64_scc_correctE hd h hgen E hE)

/-- **`hgen` from `placeOK`** (`startAllUW_gen`): at every admissible entry
state `E`, `scc_rt_start`'s blocks after `_start` are inside the run's facts
given the switch's and `scc_rt_main`'s obligations, at the entry stack's
region `entryR E` (`entryR_ok`, `entryR_al`, its 64 KiB below the entry
stack), the first stack `rS0` (`rS0_eq_lab`, `rS0_sub`) stable in
`scc_rt_start`'s three regions (`stackM_rS0`), A6's table (`rtPh_of_placeOKAt`)
and `c0`'s facts (`cfacts_c0`). This is the compiler theorem's `hgen`. -/
theorem hgen_ofPlaceOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    ∀ E : Entry, E.Ok (Ly h).Λ → ∀ cx : FnCtx, cx.frame ≤ 4095 →
      SwUW (WS h (Ly h).Λ.static) (K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))) [d] (Ly h).Λ.static (Ly h).exe
        (Ly h).endPc (entryR E) (fun m => rtF (Ly h) m ∧ StackM (Spike.Lib.A64.Rt.rS0 (Ly h)) m)
        (MS h (G0 h) (Ly h).Λ.static (fun _ => 0)) (Spike.Lib.A64.Rt.rS0 (Ly h))
        (Ret0.pinA (Ly h).lab + 0#64 + 8#64) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame)
        (UPost [d] (Ly h).Λ.static Spike.Lib.A64Consumer.c0) →
      StartAllUW (WS h (Ly h).Λ.static) (K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))) [d] (Ly h).Λ.static
        (Ly h).exe (Ly h).endPc (entryR E) (rtF (Ly h)) (MS h (G0 h) (Ly h).Λ.static (fun _ => 0))
        (Spike.Lib.A64.Rt.rS0 (Ly h)) 0#64 0#64 Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC
        (cx.frame + 48) (Int64.ofInt cx.frame) (UPost [d] (Ly h).Λ.static Spike.Lib.A64Consumer.c0) :=
  fun E hE _ _ hs3 => Spike.Lib.A64.Rt.startAllUW_gen h (immsOf d) (rtPh_of_placeOKAt h) Ret0.Inst.cfacts_c0
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) (fun _ hm => hm) rfl (rS0_eq_lab _) (Spike.Lib.A64.Rt.rS0_sub _)
    (stackM_rS0 _ hE).1 (stackM_rS0 _ hE).2.1 (stackM_rS0 _ hE).2.2 hs3

/-- **The AArch64 compiler theorem at every admissible entry state, closed**:
`a64_scc_correctE` with its `hgen` discharged (`hgen_ofPlaceOK`). For a
program `[d]` that `scc` accepts (`hd`) and whose output passes the
placement check (`h`), the output is `Correct` over the target on parsed
texts at every entry state `E` that `Entry.Ok` admits. -/
theorem a64_scc_correctE_closed (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { (tablesOf pcfg (O)).Λ with imms := immsOf d } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { (tablesOf pcfg (O)).Λ with imms := immsOf d } B ((O).prog, (O).secs) :=
  a64_scc_correctE hd h (hgen_ofPlaceOK (atTables h))

/-- **The AArch64 compiler theorem on the text, at every admissible entry
state, closed** (`Scc.Sem.A64.CorrectE`): `a64_scc_correctE_text` with its
`hgen` discharged (`hgen_ofPlaceOK`); its only premises are `Accepted0`, the
placement check and the parse check `hpa`. -/
theorem a64_scc_correctE_text_closed (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {asm : String} (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { (tablesOf pcfg (O)).Λ with imms := immsOf d } B asm :=
  a64_scc_correctE_text hd h hpa (hgen_ofPlaceOK (atTables h))

/-- **The AArch64 compiler theorem at any layout, closed**: for a program
`[d]` that `scc` accepts (`hd`) and whose output passes the placement check
at a layout `Λ` (`h`; `Λ` read off an executable, say, in place of the
static link), the output is `Correct` over the kernel-model target
`target (kernel 1) E` on parsed texts at every entry state `E` that
`Entry.Ok` admits, at `Λ` with no static label and the lowering's
immediates. The placement check reads neither field (`placeOKAt_static`); a
program in the fragment (`Accepted0`) allocates no static label, and `imms`
is the proof's table of constants folded into instructions, not an input of the loader
nor of anything `Correct` fixes outside the witness. -/
theorem a64_scc_correctE_closedAt (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := immsOf d } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { Λ with static := fun _ => none, imms := immsOf d } B ((O).prog, (O).secs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (O) = true :=
    (Scc.Cert.PlaceOK.A64.placeOKAt_static pcfg Λ (O) (fun _ => none) Λ.imms).trans h
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK h
    a64_lower_correctE hd hlow h' (fun _ => rfl) hE (hgen_ofPlaceOK h' E hE)

/-- **The AArch64 compiler theorem on the text, at any layout, closed**
(`Scc.Sem.A64.CorrectE`): for a program `[d]` that `scc` accepts (`hd`),
whose output passes the placement check at a layout `Λ` (`h`) and whose
assembler text `asm` the loader parses to it (`hpa`, the certificate's
compiled `#guard`, the trust boundary), `asm` is `Correct` over the
kernel-model target `target (kernel 1) E` at every admissible entry state
`E`, at `Λ` with no static label and the lowering's immediates. The
placement check reads neither field (`placeOKAt_static`); a program in the
fragment (`Accepted0`) allocates no static label, and `imms` is the proof's
table of constants folded into instructions, not an input of the loader
nor of anything `Correct` fixes outside the witness.

If the program exits, it exits as the source does; the theorem does not
promise that it exits. `Correct` is a safety and refinement statement:
every finite observable trace of the target, including one that ends in
exit, is a trace of the source; a target that diverges or blocks before
exiting satisfies it. -/
theorem a64_scc_correctE_text_closedAt (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := immsOf d } B asm :=
  fun E hE =>
    let ⟨h1, h2⟩ := Scc.Cert.Link.A64.parsed_of_parsesTo hpa
    Scc.Sem.A64.correct_of_parsed _ E h1 h2 (a64_scc_correctE_closedAt Λ hd h E hE)

end Correct

end Spike.Lib.LowerA64
