/-
**The x86-64 compiler theorem's assembly** (B8, the twin of
`Spike/Lib/LowerA64/Correct.lean`): for an `Accepted0` program `[d]` whose
lowering `lowerAll cfg [d]` passes `placeOKAt` at a layout `Λ`, the output
is `Correct` over the kernel-model target on parsed cells, at the runtime's
layout with the lowering's immediates (`RuntimeLayout.ofPlaceOK h (immsOf d)`).

Every admissible entry state: `x64_lower_correctE` is the theorem at any
entry state `E` that `Entry.Ok` admits (the entry stack's region `entryR E`,
`entry_atXE`, the load at `E`), `x64_scc_correctE_text` its release form
`Scc.Sem.X64.CorrectE 1`; `x64_lower_correct` and `x64_scc_correct{,_text}`
are them at `Entry.linux` (`linux_ok_ofPlaceOK`).

The proof composes the pieces: `mainPh_ofPlaceOK` (`main`'s code and phase facts),
`x64_start_segW` (the run from `scc_rt_start`, as the callee continuation
of `_start`'s call), `_start`'s segment in front of it (`entry_segW_take`),
`inst_of_segW` (the consumer's `Nodes`, `TakePath`, `AbortPath`, `WrIn`),
the overflow stub's write tail (`ovfDt_of_at`, `tailNoFul_ovf`) with
`writeNoProm_of_tail` (`WriteNoProm`), and
`correctX64P'`.

The source parameters are `srcP1 arch` (`Spike/Lib/SrcP1.lean`): one thread
(`cap 1`) starting at `main` (`mainInit 1`), no hooks. They restrict the
source semantics to the single-threaded, hook-free programs `Accepted0`
admits.

Discharged here: the write tail (`OvfDt`), the immediates (`rfl`), the
image and its static symbols (`imageIn_link_of_placeOKAt`,
`StaticSyms.of_none`), the load (`loadParsed_of_loadOk`), the link's
well-formedness, `wideIn`, the marks, the abort path's start, the loaded
thread at `_start`'s node (`entry_atX`, at `hpc_ofPlaceOK`, A1), `RtFree` at
`Λ.static` (`fun _ => none`), `c0`'s facts (`cfacts_c0`), and the runtime's
premises from `PlaceOK` (`Spike/Lib/X64StartOfPlaceOK.lean`: the value
invariant `GOf` at the loaded memory, `MemInv` at load, the runtime's
stores, the rooms, the counters' ownership given their phases; on the heap
and data off the TCB's limit word, `hclr_ofPlaceOK`, A8; the loaded thread's
phase and owned words at `_start`, its phase from A6's table,
`hph0_ofPlaceOK`), `_start`'s nodes inside the run's facts
(`entryW_ofPlaceOK`), the source's safety (`safe_of_accepted0`), and the
runtime main's and the switch's phase records (`mainPh_bare_ofPlaceOK`,
`swPh_ofPlaceOK`), and the phases of the runtime's atomic accesses, which own
their counters at `0` (`hphT_ofPlaceOK`, `hphL_ofPlaceOK`, `hphN_ofPlaceOK`,
A6's phase pins), and the overflow exit call's site premises (`hrel_ofPlaceOK`,
`htk_ofPlaceOK`, `hk_ofPlaceOK`, `hKex_ofPlaceOK`, A6's sites distinct), and the user `main`'s code and phase facts
(`mainPh_ofPlaceOK`, P5, with its overflow block for a nonempty body, B2).

The theorems with an `hgen` premise keep it for their callers; it is no
longer open work: `hgen_ofPlaceOK` discharges it from the placement check
at every admissible entry state (`startAllUW_gen`,
`Spike/Lib/Rt/X64RtStartU.lean`, with `ec_facts`). `x64_scc_correctE_closed`
and `x64_scc_correctE_text_closed` are `x64_scc_correctE{,_text}` without it,
at the static link; `x64_scc_correctE_closedAt` and
`x64_scc_correctE_text_closedAt` (the release statement) are them at any
layout `Λ` passing `placeOKAt`, with no static label.
-/
import Spike.Lib.LowerX64.StartSeg
import Spike.Lib.X64Accepted0Safe
import Spike.Lib.Rt.X64RtPhRec
import Spike.Lib.LowerX64.OvfDt
import Spike.Lib.Rt.X64Entry
import Spike.Lib.Rt.X64EntryOfPlaceOK
import Spike.Lib.LowerX64.MainPh
import Spike.Lib.X64CorrectP
import Spike.Lib.X64TailNoFul
import Spike.Lib.X64Ret0Correct
import Spike.Lib.SrcP1
import Spike.Lib.X64StartOfPlaceOK
import Spike.Lib.X64PhPinsOfPlaceOK
import Scc.Sem.CorrectEX64
import Spike.Lib.Rt.X64RtStartU

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Lower.Inv (lower0 Res)
open Spike.Lib.Form (lookupS SEnv)
open Spike.Lib.LowerNode (AbSrc immsOf)
open Spike.Lib.X64Consumer (CFacts SFacts Lbl Lsize blkPh msOf IOf TPar TParE)
open Spike.Lib.X64.Rt (RuntimeLayout SwUW StartAllUW bareMC rtF entryR)
open Spike.Lib.X64.Flow.Ret0 (StackM limA tpOf startN0)
open Spike.Lib.X64.PhRec (μ K)
open Scc.Sem Scc.Sem.X64 Scc.Cert.Link Spike.Lib.Consumer1
open Spike.Lib.X64.PhRec (rtFree_ofPlaceOK G0_ofPlaceOK hGh_ofPlaceOK hGf_ofPlaceOK hGt_ofPlaceOK hG1_ofPlaceOK
  hG0_ofPlaceOK hGn_ofPlaceOK hroomM_ofPlaceOK hroomU_ofPlaceOK hGpl_ofPlaceOK htk0_ofPlaceOK hown0_ofPlaceOK
  hownT_of_ph hownL_of_ph hownF_ofPlaceOK hownN_of_ph hph0_of
  hph0_ofPlaceOK hphT_ofPlaceOK hphL_ofPlaceOK hphN_ofPlaceOK G0_ofPlaceOKE hown0_ofPlaceOKE)

section Entry

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option maxRecDepth 100000 in
/-- **The loaded thread is at `_start`'s node** on the entry stack
(`entryR E`) of an admissible entry state `E` (`hE`), the runtime's words
unloaded (`rtF_stackMem`), the source at `main`'s start, given the loaded
pc is `_start`'s (`hpc`). -/
theorem entry_atXE {E : Entry} (hE : E.Ok (RuntimeLayout.ofPlaceOK h i).Λ)
    (hpc : (Scc.Sem.X64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceOK h i).lab "_start") :
    At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc (entryR E)
      (rtF (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.X64.Rt.entryN0 (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.X64Consumer.c0)
      (Scc.Sem.X64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) Spike.Lib.X64Consumer.c0 := by
  refine ⟨rfl, Scc.Cert.Link.X64.endPc_threadAt _ _ _ _ (RuntimeLayout.ofPlaceOK_above h i), rfl, hpc,
    ⟨{ rsp := UInt64.ofNat E.sp }, _, _, fun k =>
      BitVec.ofInt 64 ((Mem.loadInt E.stackMem ((entryR E).addr k) 8).getD 0)⟩,
    ⟨rfl, rfl, rfl, ?_, ?_⟩, Spike.Lib.X64.Rt.rtF_stackMem _ hE rfl, rfl⟩
  · intro r k hr
    simp only [Spike.Lib.X64.Rt.entryN0, SO.get] at hr
    split at hr
    · rename_i he
      subst he
      cases hr
      dsimp only
      show (UInt64.ofNat E.sp).toBitVec = BitVec.ofNat 64 E.sp + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl
    · simp [lk] at hr
  · intro k hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (Spike.Lib.X64.Rt.stack_wordE hE hk)
    refine ⟨j, hj, ?_⟩
    show _ = BitVec.ofInt 64 ((Mem.loadInt E.stackMem _ 8).getD 0)
    rw [hj]; rfl

set_option maxRecDepth 100000 in
/-- **The loaded thread is at `_start`'s node** on the entry stack (`entryR`),
the runtime's words unloaded (`rtF_stackMem`), the source at `main`'s start:
`ret0_entry`'s generic form, given the loaded pc is `_start`'s (`hpc`). -/
theorem entry_atX (hpc : (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceOK h i).lab "_start") :
    At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc (entryR Scc.Sem.Entry.linux)
      (rtF (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.X64.Rt.entryN0 (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.X64Consumer.c0)
      (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) Spike.Lib.X64Consumer.c0 :=
  entry_atXE h i (RuntimeLayout.linux_ok_ofPlaceOK h i) hpc

end Entry

section StartPrems

/-- **The first stack's range is the take's at `k0 = 0`**, at the labels'
`scc_rt_stacks`: `startAllUW_gen`'s `hrS` at the compiler theorem's `hgen`
(as `Spike.Lib.LowerA64.rS0_eq_lab`). -/
theorem rS0_eq_lab (L : RuntimeLayout) :
    Spike.Lib.X64.Rt.rS0 L = ⟨(Ret0.stacksA L.lab + 0#64).toNat, 16384⟩ := by
  rw [Spike.Lib.X64.Rt.rS0, ← L.lab_stacks]

end StartPrems

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {d : Decl} {sizes : List Nat}
  {labelOffs : List (String × Nat)}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (immsOf d)

/-- The facts every state of the run carries, at the overflow stub's write
tail. -/
local notation "WS" h:max lbl:max => fun s c => SFacts (Ly h).Λ (μ (Ly h))
  (Spike.Lib.X64.PhRec.own (Ly h)) (Spike.Lib.X64.Rt.rS0 (Ly h)) (Spike.Lib.X64.PhRec.Tk (Ly h)) lbl s c
  (OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab)

/-- The placement's memory side. -/
local notation "MS" h:max G:max => msOf (Ly h).Λ (μ (Ly h)) (fun _ => True) G
  (Spike.Lib.X64.PhRec.own (Ly h)) (Ly h).Λ.static (fun _ => 0)

/-- The callee region of `_start`'s call at the entry state `E`, where
`scc_rt_start` runs. -/
local notation "EC" E:max => (entryR E).callee (-8) (-296) 8

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.X64.PhRec.GOf (Ly h) (Spike.Lib.X64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The loaded thread. -/
local notation "S0" h => Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (Ly h).Λ.code.lo (O).prog
  (Scc.Sem.loadSyms (Ly h).Λ (O).secs.rodata)

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.X64.Rt.rS0 (Ly h))

/-- **The x86-64 compiler theorem at an admissible entry state `E`**
(`hE`), with the runtime's start as a hypothesis (`hgen`) and no static
label (`hs`): `Correct` over the target on parsed texts at `E`. -/
theorem x64_lower_correctE (hd : Scc.Lower.Accepted0 [d] = true) {em : Scc.Lower.X64.Emitted}
    (hlow : Scc.Lower.X64.lowerAll? cfg [d] = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (Ly h).Λ)
    -- Runtime: `startAllUW_gen`'s conclusion
    (hgen : ∀ fr : Scc.Emit.X64.Frame, fr.size ≤ 4096 →
      ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (KS h) F' → (∀ m, F' m → rtF (Ly h) m) →
      SwUW (WS h (Ly h).Λ.static) (KS h) [d] (Ly h).Λ.static (Ly h).exe (Ly h).endPc (EC E)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Ly h)) m) (MS h (G0 h)) (Spike.Lib.X64.Rt.rS0 (Ly h))
          (Ret0.pinA (Ly h).lab + 0#64 + 8#64) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size)
          (UPost [d] (Ly h).Λ.static Spike.Lib.X64Consumer.c0) →
        StartAllUW (WS h (Ly h).Λ.static) (KS h) [d] (Ly h).Λ.static (Ly h).exe (Ly h).endPc (EC E) F'
          (MS h (G0 h)) (Spike.Lib.X64.Rt.rS0 (Ly h)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UPost [d] (Ly h).Λ.static Spike.Lib.X64Consumer.c0)) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d]) (Ly h).Λ B
      ((O).prog, (O).secs, (O).labelOffs) := by
  have hload : ∃ t0, (TParE E).load ((O).prog, (O).secs, (O).labelOffs) (Ly h).Λ = some t0 :=
    ⟨_, Scc.Cert.Link.X64.loadParsed_of_loadOk (loadOk_link_of_placeOKAt (i := immsOf d) h) hE.1⟩
  have hss0 : imageOk (Ly h).Λ (O).secs (Scc.Sem.X64.codeLabel (Ly h).Λ.code.lo (O).prog) = true :=
    imageIn_link_of_placeOKAt (i := immsOf d) h
  have hss : Scc.Sem.StaticSyms (Ly h).Λ (O).secs (Scc.Sem.X64.codeLabel (Ly h).Λ.code.lo (O).prog)
      (fun _ => 0) (fun _ => "") :=
    Scc.Sem.StaticSyms.of_none hs
  have hs' : (Ly h).Λ.static = fun _ => none := funext hs
  obtain ⟨fr, r, entry, zl, zf, z1, z2, zs, hr, hf, h4, h16, hpro, hbody, hphB, hphP, hab⟩ :=
    mainPh_ofPlaceOK hd hlow h (immsOf d)
  have hpc := Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h (immsOf d) E
  have hS := x64_start_segW h (immsOf d) hd hf h4 h16 hpro hr hbody
    (Dt := OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab) (rd := fun _ => True) (G := G0 h)
    (hs' ▸ rtFree_ofPlaceOK h _) hE hphB hphP Ret0.Inst.cfacts_c0 hab rfl
    (fun _ _ hlo hhi _ _ _ hA => ovfDt_of_at hlo hhi hA)
    (hGh_ofPlaceOK h _) (hGf_ofPlaceOK h _) (hGt_ofPlaceOK h _)
    (hownT_of_ph h _ (by rw [hphT_ofPlaceOK h _])) (hG1_ofPlaceOK h _) (hG0_ofPlaceOK h _)
    (hGn_ofPlaceOK h _) (hownL_of_ph h _ (by rw [hphL_ofPlaceOK h _])) (hownF_ofPlaceOK h _)
    (hownN_of_ph h _ (by rw [hphN_ofPlaceOK h _]))
    (hroomM_ofPlaceOK h _)
    (hroomU_ofPlaceOK h _ (Int.natCast_nonneg _) (by omega))
    (Spike.Lib.X64.Rt.PhRecOf.mainPh_bare_ofPlaceOK h _) (Spike.Lib.X64.Rt.PhRecOf.swPh_ofPlaceOK h _)
    (hgen fr h4)
  obtain ⟨inv, hP, hN, hT, hA, hWr⟩ :=
    Spike.Lib.X64Consumer.inst_of_segW
      (Spike.Lib.X64.Rt.entry_segW_take (Ly h) hE
        (Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h)).start0
        (Spike.Lib.X64.Rt.rS0_sub (Ly h)) _
        (Spike.Lib.X64.Rt.entryW_ofPlaceOK h _ (Spike.Lib.X64.Rt.entryR_ok hE)
          (by show (-65536 : Int) ≤ -8; decide) (by show (0 : Int) ≤ 0; decide)
          Ret0.Inst.cfacts_c0) hS)
      (Spike.Lib.X64.PhRec.site_ofPlaceOK h _) (fun _ _ h => h)
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (immsOf d) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
  exact Spike.Lib.X64Consumer.correctX64PE' (lsize := fun _ => 0) (name := fun _ => "") hss0 hss
    (wideIn_of_placeOKAt h) ⟨rfl, rfl, hP _ _ (entry_atXE h _ hE hpc)⟩ hload (Spike.Lib.srcP1_hooks arch)
    (Spike.Lib.srcP1_init arch) hN (Spike.Lib.X64Consumer.safe_of_accepted0 hd arch _) hT
    (htk0_ofPlaceOK h _ (hph0_of h _ hpc (hph0_ofPlaceOK h _)))
    (hown0_ofPlaceOKE h _ hE.1 (hph0_of h _ hpc (hph0_ofPlaceOK h _)))
    (Spike.Lib.X64Consumer.writeNoProm_of_tail (tailNoFul_ovf hI (hprog_ofPlaceOK h (immsOf d))
      (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h _) (hrel_ofPlaceOK h _) (htk_ofPlaceOK h _) hWr)) (fun _ => trivial)
    (wf_link_of_placeOKAt (i := immsOf d) h) (G0_ofPlaceOKE h _ hE.1)
    (hGpl_ofPlaceOK h _ (Spike.Lib.X64.PhRec.hclr_ofPlaceOK h _)) hA (fun h => h)

/-- The runtime's layout at the static link of an output passing `placeOK`. -/
local notation "Lyt" h => RuntimeLayout.ofPlaceOK (atTables h) (immsOf d)

/-- `WS`, `MS`, `G0`, `KS` at the static link (`atTables`). -/
local notation "WSt" h:max lbl:max => WS (atTables h) lbl
local notation "MSt" h:max G:max => MS (atTables h) G
local notation "G0t" h:max => G0 (atTables h)
local notation "KSt" h => KS (atTables h)

/-- **The x86-64 compiler theorem, with its open work as hypotheses.** -/
theorem x64_lower_correct (hd : Scc.Lower.Accepted0 [d] = true) {em : Scc.Lower.X64.Emitted}
    (hlow : Scc.Lower.X64.lowerAll? cfg [d] = .ok em) (h : placeOK pcfg (O) = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion
    (hgen : ∀ fr : Scc.Emit.X64.Frame, fr.size ≤ 4096 →
      ∀ F' : MachineData → Prop, FStable (EC Scc.Sem.Entry.linux) F' → KStable (KSt h) F' →
          (∀ m, F' m → rtF (Lyt h) m) →
      SwUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc (EC Scc.Sem.Entry.linux)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Lyt h)) m) (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h))
          (Ret0.pinA (Lyt h).lab + 0#64 + 8#64) (Ret0.stacksA (Lyt h).lab + 0#64 + 16384#64)
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size)
          (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0) →
        StartAllUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc
            (EC Scc.Sem.Entry.linux) F'
          (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0)) :
    Scc.Sem.Correct TPar (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d]) (Lyt h).Λ B
      ((O).prog, (O).secs, (O).labelOffs) :=
  x64_lower_correctE hd hlow (atTables h) (fun _ => rfl) (RuntimeLayout.linux_ok_ofPlaceOK (atTables h) (immsOf d))
    hgen

/-- **The lowering succeeds on an output passing `placeOKAt`**: where
`lowerAll?` fails, `lowerAll`'s output is empty and fails the check (A11). -/
theorem lowerAll?_ok_of_placeOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    ∃ em, Scc.Lower.X64.lowerAll? cfg [d] = .ok em := by
  cases he : Scc.Lower.X64.lowerAll? cfg [d] with
  | ok em => exact ⟨em, rfl⟩
  | error _ =>
    unfold Scc.Lower.X64.lowerAll at h
    rw [he] at h
    have h0 : placeOKAt pcfg Λ (Out.ofEmitted (default : Scc.Lower.X64.Emitted) sizes labelOffs) = false :=
      placeOKAt_eq_false_of_a11 rfl
    exact absurd h (by rw [h0]; decide)

/-- **The x86-64 compiler theorem at a certificate's facts**: for a program
`[d]` that `scc` accepts (`hd`, the certificate's `prog_accepted`) and whose
output at the assembler's sizes and label offsets passes the placement check
(`h`, its `prog_placeOK`), the output is `Correct` over the canonical
target, at the static link of the output with the lowering's immediates,
for every budget and architecture. Its `hgen` premise is discharged by
`hgen_ofPlaceOK` (`x64_scc_correctE_closed`). -/
theorem x64_scc_correct (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion
    (hgen : ∀ fr : Scc.Emit.X64.Frame, fr.size ≤ 4096 →
      ∀ F' : MachineData → Prop, FStable (EC Scc.Sem.Entry.linux) F' → KStable (KSt h) F' →
          (∀ m, F' m → rtF (Lyt h) m) →
      SwUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc (EC Scc.Sem.Entry.linux)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Lyt h)) m) (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h))
          (Ret0.pinA (Lyt h).lab + 0#64 + 8#64) (Ret0.stacksA (Lyt h).lab + 0#64 + 16384#64)
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size)
          (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0) →
        StartAllUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc
            (EC Scc.Sem.Entry.linux) F'
          (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0)) :
    Scc.Sem.Correct TPar (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { (tablesOf pcfg (O)).Λ with imms := immsOf d } B
      ((O).prog, (O).secs, (O).labelOffs) :=
  have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK (atTables h)
  x64_lower_correct hd hlow h hgen

/-- **The x86-64 compiler theorem on the text**: `x64_scc_correct` carried
from the parsed triple to the assembler text `⟨text, sizes, labelOffs⟩` (the
sizes and label offsets the placement check reads) by the parse check `hpa`
(`correct_of_parsed`). `hpa` is the certificate's
`#guard Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs`,
evaluated by the compiler, not checked by the kernel: the trust boundary.
The placement premise `h` is at any configuration `pcfg` (the
certificate's `placeCfg`), the layout its link. Its `hgen` premise is
discharged by `hgen_ofPlaceOK` (`x64_scc_correctE_text_closed`). -/
theorem x64_scc_correct_text (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {text : String} (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion
    (hgen : ∀ fr : Scc.Emit.X64.Frame, fr.size ≤ 4096 →
      ∀ F' : MachineData → Prop, FStable (EC Scc.Sem.Entry.linux) F' → KStable (KSt h) F' →
          (∀ m, F' m → rtF (Lyt h) m) →
      SwUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc (EC Scc.Sem.Entry.linux)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Lyt h)) m) (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h))
          (Ret0.pinA (Lyt h).lab + 0#64 + 8#64) (Ret0.stacksA (Lyt h).lab + 0#64 + 16384#64)
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size)
          (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0) →
        StartAllUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc
            (EC Scc.Sem.Entry.linux) F'
          (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0)) :
    Scc.Sem.Correct Spike.Lib.X64Consumer.T (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { (tablesOf pcfg (O)).Λ with imms := immsOf d } B ⟨text, sizes, labelOffs⟩ :=
  let ⟨h1, h2⟩ := Scc.Cert.Link.X64.parsed_of_parsesTo hpa
  Scc.Sem.X64.correct_of_parsed _ _ h1 h2 (x64_scc_correct hd h hgen)

/-- **The x86-64 compiler theorem at every admissible entry state**: for a
program `[d]` that `scc` accepts (`hd`) and whose output passes the
placement check (`h`), the output is `Correct` over the target on parsed
texts at every entry state `E` that `Entry.Ok` admits for the output's
static link. Its `hgen` premise is discharged by `hgen_ofPlaceOK`
(`x64_scc_correctE_closed`). -/
theorem x64_scc_correctE (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion, at every admissible entry state
    (hgen : ∀ E : Entry, E.Ok (Lyt h).Λ → ∀ fr : Scc.Emit.X64.Frame, fr.size ≤ 4096 →
      ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (KSt h) F' → (∀ m, F' m → rtF (Lyt h) m) →
      SwUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc (EC E)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Lyt h)) m) (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h))
          (Ret0.pinA (Lyt h).lab + 0#64 + 8#64) (Ret0.stacksA (Lyt h).lab + 0#64 + 16384#64)
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size)
          (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0) →
        StartAllUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc (EC E) F'
          (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0)) :
    ∀ E : Entry, E.Ok { (tablesOf pcfg (O)).Λ with imms := immsOf d } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { (tablesOf pcfg (O)).Λ with imms := immsOf d } B ((O).prog, (O).secs, (O).labelOffs) :=
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK (atTables h)
    x64_lower_correctE hd hlow (atTables h) (fun _ => rfl) hE (hgen E hE)

/-- **The x86-64 compiler theorem on the text, at every admissible entry
state** (`Scc.Sem.X64.CorrectE`): `x64_scc_correctE` carried from the parsed
triple to the assembler text `⟨text, sizes, labelOffs⟩` by the parse check
`hpa` (`correct_of_parsed` at each `E`). `hpa` is the certificate's
compiled `#guard`, the trust boundary. Its `hgen` premise is discharged by
`hgen_ofPlaceOK` (`x64_scc_correctE_text_closed`). -/
theorem x64_scc_correctE_text (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {text : String} (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    -- Runtime: `startAllUW_gen`'s conclusion, at every admissible entry state
    (hgen : ∀ E : Entry, E.Ok (Lyt h).Λ → ∀ fr : Scc.Emit.X64.Frame, fr.size ≤ 4096 →
      ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (KSt h) F' → (∀ m, F' m → rtF (Lyt h) m) →
      SwUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc (EC E)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Lyt h)) m) (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h))
          (Ret0.pinA (Lyt h).lab + 0#64 + 8#64) (Ret0.stacksA (Lyt h).lab + 0#64 + 16384#64)
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size)
          (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0) →
        StartAllUW (WSt h (Lyt h).Λ.static) (KSt h) [d] (Lyt h).Λ.static (Lyt h).exe (Lyt h).endPc (EC E) F'
          (MSt h (G0t h)) (Spike.Lib.X64.Rt.rS0 (Lyt h)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UPost [d] (Lyt h).Λ.static Spike.Lib.X64Consumer.c0)) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { (tablesOf pcfg (O)).Λ with imms := immsOf d } B ⟨text, sizes, labelOffs⟩ :=
  fun E hE =>
    let ⟨h1, h2⟩ := Scc.Cert.Link.X64.parsed_of_parsesTo hpa
    Scc.Sem.X64.correct_of_parsed _ E h1 h2 (x64_scc_correctE hd h hgen E hE)

/-- **`hgen` from `placeOKAt`** (`startAllUW_gen`, `Spike/Lib/Rt/X64RtStartU.lean`):
at every admissible entry state `E`, `scc_rt_start`'s blocks after `_start`
are inside the run's facts given the switch's and `scc_rt_main`'s
obligations, in `_start`'s callee region `EC E` (`ec_facts`: it does not
wrap, holds `scc_rt_start`'s frames, and the first stack's words are out of
it), at the first stack `rS0` (`rS0_eq_lab`, `rS0_sub`) and `c0`'s facts
(`cfacts_c0`). This is the compiler theorem's `hgen`. -/
theorem hgen_ofPlaceOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    ∀ E : Entry, E.Ok (Ly h).Λ → ∀ fr : Scc.Emit.X64.Frame, fr.size ≤ 4096 →
      ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (KS h) F' → (∀ m, F' m → rtF (Ly h) m) →
      SwUW (WS h (Ly h).Λ.static) (KS h) [d] (Ly h).Λ.static (Ly h).exe (Ly h).endPc (EC E)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Ly h)) m) (MS h (G0 h)) (Spike.Lib.X64.Rt.rS0 (Ly h))
          (Ret0.pinA (Ly h).lab + 0#64 + 8#64) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size)
          (UPost [d] (Ly h).Λ.static Spike.Lib.X64Consumer.c0) →
        StartAllUW (WS h (Ly h).Λ.static) (KS h) [d] (Ly h).Λ.static (Ly h).exe (Ly h).endPc (EC E) F'
          (MS h (G0 h)) (Spike.Lib.X64.Rt.rS0 (Ly h)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UPost [d] (Ly h).Λ.static Spike.Lib.X64Consumer.c0) :=
  fun E hE _ _ _ _ _ hFF hs3 =>
    have hEC := ec_facts _ hE (Spike.Lib.X64.Rt.rS0_sub _)
    Spike.Lib.X64.Rt.startAllUW_gen h (immsOf d) Ret0.Inst.cfacts_c0 hEC.1 hEC.2.1 hEC.2.2.1 hFF rfl
      (rS0_eq_lab _) (Spike.Lib.X64.Rt.rS0_sub _) hEC.2.2.2.2 hs3

/-- **The x86-64 compiler theorem at every admissible entry state, closed**:
`x64_scc_correctE` with its `hgen` discharged (`hgen_ofPlaceOK`). For a
program `[d]` that `scc` accepts (`hd`) and whose output passes the
placement check (`h`), the output is `Correct` over the target on parsed
texts at every entry state `E` that `Entry.Ok` admits. -/
theorem x64_scc_correctE_closed (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { (tablesOf pcfg (O)).Λ with imms := immsOf d } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { (tablesOf pcfg (O)).Λ with imms := immsOf d } B ((O).prog, (O).secs, (O).labelOffs) :=
  x64_scc_correctE hd h (hgen_ofPlaceOK (atTables h))

/-- **The x86-64 compiler theorem on the text, at every admissible entry
state, closed** (`Scc.Sem.X64.CorrectE`): `x64_scc_correctE_text` with its
`hgen` discharged (`hgen_ofPlaceOK`); its only premises are `Accepted0`, the
placement check and the parse check `hpa`. -/
theorem x64_scc_correctE_text_closed (hd : Scc.Lower.Accepted0 [d] = true) (h : placeOK pcfg (O) = true)
    {text : String} (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { (tablesOf pcfg (O)).Λ with imms := immsOf d } B ⟨text, sizes, labelOffs⟩ :=
  x64_scc_correctE_text hd h hpa (hgen_ofPlaceOK (atTables h))

/-- **The x86-64 compiler theorem at any layout, closed**: for a program
`[d]` that `scc` accepts (`hd`) and whose output passes the placement check
at a layout `Λ` (`h`; `Λ` read off an executable, say, in place of the
static link), the output is `Correct` over the kernel-model target
`target (kernel 1) E` on parsed triples at every entry state `E` that
`Entry.Ok` admits, at `Λ` with no static label and the lowering's
immediates. The placement check reads neither field (`placeOKAt_static`); a
program in the fragment (`Accepted0`) allocates no static label, and `imms`
is the proof's table of constants folded into instructions, not an input of
the loader nor of anything `Correct` fixes outside the witness. -/
theorem x64_scc_correctE_closedAt (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := immsOf d } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { Λ with static := fun _ => none, imms := immsOf d } B ((O).prog, (O).secs, (O).labelOffs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (O) = true :=
    (Scc.Cert.PlaceOK.X64.placeOKAt_static pcfg Λ (O) (fun _ => none) Λ.imms).trans h
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK h
    x64_lower_correctE hd hlow h' (fun _ => rfl) hE (hgen_ofPlaceOK h' E hE)

/-- **The x86-64 compiler theorem on the text, at any layout, closed**
(`Scc.Sem.X64.CorrectE`): for a program `[d]` that `scc` accepts (`hd`),
whose output passes the placement check at a layout `Λ` (`h`) and whose
assembler text `⟨text, sizes, labelOffs⟩` the loader parses to it (`hpa`,
the certificate's compiled `#guard`, the trust boundary), the text is
`Correct` over the kernel-model target `target (kernel 1) E` at every
admissible entry state `E`, at `Λ` with no static label and the lowering's
immediates. The placement check reads neither field (`placeOKAt_static`); a
program in the fragment (`Accepted0`) allocates no static label, and `imms`
is the proof's table of constants folded into instructions, not an input of
the loader nor of anything `Correct` fixes outside the witness.

If the program exits, it exits as the source does; the theorem does not
promise that it exits. `Correct` is a safety and refinement statement:
every finite observable trace of the target, including one that ends in
exit, is a trace of the source; a target that diverges or blocks before
exiting satisfies it. -/
theorem x64_scc_correctE_text_closedAt (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := immsOf d } B ⟨text, sizes, labelOffs⟩ :=
  fun E hE =>
    let ⟨h1, h2⟩ := Scc.Cert.Link.X64.parsed_of_parsesTo hpa
    Scc.Sem.X64.correct_of_parsed _ E h1 h2 (x64_scc_correctE_closedAt Λ hd h E hE)

end Correct

end Spike.Lib.LowerX64
