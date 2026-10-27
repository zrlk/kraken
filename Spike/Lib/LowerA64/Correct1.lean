/-
**The AArch64 compiler theorem for a main-only call-free `Accepted1`
program** (milestone (i) of H7a): the twin of `Spike/Lib/LowerA64/Correct.lean`
for `[d]` with `Accepted1 [d]` (`main` only: checked `+`, saturating `-`,
`if` on `Int` atoms, no call), at the immediates `imms1Of [d]`.

The composition is `Correct.lean`'s with the user `main`'s pieces replaced:
`mainPh1_ofPlaceOK` (`Spike/Lib/LowerA64/MainCode1.lean`: the function's
blocks placed, `blocksOk`, with their runs' phase facts, `blocksPh`),
`entryCode1`/`blocksCode1` with `lower1_shape` (`Spike/Lib/LowerA64/Blocks1.lean`:
the blocks' code at `Cd1`), `a64_start_segW1` (`Spike/Lib/LowerA64/StartSeg1.lean`),
`tail_bare_of_accepted1main`, `safe_of_accepted1main`, and `hgen1_ofPlaceOK`
(`startAllUW_gen` at `imms1Of [d]`).

- `a64_lower_correctE1`: at an admissible entry state, with `hgen`.
- `hgen1_ofPlaceOK`: its `hgen` from the placement check.
- `a64_scc_correctE_closedAt1`, `a64_scc_correctE_text_closedAt1`: at any
  layout passing `placeOKAt`, closed; the latter on the text.
- `a64_scc_correctE_text_closedAt_of1`: `Correct.lean`'s `Accepted0`
  theorem (`a64_scc_correctE_text_closedAt`, same statement) as a corollary:
  `Accepted0 → Accepted1` (`accepted1_of_accepted0`), and `imms1Of [d]`'s
  entries are `immsOf d`'s (`imms1Of_sub_immsOf`), along which `CorrectE`
  is monotone (`a64_correctE_imms_mono'`).
-/
import Spike.Lib.LowerA64.Correct
import Spike.Lib.LowerA64.StartSeg1
import Spike.Lib.LowerA64.TailBare1
import Spike.Lib.A64Accepted1Safe
import Spike.Lib.ImmsMonoA64
import Spike.Lib.LowerEnvImmAgree

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

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {d : Decl}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of [d])

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


/-- **The AArch64 compiler theorem for a main-only call-free `Accepted1`
program at an admissible entry state `E`**
(`hE`), with the runtime's start as a hypothesis (`hgen`) and no static
label (`hs`): `Correct` over the target on
parsed texts at `E`. -/
theorem a64_lower_correctE1 (hd : Scc.Lower.Accepted1 [d] = true) {em : Scc.Lower.A64.Emitted}
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
    ⟨_, Scc.Cert.Link.A64.loadParsed_of_loadOk (loadOk_link_of_placeOKAt (i := Scc.Lower.imms1Of [d]) h) hE.1⟩
  obtain ⟨cx, r, -, entry, hr, -, -, hf, h1, h16, hent, hpro, hbo, hbp, hlab, hphP, hab⟩ :=
    mainPh1_ofPlaceOK hd hlow h (Scc.Lower.imms1Of [d])
  have hsh := lower1_shape d.body [] _ 0 r (Scc.Lower.Inv.accepted1_main hd).2.2.2.2.2.2
    (Scc.Lower.Inv.envScalar_nil _) hr
  have hcode := entryCode1 hf h1 h16 hlab hent hbo hbp hsh.1
  have hbl := blocksCode1 (pre := [⟨"entry", r.insts, r.term⟩]) hf h1 h16 hlab hbo hbp hsh.2
  have hss0 : imageOk (Ly h).Λ (O).secs (Scc.Cert.Link.A64.codeOf (Ly h).Λ.code.lo (O).prog) = true :=
    imageIn_link_of_placeOKAt (i := Scc.Lower.imms1Of [d]) h
  have hss : Scc.Sem.StaticSyms (Ly h).Λ (O).secs (Scc.Cert.Link.A64.codeOf (Ly h).Λ.code.lo (O).prog)
      (fun _ => 0) (fun _ => "") :=
    Scc.Sem.StaticSyms.of_none hs
  have hs' : (Ly h).Λ.static = fun _ => none := funext hs
  have htl := tail_bare_of_accepted1main hd hlow
  have hseg := a64_start_segW1 h (Scc.Lower.imms1Of [d]) hd htl hf h1 h16 hpro hr hcode hbl
    (Dt := OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab) (rd := fun _ => True) (G := G0 h) (hs' ▸ rtFree_ofPlaceOK h _) hE
    hphP Ret0.Inst.cfacts_c0 hab rfl
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
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of [d]) (rS := Spike.Lib.A64.Rt.rS0 (Ly h))
  exact Spike.Lib.A64Consumer.correctA64PE' (lsize := fun _ => 0) (name := fun _ => "") hss0 hss
    (wideIn_of_placeOKAt h) ⟨rfl, rfl, hP _ _ (entry_atE h _ hE (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E))⟩
    hload (.none (Spike.Lib.srcP1_hooks arch))
    (Spike.Lib.srcP1_init arch) hN (Spike.Lib.A64Consumer.safe_of_accepted1main hd arch _) hT
    (Spike.Lib.A64.PhRec.htk0_of_pc h _ (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E))
    (Spike.Lib.A64.PhRec.hown0_of_pcE h _ hE.1 (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E))
    (Spike.Lib.A64Consumer.writeNoProm_of_tail (tailNoFul_ovf hI (abortIn_of_placeOKAt h)
      (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h _) (hrel_ofPlaceOK h _) (htk_ofPlaceOK h _) hWr))
    (fun _ => trivial) (wf_link_of_placeOKAt (i := Scc.Lower.imms1Of [d]) h) (Spike.Lib.A64.PhRec.G0_ofPlaceOKE h _ hE.1)
    (Spike.Lib.A64.PhRec.hGpl_ofPlaceOK h _) hA
    (fun h => h)

/-- **`hgen` from `placeOK`** (`hgen_ofPlaceOK` at the immediates `imms1Of [d]`) (`startAllUW_gen`): at every admissible entry
state `E`, `scc_rt_start`'s blocks after `_start` are inside the run's facts
given the switch's and `scc_rt_main`'s obligations, at the entry stack's
region `entryR E` (`entryR_ok`, `entryR_al`, its 64 KiB below the entry
stack), the first stack `rS0` (`rS0_eq_lab`, `rS0_sub`) stable in
`scc_rt_start`'s three regions (`stackM_rS0`), A6's table (`rtPh_of_placeOKAt`)
and `c0`'s facts (`cfacts_c0`). This is the compiler theorem's `hgen`. -/
theorem hgen1_ofPlaceOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
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
  fun E hE _ _ hs3 => Spike.Lib.A64.Rt.startAllUW_gen h (Scc.Lower.imms1Of [d]) (rtPh_of_placeOKAt h) Ret0.Inst.cfacts_c0
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) (fun _ hm => hm) rfl (rS0_eq_lab _) (Spike.Lib.A64.Rt.rS0_sub _)
    (stackM_rS0 _ hE).1 (stackM_rS0 _ hE).2.1 (stackM_rS0 _ hE).2.2 hs3

/-- **The AArch64 compiler theorem for a main-only call-free `Accepted1`
program at any layout, closed**: for a program
`[d]` that `scc` accepts (`hd`) and whose output passes the placement check
at a layout `Λ` (`h`; `Λ` read off an executable, say, in place of the
static link), the output is `Correct` over the kernel-model target
`target (kernel 1) E` on parsed texts at every entry state `E` that
`Entry.Ok` admits, at `Λ` with no static label and the lowering's
immediates. The placement check reads neither field (`placeOKAt_static`); a
program in the fragment (`Accepted1`) allocates no static label, and `imms`
is the proof's table of constants folded into instructions, not an input of the loader
nor of anything `Correct` fixes outside the witness. -/
theorem a64_scc_correctE_closedAt1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B ((O).prog, (O).secs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (O) = true :=
    (Scc.Cert.PlaceOK.A64.placeOKAt_static pcfg Λ (O) (fun _ => none) Λ.imms).trans h
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK h
    a64_lower_correctE1 hd hlow h' (fun _ => rfl) hE (hgen1_ofPlaceOK h' E hE)

/-- **The AArch64 compiler theorem on the text for a main-only call-free
`Accepted1` program, at any layout, closed**
(`Scc.Sem.A64.CorrectE`): for a program `[d]` that `scc` accepts (`hd`),
whose output passes the placement check at a layout `Λ` (`h`) and whose
assembler text `asm` the loader parses to it (`hpa`, the certificate's
compiled `#guard`, the trust boundary), `asm` is `Correct` over the
kernel-model target `target (kernel 1) E` at every admissible entry state
`E`, at `Λ` with no static label and the lowering's immediates. The
placement check reads neither field (`placeOKAt_static`); a program in the
fragment (`Accepted1`) allocates no static label, and `imms` is the proof's
table of constants folded into instructions, not an input of the loader
nor of anything `Correct` fixes outside the witness.

If the program exits, it exits as the source does; the theorem does not
promise that it exits. `Correct` is a safety and refinement statement:
every finite observable trace of the target, including one that ends in
exit, is a trace of the source; a target that diverges or blocks before
exiting satisfies it. -/
theorem a64_scc_correctE_text_closedAt1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B asm :=
  fun E hE =>
    let ⟨h1, h2⟩ := Scc.Cert.Link.A64.parsed_of_parsesTo hpa
    Scc.Sem.A64.correct_of_parsed _ E h1 h2 (a64_scc_correctE_closedAt1 Λ hd h E hE)

/-- **The `Accepted0` compiler theorem on the text as a corollary of the
`Accepted1` one**: `a64_scc_correctE_text_closedAt`'s statement, from
`a64_scc_correctE_text_closedAt1` at `accepted1_of_accepted0 hd`, moved from
`imms1Of [d]` to `immsOf d` by `a64_correctE_imms_mono'` (on an `Accepted0`
program every entry of the former is the latter's: `imms1Of_sub_immsOf`). -/
theorem a64_scc_correctE_text_closedAt_of1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := immsOf d } B asm :=
  Spike.Lib.ImmsMono.a64_correctE_imms_mono'
    (Λ := { Λ with static := fun _ => none })
    (a64_scc_correctE_text_closedAt1 Λ (Scc.Lower.accepted1_of_accepted0 hd) h hpa)
    fun _ _ _ _ => Spike.Lib.LowerNode.imms1Of_sub_immsOf hd

end Correct

end Spike.Lib.LowerA64
