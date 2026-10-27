/-
**The x86-64 compiler theorem for a main-only call-free `Accepted1`
program**: the twin of `Spike/Lib/LowerX64/Correct.lean` for `[d]` with
`Accepted1 [d]` (`main` only: checked `+`, saturating `-`, `if` on `Int`
atoms, no call), at the immediates `imms1Of [d]`; the twin of
`Spike/Lib/LowerA64/Correct1.lean`.

The composition is `Correct.lean`'s with the user `main`'s pieces replaced:
`mainPh1_ofPlaceOK` (`Spike/Lib/LowerX64/MainCode1.lean`: the function's
blocks placed, `blocksOk`, with their runs' phase facts, `blocksPh`),
`entryCode1`/`blocksCode1` with `lower1_shape` and `zip_callMaps`
(`Spike/Lib/LowerX64/Blocks1.lean`: the blocks' code at `Cd1`),
`x64_start_segW1` (`Spike/Lib/LowerX64/StartSeg1.lean`),
`tail_bare_of_accepted1main`, `safe_of_accepted1main`, and `hgen1_ofPlaceOK`
(`startAllUW_gen` at `imms1Of [d]`).

- `x64_lower_correctE1`: at an admissible entry state, with `hgen`.
- `hgen1_ofPlaceOK`: its `hgen` from the placement check.
- `x64_scc_correctE_closedAt1`, `x64_scc_correctE_text_closedAt1`: at any
  layout passing `placeOKAt`, closed; the latter on the text.
- `x64_scc_correctE_text_closedAt_of1`: `Correct.lean`'s `Accepted0`
  theorem (`x64_scc_correctE_text_closedAt`'s statement, with the frame
  bound `hfr`) as a corollary: `Accepted0 → Accepted1`
  (`accepted1_of_accepted0`), and `imms1Of [d]`'s entries are `immsOf d`'s
  (`imms1Of_sub_immsOf`), along which `CorrectE` is monotone
  (`x64_correctE_imms_mono'`).

Where x86-64 differs from AArch64: the theorems take the frame bound
`hfr : MainFrame1Ok cfg d = true` (x86-64 only). A12's `fnOk1` checks a
stack-checked function's frame only against `2^31`; the stack-check
segment needs `main`'s frame within 4096 bytes, which `MainFrame1Ok`
decides on the program (on AArch64, A12's checks give `≤ 4095`). On a
certificate it is closed by `decide`.
-/
import Spike.Lib.LowerX64.Correct
import Spike.Lib.LowerX64.StartSeg1
import Spike.Lib.LowerX64.TailBare1
import Spike.Lib.LowerX64.MainCode1
import Spike.Lib.X64Accepted1Safe
import Spike.Lib.ImmsMonoX64
import Spike.Lib.LowerEnvImmAgree

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.LowerNode (immsOf)
open Spike.Lib.X64Consumer (CFacts SFacts Lbl Lsize blkPh msOf IOf TPar TParE)
open Spike.Lib.X64.Rt (RuntimeLayout SwUW StartAllUW bareMC rtF entryR)
open Spike.Lib.X64.Flow.Ret0 (StackM limA tpOf startN0)
open Spike.Lib.X64.PhRec (μ K)
open Scc.Sem Scc.Sem.X64 Scc.Cert.Link Spike.Lib.Consumer1
open Spike.Lib.X64.PhRec (rtFree_ofPlaceOK G0_ofPlaceOK hGh_ofPlaceOK hGf_ofPlaceOK hGt_ofPlaceOK hG1_ofPlaceOK
  hG0_ofPlaceOK hGn_ofPlaceOK hroomM_ofPlaceOK hroomU_ofPlaceOK hGpl_ofPlaceOK htk0_ofPlaceOK hown0_ofPlaceOK
  hownT_of_ph hownL_of_ph hownF_ofPlaceOK hownN_of_ph hph0_of
  hph0_ofPlaceOK hphT_ofPlaceOK hphL_ofPlaceOK hphN_ofPlaceOK G0_ofPlaceOKE hown0_ofPlaceOKE)

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {d : Decl} {sizes : List Nat}
  {labelOffs : List (String × Nat)}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of [d])

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

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.X64.Rt.rS0 (Ly h))

/-- **The x86-64 compiler theorem for a main-only call-free `Accepted1`
program at an admissible entry state `E`** (`hE`), `main`'s frame within
4096 bytes (`hfr`), with the runtime's start as a hypothesis (`hgen`) and
no static label (`hs`): `Correct` over the target on parsed texts at `E`. -/
theorem x64_lower_correctE1 (hd : Scc.Lower.Accepted1 [d] = true) (hfr : MainFrame1Ok cfg d = true)
    {em : Scc.Lower.X64.Emitted}
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
    ⟨_, Scc.Cert.Link.X64.loadParsed_of_loadOk (loadOk_link_of_placeOKAt (i := Scc.Lower.imms1Of [d]) h) hE.1⟩
  have hss0 : imageOk (Ly h).Λ (O).secs (Scc.Sem.X64.codeLabel (Ly h).Λ.code.lo (O).prog) = true :=
    imageIn_link_of_placeOKAt (i := Scc.Lower.imms1Of [d]) h
  have hss : Scc.Sem.StaticSyms (Ly h).Λ (O).secs (Scc.Sem.X64.codeLabel (Ly h).Λ.code.lo (O).prog)
      (fun _ => 0) (fun _ => "") :=
    Scc.Sem.StaticSyms.of_none hs
  have hs' : (Ly h).Λ.static = fun _ => none := funext hs
  obtain ⟨fr, r, n, zl, zf, z1, z2, zs, hr, -, hfrq, hf, h4, h16, hpro, hbo, hbp, hlab, hphP, hab⟩ :=
    mainPh1_ofPlaceOK hd hfr hlow h (Scc.Lower.imms1Of [d])
  -- the blocks' code at `Cd1`
  have hsh := lower1_shape d.body [] _ 0 r (Scc.Lower.Inv.accepted1_main hd).2.2.2.2.2.2
    (Scc.Lower.Inv.envScalar_nil _) hr
  obtain ⟨G, hzip, hG⟩ := zip_callMaps (Scc.Lower.Inv.func1 (Scc.Lower.Names.user "main") [] r)
  rw [hzip] at hbo hbp
  have hcode := entryCode1 (b := ⟨"entry", r.insts, r.term⟩) (bs := r.blocks) hf (by omega) hlab hG hbo hbp hsh.1
  have hbl := blocksCode1 (pre := [⟨"entry", r.insts, r.term⟩]) (bs := r.blocks) hf (by omega) hlab hG hbo hbp
    hsh.2
  have hfn : fr.fn = Scc.Lower.Names.user "main" := by rw [hfrq]; rfl
  have hra : (Ly h).lab raL = Int64.ofBitVec ((Ly h).lab bareMC.sp0).toBitVec := by
    rw [bareMC_sp0, Int64.ofBitVec_toBitVec]
  rw [hra] at hcode hbl
  simp only at hcode
  rw [hfn] at hcode
  have hpc := Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h (Scc.Lower.imms1Of [d]) E
  have htl := tail_bare_of_accepted1main hd hlow sizes labelOffs
  have hS := x64_start_segW1 h (Scc.Lower.imms1Of [d]) hd htl hf h4 h16 hpro hr hcode hbl
    (Dt := OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab) (rd := fun _ => True) (G := G0 h)
    (hs' ▸ rtFree_ofPlaceOK h _) hE hphP Ret0.Inst.cfacts_c0 (fun ha => hab ha) rfl
    (fun _ _ hlo hhi _ _ _ hA => ovfDt_of_at hlo hhi hA)
    (hGh_ofPlaceOK h _) (hGf_ofPlaceOK h _) (hGt_ofPlaceOK h _)
    (hownT_of_ph h _ (by rw [hphT_ofPlaceOK h _])) (hG1_ofPlaceOK h _) (hG0_ofPlaceOK h _)
    (hGn_ofPlaceOK h _) (hownL_of_ph h _ (by rw [hphL_ofPlaceOK h _])) (hownF_ofPlaceOK h _)
    (hownN_of_ph h _ (by rw [hphN_ofPlaceOK h _]))
    (hroomM_ofPlaceOK h _)
    (hroomU_ofPlaceOK h _ (Int.natCast_nonneg _) (by omega))
    (Spike.Lib.X64.Rt.PhRecOf.mainPh_bare_ofPlaceOK h _ htl) (Spike.Lib.X64.Rt.PhRecOf.swPh_ofPlaceOK h _)
    (hgen fr h4)
  obtain ⟨inv, hP, hN, hT, hA, hWr⟩ :=
    Spike.Lib.X64Consumer.inst_of_segW
      (Spike.Lib.X64.Rt.entry_segW_take (Ly h) hE
        (Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h htl)).start0
        (Spike.Lib.X64.Rt.rS0_sub (Ly h)) _
        (Spike.Lib.X64.Rt.entryW_ofPlaceOK h _ (Spike.Lib.X64.Rt.entryR_ok hE)
          (by show (-65536 : Int) ≤ -8; decide) (by show (0 : Int) ≤ 0; decide)
          Ret0.Inst.cfacts_c0) hS)
      (Spike.Lib.X64.PhRec.site_ofPlaceOK h _) (fun _ _ h => h)
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of [d]) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
  exact Spike.Lib.X64Consumer.correctX64PE' (lsize := fun _ => 0) (name := fun _ => "") hss0 hss
    (wideIn_of_placeOKAt h) ⟨rfl, rfl, hP _ _ (entry_atXE h _ hE hpc)⟩ hload (.none (Spike.Lib.srcP1_hooks arch))
    (Spike.Lib.srcP1_init arch) hN (Spike.Lib.X64Consumer.safe_of_accepted1main hd arch _) hT
    (htk0_ofPlaceOK h _ (hph0_of h _ hpc (hph0_ofPlaceOK h _)))
    (hown0_ofPlaceOKE h _ hE.1 (hph0_of h _ hpc (hph0_ofPlaceOK h _)))
    (Spike.Lib.X64Consumer.writeNoProm_of_tail (tailNoFul_ovf hI (hprog_ofPlaceOK h (Scc.Lower.imms1Of [d]))
      (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h _) (hrel_ofPlaceOK h _) (htk_ofPlaceOK h _) hWr)) (fun _ => trivial)
    (wf_link_of_placeOKAt (i := Scc.Lower.imms1Of [d]) h) (G0_ofPlaceOKE h _ hE.1)
    (hGpl_ofPlaceOK h _ (Spike.Lib.X64.PhRec.hclr_ofPlaceOK h _)) hA (fun h => h)

/-- **`hgen` from `placeOKAt`** (`hgen_ofPlaceOK` at the immediates
`imms1Of [d]`; `startAllUW_gen`): at every admissible entry state `E`,
`scc_rt_start`'s blocks after `_start` are inside the run's facts given the
switch's and `scc_rt_main`'s obligations, in `_start`'s callee region
`EC E` (`ec_facts`), at the first stack `rS0` and `c0`'s facts, on a bare
tail (`hs`, `tail_bare_of_accepted1main`). This is the compiler theorem's
`hgen`. -/
theorem hgen1_ofPlaceOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) (hs : (O).place.tail = .bare) :
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
  fun _E hE _ _ _ _ _ hFF hs3 =>
    have hEC := ec_facts _ hE (Spike.Lib.X64.Rt.rS0_sub _)
    Spike.Lib.X64.Rt.startAllUW_gen h (Scc.Lower.imms1Of [d]) hs Ret0.Inst.cfacts_c0 hEC.1 hEC.2.1 hEC.2.2.1 hFF
      rfl (rS0_eq_lab _) (Spike.Lib.X64.Rt.rS0_sub _) hEC.2.2.2.2 hs3

/-- **The x86-64 compiler theorem for a main-only call-free `Accepted1`
program at any layout, closed**: for a program `[d]` that `scc` accepts
(`hd`), whose output passes the placement check at a layout `Λ` (`h`; `Λ`
read off an executable, say, in place of the static link) and whose `main`'s
frame is within 4096 bytes (`hfr`, decided on the program), the output is
`Correct` over the kernel-model target `target (kernel 1) E` on parsed
triples at every entry state `E` that `Entry.Ok` admits, at `Λ` with no
static label and the lowering's immediates. The placement check reads
neither field (`placeOKAt_static`); a program in the fragment (`Accepted1`)
allocates no static label, and `imms` is the proof's table of constants
folded into instructions, not an input of the loader nor of anything
`Correct` fixes outside the witness. -/
theorem x64_scc_correctE_closedAt1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) (hfr : MainFrame1Ok cfg d = true) {B : Scc.Sem.Budget}
    {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B
        ((O).prog, (O).secs, (O).labelOffs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (O) = true :=
    (Scc.Cert.PlaceOK.X64.placeOKAt_static pcfg Λ (O) (fun _ => none) Λ.imms).trans h
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK h
    x64_lower_correctE1 hd hfr hlow h' (fun _ => rfl) hE
      (hgen1_ofPlaceOK h' (tail_bare_of_accepted1main hd hlow sizes labelOffs) E hE)

/-- **The x86-64 compiler theorem on the text for a main-only call-free
`Accepted1` program, at any layout, closed** (`Scc.Sem.X64.CorrectE`): for
a program `[d]` that `scc` accepts (`hd`), whose output passes the
placement check at a layout `Λ` (`h`), whose `main`'s frame is within 4096
bytes (`hfr`, decided on the program: A12 bounds it only by `2^31` on
x86-64) and whose assembler text `⟨text, sizes, labelOffs⟩` the loader
parses to it (`hpa`, the certificate's compiled `#guard`, the trust
boundary), the text is `Correct` over the kernel-model target
`target (kernel 1) E` at every admissible entry state `E`, at `Λ` with no
static label and the lowering's immediates. The placement check reads
neither field (`placeOKAt_static`); a program in the fragment (`Accepted1`)
allocates no static label, and `imms` is the proof's table of constants
folded into instructions, not an input of the loader nor of anything
`Correct` fixes outside the witness.

If the program exits, it exits as the source does; the theorem does not
promise that it exits. `Correct` is a safety and refinement statement:
every finite observable trace of the target, including one that ends in
exit, is a trace of the source; a target that diverges or blocks before
exiting satisfies it. -/
theorem x64_scc_correctE_text_closedAt1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) (hfr : MainFrame1Ok cfg d = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B ⟨text, sizes, labelOffs⟩ :=
  fun E hE =>
    let ⟨h1, h2⟩ := Scc.Cert.Link.X64.parsed_of_parsesTo hpa
    Scc.Sem.X64.correct_of_parsed _ E h1 h2 (x64_scc_correctE_closedAt1 Λ hd h hfr E hE)

/-- **The `Accepted0` compiler theorem on the text as a corollary of the
`Accepted1` one**: `x64_scc_correctE_text_closedAt`'s statement with the
frame bound `hfr`, from `x64_scc_correctE_text_closedAt1` at
`accepted1_of_accepted0 hd`, moved from `imms1Of [d]` to `immsOf d` by
`x64_correctE_imms_mono'` (on an `Accepted0` program every entry of the
former is the latter's: `imms1Of_sub_immsOf`). -/
theorem x64_scc_correctE_text_closedAt_of1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) (hfr : MainFrame1Ok cfg d = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := immsOf d } B ⟨text, sizes, labelOffs⟩ :=
  Spike.Lib.ImmsMono.x64_correctE_imms_mono'
    (Λ := { Λ with static := fun _ => none })
    (x64_scc_correctE_text_closedAt1 Λ (Scc.Lower.accepted1_of_accepted0 hd) h hfr hpa)
    fun _ _ _ _ => Spike.Lib.LowerNode.imms1Of_sub_immsOf hd

end Correct

end Spike.Lib.LowerX64
