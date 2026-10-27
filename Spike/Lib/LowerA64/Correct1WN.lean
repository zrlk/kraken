/-
**The AArch64 compiler theorem for a main-only call-free `Accepted1`
program, along the frame `WordsNone ∧ rtF`**: `Spike/Lib/LowerA64/Correct1.lean`
with `Spike.Lib.DmemPriv.WordsNone` (no word of the heap or the static image
loads from private memory) in the frame of every segment of the start, the
switch, `scc_rt_main` and the user `main`. The closed theorem's statement is
`a64_scc_correctE_closedAt1`'s; `WordsNone` is internal.

- `entry_atE_wn`: the loaded thread at `_start`'s node under the frame
  (`wordsNone_stackMem`);
- `a64_lower_correctE1_wn`: `a64_lower_correctE1` through
  `a64_start_segW1_wn`, `hgen` at `SwUWF`/`StartAllUWF` (`Fw := WordsNone`);
- `hgen1WN_ofPlaceOK`: that `hgen` from the placement check
  (`startAllUWF_gen`);
- `a64_scc_correctE_closedAt1_wn`: `a64_scc_correctE_closedAt1`'s statement.
-/
import Spike.Lib.LowerA64.Correct1
import Spike.Lib.LowerA64.StartSeg1WN
import Spike.Lib.A64DmemPrivPlace

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64Consumer (CFacts SFacts Lbl Lsize msOf IOf TPar TParE)
open Spike.Lib.A64.Rt (RuntimeLayout SwUWF StartAllUWF bareMC rtF entryR)
open Spike.Lib.A64.Flow.Ret0 (StackM limA)
open Spike.Lib.A64.PhRec (μ K)
open Spike.Lib.LowerNode (immsOf)
open Spike.Lib.A64.PhRec (GOf m0Of rtFree_ofPlaceOK hGh_ofPlaceOK hGf_ofPlaceOK hGt_ofPlaceOK hG1_ofPlaceOK
  hG0_ofPlaceOK hGn_ofPlaceOK hroomM_ofPlaceOK hroomU_ofPlaceOK hownT_ofPlaceOK hownL_ofPlaceOK hownF_ofPlaceOK
  hownN_ofPlaceOK)
open Scc.Sem Scc.Sem.A64 Scc.Cert.Link Spike.Lib.Consumer1

/-- **The loaded thread at `_start`'s node under `WordsNone ∧ rtF`**
(`entry_atE`): the entry state's memory `E.stackMem` loads no heap or image
word (`wordsNone_stackMem`, the entry stack clear of the layout). -/
theorem entry_atE_wn {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {E : Entry} (hE : E.Ok (RuntimeLayout.ofPlaceOK h i).Λ)
    (hpc : (Scc.Sem.A64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceOK h i).lab "_start") :
    At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc (entryR E)
      (fun m => Spike.Lib.DmemPriv.WordsNone (RuntimeLayout.ofPlaceOK h i).Λ m.dmem ∧
        rtF (RuntimeLayout.ofPlaceOK h i) m)
      (Ret0.entryN (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64Consumer.c0)
      (Scc.Sem.A64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) Spike.Lib.A64Consumer.c0 := by
  obtain ⟨a1, a2, a3, a4, σ, hA, hF, hJ⟩ := entry_atE h i hE hpc
  exact ⟨a1, a2, a3, a4, σ, hA, ⟨Spike.Lib.A64DmemPriv.wordsNone_stackMem (wf_link_of_placeOKAt i h) hE.1, hF⟩, hJ⟩

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

/-- The frame before the switch: `WordsNone` and the runtime's words. -/
local notation "FWN" h:max => fun m : MachineData => Spike.Lib.DmemPriv.WordsNone (Ly h).Λ m.dmem ∧ rtF (Ly h) m

/-- The loaded thread. -/
local notation "S0" h => Scc.Sem.A64.threadAt Scc.Sem.Entry.linux (Ly h).Λ.code.lo (O).prog
  (Scc.Sem.loadSyms (Ly h).Λ (O).secs.rodata)

/-- **`a64_lower_correctE1` along the frame `WordsNone ∧ rtF`**: the same
statement, the start segment `a64_start_segW1_wn` (`WordsNone` in every
segment's frame, before and after the switch) in place of `a64_start_segW1`,
`hgen` at `SwUWF`/`StartAllUWF` with `Fw := WordsNone`, the loaded thread's
node at the stronger frame by `entry_atE_wn`. -/
theorem a64_lower_correctE1_wn (hd : Scc.Lower.Accepted1 [d] = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg [d] = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (Ly h).Λ)
    -- Runtime: `startAllUWF_gen`'s conclusion
    (hgen : ∀ cx : FnCtx, cx.frame ≤ 4095 →
      SwUWF (WS h (Ly h).Λ.static) (K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))) [d] (Ly h).Λ.static (Ly h).exe
        (Ly h).endPc (entryR E) (fun m => (FWN h) m ∧ StackM (Spike.Lib.A64.Rt.rS0 (Ly h)) m)
        (Spike.Lib.DmemPriv.WordsNone (Ly h).Λ)
        (MS h (G0 h) (Ly h).Λ.static (fun _ => 0)) (Spike.Lib.A64.Rt.rS0 (Ly h))
        (Ret0.pinA (Ly h).lab + 0#64 + 8#64) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame)
        (UPost [d] (Ly h).Λ.static Spike.Lib.A64Consumer.c0) →
      StartAllUWF (WS h (Ly h).Λ.static) (K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))) [d] (Ly h).Λ.static
        (Ly h).exe (Ly h).endPc (entryR E) (FWN h) (Spike.Lib.DmemPriv.WordsNone (Ly h).Λ)
        (MS h (G0 h) (Ly h).Λ.static (fun _ => 0))
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
  have hseg := a64_start_segW1_wn h (Scc.Lower.imms1Of [d]) hd htl hf h1 h16 hpro hr hcode hbl
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
    (wideIn_of_placeOKAt h) ⟨rfl, rfl, hP _ _ (entry_atE_wn h _ hE (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E))⟩
    hload (.none (Spike.Lib.srcP1_hooks arch))
    (Spike.Lib.srcP1_init arch) hN (Spike.Lib.A64Consumer.safe_of_accepted1main hd arch _) hT
    (Spike.Lib.A64.PhRec.htk0_of_pc h _ (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E))
    (Spike.Lib.A64.PhRec.hown0_of_pcE h _ hE.1 (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E))
    (Spike.Lib.A64Consumer.writeNoProm_of_tail (tailNoFul_ovf hI (abortIn_of_placeOKAt h)
      (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h _) (hrel_ofPlaceOK h _) (htk_ofPlaceOK h _) hWr))
    (fun _ => trivial) (wf_link_of_placeOKAt (i := Scc.Lower.imms1Of [d]) h)
    (Spike.Lib.A64.PhRec.G0_ofPlaceOKE h _ hE.1)
    (Spike.Lib.A64.PhRec.hGpl_ofPlaceOK h _) hA
    (fun h => h)

/-- **`hgen1_ofPlaceOK` at the frame `WordsNone ∧ rtF`** (`startAllUWF_gen`,
the frame giving the runtime's words unloaded by its second conjunct): the
`hgen` of `a64_lower_correctE1_wn`. -/
theorem hgen1WN_ofPlaceOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    ∀ E : Entry, E.Ok (Ly h).Λ → ∀ cx : FnCtx, cx.frame ≤ 4095 →
      SwUWF (WS h (Ly h).Λ.static) (K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))) [d] (Ly h).Λ.static (Ly h).exe
        (Ly h).endPc (entryR E) (fun m => (FWN h) m ∧ StackM (Spike.Lib.A64.Rt.rS0 (Ly h)) m)
        (Spike.Lib.DmemPriv.WordsNone (Ly h).Λ)
        (MS h (G0 h) (Ly h).Λ.static (fun _ => 0)) (Spike.Lib.A64.Rt.rS0 (Ly h))
        (Ret0.pinA (Ly h).lab + 0#64 + 8#64) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame)
        (UPost [d] (Ly h).Λ.static Spike.Lib.A64Consumer.c0) →
      StartAllUWF (WS h (Ly h).Λ.static) (K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))) [d] (Ly h).Λ.static
        (Ly h).exe (Ly h).endPc (entryR E) (FWN h) (Spike.Lib.DmemPriv.WordsNone (Ly h).Λ)
        (MS h (G0 h) (Ly h).Λ.static (fun _ => 0))
        (Spike.Lib.A64.Rt.rS0 (Ly h)) 0#64 0#64 Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC
        (cx.frame + 48) (Int64.ofInt cx.frame) (UPost [d] (Ly h).Λ.static Spike.Lib.A64Consumer.c0) :=
  fun E hE _ _ hs3 => Spike.Lib.A64.Rt.startAllUWF_gen h (Scc.Lower.imms1Of [d])
    (rtPh_of_placeOKAt h) Ret0.Inst.cfacts_c0
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) (fun _ hm => hm.2) rfl (rS0_eq_lab _) (Spike.Lib.A64.Rt.rS0_sub _)
    (stackM_rS0 _ hE).1 (stackM_rS0 _ hE).2.1 (stackM_rS0 _ hE).2.2 hs3

/-- **The AArch64 compiler theorem for a main-only call-free `Accepted1`
program at any layout, closed, along the frame `WordsNone ∧ rtF`**:
`a64_scc_correctE_closedAt1`'s statement, word for word
(`Spike/Test/A64Correct1WN.lean` checks the two types equal); `WordsNone`
appears only inside the proof, in every segment's frame
(`a64_lower_correctE1_wn`, `hgen1WN_ofPlaceOK`). -/
theorem a64_scc_correctE_closedAt1_wn (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B ((O).prog, (O).secs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (O) = true :=
    (Scc.Cert.PlaceOK.A64.placeOKAt_static pcfg Λ (O) (fun _ => none) Λ.imms).trans h
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK h
    a64_lower_correctE1_wn hd hlow h' (fun _ => rfl) hE (hgen1WN_ofPlaceOK h' E hE)

end Correct

end Spike.Lib.LowerA64
