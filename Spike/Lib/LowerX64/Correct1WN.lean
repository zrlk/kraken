/-
**The x86-64 compiler theorem for a main-only call-free `Accepted1`
program, along the frame `WordsNone ∧ rtF`**: `Spike/Lib/LowerX64/Correct1.lean`
with `Spike.Lib.DmemPriv.WordsNone` (no word of the heap or the static image
loads from private memory) in the frame of every segment of `_start`, the
start, the switch, `scc_rt_main` and the user `main`; the twin of
`Spike/Lib/LowerA64/Correct1WN.lean`. The closed theorem's statement is
`x64_scc_correctE_closedAt1`'s; `WordsNone` is internal.

- `entry_atXE_wn`: the loaded thread at `_start`'s node under the frame
  (`wordsNone_stackMem`);
- `entry_segW_take_wn`: `entry_segW_take` at the frame `WordsNone ∧ rtF`
  (`Alloc.wordsNone_and_fstable`, `cellsR_entry`, `Rt.wordsNone_takeMem`);
- `x64_lower_correctE1_wn`: `x64_lower_correctE1` through
  `x64_start_segW1_wn`, `hgen` at `SwUWF`/`StartAllUWF` (`Fw := WordsNone`);
- `hgen1WN_ofPlaceOK`: that `hgen` from the placement check
  (`startAllUWF_gen`, at a bare tail `hs`);
- `x64_scc_correctE_closedAt1_wn`: `x64_scc_correctE_closedAt1`'s statement.
-/
import Spike.Lib.LowerX64.Correct1
import Spike.Lib.LowerX64.StartSeg1WN
import Spike.Lib.Rt.X64RtStartUF
import Spike.Lib.X64DmemPrivPlace
import Spike.Lib.X64WordsNone
import Spike.Lib.RegionCells

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.LowerNode (immsOf)
open Spike.Lib.X64Consumer (CFacts SFacts Lbl Lsize blkPh msOf IOf TPar TParE)
open Spike.Lib.X64.Rt (RuntimeLayout SwUWF StartAllUWF bareMC rtF entryR)
open Spike.Lib.X64.Flow.Ret0 (StackM limA tpOf startN0)
open Spike.Lib.X64.PhRec (μ K)
open Scc.Sem Scc.Sem.X64 Scc.Cert.Link Spike.Lib.Consumer1
open Spike.Lib.X64.PhRec (rtFree_ofPlaceOK G0_ofPlaceOK hGh_ofPlaceOK hGf_ofPlaceOK hGt_ofPlaceOK hG1_ofPlaceOK
  hG0_ofPlaceOK hGn_ofPlaceOK hroomM_ofPlaceOK hroomU_ofPlaceOK hGpl_ofPlaceOK htk0_ofPlaceOK hown0_ofPlaceOK
  hownT_of_ph hownL_of_ph hownF_ofPlaceOK hownN_of_ph hph0_of
  hph0_ofPlaceOK hphT_ofPlaceOK hphL_ofPlaceOK hphN_ofPlaceOK G0_ofPlaceOKE hown0_ofPlaceOKE)

/-- **The loaded thread at `_start`'s node under `WordsNone ∧ rtF`**
(`entry_atXE`): the entry state's memory `E.stackMem` loads no heap or image
word (`wordsNone_stackMem`, the entry stack clear of the layout). -/
theorem entry_atXE_wn {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {E : Entry} (hE : E.Ok (RuntimeLayout.ofPlaceOK h i).Λ)
    (hpc : (Scc.Sem.X64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceOK h i).lab "_start") :
    At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc (entryR E)
      (fun m => Spike.Lib.DmemPriv.WordsNone (RuntimeLayout.ofPlaceOK h i).Λ m.dmem ∧
        rtF (RuntimeLayout.ofPlaceOK h i) m)
      (Spike.Lib.X64.Rt.entryN0 (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.X64Consumer.c0)
      (Scc.Sem.X64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) Spike.Lib.X64Consumer.c0 := by
  obtain ⟨a1, a2, a3, a4, σ, hA, hF, hJ⟩ := entry_atXE h i hE hpc
  exact ⟨a1, a2, a3, a4, σ, hA, ⟨Spike.Lib.X64DmemPriv.wordsNone_stackMem (wf_link_of_placeOKAt i h) hE.1, hF⟩, hJ⟩

/-- **`_start` at the runtime's layout `L` under `WordsNone ∧ rtF`**
(`entry_segW_take` at the stronger frame): the frame `FStable` in the entry
stack (`Alloc.wordsNone_and_fstable`, `cellsR_entry`) and kept by the take
(`Rt.wordsNone_takeMem`, `rtF_takeMem`). -/
theorem entry_segW_take_wn (L : RuntimeLayout) {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) (hwf : L.Λ.WF)
    {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {W : Frag isa} {a : Int64}
    {rS : Scc.Sem.Range} (hin : Spike.Lib.X64.Rt.Code.Start.entryIn L.prog = true) (hsub : rS.Sub L.pool) (c0 : Ctl)
    (hW : Spike.Lib.X64.Rt.EntryW W (Ret0.TakeK a rS) L.exe L.endPc (entryR E)
      (fun m => Spike.Lib.DmemPriv.WordsNone L.Λ m.dmem ∧ rtF L m) L.lab c0) {Q : Frag isa}
    (hS : ∀ F' : MachineData → Prop, FStable ((entryR E).callee (-8) (-296) 8) F' → KStable (Ret0.TakeK a rS) F' →
      (∀ m, F' m → Spike.Lib.DmemPriv.WordsNone L.Λ m.dmem ∧ rtF L m) → ∀ Q' : Frag isa,
      SegW W (Ret0.TakeK a rS) p lbl ms (At L.exe L.endPc ((entryR E).callee (-8) (-296) 8) F' (startN0 L.lab c0)) Q') :
    SegW W (Ret0.TakeK a rS) p lbl ms (At L.exe L.endPc (entryR E)
      (fun m => Spike.Lib.DmemPriv.WordsNone L.Λ m.dmem ∧ rtF L m) (Spike.Lib.X64.Rt.entryN0 L.lab c0)) Q :=
  Spike.Lib.X64.Rt.entry_segW' L.lays rfl hin
    (Spike.Lib.X64.Alloc.wordsNone_and_fstable hwf hE.1 (Spike.Lib.X64.Rt.entryR_ok hE)
      (.inl (cellsR_entry hE)) (Spike.Lib.X64.Rt.rtF_stable L hE)).1
    (Spike.Lib.X64.Rt.entryR_ok hE) (Spike.Lib.X64.Rt.entryR_al hE)
    (by show (-65536 : Int) ≤ -8 + -296; decide) (by show (0 : Int) ≤ 0; decide)
    (Ret0.TakeK.kstable fun _ _ hm =>
      ⟨Spike.Lib.X64.Rt.wordsNone_takeMem hwf hsub hm.1, Spike.Lib.X64.Rt.rtF_takeMem L hsub hm.2⟩)
    (fun _ _ hk _ k hk' => by
      obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact Ret0.loadInt_takeMem (Spike.Lib.X64.Rt.rS_of_sub L hE hsub k hk'))
    c0 hW hS

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

/-- The frame before the switch: `WordsNone` and the runtime's words. -/
local notation "FWN" h:max => fun m : MachineData => Spike.Lib.DmemPriv.WordsNone (Ly h).Λ m.dmem ∧ rtF (Ly h) m

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.X64.Rt.rS0 (Ly h))

/-- **The x86-64 compiler theorem for a main-only call-free `Accepted1`
program at an admissible entry state, along the frame `WordsNone ∧ rtF`**:
`x64_lower_correctE1`'s statement, `_start`'s segment at the stronger frame
(`entry_segW_take_wn`), the start segment `x64_start_segW1_wn` in place of
`x64_start_segW1`, `hgen` at `SwUWF`/`StartAllUWF` with
`Fw := WordsNone`, the loaded thread's node at the stronger frame by
`entry_atXE_wn`. -/
theorem x64_lower_correctE1_wn (hd : Scc.Lower.Accepted1 [d] = true) (hfr : MainFrame1Ok cfg d = true)
    {em : Scc.Lower.X64.Emitted}
    (hlow : Scc.Lower.X64.lowerAll? cfg [d] = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (Ly h).Λ)
    -- Runtime: `startAllUWF_gen`'s conclusion
    (hgen : ∀ fr : Scc.Emit.X64.Frame, fr.size ≤ 4096 →
      ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (KS h) F' → (∀ m, F' m → (FWN h) m) →
      SwUWF (WS h (Ly h).Λ.static) (KS h) [d] (Ly h).Λ.static (Ly h).exe (Ly h).endPc (EC E)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Ly h)) m) (Spike.Lib.DmemPriv.WordsNone (Ly h).Λ)
          (MS h (G0 h)) (Spike.Lib.X64.Rt.rS0 (Ly h))
          (Ret0.pinA (Ly h).lab + 0#64 + 8#64) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size)
          (UPost [d] (Ly h).Λ.static Spike.Lib.X64Consumer.c0) →
        StartAllUWF (WS h (Ly h).Λ.static) (KS h) [d] (Ly h).Λ.static (Ly h).exe (Ly h).endPc (EC E) F'
          (Spike.Lib.DmemPriv.WordsNone (Ly h).Λ) (MS h (G0 h)) (Spike.Lib.X64.Rt.rS0 (Ly h)) 0#64 0#64
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
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
  have hS := x64_start_segW1_wn h (Scc.Lower.imms1Of [d]) hd htl hf h4 h16 hpro hr hcode hbl
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
      (entry_segW_take_wn (Ly h) hE (wf_link_of_placeOKAt (i := Scc.Lower.imms1Of [d]) h)
        (Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h htl)).start0
        (Spike.Lib.X64.Rt.rS0_sub (Ly h)) _
        (Spike.Lib.X64.Rt.entryW_ofPlaceOK h _ (Spike.Lib.X64.Rt.entryR_ok hE)
          (by show (-65536 : Int) ≤ -8; decide) (by show (0 : Int) ≤ 0; decide)
          Ret0.Inst.cfacts_c0) hS)
      (Spike.Lib.X64.PhRec.site_ofPlaceOK h _) (fun _ _ h => h)
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of [d]) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
  exact Spike.Lib.X64Consumer.correctX64PE' (lsize := fun _ => 0) (name := fun _ => "") hss0 hss
    (wideIn_of_placeOKAt h) ⟨rfl, rfl, hP _ _ (entry_atXE_wn h _ hE hpc)⟩ hload (.none (Spike.Lib.srcP1_hooks arch))
    (Spike.Lib.srcP1_init arch) hN (Spike.Lib.X64Consumer.safe_of_accepted1main hd arch _) hT
    (htk0_ofPlaceOK h _ (hph0_of h _ hpc (hph0_ofPlaceOK h _)))
    (hown0_ofPlaceOKE h _ hE.1 (hph0_of h _ hpc (hph0_ofPlaceOK h _)))
    (Spike.Lib.X64Consumer.writeNoProm_of_tail (tailNoFul_ovf hI (hprog_ofPlaceOK h (Scc.Lower.imms1Of [d]))
      (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h _) (hrel_ofPlaceOK h _) (htk_ofPlaceOK h _) hWr)) (fun _ => trivial)
    (wf_link_of_placeOKAt (i := Scc.Lower.imms1Of [d]) h) (G0_ofPlaceOKE h _ hE.1)
    (hGpl_ofPlaceOK h _ (Spike.Lib.X64.PhRec.hclr_ofPlaceOK h _)) hA (fun h => h)

/-- **`hgen1_ofPlaceOK` at the frames giving `WordsNone ∧ rtF`**
(`startAllUWF_gen`, the frame giving the runtime's words unloaded by its
second conjunct; at a bare tail `hs`): the `hgen` of
`x64_lower_correctE1_wn`. -/
theorem hgen1WN_ofPlaceOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) (hs : (O).place.tail = .bare) :
    ∀ E : Entry, E.Ok (Ly h).Λ → ∀ fr : Scc.Emit.X64.Frame, fr.size ≤ 4096 →
      ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (KS h) F' → (∀ m, F' m → (FWN h) m) →
      SwUWF (WS h (Ly h).Λ.static) (KS h) [d] (Ly h).Λ.static (Ly h).exe (Ly h).endPc (EC E)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Ly h)) m) (Spike.Lib.DmemPriv.WordsNone (Ly h).Λ)
          (MS h (G0 h)) (Spike.Lib.X64.Rt.rS0 (Ly h))
          (Ret0.pinA (Ly h).lab + 0#64 + 8#64) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size)
          (UPost [d] (Ly h).Λ.static Spike.Lib.X64Consumer.c0) →
        StartAllUWF (WS h (Ly h).Λ.static) (KS h) [d] (Ly h).Λ.static (Ly h).exe (Ly h).endPc (EC E) F'
          (Spike.Lib.DmemPriv.WordsNone (Ly h).Λ) (MS h (G0 h)) (Spike.Lib.X64.Rt.rS0 (Ly h)) 0#64 0#64
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UPost [d] (Ly h).Λ.static Spike.Lib.X64Consumer.c0) :=
  fun _E hE _ _ _ _ _ hFF hs3 =>
    have hEC := ec_facts _ hE (Spike.Lib.X64.Rt.rS0_sub _)
    Spike.Lib.X64.Rt.startAllUWF_gen h (Scc.Lower.imms1Of [d]) hs Ret0.Inst.cfacts_c0 hEC.1 hEC.2.1 hEC.2.2.1
      (fun m hm => (hFF m hm).2)
      rfl (rS0_eq_lab _) (Spike.Lib.X64.Rt.rS0_sub _) hEC.2.2.2.2 hs3

/-- **The x86-64 compiler theorem for a main-only call-free `Accepted1`
program at any layout, closed, along the frame `WordsNone ∧ rtF`**:
`x64_scc_correctE_closedAt1`'s statement, word for word, the frame bound
`hfr` included (`Spike/Test/X64Correct1WN.lean` checks the two types equal);
`WordsNone` appears only inside the proof, in every segment's frame
(`x64_lower_correctE1_wn`, `hgen1WN_ofPlaceOK`). -/
theorem x64_scc_correctE_closedAt1_wn (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
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
    x64_lower_correctE1_wn hd hfr hlow h' (fun _ => rfl) hE
      (hgen1WN_ofPlaceOK h' (tail_bare_of_accepted1main hd hlow sizes labelOffs) E hE)

end Correct

end Spike.Lib.LowerX64
