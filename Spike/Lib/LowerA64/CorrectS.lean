/-
**The AArch64 consumer at any call depth from `_start`'s segment** for an
`Accepted1` program with calls (the twin of `Spike/Lib/LowerX64/CorrectS.lean`):
the closure half of `Spike/Lib/LowerA64/Correct1.lean` (`a64_lower_correctE1`'s
steps after the start segment) over `SegWS`, the frames twin. Given
`_start`'s segment at depth inside `SFactsS` at the overflow stub's write
tail (`hS`: from `_start`'s node at the empty frames to `False`), the
output is `Correct` over the target on parsed texts at the entry state `E`.

- `a64_lower_correctES`: at any frame `F` of the entry stack holding at the
  loaded thread's `_start` node (`hent`): `inst_of_segWS` (the fragment with
  `NodesS`, `TakePathS`, `AbortPathS`, `WrInS`), `safeS_of_accepted1`
  (`Spike/Lib/A64Accepted1SafeS.lean`), `writeNoPromS_of_wrIn` at the
  overflow stub's closed tail (`tailNoFul_ovf`'s step) and `correctKSPE`;
- `a64_lower_correctES_rtF`: at `rtF` (`entry_atE`);
- `a64_lower_correctES_wn`: at `WordsNone ∧ rtF` (`entry_atE_wn`), the
  frames twin of `Correct1WN`'s closure;
- `msOfS_nil`: the memory side at depth 0 is the placement's (`msOf`), the
  form of `a64_start_segWSG`'s `hms`.
-/
import Spike.Lib.LowerA64.Correct1WN
import Spike.Lib.A64SegInstS
import Spike.Lib.A64Accepted1SafeS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64Consumer (Lbl Lsize msOf TParE)
open Spike.Lib.A64ConsumerS (SFactsS msOfS)
open Spike.Lib.A64.Rt (RuntimeLayout rtF entryR)
open Spike.Lib.A64.PhRec (μ K)
open Scc.Sem Scc.Sem.A64 Scc.Cert.Link Spike.Lib.Consumer1

/-- **The memory side at depth 0 is the placement's**: `msOfS` at the empty
frames, owned words independent of the frames, is `msOf` (its exit
placement `[] = [] ∧ Placed` is `Placed`). -/
theorem msOfS_nil {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64Consumer.Own} {lbl : Lbl} {lsize : Lsize} :
    msOfS Λ μ rd G (fun s _ => own s) lbl lsize [] = msOf Λ μ rd G own lbl lsize := by
  simp only [msOfS, msOf, true_and]; rfl

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The facts every pair of the run carries at its frames, at the arena's
`cells` and the overflow stub's write tail. -/
local notation "WSS" h:max cells:max => fun s c fs => SFactsS (Ly h).Λ (μ (Ly h)) p
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Spike.Lib.A64.Rt.rS0 (Ly h)) (Spike.Lib.A64.PhRec.Tk (Ly h))
  (Ly h).Λ.static cells 0 s c fs (OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab)

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max G:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) G
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.A64.PhRec.GOf (Ly h) (Spike.Lib.A64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))

/-- The loaded thread at the entry state `E`. -/
local notation "T0" h:max E:max => Scc.Sem.A64.threadAt E (Ly h).Λ.code.lo (O).prog
  (Scc.Sem.loadSyms (Ly h).Λ (O).secs.rodata)

/-- **The AArch64 consumer at any call depth for an `Accepted1` program**
at an admissible entry state `E` (`hE`), no static label (`hs`): `_start`'s
segment at depth inside `SFactsS` at the budget's arena and the overflow
stub's write tail (`hS`, from `_start`'s node at the entry frame `F` and the
empty frames, never leaving), the loaded thread at that node (`hent`), gives
`Correct` over the target on parsed texts at `E`. -/
theorem a64_lower_correctES (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (Ly h).Λ) {F : MachineData → Prop}
    (hent : At (Ly h).exe (Ly h).endPc (entryR E) F (Ret0.entryN (Ly h).lab Spike.Lib.A64Consumer.c0)
      (T0 h E) Spike.Lib.A64Consumer.c0)
    (hS : SegWS (WSS h B.cells) (KS h) p (Ly h).Λ.static (MSS h (G0 h))
      ((At (Ly h).exe (Ly h).endPc (entryR E) F
        (Ret0.entryN (Ly h).lab Spike.Lib.A64Consumer.c0)).at []) (fun _ _ _ => False)) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs) := by
  have hload : ∃ t0, (TParE E).load ((O).prog, (O).secs) (Ly h).Λ = some t0 :=
    ⟨_, Scc.Cert.Link.A64.loadParsed_of_loadOk (loadOk_link_of_placeOKAt (i := Scc.Lower.imms1Of p) h) hE.1⟩
  have hss0 : imageOk (Ly h).Λ (O).secs (Scc.Cert.Link.A64.codeOf (Ly h).Λ.code.lo (O).prog) = true :=
    imageIn_link_of_placeOKAt (i := Scc.Lower.imms1Of p) h
  have hss : Scc.Sem.StaticSyms (Ly h).Λ (O).secs (Scc.Cert.Link.A64.codeOf (Ly h).Λ.code.lo (O).prog)
      (fun _ => 0) (fun _ => "") :=
    Scc.Sem.StaticSyms.of_none hs
  have hs' : (Ly h).Λ.static = fun _ => none := funext hs
  have hpc := Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h (Scc.Lower.imms1Of p) E
  obtain ⟨inv, hP, hN, hT, hA, hWr⟩ :=
    Spike.Lib.A64ConsumerS.inst_of_segWS hS (Spike.Lib.A64.PhRec.site_ofPlaceOK h _) (fun _ _ _ h => h)
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.A64.Rt.rS0 (Ly h))
  have htl := (tailNoFul_ovf hI (abortIn_of_placeOKAt h) (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h _)
    (hrel_ofPlaceOK h _) (htk_ofPlaceOK h _)
    (I := fun _ _ _ _ => False) (Λ := (Ly h).Λ) (rS := Spike.Lib.A64.Rt.rS0 (Ly h))
    (Tk' := Spike.Lib.A64.PhRec.Tk (Ly h)) fun _ _ _ _ h => h.elim).step
  exact Spike.Lib.A64ConsumerS.correctKSPE (lsize := fun _ => 0) (name := fun _ => "") rfl hss0 hss
    (wideIn_of_placeOKAt h) ⟨rfl, rfl, hP _ _ _ ⟨hent, rfl⟩⟩ (hs' ▸ AllocInv.FreshInv.init _ _ _) hload
    (.none (Spike.Lib.srcP1_hooks arch)) (Spike.Lib.srcP1_init arch) hN
    (Spike.Lib.A64ConsumerS.safeS_of_accepted1 hp arch _) hT
    (Spike.Lib.A64.PhRec.htk0_of_pc h _ hpc)
    (Spike.Lib.A64.PhRec.hown0_of_pcE h _ hE.1 hpc)
    (Spike.Lib.A64ConsumerS.writeNoPromS_of_wrIn hWr htl) (fun _ => trivial)
    (wf_link_of_placeOKAt (i := Scc.Lower.imms1Of p) h) (Spike.Lib.A64.PhRec.G0_ofPlaceOKE h _ hE.1)
    (Spike.Lib.A64.PhRec.hGpl_ofPlaceOK h _) hA (fun h => h)

/-- **`a64_lower_correctES` at the entry frame `rtF`** (the loaded thread's
node by `entry_atE`). -/
theorem a64_lower_correctES_rtF (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (Ly h).Λ)
    (hS : SegWS (WSS h B.cells) (KS h) p (Ly h).Λ.static (MSS h (G0 h))
      ((At (Ly h).exe (Ly h).endPc (entryR E) (rtF (Ly h))
        (Ret0.entryN (Ly h).lab Spike.Lib.A64Consumer.c0)).at []) (fun _ _ _ => False)) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs) :=
  a64_lower_correctES hp h hs hE (entry_atE h _ hE (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E)) hS

/-- **`a64_lower_correctES` at the entry frame `WordsNone ∧ rtF`** (the
loaded thread's node by `entry_atE_wn`). -/
theorem a64_lower_correctES_wn (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (Ly h).Λ)
    (hS : SegWS (WSS h B.cells) (KS h) p (Ly h).Λ.static (MSS h (G0 h))
      ((At (Ly h).exe (Ly h).endPc (entryR E)
        (fun m => Spike.Lib.DmemPriv.WordsNone (Ly h).Λ m.dmem ∧ rtF (Ly h) m)
        (Ret0.entryN (Ly h).lab Spike.Lib.A64Consumer.c0)).at []) (fun _ _ _ => False)) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs) :=
  a64_lower_correctES hp h hs hE (entry_atE_wn h _ hE (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h _ E)) hS

end Correct

end Spike.Lib.LowerA64
