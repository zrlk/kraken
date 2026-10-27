/-
**The x86-64 consumer at any call depth from `_start`'s segment** for an
`Accepted1` program with calls: the closure half of
`Spike/Lib/LowerX64/Correct1.lean` (`x64_lower_correctE1`'s steps after the
start segment) over `SegWS`, the frames twin. Given `_start`'s segment at
depth inside `SFactsS` at the overflow stub's write tail (`hS`: from `_start`'s
node at the empty frames to `False`), the output is `Correct` over the target
on parsed texts at the entry state `E`.

- `x64_lower_correctES`: at any frame `F` of the entry stack holding at the
  loaded thread's `_start` node (`hent`): `inst_of_segWS` (the fragment with
  `NodesS`, `TakePathS`, `AbortPathS`, `WrInS`), `safeS_of_accepted1`
  (`Spike/Lib/X64Accepted1SafeS.lean`), `writeNoPromS_of_wrIn` at the
  overflow stub's closed tail (`tailNoFul_ovf`'s step) and `correctKSPE`;
- `x64_lower_correctES_rtF`: at `rtF` (`entry_atXE`);
- `x64_lower_correctES_wn`: at `WordsNone ∧ rtF` (`entry_atXE_wn`), the
  frames twin of `x64_lower_correctE1_wn`'s closure;
- `msOfS_nil`: the memory side at depth 0 is the placement's (`msOf`), the
  form of `x64_start_segWSG`'s `hms`.
-/
import Spike.Lib.LowerX64.Correct1WN
import Spike.Lib.X64SegInstS
import Spike.Lib.X64Accepted1SafeS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64Consumer (Lbl Lsize msOf TParE)
open Spike.Lib.X64ConsumerS (SFactsS msOfS)
open Spike.Lib.X64.Rt (RuntimeLayout rtF entryR)
open Spike.Lib.X64.PhRec (μ K)
open Scc.Sem Scc.Sem.X64 Scc.Cert.Link Spike.Lib.Consumer1
open Spike.Lib.X64.PhRec (G0_ofPlaceOKE hGpl_ofPlaceOK htk0_ofPlaceOK hph0_of hph0_ofPlaceOK hown0_ofPlaceOKE)

/-- **The memory side at depth 0 is the placement's**: `msOfS` at the empty
frames, owned words independent of the frames, is `msOf` (its exit
placement `[] = [] ∧ Placed` is `Placed`). -/
theorem msOfS_nil {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.X64Consumer.Own} {lbl : Lbl} {lsize : Lsize} :
    msOfS Λ μ rd G (fun s _ => own s) lbl lsize [] = msOf Λ μ rd G own lbl lsize := by
  simp only [msOfS, msOf, true_and]; rfl

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
  {labelOffs : List (String × Nat)}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The facts every pair of the run carries at its frames, at the arena's
`cells` and the overflow stub's write tail. -/
local notation "WSS" h:max cells:max => fun s c fs => SFactsS (Ly h).Λ (μ (Ly h)) p
  (fun s _ => Spike.Lib.X64.PhRec.own (Ly h) s) (Spike.Lib.X64.Rt.rS0 (Ly h)) (Spike.Lib.X64.PhRec.Tk (Ly h))
  (Ly h).Λ.static cells 0 s c fs (OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab)

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max G:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) G
  (fun s _ => Spike.Lib.X64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.X64.PhRec.GOf (Ly h) (Spike.Lib.X64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.X64.Rt.rS0 (Ly h))

/-- The loaded thread at the entry state `E`. -/
local notation "T0" h:max E:max => Scc.Sem.X64.threadAt E (Ly h).Λ.code.lo (O).prog
  (Scc.Sem.loadSyms (Ly h).Λ (O).secs.rodata)

/-- **The x86-64 consumer at any call depth for an `Accepted1` program**
at an admissible entry state `E` (`hE`), no static label (`hs`): `_start`'s
segment at depth inside `SFactsS` at the budget's arena and the overflow
stub's write tail (`hS`, from `_start`'s node at the entry frame `F` and the
empty frames, never leaving), the loaded thread at that node (`hent`), gives
`Correct` over the target on parsed texts at `E`. -/
theorem x64_lower_correctES (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (Ly h).Λ) {F : MachineData → Prop}
    (hent : At (Ly h).exe (Ly h).endPc (entryR E) F (Spike.Lib.X64.Rt.entryN0 (Ly h).lab Spike.Lib.X64Consumer.c0)
      (T0 h E) Spike.Lib.X64Consumer.c0)
    (hS : SegWS (WSS h B.cells) (KS h) p (Ly h).Λ.static (MSS h (G0 h))
      ((At (Ly h).exe (Ly h).endPc (entryR E) F
        (Spike.Lib.X64.Rt.entryN0 (Ly h).lab Spike.Lib.X64Consumer.c0)).at []) (fun _ _ _ => False)) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs, (O).labelOffs) := by
  have hload : ∃ t0, (TParE E).load ((O).prog, (O).secs, (O).labelOffs) (Ly h).Λ = some t0 :=
    ⟨_, Scc.Cert.Link.X64.loadParsed_of_loadOk (loadOk_link_of_placeOKAt (i := Scc.Lower.imms1Of p) h) hE.1⟩
  have hss0 : imageOk (Ly h).Λ (O).secs (Scc.Sem.X64.codeLabel (Ly h).Λ.code.lo (O).prog) = true :=
    imageIn_link_of_placeOKAt (i := Scc.Lower.imms1Of p) h
  have hss : Scc.Sem.StaticSyms (Ly h).Λ (O).secs (Scc.Sem.X64.codeLabel (Ly h).Λ.code.lo (O).prog)
      (fun _ => 0) (fun _ => "") :=
    Scc.Sem.StaticSyms.of_none hs
  have hs' : (Ly h).Λ.static = fun _ => none := funext hs
  have hpc := Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h (Scc.Lower.imms1Of p) E
  obtain ⟨inv, hP, hN, hT, hA, hWr⟩ :=
    Spike.Lib.X64ConsumerS.inst_of_segWS hS (Spike.Lib.X64.PhRec.site_ofPlaceOK h _) (fun _ _ _ h => h)
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
  have htl := (tailNoFul_ovf hI (hprog_ofPlaceOK h (Scc.Lower.imms1Of p))
    (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h _) (hrel_ofPlaceOK h _) (htk_ofPlaceOK h _)
    (I := fun _ _ _ _ => False) (Λ := (Ly h).Λ) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
    (Tk' := Spike.Lib.X64.PhRec.Tk (Ly h)) fun _ _ _ _ h => h.elim).step
  exact Spike.Lib.X64ConsumerS.correctKSPE (lsize := fun _ => 0) (name := fun _ => "") rfl hss0 hss
    (wideIn_of_placeOKAt h) ⟨rfl, rfl, hP _ _ _ ⟨hent, rfl⟩⟩ (hs' ▸ AllocInv.FreshInv.init _ _ _) hload
    (.none (Spike.Lib.srcP1_hooks arch)) (Spike.Lib.srcP1_init arch) hN
    (Spike.Lib.X64ConsumerS.safeS_of_accepted1 hp arch _) hT
    (htk0_ofPlaceOK h _ (hph0_of h _ hpc (hph0_ofPlaceOK h _)))
    (hown0_ofPlaceOKE h _ hE.1 (hph0_of h _ hpc (hph0_ofPlaceOK h _)))
    (Spike.Lib.X64ConsumerS.writeNoPromS_of_wrIn hWr htl) (fun _ => trivial)
    (wf_link_of_placeOKAt (i := Scc.Lower.imms1Of p) h) (G0_ofPlaceOKE h _ hE.1)
    (hGpl_ofPlaceOK h _ (Spike.Lib.X64.PhRec.hclr_ofPlaceOK h _)) hA (fun h => h)

/-- **`x64_lower_correctES` at the entry frame `rtF`** (the loaded thread's
node by `entry_atXE`). -/
theorem x64_lower_correctES_rtF (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (Ly h).Λ)
    (hS : SegWS (WSS h B.cells) (KS h) p (Ly h).Λ.static (MSS h (G0 h))
      ((At (Ly h).exe (Ly h).endPc (entryR E) (rtF (Ly h))
        (Spike.Lib.X64.Rt.entryN0 (Ly h).lab Spike.Lib.X64Consumer.c0)).at []) (fun _ _ _ => False)) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs, (O).labelOffs) :=
  x64_lower_correctES hp h hs hE (entry_atXE h _ hE (Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h _ E)) hS

/-- **`x64_lower_correctES` at the entry frame `WordsNone ∧ rtF`** (the
loaded thread's node by `entry_atXE_wn`). -/
theorem x64_lower_correctES_wn (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) {B : Scc.Sem.Budget} {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (Ly h).Λ)
    (hS : SegWS (WSS h B.cells) (KS h) p (Ly h).Λ.static (MSS h (G0 h))
      ((At (Ly h).exe (Ly h).endPc (entryR E)
        (fun m => Spike.Lib.DmemPriv.WordsNone (Ly h).Λ m.dmem ∧ rtF (Ly h) m)
        (Spike.Lib.X64.Rt.entryN0 (Ly h).lab Spike.Lib.X64Consumer.c0)).at []) (fun _ _ _ => False)) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs, (O).labelOffs) :=
  x64_lower_correctES hp h hs hE (entry_atXE_wn h _ hE (Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h _ E)) hS

end Correct

end Spike.Lib.LowerX64
