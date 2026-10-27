/-
**`hello1`'s allocator `W2` instance at the landings' contexts, closed**
(AArch64): `OpenAPtA` (`Spike/Test/A64Hello1HAWNone.lean`, `allocW2At_of`'s
per-allocation premises `AllocPtW` at every `CxOkH` context) at `hello1o`,
the landings `ElH` and the write tail `fun _ => True`, and so `OpenAHA`
there (`hello1_hAW_noneA`), `hello1_finalAW_ofT`'s `HA`
(`Spike/Test/A64Hello1FinalT.lean`).

The fields of `AllocPtW` at `rodata`'s allocation:

- `hleaf`, `hu`, `hacc`, `hnr`: `hello1_ptFieldsA`
  (`Spike/Test/A64Hello1AllocPtH.lean`);
- `hms`: `callMsOK_arOf` at the Linux entry (the record's executable), the
  value invariant `GOf` free at the counter and the heap
  (`gOf_ctr_arOf`, `gOf_heap_arOf`), the header without trace words
  (`hello1_rodata_hdrA`);
- `hxa`, `hxaF`: `landStk_hxa` at the context `CxOkH` with no records (its
  key the setup frame's bottom key `BotH`, from the bounds and `SB`), the
  setup call's return address of the phase anchor's phase (`raOk_setup`),
  the resumption point `BodyPtW` from `PtC2` and `Fresh`; for `hxaF` at the
  family `J'`, the call's premises and its call context rebuilt there (the
  memory sides differ only in `xa`);
- `hstub`: `hello1_hstubA` (`Spike/Test/A64Hello1AllocStubH.lean`).

- `hello1_openAPtA`: `OpenAPtA` at `hello1o`;
- `hello1_openAHA`: `OpenAHA` at `hello1o` (`hello1_hAW_noneA`).
-/
import Spike.Test.A64Hello1HAWNone
import Spike.Test.A64Hello1AllocPtH
import Spike.Test.A64Hello1AllocStubH
import Spike.Lib.LowerA64.LandStk2
import Spike.Lib.LowerA64.LandHu

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "LeA" => Λx

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h' (Spike.Lib.LowerNode.imms2Me LeA P1A)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h' (Scc.Lower.imms2Of P1A)

/-- **`OpenAPtA` at `hello1o`**: `AllocPtW` at `rodata`'s allocation at
every choice of the bounds, family containing the starts and context
`CxOkH` (see the module docstring). -/
theorem hello1_openAPtA : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
    ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenAPtA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True) := by
  intro E _ h' L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn R F fs fp ra tp G0 Ab' hC hSB
    c0 pc kk x cn τ e env n lits cs bufs tk kv en em hh hc0 hT hfr hat hco hhd hpt
  have hc := Spike.Lib.A64.Rt.ctrZ_ofPlaceOK h'
  -- the context with no records: its key the setup frame's bottom key
  have hcx : CxOkS (p := P1A) (lbl := fun _ => none) (lsize := fun _ => 0)
      (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA) (CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2)
      (BotH h') j R F fs fp ra tp G0 Ab' :=
    ⟨hC, [], ⟨J, L, D1, fS, v, D2, lS, lM, nS, fM, nM, hB, hSB⟩, d, hd, hn⟩
  -- the setup call's return address has the phase anchor's phase
  have hra : Spike.Lib.A64.PhRec.ph (LY0) (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph (LY0)
        (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat := by
    obtain ⟨-, -, -, -, -, -, -, g, fr, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, hgra, -⟩, -, -, -, -, -,
      hra, -⟩ := id hC
    rw [hra, hgra]
    exact raOk_setup _ _
  -- the allocation a resumption point of the block's code
  have hpt' : BodyPtW (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA j d hd) ra pc
      (.let_ x (.newBuf cn τ) e) env n lits cs bufs := by
    obtain ⟨l, k, r, h1, h2, h3, h4, h5, h6, h7⟩ := hpt
    unfold BodyPtW
    rw [(fnCode2OfPMe_spec _ h' _ j d hd).2.1]
    exact ⟨l, k, r, kk, h1, hfr, h2, h3, h4, h5, h6, h7⟩
  have H := hello1_ptFieldsA h' hd hC J hat hco hpt
  refine ⟨H.1, H.2.1, H.2.2.1, ?hms, H.2.2.2, ?hxa, ?hxaF, ?hstub⟩
  case hms =>
    intro q _ hτ hh'
    have hm : (Spike.Lib.A64.Alloc.mOf q.h).toNat = 0 := by
      obtain ⟨-, -, rfl, -⟩ := hello1_rodata_nbTailA hd hT
      rw [hh']
      exact hello1_rodata_hdrA (by rw [(fnCode2OfPMe_spec _ h' _ j d hd).1] at hco; exact hco)
        (by rw [(fnCode2OfPMe_spec _ h' _ j d hd).1] at hhd; exact hhd)
    have hq : ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us := by rw [hτ]; exact H.2.2.1
    exact callMsOK_arOf h' hc Entry.linux _ (gOf_ctr_arOf h' _ _) (gOf_heap_arOf h' _ _) hq hm
  case hxa =>
    intro la hla
    exact landStk_hxa (Spike.Lib.A64.Rt.arOf_ok h' hc) (startsN_of_startsS hJ) Spike.Lib.AllocReach.Reach.base hd
      hcx hra hc0 hpt' ⟨tk, en, em, hat, hco, hhd, rfl⟩ hla (arOf_units_fit _)
  case hxaF =>
    intro la hla q hq J' hJ' l b w s c hl hAt htp
    -- the call's premises at the family `J'` (the memory sides differ only in `xa`)
    have hq' : q.OK (Spike.Lib.A64ConsumerA.msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) P1A
        Spike.Lib.LowerNode.IsNum (Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ (OA).prog (OA).secs))
        (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (lay2 LeA P1A)) (fun _ => none) (fun _ => 0) J')
        (ab2 P1A (Ly).lab) (fun _ => none) (fun _ => 0) fs) (_root_.Executable.labels (Ly).exe).label := by
      cases hab : ab2 P1A (Ly).lab <;> rw [hab] at hq <;>
        exact ⟨hq.term, hq.ev, hq.num, hq.hold, hq.n_lt, hq.ctr, hq.heap, hq.room, hq.cells, hq.units, hq.off,
          hq.accs, hq.rt, hq.mp, hq.grow, hq.hdr⟩
    exact landStk_hxa (J := J') (Spike.Lib.A64.Rt.arOf_ok h' hc) hJ' Spike.Lib.AllocReach.Reach.base hd hcx hra
      hc0 hpt' ⟨tk, en, em, hat, hco, hhd, rfl⟩ hla (arOf_units_fit _) ⟨q, hq'⟩ _ (fun m hm => hm.1)
      (fun m hm => hm.2.2) l b w s c hl hAt htp
  case hstub =>
    exact hello1_hstubA h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec hd hC
      (hello1_hTnA j d hd x cn τ e hT) hpt

/-- **`OpenAHA` at `hello1o`** (`hello1_hAW_noneA` at `hello1_openAPtA`):
`hello1_finalAW_ofT`'s `HA`. -/
theorem hello1_openAHA : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
    ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenAHA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True) :=
  hello1_hAW_noneA hello1_openAPtA

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_openAPtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_openAPtA

/-- info: 'Spike.Lib.LowerA64.hello1_openAHA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_openAHA
