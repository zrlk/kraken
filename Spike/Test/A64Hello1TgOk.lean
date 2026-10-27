/-
**`hello1`'s branch targets checked** (AArch64; the twin of the x86-64
targets' check): the output's user runs pass `tgOkB`
(`Spike/Lib/LowerA64/UserTgt.lean`) by kernel decision, so `cxBlk2_ofW2`'s
`hTg` holds at `main` (`MainTgA`) and at the setup function's blocks
(`SetupOpenA.hTg`'s statement), and `MainPreUA` at `hello1o` needs no
targets' premise.

- `hello1_tgOkBA`: the check, decided;
- `hello1_mainTgA`: `MainTgA`;
- `hello1_setupTgA`: `SetupOpenA.hTg`'s statement at `hello1o`, every setup declaration;
- `hello1_mainBlkAC`: `MainBlkA` with the check discharged.
-/
import Spike.Lib.LowerA64.UserTgt
import Spike.Test.A64Hello1Main
import Spike.Test.A64Hello1HS

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.LowerNode
open Spike.Lib.A64ConsumerS (InvS)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Rt (RuntimeLayout setupMC)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- **`hello1`'s output passes the targets' check** (kernel decision). -/
theorem hello1_tgOkBA :
    tgOkB (Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A))) = true := by
  decide +kernel

/-- **`SetupOpenA.hTg` at `hello1o`**, at every placement, layout and setup
declaration (`hTg_of_tgOkB` at `hello1_tgOkBA`). -/
theorem hello1_setupTgA {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg (lay2 Λ P1A) (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    (hp : Scc.Lower.Accepted2 P1A = true) {j : Nat} {d : CoreTerm.Decl} (hd : (compiled2 P1A)[j]? = some d) :
    ∀ pc blk, SubCd (CdCLE (Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)))
      (Spike.Lib.A64.PhRec.okPc (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of P1A)))
      (Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of P1A)))
      (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of P1A)).lab
      (Int64.ofBitVec ((RuntimeLayout.ofPlaceOK h (imms2Me Λ P1A)).lab
        (setupMC (setupWords2 P1A)).e0 + 4).toBitVec)) pc blk →
    Kind2 (fnCode2OfPMe hp h Λ j d hd).cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) →
      PosOff (Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)))
        (RuntimeLayout.ofPlaceOK h (imms2Me Λ P1A)).lab ((RuntimeLayout.ofPlaceOK h (imms2Me Λ P1A)).lab L) :=
  hTg_of_tgOkB hello1_tgOkBA (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h1
    (fnCode2OfPMe hp h Λ j d hd).h16 (fun _ _ h => h) _

section Hello1

variable (h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
  (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)

set_option hygiene false in
/-- `hello1o`'s `main`'s code. -/
local notation "FC" => fnCode2OfPMe hello1o_accepted2 h LeA 1 Spike.Test.Hello1MainSrc.mainD
  Spike.Test.Hello1MainSrc.hello1_main_compiled2

/-- **`MainTgA` at `hello1o`** (`hTg_of_tgOkB` at `hello1_tgOkBA`). -/
theorem hello1_mainTgA : MainTgA h :=
  hTg_of_tgOkB hello1_tgOkBA (FC).hf (FC).h1 (FC).h16 (fun _ _ h => h) _

/-- **`MainBlkA` at `hello1o`** at a choice of the bounds, the targets'
check discharged (`hello1_mainBlkA` at `hello1_mainTgA`). -/
theorem hello1_mainBlkAC {Dt : State → Prop} {L D1 D : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2A SccCertificate.config P1A (RuntimeLayout.ofPlaceOK h (imms2Me LeA P1A)) L D1 D lS lM fS nS fM nM)
    (J : InvS) : MainBlkA h Dt J L D :=
  hello1_mainBlkA h hB J (hello1_mainTgA h)

end Hello1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_tgOkBA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_tgOkBA

/-- info: 'Spike.Lib.LowerA64.hello1_setupTgA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_setupTgA

/-- info: 'Spike.Lib.LowerA64.hello1_mainTgA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_mainTgA

/-- info: 'Spike.Lib.LowerA64.hello1_mainBlkAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_mainBlkAC
