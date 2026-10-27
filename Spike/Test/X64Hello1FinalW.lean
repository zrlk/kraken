/-
**`hello1`'s x86-64 landings on the `WordsNone` chain**: the landings `ElX`
(`Spike/Lib/LowerX64/H1InLand.lean`) at `hello1o`'s code with the setup
frame's contexts `CxOkH` and bottoms `BotH`
(`Spike/Test/X64Hello1CxOkH.lean`), the landings of the statement
`hello1_finalW_ofT` (`Spike/Test/X64Hello1FinalT.lean`). `main`'s call
`HUBVF` is closed (`hello1_hUBVF`, `Spike/Test/X64Hello1HUF.lean`).

- `ElH`: the landings at `hello1o`'s code, `CxOkH`, `BotH`.
-/
import Spike.Test.X64Hello1CxOkH
import Spike.Test.X64Hello1HUF
import Spike.Lib.LowerX64.H1InLandW

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (FragS)
open Spike.Lib.X64Consumer (Lbl Lsize)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

/-- **`hello1`'s landings**: `ElX` at `hello1o`'s code `fnCode2OfPMe`, the
setup frame's contexts `CxOkH` and bottoms `BotH`. -/
def ElH (h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true) :
    Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa :=
  ElX h (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le)
    (CxOkH h Spike.Lib.LowerNode.hello1o_accepted2) (BotH h)

end Spike.Lib.LowerX64
