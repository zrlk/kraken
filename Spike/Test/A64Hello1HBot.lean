/-
**`hello1`'s landings' bottom exits** (AArch64): `H1LandAW.hbot`
(`Spike/Lib/LowerA64/H1RestAW.lean`) at `hello1o`'s landings, the bottom
keys `BotHRA` (`Spike/Test/A64Hello1BotRes.lean`), the contexts `CxOkH` and
the write tail `fun _ => True`: `exitStk_ofBotHRL` at the extended
placement `upd L l b`, `updN ls l n` (reachable by `Reach.step`), the
aborts' segment by `hello1_hAbQA` (`Spike/Test/A64Hello1HAbQ.lean`) and
`main`'s call by `hello1_hUAFL` (`Spike/Test/A64Hello1HUFL.lean`).

The `rodata` block's return type is the setup result's
(`rodata_retTy_compiled2`). Left open: the keys' exits inside the segment
world (`hW`).

- `hello1_hbotA`: `H1LandAW.hbot`'s statement at `BotHRA`, from `hW`;
- `hello1_landA_ofHbot`: `H1LandAW` at `BotH` with `hbot` by `hello1_hbotA`.
-/
import Spike.Test.A64Hello1BotRes
import Spike.Test.A64Hello1HAbQ
import Spike.Test.A64Hello1HUFL
import Spike.Lib.LowerA64.H1RestAW
import Spike.Lib.LowerSetupRet

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.LowerNode (compiled2 hello1o_accepted2)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.A64.Rt (rtF)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

section Hello1

variable (h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me LeA P1A)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 LeA P1A)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1RestAW`'s). -/
local notation "W2R" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 LeA P1A) (Spike.Lib.A64.PhRec.μ (Ly)) P1A Spike.Lib.LowerNode.IsNum (G2 h P1A)
    (Spike.Lib.A64.PhRec.own (Ly)) (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

set_option hygiene false in
/-- The start's frame condition: the private memory loading no runtime word and `rtF`. -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- `hello1o`'s landings at the bottom keys `BotHRA`. -/
local notation "ElR" => ElA h (fnCode2OfPMe hello1o_accepted2 h LeA) (CxOkH h hello1o_accepted2) (BotHRA h)

/-- **`hello1`'s `H1LandAW.hbot` at the bottom keys `BotHRA`**
(`exitStk_ofBotHRL` at `upd L l b`, `updN ls l n`, reachable by
`Reach.step`; the aborts by `hello1_hAbQA`, `main`'s call by
`hello1_hUAFL`, the `rodata` return type by `rodata_retTy_compiled2`);
open: the keys' exits `hW`. -/
theorem hello1_hbotA {E : Entry}
    (hW : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSA h E (WNF) (ElR) (fun _ => True) (ab2 P1A (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHRA h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1A)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1A (LU) (Ly).exe (Ly).endPc k.R k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2R J (LU) (LN)) s c fs) :
    ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSA h E (WNF) (ElR) (fun _ => True) (ab2 P1A (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHRA h k fs →
        SegWS (W2R J (LU) (LN)) (TakeK ((Ly).lab StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))) P1A
          (LU)
          (msOfAX (lay2 LeA P1A) (Spike.Lib.A64.PhRec.μ (Ly)) P1A Spike.Lib.LowerNode.IsNum (G2 h P1A)
            (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
            (ab2 P1A (Ly).lab) (LU) (LN))
          (ExitStk P1A (compiled2 P1A) (LU) (Ly).exe (Ly).endPc k fs (GA (CxOkH h hello1o_accepted2)))
          fun _ _ _ => False := by
  intro J hJ L ls l b n hR hl hAL k fs hB
  exact exitStk_ofBotHRL h hello1o_accepted2 hello1_htyA.choose_spec
    (fun _ _ hd hn =>
      Spike.Lib.LowerNode.rodata_retTy_compiled2 hello1o_accepted2 hello1_htyA.choose_spec hd hn)
    (.step hR hl hAL) hB
    (hW J hJ L ls l b n hR hl hAL k fs hB)
    (hello1_hAbQA h rfl hello1o_accepted2 hello1_htyA.choose_spec (fun _ _ _ _ _ _ => trivial) J _ _)
    fun L' D1 D2 lS lM fS nS fM nM hBd => hello1_hUAFL h hBd J (.step hR hl hAL) _

/-- **`hello1_hbotA` plugs into `H1LandAW.hbot`** at the final theorems'
arguments (`BotH h`, of which `BotHRA h` is an abbreviation): any
`H1LandAW` with its `hbot` replaced by `hello1_hbotA`'s. -/
theorem hello1_landA_ofHbot {E : Entry}
    (H : H1LandAW h E (fnCode2OfPMe hello1o_accepted2 h LeA) (CxOkH h hello1o_accepted2) (BotH h)
      (fun _ => True))
    (hW : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSA h E (WNF) (ElR) (fun _ => True) (ab2 P1A (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHRA h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1A)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1A (LU) (Ly).exe (Ly).endPc k.R k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2R J (LU) (LN)) s c fs) :
    H1LandAW h E (fnCode2OfPMe hello1o_accepted2 h LeA) (CxOkH h hello1o_accepted2) (BotH h)
      (fun _ => True) :=
  { H with hbot := hello1_hbotA h hW }

end Hello1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_hbotA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hbotA
/-- info: 'Spike.Lib.LowerA64.hello1_landA_ofHbot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_landA_ofHbot
