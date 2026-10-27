/-
**`hello1`'s landings' bottom exits** (x86-64; the twin of
`Spike/Test/A64Hello1HBot.lean`): `H1RestXW.hbot`
(`Spike/Lib/LowerX64/H1RestXW.lean`) at `hello1o`'s landings, the bottom
keys `BotHR` (`Spike/Test/X64Hello1H0L.lean`), the contexts `CxOkH` and the
write tail `fun _ => True`: `exitStk_ofBotHR` at the extended placement
`upd L l b`, `updN ls l n` (reachable by `Reach.step`), the aborts' segment
by `hello1_hAbQ`, `h0` by `h0L_ofPreUL` from `main`'s callee entry
`hello1_mainPreUTL` (`Spike/Test/X64Hello1MainL.lean`).

The `rodata` block's return type is the setup result's
(`rodata_retTy_compiled2`). Left open: the keys' exits inside the segment
world (`hW`).

- `hello1_hbot`: `H1RestXW.hbot`'s statement at `BotHR`, from `hW`;
- `hello1_h1RestXW_hbot`: the same as `H1RestXW`'s field (a check);
- `hello1_restX_ofHbot`: `H1RestXW` at `BotH` with `hbot` by `hello1_hbot`.
-/
import Spike.Test.X64Hello1H0L
import Spike.Test.X64Hello1MainL
import Spike.Test.X64Hello1Reduce
import Spike.Lib.LowerX64.H1RestXW
import Spike.Lib.LowerSetupRet
import Spike.Test.X64Hello1HAbQ
import Spike.Lib.LblRangeReach

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FragS)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.LowerNode (compiled2 hello1o_accepted2)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.X64.Rt (rtF)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

section Hello1

variable (h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Le P1)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Le P1)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1RestXW`'s). -/
local notation "W2R" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Le P1) (Spike.Lib.X64.PhRec.μ (Ly)) P1 Spike.Lib.LowerNode.IsNum (G2 h P1)
    (Spike.Lib.X64.PhRec.own (Ly)) (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

set_option hygiene false in
/-- The start's frame condition: the runtime's words unloaded and no heap or image word loaded. -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- `hello1o`'s landings at the bottom keys `BotHR`. -/
local notation "ElR" => ElX h (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotHR h)

/-- **`hello1`'s `H1RestXW.hbot` at the bottom keys `BotHR`**
(`exitStk_ofBotHR` at `upd L l b`, `updN ls l n`, reachable by
`Reach.step`; the aborts by `hello1_hAbQ`, `h0` by `h0L_ofPreUL` from
`hello1_mainPreUTL`, the `rodata` return type by `rodata_retTy_compiled2`);
open: the keys' exits `hW`. -/
theorem hello1_hbot {E : Entry}
    (hW : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSX h E (WNF) (ElR) (fun _ => True) (ab2 P1 (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHR h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1 (LU) (Ly).exe (Ly).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2R J (LU) (LN)) s c fs) :
    ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSX h E (WNF) (ElR) (fun _ => True) (ab2 P1 (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHR h k fs →
        SegWS (W2R J (LU) (LN)) (TakeK ((Ly).lab StackTake.siteL) (Spike.Lib.X64.Rt.rS0 (Ly))) P1
          (LU)
          (msOfAX (lay2 Le P1) (Spike.Lib.X64.PhRec.μ (Ly)) P1 Spike.Lib.LowerNode.IsNum (G2 h P1)
            (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
            (ab2 P1 (Ly).lab) (LU) (LN))
          (ExitStk P1 (compiled2 P1) (LU) (Ly).exe (Ly).endPc k fs (GX (CxOkH h hello1o_accepted2)))
          fun _ _ _ => False := by
  intro J hJ L ls l b n hR hl hAL k fs hB
  have hR' := Reach.step hR hl hAL
  have hsw : Spike.Lib.LowerNode.setupWords2 P1 < 6 := by decide
  have hZ := Spike.Lib.LowerX64.setupMC_Z _ hsw
  refine exitStk_ofBotHR h (by rw [hZ]; decide) (by rw [hZ]; decide) hB
    (hW J hJ L ls l b n hR hl hAL k fs hB)
    (hello1_hAbQ h rfl hello1o_accepted2 hello1_hty.choose_spec (fun _ _ _ _ _ _ => trivial) J _ _) ?_
  intro J0 L' D1 fS v D2 lS lM nS fM nM hBd _ d hd hn
  rw [Spike.Lib.LowerNode.rodata_retTy_compiled2 hello1o_accepted2 hello1_hty.choose_spec hd hn]
  have hcx : (fnCode2OfPMe hello1o_accepted2 h Le 1 Spike.Test.Hello1MainSrc.mainD
      Spike.Test.Hello1MainSrc.hello1_main_compiled2).lcx.externs = Scc.Frontend.externs P1 := by
    rw [(fnCode2OfPMe_spec hello1o_accepted2 h Le 1 Spike.Test.Hello1MainSrc.mainD
      Spike.Test.Hello1MainSrc.hello1_main_compiled2).1]
  exact h0L_ofPreUL h hello1o_accepted2 hello1_hty.choose_spec Spike.Test.Hello1MainSrc.hello1_main_compiled2
    Spike.Test.Hello1MainSrc.hello1_main_find rfl (by decide) (by rw [hello1_hty_eq]; rfl)
    (by rw [hello1_hty_eq]; decide) (by decide) (Spike.Test.Hello1MainSrc.hello1_main_noCallee hcx)
    Spike.Test.Hello1MainSrc.hello1_main_noXchg Spike.Test.Hello1MainSrc.hello1_main_noNewBuf J hR' hBd
    (hello1_mainPreUTL h hBd J
      (Spike.Lib.lblRange_reach (Spike.Lib.X64.Rt.arOf_sub h) (fun _ => rfl) hR')
      (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (hello1_mainTg h)) v

/-- **`hello1_hbot` is `H1RestXW.hbot`'s field** at `hello1o`'s landings
(`BotHR`, `CxOkH`, the write tail `fun _ => True`): any `H1RestXW` with its
`hbot` replaced. -/
theorem hello1_h1RestXW_hbot {E : Entry}
    (H : H1RestXW h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotHR h) (fun _ => True))
    (hW : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSX h E (WNF) (ElR) (fun _ => True) (ab2 P1 (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHR h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1 (LU) (Ly).exe (Ly).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2R J (LU) (LN)) s c fs) :
    H1RestXW h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotHR h) (fun _ => True) :=
  { H with hbot := hello1_hbot h hW }

/-- **`hello1_hbot` plugs into `H1RestXW.hbot`** at the final theorems'
arguments (`BotH h`, of which `BotHR h` is an abbreviation; the twin of
`hello1_landA_ofHbot`): any `H1RestXW` at `BotH h` with its `hbot` replaced. -/
theorem hello1_restX_ofHbot {E : Entry}
    (H : H1RestXW h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True))
    (hW : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSX h E (WNF) (ElR) (fun _ => True) (ab2 P1 (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHR h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1 (LU) (Ly).exe (Ly).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2R J (LU) (LN)) s c fs) :
    H1RestXW h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True) :=
  { H with hbot := hello1_hbot h hW }

end Hello1

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_hbot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hbot

/-- info: 'Spike.Lib.LowerX64.hello1_h1RestXW_hbot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_h1RestXW_hbot

/-- info: 'Spike.Lib.LowerX64.hello1_restX_ofHbot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_restX_ofHbot
