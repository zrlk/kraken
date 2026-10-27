/-
**`hello1`'s landings at the walk past `rodata`'s allocation** (AArch64;
the twin of `Spike/Test/X64Hello1ResI.lean`'s `resumeCx2T_ofCxOkH`,
`hello1_restXT`, `hello1_finalT`): `H1LandAWT`
(`Spike/Lib/LowerA64/H1LandAWT.lean`) at `hello1o`'s landings at
`Tr := fun j => TrNb (TailAt2 P1A j)`, the shape `hello1_finalA'`
(`Spike/Test/A64Hello1FinalO.lean`) takes it.

- `resumeCx2T_ofCxOkH`: `H1LandAWT.hresL`'s field at `CxOk := CxOkH h hp`
  at a restriction `Tr` with no allocation on `rodata`'s restricted walk:
  the context's `CxLB` there (`cxLBT_ofCxOkH`), its blocks
  (`cxBlk2_ofCxOkHA`), the abort node empty (addition-free), by
  `resumeCx2T_ofCxLB_noCall`;
- `hello1_landAWT`: `H1LandAWT` at `hello1o` from the bottom keys' exits
  `hW` (`hAW` by `hello1_hAWA`, `hTr` by `TrNb.intro`, `hresL` by
  `resumeCx2T_ofCxOkH`, `hresS` vacuous by `hello1_rodata_noCallT`, `hbot`
  by `hello1_hbotA`);
- `hello1_finalTA`: `hello1_finalA'` with `H1` by `hello1_landAWT`;
- `hello1_landAWTW`, `hello1_finalTWA`: the same at `hW := hello1_hWBotA`.
-/
import Spike.Test.A64Hello1ResI
import Spike.Test.A64Hello1HAW
import Spike.Test.A64Hello1HWBot
import Spike.Test.A64Hello1TgOk
import Spike.Test.A64Hello1HsOf
import Spike.Test.A64Hello1FinalO
import Spike.Lib.LowerA64.H1LandAWT

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (rS0 rtF)
open Spike.Lib.LowerNode (compiled2 TailAt2 imms2Me addFreeT tailOf_addFree)
open Spike.Lib.AllocReach (Reach IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1LandAWT`'s). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (`H1LandAWT`'s). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
    (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

/-- **A landings' context's `ResumeCx2T` at an extended placement on a walk
restriction with no allocation** (`H1LandAWT.hresL`'s field at `CxOk :=
CxOkH h hp`): at a restriction `Tr` whose points of `rodata`'s walk hold no
allocation's `let` (`hT`), the context's `CxLB` at `TailAt2 p j ∧ Tr j`
(`cxLBT_ofCxOkH`), its `ResumeCx2T` by `resumeCx2T_ofCxLB_noCall`: the
body's and pending blocks by `cxBlk2_ofCxOkHA` (the jump targets by
`tgOkB`), the calls in the code (`cdOf_of_blC`), the abort node empty at an
addition-free body (`hno`). -/
theorem resumeCx2T_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) (hA : Spike.Lib.A64.Flow.allocIn OP = true) (hTg : tgOkB OP = true)
    (hnc : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" →
      (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hno : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → addFreeT d.body = true)
    {Tr : Nat → Expr → Prop}
    (hT : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" →
      ∀ x cn τ e, ¬ (TailAt2 p j (.let_ x (.newBuf cn τ) e) ∧ Tr j (.let_ x (.newBuf cn τ) e))) :
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ j d (hd : (compiled2 p)[j]? = some d) R F fs fp ra tp G0 Ab, CxOkH h hp j R F fs fp ra tp G0 Ab →
      Spike.Lib.A64.PhRec.ph (LY0) (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.A64.PhRec.ph (LY0)
          (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat →
      ResumeCx2T (W2R J Dt (LU) (LN)) (KT) p (LU) (LN) (MSR J (LU) (LN))
        (fnCode2OfPMe hp h Λ j d hd) R F fs fp ra tp G0 Ab (Tr j) := by
  intro L ls l b n hL hl hAL j d hd R F fs fp ra tp G0 Ab hc hra
  have H := cxLBT_ofCxOkH h hp hty J (Dt := Dt) (T := fun t => TailAt2 p j t ∧ Tr j t) hL hl hAL hd
    (hT j d hd) hc
  have hblk := cxBlk2_ofCxOkHA h hp hty hTg J (Dt := Dt) (LU) (LN) hd hc
  have hn : d.name = "rodata" := by
    obtain ⟨d', hd', -, -, -, -, -, -, -, -, hn, -⟩ := hc
    cases (Option.some.inj (hd.symm.trans hd'))
    exact hn
  have hfs : fs ≠ [] := by
    obtain ⟨-, -, -, -, -, -, -, -, fr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfs, -⟩ := hc
    exact fun h0 => List.cons_ne_nil _ _ (hfs.symm.trans h0)
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))
  refine resumeCx2T_ofCxLB_noCall (Λ := (Ly).Λ) hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hA
    (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hpN
    (fnCode2OfPMe hp h Λ j d hd) (Tr := Tr j) (fun t ht => ht d hd) (hnc j d hd hn) (hTn j d hd hn) hra ?_ H ?_
    (fun c0 hc0 pc t s lits cs bufs blk hsub hk => hblk.1 c0 hc0 pc t s lits cs bufs blk hsub hk (absurd · hfs))
    (fun c0 hc0 pc t s lits cs bufs k blk hsub hk h1 =>
      hblk.2 c0 hc0 pc t s lits cs bufs k blk hsub hk h1 (absurd · hfs))
    (fun _ _ s c' hA' => by
      exfalso
      obtain ⟨-, -, -, -, σ, -, -, ⟨⟨sv, lits, hAb, -, -, -, hT'⟩, -⟩, -⟩ := hA'
      obtain ⟨x, a, b', e, -, -, -, -, -, -, he, -⟩ := hAb.1
      exact tailOf_addFree (hT'.1 d hd) (hno j d hd hn) x a b' e he)
  · intro pc g k hb
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1] at hb
    exact cdOf_of_blC hI hb.1.1
  · rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]

end Assembled

section Hello1

open Spike.Lib.LowerNode (hello1o_accepted2)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

variable (h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "LyH" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me LeA P1A)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "ArH" => Spike.Lib.A64.Rt.arOf (lay2 LeA P1A)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1LandAWT`'s at `Dt := fun _ => True`). -/
local notation "W2H" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 LeA P1A) (Spike.Lib.A64.PhRec.μ (LyH)) P1A Spike.Lib.LowerNode.IsNum (G2 h P1A)
    (Spike.Lib.A64.PhRec.own (LyH)) (rS0 (LyH)) (Spike.Lib.A64.PhRec.Tk (LyH)) (ArH)
    (IN (ArH) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.A64.WriteAb.Ab (LyH).lab) L ls s c fs

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

set_option hygiene false in
/-- The start's frame condition: the private memory loading no runtime word and `rtF`. -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (LyH).Λ (MachineData.dmem m) ∧ rtF (LyH) m

set_option hygiene false in
/-- `hello1o`'s landings at the bottom keys `BotHRA`. -/
local notation "ElR" => ElA h (fnCode2OfPMe hello1o_accepted2 h LeA) (CxOkH h hello1o_accepted2) (BotHRA h)

/-- **`hello1`'s `H1LandAWT` at the walk past `rodata`'s allocation**
(`hello1_finalA'`'s `H1` at `Tr := fun j => TrNb (TailAt2 P1A j)`), from
the bottom keys' exits `hW` alone (`hello1_hbotA`'s): `hAW` by
`hello1_hAWA`; `hTr` by `TrNb.intro`; `hresL` by `resumeCx2T_ofCxOkH` (no
allocation on the restricted walk: `hello1_rodata_trNoNbT`; no call,
element types, addition-free: `hello1_rodata_noCall`, `hello1_hTnA`,
`hello1_rodata_addFree`; the allocator's code and jump targets:
`hello1_allocInA`, `hello1_tgOkBA`); `hresS` vacuous (no call in `rodata`:
`hello1_rodata_noCallT`); `hbot` by `hello1_hbotA`. -/
theorem hello1_landAWT {E : Entry}
    (hW : ∀ J : InvS, (∀ L ls, Reach (ArH) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSA h E (WNF) (ElR) (fun _ => True) (ab2 P1A (LyH).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (ArH) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (ArH).heap (ArH).cells b n →
      ∀ k fs, BotHRA h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1A)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1A (LU) (LyH).exe (LyH).endPc k.R k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2H J (LU) (LN)) s c fs) :
    H1LandAWT h E (fnCode2OfPMe hello1o_accepted2 h LeA) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True)
      (fun j => TrNb (TailAt2 P1A j)) where
  hAW := hello1_hAWA h
  hTr := fun _ _ _ _ _ _ _ _ hT ht => TrNb.intro hT ht
  hresL := fun J _ => resumeCx2T_ofCxOkH h hello1o_accepted2 hello1_htyA.choose_spec J hello1_allocInA
    hello1_tgOkBA hello1_rodata_noCall (fun j d hd _ => hello1_hTnA j d hd) hello1_rodata_addFree
    (fun _ _ hd hn => hello1_rodata_trNoNbT hd hn)
  hresS := fun _ _ _ _ _ _ _ _ _ _ j d hd _ _ _ _ _ _ _ _ hc _ ⟨x, g, b, e, hT⟩ => by
    exfalso
    obtain ⟨d', hd', -, -, -, -, -, -, -, -, hn, -⟩ := hc
    obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
    exact hello1_rodata_noCallT hd hn x g [] b [] e hT
  hbot := hello1_hbotA h hW

omit h in
/-- **`hello1_finalA'` with `H1` by `hello1_landAWT`**: `hello1`'s AArch64
statement from the bottom keys' exits `hW` and the allocator's `W2`
instance at the setup frame `OpenAHA`. -/
theorem hello1_finalTA
    (hW : ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      ∀ J : InvS, (∀ L ls, Reach (ArH) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSA h E (WNF) (ElR) (fun _ => True) (ab2 P1A (LyH).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (ArH) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (ArH).heap (ArH).cells b n →
      ∀ k fs, BotHRA h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1A)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1A (LU) (LyH).exe (LyH).endPc k.R k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2H J (LU) (LN)) s c fs)
    (HA : ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenAHA h hello1o_accepted2 E (ElH h hello1o_accepted2) (fun _ => True))
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
      SccCertificate.asm :=
  hello1_finalA' (fun E hE h => hello1_landAWT h (hW E hE h)) HA hpa hB

/-- **`hello1`'s `H1LandAWT` closed** at `TrNb (TailAt2 P1A j)`:
`hello1_landAWT` at the bottom keys' exits `hello1_hWBotA`. -/
theorem hello1_landAWTW {E : Entry} :
    H1LandAWT h E (fnCode2OfPMe hello1o_accepted2 h LeA) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True)
      (fun j => TrNb (TailAt2 P1A j)) :=
  hello1_landAWT h (hello1_hWBotA h)

omit h in
/-- **`hello1`'s AArch64 statement from `OpenAHA` alone**: `hello1_finalTA`
at the bottom keys' exits `hello1_hWBotA`. -/
theorem hello1_finalTWA
    (HA : ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenAHA h hello1o_accepted2 E (ElH h hello1o_accepted2) (fun _ => True))
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
      SccCertificate.asm :=
  hello1_finalTA (fun _ _ h => hello1_hWBotA h) HA hpa hB

end Hello1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.resumeCx2T_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.resumeCx2T_ofCxOkH

/-- info: 'Spike.Lib.LowerA64.hello1_landAWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_landAWT

/-- info: 'Spike.Lib.LowerA64.hello1_finalTA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalTA

/-- info: 'Spike.Lib.LowerA64.hello1_landAWTW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_landAWTW

/-- info: 'Spike.Lib.LowerA64.hello1_finalTWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalTWA
