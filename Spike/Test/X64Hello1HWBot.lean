/-
**`hello1`'s bottom keys' exits inside the segment world** (x86-64): the
premise `hW` of `hello1_hbot` (`Spike/Test/X64Hello1HBot.lean`). At a
`BotHR` key's return exit `s`, `c` (`ExitC2SL`'s return disjunct), the
key's frames are the setup call's one frame `fr` and the source pops it to
`c''` with `s` at `scc_rt_main`'s `mainS0` (`setupBot_popM`); `h0`'s
segment (`h0L_ofPreUL`) has `W2` at `(s, c'', [])` (its invariant holds at
its pre); the pop is undone by `w2_ofPopped`: `c''` (the setup call's
continuation, `SPostC`) allocates nothing and is no overflow
(`postS_setupTerm`), the `ret`'s pair with `fr` is free of `ZBad`
(`frOk2_retFr`) and placed from `c''`'s placement and the result registers
(`placedS_retFr`; `c''` is at no output-extern model term and reads
variables, so `W2`'s placement at it is `PlacedS`).

- `hello1_hWBot`: `hello1_hbot`'s premise `hW`;
- `hello1_hbotW`: `H1RestXW.hbot`'s statement at `BotHR` with no premise;
- `hello1_restX_ofHbotW`: `H1RestXW` at `BotH` with `hbot` by `hello1_hbotW`;
- `hello1_restXT_ofHbotW`: the same for `H1RestXWT`.
-/
import Spike.Test.X64Hello1HBot
import Spike.Lib.LowerX64.SetupBotPop
import Spike.Lib.LowerX64.PlacedRetFr
import Spike.Lib.LowerX64.W2Pop
import Spike.Lib.LowerX64.PostSOf
import Spike.Lib.LowerX64.SetupHCall
import Spike.Lib.LowerX64.H1InLandWT

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

/-- The setup call's continuation's term: `main`'s argument pair, then `main`. -/
private theorem setupRestTerm_ext :
    ¬ ((Expr.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")) ∈ externModelTerms ∨
      exprFv (Expr.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))) = [])) := by
  simp [externModelTerms, modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody, Scc.Frontend.printAdv,
    Scc.Frontend.printNext, exprFv, opVars, atVars]
  exact ⟨.var "r", by simp [opAts]⟩

/-- **`hello1_hbot`'s premise `hW`**: at a `BotHR` key's return exit, `W2`
at the key's frames (`setupBot_popM`, `h0L_ofPreUL`'s invariant at the
popped pair, `w2_ofPopped`). -/
theorem hello1_hWBot {E : Entry} :
    ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSX h E (WNF) (ElR) (fun _ => True) (ab2 P1 (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHR h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1 (LU) (Ly).exe (Ly).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2R J (LU) (LN)) s c fs := by
  intro J _ L ls l b n hR hl hAL k fs hB c0 ty _ hd s c hE
  rcases hE with ⟨-, c0', hr, hA⟩ | hE
  case inr => exact hE.elim
  obtain ⟨⟨J0, L', D1, fS, v, D2, lS, lM, nS, fM, nM, hBd, hSB⟩, d', hd', hn⟩ := hB
  obtain ⟨d, hd, rfl⟩ := hd
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  rw [Spike.Lib.LowerNode.rodata_retTy_compiled2 hello1o_accepted2 hello1_hty.choose_spec hd hn] at hA
  have hR' := Reach.step hR hl hAL
  have hsw : Spike.Lib.LowerNode.setupWords2 P1 < 6 := by decide
  have hZ := Spike.Lib.LowerX64.setupMC_Z _ hsw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hD10, -, -, -, -, hL1, -⟩ := id hBd
  -- the pop to `mainS0` at the setup call's continuation
  obtain ⟨cE, fr, c'', rfl, hCT, -, hAt⟩ := setupBot_popM (PostS := SPostC P1 (LU) hello1_hty.choose _) hD10
    (by rw [hZ]; decide) (by simp only [Region.callee]; omega) (by simp only [Region.callee]; omega) hSB
    (hPS_framed (ty := hello1_hty.choose)) ⟨c0', hr, hA⟩
  -- `W2` at the popped pair: `h0`'s invariant at its pre
  have hcx : (fnCode2OfPMe hello1o_accepted2 h Le 1 Spike.Test.Hello1MainSrc.mainD
      Spike.Test.Hello1MainSrc.hello1_main_compiled2).lcx.externs = Scc.Frontend.externs P1 := by
    rw [(fnCode2OfPMe_spec hello1o_accepted2 h Le 1 Spike.Test.Hello1MainSrc.mainD
      Spike.Test.Hello1MainSrc.hello1_main_compiled2).1]
  obtain ⟨inv, hpre, hinvW, -⟩ := h0L_ofPreUL h hello1o_accepted2 hello1_hty.choose_spec
    Spike.Test.Hello1MainSrc.hello1_main_compiled2
    Spike.Test.Hello1MainSrc.hello1_main_find rfl (by decide) (by rw [hello1_hty_eq]; rfl)
    (by rw [hello1_hty_eq]; decide) (by decide) (Spike.Test.Hello1MainSrc.hello1_main_noCallee hcx)
    Spike.Test.Hello1MainSrc.hello1_main_noXchg Spike.Test.Hello1MainSrc.hello1_main_noNewBuf J hR' hBd
    (hello1_mainPreUTL h hBd J
      (Spike.Lib.lblRange_reach (Spike.Lib.X64.Rt.arOf_sub h) (fun _ => rfl) hR')
      (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (hello1_mainTg h))
    (Q := fun _ _ _ => False) v
  have hW2 := hinvW s c'' [] (hpre s c'' [] ⟨hAt, rfl⟩)
  -- the continuation's facts
  obtain ⟨-, -, -, -, σ', -, -, ⟨hPost, -⟩, -⟩ := hAt
  have hc0 := th02_term_setup hello1_hty.choose_spec
    (meW2 (lay2 Le P1) OX)
  obtain ⟨hCF, hMC⟩ := postS_setupTerm hc0 c'' _ hPost
  obtain ⟨cE', fr', cr, a', t', ws, hct', -, -, -, rfl⟩ := hPost
  obtain rfl := (CallTo.unique hCT hct').2
  -- the frame's body is the setup call's rest
  have hbody : fr.body = .let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")) := by
    obtain ⟨x, f, a, e, d0, t, ws0, ht, -, -, -, rfl⟩ := hCT
    rw [hc0] at ht
    simp only [Scc.Sem.SrcSem.setupTerm, Expr.let_.injEq] at ht
    exact ht.2.2.symm
  -- the `ret`'s exit by placements
  obtain ⟨-, -, -, -, σ, hAbs, -, ⟨⟨hJ, -⟩, -⟩, -⟩ := hA
  obtain ⟨a, -, -, -, -, -, ht, -⟩ := id hJ
  have hP : PlacedS (lay2 Le P1) (LU) s ⟨fr.body, (fr.x, fr.ty, ws) :: fr.env, none⟩ [] := by
    rcases hW2.place with hP | ⟨hx, -⟩
    · exact hP
    · exact absurd (hbody ▸ hx) setupRestTerm_ext
  exact w2_ofPopped (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hello1o_accepted2) hW2 hCF.noAlloc hMC.2
    (List.cons_ne_nil _ _) (frOk2_retFr ht hMC.1.1)
    (PlacedSE.of_placedS (placedS_retFr hJ hAbs.regs hP))

/-- **`hello1`'s `H1RestXW.hbot` at the bottom keys `BotHR`** with no
premise (`hello1_hbot` at `hello1_hWBot`). -/
theorem hello1_hbotW {E : Entry} :
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
          fun _ _ _ => False :=
  hello1_hbot h (hello1_hWBot h)

/-- **`H1RestXW` at `BotH` with `hbot` by `hello1_hbotW`** (`hello1_restX_ofHbot`
at `hello1_hWBot`). -/
theorem hello1_restX_ofHbotW {E : Entry}
    (H : H1RestXW h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True)) :
    H1RestXW h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True) :=
  hello1_restX_ofHbot h H (hello1_hWBot h)

/-- **`H1RestXWT` at `BotH` with `hbot` by `hello1_hbotW`**, at any
restriction `Tr` (the field `hello1_finalW_ofT`'s `HR` asks for). -/
theorem hello1_restXT_ofHbotW {E : Entry} {Tr : Nat → Expr → Prop}
    (H : H1RestXWT h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True)
      Tr) :
    H1RestXWT h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True) Tr :=
  { H with hbot := hello1_hbotW h }

end Hello1

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_hWBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hWBot

/-- info: 'Spike.Lib.LowerX64.hello1_hbotW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hbotW

/-- info: 'Spike.Lib.LowerX64.hello1_restX_ofHbotW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_restX_ofHbotW

/-- info: 'Spike.Lib.LowerX64.hello1_restXT_ofHbotW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_restXT_ofHbotW
