/-
**hello's level 1 at the root's choices, its landings asked only with the child's stack unmapped** (x86-64; the
twin of `Spike/Lib/A64HelloLevel1IU.lean`): `Level1HA.hB_landAg` with `MainWcPS` (`hP`) at the
fragment `invUH I` (`I` asked only with `r1Of` unmapped, `StartH0U.invUH`), where its box landings `hxa` are
`LandR1U.HLand2U`'s (`MainWcL1X.hxa_L1`), the conclusion at the level's memory sides at `I`.

`hB_landAg` at `invUH I` is the landing segment under `msOfA … (invUH I)`; its landings give `I`'s at states with
`r1Of` unmapped, so `SegWSP.mono_xa` moves it to `KeepUn.unXa (msOfA … I) r1Of` and `SegWSP.keepUn` (the take
keeps `r1Of` unmapped at `X0WH` states, `LandR1U.takeU_X`) back to `msOfA … I`. The entry's `U r1Of` is
`RdLandHg`'s own conjunct, and `RdLandHg` and `hmem0` do not read the fragment (`rdLandHg_xa`, `okb_xa`):
they are asked at `I`.

- `okb_xa`: a box call's premises do not read the memory side's `xa`;
- `rdLandHg_xa`: `StartH0H1.RdLandHg own` does not read the fragment;
- `hB_landUg`: `hB_landAg` with `hP` at `invUH I`, at the level's memory sides at `I`, at any owned words `own`
  (its stub path `hP0` a premise);
- `h1_level1Ug`: the root's `h1` (`H1StmtHF` at `inv1G`) from it, at any owned words `own`.

## Differences from the AArch64 version

- The segments are `SegWSP` (the source's publication is a stutter before `wc_rodata`'s last block,
  `X64SegWPub`): `SegWSP.mono_xa`, `SegWSP.keepUn` (`X64KeepUnSP`) and `H1Gfp.h1StmtHF_of_segWSP` (AArch64:
  `KeepUnS.SegWS.mono_xa`, `SegWS.keepUn`, `h1StmtHF_of_segWS`).
- `LandR1U.takeU_X` takes no `a13data` premise (the stacks' bound is `X64WakeHClC.hbd_W`), so there is no `hA13`.
- `MainWcPS` has the last block's controls past the publication `J4x` (`hP`'s existential; AArch64 has the fence
  node's invariant instead). The region is `RS helloLsw TOP` and the caller's TCB slot `-16`, the thread pointer
  `tpOf (tcbS Ly)` (AArch64 `swR TOP (-helloLsw) 0`, `-80`, `pinA + 8`), as in `Level1HA.hB_landAg`.
- `rdLandH_invU` is `rdLandHg_xa` (any two fragments). `habCtlH_xa` is not twinned:
  `hB_landAg` asks no `HabCtlH` (the abort's controls come from the certificate table's `z`, `hz`), so it is dead.
  The closing `example` against `Level1I.h1_level1` is not repeated: `h1_level1` has no x86-64 version (dead).
- `hB_landUg`, `h1_level1Ug`, `rdLandHg_xa` are generic in the owned words (AArch64's are at `ownGH` only), so
  that `ownGHXW`, which carries main's and the worker's TCB words, shares them; `hB_landUg` takes `hB_landAg`'s
  stub path `hP0` (AArch64 discharges it at `ownGH` inside `hB_landA`).
-/
import Spike.Lib.X64HelloLevel1HA
import Spike.Lib.X64HelloLandR1U
import Spike.Lib.X64HelloRootL1F
import Spike.Lib.X64HelloStartH0U
import Spike.Lib.X64KeepUnSP
import Spike.Lib.X64HelloH1Gfp

namespace Spike.Lib.X64.HelloPh.Level1IU

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Scc.Sem.X64 (cellsOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib (FragS Frag MemSide PlaceWX)
open Spike.Lib.X64SegWPub (SegWSP)
open Spike.Lib.X64.Flow.Hello1 (mRdJ0)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH invUH)
open Spike.Lib.X64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.X64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.X64.HelloPh.Level1I (XR)
open Spike.Lib.X64.Flow.HelloM (wcR)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloMainPreSrc (newTerm)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## Facts that do not read `xa` -/

/-- **A box call's premises do not read `xa`**. -/
theorem okb_xa {ms ms' : MemSide isa} (hms : ms' = { ms with xa := ms'.xa }) {lab : String → Int64}
    {q : Call} (h : q.OKB ms lab) : q.OKB ms' lab := by
  obtain ⟨X, rfl⟩ : ∃ X, ms' = { ms with xa := X } := ⟨_, hms⟩
  exact { h with toS := { h.toS with } }

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `wc_rodata`'s entry invariant at the first stack's top. -/
local notation "J'" => rdJH (Ly).lab (RS helloLsw (TOP)) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The fragment `I` asked only with `r1Of` unmapped. -/
local notation "IU" => invUH hpw i0 I

set_option hygiene false in
/-- Level 0's memory sides at a fragment `J` (the landing's). -/
local notation "MSU" => fun (J : Spike.Lib.X64ConsumerS.InvS) => msUH (asm := asm) hpw i0 E rd J ls

set_option hygiene false in
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`. -/
local notation "MS1" => fun (J : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s)
    (AR) J (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
/-- Level 0's memory sides at a fragment `J` at the owned words `own`. -/
local notation "MSUg" => fun (own : Spike.Lib.X64Consumer.Own) (J : Spike.Lib.X64ConsumerS.InvS) =>
  Spike.Lib.X64.HelloPh.StartH0U.msUHg (asm := asm) hpw i0 own E rd J ls

set_option hygiene false in
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`, at the
owned words `own`. -/
local notation "MS1g" => fun (own : Spike.Lib.X64Consumer.Own) (J : Spike.Lib.X64ConsumerS.InvS)
    (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => own s)
    (AR) J (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

/-- **`RdLandHg own` does not read the fragment** (AArch64 `RootL1F.rdLandH_xa` at any owned words). -/
theorem rdLandHg_xa {own : Spike.Lib.X64Consumer.Own} {I' : Spike.Lib.X64ConsumerS.InvS}
    {J1 : FAS → FAS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : Spike.Lib.X64.HelloPh.StartH0H1.RdLandHg (asm := asm) hpw i0 own E rd I ls J1 l b w s c) :
    Spike.Lib.X64.HelloPh.StartH0H1.RdLandHg (asm := asm) hpw i0 own E rd I' ls J1 l b w s c := by
  obtain ⟨v, m0, σC, q, F', h1, h2, h3, hu, ht⟩ := h
  exact ⟨v, m0, σC, ⟨q.1, { q.2 with }⟩, F', h1, h2, h3, hu, ht⟩

/-- **`invUH I` is not vacuous at level 1's entry**: at rodata's landing `r1Of` is unmapped (`RdLandHg`'s own
conjunct), so there `invUH I` is `I`. -/
example {own : Spike.Lib.X64Consumer.Own} {J1 : FAS → FAS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel}
    {b w : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : Spike.Lib.X64.HelloPh.StartH0H1.RdLandHg (asm := asm) hpw i0 own E rd I ls J1 l b w s c) (L : Lbl) (S : Lsize)
    (fs : List TermRun.Frame) : U (R1) s ∧ ((IU) L S s c fs ↔ I L S s c fs) := by
  obtain ⟨-, -, -, -, -, -, -, -, hu, -⟩ := h
  exact ⟨hu, fun hi => hi hu, fun hi _ => hi⟩

/-! ## The landing segment -/

/-- **Level 1's landing segment with `hP` at `invUH I`, at the owned words `own`** (AArch64's
landing segment at any `own`): `Level1HA.hB_landAg` at `invUH I`, carried to the level's memory sides at `I` with
`r1Of` unmapped; the stub's path inside the level `hP0` (`hB_landAg`'s) is a premise. -/
theorem hB_landUg {own : Spike.Lib.X64Consumer.Own} {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo)
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hpw i0 E rd ls own l b n) (KR) helloSrc
        (Spike.Lib.X64ConsumerA.upd (LB) l b)
        ((MS1g) own (IU) l b n) (Ly).exe (Ly).endPc (RS helloLsw (TOP)) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP))
        (FR) m0 σC
        (JpT (JpL (R := RS helloLsw (TOP)) ((MSUg) own (IU) [FR]) (Ly).lab (mRdJ0 (J') σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1g) own I l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1g) own I l b n []).ctr ∨ ∃ o, o + ((MS1g) own I l b n []).units q.n q.τ ≤
        ((MS1g) own I l b n []).cells ∧ a.toNat = q.hdrAt ((MS1g) own I l b n []) o) →
      ∀ m, FS (Ly) (RS0) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none)
    (hz : i0 newTerm "z" 0 = some 0)
    (hP0 : ∀ l b n (F' : MachineData → Prop) (c0 : Spike.Lib.Ctl),
      FStable ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16) F' →
      (([] : List TermRun.Frame) = [] → ∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c0 [] →
      (∀ s : State, F' s.st.1 →
        Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) s c0 []) →
      Spike.Lib.HeapAbortOblA (AR).cells (AR).ctr c0 →
      Abort.Disp.HPathW (fun s c => Spike.Lib.X64.HelloPh.StartWcS.WSg own (Ly) (AR) helloSrc DtW
          (Spike.Lib.X64.HelloPh.ClH (Ly)) (Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls l b n)
          (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) (FR) (X0WH (Ly) (AX))
          s c []) (fun _ _ => False) (Ly).exe
        (Ly).endPc ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16) F' c0
        ((Ly).lab ".Lscc_rt_alloc.full" + 12).toBitVec) :
    ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      SegWSP (fun s c fs => Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hpw i0 E rd ls own l b n s c fs ∧
          XR hpw i0 l b n s c fs)
        (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
        ((MS1g) own I l b n)
        (Frag.at (Spike.Lib.X64.HelloPh.StartH0H1.RdLandHg (asm := asm) hpw i0 own E rd I ls J1 l b n) [FR])
        (fun _ _ _ => False) := by
  intro l b n hl hb
  have h := Spike.Lib.X64.HelloPh.Level1HA.hB_landAg hpw i0 E rd (IU) ls hpa hhp hlo0 hz hJ1 hP
    (fun l b n q hq => hmem0 l b n q (okb_xa rfl hq)) hP0 l b n hl hb
  have hX := SegWSP.mono_xa (ms' := fun fs => unXa ((MS1g) own I l b n fs) (R1)) h
    (fun _ => rfl) fun _ _ _ _ _ _ hx hu => ⟨hx.1, hx.2 hu⟩
  have hU := SegWSP.keepUn (fun _ => rfl) hX
    fun s _ _ hW s' hk hu => Spike.Lib.X64.HelloPh.LandR1U.takeU_X hpw i0 s s' hW.2 hk hu
  refine SegWSP.mono_post (SegWSP.mono_pre hU fun s c fs ⟨hR, hfs⟩ =>
    ⟨⟨rdLandHg_xa hpw i0 E rd I ls hR, hfs⟩, ?_⟩) fun _ _ _ h => h.1
  obtain ⟨-, -, -, -, -, -, -, -, hu, -⟩ := hR
  exact hu

/-- **The root's `h1` with `hP` at `invUH I`, at the owned words `own`** (AArch64's `h1`
at any `own`, from `hB_landUg`). -/
theorem h1_level1Ug {own : Spike.Lib.X64Consumer.Own} {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo)
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hpw i0 E rd ls own l b n) (KR) helloSrc
        (Spike.Lib.X64ConsumerA.upd (LB) l b)
        ((MS1g) own (IU) l b n) (Ly).exe (Ly).endPc (RS helloLsw (TOP)) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP))
        (FR) m0 σC
        (JpT (JpL (R := RS helloLsw (TOP)) ((MSUg) own (IU) [FR]) (Ly).lab (mRdJ0 (J') σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1g) own I l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1g) own I l b n []).ctr ∨ ∃ o, o + ((MS1g) own I l b n []).units q.n q.τ ≤
        ((MS1g) own I l b n []).cells ∧ a.toNat = q.hdrAt ((MS1g) own I l b n []) o) →
      ∀ m, FS (Ly) (RS0) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none)
    (hz : i0 newTerm "z" 0 = some 0)
    (hP0 : ∀ l b n (F' : MachineData → Prop) (c0 : Spike.Lib.Ctl),
      FStable ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16) F' →
      (([] : List TermRun.Frame) = [] → ∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c0 [] →
      (∀ s : State, F' s.st.1 →
        Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) s c0 []) →
      Spike.Lib.HeapAbortOblA (AR).cells (AR).ctr c0 →
      Abort.Disp.HPathW (fun s c => Spike.Lib.X64.HelloPh.StartWcS.WSg own (Ly) (AR) helloSrc DtW
          (Spike.Lib.X64.HelloPh.ClH (Ly)) (Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls l b n)
          (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) (FR) (X0WH (Ly) (AX))
          s c []) (fun _ _ => False) (Ly).exe
        (Ly).endPc ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16) F' c0
        ((Ly).lab ".Lscc_rt_alloc.full" + 12).toBitVec) :
    Spike.Lib.X64HelloPreA.H1StmtHF (Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hpw i0 E rd ls own)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (AR) (LB)
      ((MS1g) own I) (Ly) (Spike.Lib.X64.HelloPh.StartH0H1.RdLandHg (asm := asm) hpw i0 own E rd I ls J1)
      (Spike.Lib.X64HelloPreA.H1Gfp.inv1G (Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hpw i0 E rd ls own)
        (XR hpw i0) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (LB) ((MS1g) own I)) [FR] :=
  Spike.Lib.X64HelloPreA.H1Gfp.h1StmtHF_of_segWSP (fun _ _ _ _ _ _ h => h.1)
    (hB_landUg hpw i0 E rd I ls hpa hhp hlo0 hJ1 hP hmem0 hz hP0)

end Spike.Lib.X64.HelloPh.Level1IU

/-- info: 'Spike.Lib.X64.HelloPh.Level1IU.okb_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1IU.okb_xa

/-- info: 'Spike.Lib.X64.HelloPh.Level1IU.rdLandHg_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1IU.rdLandHg_xa

/-- info: 'Spike.Lib.X64.HelloPh.Level1IU.hB_landUg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1IU.hB_landUg

/-- info: 'Spike.Lib.X64.HelloPh.Level1IU.h1_level1Ug' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1IU.h1_level1Ug
