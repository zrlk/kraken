/-
**hello's level 1 at the root's choices, its landings asked only with the child's stack unmapped** (AArch64):
`Level1I.hB_land`/`h1_level1` with `MainWcPS` (`hP`) at the fragment `invUH I` (`I` asked
only with `r1Of` unmapped, `StartH0U.invUH`), where its box landings `hxa` are `LandR1U.HLand2U`'s
(`MainWcL1X.hxa_L1`), the conclusion at the level's memory sides at `I` byte-identical to `Level1I`'s.

`hB_land` at `invUH I` is the landing segment under `msOfA … (invUH I)`; its landings give `I`'s at states with
`r1Of` unmapped, so `KeepUnS.SegWS.mono_xa` moves it to `KeepUn.unXa (msOfA … I) r1Of` and
`KeepUnS.SegWS.keepUn` (the take keeps `r1Of` unmapped at `X0WH` states, `LandR1U.takeU_X`) back to `msOfA … I`. The
entry's `U r1Of` is `RdLandH`'s own conjunct (`RootL1U.rdLand_U`), and `RdLandH`, `hmem0`, `hhabctl` do not read
the fragment (`rdLandH_invU`, `okb_xa`, `habCtlH_xa`): they are asked at `I`, as in `Level1I`. The heap abort
closes at `wXA` (`Level1HA.hB_landA`, row `5h-S-habctl-L1`): `hhabctl` is replaced by the certificate table's `z`
(`hz`).

- `okb_xa`, `habCtlH_xa`: a box call's premises and `HabCtlH` do not read the memory side's `xa`;
- `rdLandH_invU`: rodata's landing at `I` is one at `invUH I`;
- `hB_landU`: `hB_land` with `hP` at `invUH I`;
- `h1_level1U`: `h1_level1` with `hP` at `invUH I`.
-/
import Spike.Lib.A64HelloLevel1I
import Spike.Lib.A64HelloLandR1U
import Spike.Lib.A64KeepUnS
import Spike.Lib.A64HelloLevel1HA

namespace Spike.Lib.A64.HelloPh.Level1IU

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (abi textProgram)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib (FragS Frag MemSide SegWS)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Hello1 (mWC mRdJ0)
open Spike.Lib.A64.Flow.HelloM (wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.Flow.WakeWc (AGB)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.KeepUn (U unXa)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH invUH)
open Spike.Lib.A64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.A64.HelloPh.HabCtl (HabCtlH)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.A64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.A64.HelloPh.Level1I (W1R XR)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## Facts that do not read `xa` -/

/-- **A box call's premises do not read `xa`**. -/
theorem okb_xa {ms ms' : MemSide isaLSE2} (hms : ms' = { ms with xa := ms'.xa }) {lab : String → Int64}
    {q : Call} (h : q.OKB ms lab) : q.OKB ms' lab := by
  obtain ⟨X, rfl⟩ : ∃ X, ms' = { ms with xa := X } := ⟨_, hms⟩
  exact { h with toS := { h.toS with } }

/-- **`HabCtlH` does not read `xa`**: `wXH .abort`'s states under `ms'` are `ms`'s. -/
theorem habCtlH_xa {ms ms' : MemSide isaLSE2} (hms : ms' = { ms with xa := ms'.xa }) {lab : String → Int64}
    {p : Prog} {Λ : Scc.Sem.Layout} {L0 : Lbl} {ar : Spike.Lib.Arena} {fs : List TermRun.Frame}
    {J1 : FAS → Spike.Lib.Ctl → Prop} (h : HabCtlH ms lab p Λ L0 ar fs J1) : HabCtlH ms' lab p Λ L0 ar fs J1 := by
  obtain ⟨X, rfl⟩ : ∃ X, ms' = { ms with xa := X } := ⟨_, hms⟩
  rintro σ c0 ⟨h0, h30, q, hq, hJ⟩
  exact h σ c0 ⟨h0, h30, ⟨q.1, okb_xa (ms := { ms with xa := X }) (ms' := ms) rfl q.2⟩, hq, hJ⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.A64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The fragment `I` asked only with `r1Of` unmapped. -/
local notation "IU" => invUH hpw i0 I

set_option hygiene false in
/-- Level 0's memory sides at a fragment `J` (the landing's). -/
local notation "MSU" => fun (J : Spike.Lib.A64ConsumerS.InvS) => msUH (asm := asm) hpw i0 E rd J ls

set_option hygiene false in
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`. -/
local notation "MS1" => fun (J : Spike.Lib.A64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
    (AR) J (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) fs

/-! ## rodata's landing at `invUH I` -/

/-- **rodata's landing at `I` is one at `invUH I`** (`RdLandH` does not read the fragment). -/
theorem rdLandH_invU {J1 : FAS → FAS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat} {s : State}
    {c : Spike.Lib.Ctl} (h : RdLandH (asm := asm) hpw i0 E rd I ls J1 l b w s c) :
    RdLandH (asm := asm) hpw i0 E rd (IU) ls J1 l b w s c := by
  obtain ⟨v, m0, σC, q, F', h1, h2, h3, hu, ht⟩ := h
  exact ⟨v, m0, σC, ⟨q.1, { q.2 with }⟩, F', h1, h2, h3, hu, ht⟩

/-- **`invUH I` is not vacuous at level 1's entry**: at rodata's landing `r1Of` is unmapped (`RdLandH`'s own
conjunct, `RootL1U.rdLand_U`), so there `invUH I` is `I`. -/
example {J1 : FAS → FAS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat} {s : State}
    {c : Spike.Lib.Ctl} (h : RdLandH (asm := asm) hpw i0 E rd I ls J1 l b w s c) (L : Lbl) (S : Lsize)
    (fs : List TermRun.Frame) : U (R1) s ∧ ((IU) L S s c fs ↔ I L S s c fs) := by
  obtain ⟨-, -, -, -, -, -, -, -, hu, -⟩ := h
  exact ⟨hu, fun hi => hi hu, fun hi _ => hi⟩

/-! ## The landing segment -/

/-- **Level 1's landing segment with `hP` at `invUH I`** (module doc): `Level1I.hB_land` at `invUH I`, carried to
the level's memory sides at `I` with `r1Of` unmapped. -/
theorem hB_landU {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    /- the landing's caller holds main's TCB at its slot `-80` (`slot80_rdJ` at `J1 := mRdJ0 J'`) -/
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- `MainWcPS` at the level at `invUH I` -/
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (W1R (asm := asm) hpw i0 E rd ls l b n) (KR) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
        ((MS1) (IU) l b n)
        (Ly).exe (Ly).endPc (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
        (JpT (JpL (R := swR (TOP) (-helloLsw) 0) ((MSU) (IU) [FR]) (Ly).lab (mRdJ0 (J') σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J5 Jr (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    /- the box allocation's words free at `FS` (`Level1M.hmem0_level1`) -/
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1) I l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1) I l b n []).ctr ∨ ∃ o, o + ((MS1) I l b n []).units q.n q.τ ≤
        ((MS1) I l b n []).cells ∧ a.toNat = q.hdrAt ((MS1) I l b n []) o) →
      ∀ m, FS (Ly) (RS) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none)
    /- the certificate table's `z` at `newTerm` (`Level1HA.hB_landA`'s; at the root `HabCtlA.hz_i0M`) -/
    (hz : i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0) :
    ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      SegWS (fun s c fs => W1R (asm := asm) hpw i0 E rd ls l b n s c fs ∧ XR hpw i0 l b n s c fs)
        (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
        ((MS1) I l b n) (Frag.at (RdLandH (asm := asm) hpw i0 E rd I ls J1 l b n) [FR]) (fun _ _ _ => False) := by
  intro l b n hl hb
  have h := Spike.Lib.A64.HelloPh.Level1HA.hB_landA hpw i0 E rd (IU) ls hpa hhp hlo0 hz hJ1 hP
    (fun l b n q hq => hmem0 l b n q (okb_xa rfl hq)) l b n hl hb
  have hX := Spike.Lib.A64.KeepUnS.SegWS.mono_xa (ms' := fun fs => unXa ((MS1) I l b n fs) (R1)) h
    (fun _ => rfl) fun _ _ _ _ _ _ hx hu => ⟨hx.1, hx.2 hu⟩
  have hU := Spike.Lib.A64.KeepUnS.SegWS.keepUn (fun _ => rfl) hX
    fun s _ _ hW s' hk hu => Spike.Lib.A64.HelloPh.LandR1U.takeU_X hpw i0 hA13 s s' hW.2 hk hu
  refine SegWS.mono_post (SegWS.mono_pre hU fun s c fs ⟨hR, hfs⟩ =>
    ⟨⟨rdLandH_invU hpw i0 E rd I ls hR, hfs⟩, ?_⟩) fun _ _ _ h => h.1
  obtain ⟨-, -, -, -, -, -, -, -, hu, -⟩ := hR
  exact hu

/-- **The root's `h1` with `hP` at `invUH I`** (`Level1I.h1_level1`'s statement; module doc). -/
theorem h1_level1U {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (W1R (asm := asm) hpw i0 E rd ls l b n) (KR) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
        ((MS1) (IU) l b n)
        (Ly).exe (Ly).endPc (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
        (JpT (JpL (R := swR (TOP) (-helloLsw) 0) ((MSU) (IU) [FR]) (Ly).lab (mRdJ0 (J') σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J5 Jr (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1) I l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1) I l b n []).ctr ∨ ∃ o, o + ((MS1) I l b n []).units q.n q.τ ≤
        ((MS1) I l b n []).cells ∧ a.toNat = q.hdrAt ((MS1) I l b n []) o) →
      ∀ m, FS (Ly) (RS) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none)
    (hz : i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0) :
    Spike.Lib.HelloPreA.H1StmtHF (W1R (asm := asm) hpw i0 E rd ls) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly)))
      (AR) (LB)
      ((MS1) I) (Ly) (RdLandH (asm := asm) hpw i0 E rd I ls J1)
      (Spike.Lib.HelloPreA.H1Gfp.inv1G (W1R (asm := asm) hpw i0 E rd ls) (XR hpw i0)
        (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) (LB) ((MS1) I)) [FR] :=
  Spike.Lib.HelloPreA.H1Gfp.h1StmtHF_of_segWS (fun _ _ _ _ _ _ h => h.1)
    (hB_landU hpw i0 E rd I ls hpa hhp hlo0 hA13 hJ1 hP hmem0 hz)

/-- **`h1_level1U`'s conclusion is `h1_level1`'s** (ascription at `Level1I.h1_level1`'s type, its `hP` at `I` a
binder `hP0` and its `hhabctl` a binder, both read only by `type_of%`). -/
example {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (W1R (asm := asm) hpw i0 E rd ls l b n) (KR) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
        ((MS1) (IU) l b n)
        (Ly).exe (Ly).endPc (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
        (JpT (JpL (R := swR (TOP) (-helloLsw) 0) ((MSU) (IU) [FR]) (Ly).lab (mRdJ0 (J') σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J5 Jr (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1) I l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1) I l b n []).ctr ∨ ∃ o, o + ((MS1) I l b n []).units q.n q.τ ≤
        ((MS1) I l b n []).cells ∧ a.toNat = q.hdrAt ((MS1) I l b n []) o) →
      ∀ m, FS (Ly) (RS) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none)
    (hhabctl : ∀ l b n (σC σ1 : FAS), HabCtlH ((MS1) I l b n []) (Ly).lab helloSrc (Ly).Λ
      (Spike.Lib.A64ConsumerA.upd (LB) l b) (AR) []
      (wcJ0 (mWC (Ly).lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1))
    (hP0 : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (W1R (asm := asm) hpw i0 E rd ls l b n) (KR) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
        ((MS1) I l b n)
        (Ly).exe (Ly).endPc (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
        (JpT (JpL (R := swR (TOP) (-helloLsw) 0) ((MSU) I [FR]) (Ly).lab (mRdJ0 (J') σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J5 Jr (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    (hz : i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0)
    : type_of% (Spike.Lib.A64.HelloPh.Level1I.h1_level1 hpw i0 E rd I ls hpa hhp hlo0 hJ1 hP0 hmem0 hhabctl) :=
  h1_level1U hpw i0 E rd I ls hpa hhp hlo0 hA13 hJ1 hP hmem0 hz

end Spike.Lib.A64.HelloPh.Level1IU

/-- info: 'Spike.Lib.A64.HelloPh.Level1IU.okb_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1IU.okb_xa

/-- info: 'Spike.Lib.A64.HelloPh.Level1IU.habCtlH_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1IU.habCtlH_xa

/-- info: 'Spike.Lib.A64.HelloPh.Level1IU.rdLandH_invU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1IU.rdLandH_invU

/-- info: 'Spike.Lib.A64.HelloPh.Level1IU.hB_landU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1IU.hB_landU

/-- info: 'Spike.Lib.A64.HelloPh.Level1IU.h1_level1U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1IU.h1_level1U
