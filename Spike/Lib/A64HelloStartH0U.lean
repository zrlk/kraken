/-
**hello's start segment at the root's immediate table with the child's stack unmapped** (AArch64;
the twin of `A64WakeStartH0U`'s `hst0_ofU`): `StartH0R.hst0_ofH_iH` with its premise `hxa`
(the allocator's fresh-label landing in `ms [FR]`'s allocation fragment) replaced by `hRdU`, which is asked only
for a landing the arena hands out (`AllocLand`, derived here from `Ea`'s arithmetic at `arOf`) with the child's
stack `r1Of` unmapped (`KeepUn.U`).

The start segment `StartH0G.hello_start_wc_h0G` runs at `msUH`: the root's memory sides with the fragment `I`
asked only with `r1Of` unmapped (`invUH`); `KeepUnS.SegWS.mono_xa` moves it to `KeepUn.unXa (ms fs) r1Of`,
`KeepUnS.SegWS.keepUn` (the take of `rS0`, disjoint from `r1Of`, keeps it unmapped) back to the root's `ms`, the
entry's `U r1Of` discharged at the loaded thread (`wideSt_threadAt`, `WakeOHinit.unowned_stack`). The exits are
transported from `msUH` to `ms` (their facts do not read the allocation fragment) and closed by `hC`
(`StartH0C.hello_hab_closed`) and `RdHAb.hello_rd_hab_closed` (at `frM := FR`), as in `StartH0R.hst0_ofH_i0`.

Left as premises: those of `hst0_ofH_iH`, with `wc_main`'s source and frame premises `hrd`, `hq`, `hret`, `hPw`
at `msUH` (generic in `I`, so `hst0_ofH_iH`'s at `I := invUH I`; wake's `hWp`/`hWs` at `msU` likewise), and `hRdU`
(from `h1`'s statement at the frame `[FR]`) in place of `hxa`.

- `invUH`, `msUH`: the fragment asked only with `r1Of` unmapped, the memory sides at it.
- `hst0_ofHU_i0`: the statement, at `C0S.immsH Λ0 i0` for any certificate table `i0` (`hst0_ofH_i0`'s);
  `hst0_ofHU`: at `i0 := helloImms` (`ImmsH.iH`).

Superseded: level 0 ends at rodata's landing, so the root uses
`StartH0U0.hst0_ofHU0_i0` (no `hret`, `hPw`, `hhabctl`; those move to level 1's segment from rodata's landing).
This file is kept frozen.
-/
import Spike.Lib.A64HelloStartH0R
import Spike.Lib.A64KeepUnS
import Spike.Lib.WakeOHinit
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.A64WakeHClW
import Spike.Lib.Rt.A64RtTi2
import Spike.Lib.LowerA64.ArCallMs
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.StartH0U

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.A64.Flow (swR At enter leave)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 mNC aR mWC)
open Spike.Lib.A64.Flow.HelloRd (rN rX pN RdPreW)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.KeepUn (U unXa)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.A64.HelloPh.HabCtl (HabCtlH)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib (FragS Frag SegWS LocalRun)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (`C0S.immsH Λ0 i0`; `ImmsH.iH` at
`i0 := helloImms`, `ImmsRd.iRd` at `i0 := i0Rd`; wake's `WakeFinalCAW.iW`). -/
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
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

/-- **The fragment `I` asked only with the child's stack unmapped** (wake's `StartH0U.invU`). -/
abbrev invUH (I : Spike.Lib.A64ConsumerS.InvS) : Spike.Lib.A64ConsumerS.InvS := fun lbl lsize s c fs =>
  U R1 s → I lbl lsize s c fs

/-- **The root's memory sides at `invUH I`** (wake's `StartH0U.msU`). -/
noncomputable abbrev msUH (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.A64ConsumerS.InvS) (ls : Lsize)
    (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  Spike.Lib.A64ConsumerA.msOfA (Ly).Λ ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ)
    rd (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
    (AR) (invUH hpw i0 I) (LB) (ls0T ls) fs

set_option hygiene false in
/-- The root's memory sides at the frames `fs`, the entry's marks. -/
local notation "MSF" => fun fs : List TermRun.Frame => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
  (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH)) (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
  (AR) I (LB) (ls0T ls) fs

set_option hygiene false in
/-- The root's memory sides at `invUH I`. -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
/-- The start's level at the root's choices. -/
local notation "WP" => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

set_option hygiene false in
local notation "KR" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option hygiene false in
local notation "JW" => JS (Ly) 0#64 c0S

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JW)


/-- **hello's start segment at `iH`, the child's stack unmapped** (`hst0_ofH_iH` with `hxa` from `hRdU`): the
start segment at `msUH`, `keepUn` carrying `r1Of` unmapped, the exits transported to `ms` and closed by `hC`
(`hello_hab_closed`) and `hello_rd_hab_closed`; `hxa` at `msUH` from `Ea`'s `AllocLand` and `hRdU` (module doc). -/
theorem hst0_ofHU_i0 (E : Entry) (hE : E.Ok (Ly).Λ)
    {Ctx : FragS isaLSE2} {ls0 : Lsize}
    {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) (mNC (Ly).lab (JW))
      s c → WP s c [])
    (hrd : ∀ v m0 σC, RdPreW (fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc (mR (swR v (-helloLsw) 0))
      (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC) ((MSU) [FR]) (mRdJ0 (J') σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 (J') σC σ c → ∃ c', LocalRun helloSrc c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSU) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSU) [FR]) = 3#64)
    {t : UInt64} {Jp Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 : BitVec 64 → MachineData → FAS → FAS → Ctl → Prop}
    /- open premise: a landing the arena hands out, the child's stack unmapped,
    is in `I` at the fresh label -/
    (hRdU : ∀ v m0 σC, ∀ q : AG ((MSU) [FR]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-helloLsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mRdJ0 (J') σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N (Ly).lab ((MSU) [FR]) q.1 .e).J (enter (-48) σ) c ∧
        Spike.Lib.A64.Flow.CKept (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, (LB) l = none →
        At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0))) F' (Ea ((MSU) [FR]) q.1 l b w) s c →
        AllocLand (AR).heap (AR).cells b w → U R1 s →
        I (fun l' => if l' = l then some b else (LB) l') (fun l' => if l' = l then w else ls0T ls l') s c [FR])
    (hret : ∀ v m0 σC σ c, (rX ((MSU) [FR]) (Ly).lab (LB) (J1 σC) .sp0).J σ c → Jp v m0 σC σ c)
    (hPw : ∀ v m0 σC, MainWcPS (WP) KR helloSrc (LB) (MSU) (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) helloD
      (FS (Ly) RS helloLsw 0#64 v) (FR) m0 σC (Jp v m0 σC) (Jp' v m0 σC) (Jx1 v m0 σC) (J2 v m0 σC) (J2' v m0 σC)
      (J3 v m0 σC) (J4 v m0 σC) (J5 v m0 σC) (Jr v m0 σC) (Jr1 v m0 σC) t)
    /- named premise -/
    (hhabctl : ∀ v m0 σC σ1, HabCtlH ((MSF) []) (Ly).lab helloSrc (Ly).Λ (LB) (AR) []
      (wcJ0 (mWC (Ly).lab σC (Jr1 v m0 σC)).J σ1))
    /- named premise (`HabCtlRdH`): the controls' facts at `rX .abort` -/
    (hhabctlRd : ∀ σC, Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH ((MSF) [FR]) (Ly).lab helloSrc (Ly).Λ (LB) (AR)
      [FR] (J1 σC)) :
    SegWS (W0H (asm := asm) hpw IH E DtW Ctx (ls0T ls0) (FR)) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH
        (Ly))) helloSrc (LB)
      (MSF) (StartPH hpw IH E) (fun _ _ _ => False) := by
  -- the ranges: `r1Of` in the pool, disjoint from `rS0`, both in the address space
  have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hpw IH hA13
  have hbd' : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by
    rw [(Ly).lab_stacks]; exact Spike.Lib.WakeHClW.hbd_W hpw IH hsub1
  obtain ⟨h1l, h1s⟩ := Spike.Lib.A64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS).size = 16384 := rfl
  have hst := (Ly).stacks_sub
  have hpf := (Ly).pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS).lo + (RS).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS) := by unfold Scc.Sem.Range.Disjoint; omega
  -- `hxa` at `msUH`: the landing is one the arena hands out (`Ea` at `arOf`), the rest `hRdU` given `U r1Of`
  have hxa : ∀ v m0 σC, ∀ q : AG ((MSU) [FR]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-helloLsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mRdJ0 (J') σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N (Ly).lab ((MSU) [FR]) q.1 .e).J (enter (-48) σ) c ∧
        Spike.Lib.A64.Flow.CKept (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, (LB) l = none →
        At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0))) F' (Ea ((MSU) [FR]) q.1 l b w) s c →
        ((MSU) [FR]).xa l b w s c := by
    intro v m0 σC q F' hF1 hF2 l b w s c hl hA
    have hAL : AllocLand (AR).heap (AR).cells b w := by
      obtain ⟨-, -, -, -, -, -, -, -, old, -, -, hb, hold, -, -, -, us, hus, hw⟩ := id hA
      have hf : ((MSU) [FR]).off q.1.n q.1.τ = 8 := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) q.2.accs
      have hcl : ((MSU) [FR]).cells = 4194304 := rfl
      have hu : ((MSU) [FR]).units q.1.n q.1.τ = q.1.n * TermRun.nWords us + 1 :=
        Spike.Lib.Arena.ofWords_units_fit (heap := (Ly).Λ.heap.lo) (cells := Scc.Cert.PlaceOK.allocCells)
          (ctr := Scc.Cert.PlaceOK.heapUseOf (Ly).Λ) (m := fun _ => 0) (by decide) hus
          (Nat.le_trans (Nat.le_add_left _ old) hold)
      show ((MSU) [FR]).heap + 8 ≤ b ∧ b + 8 * w ≤ ((MSU) [FR]).heap + 16 * ((MSU) [FR]).cells ∧
        w + 1 ≤ ((MSU) [FR]).cells
      rw [hf] at hb; rw [hu, hcl] at hold; rw [hcl]; subst hw
      omega
    exact ⟨hAL, fun hU => hRdU v m0 σC q F' hF1 hF2 l b w s c hl hA hAL hU⟩
  -- the start segment at `msUH`, then at `unXa (ms fs) r1Of`, then `keepUn`
  have hG0 := Spike.Lib.A64.HelloPh.StartH0G.hello_start_wc_h0G hpw IH (I := invUH hpw i0 I) (rd := rd) (ls := ls)
    hE hpa hhp hlo0 hstat hA13 hctr2 hc (Spike.Lib.A64.HelloPh.C0S.immsH_start Λ0 _) hWe hrd hloc hq hxa
    hret hPw
  have hG1 := Spike.Lib.A64.KeepUnS.SegWS.mono_xa (ms' := fun fs => unXa ((MSF) fs) R1) hG0 (fun _ => rfl)
    fun _ _ _ _ _ _ h hU => ⟨h.1, h.2 hU⟩
  have hG := Spike.Lib.A64.KeepUnS.SegWS.keepUn (fun _ => rfl) hG1 fun _ _ _ _ s' hk hs => by
    obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.A64.KeepUn.take_un pm hd hw1 hwS hs
  -- the exits at `ms`, closed; the take as `TakeCKS`; `WS` as `W0H`; the start pair as `hG`'s entry
  have hprog : (Ly).prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hpL : textProgram asm = .ok (Ly).prog := by rw [hprog]; exact hhp
  have hC := (Spike.Lib.A64.HelloPh.StartH0C.hello_hab_closed hpw IH (Ctx := Ctx) (ls0 := ls0) (frM := FR)
    (t := t) hpa hhp hlo0 hhabctl).or_pre
    (Spike.Lib.A64.HelloPh.RdHAb.hello_rd_hab_closed hpw IH (Ctx := Ctx) (ls0 := ls0) hpa hhp hlo0 hhabctlRd)
  refine ((((hG.mono_post fun s c fs hQ => ?_).seq hC).mono_K
      fun s c fs hW s' => Spike.Lib.A64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1).mono_W
    fun s c fs h => ?_).mono_pre fun s c fs ⟨hs, hc, hfs⟩ => ?_
  · obtain ⟨hQ, -⟩ := hQ
    rcases hQ with ⟨⟨v, m0, σC, m1, σ1, ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hX30, q, hq, hJ⟩, htp⟩, hfs⟩ |
      ⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hX30, q, hq, hJ⟩⟩, hfs⟩
    · exact .inl ⟨⟨v, m0, σC, m1, σ1,
        ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hX30, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, hq, hJ⟩, htp⟩, hfs⟩
    · exact .inr ⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hX30, ⟨q.1, { q.2 with }⟩, hq, hJ⟩⟩, hfs⟩
  · show Spike.Lib.A64.WakeWf.W0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ s c fs
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]; exact h
  · subst hs hc hfs
    exact ⟨⟨Spike.Lib.A64.HelloPh.StartH0B.entry_atH hpw IH E hE, rfl⟩,
      Scc.Cert.WideA64.wideSt_threadAt (PlaceW.wideIn_of_placeW hpw) E _ _,
      Spike.Lib.WakeOHinit.unowned_stack hpw IH hE.1 hsub1 hw1 _ rfl⟩

/-- **`hst0_ofHU_i0` at the certificate's table** (`i0 := helloImms`, the root's table `ImmsH.iH`). -/
theorem hst0_ofHU : type_of% (hst0_ofHU_i0 (asm := asm) hpw SccCode.helloImms) := hst0_ofHU_i0 (asm :=
    asm) hpw SccCode.helloImms

end Spike.Lib.A64.HelloPh.StartH0U

/-- info: 'Spike.Lib.A64.HelloPh.StartH0U.hst0_ofHU_i0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0U.hst0_ofHU_i0

/-- info: 'Spike.Lib.A64.HelloPh.StartH0U.hst0_ofHU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0U.hst0_ofHU
