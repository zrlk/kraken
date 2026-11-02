/-
**hello's start segment at the root's immediate table with the child's stack unmapped, level 0** (AArch64, the twin of
`A64HelloStartH0U`): `StartH0U.hst0_ofHU_i0`'s proof at
`StartH0G0.hello_start_rd_h0G0` (level 0 ends at rodata's landing: the only exit is `wc_rodata`'s heap abort,
closed by `RdHAb.hello_rd_hab_closed` at `frM := FR`). The start segment runs at `StartH0U.msUH` (the fragment
asked only with `r1Of` unmapped), `KeepUnS.SegWS.mono_xa`/`keepUn` carry it back to the root's `ms`, and `hxa` at
`msUH` comes from `Ea`'s `AllocLand` and `hRdU`, as there.

Left as premises: the loader's facts (`hpa`, `hhp`, `hlo0`, `hstat`, `hA13`, `hctr2`, `hc`), the source
and frame premises `hWe`, `hrd`, `hloc`, `hq` at `msUH`, `hhabctlRd`, and `hRdU` (level 1's
generic hand-off: from `h1`'s statement at the frame `[FR]`). `hret`, `hPw`, `hhabctl` are level 1's.

- `hst0_ofHU0_i0`: the statement (`hRdU` may assume `TP (pinA + 8)` at the landing, L1-TP),
  at `C0S.immsH Λ0 i0`; `hst0_ofHU0`: at `i0 := helloImms` (`ImmsH.iH`).
-/
import Spike.Lib.A64HelloStartH0U
import Spike.Lib.A64HelloStartH0R0
import Spike.Lib.A64KeepUnS
import Spike.Lib.WakeOHinit
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.A64WakeHClW
import Spike.Lib.Rt.A64RtTi2
import Spike.Lib.LowerA64.ArCallMs
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.StartH0U0

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
open Spike.Lib.A64.HelloPh.StartH0U (invUH msUH)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0B (StartPH W0H)
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


/-- **hello's start segment at `iH`, the child's stack unmapped, level 0** (`StartH0U.hst0_ofHU_i0`'s twin): the start
segment `StartH0G0.hello_start_rd_h0G0` at `msUH` (its only exit `wc_rodata`'s
heap abort), `keepUn` carrying `r1Of` unmapped, the exit transported to `ms` and closed by `hello_rd_hab_closed`;
`hxa` at `msUH` from `Ea`'s `AllocLand` and `hRdU` (module doc). -/
theorem hst0_ofHU0_i0 (E : Entry) (hE : E.Ok (Ly).Λ)
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
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.A64.Flow.WakeWc.tpG
        (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) fun s c => WP s c [FR]) KR (Ly).exe
      (Ly).endPc (mR (swR v (-helloLsw) 0))
      (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC) ((MSU) [FR]) (mRdJ0 (J') σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 (J') σC σ c → ∃ c', LocalRun helloSrc c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSU) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSU) [FR]) = 3#64)
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
        TP (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) s →
        I (fun l' => if l' = l then some b else (LB) l') (fun l' => if l' = l then w else ls0T ls l') s c [FR])
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
        TP (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) s → ((MSU) [FR]).xa l b w s c := by
    intro v m0 σC q F' hF1 hF2 l b w s c hl hA ht
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
    exact ⟨hAL, fun hU => hRdU v m0 σC q F' hF1 hF2 l b w s c hl hA hAL hU ht⟩
  -- the start segment at `msUH`, then at `unXa (ms fs) r1Of`, then `keepUn`
  have hG0 := Spike.Lib.A64.HelloPh.StartH0G0.hello_start_rd_h0G0 hpw IH (I := invUH hpw i0 I) (rd := rd)
    (ls := ls) hE hpa hhp hlo0 hstat hA13 hctr2 hc (Spike.Lib.A64.HelloPh.C0S.immsH_start Λ0 _) hWe hrd hloc
    hq hxa
  have hG1 := Spike.Lib.A64.KeepUnS.SegWS.mono_xa (ms' := fun fs => unXa ((MSF) fs) R1) hG0 (fun _ => rfl)
    fun _ _ _ _ _ _ h hU => ⟨h.1, h.2 hU⟩
  have hG := Spike.Lib.A64.KeepUnS.SegWS.keepUn (fun _ => rfl) hG1 fun _ _ _ _ s' hk hs => by
    obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.A64.KeepUn.take_un pm hd hw1 hwS hs
  -- the exits at `ms`, closed; the take as `TakeCKS`; `WS` as `W0H`; the start pair as `hG`'s entry
  have hprog : (Ly).prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hpL : textProgram asm = .ok (Ly).prog := by rw [hprog]; exact hhp
  have hC := Spike.Lib.A64.HelloPh.RdHAb.hello_rd_hab_closed hpw IH (Ctx := Ctx) (ls0 := ls0) hpa hhp hlo0
    hhabctlRd
  refine ((((hG.mono_post fun s c fs hQ => ?_).seq hC).mono_K
      fun s c fs hW s' => Spike.Lib.A64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1).mono_W
    fun s c fs h => ?_).mono_pre fun s c fs ⟨hs, hc, hfs⟩ => ?_
  · obtain ⟨hQ, -⟩ := hQ
    obtain ⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hX30, q, hq, hJ⟩, -⟩, hfs⟩ := hQ
    exact ⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hX30, ⟨q.1, { q.2 with }⟩, hq, hJ⟩⟩, hfs⟩
  · show Spike.Lib.A64.WakeWf.W0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ s c fs
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]; exact h
  · subst hs hc hfs
    exact ⟨⟨Spike.Lib.A64.HelloPh.StartH0B.entry_atH hpw IH E hE, rfl⟩,
      Scc.Cert.WideA64.wideSt_threadAt (PlaceW.wideIn_of_placeW hpw) E _ _,
      Spike.Lib.WakeOHinit.unowned_stack hpw IH hE.1 hsub1 hw1 _ rfl⟩

/-- **`hst0_ofHU0_i0` at the certificate's table** (`i0 := helloImms`, the root's table `ImmsH.iH`). -/
theorem hst0_ofHU0 : type_of% (hst0_ofHU0_i0 (asm := asm) hpw SccCode.helloImms) := hst0_ofHU0_i0 (asm :=
    asm) hpw SccCode.helloImms

end Spike.Lib.A64.HelloPh.StartH0U0

/-- info: 'Spike.Lib.A64.HelloPh.StartH0U0.hst0_ofHU0_i0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0U0.hst0_ofHU0_i0

/-- info: 'Spike.Lib.A64.HelloPh.StartH0U0.hst0_ofHU0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0U0.hst0_ofHU0
