/-
**`wc_rodata`'s level obligations at hello's root at `ownGHXW`** (x86-64 only; the `ownGHXW` instance of
`Spike/Lib/X64HelloHrdS.lean`'s `hrd_WSHF` and `Spike/Lib/X64HelloHrdRoot.lean`'s `hrd_R`, as `X64HelloRdWfSFX` is
`X64HelloRdWfSF`'s): the root's `hrd` inside the start's level `WSg (ownGHXW Ly ntA)` at the memory side
`StartH0U.msUHg (ownGHXW Ly ntA)` (`StartH0X.hst0_X`'s `hrd`).

`hrd_WSHX` is `HrdS.hrd_WSHF` through `RdWfSFX.rdPreW_WSHX`, with `ownGHXW`'s separation (`hsep`, `ha`, `hW`), the
band of `wc_rodata`'s region on the pool (`hb`) and the allocator's words off `tcbM` (`hnoM`). At the root
(`hrd_RX`) these are discharged from A13's data part: `hsep`, `ha` by `StartPlaceLy.wsep_W`, `hW` by
`tcbWH_notG_W`; `hb` from `scc_rt_main`'s region on the first stack (`bandRS`); `hnoM` from the counter's
separation from the runtime words (`ctrSep_of_rtWordsOk`) and the headers inside `.heap` (`ne_tcbM_of_heap`). The
arena's facts are `HrdArena`'s at `msUH`, carried over by `Call.OK`'s fields (none reads the owned words).

- `bandRS`: `scc_rt_main`'s region at the first stack's top lies on the pool in `[slo, 8]`, `8 - Lsw ≤ slo`.
- `hrd_WSHX`: `hrd_WSHF` inside `WSHFg (ownGHXW L a)`.
- `hrd_RX`: the root's `hrd` at `msUHg (ownGHXW Ly ntA)`, any context `Ctx`, given `hctx` under the thread pointer.
- `hrd_RXT`: `hrd_RX` with the allocator's caller's invariant at the first stack's top (`J1 := mRdJ0 (J' TOP)`,
  the shape `StartH0X.hst0_X` asks).
- `hrd_RdHX`: `hrd_RXT` at `LandRU.CtxRdHg (ownGHXW Ly ntA)` (`LandRU.hctx_rdRHg`), no context premise left.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against `X64HelloHrdS`/`X64HelloHrdRoot`: the level is
`WSg (ownGHXW Ly ntA)` and the memory side `msUHg (ownGHXW Ly ntA)`; the premises `hsep`, `ha`, `hW`, `hb`, `hnoM`
are new (discharged at the root); `hX0a` is restated at the new memory side (`HrdArena.hX0a_U`'s proof).
`hrd_RdH`'s twin `hrd_RdHX` is at `LandRU.CtxRdHg (ownGHXW Ly ntA)`, the context at the reference side `refHg` owning
`ownGHXW`.
-/
import Spike.Lib.X64HelloHrdRoot
import Spike.Lib.X64HelloRdWfSFX
import Spike.Lib.X64WakeStartPlaceLy
import Spike.Lib.X64HelloOwnSX
import Spike.Lib.X64WakeOwnBoxM

namespace Spike.Lib.X64.HelloPh.HrdRootX

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry ValRep)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (At swR)
open Spike.Lib.X64.HelloPh (lo ownGHXW ownH)
open Spike.Lib.X64.HelloPh.WcW (freeNH)
open Spike.Lib.X64.HelloWf (WSHFg)
open Spike.Lib.X64.Flow.HelloRd (RdPreW RdCtx)
open Spike.Lib.X64.Flow.Hello1 (mR mF mRdJ0 aR)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf stacksA)
open Spike.Lib.X64.Alloc (Call AllocW N)
open Spike.Lib.X64HelloRdCf (frH)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH WSg)
open Spike.Lib.X64.WakePh (tcbM BandOnP)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH msUHg)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib (Arena FragS Frag Region PlaceWX)

/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## The band -/

/-- **`scc_rt_main`'s region at the first stack's top lies on the pool in `[slo, 8]`**: its addresses are the
top less `8 - k`, inside the first stack (`RuntimeLayout.stacks_sub`), which lies in the pool. -/
theorem bandRS {L : RuntimeLayout} {Lsw slo : Int} (hk : 8 - Lsw ≤ slo) (hL : Lsw < 16384)
    (hok : (swR (topS L 0#64) (-Lsw) 0).OK) : BandOnP L (RS Lsw (topS L 0#64)) slo 8 := by
  intro k h1 h2
  have hR' : (⟨topS L 0#64, -Lsw, 1⟩ : Region).OK := ⟨hok.lo, by
    show ((topS L 0#64).toNat : Int) + 1 ≤ 2 ^ 64; have := (topS L 0#64).isLt; omega⟩
  have ha := Region.addr_toNat_of hR' (k := -8 - 0 + k) (by show -Lsw ≤ _; omega) (by show _ < (1 : Int); omega)
  have e : (RS Lsw (topS L 0#64)).addr k = Region.addr ⟨topS L 0#64, -Lsw, 1⟩ (-8 - 0 + k) := by
    rw [Region.callee_addr]; rfl
  have hf := L.pool_fit
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  simp only at hs1 hs2
  have ht : (topS L 0#64).toNat = L.stacksA.toNat + 16384 := by
    show (stacksA L.lab + 0#64 + 16384#64).toNat = _
    rw [L.lab_stacks, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  change (((Region.addr ⟨topS L 0#64, -Lsw, 1⟩ (-8 - 0 + k)).toNat : Nat) : Int) = (topS L 0#64).toNat + (-8 - 0 + k)
    at ha
  rw [e]
  omega

/-! ## `hrd` inside `WSHFg (ownGHXW L a)` -/

section Hello

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {X0 : State → Prop}
  (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-- **`wc_rodata` up to the allocator's return inside `WSHFg (ownGHXW L a)` at the setup call's frame**
(`HrdS.hrd_WSHF` through `RdWfSFX.rdPreW_WSHX`): `hrd_WSHF`'s premises, `ownGHXW`'s separation (`hsep`, `ha`, `hW`),
`wc_rodata`'s region's band on the pool (`hb`), the counter and headers off `tcbM` (`hnoM`). -/
theorem hrd_WSHX (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (hb : BandOnP L (mR R) (-208) 8)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa} {J : FAS → Ctl → Prop} {tp : UInt64}
    {w : Word} {env : Env} {m0 : MachineData} {σC : FAS}
    (hJ : ∀ σ c, J σ c → σ.regs.fsBase = tp ∧ ValRep lbl w.val σ.regs.rdi.toBitVec.toNat)
    (hme : ∀ ty ws, lookupE env "me" = some (ty, ws) → ws = [w])
    (hm : L.Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hnoM : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      w ≠ tcbM L)
    (hX0a : ∀ q : Call, q.OK ms L.lab → q.ra = (L.lab ".Lwc_rodata.x15").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (aR (mR R))
        (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 8 m ∧
          RdCtx ms L.lab (mR R) (mRdJ0 (rdJH L.lab R J) σC) (mRdJ0 (rdJH L.lab R J) σC) q m))
    (hctx : ∀ q : Call, q.OK ms L.lab → q.ra = (L.lab ".Lwc_rodata.x15").toBitVec →
      ∀ s c, At L.exe L.endPc (aR (mR R)) (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 8 m ∧
        RdCtx ms L.lab (mR R) (mRdJ0 (rdJH L.lab R J) σC) (mRdJ0 (rdJH L.lab R J) σC) q m)
        (N L.lab ms q .rmw) s c → Ctx s c [frH env])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    RdPreW (WSHFg (ownGHXW L a) L ar Spike.Lib.X64HelloSrc.helloSrc Dt Cl Ctx lbl lsize (frH env) X0 [frH env])
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc (mR R) (mF R F m0 σC) ms (mRdJ0 (rdJH L.lab R J) σC)
      (mRdJ0 (rdJH L.lab R J) σC) := by
  have hmR : (mR R).OK := Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have hR8' : (mR R).base.toNat % 8 = 0 := by
    have hb : ((mR R).base.toNat : Int) = R.base.toNat + -80 :=
      Region.callee_base (hi' := 8) hR (kc := -80) (lo' := -208) (by omega) (by decide) (by omega)
    omega
  have hctl : ∀ σ c, mRdJ0 (rdJH L.lab R J) σC σ c → c = Spike.Lib.X64HelloRodataSrc.rdCN :=
    fun _ _ h => h.2.1
  have hcf : ∀ σ c, mRdJ0 (rdJH L.lab R J) σC σ c → ([frH env] = [] → ∀ a, c.term ≠ .ret a) ∧
      Spike.Lib.X64.WakeWf.RunWf Spike.Lib.X64HelloSrc.helloSrc c [frH env] := fun σ c h => by
    rw [hctl σ c h]
    exact Spike.Lib.X64HelloRdCf.hcf_frH (Spike.Lib.X64HelloRdCf.rd_terms 0 0 (cst (.num 0)) (cst (.num 0))).2.1
  refine Spike.Lib.X64.HelloPh.RdWfSFX.rdPreW_WSHX (fs := [frH env]) (frM := frH env) (rS := rS) hp hlo hΛ hlab
    hsite hcl hX0 (.inr rfl) hsep ha hW hb hmR hR8' (by simp only [mR, Region.callee]; omega)
    (by simp only [mR, Region.callee]; omega) hpool (tp := tp) ?_ hmr (fun m hm => hun m hm.1) hmp
    (fun q hq w hw m hm => hmem q hq w hw m hm.1) hno hnoM hcf hcf ?_ hX0a hctx hctr hheap hoff hnew hlt h64
  · rintro σ c ⟨rfl, -, c', σe, hJe, -, -, -, -, ht, -, -⟩
    exact ht.trans (hJ σe _ hJe).1
  · refine Spike.Lib.X64.HelloPh.HrdS.rdPreW_frS' (fun ⟨σ, c, h⟩ => ?_) hRlo fun σ c h _ => ?_
    · have h' : mRdJ0 (rdJH L.lab R J) σC σ c := h.elim id id
      obtain ⟨-, -, c', hc'⟩ := h'
      exact Spike.Lib.X64.HelloPh.HrdS.frP_mNC hR (by omega) (by omega) hme (fun σ c h => (hJ σ c h).2)
        ⟨c', hc'⟩
    · rw [hctl σ c (h.elim id id)]
      exact Spike.Lib.X64.HelloPh.RdPreS.placed_rdCN hm

end Hello

/-! ## The root's `hrd` at `ownGHXW` -/

section Root

variable {asm : Scc.Sem.X64.Asm}
variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
/-- main's owned words at the root. -/
local notation "OX" => ownGHXW (Ly) NT

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- main's frame at the root. -/
local notation "FR" => frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at the new stack's base `v` (`LandRd`'s `J'`). -/
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The root's memory side under main's frame, owning `OX` (`StartH0X`'s `MSU [FR]`). -/
local notation "MSX" => msUHg (asm := asm) hpw i0 (OX) E rd I ls [FR]

set_option hygiene false in
/-- The same at `ownGH` (`HrdArena`'s facts are stated there). -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls [FR]

set_option hygiene false in
/-- The start's level at the root's choices, at `OX` (`StartH0X`'s `WP`). -/
local notation "WP" => WSg (OX) (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

/-- **The root's `hrd` at `ownGHXW`, any context** (module doc): `wc_rodata` up to the allocator's return inside
`WSg (ownGHXW Ly ntA)` under main's thread pointer, from `scc_rt_main`'s call at the first stack's top, for every
`v`, `m0`, `σC`, at `msUHg (ownGHXW Ly ntA) … [FR]`. The context at the counter add is the one premise (`hctx`,
under main's thread pointer). -/
theorem hrd_RX (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2) {Ctx : FragS isa} {ls0 : Lsize}
    (hctx : ∀ (v : BitVec 64) (m0 : MachineData) (σC : FAS), ∀ q : Call, q.OK (MSX) (Ly).lab →
      q.ra = ((Ly).lab ".Lwc_rodata.x15").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (RS helloLsw v)))
        (fun m => mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (RS helloLsw v)) (-48) (-160) 8 m ∧
          RdCtx (MSX) (Ly).lab (mR (RS helloLsw v)) (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC) q m)
        (N (Ly).lab (MSX) q .rmw) s c → TP (TV) s → Ctx s c [FR]) :
    ∀ v m0 σC, RdPreW (tpG (TV) fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc (mR (RS helloLsw v))
      (mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC) (MSX) (mRdJ0 ((J') v) σC)
      (mRdJ0 ((J') v) σC) := by
  intro v m0 σC
  -- the frame condition pins `v` at the first stack's top
  by_cases hv : v = TOP
  case neg => exact Spike.Lib.X64.HelloPh.HrdRoot.rdPreW_vac fun m hm => hv hm.1.1.2.1.1
  subst hv
  -- the layout's facts
  have hprog : (Ly).prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab := Spike.Lib.X64HelloOInit.hlab_H hpw IH hpa hhp hlo0
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  have hsite := Spike.Lib.X64.HelloPh.siteH hprog hlo hlab
  have hX0 := Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly) (a := AX) hlab rfl
  have hcl := Spike.Lib.X64.HelloPh.ClH.cl (L := Ly)
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceWX.wf_link_of_placeWX IH hpw
  -- `ownGHXW`'s separation, from A13's data part
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw IH hA13
  have hsep : Spike.Lib.X64.PhRec.TcbSep (Ly) := hs.tcb
  have ha : tcbM (Ly) ≠ NT := hs.tcb_a 1 (by decide)
  have hW := Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw IH hA13
  -- the region: `scc_rt_main`'s at the first stack's top, 8-aligned, its band on the pool
  obtain ⟨hok, hR, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hbd : (stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := Spike.Lib.X64WakeHClC.hbd_W hpw IH
  have hal : (stacksA (Ly).lab).toNat % 16 = 0 := by
    rw [(Ly).lab_stacks]; exact (Ly).stacks_al
  have hb0 : ((RS helloLsw (TOP)).base.toNat : Int) = (TOP).toNat + (-8 - 0) :=
    Region.callee_base hok (by show (-helloLsw : Int) ≤ -8 - 0 + (8 - helloLsw); decide) (by decide)
      (by show (-8 - 0 : Int) < 0; decide)
  have htop : (TOP).toNat = (stacksA (Ly).lab).toNat + 16384 := by
    simp only [topS, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hR8 : (RS helloLsw (TOP)).base.toNat % 8 = 0 := by omega
  have hbRS : BandOnP (Ly) (RS helloLsw (TOP)) (-288) 8 :=
    bandRS (show (8 - helloLsw : Int) ≤ -288 by decide) (show helloLsw < 16384 by decide) hok
  have hb : BandOnP (Ly) (mR (RS helloLsw (TOP))) (-208) 8 := fun k h1 h2 => by
    have e : (mR (RS helloLsw (TOP))).addr k = (RS helloLsw (TOP)).addr (-80 + k) :=
      Region.callee_addr _ (-80) (-208) 8 k
    rw [e]; exact hbRS _ (by omega) (by omega)
  -- the arena's facts: `HrdArena`'s at `msUH`, `Call.OK` carried over field by field
  have hOK : ∀ q : Call, q.OK (MSX) (Ly).lab → q.OK (MSU) (Ly).lab := fun _ hq => { hq with }
  have hnoM : ∀ q : Call, q.OK (MSX) (Ly).lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 (MSX).ctr ∨ ∃ o', o' + (MSX).units q.n q.τ ≤ (MSX).cells ∧ w.toNat = q.hdrAt (MSX) o') →
      w ≠ tcbM (Ly) := by
    intro q hq w hw
    rcases hw with rfl | ⟨o', ho, h⟩
    · intro he
      have hct : (MSX).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
      have hsep' : Scc.Cert.Rt.X64.WordSep (tcbM (Ly)) (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) :=
        Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX IH hpw) _
          ((Ly).fld_mem (i := 0) (by decide))
      rw [← he, hct] at hsep'
      unfold Scc.Cert.Rt.X64.WordSep at hsep'
      omega
    · have h1 : (MSX).off q.n q.τ ≤ 16 * (MSX).units q.n q.τ :=
        Spike.Lib.X64.HelloPh.HrdArena.hoffQ_U hpw i0 q (hOK q hq)
      have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
        Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
      have hh : (MSX).heap = (Ly).Λ.heap.lo := rfl
      have hcl' : (MSX).cells = Scc.Cert.PlaceOK.allocCells := rfl
      rw [hq.off] at h1
      rw [Spike.Lib.X64.Alloc.Call.hdrAt, hh] at h
      rw [hcl'] at ho
      have hn := Spike.Lib.X64.WakePh.ne_tcbM_of_heap (L := Ly) hwf (c := w.toNat) w.isLt (by
        simp only [Scc.Sem.Range.contains]
        generalize q.n * (Spike.Lib.X64.Alloc.mOf q.h).toNat = k at h1 h
        generalize (MSX).units q.n q.τ = u at h1 ho
        omega)
      simpa using hn
  -- `hrd_WSHX` at the context guarded by the thread pointer, then the guard discharged inside `tpG`
  have h := hrd_WSHX (rS := RS0) (a := NT) (ar := AR) (Dt := DtW)
    (Cl := Spike.Lib.X64.HelloPh.ClH (Ly)) (Ctx := fun s c fs => TP (TV) s → Ctx s c fs) (lbl := LB)
    (lsize := ls0T ls0) (X0 := X0WH (Ly) (AX)) hprog hlo hΛ hlab hsite hcl hX0 hsep ha hW hb hR hR8
    (show (8 - helloLsw : Int) ≤ -288 by decide) (show (8 : Int) ≤ 8 by decide)
    (Spike.Lib.X64.HelloPh.HrdArena.hpool_U hpw i0) (ms := MSX) (J := JS (Ly) 0#64 c0S) (tp := TV)
    (w := TermRun.cst (.loc ⟨Spike.Lib.X64WakeT1.mainTidLbl 2, 0⟩ 0)) (env := c0S.env) (m0 := m0) (σC := σC)
    (Spike.Lib.X64.HelloPh.HrdR.hJ_JS hpw i0) Spike.Lib.X64.HelloPh.HrdR.hme_c0S hm ?hmr
    Spike.Lib.X64.HelloPh.HrdR.hun_FS
    (fun _ h => h.1)
    (fun q hq => Spike.Lib.X64.HelloPh.HrdArena.hmem_U hpw i0 hc q (hOK q hq))
    (fun q hq => Spike.Lib.X64.HelloPh.HrdArena.hno_U hpw i0 hA13 q (hOK q hq)) hnoM
    (fun _ _ _ => Spike.Lib.X64.AllocG.AllocW.imp (Spike.Lib.X64.HelloPh.WcWfR.allocW_freeH hlab)
      (Spike.Lib.X64.Alloc.AllocW.triv _ _) (fun s _ h _ => hX0 s h))
    (fun q hq hra s c hAt htp => hctx (TOP) m0 σC q hq hra s c hAt htp)
    rfl rfl (fun _ _ => rfl) id
    (Spike.Lib.X64.HelloPh.HrdArena.hlt_U hpw i0 hc) (Spike.Lib.X64.HelloPh.HrdArena.h64_U hpw i0 hc)
  case hmr =>
    show Scc.Sem.Kernel.mapped _ false ⟨Spike.Lib.X64.Flow.Ret0.limA (tpOf (Spike.Lib.X64.Flow.Ret0.pinA
      (Ly).lab + 0#64 + 8#64)), 8⟩ = true
    rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (i := 1) (by decide))).2.1
  exact Spike.Lib.X64.HelloPh.HrdTp.RdPreW.mapWK
    (fun s c hw hk => ⟨fun ht => Spike.Lib.X64.WakePh.RootUL.w0_mono hw fun hC => hC ht, hk⟩) h

/-- **The root's `hrd` at `ownGHXW` with the allocator's caller's invariant at the first stack's top**
(`StartH0X.hst0_X`'s `hrd` at `J1 := fun σC => mRdJ0 (J' TOP) σC`): `hrd_RX` at `v = TOP`, vacuous elsewhere
(`HrdRoot.rdPreW_vac`). -/
theorem hrd_RXT (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2) {Ctx : FragS isa} {ls0 : Lsize}
    (hctx : ∀ (v : BitVec 64) (m0 : MachineData) (σC : FAS), ∀ q : Call, q.OK (MSX) (Ly).lab →
      q.ra = ((Ly).lab ".Lwc_rodata.x15").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (RS helloLsw v)))
        (fun m => mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (RS helloLsw v)) (-48) (-160) 8 m ∧
          RdCtx (MSX) (Ly).lab (mR (RS helloLsw v)) (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC) q m)
        (N (Ly).lab (MSX) q .rmw) s c → TP (TV) s → Ctx s c [FR]) :
    ∀ v m0 σC, RdPreW (tpG (TV) fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc (mR (RS helloLsw v))
      (mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC) (MSX) (mRdJ0 ((J') v) σC)
      (mRdJ0 ((J') (TOP)) σC) := by
  intro v m0 σC
  by_cases hv : v = TOP
  case neg => exact Spike.Lib.X64.HelloPh.HrdRoot.rdPreW_vac fun m hm => hv hm.1.1.2.1.1
  subst hv
  exact hrd_RX hpw i0 E rd I ls hpa hhp hlo0 hc hA13 hm hctx (TOP) m0 σC

/-- **The root's `hrd` at `ownGHXW` at `LandRU.CtxRdHg (ownGHXW Ly ntA)`** (the level-0 context at `ownGHXW`): `hrd_RXT`
at `LandRU.hctx_rdRHg`, no context premise left. -/
theorem hrd_RdHX (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2) {ls0 : Lsize} :
    ∀ v m0 σC, RdPreW (tpG (TV) fun s c => WSg (OX) (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly))
        (Spike.Lib.X64.HelloPh.LandRU.CtxRdHg (asm := asm) hpw i0 E rd ls (OX)) (LB) (ls0T ls0) (FR)
        (X0WH (Ly) (AX)) s c [FR])
      KR (Ly).exe (Ly).endPc (mR (RS helloLsw v)) (mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC)
      (MSX) (mRdJ0 ((J') v) σC) (mRdJ0 ((J') (TOP)) σC) :=
  hrd_RXT hpw i0 E rd I ls hpa hhp hlo0 hc hA13 hm fun v m0 σC =>
    Spike.Lib.X64.HelloPh.LandRU.hctx_rdRHg hpw i0 E rd ls (OX) hc rfl v m0 σC

end Root

end Spike.Lib.X64.HelloPh.HrdRootX

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.HrdRootX.bandRS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdRootX.bandRS

/-- info: 'Spike.Lib.X64.HelloPh.HrdRootX.hrd_WSHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdRootX.hrd_WSHX

/-- info: 'Spike.Lib.X64.HelloPh.HrdRootX.hrd_RX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdRootX.hrd_RX

/-- info: 'Spike.Lib.X64.HelloPh.HrdRootX.hrd_RXT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdRootX.hrd_RXT

/-- info: 'Spike.Lib.X64.HelloPh.HrdRootX.hrd_RdHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdRootX.hrd_RdHX
