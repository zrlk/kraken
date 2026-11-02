/-
**`wc_rodata`'s heap abort at hello's root closes, at `ownGHXW`** (x86-64 only; the `ownGHXW` instance of
`Spike/Lib/X64HelloRdHAbC.lean`): from `wc_rodata`'s `rX .abort` at the frames `[FR]`, a segment inside the
start's level at `ownGHXW` (`StartWcS.WSg (ownGHXW Ly ntA)`, which is `WSHFg (ownGHXW …)` at the frames) under the
take move, with no exit. The heap abort path is lifted to `ownGHXW` by `HabLftX.hpathW_hab0HSX`.

- `bandRSd`: `scc_rt_main`'s region band `[-d, 8]` on the pool (`MainGlueX.bandRS80` at any depth).
- `heapAbStubK_atX`: `HAbStub.heapAbStubK_at` inside `W0` at `ownGHXW`, given `ownGHXW`'s separations and the
  dispatcher band on the pool.
- `hello_rd_hab_closedX`: `RdHAb.hello_rd_hab_closed` at `WSg (ownGHXW Ly ntA)`; the separations from A13's data
  part (`hA13`: `wsep_W`, `tcbWH_notG_W`), the band at `scc_rt_main`'s region at the first stack's top
  (`bandRSd` at `336`).

## Differences from the AArch64 version

AArch64 has no counterpart: its level owns `ownGH` (main owns no TCB word there), so `A64HelloRdHAb`'s closure is
the only one. Against x86-64's `hello_rd_hab_closed` at `ownGH`: the path's states are lifted to `ownGHXW`
(`CstOkH`: main's word held on the abort path, the worker's not, the return address `.Lscc_rt_alloc.full + 12`),
which asks `hA13` for the separations; the proof is otherwise `hello_rd_hab_closed`'s.
-/
import Spike.Lib.X64HelloRdHAb
import Spike.Lib.X64HelloHAbW
import Spike.Lib.X64HelloHabCtlRd
import Spike.Lib.X64HelloStartWcS
import Spike.Lib.X64HelloLand
import Spike.Lib.X64HelloRodata
import Spike.Lib.X64HelloC0S
import Spike.Lib.X64WakeAbOffW
import Spike.Lib.X64HelloClH
import Spike.Lib.X64HelloRdHAbC
import Spike.Lib.X64HelloHabLftX
import Spike.Lib.X64HelloOwnSX
import Spike.Lib.X64WakeStartPlaceLy

namespace Spike.Lib.X64.HelloPh.RdHAbX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf abi cellsOf)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Frag Region SegWS PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Hello1 (mR mF)
open Spike.Lib.X64.Flow.HelloRd (rX)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakePh.MainGlue (FS RS topS)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (WSg)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.HabCtlRd (HabCtlRdH)
open Spike.Lib.X64.HelloPh.HAbStub (x0WH_abort)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib (HeapAbortOblA)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.WakeWf (W0 RunWf)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64.HelloPh.HAbStub (hpathW_hXH)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The memory side at the start's labels, the entry's marks. -/
local notation "MSf" => fun fs => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd G own
  (Spike.Lib.X64.WakeOD.arW hpw i) I (L0T (Ly).Λ) ls fs

set_option hygiene false in
/-- `rodata`'s frame at the start control. -/
local notation "FR" => Spike.Lib.X64HelloRdCf.frH Spike.Lib.X64.HelloPh.C0S.c0S.env

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => topS (Ly) 0#64

/-- **`scc_rt_main`'s region band `[-d, 8]` lies on the pool** (`MainGlueX.bandRS80` at any depth `d` with
`d + 8 ≤ Lsw`, `d ≤ 8192`). -/
theorem bandRSd {L : RuntimeLayout} {rS : Scc.Sem.Range} {k0 : BitVec 64} {Lsw d : Int}
    (hrS : rS = ⟨(Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hLsw : d + 8 ≤ Lsw) (hd : d ≤ 8192) (hok : (Spike.Lib.X64.swR (topS L k0) (-Lsw) 0).OK) :
    Spike.Lib.X64.WakePh.BandOnP L (RS Lsw (topS L k0)) (-d) 8 := by
  intro k h1 h2
  have hR' : (⟨topS L k0, -Lsw, 1⟩ : Region).OK := ⟨hok.lo, by
    show ((topS L k0).toNat : Int) + 1 ≤ 2 ^ 64; have := (topS L k0).isLt; omega⟩
  have ha := Region.addr_toNat_of hR' (k := -8 - 0 + k) (by show -Lsw ≤ _; omega) (by show _ < (1 : Int); omega)
  have e : (RS Lsw (topS L k0)).addr k = Region.addr ⟨topS L k0, -Lsw, 1⟩ (-8 - 0 + k) := by
    rw [Region.callee_addr]; rfl
  have hf := L.pool_fit
  subst hrS
  obtain ⟨hs1, hs2⟩ := hsub
  simp only at hs1 hs2
  have ht : (topS L k0).toNat = (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0).toNat + 16384 := by
    show (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  change (((Region.addr ⟨topS L k0, -Lsw, 1⟩ (-8 - 0 + k)).toNat : Nat) : Int) = (topS L k0).toNat + (-8 - 0 + k) at ha
  rw [e]
  omega

section Stub

variable {L : RuntimeLayout} (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **`HAbStub.heapAbStubK_at` inside `W0` at `ownGHXW`**: the path at `ownGHXW` (`HabLftX.hpathW_hab0HSX`, the
placement at every state given) in the region below `k`, its dispatcher band on the pool (`hb`). -/
theorem heapAbStubK_atX {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {rS : Scc.Sem.Range} {C : Ctl → Prop} {k : Int} (a : BitVec 64)
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : Spike.Lib.X64.WakePh.tcbM L ≠ a)
    (hW : Spike.Lib.X64HelloOwnLift.tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : Spike.Lib.X64.WakePh.BandIn L (R.callee (k - 8) (-24) 16))
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.X64.FStable R F) (hR : R.OK) (hlo' : R.lo ≤ k - 32) (hhi : k + 8 ≤ R.hi) (h8 : k % 8 = 0)
    (hK : ms.K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : ∀ c0, C c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE L.Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0)
    (hab : ∀ s : State, s.st.2 = L.lab Spike.Lib.X64.Abort.heap.exit → ms.abortAt s)
    (hX0 : ∀ s, Spike.Lib.X64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    ∀ m0 σC c0, C c0 →
      Spike.Lib.X64.Abort.Disp.StubHRW (fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L)
        (Spike.Lib.X64.HelloPh.ownGHXW L a) ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
        (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs)
        (Spike.Lib.X64.PhRec.K L rS) p lbl ms L.exe L.endPc (R.callee (k - 8) (-24) 16)
        (fun m => F m ∧ Spike.Lib.X64.CKept R (k - 8) (-24) 16 m0 m ∧ Spike.Lib.X64.Abs R ⟨k, []⟩ m0 σC) c0
        ((L.lab Spike.Lib.X64.Alloc.fullL + 12).toBitVec) := by
  haveI := L.valid
  intro m0 σC c0 hC
  obtain ⟨hc0, hpl, hobl⟩ := hctl c0 hC
  have hR' := Region.callee_ok (hi' := 16) hR (show R.lo ≤ k - 8 + -24 by omega) (by decide) (by omega)
    (by omega)
  have hFe : Spike.Lib.X64.FStable (R.callee (k - 8) (-24) 16)
      (fun m => F m ∧ Spike.Lib.X64.CKept R (k - 8) (-24) 16 m0 m ∧ Spike.Lib.X64.Abs R ⟨k, []⟩ m0 σC) :=
    Spike.Lib.X64.fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by omega) (by decide)
      (by decide)
  have h0 := Spike.Lib.X64.HelloPh.HabLftX.hpathW_hab0HSX (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0)
    (ls0 := ls0) (frM := frM) (X0 := X0) (c0 := c0) hp hlo hlab a hsep ha hW hb hΛ hR'
    (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hFe (fun s _ => hpl s) hobl hX0
  have hX := hpathW_hXH (F := fun m => F m ∧ Spike.Lib.X64.CKept R (k - 8) (-24) 16 m0 m ∧
      Spike.Lib.X64.Abs R ⟨k, []⟩ m0 σC) (c0 := c0)
    (ra := (L.lab Spike.Lib.X64.Alloc.fullL + 12).toBitVec) hp hlo hlab hR' (by simp [Region.callee])
    (by simp [Region.callee])
  have hpath := Spike.Lib.X64.WakePh.HPathW.map (Spike.Lib.X64.WakePh.HAbStubK.hpathW_K
    (K := Spike.Lib.X64.PhRec.K L rS)
    (Spike.Lib.X64.Abort.Disp.HPathW.and h0 hX fun _ _ h₁ h₂ => And.intro h₁ h₂)
    fun s _ h s' hk => (Spike.Lib.X64.HelloPh.HAbStub.abort_offH hlab s h.2).2 (congrArg (fun x : Int64 => x.toBitVec.toNat) hk.1))
    fun _ _ h => h.1
  exact Spike.Lib.X64.StubW.stubHRW_of_code L.lays rfl (hp ▸ SccCode.hello_abort) hK hFe hpath fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

end Stub

set_option maxHeartbeats 800000 in
/-- **The start's `wc_rodata` heap-abort exit closes** (`StartH0R`/`StartH0U`'s `hCrd`): from `rX .abort` in
`wc_rodata`'s region at the frames `[FR]` (any `v`, `m0`, `σC`), a segment inside `W0` at `ownGHXW`, `arW`,
`ClH`, `DtW`, `X0WH … (lab take_site)`, `frM := FR` under the take move, with no exit. -/
theorem hello_rd_hab_closedX {asm : Scc.Sem.X64.Asm} {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize}
    {Ctx : FragS isa} {ls0 : Lsize} {J1 : FAS → FAS → Ctl → Prop}
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some helloCells) (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    /- the controls' facts at `rX .abort` -/
    (hhabctlRd : ∀ σC, HabCtlRdH ((MSf) [FR]) (Ly).lab helloSrc (Ly).Λ (L0T (Ly).Λ) (mR (RS helloLsw (TOP)))
      (Spike.Lib.X64.WakeOD.arW hpw i) [FR] (J1 σC)) :
    SegWS (WSg (Spike.Lib.X64.HelloPh.ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)) (Ly)
        (Spike.Lib.X64.WakeOD.arW hpw i) helloSrc DtW
        (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (L0T (Ly).Λ) (ls0T ls0) FR
        (X0WH (Ly) ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) helloSrc (L0T (Ly).Λ) (MSf)
      (Frag.at (fun s c => ∃ v m0 σC,
        At (Ly).exe (Ly).endPc (mR (RS helloLsw v)) (mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC)
          (rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (mR (RS helloLsw v)) (J1 σC) .abort) s c) [FR])
      (fun _ _ _ => False) := by
  have hp : o.prog = helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeLabel lo helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw i hA13
  have bandIn_rdAb : Spike.Lib.X64.WakePh.BandIn (Ly) ((RS helloLsw (TOP)).callee (-288 - 8) (-24) 16) := by
    have hok := (Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i).1
    have hB := bandRSd (k0 := 0#64) (d := 336) (rS := RS0) (by rw [(Ly).lab_stacks])
      (Spike.Lib.X64.Rt.rS0_sub (Ly)) (by decide) (by decide) hok
    intro k h1 h2
    rw [Region.callee_addr]
    exact hB _ (by omega) (by omega)
  have hab : ∀ s : State, s.st.2 = (Ly).lab Spike.Lib.X64.Abort.heap.exit → ((MSf) [FR]).abortAt s :=
    fun s hs => by
      obtain ⟨-, e9⟩ := Spike.Lib.X64.HelloPh.abH_labsH hlab (L := Ly)
      refine ⟨.heap, 4202760, ?_, by unfold pcOf; rw [hs]; erw [e9]; rfl⟩
      rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
      show codeLabel (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .heap) = _
      rw [hprog, hlo, hΛ, ← codeT_eq]; decide +kernel
  refine (SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × FAS =>
      Frag.at (At (Ly).exe (Ly).endPc (mR (RS helloLsw g.1))
        (mF (RS helloLsw g.1) (FS (Ly) (RS0) helloLsw 0#64 g.1) g.2.1 g.2.2)
        (rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (mR (RS helloLsw g.1)) (J1 g.2.2) .abort)) [FR])
      fun ⟨v, m0, σC⟩ => ?_).mono_pre
    fun _ _ _ ⟨⟨v, m0, σC, h⟩, hf⟩ => ⟨⟨v, m0, σC⟩, h, hf⟩
  by_cases hv : v = TOP
  case neg =>
    refine SegWS.empty fun _ _ _ h => ?_
    obtain ⟨⟨-, -, -, -, _, -, hF, -⟩, -⟩ := h
    exact hv hF.1.1.2.1.1
  subst hv
  obtain ⟨-, hR, hF⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i
  refine (SegWS.liftS (Q₀ := fun _ _ => False) [FR] (Spike.Lib.X64.Abort.Disp.seg_jabort2RW_up
      (Q := fun _ _ => False) (kc := -80) (lo' := -208) (hi' := 8) (e := -208) (k := -288)
      (nX := rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (mR (RS helloLsw (TOP))) (J1 σC) .abort)
      (F' := mF (RS helloLsw (TOP)) (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m0 σC)
      rfl (by decide) rfl (fun σ c h => h.1) (by simp [Spike.Lib.Region.callee, Spike.Lib.Region.Off])
      (fun σ c h => h.2.1) (fun m hm => ⟨hm.1, m0, σC, _, hm.2.1, hm.2.2⟩) hF hR
      (by show (8 - helloLsw : Int) ≤ -288 - 32; decide)
      (by show (-288 : Int) + 8 ≤ 8; decide) (by decide) rfl
      (heapAbStubK_atX (C := fun c0 => ∃ σx,
          (rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (mR (RS helloLsw (TOP))) (J1 σC) .abort).J σx c0)
        hprog hlo hlab _ hs.tcb (hs.tcb_a 1 (by decide)) (Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw i hA13)
        bandIn_rdAb hΛ hF hR
        (by show (8 - helloLsw : Int) ≤ -288 - 32; decide)
        (by show (-288 : Int) + 8 ≤ 8; decide) (by decide) rfl
        (.inr rfl) (fun _ h => h.2) (fun c0 hx => hx.elim fun σx hJ => hhabctlRd σC σx c0 hJ) hab
        (x0WH_abort hlab rfl))) (fun _ _ h => h)).mono_post fun _ _ _ h => h.1.elim

end Spike.Lib.X64.HelloPh.RdHAbX

/-- info: 'Spike.Lib.X64.HelloPh.RdHAbX.bandRSd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdHAbX.bandRSd

/-- info: 'Spike.Lib.X64.HelloPh.RdHAbX.heapAbStubK_atX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdHAbX.heapAbStubK_atX

/-- info: 'Spike.Lib.X64.HelloPh.RdHAbX.hello_rd_hab_closedX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdHAbX.hello_rd_hab_closedX
