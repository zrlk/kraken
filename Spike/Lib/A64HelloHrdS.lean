/-
**hello.w's `wc_rodata` up to the allocator's return inside the start's level at the setup call's frame**
(AArch64; `StartWcS.hello_start_wc_segWS`'s / `StartH0U.hst0_ofHU_i0`'s `hrd`):
`RdWfSF.rdPreW_WSHF` at `fs = [frH env]` (the root's `frM`), `wc_rodata`'s entry invariant `mRdJ0 (rdJH lab J) σC`
(the source at `rodata`'s allocation `rdCN` after the setup's call) taken also as the allocator's caller's
(`J1 := J0`: the entry block's local run is the empty one).

The controls' facts are `RdCf.hcf_frH` at `rdCN`, the placement `RdPreS.rdPreW_frS` with the frame's `me` at
`scc_rt_main`'s saved `x0` (slot `-80`, `frP_mNC`) whenever the invariant is inhabited (`rdPreW_frS'`; else
`rdPreW_void`). The memory side's and the arena's premises (`hmp`, `hmem`, `hno`, `hX0a`, `hctx`, `hctr` … `h64`)
are left to the root (row 5h-S-arena).

- `rdPreW_void`: `RdPreW` at uninhabited invariants, inside any predicate.
- `rdPreW_frS'`: `RdPreS.rdPreW_frS` with the frame's premises asked only at an inhabited invariant.
- `frP_mNC`: the frame's premises at a caller's state at `mNC`, `me` the entry's `x0`.
- `hrd_WSHF`: the statement.
-/
import Spike.Lib.A64HelloRdPreS
import Spike.Lib.A64HelloWeS

namespace Spike.Lib.A64.HelloPh.HrdS

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (ValRep)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize Placed)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.HelloPh.WcW (freeNH)
open Spike.Lib.A64.HelloWf (WSHF)
open Spike.Lib.A64.Flow.HelloRd (rN RdPreW RdCtx)
open Spike.Lib.A64.Flow.Hello1 (mNC mR mF mRdJ0 aR)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.HelloRdCf (frH)
open Spike.Lib.A64.HelloPh.RdPlS (FrP)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib (Arena FragS Frag Ctl Region)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## The placement at inhabited invariants -/

section Pl

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {ms : Spike.Lib.MemSide isaLSE2}
  {J0 J1 : FAS → Ctl → Prop}

/-- **`wc_rodata` up to the allocator's return at uninhabited invariants** is inside any predicate. -/
theorem rdPreW_void {P : Frag isaLSE2} {R : Region} {F : MachineData → Prop}
    (hn : ∀ σ c, ¬ J0 σ c ∧ ¬ J1 σ c) : RdPreW P (fun _ _ => False) exe endPc R F ms J0 J1 :=
  ⟨Spike.Lib.A64.HelloPh.WeS.proW_ofCtl fun σ c h => absurd h (hn σ c).1,
    fun _ _ c _ _ _ _ _ _ ⟨σe, h, _⟩ => absurd h (hn σe c).1,
    fun q _ _ => Spike.Lib.A64SetupPlaced.allocW_of_ctl fun _ hF _ _ _ _ => by
      obtain ⟨-, -, -, -, c', -, ⟨⟨σe, h, -⟩, -⟩, -⟩ := hF
      exact absurd h (hn σe c').2⟩

/-- **`RdPreS.rdPreW_frS` with the frame's premises asked only at an inhabited invariant** (`hP`). -/
theorem rdPreW_frS' {R : Region} {F : MachineData → Prop} {m0 : MachineData} {σC : FAS} {env : Env}
    (hP : (∃ σ c, J0 σ c ∨ J1 σ c) → FrP lbl R env σC) (hlo : R.lo ≤ -288)
    (hc : ∀ σ c, J0 σ c ∨ J1 σ c → ∀ s, Placed Λ lbl s c) :
    RdPreW (fun s c => PlacedSE Λ lbl s c [frH env]) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC) ms
      J0 J1 := by
  by_cases h : ∃ σ c, J0 σ c ∨ J1 σ c
  · exact Spike.Lib.A64.HelloPh.RdPreS.rdPreW_frS (hP h) hlo hc
  · exact rdPreW_void fun σ c => ⟨fun h0 => h ⟨σ, c, .inl h0⟩, fun h1 => h ⟨σ, c, .inr h1⟩⟩

/-- **The frame's premises at a caller's state at `mNC`** (`hJC`): `me`'s one word `w` (`hme`) is represented
by the entry's `x0` (`hX`), which `scc_rt_main` saved at its slot `-80`. -/
theorem frP_mNC {lab : Label → Int64} {J : FAS → Ctl → Prop} {R : Region} {env : Env} {w : Word} {σC : FAS}
    (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hme : ∀ ty ws, lookupE env "me" = some (ty, ws) → ws = [w])
    (hX : ∀ σ c, J σ c → ValRep lbl w.val σ.regs.X0.toBitVec.toNat) (hJC : ∃ c, (mNC lab J).J σC c) :
    FrP lbl R env σC := by
  obtain ⟨c, ⟨σe, hJ, -, -, h80, -⟩, -⟩ := hJC
  refine ⟨hR, hlo, hhi, -80, w, ⟨⟨by decide, hlo, by omega⟩, Int.le_refl _⟩, hme, ?_⟩
  rw [h80]
  exact hX σe c hJ

end Pl

/-! ## `hrd` -/

section Hello

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {X0 : State → Prop}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-- **`wc_rodata` up to the allocator's return inside `WSHF` at the setup call's frame** (`hello_start_wc_segWS`'s
`hrd` at `J1 := mRdJ0 (rdJH lab J)`): from `scc_rt_main`'s call of `wc_rodata` at `mNC lab J` in the region `R`
(`hRlo`), the frame condition `mF R F m0 σC`, the source at `rodata`'s allocation under `frH env`.
- Every entry state of `J` is at the thread pointer `tp` and its `x0` represents `me`'s word `w` (`hJ`, `hme`); the
  layout's immediate of `m` at `rodata`'s allocation is `2` (`hm`; `helloImms`'s at `helloImm_t2 = eB`).
- The limit word `limA tp` is mapped (`hmr`) and unmapped in private memory under `F` (`hun`).
- `rdPreW_WSHF`'s memory side's and arena's premises at `ms`, the allocator's region `aR (mR R)` (`hpool`, `hmp`,
  `hmem`, `hno`, `hX0a`, `hctx`, `hctr` … `h64`; row 5h-S-arena). -/
theorem hrd_WSHF (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2} {J : FAS → Ctl → Prop} {tp : UInt64}
    {w : Word} {env : Env} {m0 : MachineData} {σC : FAS}
    (hJ : ∀ σ c, J σ c → σ.regs.TPIDR_EL0 = tp ∧ ValRep lbl w.val σ.regs.X0.toBitVec.toNat)
    (hme : ∀ ty ws, lookupE env "me" = some (ty, ws) → ws = [w])
    (hm : L.Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.A64.HelloPh.ownH L a j)
    (hX0a : ∀ q : Call, q.OK ms L.lab → q.ra = (L.lab ".L19_wc_rodata.sp0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (aR (mR R))
        (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 0 m ∧
          RdCtx ms L.lab (mR R) (mRdJ0 (rdJH L.lab J) σC) (mRdJ0 (rdJH L.lab J) σC) q m))
    (hctx : ∀ q : Call, q.OK ms L.lab → q.ra = (L.lab ".L19_wc_rodata.sp0").toBitVec →
      ∀ s c, At L.exe L.endPc (aR (mR R)) (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 0 m ∧
        RdCtx ms L.lab (mR R) (mRdJ0 (rdJH L.lab J) σC) (mRdJ0 (rdJH L.lab J) σC) q m)
        (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → Ctx s c [frH env])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    RdPreW (WSHF L a ar Spike.Lib.HelloSrc.helloSrc Dt Cl Ctx lbl lsize (frH env) X0 [frH env])
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (mR R) (mF R F m0 σC) ms (mRdJ0 (rdJH L.lab J) σC)
      (mRdJ0 (rdJH L.lab J) σC) := by
  obtain ⟨hmR, halR, -⟩ := Spike.Lib.A64.Flow.Hello1.mR_ok (F := fun _ => True) hR hal (fun _ _ _ _ => trivial)
    hRlo hhi m0 σC
  have hctl : ∀ σ c, mRdJ0 (rdJH L.lab J) σC σ c → c = Spike.Lib.HelloRodataSrc.rdCN :=
    fun _ _ h => h.2.1
  have hcf : ∀ σ c, mRdJ0 (rdJH L.lab J) σC σ c → ([frH env] = [] → ∀ a, c.term ≠ .ret a) ∧
      Spike.Lib.A64.WakeWf.RunWf Spike.Lib.HelloSrc.helloSrc c [frH env] := fun σ c h => by
    rw [hctl σ c h]
    exact Spike.Lib.HelloRdCf.hcf_frH (Spike.Lib.HelloRdCf.rd_terms 0 0 (cst (.num 0)) (cst (.num 0))).2.1
  refine Spike.Lib.A64.HelloPh.RdWfSF.rdPreW_WSHF (fs := [frH env]) (frM := frH env) (rS := rS) hp hlo hΛ hlab
    hsite hcl hX0 (.inr rfl) hmR halR (by simp only [mR, Region.callee]; omega)
    (by simp only [mR, Region.callee]; omega) hpool (tp := tp) ?_ hmr (fun m hm => hun m hm.1) hmp
    (fun q hq w hw m hm => hmem q hq w hw m hm.1) hno hcf hcf ?_ hX0a hctx hctr hheap hoff hnew hlt h64
  · rintro σ c ⟨rfl, -, c', ⟨σe, hJe, -, -, -, -, ht⟩, -⟩
    exact ht.trans (hJ σe _ hJe).1
  · refine rdPreW_frS' (fun ⟨σ, c, h⟩ => ?_) hRlo fun σ c h _ => ?_
    · have h' : mRdJ0 (rdJH L.lab J) σC σ c := h.elim id id
      obtain ⟨-, -, c', hc'⟩ := h'
      exact frP_mNC hR (by omega) hhi hme (fun σ c h => (hJ σ c h).2) ⟨c', hc'⟩
    · rw [hctl σ c (h.elim id id)]
      exact Spike.Lib.A64.HelloPh.RdPreS.placed_rdCN hm

end Hello

end Spike.Lib.A64.HelloPh.HrdS

/-- info: 'Spike.Lib.A64.HelloPh.HrdS.rdPreW_frS'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdS.rdPreW_frS'

/-- info: 'Spike.Lib.A64.HelloPh.HrdS.hrd_WSHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdS.hrd_WSHF
