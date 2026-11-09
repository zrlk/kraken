/-
**wake.w's `wc_main` before the box's landing inside the start's level
guarded by the thread pointer** (x86-64): `WcWfS`'s `WcPreW`/`WcSp0W` at
`W0 … own … []` with the obligations that only hold at the root's thread
pointer `t` owed only there: the box's store's writes' obligation (`hwr`)
and the allocator's counter context (`hctx`); the conclusions at
`tpG t (W0 …)`. Generic in the layout, the owned words `own`, the region,
the source, the arena and the level, as `WcWfS`.

- `nT`, `at_of_nT`, `nT_of_at`, `nodeW_nT`, `nodeW_unTp`: a node restricted
  to the states with thread pointer `t`.
- `wcSp0W_WSOg`: `.x18`'s block and the box's store, `hwr` under `tpG t`.
- `allocW_WSOg`: `scc_rt_alloc` with the counter's context owed only at `t`
  (`WakeWf.allocW_WS_tp`'s proof at the allocator's `SFactsSt2` given).
- `wcPreW_WSOg`: the prologue and entry block by `WcWfS`'s, the allocator
  by `allocW_WSOg`.

x86-64 twin of `Spike/Lib/A64WakeWcWfR.lean`'s sections `Tp` and `Gen`
(`nT` … `nodeW_unTp`, `wcSp0W_WSg`, `allocW_wcWSg`, `wcPreW_WSg`; namespace
`Spike.Lib.X64.WakePh.WcWfR`, the level lemmas suffixed `O`). **Where this
differs from AArch64**: the thread pointer is `fsBase` (A64
`TPIDR_EL0`); as `WcWfS`, the owned words are any `own` with the nodes'
`SFactsSt2` given (`hS`, `hSa`; A64 builds them at `ownG` by `WcW.*_wcG`),
so `allocW_WSOg` takes no `hmp`/`hno`/`hpool` and `wcSp0W_WSOg` no
`hbox` (its store's step from `hunB`); the box's store is at `.x18 + 15`
(A64 `.sp0 + 3` words); no `hal`.
-/
import Spike.Lib.X64WakeWcWfS
import Spike.Lib.X64WakeTP

namespace Spike.Lib.X64.WakePh.WcWfR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW At mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakeWf (W0 RunWf NoWrC)
open Spike.Lib.X64.WakePh.WcW (freeN)
open Spike.Lib.X64.WakePh (instOkW)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.Flow.WakeWc
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_store_agrees)

/-! ## A node restricted to a thread pointer -/

section Tp

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- `n` at the abstract states of thread pointer `t`. -/
def nT (n : ND) (t : UInt64) : ND := ⟨n.pc, n.o, fun σ c => n.J σ c ∧ σ.regs.fsBase = t⟩

/-- A state at the restricted node is at the node. -/
theorem at_of_nT {n : ND} {t : UInt64} {s : State} {c : Ctl} (h : At exe endPc R F (nT n t) s c) :
    At exe endPc R F n s c :=
  let ⟨he, hn, hd, hpc, σ, hA, hF, hJ, _⟩ := h
  ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩

/-- A state at the node with thread pointer `t` is at the restricted node. -/
theorem nT_of_at {n : ND} {t : UInt64} {s : State} {c : Ctl} (h : At exe endPc R F n s c)
    (ht : TP t s) : At exe endPc R F (nT n t) s c :=
  let ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩ := h
  ⟨he, hn, hd, hpc, σ, hA, hF, hJ, by rw [← hA.regs]; exact ht⟩

/-- A node obligation restricts to the thread pointer `t`. -/
theorem nodeW_nT {W : Spike.Lib.Frag isa} {K : State → State → Prop} {n : ND} {t : UInt64}
    (h : NodeW W K exe endPc R F n) : NodeW W K exe endPc R F (nT n t) :=
  fun s c hA => h s c (at_of_nT hA)

/-- A node obligation guarded by the thread pointer is one at the restricted node. -/
theorem nodeW_unTp {W : Spike.Lib.Frag isa} {n : ND} {t : UInt64}
    (h : NodeW (tpG t W) (fun _ _ => False) exe endPc R F n) :
    NodeW W (fun _ _ => False) exe endPc R F (nT n t) :=
  fun s c hA => ⟨(h s c (at_of_nT hA)).1 (Spike.Lib.X64.WakeTP.tp_of_at (n := nT n t)
    (fun _ _ (h : n.J _ _ ∧ _) => h.2) hA),
    fun _ h => h⟩

end Tp

section Gen

variable {L : RuntimeLayout} {own : Spike.Lib.X64Consumer.Own} {K : State → State → Prop} {rS : Range}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}
  (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeN (pcOf s) = true → X0 s)

set_option hygiene false in
/-- The start's level at the owned words `own`. -/
local notation "WO" => fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
  (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize frM X0 s c []

include hp hlo hΛ hlab hsite hcl hX0

/-- **`WcWfS.wcSp0W_WSO` guarded by the thread pointer `t`**: the store's
writes' obligation only at `t` (`hwr`), the level only at `t`. -/
theorem wcSp0W_WSOg (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop} {t : UInt64}
    (hunB : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hS : WcSp0W (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F ms J0)
    (hpl : WcSp0W (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J0)
    (hwr : NodeW (tpG t (NoWrC ar p lbl lsize Ctx [])) (fun _ _ => False) L.exe L.endPc R F
      (sN ms L.lab R J0 .st)) :
    WcSp0W (tpG t (WO)) K L.exe L.endPc R F ms J0 := by
  obtain ⟨-, -, -, eX, -, -, -⟩ := Spike.Lib.X64.WakePh.OwnWc.wc_labs hlab (L := L)
  have hin := wake_wcS0In
  simp only [wcS0In, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  have hI := instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hb : blockAtB L.prog ".Lwc_main.x0" 15 [(Spike.Lib.X64.stDir .rcx 0 .rax, 3)] = true := by
    rw [hp]; exact h3
  refine ⟨?_, ?_⟩
  · exact Spike.Lib.X64.AllocG.BlkW.imp
      (Spike.Lib.X64.WakePh.WcWfS.blkW_WSO hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.x0") (k := 0) h0
        (ofNat_zero' _) wcS0_ok hR hRlo hhi hS.b (by intro j hj; rw [eX]; revert j; decide +kernel)
        (by unfold Spike.Lib.X64.WakeWf.phOffW; decide +kernel) (by decide) (by wcfreeB_dec)
        (fun _ _ ⟨q, ⟨σe, hJe, _⟩, _, o, hc, _⟩ => hc ▸ Spike.Lib.X64.WakePh.WcWfS.cf_hold (hc0J σe _ hJe))
        hpl.b)
      Spike.Lib.X64.BlkW.triv fun _ _ h _ _ => h
  · have hT := Spike.Lib.X64.WakePh.WcWfS.nodeW_WSO hp hlo hΛ hlab hsite hcl hX0 (Dt := Dt) (frM := frM)
      (n := nT (sN ms L.lab R J0 .st) t) (l := ".Lwc_main.x0") (k := 15) (z := 3) rfl (nodeW_nT hS.st)
      (by rw [eX]; decide +kernel) (by wcfree_dec) (by unfold Spike.Lib.X64.WakeWf.siOffW; decide +kernel)
      (by
        rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, hJ, -⟩
        have hc := Spike.Lib.X64.Rt.cellOf hI hb rfl h1 h2 h4'
        obtain ⟨q, o, hj, hlo', hle, e⟩ := Spike.Lib.X64.WakePh.WcW.slot_box hJ
        have ha' : eaddr s 3 (mB .rcx 0) = σ.slot (-24) :=
          (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs]; exact Spike.Lib.X64.WakePh.WcW.bAddr_box hJ)
        refine ⟨_, _, hc, fun w w' h => (by cases h),
          exec_store_agrees hc ha' (by rw [e]; exact hunB q o hj hlo' hle _ hF) (agrees_of_decls h3' _ _),
          fun s' hu => ?_⟩
        simp only [TreeLeaf] at hu
        obtain ⟨_, rfl⟩ := hu; rfl)
      (fun _ _ ⟨⟨q, o, ⟨σe, hJe, _⟩, hc, _⟩, _⟩ => hc ▸ Spike.Lib.X64.WakePh.WcWfS.cf_hold (hc0J σe _ hJe))
      (nodeW_nT hpl.st) (nodeW_unTp hwr)
    exact fun s c hA => ⟨fun ht => (hT s c (nT_of_at hA ht)).1, (hS.st s c hA).2⟩

omit hX0 in
set_option maxHeartbeats 800000 in
/-- **`WcWfS.allocW_WSO` guarded by the thread pointer `t`**
(`WakeWf.allocW_WS_tp`): the counter's context owed only at `t`. -/
theorem allocW_WSOg {ms : Spike.Lib.MemSide isa} {q : Call} {t : UInt64}
    (hR : R.OK) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hra : q.ra = (L.lab ".Lwc_main.x0").toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hSa : AllocW ms q (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F)
    (hpl : AllocW ms q (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F)
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc R F)
    (hcf : AllocW ms q (fun _ c => (∀ a, c.term ≠ .ret a) ∧ RunWf p c []) (fun _ _ => False)
      L.exe L.endPc R F)
    (hctx : ∀ s c, At L.exe L.endPc R F (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (tpG t (WO)) K L.exe L.endPc R F := by
  have hI := instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hA : Spike.Lib.X64.Alloc.allocIn L.prog = true := by
    rw [hp]; exact Spike.Lib.X64.Flow.WakeWc.wake_alloc
  have hph := Spike.Lib.X64.WakePh.WcW.allocPhW (Λ := L.Λ) hΛ hlab
  have hPh := Spike.Lib.X64.WakeWf.allocAbAcW (Cl := Cl) hI hA hph hlab hR hlo' hhi hq hra hmem
  have hAr := Spike.Lib.X64.AllocG.allocArenaS (lbl := lbl) (p := p) hI hA hR hlo' hhi hq hmem hctr hheap
    hoff hnew
  have hCx := Spike.Lib.X64.AllocG.allocCtrS (Ctx := fun s c => TP t s → Ctx s c []) hI hA hR hlo' hhi hq
    (fun a h => hmem a (.inr h)) hheap hlt h64 hctx
  have hPc := Spike.Lib.X64.AllocG.allocPc (R := R) (F := F) (ms := ms) (q := q) hI hph
  have g1 := Spike.Lib.X64.AllocG.AllocW.imp hX0a hcf (fun _ _ => And.intro)
  have g2 := Spike.Lib.X64.AllocG.AllocW.imp hpl g1 (fun _ _ => And.intro)
  have g3 := Spike.Lib.X64.AllocG.AllocW.imp hPc g2 (fun _ _ => And.intro)
  have g4 := Spike.Lib.X64.AllocG.AllocW.imp hCx g3 (fun _ _ => And.intro)
  have g5 := Spike.Lib.X64.AllocG.AllocW.imp hAr g4 (fun _ _ => And.intro)
  have h2 := Spike.Lib.X64.AllocG.AllocW.imp hPh g5 (fun _ _ => And.intro)
  refine Spike.Lib.X64.AllocG.AllocW.imp hSa h2 ?_
  rintro s c hst ⟨⟨hab, hac⟩, har, hcx, hpc, hpl', hx, hnr, hr⟩ htp
  exact Spike.Lib.X64.WakeWf.W0.intro0 hx (Spike.Lib.X64.WakeWf.Wf.intro
    (Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt hst fun h => h.elim) hab hac hcl (fun _ => hnr) hpl'
    (fun c' fs' hrun L0 hW hne => .inl (har [] c' fs' hrun L0 hW hne lsize)) (fun hW => hcx hW htp) hr
    (Spike.Lib.X64.WakeWf.abortWf_of_off (hI.off s hpc).1.noAbort))

/-- **`WcWfS.wcPreW_WSO` guarded by the thread pointer `t`**: the prologue
and the entry block by `WcWfS`'s, the allocator by `allocW_WSOg` (the
counter's context `hctx` owed only at `t`). -/
theorem wcPreW_WSOg (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop} {tp t : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hS : WcPreW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F ms J0 J0)
    (hpl : WcPreW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J0 J0)
    (hX0a : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".Lwc_main.x0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wAR R)
        (fun m => F m ∧ CallerCells R (-80) (-160) 8 m ∧ WcCtx ms L.lab R J0 q m))
    (hctx : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".Lwc_main.x0").toBitVec →
      ∀ s c, At L.exe L.endPc (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 8 m ∧
        WcCtx ms L.lab R J0 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    WcPreW (tpG t (WO)) K L.exe L.endPc R F ms J0 J0 := by
  obtain ⟨hR', -⟩ := Spike.Lib.X64.WakePh.WcW.wAR_ok hR hR8 hRlo hhi
  refine ⟨Spike.Lib.X64.Flow.XProW.imp
      (Spike.Lib.X64.WakePh.WcWfS.proW_WSO hp hlo hΛ hlab hsite hcl hX0 hR (by omega) (by omega) htp hun hc0J
        hS.pro hpl.pro)
      Spike.Lib.X64.Flow.XProW.triv fun _ _ h _ _ => h,
    Spike.Lib.X64.AllocG.BlkW.imp
      (Spike.Lib.X64.WakePh.WcWfS.eW_WSO hp hlo hΛ hlab hsite hcl hX0 hR hRlo hhi hc0J hS.e hpl.e)
      Spike.Lib.X64.BlkW.triv fun _ _ h _ _ => h, fun q hq hra => ?_⟩
  refine allocW_WSOg hp hlo hΛ hlab hsite hcl hR' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) hra (fun _ _ => hq.toS) (fun w hw m hm => hmem q hq w hw m hm.1)
    (hS.alloc q hq hra) (hpl.alloc q hq hra) (hX0a q hq hra) ?_ (hctx q hq hra) hctr hheap hoff hnew hlt h64
  refine Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
  obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  have h0 := hc0J σe c' hJe
  rw [hq0] at h0
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h0
  · exact Spike.Lib.X64.WakePh.WcWfS.cf_hold h0

end Gen

end Spike.Lib.X64.WakePh.WcWfR

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.nodeW_unTp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.nodeW_unTp

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.wcSp0W_WSOg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.wcSp0W_WSOg

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.allocW_WSOg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.allocW_WSOg

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.wcPreW_WSOg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.wcPreW_WSOg
