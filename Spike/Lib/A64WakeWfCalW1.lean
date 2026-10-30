/-
**wake.w's `wc_main` callees inside `h1`'s level `W1W`** (AArch64): the
`hres`/`htcb` premises of `WakeWc.wcMidW_w1`, from `A64WakeWfCal`'s
`reserveW_wfG`/`tcbWG_wfG` at `Ly := RuntimeLayout.ofPlaceW hpw i`, the
canonical target's marks rewritten to `PhRec.μ Ly` (`AbOffW.marks_target`).

- `blkW_noK`, `nodeW_noK`, `reserveW_noK`, `tcbWG_noK`: a node family inside
  `W` at any move inside a weaker `W'` at no move.
- `reserveW_vac`: every `ReserveW` node holds at a frame condition that holds
  for no memory.
- `reserveW_wf`: `hres`. The nodes' `SFactsSt2` from `WcW.reserveW_wcG`; the
  reserve's control from the source's (`hSctl`, via `ResCtx`); the nodes'
  placement given (`hpl`).
- `tcbWG_wf`: `htcb`. The nodes' `SFactsSt2` (`hst`, e.g.
  `Tcb2CallW.tcb2W_ownGK`) and placement (`hpl`) given.
-/
import Spike.Lib.A64WakeWfCal
import Spike.Lib.A64WakeWcRes
import Spike.Lib.WakeOPremW
import Spike.Lib.A64WakeAbOffW
import Spike.Lib.A64SiteOfPlaceW

namespace Spike.Lib.A64.WakePh.CalWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout TcbWG)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.Rt.Reserve (ReserveW ntA)
open Spike.Lib.A64.Flow.WakeWc (rN rAR ResCtx)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib (Region FragS)

section NoK

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W W' : Frag isaLSE2} {K : State → State → Prop}

/-- A block inside `W` at `K` is inside a weaker `W'` at no move. -/
theorem blkW_noK {n : ND} {blk : List Directive} (h : BlkW W K exe endPc R F n blk) (hw : ∀ s c, W s c → W' s c) :
    BlkW W' (fun _ _ => False) exe endPc R F n blk := fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
  ⟨hw _ _ (h s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1, fun _ h => h⟩

/-- A node inside `W` at `K` is inside a weaker `W'` at no move. -/
theorem nodeW_noK {n : ND} (h : NodeW W K exe endPc R F n) (hw : ∀ s c, W s c → W' s c) :
    NodeW W' (fun _ _ => False) exe endPc R F n := fun s c hA => ⟨hw _ _ (h s c hA).1, fun _ h => h⟩

/-- `ReserveW` inside `W` at `K` is inside a weaker `W'` at no move. -/
theorem reserveW_noK {q : Spike.Lib.A64.Rt.Reserve.ResG} (h : ∀ i, ReserveW W K exe endPc R F q i)
    (hw : ∀ s c, W s c → W' s c) : ∀ i, ReserveW W' (fun _ _ => False) exe endPc R F q i := by
  intro i; have h := h i
  cases i <;> dsimp only [ReserveW] at h ⊢ <;> first | exact blkW_noK h hw | exact nodeW_noK h hw

/-- `TcbWG` inside `W` at `K` is inside a weaker `W'` at no move. -/
theorem tcbWG_noK {q : Spike.Lib.A64.Rt.TcbGG} (h : ∀ i, TcbWG W K exe endPc R F q i)
    (hw : ∀ s c, W s c → W' s c) : ∀ i, TcbWG W' (fun _ _ => False) exe endPc R F q i := by
  intro i; have h := h i
  cases i <;> dsimp only [TcbWG] at h ⊢ <;> first | exact blkW_noK h hw | exact nodeW_noK h hw

/-- **`ReserveW` at a frame condition holding for no memory.** -/
theorem reserveW_vac {q : Spike.Lib.A64.Rt.Reserve.ResG} (hF : ∀ m, ¬ F m) :
    ∀ i, ReserveW W K exe endPc R F q i := by
  intro i
  cases i <;> dsimp only [ReserveW] <;>
    first
    | exact fun _ _ _ _ _ _ _ _ hF' => (hF _ hF').elim
    | exact fun _ _ ⟨_, _, _, _, _, _, hF', _⟩ => (hF _ hF').elim

end NoK

section W1

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option maxHeartbeats 1600000 in
/-- **`wcMidW_w1`'s `hres`**: the reserve's nodes inside `W1W … l b n` at
no frames, for every frame ghost and control returning to `.sp3`, in
`wc_main`'s region `R` (its frame `[-128, 0]`). The source's controls are
not `main`'s `ret` and their runs are well formed (`hSctl`); the counter
`scc_rt_nthreads` is apart from the runtime's words (`hsep`), mapped (`hmN`),
unmapped under `F` (`hunN`), off wake's arena and not its counter word
(`hoffN`); the nodes' frames are placed (`hpl`). -/
theorem reserveW_wf (E : Scc.Sem.Entry)
    (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) (hpg : o.prog = wakeProg) (hlo : (Ly).Λ.code.lo = lo)
    (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    {S : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hSctl : ∀ l A c, S l A c → (∀ a, c.term ≠ .ret a) ∧ RunWf wakeSrc c [])
    (hsep : ntA (Ly).lab ≠ (Ly).pnA ∧ ntA (Ly).lab ≠ (Ly).lockA ∧ ntA (Ly).lab ≠ (Ly).freeNA ∧
      ntA (Ly).lab ≠ (Ly).nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨ntA (Ly).lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none)
    (hoffN : ¬ ((WakeOD.arW hpw i).heap ≤ (ntA (Ly).lab).toNat ∧
        (ntA (Ly).lab).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨ntA (Ly).lab, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hpl : ∀ g : Spike.Lib.A64.Flow.Reserve.G × Ctl, g.1.ra = ((Ly).lab ".L21_wc_main.sp3").toBitVec →
      ∀ nd, ReserveW (fun s c => PlacedSE (Ly).Λ (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b)
          s c []) (fun _ _ => False) (Ly).exe (Ly).endPc (rAR R)
        (fun m => F m ∧ CallerCells R (-80) (-48) 0 m ∧ ResCtx (Ly).lab R (rN ms (Ly).lab J0 S .call).J g m)
        ⟨g.1, 0#64, g.2⟩ nd) :
    ∀ g : Spike.Lib.A64.Flow.Reserve.G × Ctl, g.1.ra = ((Ly).lab ".L21_wc_main.sp3").toBitVec →
      ∀ nd, ReserveW (fun s c => WakeOPremW.W1W hpw i E Dt Ctx ls0 l b n s c []) (fun _ _ => False)
        (Ly).exe (Ly).endPc (rAR R)
        (fun m => F m ∧ CallerCells R (-80) (-48) 0 m ∧ ResCtx (Ly).lab R (rN ms (Ly).lab J0 S .call).J g m)
        ⟨g.1, 0#64, g.2⟩ nd := by
  intro g hra
  have hlab : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hpw i
  have hpL : (Ly).prog = wakeProg := hpg
  by_cases hS : ∃ l' A', S l' A' g.2
  · obtain ⟨l', A', hs⟩ := hS
    have hc := hSctl _ _ _ hs
    obtain ⟨hR', hal'⟩ := Spike.Lib.A64.Rt.StartU.callee_facts (kc := -80) (lo' := -48) hR hal
      (by omega) (by decide) (by omega) (by decide)
    have hst0 := Spike.Lib.A64.WakePh.WcW.reserveW_wcG (Λ := (Ly).Λ) (rS := ⟨0, 0⟩)
      (F := fun m => F m ∧ CallerCells R (-80) (-48) 0 m ∧ ResCtx (Ly).lab R (rN ms (Ly).lab J0 S .call).J g m) hpL hlo hΛ hlab hsite hsep hR'
      hal' (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) g hra hmN
      (fun m hm => hunN m hm.1)
    have hW := reserveW_wfG (Dt := Dt) (ar := WakeOD.arW hpw i) (p := wakeSrc) (Cl := WakeOD.ClW hpw i)
      (Ctx := fun _ _ _ => False) (lsize := Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls0) l n)
      (fs := []) hpL hlo hΛ hlab hsite (fun _ h => h.2) hR' hal' (by simp [Spike.Lib.Region.callee])
      (by simp [Spike.Lib.Region.callee]) ⟨g.1, 0#64, g.2⟩ hra ⟨fun _ => hc.1, hc.2⟩ (fun m hm => hunN m hm.1)
      hoffN (reserveW_noK hst0 fun _ _ h => h) (hpl g hra)
    intro nd
    unfold WakeOPremW.W1W Spike.Lib.A64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
    exact reserveW_noK hW (fun _ _ h => h) nd
  · refine reserveW_vac fun m hm => hS ?_
    obtain ⟨_, _, c, _, ⟨⟨l', A', hs, _⟩, _⟩, ⟨hc, _⟩, _⟩ := hm.2.2
    exact ⟨l', A', by rw [← show c = g.2 from hc]; exact hs⟩

set_option maxHeartbeats 1600000 in
/-- **`tcbWG_wf` at one source control `c0` and ghost `g`**, `hst`/`hpl` at those. -/
theorem tcbWG_wf_pt (E : Scc.Sem.Entry)
    (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) (hpg : o.prog = wakeProg) (hlo : (Ly).Λ.code.lo = lo)
    (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    {R : Region} {F : MachineData → Prop} {S : WeakMem.AllocLabel → Nat → Ctl → Prop} {K' : State → State → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -272) (hhi : 0 ≤ R.hi)
    (hSctl : ∀ l A c, S l A c → (∀ a, c.term ≠ .ret a) ∧ RunWf wakeSrc c [])
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hoffP : ¬ ((WakeOD.arW hpw i).heap ≤ (Ly).pnA.toNat ∧
        (Ly).pnA.toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pnA, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none)
    (hoffH : ¬ ((WakeOD.arW hpw i).heap ≤ ((Ly).pinA + 96#64).toNat ∧
        ((Ly).pinA + 96#64).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pinA + 96#64, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (c0 : Ctl) (hS : ∃ l' A', S l' A' c0) (g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G)
    (hra : g.ra = ((Ly).lab ".L21_wc_main.sp4").toBitVec)
    (hst : ∀ nd, TcbWG (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (ownG (Ly) (ntA (Ly).lab)) s) K'
        (Ly).exe (Ly).endPc (R.callee (-80) (-192) 0) F (Tcb2Call.tcb2Q g c0) nd)
    (hpl : ∀ nd, TcbWG (fun s c => PlacedSE (Ly).Λ (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b)
        s c []) (fun _ _ => False) (Ly).exe (Ly).endPc (R.callee (-80) (-192) 0) F (Tcb2Call.tcb2Q g c0) nd) :
    ∀ nd, TcbWG (fun s c => WakeOPremW.W1W hpw i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe
      (Ly).endPc (R.callee (-80) (-192) 0) F (Tcb2Call.tcb2Q g c0) nd := by
  have hlab : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hpw i
  have hpL : (Ly).prog = wakeProg := hpg
  obtain ⟨l', A', hs⟩ := hS
  have hc := hSctl _ _ _ hs
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.Rt.StartU.callee_facts (kc := -80) (lo' := -192) hR hal
    (by omega) (by decide) (by omega) (by decide)
  have hW := tcbWG_wfG (Dt := Dt) (ar := WakeOD.arW hpw i) (p := wakeSrc) (Cl := WakeOD.ClW hpw i)
    (Ctx := fun _ _ _ => False) (lsize := Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls0) l n)
    (fs := []) hpL hlo hΛ hlab hsite (fun _ h => h.2) hR' hal' (by show (-192 : Int) ≤ -192; omega)
    (by show (0 : Int) ≤ 0; omega) g c0 hra ⟨fun _ => hc.1, hc.2⟩ hunP hoffP hunH hoffH
    (tcbWG_noK hst fun _ _ h => h)
    hpl
  intro nd
  unfold WakeOPremW.W1W Spike.Lib.A64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
  rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
  exact tcbWG_noK hW (fun _ _ h => h) nd

/-- **`wcMidW_w1`'s `htcb`**: the second TCB's `scc_rt_alloc_tcb` nodes
inside `W1W … l b n` at no frames, at every control of the source
(`hSctl`) and ghost returning to `.sp4`, in `wc_main`'s region `R` (the
callee's frame `[-272, 0]`). The nodes' `SFactsSt2` (`hst`, at any move)
and placement (`hpl`) are given; the counter `scc_rt_pinned_next` and the
header word `scc_rt_pinned + 96` are unmapped under `F` (`hunP`, `hunH`),
off wake's arena and not its counter word (`hoffP`, `hoffH`). -/
theorem tcbWG_wf (E : Scc.Sem.Entry)
    (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) (hpg : o.prog = wakeProg) (hlo : (Ly).Λ.code.lo = lo)
    (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    {R : Region} {F : MachineData → Prop} {S : WeakMem.AllocLabel → Nat → Ctl → Prop} {K' : State → State → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -272) (hhi : 0 ≤ R.hi)
    (hSctl : ∀ l A c, S l A c → (∀ a, c.term ≠ .ret a) ∧ RunWf wakeSrc c [])
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hoffP : ¬ ((WakeOD.arW hpw i).heap ≤ (Ly).pnA.toNat ∧
        (Ly).pnA.toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pnA, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none)
    (hoffH : ¬ ((WakeOD.arW hpw i).heap ≤ ((Ly).pinA + 96#64).toNat ∧
        ((Ly).pinA + 96#64).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pinA + 96#64, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hst : ∀ c0, (∃ l' A', S l' A' c0) →
      ∀ g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G, g.ra = ((Ly).lab ".L21_wc_main.sp4").toBitVec →
      ∀ nd, TcbWG (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (ownG (Ly) (ntA (Ly).lab)) s) K'
        (Ly).exe (Ly).endPc (R.callee (-80) (-192) 0) F (Tcb2Call.tcb2Q g c0) nd)
    (hpl : ∀ c0, (∃ l' A', S l' A' c0) →
      ∀ g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G, g.ra = ((Ly).lab ".L21_wc_main.sp4").toBitVec →
      ∀ nd, TcbWG (fun s c => PlacedSE (Ly).Λ (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b)
          s c []) (fun _ _ => False) (Ly).exe (Ly).endPc (R.callee (-80) (-192) 0) F (Tcb2Call.tcb2Q g c0) nd) :
    ∀ c0, (∃ l' A', S l' A' c0) →
      ∀ g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G, g.ra = ((Ly).lab ".L21_wc_main.sp4").toBitVec →
      ∀ nd, TcbWG (fun s c => WakeOPremW.W1W hpw i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe
        (Ly).endPc (R.callee (-80) (-192) 0) F (Tcb2Call.tcb2Q g c0) nd :=
  fun c0 hS g hra => tcbWG_wf_pt hpw i E Dt Ctx ls0 l b n hpg hlo hpa hR hal hRlo hhi hSctl hunP hoffP hunH hoffH
    c0 hS g hra (hst c0 hS g hra) (hpl c0 hS g hra)

end W1

end Spike.Lib.A64.WakePh.CalWf

/-- info: 'Spike.Lib.A64.WakePh.CalWf.reserveW_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.CalWf.reserveW_wf

/-- info: 'Spike.Lib.A64.WakePh.CalWf.tcbWG_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.CalWf.tcbWG_wf

/-- info: 'Spike.Lib.A64.WakePh.CalWf.tcbWG_wf_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.CalWf.tcbWG_wf_pt
