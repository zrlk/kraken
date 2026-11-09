/-
**wake.w's worker on x86-64, a fact at every node's states** (the x64 twin
of `Spike/Lib/A64WakeWorkerLabelsNNA.lean`): the prologues and the
whole-function segments of `Spike/Lib/X64WakeWorkerLabelsNN.lean` with the
fragment `Z` at every node's states (`XProW` at the prologues, `NodeZA` per
node, the callees' at every frame condition seeing their call: `CallerF`).

- `ThrZA`: `Z` at every node's states of `scc_rt_thr_worker`'s run;
  `ThrZ.toA`: a fact of the pc and the control at every node (`ThrZ`) is one
  at every node's states; `XProW.monoJ`: a prologue's obligation at a
  stronger entry invariant.
- `wc_prologue_segNNA`, `thr_prologue_segNNA`, `seg_wcWorkerXNNA`,
  `seg_thrWorkerNNA`: the `…NN` segments with `hz : XProW …`, `hZW`/`hZU`
  over `NodeZA`, `seg_thrWorkerNNA`'s bundled as `ThrZA`.

**Unlike AArch64** (forced by the x64 shape):

- the prologues' obligations are `XProW` (the x64 prologue's five nodes:
  `push`/`mov`, `lea`, the `%fs` load, `cmp`/`jb`, the frame), not `ProW`.
- `wc_worker`'s entry invariant inside `seg_wcWorkerX` also knows `%rsp` at
  the region's base (`At.rspAt`); `seg_wcWorkerXNNA` takes `hz` at
  `wcJE ∧ X` and weakens it (`XProW.monoJ`).
- the epilogue nodes reclaiming `%rbp` are at their executing offsets
  (`WkTailW.NA`, `ThrTailW.NA`), and `wc_worker`'s nodes at the callee
  region's base (`R'.addr 0`).
-/
import Spike.Lib.X64WakeWorkerLabelsNN
import Spike.Lib.X64WakeWorkerNNA

namespace Spike.Lib.X64.Flow.Worker.Wake.Labels

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Sem (ValRep)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk LimOk)

set_option linter.unusedSimpArgs false

/-- **`Z` at every node's states of `scc_rt_thr_worker`'s run** in the
region `R` with frame condition `F`: its prologue (`XProW`), its head, its
tail (`NodeZA`); `wc_worker`'s prologue and tail at every frame condition
seeing the head's call (`CallerF`) and every return frame; the unpark
callee at every frame condition seeing `wc_worker`'s call. -/
structure ThrZA (Z : Frag isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isa) (c0 c1 c2 c3 : Ctl) (A B tp sp0 : BitVec 64) : Prop where
  pro : XProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 32 8 ".Lscc_rt_thr_worker.stk" 5 9 3 2 4
      [(.rdi, -8, 4), (.rsi, -16, 4)] (thrJE c0 A B tp sp0)
  head : ∀ i, NodeZA Z exe endPc R F (ThrHeadW.tN (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0) (fun _ c => c = c1) i)
    (ThrHeadW.blkN i)
  wpro : ∀ (R' : Region) (F' : MachineData → Prop), CallerF R F (ThrHeadW.tN (_root_.Executable.labels exe).label
      (thrJ c0 A B tp sp0) (fun _ c => c = c1) .call) 0 (-72) 8 R' F' → ∀ rbp0 ra,
    XProW Z (fun _ _ => False) exe endPc R' F' ms ((_root_.Executable.labels exe).label "wc_worker") 16 8 ".Lwc_worker.stk" 5 9 3 2 4
      [(.rdi, -8, 4), (.rsi, -16, 4)] fun σ c => wcJE c1 A B rbp0 ra tp σ c ∧ σ.regs.rsp.toBitVec = sp0 - 48#64
  wk : ∀ (R' : Region) (F' : MachineData → Prop), CallerF R F (ThrHeadW.tN (_root_.Executable.labels exe).label
      (thrJ c0 A B tp sp0) (fun _ c => c = c1) .call) 0 (-72) 8 R' F' → ∀ rbp0 ra i,
    NodeZA Z exe endPc R' F' (WkTailW.NA (_root_.Executable.labels exe).label c1 c2 c3 A B rbp0 ra tp (R'.addr 0) i) (WkTailW.blkN i)
  unpk : ∀ (R' : Region) (F' : MachineData → Prop), CallerF R F (ThrHeadW.tN (_root_.Executable.labels exe).label
      (thrJ c0 A B tp sp0) (fun _ c => c = c1) .call) 0 (-72) 8 R' F' → ∀ rbp0 ra,
    ∀ (R'' : Region) (F'' : MachineData → Prop),
      CallerF R' F' (WkTailW.N (_root_.Executable.labels exe).label c1 c2 c3 A B rbp0 ra tp (R'.addr 0) .unpk) 0 (-40) 8 R'' F'' →
      ∀ rbp1 ra1 i, NodeZA Z exe endPc R'' F'' (Unpark.N (_root_.Executable.labels exe).label c2 c3 B rbp1 ra1 tp i) (Unpark.blkN i)
  tail : ∀ i, NodeZA Z exe endPc R F (ThrTailW.NA (_root_.Executable.labels exe).label c3 tp sp0 i) (ThrTailW.blkN i)

/-- A prologue's obligation at a stronger entry invariant. -/
theorem XProW.monoJ {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {pc0 Z lim : Int64} {L : String}
    {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)} {J J' : AS → Ctl → Prop}
    (h : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J) (hJ : ∀ σ c, J' σ c → J σ c) :
    XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J' :=
  ⟨fun s σ c he hn hd hpc hA hD h' => h.w0 s σ c he hn hd hpc hA hD (hJ σ c h'),
    fun s σ c he hn hd hpc hA hD ⟨σ0, h0, e⟩ => h.w1 s σ c he hn hd hpc hA hD ⟨σ0, hJ _ _ h0, e⟩,
    fun s c ⟨he, hn, hd, hpc, σ, hA, hD, σ0, h0, e⟩ => h.w2 s c ⟨he, hn, hd, hpc, σ, hA, hD, σ0, hJ _ _ h0, e⟩,
    fun s σ c he hn hd hpc hA hD ⟨σ0, v, h0, e⟩ => h.w3 s σ c he hn hd hpc hA hD ⟨σ0, v, hJ _ _ h0, e⟩,
    fun s σ c he hn hd hpc hA hD ⟨σ0, v, h0, e⟩ => h.w4 s σ c he hn hd hpc hA hD ⟨σ0, v, hJ _ _ h0, e⟩⟩

/-- A fact of the pc and the control at every node (`ThrZ`) is one at every
node's states. -/
theorem ThrZ.toA {Z : Frag isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isa} {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (h : ThrZ Z exe c0 c1 c2 c3 A B tp sp0) : ThrZA Z exe endPc R F ms c0 c1 c2 c3 A B tp sp0 where
  pro := XProW.ofPcs fun s σ c k hk => h.pro s σ c k (Nat.le_trans hk (by decide))
  head i := NodeZ.toA (h.head i)
  wpro _ _ _ rbp0 ra := XProW.ofPcs fun s σ c k hk he hpc hJ =>
    h.wpro rbp0 ra s σ c k (Nat.le_trans hk (by decide)) he hpc hJ.1
  wk R' _ _ rbp0 ra i := by cases i <;> exact NodeZ.toA (h.wk rbp0 ra (R'.addr 0) _)
  unpk _ _ _ _ _ _ _ _ rbp1 ra1 i := NodeZ.toA (h.unpk rbp1 ra1 i)
  tail i := by cases i <;> exact NodeZ.toA (h.tail _)

section ProNNA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Region} {F : MachineData → Prop} {Z : Frag isa}

/-- **`wc_prologue_seg` off the transfer sites, `Z` at the
prologue's states** (`XProW`). -/
theorem wc_prologue_segNNA (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lwc_worker.entry")
    (ho : SO.le nb.o (oF 16) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (16 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 16 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [(.rdi, -8, 4), (.rsi, -16, 4)] (xS1 σ).slot → nb.J σ' c)
    (hz : XProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "wc_worker") 16 8 ".Lwc_worker.stk" 5 9 3 2 4
      [(.rdi, -8, 4), (.rsi, -16, 4)] J) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofNNA hp hend wake_wcPro (by decide) hF hR
    (by have : (16 : Int64).toInt = 16 := by decide
        omega) hhi (by decide) hpc ho hedge hz

/-- **`thr_prologue_seg` off the transfer sites, `Z` at the
prologue's states** (`XProW`). -/
theorem thr_prologue_segNNA (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry")
    (ho : SO.le nb.o (oF 32) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 32 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [(.rdi, -8, 4), (.rsi, -16, 4)] (xS1 σ).slot → nb.J σ' c)
    (hz : XProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 32 8 ".Lscc_rt_thr_worker.stk" 5 9 3 2 4
      [(.rdi, -8, 4), (.rsi, -16, 4)] J) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofNNA hp hend wake_thrPro (by decide) hF hR
    (by have : (32 : Int64).toInt = 32 := by decide
        omega) hhi (by decide) hpc ho hedge hz

/-- **`seg_wcWorkerXNN` with `Z` at every node's states** (`XProW` at the
prologue, `NodeZA` per node; the unpark callee's at the frame conditions
seeing the call, `CallerF`). -/
theorem seg_wcWorkerXNNA (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {c0 c1 c2 : Ctl} {A B rbp0 ra tp : BitVec 64} {X : AS → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 A B rbp0 ra tp σ c → X σ →
      LimOk ms F (tp + (8 : Int64).toBitVec) (σ.regs.rsp.toBitVec - 8#64 - (16 : Int64).toBitVec))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    (hz : XProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "wc_worker") 16 8 ".Lwc_worker.stk" 5 9 3 2 4
      [(.rdi, -8, 4), (.rsi, -16, 4)] fun σ c => wcJE c0 A B rbp0 ra tp σ c ∧ X σ)
    (hZW : ∀ i, NodeZA Z exe endPc R F
      (WkTailW.NA (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) i) (WkTailW.blkN i))
    (hZU : ∀ (R' : Region) (F' : MachineData → Prop),
      CallerF R F (WkTailW.N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .unpk) 0 (-40) 8
        R' F' →
      ∀ rbp1 ra1 i, NodeZA Z exe endPc R' F' (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i)
        (Unpark.blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 A B rbp0 ra tp σ c ∧ X σ⟩)
      (fun s c => ∃ x, At exe endPc R F (WkTailW.E c2 rbp0 ra tp x) s c) := by
  refine (SegTC.seq (wc_prologue_segNNA hp hend hF hR (Int.le_trans hlo (by decide)) (by omega)
    (J := fun σ c => (wcJE c0 A B rbp0 ra tp σ c ∧ X σ) ∧ σ.regs.rsp.toBitVec = R.addr 0)
    (nb := WkTailW.N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .e)
    rfl (by show SO.le WkTailW.oI (oF 16) = true; decide) (fun σ c hJ => ?_)
    (XProW.monoJ hz fun _ _ h => h.1))
    (WkTailW.seg_wkTailWUNNA hF hR hlo hhi hdm ht hev hv htag hevb hvb hc1 (wkCode hp hend) hK hS htp4
      htu hhu hevu hvu hc2 (unpkCode hp hend (c0 := c0) (c1 := c1) (B := B) (rbp0 := rbp0) (ra := ra) (tp := tp))
      (hpentry hp) (hx14 hp) hZW hZU)).mono_pre fun _ _ h => At.rspAt h
  obtain ⟨⟨hJ, hX⟩, hsp⟩ := hJ
  have hl := hlim σ c hJ hX
  obtain ⟨rfl, hdi, hsi, hbp, h0, htp⟩ := hJ
  rw [htp]
  refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ?_⟩⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]; simp [xStSlots, xS1, upd_apply, hbp]
  · rw [hs]; simp [xStSlots, xS1, upd_apply, h0]
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdi]
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hsi]
  · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
  · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]

/-- **`seg_thrWorkerNN` with `Z` at every node's states** (`ThrZA`). -/
theorem seg_thrWorkerNNA {Q : Frag isa} (hp : Lays exe SccCode.wakeCells kp)
    (hend : endPc = endOf exe SccCode.wakeCells kp)
    {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -120) (hhi : 8 ≤ R.hi)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) (sp0 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (tp + (8 : Int64).toBitVec) (sp0 - 48#64 - 8#64 - (16 : Int64).toBitVec))
    (hsplit : LocalRun p c0 c1)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c1.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c1.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c1.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc2 : c2 = ⟨e1, (d, .unit, []) :: c1.env, none⟩)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c2.term = .let_ x (.ext .unpark au) e) (hhu : c2.hold = none)
    (hevu : TermRun.evalAt c2.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc3 : c3 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c2.env, none⟩)
    {ar : CoreTerm.At} (hret3 : c3.term = .ret ar)
    (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x0") tp tp)
    (hSx : StOk ms F (tp + 24#64) 1#64)
    (hZ : ThrZA Z exe endPc R F ms c0 c1 c2 c3 A B tp sp0) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE c0 A B tp sp0⟩) Q := by
  by_cases hsp : sp0 = R.addr 0
  case neg =>
    refine ⟨fun _ _ => False, fun s c h => ?_, fun _ _ h => h.elim, fun _ _ h => h.elim⟩
    obtain ⟨-, -, -, -, σ, -, -, hJ, hr⟩ := At.rspAt h
    exact hsp (hJ.2.2.2.2.symm.trans hr)
  subst hsp
  let lab := (_root_.Executable.labels exe).label
  refine SegTC.seq (thr_prologue_segNNA hp hend hF hR (Int.le_trans hlo (by decide)) (by omega)
    (nb := ThrHeadW.tN lab (thrJ c0 A B tp (R.addr 0)) (fun _ c => c = c1) .e)
    rfl (by show SO.le ThrHeadW.oI (oF 32) = true; decide) (fun σ c hJ => ?_) hZ.pro) ?_
  · obtain ⟨rfl, hdi, hsi, htp, hsp⟩ := hJ
    rw [htp]
    refine ⟨hlim.rt, hlim.mp, hlim.unmapped, fun v hv => ⟨by rw [hsp]; exact hlim.room v hv, fun σ' hr hs => ?_⟩⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdi]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hsi]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
      bv_omega
  refine SegTC.seq (ThrHeadW.seg_thrHeadWNNA (N := fun _ : Unit => ThrTailW.N lab c3 tp (R.addr 0) .x12)
    (E := (nofun : Empty → ND)) hF hR hlo hhi (fun σ c hJ => ⟨c1, by rw [hJ.1]; exact hsplit, rfl⟩)
    (thECode hp hend)
    (Ne := fun g : BitVec 64 × BitVec 64 => ⟨lab "wc_worker", ⟨0, []⟩,
      fun σ c => wcJE c1 A B g.1 g.2 tp σ c ∧ σ.regs.rsp.toBitVec = R.addr 0 - 48#64⟩)
    (Ex := fun g y => WkTailW.E c3 g.1 g.2 tp y)
    (fun R' F' hC g =>
      seg_wcWorkerXNNA hp hend hC.stab hC.ok hC.lo hC.hi
        (fun σ c _ hX => by rw [hX]; exact hlimW.mono fun m hm => (hC.sees m hm).1)
        (fun m hm => hdm m (hC.sees m hm).1) ht hev hv htag hevb hvb hc2 hK (hS.mono fun m hm => (hC.sees m hm).1)
        htp4 htu hhu hevu hvu hc3 (hZ.wpro R' F' hC g.1 g.2) (hZ.wk R' F' hC g.1 g.2) (hZ.unpk R' F' hC g.1 g.2))
    (fun _ => rfl) ?_ ?_ hZ.head) ?_
  · rintro σC c ⟨σ0, c0', ⟨-, h16, h24, htp, -, hsp⟩, hc, rfl⟩
    refine ⟨(_, _), rfl, ⟨hc, ?_, ?_, rfl, rfl, ?_⟩, ?_⟩ <;>
      simp [enter, ThrHeadW.thE_run, Reg64s.set64, Reg64s.get64, h16, h24, htp, hsp]
    bv_omega
  · rintro ⟨rbp1, ra1⟩ ⟨⟩ σC c σx c' σR ⟨σ0, c0', ⟨-, -, -, -, hbp, -⟩, -, rfl⟩ ⟨⟨-, -, -, hrb, hra, -⟩, -⟩
      ⟨hc', hrb', htp'⟩ hreg - - -
    refine .inl ⟨(), ?_, by show SO.le ThrTailW.oP ⟨-48 - 0 + 8, []⟩ = true; decide, hc', ?_, ?_⟩
    · show (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x0" = Int64.ofBitVec ra1
      have hra' : (enter (-48 - 0) (arun lab ThrHeadW.thE ⟨lab ".Lscc_rt_thr_worker.entry", ThrHeadW.oI, σ0⟩).σ).slot 0
        = ra1 := hra
      rw [← hra', hx12 hp]
      simp only [enter, ThrHeadW.thE_run, upd_apply]
      rfl
    · show σR.regs.fsBase.toBitVec = tp
      rw [hreg]; exact htp'
    · show σR.regs.rbp.toBitVec = _
      have h1 : σx.regs.get64 .rbp = rbp1 := hrb'
      have h2 : (enter (-48 - 0) (arun lab ThrHeadW.thE ⟨lab ".Lscc_rt_thr_worker.entry", ThrHeadW.oI, σ0⟩).σ).regs.rbp.toBitVec
        = rbp1 := hrb
      rw [hreg]; simp only [Reg64s.get64] at h1; rw [h1, ← h2]
      simp [enter, ThrHeadW.thE_run, Reg64s.set64, hbp]
  · exact (ThrTailW.seg_thrTailWNNA hF hR (Int.le_trans hlo (by decide)) hhi hK hT hown hSx hret3
      (thrCode hp hend) hZ.tail).mono_pre fun s c h => h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim

end ProNNA

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.Labels.seg_wcWorkerXNNA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_wcWorkerXNNA

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.Labels.seg_thrWorkerNNA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_thrWorkerNNA

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.Labels.ThrZ.toA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ThrZ.toA

end Spike.Lib.X64.Flow.Worker.Wake.Labels
