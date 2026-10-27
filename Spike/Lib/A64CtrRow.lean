/-
**The counter's add at a node gives the consumer's `CtrRow`** (AArch64):
the premises of `ctr_ndW` (`Spike/Lib/A64AllocNodes.lean`) at a state of
the node give `CtrRow` (`Spike/Lib/A64ConsumerA.lean`) landing in the
node's successors (`Next`), the obligation `WrOkA.ctr` of the consumer at
the allocator's counter add.

- `ctrRow_nd`: the rule.
- `Alloc.ctrRow_alloc`: at `scc_rt_alloc`'s counter add (`Alloc.N .rmw`),
  landing in the allocator's nodes and exits (`seg_allocW_at`'s).
-/
import Spike.Lib.A64Alloc
import Spike.Lib.A64ConsumerA

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64ConsumerA (CtrRow)

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **`CtrRow` at a state of the counter's add node** `ld<add><k> Xs, Xt,
[Xn]`, from `ctr_ndW`'s premises (`hcode`, `hedge`): the row lands in the
node's successors. -/
theorem ctrRow_nd {n : ND} {k : RmwKind} {rs rt b : XReg} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldopDir .ADD k rs rt b])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (nn : Nat),
        c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some nn ∧
        c.hold = none ∧ σ.regs.getRegOrZr (.low (.reg rs) .W64) = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt (old.setWidth 64) σ⟩
            (holdCtr ms c (old.setWidth 64)))
    {s : State} {c : Ctl} (hAt : At exe endPc R F n s c) :
    CtrRow ms (Next exe endPc R F N E) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hc : CellAt s (ldopDir .ADD k rs rt b) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, hrt, hmp, hdm, x, a, τ, e, ta, ws, nn, ht, hev, hnn, hh, hrs, hX⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = BitVec.ofNat 64 ms.ctr := by rw [hA.regs]; exact hb
  have hex := exec_ldop hc (by rw [hb']; exact hdm)
  rw [hb', access_agrees (agrees_of_decls hdc _ _)] at hex
  refine ⟨k, _, _, x, a, τ, e, ta, ws, nn, hex, hrt, hmp, ht, hev, hnn, hh, fun old => ?_,
    fun old hG _ hle => ?_⟩
  · rw [hA.regs, hrs, add_apply]
  obtain ⟨hG', hL⟩ := hX old hG hle
  refine ⟨hG', ?_⟩
  have hA' : Abs R (n.o.kill rt)
      { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) }
      (ldStep rt (old.setWidth 64) σ) := by
    refine ⟨by simp only [ldStep, hA.regs], hA.status, ?_, hA.slot⟩
    exact hA.so.killZ (.low (.reg rt) .W64) (old.setWidth 64)
  have hD' : F { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s 4 { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) },
        n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' hD'⟩

end Spike.Lib.A64.Flow

namespace Spike.Lib.A64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64ConsumerA (CtrRow)

/-- **`CtrRow` at `scc_rt_alloc`'s counter add** for the call `q` (its
premises `hq`, its code `hcode`, the counter unmapped under `F`): the row
lands in the allocator's nodes and exits. -/
theorem ctrRow_alloc {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {q : Call} (hF : FStable R F)
    (hq : q.OK ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hmem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {s : State} {c : Ctl} (hAt : At exe endPc R F (N (_root_.Executable.labels exe).label ms q .rmw) s c) :
    CtrRow ms (Next exe endPc R F (N (_root_.Executable.labels exe).label ms q)
      (E (_root_.Executable.labels exe).label ms q lbl)) s c :=
  ctrRow_nd hF (fun s he hn => hcode.rmw s he hn) (fun m σ c hA hD hJ => by
    obtain ⟨⟨rfl, hF, hn28⟩, h10, h9⟩ := hJ
    exact ⟨h10, hq.rt, hq.mp, hmem _ hD, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, hq.term, hq.ev,
      hq.num, hq.hold, by rw [getRegOrZr_x]; exact h9, fun old hG hle =>
        ⟨hq.grow old hG hle, .inl ⟨AN.n4, rfl, rfl, _, rfl, hle, hF, hn28, rfl⟩⟩⟩) hAt

end Spike.Lib.A64.Alloc
