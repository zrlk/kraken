/-
**hello.w's `wc_main` from `.sp6` to its `clone`'s `svc`, inside `W`**
(AArch64), in any valid layout of `helloProg`: the
blocks, nodes and edges of `Spike/Lib/A64HelloWcSp6.lean` composed with the
fence row,

    .sp6:      sp6AH                    (sp6AH_edge)
    .sp6+44:   dmb ish                  -- row: a fence, the source stuttering (dmb_ndW)
    .sp6+48:   cloneArgsH               (cloneArgsH_edge)
    .sp6+100:  svc #0                   -- the exit `wcNSH`

wake's `.sp6` part of `wake_wc_sp4_call_segW` at hello's frame (`oWH`, the
region's low end at most `-144`). The entry `wcN6H` is the exit of
`A64HelloWcSp3`'s segment (`.sp4`, the tid word, `thread_init`).

- `XS`, `sN`: the nodes from `.sp6` to the `svc`;
- `WcSp6W`: their states inside `W`, none moved by `K`; `WcSp6W.triv`;
- `hit_of_edgeH`: a block's edge in hello's frame is a hit;
- `hello_wc_sp6_segW`: the segment.
-/
import Spike.Lib.A64HelloWcSp6
import Spike.Lib.A64WakeWcSp4Seg

namespace Spike.Lib.A64.HelloPh.WcSp6

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.WakePh.WcSp4 (fenceB)
open Spike.Lib.A64.Flow.WakeWc (fenceB_eq)
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open SccCode (helloProg)

set_option linter.unusedSimpArgs false

/-- `.sp6`'s nodes before the `svc`. -/
inductive XS where
  | n6 | n6f | n6a

/-- **The nodes from `.sp6` to the `svc`.** -/
def sN (lab : Label → Int64) (c0 : Ctl) (t k : BitVec 64) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) : XS → ND
  | .n6 => wcN6H lab c0 t k sl me cA fr
  | .n6f => wcN6fH lab c0 t k sl me cA fr
  | .n6a => wcN6aH lab c0 t k sl me cA fr

/-- **`.sp6`'s states to the `svc` inside `W`**, none moved by `K`. -/
structure WcSp6W (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (t k : BitVec 64)
    (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    Prop where
  n6 : BlkW W K exe endPc R F (wcN6H (_root_.Executable.labels exe).label c0 t k sl me cA fr) sp6AH
  n6f : NodeW W K exe endPc R F (wcN6fH (_root_.Executable.labels exe).label c0 t k sl me cA fr)
  n6a : BlkW W K exe endPc R F (wcN6aH (_root_.Executable.labels exe).label c0 t k sl me cA fr) cloneArgsH

/-- From `.sp6` to the `svc` inside the trivial predicate, with no outside moves. -/
theorem WcSp6W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} :
    WcSp6W (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 t k sl me cA fr :=
  ⟨BlkW.triv, fun _ _ _ => ⟨trivial, fun _ h => h⟩, BlkW.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- A block's edge in hello's frame (`EdgeH`) is a hit at the target node. -/
theorem hit_of_edgeH {lab : Label → Int64} {blk : List Directive} {n n' : ND} {σ : Spike.Lib.A64.Flow.AS}
    {c : Ctl} (h : EdgeH lab blk n n' σ c) (ho : n'.o = oWH) :
    Hit n' (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, oWH, σ⟩) c :=
  ⟨h.1.symm, by rw [h.2.1, ho]; rfl, h.2.2⟩

/-- **`wc_main` from `.sp6` to its `clone`'s `svc` is one segment inside
`W`** in any valid layout of `helloProg`: from `wcN6H` (the child's stack
top `k` in `x0`, the TCB `t` at `[sp, #56]`, the frame's words, the source
at `c0`) to `wcNSH` (`clone(855808, k, 0, t, 0)`, `x9 .. x14` the slice's
first register and the packet). The frame condition `F` is stable in `R`
(`hF`), `R`'s low end at most `-144`. Its states lie in `W` (`hW`). -/
theorem hello_wc_sp6_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (hW : WcSp6W W K exe endPc R F c0 t k sl me cA fr) :
    SegW W K p lbl ms (At exe endPc R F (wcN6H (_root_.Executable.labels exe).label c0 t k sl me cA fr))
      (At exe endPc R F (wcNSH (_root_.Executable.labels exe).label c0 t k sl me cA fr)) := by
  have hin := hello_wcSp6In
  simp only [wcSp6In, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨b6, b6f⟩, b6a⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have hB : SegW W K p lbl ms (At exe endPc R F (sN lab c0 t k sl me cA fr .n6))
      (fun s c => ∃ x : Unit, At exe endPc R F ((fun _ => wcNSH lab c0 t k sl me cA fr) x) s c) := by
    refine fn_segW (N := sN lab c0 t k sl me cA fr) (fun i => ?_) XS.n6
    cases i
    case n6 =>
      refine seg_ndW (by simp [sp6AH]) sp6AH_ok hF hR hal hlo hhi (code_of hp hend b6 (ofNat4_zero _))
        hW.n6 fun σ c hJ => ⟨c, .refl c, .inl ⟨XS.n6f, hit_of_edgeH (sp6AH_edge hJ) rfl⟩⟩
    case n6f =>
      refine dmb_ndW (code_of hp hend (fenceB_eq ▸ b6f) rfl) hW.n6f fun σ c hJ =>
        ⟨c, .loc (.refl c), .inl ⟨XS.n6a, ?_, rfl, hJ⟩⟩
      show lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 12) =
        lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 11) + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl
    case n6a =>
      refine seg_ndW (by simp [cloneArgsH]) cloneArgsH_ok hF hR hal hlo hhi (code_of hp hend b6a rfl)
        hW.n6a fun σ c hJ => ⟨c, .refl c, .inr ⟨(), hit_of_edgeH (cloneArgsH_edge hJ) rfl⟩⟩
  exact hB.mono_post fun _ _ ⟨_, h⟩ => h

end Seg

/-- info: 'Spike.Lib.A64.HelloPh.WcSp6.hello_wc_sp6_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_wc_sp6_segW

end Spike.Lib.A64.HelloPh.WcSp6
