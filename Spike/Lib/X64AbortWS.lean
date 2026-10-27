/-
**The x86-64 overflow abort at depth, the source held back at depth 0**
(`Spike/Lib/X64AbortW.lean`'s `seg_localW_lag` at frames).

A function's `.ovf` block reached at frames `fs` (a callee's body under its
callers' frames) is, after `SegWS.lag` (`Spike/Lib/SegLagS.lean`), a pair at
depth 0 at the source control `cS` a frame run reaches the block's control
and frames from (`LagS p (· = cS)`). The abort does not return, so the
source is not advanced: the segment at `fs` is `seg_localW_adv` with the
empty local run, lifted to frames `fs` (`SegWS.liftS`), its entry reached
from the held-back pair by the frame run (`SegWS.pre_run`).

- `seg_localWS_lag`: the block held back at depth 0, given `seg_localW_adv`'s
  hypotheses at `fs` (the block's and the abort path's states inside `W` at
  `fs`) and `W` at the held-back pair (`hWl`).
- `lb_take_slot`: the block's cells before each of its instructions are the
  node's.
- `blkW_mapF`, `nodeW_mapF`, `StubW.mapF`: the abort path's obligations
  moved from `W` to `W'` at its source control `c0` in the frame condition
  (the stub's `write` rebuilt by `seg_syscallW`, its state not moved from
  outside, `hKs`).
-/
import Spike.Lib.X64AbortW
import Spike.Lib.X64StubW
import Spike.Lib.SegLagS

namespace Spike.Lib.X64.Abort.Local

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A function's `.ovf` block at frames `fs`, held back at depth 0** (the
post of a segment at depth after `SegWS.lag`): from the block at `fs` with
the source held back at `cS` (`LagS p (· = cS)`), `seg_localW_adv` under the
memory side at `fs` with the source not advanced, its states inside `W` at
`fs` (`hW`, `hstub`), and the held-back pairs inside `W` (`hWl`). -/
theorem seg_localWS_lag {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {o : SO} {pcA : Int64}
    {J : AS → Ctl → Prop} {fs : List TermRun.Frame} {cS : Ctl}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ o.sp - 40) (hhi : o.sp ≤ R.hi) (h8 : o.sp % 8 = 0)
    (hK : (ms fs).K = some Scc.Sem.X64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcA lb)
    (hW : BlkW (fun s c => W s c fs) K exe endPc R F (LN (_root_.Executable.labels exe).label o pcA J false) lb)
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -24 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → R' = R.callee (o.sp - 8 - 8) (-24) 16 →
      ∀ c0, (∃ σ0, J σ0 c0) →
      (∀ m, F' m → ∃ mC σC σ0, Abs R ⟨o.sp - 8, []⟩ mC σC ∧ (∀ k, k ≠ o.sp - 8 → σC.slot k = σ0.slot k) ∧
        J σ0 c0 ∧ ∀ k, R.Off k → ¬ R'.Off (k - (o.sp - 8 - 8)) →
          Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      StubW (fun s c => W s c fs) K p lbl (ms fs) exe endPc R' F' c0)
    (hWl : ∀ s c', At exe endPc R F (LN (_root_.Executable.labels exe).label o pcA J false) s c' →
      FrameRun p (cS, []) (c', fs) → W s cS []) :
    SegWS W K p lbl ms (LagS p (· = cS) ((At exe endPc R F (LN (_root_.Executable.labels exe).label o pcA J false)).at fs))
      Q := by
  have h0 : SegW (fun s c => W s c fs) K p lbl (ms fs)
      (At exe endPc R F (LNa (_root_.Executable.labels exe).label o pcA J J false)) (fun _ _ => False) :=
    seg_localW_adv hF hR hlo hhi h8 hK hcode hW (fun _ c hJ => ⟨c, .refl c, hJ⟩) hstub
  refine ((SegWS.liftS fs h0 fun _ _ h => h).mono_post fun _ _ _ h => h.1.elim).pre_run ?_
  rintro s c _ ⟨rfl, rfl, c', fs', ⟨hA, rfl⟩, hr⟩
  exact ⟨hWl s c' hA hr, c', _, hr, hA, rfl⟩

/-- **The block's cells before each of its instructions are the node's**
(the `movl` writes no cell). -/
theorem lb_take_slot (lab : Label → Int64) (pc : Int64) (o : SO) (σ : AS) {k : Nat} (hk : k < lb.length)
    (k' : Int) : (arun lab (lb.take k) ⟨pc, o, σ⟩).σ.slot k' = σ.slot k' := by
  rcases k with _ | _ | k
  · simp [arun]
  · simp [lb, arun, dstep, classify, AI.tgt, AI.so, AI.step, RegOnly, regRes, soReg, regDst, Reg.base, SO.kill,
      SO.write, Operation.interp, Operand.interp, MachineData.set, MachineData.setReg, Reg64s.set,
      ConstExpr.interp]
  · exact absurd hk (by simp [lb])

/-- **A block's states moved from `W` to `W'`** at a node whose controls
are `c0` (`hJ`), in a stable frame condition (`hF`). -/
theorem blkW_mapF {W W' : Frag isa} {K : State → State → Prop} {n : ND} {blk : List (Directive × Nat)} {c0 : Ctl}
    (hF : FStable R F) (h : BlkW W K exe endPc R F n blk) (hJ : ∀ σ c, n.J σ c → c = c0)
    (hmap : ∀ s : State, W s c0 → F s.st.1 → W' s c0) : BlkW W' K exe endPc R F n blk := by
  intro s σ c he hn hd hpc hA hD hJn k hk m hA' hDF
  obtain ⟨hw, hK⟩ := h s σ c he hn hd hpc hA hD hJn k hk m hA' hDF
  obtain rfl := hJ σ c hJn
  exact ⟨hmap _ hw (hF _ _ hD hDF), hK⟩

/-- **A node's states moved from `W` to `W'`**, as `blkW_mapF`. -/
theorem nodeW_mapF {W W' : Frag isa} {K : State → State → Prop} {n : ND} {c0 : Ctl}
    (h : NodeW W K exe endPc R F n) (hJ : ∀ σ c, n.J σ c → c = c0)
    (hmap : ∀ s : State, W s c0 → F s.st.1 → W' s c0) : NodeW W' K exe endPc R F n := by
  intro s c hAt
  obtain ⟨hw, hK⟩ := h s c hAt
  obtain ⟨-, -, -, -, σ, -, hD, hJn⟩ := hAt
  obtain rfl := hJ σ c hJn
  exact ⟨hmap _ hw hD, hK⟩

/-- **The abort path's obligations moved from `W` to `W'`** at its source
control `c0` in the frame condition (`hmap`): the nodes' states mapped, the
stub's `write` rebuilt (`seg_syscallW`) from its states inside `W` (the
entry of `StubW.sys`), none moved from outside (`hKs`). -/
theorem StubW.mapF {W W' : Frag isa} {K : State → State → Prop} {c0 : Ctl} {ms₀ : MemSide isa}
    (hK : ms₀.K = some Scc.Sem.X64.abi) (hF : FStable R F) (h : StubW W K p lbl ms₀ exe endPc R F c0)
    (hmap : ∀ s : State, W s c0 → F s.st.1 → W' s c0)
    (hKs : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .sys) s c →
      ∀ s', ¬ K s s') :
    StubW W' K p lbl ms₀ exe endPc R F c0 := by
  have hsysW : NodeW W' K exe endPc R F
      (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .sys) := by
    intro s c hAt
    obtain ⟨inv, hP, hiW, -⟩ := h.sys
    have hw := hiW s c (hP s c hAt)
    obtain ⟨-, -, -, -, σ, -, hD, ⟨rfl, -⟩⟩ := id hAt
    exact ⟨hmap s hw hD, hKs s c hAt⟩
  exact ⟨h.dcode, blkW_mapF hF h.de (fun _ _ h => h.1) hmap, blkW_mapF hF h.dt1 (fun _ _ h => h.1) hmap,
    blkW_mapF hF h.dg1 (fun _ _ h => h) hmap, h.scode, blkW_mapF hF h.se (fun _ _ h => h) hmap,
    nodeW_mapF h.sn1 (fun _ _ h => h) hmap, blkW_mapF hF h.sn2 (fun _ _ h => h) hmap,
    blkW_mapF hF h.sn5 (fun _ _ h => h) hmap, nodeW_mapF h.sex (fun _ _ h => h.1) hmap,
    StubW.seg_syscallW hK hF h.scode.sys hsysW, h.ab⟩

end Proof

end Spike.Lib.X64.Abort.Local
