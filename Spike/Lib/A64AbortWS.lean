/-
**The AArch64 overflow abort at depth, the source held back at depth 0**
(`Spike/Lib/A64AbortW.lean`'s `seg_localW_lag` at frames).

A function's `.abort_overflow` block reached at frames `fs` (a callee's
body under its callers' frames) is, after `SegWS.lag`
(`Spike/Lib/SegLagS.lean`), a pair at depth 0 at the source control `cS` a
frame run reaches the block's control and frames from (`LagS p (· = cS)`).
The abort does not return, so the source is not advanced: the segment at
`fs` is `seg_localW_adv` with the empty local run, lifted to frames `fs`
(`SegWS.liftS`), its entry reached from the held-back pair by the frame run
(`SegWS.pre_run`).

- `seg_localWS_lag`: the block held back at depth 0, given `seg_localW_adv`'s
  hypotheses at `fs` (the block's and the abort path's states inside `W` at
  `fs`) and `W` at the held-back pair (`hWl`).
- `lb_take_slot`: the block's cells before each of its instructions are the
  node's.
- `blkW_mapF`, `nodeW_mapF`, `StubW.mapF`: the abort path's obligations
  moved from `W` to `W'` at its source control `c0` in the frame condition
  (the stub's `write` rebuilt by `seg_svcW`, its state not moved from
  outside, `hKs`).
-/
import Spike.Lib.A64AbortW
import Spike.Lib.A64StubW
import Spike.Lib.SegLagS

namespace Spike.Lib.A64.Abort.Local

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A function's `.abort_overflow` block at frames `fs`, held back at
depth 0** (the post of a segment at depth after `SegWS.lag`): from the block
at `fs` with the source held back at `cS` (`LagS p (· = cS)`),
`seg_localW_adv` under the memory side at `fs` with the source not advanced,
its states inside `W` at `fs` (`hW`, `hstub`), and the held-back pairs inside
`W` (`hWl`). -/
theorem seg_localWS_lag {W : FragS isaLSE2} {K : State → State → Prop} {Q : FragS isaLSE2} {fr : Int}
    {pcA : Int64} {J : Flow.AS → Ctl → Prop} {fs : List TermRun.Frame} {cS : Ctl}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -fr - 48) (hhi : 0 ≤ R.hi)
    (hkc : -fr < R.hi) (h16 : fr % 16 = 0) (hK : (ms fs).K = some Scc.Sem.A64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcA lb)
    (hW : BlkW (fun s c => W s c fs) K exe endPc R F (LN (_root_.Executable.labels exe).label fr pcA J false) lb)
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → R' = R.callee (-fr) (-48) 0 →
      ∀ c0, (∃ σ0, J σ0 c0) →
      (∀ m, F' m → ∃ mC σC σ0, Flow.Abs R ⟨-fr, []⟩ mC σC ∧ σC.slot = σ0.slot ∧ J σ0 c0 ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -fr) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      StubW (fun s c => W s c fs) K p lbl (ms fs) exe endPc R' F' c0)
    (hWl : ∀ s c', At exe endPc R F (LN (_root_.Executable.labels exe).label fr pcA J false) s c' →
      FrameRun p (cS, []) (c', fs) → W s cS []) :
    SegWS W K p lbl ms
      (LagS p (· = cS) ((At exe endPc R F (LN (_root_.Executable.labels exe).label fr pcA J false)).at fs)) Q := by
  have h0 : SegW (fun s c => W s c fs) K p lbl (ms fs)
      (At exe endPc R F (LNa (_root_.Executable.labels exe).label fr pcA J J false)) (fun _ _ => False) :=
    seg_localW_adv hF hR hal hlo hhi hkc h16 hK hcode hW (fun _ c hJ => ⟨c, .refl c, hJ⟩) hstub
  refine ((SegWS.liftS fs h0 fun _ _ h => h).mono_post fun _ _ _ h => h.1.elim).pre_run ?_
  rintro s c _ ⟨rfl, rfl, c', fs', ⟨hA, rfl⟩, hr⟩
  exact ⟨hWl s c' hA hr, c', _, hr, hA, rfl⟩

/-- **The block's cells before each of its instructions are the node's**
(the `movz` writes no cell). -/
theorem lb_take_slot (lab : Label → Int64) (pc : Int64) (o : SO) (σ : Flow.AS) {k : Nat} (hk : k < lb.length)
    (k' : Int) : (Flow.arun lab (lb.take k) ⟨pc, o, σ⟩).σ.slot k' = σ.slot k' := by
  rcases k with _ | _ | k
  · simp [Flow.arun]
  · simp [lb, Flow.arun, Flow.dstep, Flow.classify, AI.tgt, AI.so]
    rfl
  · exact absurd hk (by simp [lb])

/-- **A block's states moved from `W` to `W'`** at a node whose controls
are `c0` (`hJ`), in a stable frame condition (`hF`). -/
theorem blkW_mapF {W W' : Frag isaLSE2} {K : State → State → Prop} {n : ND} {blk : List Directive} {c0 : Ctl}
    (hF : FStable R F) (h : BlkW W K exe endPc R F n blk) (hJ : ∀ σ c, n.J σ c → c = c0)
    (hmap : ∀ s : State, W s c0 → F s.st.1 → W' s c0) : BlkW W' K exe endPc R F n blk := by
  intro s σ c he hn hd hpc hA hD hJn k hk m hA' hDF
  obtain ⟨hw, hK⟩ := h s σ c he hn hd hpc hA hD hJn k hk m hA' hDF
  obtain rfl := hJ σ c hJn
  exact ⟨hmap _ hw (hF _ _ hD hDF), hK⟩

/-- **A node's states moved from `W` to `W'`**, as `blkW_mapF`. -/
theorem nodeW_mapF {W W' : Frag isaLSE2} {K : State → State → Prop} {n : ND} {c0 : Ctl}
    (h : NodeW W K exe endPc R F n) (hJ : ∀ σ c, n.J σ c → c = c0)
    (hmap : ∀ s : State, W s c0 → F s.st.1 → W' s c0) : NodeW W' K exe endPc R F n := by
  intro s c hAt
  obtain ⟨hw, hK⟩ := h s c hAt
  obtain ⟨-, -, -, -, σ, -, hD, hJn⟩ := hAt
  obtain rfl := hJ σ c hJn
  exact ⟨hmap _ hw hD, hK⟩

/-- **The abort path's obligations moved from `W` to `W'`** at its source
control `c0` in the frame condition (`hmap`): the nodes' states mapped, the
stub's `write` rebuilt (`seg_svcW`) from its states inside `W` (the entry
of `StubW.svc`), none moved from outside (`hKs`). -/
theorem StubW.mapF {W W' : Frag isaLSE2} {K : State → State → Prop} {c0 : Ctl} {ms₀ : MemSide isaLSE2}
    (hK : ms₀.K = some Scc.Sem.A64.abi) (hF : FStable R F) (h : StubW W K p lbl ms₀ exe endPc R F c0)
    (hmap : ∀ s : State, W s c0 → F s.st.1 → W' s c0)
    (hKs : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .svc) s c →
      ∀ s', ¬ K s s') :
    StubW W' K p lbl ms₀ exe endPc R F c0 := by
  have hsvcW : NodeW W' K exe endPc R F
      (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .svc) := by
    intro s c hAt
    obtain ⟨inv, hP, hiW, -⟩ := h.svc
    have hw := hiW s c (hP s c hAt)
    obtain ⟨-, -, -, -, σ, -, hD, ⟨rfl, -⟩⟩ := id hAt
    exact ⟨hmap s hw hD, hKs s c hAt⟩
  exact ⟨h.dcode, blkW_mapF hF h.de (fun _ _ h => h.1) hmap, blkW_mapF hF h.dt1 (fun _ _ h => h.1) hmap,
    blkW_mapF hF h.dg1 (fun _ _ h => h) hmap, h.scode, blkW_mapF hF h.se (fun _ _ h => h) hmap,
    nodeW_mapF h.sn1 (fun _ _ h => h) hmap, nodeW_mapF h.sn1b (fun _ _ h => h) hmap,
    blkW_mapF hF h.sn2 (fun _ _ h => h) hmap, blkW_mapF hF h.sn5 (fun _ _ h => h) hmap,
    nodeW_mapF h.sex (fun _ _ h => h.1) hmap, StubW.seg_svcW hK hF h.scode.svc hsvcW, h.ab⟩

end Proof

end Spike.Lib.A64.Abort.Local
