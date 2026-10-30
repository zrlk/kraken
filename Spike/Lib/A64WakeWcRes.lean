/-
**wake.w's `wc_main` from the box's store to `.sp3`** (AArch64, the
pre-spawn consumer), inside `W`, in any valid layout of `wakeProg`:

    .L21_wc_main.sp0 + 16:              -- past the box's store (`bX l A`)
      dmb ishst                         -- row: the source's `publish` (FenceRun.pub)
      bl scc_rt_thread_reserve          -- (resB), x30 = .sp3
    .L21_wc_main.sp3:                   -- x0 = n + 1 = 1

The fence is where the source publishes the box (`let c = publish o`,
`FenceRun` under `ms.pub`) and runs locally to its `spawn` (`hfr`: the
controls `S l A` the instance names). The reserve is `Rt.Reserve`'s
segment at the counter's old value `0` (`ResOkA`: owned at the `ldadd`
node's states, not at every state at its pc), the source unchanged
across it.

- `dmb_ndW`: a node at a fence `dmb <opt>` inside `W` (`Out.fence`), the
  source's `FenceRun`.
- `resB`, `wcResIn`, `wake_wcResIn`, `wake_reserveIn`: the call block and
  the code checks;
- `wFr`, `rN`, `rNQ`, `rX`, `rAR`, `ResCtx`: `wc_main`'s frame past the store,
  the nodes (the fence, the call block, the reserve's entry; `rNQ` with the
  fence guarded), the exit at `.sp3`,
  the reserve's region and call context;
- `reserveW_mono`, `WcResW`: the reserve's obligations under a stronger
  frame condition, the nodes' states inside `W`;
- `wake_wc_res_segW`: the segment from the landing past the box's store to
  `.sp3`.
-/
import Spike.Lib.A64WakeWcSp0
import Spike.Lib.Rt.A64RtReserveA
import Spike.Lib.WakePreA

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

section Fence

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at a fence** `dmb <opt>` inside `W` (`Out.fence`): the abstract
state unchanged, the source's run at the fence (`FenceRun` under `ms.pub`:
a local run, or its publication step then one), landing at `pc + 4`. Its
states lie in `W`, none moved by `K` (`hW`). -/
theorem dmb_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {k : FenceKind}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [.instr ⟨.W64, .DMB k⟩])
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ σ c, n.J σ c → ∃ c', FenceRun p ms.pub k c c' ∧ Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (.instr ⟨.W64, .DMB k⟩) 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨c', hr, hL⟩ := hedge σ c hJ
  refine .fence k _ c' (exec_dmb hc) hr ?_
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

end Fence


namespace WakeWc

open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Rt.Reserve (ResG RN rvN rvX ResOkA ReserveW reserve_segWA)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

section ResMono

open Spike.Lib.A64.Rt.Reserve (ResG RN ReserveW)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F' : MachineData → Prop}

/-- The reserve's obligations under a weaker frame condition hold under a
stronger one. -/
theorem reserveW_mono {W : Frag isaLSE2} {K : State → State → Prop} {q : ResG} {i : RN}
    (h : ReserveW W K exe endPc R F q i) (hFF : ∀ m, F' m → F m) : ReserveW W K exe endPc R F' q i := by
  cases i <;> first | exact Ret0.blkW_mono h hFF | exact Ret0.nodeW_mono h hFF

end ResMono

/-! ## The block and the checks -/

/-- The reserve's call. -/
def resB : List Directive := parseAArch64("bl scc_rt_thread_reserve")

block_spec resB (-80) 0 (⟨-80, []⟩ : SO) resB

/-- The fence (a row). -/
def pubF : List Directive := parseAArch64("dmb ishst")

theorem pubF_eq : pubF = [.instr ⟨.W64, .DMB .st⟩] := by decide

/-- **The fence and the call in `prog`**: at `.sp0`'s `4` and `5`, `.sp3`
right after. -/
def wcResIn (prog : List Directive) : Bool :=
  blockAt prog ".L21_wc_main.sp0" 4 pubF && blockAt prog ".L21_wc_main.sp0" 5 resB &&
    labelGap prog ".L21_wc_main.sp0" ".L21_wc_main.sp3" 6

theorem wake_wcResIn : wcResIn SccCode.wakeProg = true := by decide +kernel

theorem wake_reserveIn : Flow.Reserve.reserveIn SccCode.wakeProg = true := by decide +kernel

/-! ## Nodes -/

/-- `wc_main`'s nodes from the fence to the reserve's entry. -/
inductive RsN where
  | f | bl | call

section Res

/-- **main's term past the box's `new`** (wake.w's `main` after `z`, `o`;
`WakePreA.main_body`): `let c = publish o in let p = pair c me in
spawnTerm`. -/
def boxTerm : CoreTerm.Expr :=
  .let_ "c" (.publish (.var "o")) (.let_ "p" (.pair (.var "c") (.var "me")) Spike.Lib.WakePreA.spawnTerm)

variable (ms : MemSide isaLSE2) (lab : Label → Int64) (J0 : AS → Ctl → Prop)

/-- **`wc_main`'s frame past the box's store**: some allocator's ghost whose
caller's frame it is (`wcJ`), the cell `A` at `[sp, #8]`. -/
def wFr (A : Nat) (σ : AS) : Prop := ∃ q : AGB ms lab, wcJ J0 σ q.1.c0 ∧ (σ.slot (-72)).toNat = A

variable (S : WeakMem.AllocLabel → Nat → Ctl → Prop)

/-- **The nodes**: the fence (some fresh label's landing past the box's
store), the call block (the source at `S l A`), the reserve's entry
(`x30 = .sp3`). -/
def rN : RsN → ND
  | .f => ⟨lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 4), ⟨-80, []⟩, fun σ c => ∃ l A,
      (bX ms lab J0 l A).J σ c ∧ c.term = boxTerm⟩
  | .bl => ⟨lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 5), ⟨-80, []⟩, fun σ c => ∃ l A, S l A c ∧ wFr ms lab J0 A σ⟩
  | .call => ⟨lab "scc_rt_thread_reserve", ⟨-80, []⟩, fun σ c => (∃ l A, S l A c ∧ wFr ms lab J0 A σ) ∧
      σ.regs.X30.toBitVec = (lab ".L21_wc_main.sp3").toBitVec⟩

/-- **The exit at `.sp3`**: the reserve's result `1` in `x0`, the source at
`S l A`, the frame kept. -/
def rX : Unit → ND
  | () => ⟨lab ".L21_wc_main.sp3", ⟨-80, []⟩, fun σ c => ∃ l A, S l A c ∧ wFr ms lab J0 A σ ∧
      σ.regs.X0.toBitVec = 1#64⟩

/-- **The nodes with the fence guarded by `Q`**: `rN`, the fence's landing
also at `Q l A` for its label `l` and cell `A` (what the instance knows of the
source there, `wake_wc_res_segW`'s `hfr`). -/
def rNQ (Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : RsN → ND
  | .f => ⟨lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 4), ⟨-80, []⟩, fun σ c => ∃ l A,
      (bX ms lab J0 l A).J σ c ∧ Q l A c⟩
  | .bl => rN ms lab J0 S .bl
  | .call => rN ms lab J0 S .call

/-- The reserve's entry for the frame ghosts `g.1` and the control `g.2`, at
the counter's old value `0`. -/
def rNe (g : Flow.Reserve.G × Ctl) : ND := rvN lab ⟨g.1, 0#64, g.2⟩ .e

end Res

/-- The reserve's region at the call (its frame of 48). -/
abbrev rAR (R : Region) : Region := R.callee (-80) (-48) 0

/-- **The reserve's call context in `wc_main`'s region `R`** at the memory
`m`, for the ghosts `g` (`WcCtx`'s form). -/
def ResCtx (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (g : Flow.Reserve.G × Ctl)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-80, []⟩ mC σC ∧ Jc σC c ∧ (rNe lab g).J (enter (-80) σC) c ∧ CKept R (-80) (-48) 0 mC m

/-- **`wc_main`'s states from the fence to `.sp3` inside `W`**, none moved
by `K`: the fence's, the call block's, and the reserve's in its region (at
the counter's old value `0`, returning to `.sp3`). The fence's states are
`rNQ`'s at the source facts `Q`. -/
structure WcResW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J0 : AS → Ctl → Prop)
    (S Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  f : NodeW W K exe endPc R F (rNQ ms (_root_.Executable.labels exe).label J0 S Q .f)
  bl : BlkW W K exe endPc R F (rN ms (_root_.Executable.labels exe).label J0 S .bl) resB
  res : ∀ g : Flow.Reserve.G × Ctl, g.1.ra = ((_root_.Executable.labels exe).label ".L21_wc_main.sp3").toBitVec →
    ∀ i, ReserveW W K exe endPc (rAR R)
      (fun m => F m ∧ CallerCells R (-80) (-48) 0 m ∧ ResCtx (_root_.Executable.labels exe).label R
        (rN ms (_root_.Executable.labels exe).label J0 S .call).J g m) ⟨g.1, 0#64, g.2⟩ i

/-- From the fence to `.sp3` inside the trivial predicate, with no outside
moves. -/
theorem WcResW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcResW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 S Q := by
  refine ⟨fun _ _ _ => ⟨trivial, fun _ h => h⟩, BlkW.triv, fun _ _ i => ?_⟩
  cases i <;> dsimp only [ReserveW] <;> first | exact BlkW.triv | exact fun _ _ _ => ⟨trivial, fun _ h => h⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from the box's store to `.sp3` is one segment inside `W`**
in any valid layout of `wakeProg`: from the landing past the box's store
(`bX l A`, some fresh label `l`, the source at `Q l A`) to `.sp3` (`rX`).
At the fence the source publishes the box and runs locally to `S l A`
(`hfr`, from any source at `Q l A`); the reserve runs at
the counter's old value `0` (`hres`, the counter owned at the `ldadd`
node's states in the reserve's region), returning `1`, the source unchanged.
Its states lie in `W`, none moved by `K` (`hW`). -/
theorem wake_wc_res_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (hW : WcResW W K exe endPc R F ms J0 S Q)
    (hfr : ∀ (q : AGB ms (_root_.Executable.labels exe).label) (l : WeakMem.AllocLabel) (A : Nat),
      Q l A ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ →
      ∃ c', FenceRun p ms.pub .st
        ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ c' ∧ S l A c')
    (hres : ∀ g : Flow.Reserve.G × Ctl, ResOkA ms F exe endPc (rAR R) F ⟨g.1, 0#64, g.2⟩) :
    SegW W K p lbl ms
      (fun s c => ∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c)
      (fun s c => ∃ x, At exe endPc R F (rX ms (_root_.Executable.labels exe).label J0 S x) s c) := by
  have hin := wake_wcResIn
  simp only [wcResIn, Bool.and_eq_true] at hin
  obtain ⟨⟨h4, h5⟩, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e3 : lab ".L21_wc_main.sp3" = lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 6) := label_labelGap hp hgap
  refine (fn_segW (N := rNQ ms lab J0 S Q) (E := rX ms lab J0 S) (fun i => ?_) RsN.f).mono_pre ?_
  rotate_left
  · rintro s c ⟨l, A, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hQ⟩
    exact ⟨he, hn, hdc, hpc, σ, hA, hD, l, A, hJ, hQ⟩
  cases i
  case f =>
    refine dmb_ndW (code_of hp hend (pubF_eq ▸ h4) rfl) hW.f fun σ c hJ => ?_
    obtain ⟨l, A, ⟨q, hwc, h72, rfl, -⟩, hQ⟩ := hJ
    obtain ⟨c', hr, hS⟩ := hfr q l A hQ
    refine ⟨c', hr, .inl ⟨RsN.bl, ?_, rfl, l, A, hS, q, hwc, h72⟩⟩
    show lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 5) = lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 4) + Int64.ofNat 4
    rw [Int64.add_assoc]; rfl
  case bl =>
    refine seg_ndW (by simp [resB]) resB_ok hF hR hal (by show R.lo ≤ -80; omega) hhi
      (code_of hp hend h5 rfl) hW.bl fun σ c hJ => ⟨c, .refl c, .inl ⟨RsN.call, ?_, ?_, ?_⟩⟩
    · simp only [rNQ, rN]; rw [resB_run]
    · simp only [rNQ, rN]; rw [resB_run]; rfl
    · simp only [rNQ, rN] at hJ ⊢
      rw [resB_run]
      refine ⟨hJ, ?_⟩
      rw [e3]
      show BitVec.ofInt 64 _ = _
      rw [Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
      rfl
  case call =>
    refine call_nd_FWK (KC := False) (lo' := -48) (hi' := 0) (M := fun _ => True)
      (Ne := rNe lab) (Ex := fun g : Flow.Reserve.G × Ctl => rvX ⟨g.1, 0#64, g.2⟩)
      hR hal hF (by show R.lo ≤ -80 + -48; omega) (by decide) (by show (-80 : Int) < R.hi; omega) (by decide)
      (by show (-80 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h30⟩, ⟨-, -, -, h30'⟩⟩ := hg
        have hra : g.1.ra = (lab ".L21_wc_main.sp3").toBitVec := by
          rw [← h30']; exact h30
        exact (reserve_segWA hp hend wake_reserveIn hF' hR' hal' hlo' hhi' hFF ⟨g.1, 0#64, g.2⟩
          (by show (0#64 : BitVec 64).toNat + 1 ≤ 1023; decide) ((hres g).mono hFF)
          fun i => reserveW_mono (hW.res g hra i) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨-, -⟩
      exact ⟨(⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, c), rfl, rfl, rfl, rfl, rfl⟩
    · rintro g ⟨⟩ σC c σx c' σR ⟨⟨l, A, hS, q, ⟨σe, hJe, h16, h8, h80⟩, h72⟩, h30⟩ ⟨hc, -, -, h30'⟩ ⟨hc', hpost⟩ hreg
        - hsl
      have hkeep : ∀ k : Int, -80 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rNQ, rN]; omega)
      refine .inr ⟨(), ?_, rfl, l, A, hc' ▸ hc ▸ hS, ⟨q, ⟨σe, hJe, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · show lab ".L21_wc_main.sp3" = Int64.ofBitVec g.1.ra
        rw [← h30']
        show _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
      · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
      · rw [hkeep (-80) (by omega) (by omega) (by omega), h80]
      · rw [hkeep (-72) (by omega) (by omega) (by omega), h72]
      · rw [hreg, Rt.Reserve.post_x0 hpost]; rfl

end Seg

end WakeWc

end Spike.Lib.A64.Flow

/-- info: 'Spike.Lib.A64.Flow.dmb_ndW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.dmb_ndW

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_res_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_res_segW
