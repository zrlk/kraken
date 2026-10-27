/-
**`main`'s return tail after an output call, end to end** (x86-64; the twin
of `Spike/Lib/LowerA64/MainTailP.lean`): `main` ending `let x = print … in
ret a` (hello1's `print …; ret 0`), the source held at `print`'s `ret ()`
(`PrintCallCH`), which reads nothing: its `Ret0` is the literal disjunct
(`exprFv c.term = []`), no result cell.

The held node `heldRNU` is `heldRN`'s (`Spike/Lib/LowerX64/Body2SegHF.lean`)
with the held control reading nothing.
The block `(retDirs lw).zip zs` of `main`'s `ret a` is one segment from it
to `ExitC2SLF`, its states inside `W2` at the held frames
(`blkW_heldTail`): `SFacts` by `blkW_sfacts_ret2`, `HeldS` by `blkW_heldS`
from the write abort's phase (`retHeld_hab`, `retDirs_pc_bodyN2`), `Ret0`
from the held control (`blkW_ret0_nil`), no write and no system call.

- `heldRNU`, `BlkEdge.heldRNU`, `exitC2SLF_of_heldRNU`: the held node with
  a control reading nothing, a block's edge lifted to it, the return's exit
  there;
- `blkW_ret0_nil`: `Ret0` along a block at such a node;
- `mainTailX_segP`: the tail as one segment.
-/
import Spike.Lib.LowerX64.RetHeldW
import Spike.Lib.LowerX64.RetSFacts2
import Spike.Lib.LowerX64.MainExitF
import Spike.Lib.LowerX64.BlocksC1Code
import Spike.Lib.LowerX64.Body2SegHF

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Spike.Lib.Form (WordPl group)
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)

/-- **A node at a held pair whose control reads nothing** (`heldRN` with
`exprFv c.term = []`, e.g. `print`'s `ret ()`). -/
def heldRNU (p : Prog) (fs : List TermRun.Frame) (n : ND) : ND :=
  ⟨n.pc, n.o, fun σ c => Scc.Sem.exprFv c.term = [] ∧ (heldRN p fs n).J σ c⟩

section HeldRNU

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isa} {K : State → State → Prop}

/-- **A block's edge lifted to the held nodes reading nothing**: the held
source takes no step; the run the edge takes at depth 0 extends the held
pair's run. -/
theorem BlkEdge.heldRNU {lab : String → Int64} {lo hi : Int} {n : ND} {blk : List (Directive × Nat)}
    {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (h : BlkEdge p lab lo hi n blk N E) (fs : List TermRun.Frame) :
    BlkEdge p lab lo hi (heldRNU p fs n) blk (fun j => heldRNU p fs (N j)) (fun x => heldRNU p fs (E x)) := by
  refine ⟨h.1, h.2.1, fun σ c ⟨hv, hH, cR, hr, hJ⟩ => ?_⟩
  obtain ⟨c', hr', hL⟩ := h.2.2 σ cR hJ
  have hrr : FrameRun p (c, fs) (c', []) := hr.trans (FrameRun.ofLocal hr' [])
  refine ⟨c, .refl c, ?_⟩
  rcases hL with ⟨j, h1, h2, h3⟩ | ⟨x, h1, h2, h3⟩
  · exact .inl ⟨j, h1, h2, hv, hH, c', hrr, h3⟩
  · exact .inr ⟨x, h1, h2, hv, hH, c', hrr, h3⟩

/-- **The return's exit at a held pair reading nothing is `ExitC2SLF`**:
the frame run in `heldRNU`'s invariant reaches the return's control at
depth 0. -/
theorem exitC2SLF_of_heldRNU {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {ty : Ty} {Ab : FragS isa}
    {fs : List TermRun.Frame} (hr : FrameRunM p (c0, []) (c0', [])) {s : State} {c : Ctl}
    (h : At exe endPc R F (heldRNU p fs ((retNSL p lbl fp ra c0' ty).withTp tp)) s c) :
    ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab s c fs := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hF, -, -, cR, hrR, hJ⟩ := h
  exact .inl ⟨cR, hrR, c0', hr, he, hn, hdc, hpc, σ, hA, hF, hJ⟩

/-- **`Ret0` along a block at a node whose controls read nothing** (the
literal disjunct). -/
theorem blkW_ret0_nil {lbl : Lbl} {n : ND} {blk : List (Directive × Nat)}
    (hJ : ∀ σ c, n.J σ c → Scc.Sem.exprFv c.term = []) :
    BlkW (Ret0 lbl) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hJn k hk m hA' _
  exact ⟨.inl (hJ σ c hJn), fun _ h => h⟩

end HeldRNU

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl}
  {lsize : Lsize} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {K : State → State → Prop} {okPc : Nat → Bool}
  {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {ms : List TermRun.Frame → MemSide isa} {W : FragS isa}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **`main`'s return tail after an output call is one segment to
`ExitC2SLF`** (`ret_edgeSL` lifted to `heldRNU`, the source at `print`'s
`ret ()`): the block's states inside `W2` at the held frames
(`blkW_heldTail`; `SFacts` by `blkW_sfacts_ret2`, `HeldS` by `blkW_heldS`
from `retHeld_hab` and `blkW_ret0_nil`). The frame and the region, the
runtime's facts, the block of the code at `main`'s return address `ra`
(`hcd`), `ra` off the write abort (`hpos`), the returned atom's placements
and layout at any symbolic environment `s`, the frame run to the ghost
`c0'` (`hr`), `W` from `W2` (`hW₀`). -/
theorem mainTailX_segP (hp : ProgNoS ZBad p) {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {vs : List Scc.IR.Operand} {lw : List Item} (hl : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw)
    (hn : vs.length ≤ Scc.Emit.X64.retRegs.length) {zs : List Nat} (hz : zs.length = (retDirs lw).length)
    {pc : Int64} {fp ra : BitVec 64}
    (hcd : SubCd (CdCL cells okPc ph lab (Int64.ofBitVec ra)) pc ((retDirs lw).zip zs))
    (hpos : PosOff cells lab (Int64.ofBitVec ra))
    {s : Spike.Lib.Form.SEnv} {a : At} {t : Ty} {pls : List WordPl}
    (hsa : Spike.Lib.Form.sevalAt s a = some (t, pls))
    (hg : group t vs = some pls) {i : Expr → String → Nat → Option Nat} {ty : Ty} (hsc : InLits lits a)
    (hlit : ∀ n, a = .lit n → n < 2 ^ 64) (hera : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf ty)
    {fs : List TermRun.Frame} {tp : UInt64} {c0 c0' : Ctl} (hr : FrameRunM p (c0, []) (c0', []))
    (hW₀ : ∀ st c, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize st c fs → W st c fs)
    {Ab : FragS isa} :
    SegWS W K p lbl ms
      ((At exe endPc R F (heldRNU p fs ((bodyN2 p lbl lsize i fr fp ra c0' pc (.ret a) s lits cs bufs).withTp
        tp))).at fs)
      (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  have he := (ret_edgeSL (p := p) (lbl := lbl) (lsize := lsize) (fp := fp) (ra := ra) (c0 := c0') (pc := pc)
    (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 hl hn hz (_root_.Executable.labels exe).label
    hsa hg hsc hlit hera).tp tp
  have hok := he.2.1
  have hcode : ∀ st : State, st.exe = exe → st.endPc = endPc → CodeAt st pc ((retDirs lw).zip zs) :=
    SubCd.cdOf (fun pc' blk h => by
      have h' := CdCL.toCdC h
      rw [← hI.labOk] at h'
      exact cdOf_cdC hI.lays hI.endOk pc' blk h') hcd
  let n := heldRNU p fs ((bodyN2 p lbl lsize i fr fp ra c0' pc (.ret a) s lits cs bufs).withTp tp)
  have hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot := fun _ _ ⟨_, _, _, _, ⟨⟨_, hfj, _⟩, _⟩⟩ => hfj
  have hS := blkW_sfacts_ret2 (lbl := lbl) (n := n) hI hf h1 hR hR8 hlo hhi hl8 hh8 hsub hfit hFO rfl hfj hl hn
    hz (hcd.mono fun _ _ h => CdCL.toCdC h)
  have hab := retHeld_hab (F := F) (n := n) hI hpr habt hl hz hcd hok hR hlo hhi
    (fun _ _ ⟨_, _, _, _, ⟨hJ, _⟩⟩ => retDirs_pc_bodyN2 hf h1 hl hn hz lab hJ) hpos
  have hW := blkW_heldTail (Λ := Λ) (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize) hp hS
    (fun _ _ h => h.2.1)
    (blkW_heldS hab (blkW_ret0_nil (lbl := lbl) fun _ _ h => h.1) (blkW_noWr' hcode hok hR hlo hhi)
      (blkW_noSys' hcode hok))
  exact (SegWS.liftS fs (((he.heldRNU fs).seg hF hR hlo hhi hcode hW).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim) hW₀).mono_post
    fun _ _ _ ⟨h, hfs⟩ => hfs ▸ exitC2SLF_of_heldRNU hr h

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.mainTailX_segP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainTailX_segP
