/-
**The state's facts at a body block of `Kind2`** (x86-64): `SFacts` at
`dumN n` for a block of a construct or of `main`'s many-word `ret`
(`Kind2`), at a node with the frame's offsets whose controls have the saved
pair in their cells (`FrJ`), as `blkW_w2BP`'s `hS` for a block without a
`ret`. The `hS` premise of `blkW_heldTailN` at `main`'s `ret a` block, which
has no other producer among the `W2` lemmas.

- `okBlk_kind2`: a `Kind2` block is covered at the frame's offsets;
- `hret_kind2`: a `Kind2` block returns only to the saved `ra`
  (`hret_kind1`, `retBlk_run`);
- `blkW_sfacts_k2P`: `SFacts` at `dumN n` for a `Kind2` block given its code
  and phase check (`blkW_postO'`);
- `blkW_sfacts_k2`: the same for a block of the code predicate `CdC`
  (`SubCd`, as `blkW_w2CP`);
- `blkW_sfacts_ret2`: the same at `main`'s `ret` block `(retDirs lw).zip zs`.
-/
import Spike.Lib.LowerX64.W2Body
import Spike.Lib.LowerX64.Node2Edges
import Spike.Lib.LowerX64.Body2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib (Region)
open Spike.Lib.X64Consumer (SFacts blkPh hret_of_run Own Lbl)
open Spike.Lib.X64 (BlkW ND okBlk CodeAt cellOff RW retBlk retBlk_ok retBlk_run classify arun)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.AllocG (dumN)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)
open Scc.Emit.X64 (Item)

section K2

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {lbl : Lbl} {R : Region} {F : MachineData → Prop} {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64}

/-- `main`'s `ret` block is `retBlk` of its words (`getOps_rw`), each at
the frame's offsets. -/
theorem retDirs_retBlk (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {vs : List Scc.IR.Operand}
    {lw : List Item} (hl : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw)
    (hn : vs.length ≤ Scc.Emit.X64.retRegs.length) :
    ∃ rws : List RW, (∀ w ∈ rws, w.ok (-(fr.size : Int)) 16 = true) ∧ retDirs lw = retBlk rws := by
  have hrr : Scc.Emit.X64.retRegs = Spike.Lib.X64.retRegs := rfl
  rw [hrr] at hl hn
  obtain ⟨rws, -, hd, hoks, -⟩ := getOps_rw hf h1 hl hn
  exact ⟨rws, hoks, by rw [retDirs, dirs_append, dirs_epiItems, hd]; rfl⟩

/-- **A `Kind2` block is covered** at the frame's offsets (`kind1_ok`,
`retBlk_ok`). -/
theorem okBlk_kind2 (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {blk : List (Directive × Nat)}
    (hk : Kind2 fr blk) : okBlk (-(fr.size : Int)) 16 (oB fr) blk = true := by
  rcases hk with hk | ⟨vs, lw, hn, hl, hb⟩
  · exact kind1_ok hf h1 hk
  obtain ⟨rws, hoks, hblk⟩ := retDirs_retBlk hf h1 hl hn
  have e := zip_fst_snd blk
  rw [hb, hblk] at e
  rw [← e]
  exact retBlk_ok (by omega) hoks (by rw [List.length_map, ← hblk, ← hb, List.length_map])

omit [Kraken.Executable.ValidLayout exe] in
/-- **A `Kind2` block returns only to the saved `ra`** (`blkW_postO`'s
`hret`): `hret_kind1` for a construct's block; `main`'s `ret` block's run
ends at the slot `8` (`retBlk_run`), `ra` by `FrJ`. -/
theorem hret_kind2 (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {n : ND} (hno : n.o = oB fr)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List (Directive × Nat)} (hk : Kind2 fr blk) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp) = Int64.ofBitVec ra := by
  rcases hk with hk | ⟨vs, lw, hn, hl, hb⟩
  · exact hret_kind1 hf h1 hno hfj hk
  obtain ⟨rws, -, hblk⟩ := retDirs_retBlk hf h1 hl hn
  have e := zip_fst_snd blk
  rw [hb, hblk] at e
  have hz : (blk.map (·.2)).length = (retBlk rws).length := by
    rw [List.length_map, ← hblk, ← hb, List.length_map]
  rw [← e]
  refine hret_of_run (hno ▸ e ▸ okBlk_kind2 hf h1 (.inr ⟨vs, lw, hn, hl, hb⟩)) fun σ c hJ => ?_
  rw [hno, show oB fr = Spike.Lib.X64.oR (-(fr.size : Int)) from rfl, (retBlk_run lab n.pc _ σ rws hz).1]
  exact congrArg Int64.ofBitVec (hfj σ c hJ).2

omit [Kraken.Executable.ValidLayout exe] in
/-- **`SFacts` at a `Kind2` block at its code** (`blkW_postO'` at
`dumN n`): a block of a construct or of `main`'s `ret` (`hk`), in the code
at its node's pc (`hcode`), passing the phase check there at the saved
`ra` (`hph`), at a node with the frame's offsets (`hno`) whose controls
have the saved pair in their cells (`hfj`). -/
theorem blkW_sfacts_k2P {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {n : ND} (hno : n.o = oB fr)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List (Directive × Nat)} (hk : Kind2 fr blk)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc (Int64.ofBitVec ra) blk = true) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) blk :=
  blkW_postO' (n := dumN n) (dead := fun _ => false) (ra := Int64.ofBitVec ra) hI hcode
    (hno ▸ okBlk_kind2 hf h1 hk) hR hlo hhi hR8 hl hh (fun _ _ h => h.1 ▸ cfacts_c0) hph
    (hret_kind2 (n := dumN n) hf h1 hno (fun σ _ ⟨_, c1, hJ1⟩ => hfj σ c1 hJ1) hk)
    (fun _ _ _ => rfl) hsub hfit hFO

/-- **`SFacts` at a `Kind2` block of the code** (`blkW_sfacts_k2P`): a
block of the code predicate `CdC` at the saved return address (`SubCd`,
its phase from the run's check, as `blkW_w2CP`). -/
theorem blkW_sfacts_k2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {n : ND} (hno : n.o = oB fr)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List (Directive × Nat)} (hk : Kind2 fr blk)
    (hcd : SubCd (CdC cells okPc ph lab (Int64.ofBitVec ra)) n.pc blk) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) blk := by
  obtain ⟨pc0, pre, post, ⟨-, L, j, off, hpc0, hb, hrun⟩, hpc⟩ := hcd
  have hok : okBlk (-(fr.size : Int)) 16 n.o blk = true := hno ▸ okBlk_kind2 hf h1 hk
  have hc : cellOff (pre ++ blk ++ post) pre.length = (pre.map (·.2)).sum := by
    simp [cellOff]
  have hph := Scc.Cert.Ph1X64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  rw [hc, ← hpc] at hph
  have hb' := blockAt_sub hb
  have hpc' : lab L + Int64.ofNat (off + (pre.map (·.2)).sum) = n.pc := by
    rw [hpc, ← hpc0, Int64.ofNat_add, Int64.add_assoc]
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb'
    rwa [hI.labOk, hpc'] at this
  exact blkW_sfacts_k2P hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hno hfj hk hcode hph

/-- **`SFacts` at `main`'s `ret` block** (`blkW_sfacts_k2` at `Kind2`'s
`ret` arm): the loads of the words `vs` into the result registers and the
epilogue, `(retDirs lw).zip zs`, a block of the code predicate `CdC` at a
node with the frame's offsets whose controls have the saved pair in their
cells (`bodyN2`'s). The `hS` of `blkW_heldTailN` at the `ret a` node. -/
theorem blkW_sfacts_ret2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {n : ND} (hno : n.o = oB fr)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {vs : List Scc.IR.Operand} {lw : List Item}
    (hgo : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw) (hn : vs.length ≤ Scc.Emit.X64.retRegs.length)
    {zs : List Nat} (hz : zs.length = (retDirs lw).length)
    (hcd : SubCd (CdC cells okPc ph lab (Int64.ofBitVec ra)) n.pc ((retDirs lw).zip zs)) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) ((retDirs lw).zip zs) := by
  refine blkW_sfacts_k2 hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hno hfj ?_ hcd
  unfold Kind2
  rw [List.map_fst_zip (by omega)]
  exact .inr ⟨vs, lw, hn, hgo, rfl⟩

end K2

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.
/-- info: 'Spike.Lib.LowerX64.okBlk_kind2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.okBlk_kind2

/-- info: 'Spike.Lib.LowerX64.hret_kind2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hret_kind2

/-- info: 'Spike.Lib.LowerX64.blkW_sfacts_k2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.blkW_sfacts_k2

/-- info: 'Spike.Lib.LowerX64.blkW_sfacts_ret2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.blkW_sfacts_ret2
