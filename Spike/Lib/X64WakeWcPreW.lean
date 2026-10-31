/-
**`wc_main` up to `.x19` inside `SFactsSt2` at wake.w's global owned-words
map `ownG`** (x86-64; twin of `Spike/Lib/A64WakeWcPreW.lean`): the
`SFactsSt2` component of the pre-spawn chain's `W` at `wc_main`'s own
blocks before `.x20` (the prologue, the entry block, `.x18`'s block and box
store, the reserve's call), proved at the first instance (`instOkW`, owned
words `ownW L a (phW pc)`, no take phase) and moved to `ownG`, which picks
`ownW` at every pc off its four ranges (`GoodW`'s last disjunct).

The pcs are checked by the kernel against the certificate's labels, with
no absolute address in this file: `freeN`, `freeBlk` (`X64WakeFree`) and
`wcTabW` (the blocks' phase facts).

- `wcTabW`, `wcFactsW`, `wcW_fact`: the blocks' phase facts at `phW`.
- `blkW_wcG`: a block of `wc_main` before `.x20` inside `SFactsSt2` at
  `ownG`.

**Where this differs from AArch64**: the label-relative checks (`cv`,
`freeN`, `freeAt`, `goodW_of_freeN`, `blkAgreeW`) are
`Spike/Lib/X64WakeFree.lean`'s and the invariant moves (`blkW_mapC`,
`nodeW_mapC`) `Spike/Lib/X64WakeWcMidW.lean`'s, not this file's; offsets
are bytes, so a fact names a block by its label and byte offset
(`.Lwc_main.chk + 14`, A64's `.stack_check + 3` words) and `blkW_wcG`
takes `freeBlk l k blk` (A64's `freeAt l k blk.length`); the prologue is
x86-64's (`xHead` at `wc_main`, `xLea`, the limit's load as a `step` of 9
bytes, `xCmp`, `xFr`); there is no fence block (scc's `# fence st` emits
no code under TSO, `X64WakeWcRes`), the box's store is one `step` of 3
bytes (A64's two), and the reserve's call is at `.Lwc_main.x18 + 18`;
`blkW_wcG` has no `hal`.
-/
import Spike.Lib.X64WakeFree
import Spike.Lib.X64WakeWcRes
import Spike.Lib.X64WakeTcb2CallW
import Spike.Lib.X64WakeWcMidW

namespace Spike.Lib.X64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk blockAtB code_field)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl CFacts)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW cellOff arun okBlk)
open Spike.Lib.X64.Rt.PhOfTab (blkPh_of_factOk)

/-! ## The blocks' phase facts -/

/-- **`wc_main`'s blocks before `.x20`**: the prologue's four blocks and
its limit load, the entry block, `.x18`'s block, the box's store, the
reserve's call. -/
def wcTabW : List PhFact :=
  [.blk "wc_main" 0 Spike.Lib.X64.Flow.xHead none none,
   .blk ".Lwc_main.chk" 0 (Spike.Lib.X64.Flow.xLea 64 5) none none,
   .step ".Lwc_main.chk" 5 9,
   .blk ".Lwc_main.chk" 14 (Spike.Lib.X64.Flow.xCmp ".Lwc_main.stk" 3 6) none none,
   .blk ".Lwc_main.chk" 23 (Spike.Lib.X64.Flow.xFr 64 4 [(.rdi, -8, 4)]) none none,
   .blk ".Lwc_main.entry" 0 Spike.Lib.X64.Flow.WakeWc.wcE none none,
   .blk ".Lwc_main.x18" 0 Spike.Lib.X64.Flow.WakeWc.wcS0 none none,
   .step ".Lwc_main.x18" 15 3,
   .blk ".Lwc_main.x18" 18 Spike.Lib.X64.Flow.WakeWc.resB none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem wcFactsW : wcTabW.all (factOk (codeT lo wakeCells) okC phC) = true := by
  decide +kernel

/-- **A fact of `wcTabW` at `phW`.** -/
theorem wcW_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ wcTabW) : factOk (codeLabel lo wakeCells) (okPcOf lo wakeCells Λ) phW f = true := by
  have := List.all_eq_true.mp wcFactsW f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at this
  exact this

/-! ## A block inside `SFactsSt2` at `ownG` -/

variable {L : RuntimeLayout}

/-- **A covered `ret`-free block of `wc_main` before `.x20` inside
`SFactsSt2` at `ownG`**, at the outside move of any range `rS`: `blkW_pre`
at the first instance with no take phase (`instOkW`), the source control
replaced by `X64Consumer.c0` (`cfacts_c0`: the state facts do not read it),
moved to `ownG` (`blkAgreeW`) at its free pcs (`hfree`) and free end
(`hlast`), its phase fact `hf` from `wcTabW`. -/
theorem blkW_wcG (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND}
    {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hf : PhFact.blk l k blk none none ∈ wcTabW) (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hfree : freeBlk l k blk = true)
    (hlast : ∀ σ c, n.J σ c →
      freeN (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.X64Consumer.c0 ∧ ∃ c', n.J σ c'⟩
  have hph := blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false) (fun _ _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) (wcW_fact hΛ hf)
  have hW := Spike.Lib.X64.Rt.blkW_pre (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ)
    (lbl := fun _ => none) (rS := rS) (F := F) (n := n') (hp ▸ hb) he hok hR hlo' hhi
    (fun _ _ hJ => hJ.1 ▸ Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0) hph
    (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hcode := code_field L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hag := blkAgreeW (a := a) (μ := Spike.Lib.X64.PhRec.μ L) (F := F) (n := n') hlab hcode hok hR hlo' hhi
    hsite (fun j hj => by rw [← he]; exact freeBlk_pc hlab hfree hj)
    (fun σ c hJ => let ⟨_, hJ'⟩ := hJ.2; hlast σ _ hJ')
  have h2 := Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 hW) hag
  exact blkW_mapC (n' := n') rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

end Spike.Lib.X64.WakePh.WcW

/-- info: 'Spike.Lib.X64.WakePh.WcW.wcFactsW' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.wcFactsW

/-- info: 'Spike.Lib.X64.WakePh.WcW.wcW_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.wcW_fact

/-- info: 'Spike.Lib.X64.WakePh.WcW.blkW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.blkW_wcG
