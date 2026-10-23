/-
**The user `main`'s own states inside the consumer's facts** (x86-64); the
twin of `Spike/Lib/LowerA64/UserW.lean`: the prologue's obligation `XProW`
of `fn0_seg` (`Spike/Lib/LowerX64/Fn.lean`) inside `BodyW0`
(`Spike/Lib/LowerX64/BodyW.lean`), for any program with an instance's
facts (`InstOk`, `Spike/Lib/Rt/X64RtW.lean`).

- `BlkW.mapC`, `NodeW.mapC`, `XProW.mapC`: a node's obligations at another
  invariant whose controls carry the predicate over (each control of the
  new invariant has one of the old with the same state, `W` there giving
  `W'` here). With `W` the consumer's facts at the control and the old
  invariant's controls the entry `c0`, it moves an obligation proven at
  `c0` (`blkW_postO`) into `BodyW0` (`proW_body0`).
- `ProPh`: the prologue's phase facts (its blocks' `blkPh` at their pcs, no
  dead target, no `ret`; the limit's load off the sites and in its next
  pc's phase), as `MainPh`'s prologue part (`Spike/Lib/Rt/X64RtMainU.lean`).
- `proW_sfacts`: a stack-checked prologue without saved registers
  (`prologueIn`, the limit at `%fs:8`) inside the consumer's facts, every
  control of its invariant `c0` (as `mainUW_gen`'s `pro`).
- `proW_body0`: `fn0_seg`'s `hWp` inside `BodyW0`, the invariant's
  controls reached from `c0` by local runs, the thread pointer `tp`.

Where x86-64 differs from AArch64:
- the prologue has five nodes (the head `pushq %rbp; movq %rsp, %rbp`, the
  check's address, the limit's `%fs` load, the check, the frame's set-up;
  `XProW`), at byte offsets given by the listing's cell sizes `zl zf z1 z2
  zs` (AArch64: four nodes at instruction offsets), so `ProPh` takes the
  sizes;
- the region is 8-aligned (no 16-aligned `%rsp`) and holds the frame below
  the saved `%rbp` (`R.lo ≤ -8 - Z`);
- the thread pointer is `%fs`'s base (`fsBase`; AArch64: `TPIDR_EL0`).
-/
import Spike.Lib.LowerX64.BodyW
import Spike.Lib.Rt.X64RtMainU

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok
  xS2 xS1 hdRegs prologueIn ofNat_add')
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.Rt.X64 (blockAtB label_labelGapB)
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer (CFacts SFacts blkPh noRetBlk noRet_false Own Lbl K0)
open Spike.Lib.X64.Rt (InstOk blkW_postO nodeW_fsld_postO)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA)
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet)

/-! ## Obligations at another invariant -/

section Map

variable {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {W W' : Frag isa}

/-- **A block's obligation at another invariant**: same pc and offsets,
each control of `n`'s invariant with one of `n'`'s at the same state, `W`
there giving `W'` here. -/
theorem BlkW.mapC {n n' : ND} {blk : List (Directive × Nat)} (hpc : n'.pc = n.pc) (ho : n'.o = n.o)
    (h : BlkW W K exe endPc R F n' blk) (hJ : ∀ σ c, n.J σ c → ∃ c', n'.J σ c' ∧ ∀ s, W s c' → W' s c) :
    BlkW W' K exe endPc R F n blk := by
  obtain ⟨pc, o, J⟩ := n
  obtain ⟨pc', o', J'⟩ := n'
  simp only at hpc ho
  subst hpc ho
  intro s σ c he hn hd hp hA hF hJn k hk m hA' hD
  obtain ⟨c', hJ', hW⟩ := hJ σ c hJn
  obtain ⟨h1, h2⟩ := h s σ c' he hn hd hp hA hF hJ' k hk m hA' hD
  exact ⟨hW _ h1, h2⟩

/-- **A node's obligation at another invariant** (as `BlkW.mapC`). -/
theorem NodeW.mapC {n n' : ND} (hpc : n'.pc = n.pc) (ho : n'.o = n.o) (h : NodeW W K exe endPc R F n')
    (hJ : ∀ σ c, n.J σ c → ∃ c', n'.J σ c' ∧ ∀ s, W s c' → W' s c) : NodeW W' K exe endPc R F n := by
  obtain ⟨pc, o, J⟩ := n
  obtain ⟨pc', o', J'⟩ := n'
  simp only at hpc ho
  subst hpc ho
  rintro s c ⟨h1, h2, h3, h4, σ, hA, hF, hJn⟩
  obtain ⟨c', hJ', hW⟩ := hJ σ c hJn
  obtain ⟨hw, hk⟩ := h s c' ⟨h1, h2, h3, h4, σ, hA, hF, hJ'⟩
  exact ⟨hW _ hw, hk⟩

/-- **A prologue's obligations at another invariant** (`BlkW.mapC`,
`NodeW.mapC` at each of its nodes). -/
theorem XProW.mapC {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J J' : AS → Ctl → Prop}
    (h : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J')
    (hJ : ∀ σ c, J σ c → ∃ c', J' σ c' ∧ ∀ s, W s c' → W' s c) :
    XProW W' K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J := by
  refine ⟨BlkW.mapC (n' := ⟨pc0, ⟨0, []⟩, J'⟩) rfl rfl h.w0 hJ, BlkW.mapC (n' := xProN1 pc0 J') rfl rfl h.w1 ?_,
    NodeW.mapC (n' := xProN2 pc0 zl Z J') rfl rfl h.w2 ?_,
    BlkW.mapC (n' := xProN3 ms pc0 zl zf Z lim J') rfl rfl h.w3 ?_,
    BlkW.mapC (n' := xProN4 ms pc0 zl zf z1 z2 Z lim J') rfl rfl h.w4 ?_⟩
  · rintro σ1 c ⟨σ, hJσ, he⟩
    obtain ⟨c', h', hw⟩ := hJ σ c hJσ
    exact ⟨c', ⟨σ, h', he⟩, hw⟩
  · rintro σ2 c ⟨σ, hJσ, he⟩
    obtain ⟨c', h', hw⟩ := hJ σ c hJσ
    exact ⟨c', ⟨σ, h', he⟩, hw⟩
  · rintro σ3 c ⟨σ, v, hJσ, hg, he⟩
    obtain ⟨c', h', hw⟩ := hJ σ c hJσ
    exact ⟨c', ⟨σ, v, h', hg, he⟩, hw⟩
  · rintro σ4 c ⟨σ, v, hJσ, hg, he, hs⟩
    obtain ⟨c', h', hw⟩ := hJ σ c hJσ
    exact ⟨c', ⟨σ, v, h', hg, he, hs⟩, hw⟩

end Map

/-! ## The prologue -/

/-- **A stack-checked prologue's phase facts** at labels `lab`, phase index
`ph`, off-site pcs `okPc`: its blocks (the head at `fn`; after its check
label `sc` the check's address, the check, the frame's set-up with saved
registers `ps`, at the cell sizes `zl zf z1 z2 zs`) at their pcs, no dead
target, no `ret`; the limit's load off the sites and in its next pc's
phase. -/
structure ProPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (fn sc : Label) (Z : Int64)
    (L : Label) (zl zf z1 z2 zs : Nat) (ps : List (Reg64 × Int64 × Nat)) : Prop where
  hd : blkPh okPc ph (fun _ => false) lab (lab fn + Int64.ofNat 0) 0 xHead = true
  lea : blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat 0) 0 (xLea Z zl) = true
  ld : okPc (lab sc + Int64.ofNat zl).toBitVec.toNat = true ∧
    ph (lab sc + Int64.ofNat zl + Int64.ofNat zf).toBitVec.toNat = ph (lab sc + Int64.ofNat zl).toBitVec.toNat
  cmp : blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (zl + zf)) 0 (xCmp L z1 z2) = true
  fr : blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (zl + zf + z1 + z2)) 0 (xFr Z zs ps) = true

/-- No `ret` in a block: `hret` of `blkW_postO`, for any return address. -/
private theorem hnr' {lab : Label → Int64} {blk : List (Directive × Nat)} (hb : noRetBlk blk = true) {n : ND}
    {ra' : Int64} : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra' :=
  fun _ _ _ k hk hr => (noRet_false hb k hk hr).elim

section Pro

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

set_option maxHeartbeats 800000 in
/-- **A stack-checked prologue without saved registers is inside the
consumer's facts** (`mainUW_gen`'s `pro`, for any frame `Z`): its code
(`hin`), its phase facts (`hph`), every control of its invariant `c0` with
its facts (`hJc`, `hC0`), the thread pointer `tp` (`htp`) whose limit word
is mapped (`hmr`) and unmapped in private memory under the frame condition
(`hun`), in any 8-aligned region holding the frame below the saved `%rbp`
with 8-aligned bounds. -/
theorem proW_sfacts {ms : MemSide isa} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph)
    {fn sc entry : Label} {Z : Int64} {L : Label} {zl zf z1 z2 zs : Nat}
    (hin : prologueIn cells fn sc entry Z 8 L zl zf z1 z2 zs [] = true)
    {J : AS → Ctl → Prop} {c0 : Ctl} (hC0 : CFacts Λ lbl c0) (hJc : ∀ σ c, J σ c → c = c0) {tp : UInt64}
    (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp) (hph : ProPh okPc ph lab fn sc Z L zl zf z1 z2 zs [])
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hZ : 0 ≤ Z.toInt)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    XProW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms ((_root_.Executable.labels exe).label fn)
      Z 8 L zl zf z1 z2 zs [] J := by
  have h := hin
  simp only [prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have esc := label_labelGapB hI.lays hgap
  rw [hI.labOk] at esc
  have h4 : lab fn + 1 + 3 = lab sc := by rw [esc, Int64.add_assoc]; rfl
  rw [hI.labOk]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_postO hI bHd (Spike.Lib.X64.Flow.ofNat_zero' _)
      (xHead_ok (lo := -8 - Z.toInt) (hi := 0) (by omega) (Int.le_refl _))
      hR (by omega) hhi hR8 hl hh (fun _ _ hJ => hJc _ _ hJ ▸ hC0) hph.hd (hnr' xHead_noRet) (fun _ _ _ => rfl)
      hsub hfit hFO
  · exact blkW_postO hI bLea (by show _ = _ + 1 + 3; rw [h4, Spike.Lib.X64.Flow.ofNat_zero'])
      (xLea_ok (lo := -8 - Z.toInt) (hi := 0) _ _) hR (by omega) hhi hR8 hl hh
      (fun _ _ ⟨_, hJ, _⟩ => hJc _ _ hJ ▸ hC0) hph.lea (hnr' (xLea_noRet _ _)) (fun _ _ _ => rfl) hsub hfit hFO
  · exact nodeW_fsld_postO (p := lab sc + Int64.ofNat zl) hI bLd rfl
      (by show _ + 1 + 3 + _ = _; rw [h4]) (fun _ _ ⟨_, hJ, _⟩ => hJc _ _ hJ ▸ hC0) hph.ld.1 hph.ld.2
      (fun _ _ ⟨σ0, hJ, he⟩ => by
        rw [he, show (xS2 Z σ0).regs.fsBase = σ0.regs.fsBase by simp [xS2, xS1, hdRegs, Reg64s.set64],
          htp _ _ hJ]
        rfl)
      hmr hun hR hR8 hl hh hsub hFO
  · exact blkW_postO hI bCmp (by show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add'])
      (xCmp_ok (lo := -8 - Z.toInt) (hi := 0) _ _ _ _) hR (by omega) hhi hR8 hl hh
      (fun _ _ ⟨_, _, hJ, _⟩ => hJc _ _ hJ ▸ hC0) hph.cmp (hnr' (xCmp_noRet _ _ _)) (fun _ _ _ => rfl) hsub hfit hFO
  · exact blkW_postO hI bFr (by show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add'])
      (xFr_ok (lo := -8 - Z.toInt) (hi := 0) _ _ _ (by simp)) hR (by omega) hhi hR8 hl hh
      (fun _ _ ⟨_, _, hJ, _⟩ => hJc _ _ hJ ▸ hC0) hph.fr (hnr' (xFr_noRet _ _ _)) (fun _ _ _ => rfl) hsub hfit hFO

/-- **`fn0_seg`'s `hWp` inside `BodyW0`**: a user function's prologue
(`proInC`) with its phase facts (`hph`), every control of its invariant
reached from `c0` by a local run (`hJr`) and `Quiet` there (`hQ`), the
thread pointer `tp` (`htp`, `hmr`, `hun`). -/
theorem proW_body0 {ms : MemSide isa} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph)
    {fr : Scc.Emit.X64.Frame} (h1 : fr.size ≤ 2 ^ 31) {fn entry : Label} {zl zf z1 z2 zs : Nat}
    (hin : proInC cells fr fn entry zl zf z1 z2 zs = true) {J : AS → Ctl → Prop} {c0 : Ctl} {p : Prog}
    (hC0 : CFacts Λ lbl c0) (hJr : ∀ σ c, J σ c → LocalRun p c0 c) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {tp : UInt64} (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hph : ProPh okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (fr.size : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    XProW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F ms ((_root_.Executable.labels exe).label fn)
      (Int64.ofInt fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs [] J := by
  have hF64 : (Int64.ofInt fr.size).toInt = fr.size := toInt_ofInt_small (by omega) (by omega)
  have H := proW_sfacts (J := fun σ c => c = c0 ∧ ∃ c1, J σ c1) (ms := ms) hI hin hC0 (fun _ _ h => h.1)
    (fun _ _ ⟨_, _, h⟩ => htp _ _ h) hph hR hR8 (by rw [hF64]; exact hlo) hhi hl hh (by rw [hF64]; omega)
    hmr hun hsub hfit hFO
  exact XProW.mapC H fun σ c hJ => ⟨c0, ⟨rfl, c, hJ⟩, fun _ hs => ⟨hQ c (hJr σ c hJ), hs⟩⟩

end Pro

end Spike.Lib.LowerX64
