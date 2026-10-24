/-
**The runtime's blocks and nodes inside `W` on x86-64, for any program**
(`SFacts`, `Spike/Lib/X64SegInst.lean`): the block and node lemmas of
`ret0.x`'s instance (`blkW_pre`, `blkW_post`, `blkW_postO`, `nodeW_*`,
`Spike/Lib/X64Ret0I.lean`) over code cells `cells` laid out in `exe`, its
labels `lab`, marks `μ`, owned words `own`, take's phase `Tk`, outside move
`K`, phase index `ph` and off-site pcs `okPc`. The twin of
`Spike/Lib/Rt/A64RtW.lean`: a block sits `off` bytes after its label, an
instruction is `z` bytes long.

- **The instance's facts** (`InstOk`): the layout, the labels, the owned
  words and the take's phase factoring through `ph` (`same`), off-site pcs
  off the marks' sites with no outside move (`off`). Same argument order and
  fields as AArch64's.
- **A node's memory word** by its facts: mapped in the loaded kernel state
  (`hmw`, `hmr`), unmapped in private memory under the frame condition
  (`hun`); the owned words through a table by phase (`hown`, `ownOf`).
- **The take's phase** at a pc by a premise over every state at it (`hT`,
  `hT'`), as AArch64's; an instance with a phase bit discharges it by its
  `not_tk`.
- **A block's phase check** from `RtNodesOk` (`Spike/Lib/Rt/X64RtNodes.lean`,
  a premise A6 discharges): the `_row` forms take a row of the table.
- **Oracle**: the hand lemmas are these at `ret0.x`'s instance
  (`Spike/Test/X64RtW.lean`).
-/
import Spike.Lib.Rt.X64RtNodes

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (StackM StackOff stackOff_stable CallerCells)
open Scc.Cert.Rt.X64 (blockAtB code_field OGrp OBlk Lays endOf)

/-- **An instance's facts for its blocks**: the code cells `cells` laid out
in `exe` (its end `endPc`), its labels `lab`; the owned words and the take's
phase factoring through `ph` of the pc; an off-site pc (`okPc`) off the
marks' sites, with no outside move. -/
structure InstOk (exe : _root_.Executable) (endPc : Int64) (cells : List (Directive × Nat))
    (lab : Label → Int64) (μ : Marks) (own : Own) (Tk : State → Prop) (K : State → State → Prop)
    (okPc : Nat → Bool) (ph : Nat → Nat) (kp : Nat := 0) : Prop where
  lays : Lays exe cells kp
  endOk : endPc = endOf exe cells kp
  labOk : (_root_.Executable.labels exe).label = lab
  same : ∀ s s' : State, ph (pcOf s') = ph (pcOf s) → own s' = own s ∧ (Tk s' ↔ Tk s)
  off : ∀ s : State, okPc (pcOf s) = true → PcOff μ s ∧ ∀ s', ¬ K s s'

section Blk

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- A block of the cells at its label, in the loaded thread. -/
theorem codeOf {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {l : Label} {off : Nat}
    {b : List (Directive × Nat)} (hb : blockAtB cells l off b = true) {s : State} (hs : s.exe = exe)
    (hn : s.endPc = endPc) : CodeAt s (lab l + Int64.ofNat off) b :=
  code_field hI.lays hI.endOk hb (by rw [hI.labOk]) s hs hn

omit [Kraken.Executable.ValidLayout exe] in
/-- **The range owned from a region's cells and the words off it**: every
aligned word of `rS` either lies off the 8-aligned region `R` (`hoff`) or is
one of its cells (`hc`). -/
theorem owned_off {R : Region} (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) {s : State} (hoff : StackOff rS R s.st.1)
    (hc : ∀ k, R.Off k → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome) : Owned Λ rS s := by
  refine ⟨hsub, fun a h8 ha ha7 => ?_⟩
  unfold Scc.Sem.X64.privLoad
  rw [Option.isSome_map]
  by_cases hout : (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a
  · exact hoff a h8 ha ha7 hout
  · have h1 := hR.lo
    have h2 := hR.hi
    have hk : R.Off ((a : Int) - R.base.toNat) := ⟨by omega, by omega, by omega⟩
    have he : R.addr ((a : Int) - R.base.toNat) = BitVec.ofNat 64 a := by
      apply BitVec.eq_of_toNat_eq
      have := Region.addr_toNat hR hk
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← he]
    exact hc _ hk

omit [Kraken.Executable.ValidLayout exe] in
/-- **The words of `rS` off a callee's region**: off the caller's region
(`StackOff`) or a caller's cell outside the callee's (`CallerCells`). -/
theorem stackOff_callee {R : Region} (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) {kc lo' hi' : Int} (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi)
    (hk8 : kc % 8 = 0) {m : MachineData} (hoff : StackOff rS R m) (hcc : CallerCells R kc lo' hi' m) :
    StackOff rS (R.callee kc lo' hi') m := by
  intro a h8 ha ha7 hout'
  have hcb := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  by_cases hout : (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a
  · exact hoff a h8 ha ha7 hout
  · have h1 := hR.lo
    have h2 := hR.hi
    have hk : R.Off ((a : Int) - R.base.toNat) := ⟨by omega, by omega, by omega⟩
    have hn : ¬ (R.callee kc lo' hi').Off ((a : Int) - R.base.toNat - kc) := by
      rintro ⟨-, h3, h4⟩
      simp only [Region.callee] at hcb h3 h4 hout'
      omega
    have he : R.addr ((a : Int) - R.base.toNat) = BitVec.ofNat 64 a := by
      apply BitVec.eq_of_toNat_eq
      have := Region.addr_toNat hR hk
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← he]
    exact hcc _ hk hn

/-- **A covered block before the take** is inside `SFacts`: its code
(`hb`), its cover (`hok`), the region's facts, the source control's facts
at the node (`hC`), the phase check (`hph`), every `ret` returning to `ra`
(`hret`), its dead targets never reached (`hdead`), and its entry not in
the take's phase (`hT`). -/
theorem blkW_pre {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label}
    {off : Nat} (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : ∀ s : State, pcOf s = (lab l + Int64.ofNat off).toBitVec.toNat → ¬ Tk s) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  rw [he] at hph hT
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeOf hI hb hs hn
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', hsm⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfacts hcode hok hR hlo hhi hC hpc hph' fun s m _ _ _ k hk s' _ hpc' htk => ?_
  have := (hsm k hk { s' with st := (s'.st.1, n.pc) } s' rfl hpc').2.mp htk
  exact absurd this (hT _ (by unfold pcOf; rfl))

/-- **A covered block after the take** is inside `SFacts`: as `blkW_pre`
without the entry's phase, its frame condition also `StackM rS` (kept by
the region's writes, `hSM`) and `rS` in the pool (`hsub`). -/
theorem blkW_post {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label}
    {off : Nat} (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS)) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n blk := by
  rw [he] at hph
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeOf hI hb hs hn
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfacts hcode hok hR hlo hhi hC hpc hph' fun s m hF hD _ k hk s' hm _ _ => ?_
  refine ⟨hsub, fun a h8 ha ha7 => ?_⟩
  unfold Scc.Sem.X64.privLoad
  rw [Option.isSome_map, hm]
  exact hSM _ _ hF.2 hD a h8 ha ha7

/-- **A covered block after the switch**, in an 8-aligned region whose
frame condition gives the words of `rS` off it (`hFO`): as `blkW_post`,
`rS` not wrapping (`hfit`). -/
theorem blkW_postO {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label}
    {off : Nat} (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  rw [he] at hph
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeOf hI hb hs hn
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfacts hcode hok hR hlo hhi hC hpc hph' fun s m hF hD hc k hk s' hm _ _ => ?_
  subst hm
  exact owned_off hR hR8 hl hh hsub (stackOff_stable hfit _ _ (hFO _ hF) hD) hc

/-! ### From a row of the table -/

/-- **A row before the take** inside `SFacts`, its phase check from
`RtNodesOk` (`hN`; the row not a site's `nop`, `hs`), its cover at the row's
offsets (A5). -/
theorem blkW_pre_row {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {dead : Label → Nat → Nat → Bool}
    {ra : Label → Int64} {gs : List OGrp} (hN : RtNodesOk okPc ph dead lab ra gs) {g : OGrp} (hg : g ∈ gs)
    {b : OBlk} (hbm : b ∈ g.bs) (hs : b.blk ≠ siteBlk) {R : Region} {F : MachineData → Prop} {n : ND}
    (hb : blockAtB cells g.l b.off b.blk = true) (he : lab g.l + Int64.ofNat b.off = n.pc) (ho : n.o = b.o)
    (hok : okBlk b.lo b.hi b.o b.blk = true) (hR : R.OK) (hlo : R.lo ≤ b.lo) (hhi : b.hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < b.blk.length), classify b.blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (b.blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun lab (b.blk.take k) ⟨n.pc, n.o, σ⟩).so.sp) = ra g.l)
    (hdead : ∀ σ c, n.J σ c → dead g.l b.k (arun lab b.blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : ∀ s : State, pcOf s = (lab g.l + Int64.ofNat b.off).toBitVec.toNat → ¬ Tk s) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n b.blk :=
  blkW_pre hI hb he (ho ▸ hok) hR hlo hhi hC (hN.row hg hbm hs) hret hdead hT

/-- **A row after the take** inside `SFacts`, as `blkW_post`. -/
theorem blkW_post_row {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {dead : Label → Nat → Nat → Bool}
    {ra : Label → Int64} {gs : List OGrp} (hN : RtNodesOk okPc ph dead lab ra gs) {g : OGrp} (hg : g ∈ gs)
    {b : OBlk} (hbm : b ∈ g.bs) (hs : b.blk ≠ siteBlk) {R : Region} {F : MachineData → Prop} {n : ND}
    (hb : blockAtB cells g.l b.off b.blk = true) (he : lab g.l + Int64.ofNat b.off = n.pc) (ho : n.o = b.o)
    (hok : okBlk b.lo b.hi b.o b.blk = true) (hR : R.OK) (hlo : R.lo ≤ b.lo) (hhi : b.hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < b.blk.length), classify b.blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (b.blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun lab (b.blk.take k) ⟨n.pc, n.o, σ⟩).so.sp) = ra g.l)
    (hdead : ∀ σ c, n.J σ c → dead g.l b.k (arun lab b.blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS)) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n b.blk :=
  blkW_post hI hb he (ho ▸ hok) hR hlo hhi hC (hN.row hg hbm hs) hret hdead hsub hSM

/-- **A row after the switch, the words of `rS` off its region from the
frame condition**, as `blkW_postO`. -/
theorem blkW_postO_row {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {dead : Label → Nat → Nat → Bool}
    {ra : Label → Int64} {gs : List OGrp} (hN : RtNodesOk okPc ph dead lab ra gs) {g : OGrp} (hg : g ∈ gs)
    {b : OBlk} (hbm : b ∈ g.bs) (hs : b.blk ≠ siteBlk) {R : Region} {F : MachineData → Prop} {n : ND}
    (hb : blockAtB cells g.l b.off b.blk = true) (he : lab g.l + Int64.ofNat b.off = n.pc) (ho : n.o = b.o)
    (hok : okBlk b.lo b.hi b.o b.blk = true) (hR : R.OK) (hlo : R.lo ≤ b.lo) (hhi : b.hi ≤ R.hi)
    (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < b.blk.length), classify b.blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (b.blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun lab (b.blk.take k) ⟨n.pc, n.o, σ⟩).so.sp) = ra g.l)
    (hdead : ∀ σ c, n.J σ c → dead g.l b.k (arun lab b.blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n b.blk :=
  blkW_postO hI hb he (ho ▸ hok) hR hlo hhi hR8 hl hh hC (hN.row hg hbm hs) hret hdead hsub hfit hFO

end Blk

/-! ## A single instruction's states -/

section Node

open Kraken.Promising.Lower.X64 (CellAt after exec_store_agrees exec_load_agrees exec_xaddG_agrees
  exec_xchgG_agrees eaddr exec_movfs_load_agrees fsAddr)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- An instruction of the cells at its label, in the loaded thread. -/
theorem cellOf {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {l : Label} {off z : Nat} {d : Directive}
    {p : Int64} (hb : blockAtB cells l off [(d, z)] = true) (he : lab l + Int64.ofNat off = p) {s : State}
    (hs : s.exe = exe) (hn : s.endPc = endPc) (hpc : s.st.2 = p) : CellAt s d z :=
  (codeOf hI hb hs hn).cell0 rfl rfl (hpc.trans he.symm)

omit [Kraken.Executable.ValidLayout exe] in
/-- Past an instruction of `z` bytes at `p` whose next pc has its phase, a
state owns what it owns and is in the take's phase iff it is. -/
theorem next_same {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {s : State} {p : Int64} {z : Nat}
    (hpc : s.st.2 = p) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    ∀ m, own (after s z m) = own s ∧ (Tk (after s z m) ↔ Tk s) :=
  fun _ => hI.same _ _ (by
    show ph (s.st.2 + Int64.ofNat z).toBitVec.toNat = ph s.st.2.toBitVec.toNat; rw [hpc]; exact hph)

/-- Past an instruction of `z` bytes at `p`, neither it nor the next pc in
the take's phase, a state is in it iff it is. -/
theorem next_tk {s : State} {p : Int64} {z : Nat} (hpc : s.st.2 = p)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hT' : ∀ s : State, pcOf s = (p + Int64.ofNat z).toBitVec.toNat → ¬ Tk s) :
    ∀ m, Tk (after s z m) ↔ Tk s := fun m =>
  ⟨fun h => absurd h (hT' _ (by show (s.st.2 + Int64.ofNat z).toBitVec.toNat = _; rw [hpc])),
    fun h => absurd h (hT _ (by show s.st.2.toBitVec.toNat = _; rw [hpc]))⟩

/-- The owned words at `p`, given they factor through the phase (`hown`). -/
theorem own_at {ownOf : Nat → List (Loc × Val)} (hown : ∀ s, own s = ownOf (ph (pcOf s))) {s : State} {p : Int64}
    (hpc : s.st.2 = p) : own s = ownOf (ph p.toBitVec.toNat) := by
  rw [hown]; show ownOf (ph s.st.2.toBitVec.toNat) = _; rw [hpc]

/-- **A write's update of the owned words, decided**: for each owned value
`v` of `L`, `ow'` is `ow` with `L` at `f v`, or a word of `ow` other than
`L`. -/
def ownUpdB (ow ow' : List (Loc × Val)) (L : Loc) (f : Val → Val) : Bool :=
  ow.all fun q => decide (q.1 ≠ L) || ow'.all fun r => decide ((r.1 = L ∧ r.2 = f q.2) ∨ (r.1 ≠ L ∧ r ∈ ow))

theorem ownUpd_of {ow ow' : List (Loc × Val)} {L : Loc} {f : Val → Val} (h : ownUpdB ow ow' L f = true) :
    ∀ v, (L, v) ∈ ow → Spike.Lib.Consumer1.OwnUpd ow ow' L (f v) := by
  intro v hv L' w hm
  have := List.all_eq_true.mp h _ hv
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_or, List.all_eq_true, decide_eq_true_eq] at this
  exact this _ hm

omit [Kraken.Executable.ValidLayout exe] in
/-- **A node before the take**, at `p` off the sites (`hok`), not in the
take's phase (`hT`): its states are inside `SFacts` given it with `PcOff`
and the range owned in the take's phase. -/
theorem nodeW_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {p : Int64}
    (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true) (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (h : ∀ s c σ, s.exe = exe → s.endPc = endPc → s.decls = {} → s.st.2 = p → Abs R n.o s.st.1 σ →
      F s.st.1 → n.J σ c → PcOff μ s → (Tk s → Owned Λ rS s) → SFacts Λ μ own rS Tk lbl s c) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hpc' : pcOf s = p.toBitVec.toNat := by unfold pcOf; rw [hpc]
  have hP := hI.off s (by rw [hpc']; exact hok)
  exact ⟨h s c σ hs hn hdc hpc hA hD hJ hP.1 fun h' => absurd h' (hT s hpc'), hP.2⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **A node after the take**, at `p` off the sites: as `nodeW_pre`, its
frame condition also `StackM rS` and `rS` in the pool (`hsub`). -/
theorem nodeW_post {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {p : Int64}
    (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true) (hsub : rS.Sub Λ.stackPool)
    (h : ∀ s c σ, s.exe = exe → s.endPc = endPc → s.decls = {} → s.st.2 = p → Abs R n.o s.st.1 σ →
      F s.st.1 → n.J σ c → PcOff μ s → (Tk s → Owned Λ rS s) → SFacts Λ μ own rS Tk lbl s c) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact hok)
  refine ⟨h s c σ hs hn hdc hpc hA hD.1 hJ hP.1 fun _ => ⟨hsub, fun a h8 ha ha7 => ?_⟩, hP.2⟩
  unfold Scc.Sem.X64.privLoad
  rw [Option.isSome_map]
  exact hD.2 a h8 ha ha7

omit [Kraken.Executable.ValidLayout exe] in
/-- **A node after the switch**, in an 8-aligned region whose frame
condition gives the words of `rS` off it (`hFO`): as `nodeW_post`. -/
theorem nodeW_postO {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {p : Int64}
    (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true)
    (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (h : ∀ s c σ, s.exe = exe → s.endPc = endPc → s.decls = {} → s.st.2 = p → Abs R n.o s.st.1 σ →
      F s.st.1 → n.J σ c → PcOff μ s → (Tk s → Owned Λ rS s) → SFacts Λ μ own rS Tk lbl s c) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact hok)
  refine ⟨h s c σ hs hn hdc hpc hA hD hJ hP.1 fun _ => owned_off hR hb hl hh hsub (hFO _ hD) fun k hk => ?_, hP.2⟩
  obtain ⟨j, hj, -⟩ := hA.slot k hk
  rw [hj]; rfl

/-- **A node at a single instruction without an event** (`SI`) before the
take, its next pc in its phase. -/
theorem nodeW_si_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {si : SI} {z : Nat}
    {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(si.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

/-- **A node at a single instruction without an event** (`SI`) after the
take, its next pc in its phase. -/
theorem nodeW_si_post {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {si : SI} {z : Nat}
    {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(si.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

/-- **A node at an instruction with undefined flags** (`FI`) before the
take, its next pc in its phase. -/
theorem nodeW_fi_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {fi : FI} {z : Nat}
    {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(fi.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_fi (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

/-- **A node at `andq $k, %rsp`** (`z` bytes) before the take, its next pc
in its phase: as `nodeW_fi_pre`, at `andRsp` (`_start`'s alignment). -/
theorem nodeW_and_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {k : Int64} {z : Nat}
    {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(andRsp k, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    obtain ⟨t, hex, hst⟩ := exec_andRsp hc
    exact sfacts_silent (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hst
      (fun _ ⟨_, h⟩ => h ▸ next_same hI hpc hph _) hO

/-- **A node at an instruction with undefined flags** (`FI`) after the
switch, as `nodeW_postO`, its next pc in its phase. -/
theorem nodeW_fi_postO {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {fi : FI} {z : Nat}
    {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(fi.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_fi (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

/-- **A node at a register operation** after the take, the range in private
memory, its next pc in its phase. -/
theorem nodeW_reg_post {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {w : Width}
    {op : Operation w} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hop : RegOnly op = true) (hb : blockAtB cells l off [(.instr (.regular .W64 w op), z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun s c σ hs hn _ hpc _ _ hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    exact sfacts_done (hC σ c hJ) hP hc (fun w w' h => by cases h; simp [RegOnly] at hop) (exec_reg hop hc)
      (next_same hI hpc hph _).1 (next_same hI hpc hph _).2 hO

/-- **A node at a `syscall`** (`z` bytes) before the take, its next pc in
its phase, its `%rax` not `write`'s number (`hnr`). -/
theorem nodeW_syscall_pre {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {z : Nat} {l : Label}
    {off : Nat} {p : Int64} (hb : blockAtB cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hnr : ∀ σ c, n.J σ c → σ.regs.rax.toNat ≠ 1) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_syscall (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.rax.toNat ≠ 1; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at a `syscall`** (`z` bytes) after the take, its next pc in
its phase, its `%rax` not `write`'s number (`hnr`). -/
theorem nodeW_syscall_post {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {z : Nat} {l : Label}
    {off : Nat} {p : Int64} (hb : blockAtB cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub Λ.stackPool)
    (hnr : ∀ σ c, n.J σ c → σ.regs.rax.toNat ≠ 1) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_syscall (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.rax.toNat ≠ 1; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at a `syscall`** (`z` bytes) after the switch, as
`nodeW_postO`, its next pc in its phase, its `%rax` not `write`'s number
(`hnr`). -/
theorem nodeW_syscall_postO {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {z : Nat} {l : Label}
    {off : Nat} {p : Int64} (hb : blockAtB cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hnr : ∀ σ c, n.J σ c → σ.regs.rax.toNat ≠ 1) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_syscall (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.rax.toNat ≠ 1; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at a store** `movq %r, k(%b)` to a mapped word `a` (`hmw`)
unmapped in private memory under the frame condition (`hun`), owned at no
phase (`hno`), before the take, its next pc in its phase. -/
theorem nodeW_st_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label}
    {off : Nat} {p : Int64} {a : BitVec 64} (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_store_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) hmw
      (next_same hI hpc hph _).2
      (.inl ⟨(next_same hI hpc hph _).1, fun w h => by rw [own_at hown hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown' htk hO

/-- **A node at a store** after the take, as `nodeW_st_pre`. -/
theorem nodeW_st_post {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {ownOf : Nat → List
    (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label}
    {off : Nat} {p : Int64} {a : BitVec 64} (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_store_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) hmw
      (next_same hI hpc hph _).2
      (.inl ⟨(next_same hI hpc hph _).1, fun w h => by rw [own_at hown hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown' htk hO

/-- **A node at a load `movq k(%b), %r`** of a mapped word `a` (`hmr`)
unmapped in private memory under the frame condition (`hun`), before the
take, its next pc in its phase. -/
theorem nodeW_ld_pre {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {b r : Reg64} {k : Int64}
    {z : Nat} {l : Label} {off : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAtB cells l off [(ldDir b k r, z)] = true) (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_load_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := load_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s) (z := z)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.set (.low r .W64) (v.setWidth 64) })
      hmr (fun _ => (next_same hI hpc hph _).2) (fun _ => (next_same hI hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown' htk hO

/-- **A node at a thread-pointer load `movq %fs:k, %d`** of a mapped word
`a` (`hmr`) unmapped in private memory under the frame condition (`hun`),
after the switch, as `nodeW_postO`, its next pc in its phase. -/
theorem nodeW_fsld_postO {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {d : Reg64} {k : Int64}
    {z : Nat} {l : Label} {off : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAtB cells l off [(fsDir d k, z)] = true) (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → σ.regs.fsBase.toBitVec + k.toBitVec = a)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : fsAddr s z { base := none, idx := none, disp := .int64 k } = a := by
      rw [← ha σ c hJ]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    have hex := exec_movfs_load_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := load_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s) (z := z)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.set (.low d .W64) (v.setWidth 64) })
      hmr (fun _ => (next_same hI hpc hph _).2) (fun _ => (next_same hI hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown' htk hO

/-- **A node at an owned counter's `lock xaddq %r, k(%b)`** before the
take, its next pc before it too: the counter's word `a` (`ha`), owned at
`p` (`hin`), updated to the sum at the next pc (`hupd`). -/
theorem nodeW_xadd_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {ownOf : Nat → List
    (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label}
    {off : Nat} {p : Int64} {a : BitVec 64} (hb : blockAtB cells l off [(xaddDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hT' : ∀ s : State, pcOf s = (p + Int64.ofNat z).toBitVec.toNat → ¬ Tk s)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (old.setWidth 64 + σ.regs.get64 r).setWidth 128) = true) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_xaddG_agrees (w := .W64) hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    have hpc4 : ∀ m, (after s z m).st.2 = p + Int64.ofNat z := fun _ => by rw [← hpc]
    obtain ⟨hT'', hown', htk⟩ := rmw_facts (Λ := Λ) (own := own) (Tk := Tk) (s := s) (k := .acqRel)
      (nr := false) (z := z)
      (op := fun old => some ((old.setWidth 64 + s.st.1.regs.get (.low r .W64)).setWidth 128))
      (m := fun v => { s.st.1 with
        regs := s.st.1.regs.set (.low r .W64) (v.setWidth 64)
        status := LockBinOp.add.status (v.setWidth 64) (s.st.1.regs.get (.low r .W64))
          (v.setWidth 64 + s.st.1.regs.get (.low r .W64)) false })
      hmw (fun _ => next_tk hpc hT hT' _) (by rw [own_at hown hpc]; exact hin)
      (fun v hv => by
        rw [own_at hown hpc, own_at hown (hpc4 _), Option.getD_some, Reg64s.get_low64, hA.regs]
        rw [own_at hown hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT'' hown' htk hO

/-- **A node at an owned word's `xchgq %r, k(%b)`** before the take, its
next pc before it too: the word `a` (`ha`), owned at `p` (`hin`), set to
`%r` at the next pc (`hupd`). -/
theorem nodeW_xchg_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {ownOf : Nat → List
    (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label}
    {off : Nat} {p : Int64} {a : BitVec 64} (hb : blockAtB cells l off [(xchgDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hT' : ∀ s : State, pcOf s = (p + Int64.ofNat z).toBitVec.toNat → ¬ Tk s)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun _ => (σ.regs.get64 r).setWidth 128) = true) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_xchgG_agrees (w := .W64) hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    have hpc4 : ∀ m, (after s z m).st.2 = p + Int64.ofNat z := fun _ => by rw [← hpc]
    obtain ⟨hT'', hown', htk⟩ := rmw_facts (Λ := Λ) (own := own) (Tk := Tk) (s := s) (k := .acqRel)
      (nr := false) (z := z)
      (op := fun _ => some ((s.st.1.regs.get (.low r .W64)).setWidth 128))
      (m := fun v => { s.st.1 with regs := s.st.1.regs.set (.low r .W64) (v.setWidth 64) })
      hmw (fun _ => next_tk hpc hT hT' _) (by rw [own_at hown hpc]; exact hin)
      (fun v hv => by
        rw [own_at hown hpc, own_at hown (hpc4 _), Option.getD_some, Reg64s.get_low64, hA.regs]
        rw [own_at hown hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT'' hown' htk hO

/-- **A node at an owned word's plain store `movq %r, k(%b)`** before the
take, its next pc before it too: the word `a` (`ha`), owned at `p` (`hin`),
set to `%r` at the next pc (`hupd`). The lock's release on the bump path. -/
theorem nodeW_stown_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {ownOf : Nat → List
    (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label}
    {off : Nat} {p : Int64} {a : BitVec 64} (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hT' : ∀ s : State, pcOf s = (p + Int64.ofNat z).toBitVec.toNat → ¬ Tk s)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun _ => (σ.regs.get64 r).setWidth 128) = true) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_store_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    have hpc4 : (after s z s.st.1).st.2 = p + Int64.ofNat z := by rw [← hpc]
    obtain ⟨v, hv⟩ := hin
    obtain ⟨hT'', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s) (z := z)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) hmw
      (next_tk hpc hT hT' _)
      (.inr (by rw [own_at hown hpc, own_at hown hpc4, Reg64s.get_low64, hA.regs]; exact ownUpd_of (hupd σ c hJ) v hv))
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT'' hown' htk hO

end Node

end Spike.Lib.X64.Rt
