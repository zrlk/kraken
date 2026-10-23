/-
**The runtime's blocks and nodes inside `W`, for any program** (`SFacts`,
`Spike/Lib/A64SegInst.lean`): the block and node lemmas of `ret0.w`'s
instance (`blkW_pre`, `blkW_post`, `blkW_postO`, `nodeW_*`,
`Spike/Lib/A64Ret0I.lean`) over a program `prog` laid out in `exe`, its
labels `lab`, marks `μ`, owned words `own`, take's phase `Tk`, outside move
`K`, phase index `ph` and off-site pcs `okPc`.

- **The instance's facts** (`InstOk`): the layout, the labels, the owned
  words and the take's phase factoring through `ph` (`same`), off-site pcs
  off the marks' sites with no outside move (`off`).
- **A node's memory word** by its facts: mapped in the loaded kernel state
  (`hmw`, `hmr`), unmapped in private memory under the frame condition
  (`hun`); the owned words through a table by phase (`hown`, `ownOf`).
- **A block's phase check** from `RtNodesOk` (`Spike/Lib/Rt/A64RtNodes.lean`,
  a premise A6 discharges): the `_row` forms take a row of the table.
- **Oracle**: the hand lemmas are these at `ret0.w`'s instance
  (`Spike/Test/A64RtW.lean`).
-/
import Spike.Lib.Rt.A64RtNodes
import Spike.Lib.A64Ret0

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackM StackOff stackOff_stable)
open Scc.Cert.Rt.A64 (blockAt OGrp OBlk Lays endOf)

/-- **An instance's facts for its blocks**: `prog` laid out in `exe` (its
end `endPc`), its labels `lab`; the owned words and the take's phase
factoring through `ph` of the pc; an off-site pc (`okPc`) off the marks'
sites, with no outside move. -/
structure InstOk (exe : _root_.Executable) (endPc : Int64) (prog : List Directive) (lab : Label → Int64)
    (μ : Marks) (own : Own) (Tk : State → Prop) (K : State → State → Prop) (okPc : Nat → Bool)
    (ph : Nat → Nat) : Prop where
  lays : Lays exe prog
  endOk : endPc = endOf exe prog
  labOk : (_root_.Executable.labels exe).label = lab
  same : ∀ s s' : State, ph (pcOf s') = ph (pcOf s) → own s' = own s ∧ (Tk s' ↔ Tk s)
  off : ∀ s : State, okPc (pcOf s) = true → PcOff μ s ∧ ∀ s', ¬ K s s'

section Blk

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- **The range owned from a region's cells and the words off it**: every
aligned word of `rS` either lies off the 8-aligned region `R` (`hoff`) or is one of
its cells (`hc`). -/
theorem owned_off {R : Region} (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) {s : State}
    (hoff : StackOff rS R s.st.1) (hc : ∀ k, R.Off k → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome) :
    Owned Λ rS s := by
  refine ⟨hsub, fun a h8 ha ha7 => ?_⟩
  unfold Scc.Sem.A64.privLoad
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

/-- **A covered block before the take** is inside `SFacts`: its code
(`hb`), its cover (`hok`), the region's facts, the source control's facts
at the node (`hC`), the phase check (`hph`), every `ret` returning to `ra`
(`hret`), its dead targets never reached (`hdead`), and its entry not in
the take's phase (`hT`). -/
theorem blkW_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : ∀ s : State, pcOf s = (lab l + Int64.ofNat (4 * k)).toBitVec.toNat → ¬ Tk s) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  rw [he] at hph hT
  have hcode := code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', hsm⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfacts hcode hok hR hal hlo hhi hC hpc hph' fun s m _ _ _ k hk s' _ hpc' htk => ?_
  have := (hsm k hk { s' with st := (s'.st.1, n.pc) } s' rfl hpc').2.mp htk
  exact absurd this (hT _ (by unfold pcOf; rfl))

/-- **A covered block after the take** is inside `SFacts`: as `blkW_pre`
without the entry's phase, its frame condition also `StackM rS` (kept by
the region's writes, `hSM`) and `rS` in the pool (`hsub`). -/
theorem blkW_post (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS)) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n blk := by
  rw [he] at hph
  have hcode := code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfacts hcode hok hR hal hlo hhi hC hpc hph' fun s m hF hD _ k hk s' hm _ _ => ?_
  refine ⟨hsub, fun a h8 ha ha7 => ?_⟩
  unfold Scc.Sem.A64.privLoad
  rw [Option.isSome_map, hm]
  exact hSM _ _ hF.2 hD a h8 ha ha7

/-- **A covered block after the take, in a region whose frame condition
gives the words of `rS` off it** (`hFO`): as `blkW_post`. -/
theorem blkW_postO (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  rw [he] at hph
  have hcode := code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfacts hcode hok hR hal hlo hhi hC hpc hph' fun s m hF hD hc k hk s' hm _ _ => ?_
  subst hm
  exact owned_off hR (by omega) hl hh hsub (stackOff_stable hfit _ _ (hFO _ hF) hD) hc

/-! ### From a row of the table -/

/-- **A row before the take** inside `SFacts`, its phase check from
`RtNodesOk` (`hN`), its cover at the row's offsets (A5). -/
theorem blkW_pre_row (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {dead : Label → Nat → Nat → Bool}
    {ra : Label → Int64} {gs : List OGrp} (hN : RtNodesOk okPc ph dead lab ra gs) {g : OGrp} (hg : g ∈ gs)
    {b : OBlk} (hbm : b ∈ g.bs) {R : Region} {F : MachineData → Prop} {n : ND}
    (hb : blockAt prog g.l b.k b.blk = true) (he : lab g.l + Int64.ofNat (4 * b.k) = n.pc) (ho : n.o = b.o)
    (hok : Flow.okBlk b.lo b.hi b.o b.blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ b.lo) (hhi : b.hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < b.blk.length) r, Flow.classify b.blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (b.blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra g.l)
    (hdead : ∀ σ c, n.J σ c → dead g.l b.k (Flow.arun lab b.blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : ∀ s : State, pcOf s = (lab g.l + Int64.ofNat (4 * b.k)).toBitVec.toNat → ¬ Tk s) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n b.blk :=
  blkW_pre hI hb he (ho ▸ hok) hR hal hlo hhi hC (hN.row hg hbm) hret hdead hT

/-- **A row after the take** inside `SFacts`, as `blkW_post`. -/
theorem blkW_post_row (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {dead : Label → Nat → Nat → Bool}
    {ra : Label → Int64} {gs : List OGrp} (hN : RtNodesOk okPc ph dead lab ra gs) {g : OGrp} (hg : g ∈ gs)
    {b : OBlk} (hbm : b ∈ g.bs) {R : Region} {F : MachineData → Prop} {n : ND}
    (hb : blockAt prog g.l b.k b.blk = true) (he : lab g.l + Int64.ofNat (4 * b.k) = n.pc) (ho : n.o = b.o)
    (hok : Flow.okBlk b.lo b.hi b.o b.blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ b.lo) (hhi : b.hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < b.blk.length) r, Flow.classify b.blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (b.blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra g.l)
    (hdead : ∀ σ c, n.J σ c → dead g.l b.k (Flow.arun lab b.blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS)) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n b.blk :=
  blkW_post hI hb he (ho ▸ hok) hR hal hlo hhi hC (hN.row hg hbm) hret hdead hsub hSM

/-- **A row after the take, the words of `rS` off its region from the
frame condition**, as `blkW_postO`. -/
theorem blkW_postO_row (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {dead : Label → Nat → Nat → Bool}
    {ra : Label → Int64} {gs : List OGrp} (hN : RtNodesOk okPc ph dead lab ra gs) {g : OGrp} (hg : g ∈ gs)
    {b : OBlk} (hbm : b ∈ g.bs) {R : Region} {F : MachineData → Prop} {n : ND}
    (hb : blockAt prog g.l b.k b.blk = true) (he : lab g.l + Int64.ofNat (4 * b.k) = n.pc) (ho : n.o = b.o)
    (hok : Flow.okBlk b.lo b.hi b.o b.blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ b.lo) (hhi : b.hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < b.blk.length) r, Flow.classify b.blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (b.blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra g.l)
    (hdead : ∀ σ c, n.J σ c → dead g.l b.k (Flow.arun lab b.blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n b.blk :=
  blkW_postO hI hb he (ho ▸ hok) hR hal hlo hhi hC (hN.row hg hbm) hret hdead hl hh hsub hfit hFO

end Blk

/-! ## A single instruction's states -/

section Node

open Kraken.Promising.Lower.A64 (CellAt after exec_str_agrees exec_stlr_agrees exec_ldr_agrees exec_ldop exec_swp
  access_agrees)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- An instruction of the program at its label, in the loaded thread. -/
theorem cellOf (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {l : Label} {k : Nat} {d : Directive}
    {p : Int64} (hb : blockAt prog l k [d] = true) (he : lab l + Int64.ofNat (4 * k) = p) {s : State}
    (hs : s.exe = exe) (hn : s.endPc = endPc) (hpc : s.st.2 = p) : CellAt s d 4 :=
  (code_of hI.lays hI.endOk hb (q := lab l + Int64.ofNat (4 * k)) (by rw [hI.labOk]) s hs hn).cell (j := 0)
    rfl rfl rfl (by rw [hpc, ← he]; simp)

omit [Kraken.Executable.ValidLayout exe] in
/-- Past an instruction at `p` whose next pc has its phase, a state owns
what it owns and is in the take's phase iff it is. -/
theorem next_same (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {s : State} {p : Int64}
    (hpc : s.st.2 = p) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) :
    ∀ m, own (after s 4 m) = own s ∧ (Tk (after s 4 m) ↔ Tk s) :=
  fun _ => hI.same _ _ (by
    show ph (s.st.2 + Int64.ofNat 4).toBitVec.toNat = ph s.st.2.toBitVec.toNat; rw [hpc]; exact hph)

/-- Past an instruction at `p`, neither it nor the next pc in the take's
phase, a state is in it iff it is. -/
theorem next_tk {s : State} {p : Int64} (hpc : s.st.2 = p)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hT4 : ∀ s : State, pcOf s = (p + Int64.ofNat 4).toBitVec.toNat → ¬ Tk s) :
    ∀ m, Tk (after s 4 m) ↔ Tk s := fun m =>
  ⟨fun h => absurd h (hT4 _ (by show (s.st.2 + Int64.ofNat 4).toBitVec.toNat = _; rw [hpc])),
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
theorem nodeW_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {p : Int64} (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true) (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (h : ∀ s c σ, s.exe = exe → s.endPc = endPc → s.decls = {} → s.st.2 = p → Flow.Abs R n.o s.st.1 σ →
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
theorem nodeW_post (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {p : Int64} (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true) (hsub : rS.Sub Λ.stackPool)
    (h : ∀ s c σ, s.exe = exe → s.endPc = endPc → s.decls = {} → s.st.2 = p → Flow.Abs R n.o s.st.1 σ →
      F s.st.1 → n.J σ c → PcOff μ s → (Tk s → Owned Λ rS s) → SFacts Λ μ own rS Tk lbl s c) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact hok)
  refine ⟨h s c σ hs hn hdc hpc hA hD.1 hJ hP.1 fun _ => ⟨hsub, fun a h8 ha ha7 => ?_⟩, hP.2⟩
  unfold Scc.Sem.A64.privLoad
  rw [Option.isSome_map]
  exact hD.2 a h8 ha ha7

omit [Kraken.Executable.ValidLayout exe] in
/-- **A node after the take**, in a region whose frame condition gives the
words of `rS` off it (`hFO`): as `nodeW_post`. -/
theorem nodeW_postO (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {p : Int64} (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true)
    (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (h : ∀ s c σ, s.exe = exe → s.endPc = endPc → s.decls = {} → s.st.2 = p → Flow.Abs R n.o s.st.1 σ →
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
theorem nodeW_si_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {si : SI} {l : Label} {k : Nat}
    {p : Int64} (hb : blockAt prog l k [si.toDir] = true) (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

/-- **A node at a single instruction without an event** (`SI`) after the
take, its next pc in its phase. -/
theorem nodeW_si_post (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {si : SI} {l : Label} {k : Nat}
    {p : Int64} (hb : blockAt prog l k [si.toDir] = true) (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

/-- **A node at a register operation** after the take, the range in private
memory, its next pc in its phase. -/
theorem nodeW_reg_post (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {w : RegWidth}
    {op : Operation w} {l : Label} {k : Nat} {p : Int64}
    (hop : RegOnly op = true) (hb : blockAt prog l k [.instr ⟨w, op⟩] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun s c σ hs hn _ hpc _ _ hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    exact sfacts_done (hC σ c hJ) hP hc (fun imm h => by cases h; simp [RegOnly] at hop) (exec_reg hop hc)
      (next_same hI hpc hph _).1 (next_same hI hpc hph _).2 hO

/-- **A node at `svc #0`** before the take, its next pc in its phase, its
`x8` not `write`'s number (`hnr`). -/
theorem nodeW_svc_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {l : Label} {k : Nat}
    {p : Int64} (hb : blockAt prog l k [svcDir] = true) (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hnr : ∀ σ c, n.J σ c → σ.regs.X8.toNat ≠ 64) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_svc (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.X8.toNat ≠ 64; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at `svc #0`** after the take, as `nodeW_postO`, its next pc in
its phase, its `x8` not `write`'s number (`hnr`). -/
theorem nodeW_svc_postO (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {l : Label} {k : Nat}
    {p : Int64} (hb : blockAt prog l k [svcDir] = true) (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hnr : ∀ σ c, n.J σ c → σ.regs.X8.toNat ≠ 64) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_svc (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.X8.toNat ≠ 64; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at a store** `str Xt, [Xn, #i]` to a mapped word `a` (`hmw`)
unmapped in private memory under the frame condition (`hun`), owned at no
phase (`hno`), before the take, its next pc in its phase. -/
theorem nodeW_st_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAt prog l k [strDir t b i] = true) (he : lab l + Int64.ofNat (4 * k) = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_str_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) hmw
      (next_same hI hpc hph _).2
      (.inl ⟨(next_same hI hpc hph _).1, fun w h => by rw [own_at hown hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

/-- **A node at a store** after the take, as `nodeW_st_pre`. -/
theorem nodeW_st_post (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAt prog l k [strDir t b i] = true) (he : lab l + Int64.ofNat (4 * k) = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_str_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) hmw
      (next_same hI hpc hph _).2
      (.inl ⟨(next_same hI hpc hph _).1, fun w h => by rw [own_at hown hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

/-- **A node at a load `ldr Xt, [Xn, #i]`** of a mapped word `a` (`hmr`)
unmapped in private memory under the frame condition (`hun`), before the
take, its next pc in its phase. -/
theorem nodeW_ldr_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {t b : XReg} {i : Int64}
    {l : Label} {k : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAt prog l k [ldrDir t b i] = true) (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_ldr_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := load_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) })
      hmr (fun _ => (next_same hI hpc hph _).2) (fun _ => (next_same hI hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

/-- **A node at a load** after the take, as `nodeW_ldr_pre` and
`nodeW_postO`. -/
theorem nodeW_ldr_postO (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {n : ND} {t b : XReg} {i : Int64}
    {l : Label} {k : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAt prog l k [ldrDir t b i] = true) (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_ldr_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := load_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) })
      hmr (fun _ => (next_same hI hpc hph _).2) (fun _ => (next_same hI hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

/-- **A node at an owned counter's `ld<op><k> Xs, Xt, [Xn]`** before the
take, its next pc before it too: the counter's word `a` (`ha`), owned at
`p` (`hin`), updated to the operation's result at the next pc (`hupd`). -/
theorem nodeW_ldop_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {op : AtomicOp} {kk : RmwKind} {rs rt b : XReg}
    {l : Label} {k : Nat} {p : Int64} {a : BitVec 64} (hb : blockAt prog l k [ldopDir op kk rs rt b] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hT4 : ∀ s : State, pcOf s = (p + Int64.ofNat 4).toBitVec.toNat → ¬ Tk s)
    (ha : ∀ σ c, n.J σ c → (σ.regs.getXReg b).toBitVec = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat 4).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (op.apply (old.setWidth 64) (σ.regs.getRegOrZr (.low (.reg rs) .W64))).setWidth 128)
      = true) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_ldop hc (by rw [ha']; exact hun _ hD)
    rw [ha', access_agrees (agrees_of_decls hdc _ _)] at hex
    have hpc4 : ∀ m, (after s 4 m).st.2 = p + Int64.ofNat 4 := fun _ => by rw [← hpc]
    obtain ⟨hT', hown', htk⟩ := rmw_facts (Λ := Λ) (own := own) (Tk := Tk) (s := s) (k := kk)
      (nr := (RegOrZr.low (.reg rt) .W64 : RegOrZr .W64).isZr)
      (op := fun old => some ((op.apply (old.setWidth 64) (s.st.1.regs.getRegOrZr (.low (.reg rs) .W64))).setWidth 128))
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (v.setWidth 64) })
      hmw (fun _ => next_tk hpc hT hT4 _) (by rw [own_at hown hpc]; exact hin)
      (fun v hv => by
        rw [own_at hown hpc, own_at hown (hpc4 _), Option.getD_some, hA.regs]
        rw [own_at hown hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

/-- **A node at an owned word's `swp<k> Xs, Xt, [Xn]`** before the take,
its next pc before it too: the word `a` (`ha`), owned at `p` (`hin`), set to
`Xs` at the next pc (`hupd`). -/
theorem nodeW_swp_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {kk : RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    {p : Int64} {a : BitVec 64}
    (hb : blockAt prog l k
      [.instr ⟨.W64, .SWP kk .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hT4 : ∀ s : State, pcOf s = (p + Int64.ofNat 4).toBitVec.toNat → ¬ Tk s)
    (ha : ∀ σ c, n.J σ c → (σ.regs.getXReg b).toBitVec = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat 4).toBitVec.toNat))
      ⟨a, 8⟩ (fun _ => (σ.regs.getRegOrZr (.low (.reg rs) .W64)).setWidth 128) = true) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_swp hc (by rw [ha']; exact hun _ hD)
    rw [ha', access_agrees (agrees_of_decls hdc _ _)] at hex
    have hpc4 : ∀ m, (after s 4 m).st.2 = p + Int64.ofNat 4 := fun _ => by rw [← hpc]
    obtain ⟨hT', hown', htk⟩ := rmw_facts (Λ := Λ) (own := own) (Tk := Tk) (s := s) (k := kk)
      (nr := (RegOrZr.low (.reg rt) .W64 : RegOrZr .W64).isZr)
      (op := fun _ => some ((s.st.1.regs.getRegOrZr (.low (.reg rs) .W64)).setWidth 128))
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (v.setWidth 64) })
      hmw (fun _ => next_tk hpc hT hT4 _) (by rw [own_at hown hpc]; exact hin)
      (fun v hv => by
        rw [own_at hown hpc, own_at hown (hpc4 _), Option.getD_some, hA.regs]
        rw [own_at hown hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

/-- **A node at an owned word's release store `stlr Xt, [Xn]`** before the
take, its next pc before it too: the word `a` (`ha`), owned at `p` (`hin`),
set to `Xt` at the next pc (`hupd`). -/
theorem nodeW_stlr_pre (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {t b : XReg} {l : Label} {k : Nat} {p : Int64}
    {a : BitVec 64}
    (hb : blockAt prog l k [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hT4 : ∀ s : State, pcOf s = (p + Int64.ofNat 4).toBitVec.toNat → ¬ Tk s)
    (ha : ∀ σ c, n.J σ c → (σ.regs.getXReg b).toBitVec = a) (hmw : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat 4).toBitVec.toNat))
      ⟨a, 8⟩ (fun _ => (σ.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) = true) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_stlr_agrees hc (by rw [ha']; exact hun _ hD) (agrees_of_decls hdc _ _)
    rw [ha'] at hex
    have hpc4 : (after s 4 s.st.1).st.2 = p + Int64.ofNat 4 := by rw [← hpc]
    obtain ⟨v, hv⟩ := hin
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .rel) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) hmw
      (next_tk hpc hT hT4 _)
      (.inr (by rw [own_at hown hpc, own_at hown hpc4, hA.regs]; exact ownUpd_of (hupd σ c hJ) v hv))
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

end Node

end Spike.Lib.A64.Rt
