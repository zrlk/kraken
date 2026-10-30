/-
**`wc_main` up to `.sp3` inside `SFactsSt2` at wake.w's global owned-words
map `ownG`** (AArch64): the `SFactsSt2` component of the pre-spawn
chain's `W` at `wc_main`'s own blocks before `.sp4` (the prologue, the
entry block, `.sp0`'s block and box store, the fence and the reserve's
call), proved at the first instance (`instOkW`, owned words
`ownW L a (phW pc)`, no take phase) and moved to `ownG`, which picks `ownW`
at every pc off its four ranges (`GoodW`'s last disjunct).

The pcs are checked by the kernel against the certificate's labels, with
no absolute address in this file: `freeN` (a pc off `ownG`'s ranges and
off the take site), `freeAt` (the pcs of a block), `wcTabW` (the blocks'
phase facts).

- `cv`, `freeN`, `freeAt`, `freeAt_pc`: the label-relative checks.
- `goodW_of_freeN`, `site_ne_of_freeN`: `GoodW` and off the take site.
- `blkAgreeW`: a block's agreement with `ownW` from its pcs and its
  final pc off `ownG`'s ranges.
- `wcTabW`, `wcW_fact`: the blocks' phase facts at `phW`.
- `blkW_wcG`: a block of `wc_main` before `.sp4` inside `SFactsSt2` at `ownG`.
-/
import Spike.Lib.A64WakeWcRes
import Spike.Lib.A64WakeStart
import Spike.Lib.A64WakeTcb2CallW

namespace Spike.Lib.A64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk blockAt pcAt)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl CFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.Rt.PhOfTab (pcAt_eq pcAt0_eq blkPh_of_factOk step_of_factOk)

/-! ## The label-relative checks -/

/-- A label's address in wakeProg at the canonical base (`0` if absent). -/
def cv (l : Label) : Nat := (codeOf lo wakeProg l).getD 0

/-- `x` in `[cv l₁, cv l₂)`. -/
def inCv (l₁ l₂ : Label) (x : Nat) : Bool := cv l₁ ≤ x && x < cv l₂

/-- **A pc where `ownG` picks `ownW` whatever the state**: off `ownG`'s four
ranges, and off the take site. -/
def freeN (x : Nat) : Bool :=
  !inCv "scc_rt_alloc_tcb" "scc_rt_thread_reserve" x && !inCv "scc_rt_thread_init" "scc_rt_stack_release" x &&
    !inCv ".L21_wc_main.sp4" ".L21_wc_main.stack_grow" x && !inCv "scc_rt_abort" "scc_rt_thr_worker" x &&
    x != cv Spike.Lib.A64.Flow.Ret0.StackTake.siteL

/-- **The `n` pcs from `l + 4 k` are free.** -/
def freeAt (l : Label) (k n : Nat) : Bool :=
  (List.range n).all fun j => match pcAt (codeOf lo wakeProg) l (k + j) with
    | some t => freeN t
    | none => false

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

/-- A label of wakeProg read through `L.lab`. -/
theorem lab_cv (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {l : Label}
    (hs : (codeOf lo wakeProg l).isSome = true) (hb : cv l < 2 ^ 64) : (L.lab l).toBitVec.toNat = cv l := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  have e : cv l = x := by simp [cv, hx]
  rw [e] at hb ⊢
  rw [hlab l x hx]
  show (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

/-- **The pcs `freeAt` checks**, read through `L.lab`. -/
theorem freeAt_pc (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {k n : Nat} (h : freeAt l k n = true) {j : Nat} (hj : j < n) :
    freeN (L.lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j)).toBitVec.toNat = true := by
  have h1 := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  revert h1
  cases ht : pcAt (codeOf lo wakeProg) l (k + j) with
  | none => intro h1; cases h1
  | some t =>
    intro h1
    have e := pcAt_eq hlab ht
    rw [Nat.mul_add, Int64.ofNat_add, ← Int64.add_assoc] at e
    rw [e]; exact h1

/-- **`freeAt` at one pc.** -/
theorem freeAt_pc0 (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {k : Nat} (h : freeAt l k 1 = true) : freeN (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true := by
  have := freeAt_pc hlab h (j := 0) (by decide)
  rwa [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero] at this

/-- **`freeAt` at a label.** -/
theorem freeAt_lab (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {l : Label}
    (h : freeAt l 0 1 = true) : freeN (L.lab l).toBitVec.toNat = true := by
  have := freeAt_pc0 hlab h
  rwa [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero] at this

/-- The labels `freeN` reads are wakeProg's, below `2 ^ 64`. -/
theorem freeLabs :
    [("scc_rt_alloc_tcb" : Label), "scc_rt_thread_reserve", "scc_rt_thread_init", "scc_rt_stack_release",
      ".L21_wc_main.sp4", ".L21_wc_main.stack_grow", "scc_rt_abort", "scc_rt_thr_worker",
      Spike.Lib.A64.Flow.Ret0.StackTake.siteL].all
      (fun l => (codeOf lo wakeProg l).isSome && decide (cv l < 2 ^ 64)) = true := by
  rw [← codeT_eq]; decide +kernel

/-- **At a free pc `ownG` picks `ownW`.** -/
theorem goodW_of_freeN (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (h : freeN (pcOf s) = true) : GoodW L s := by
  have hl : ∀ l ∈ [("scc_rt_alloc_tcb" : Label), "scc_rt_thread_reserve", "scc_rt_thread_init",
      "scc_rt_stack_release", ".L21_wc_main.sp4", ".L21_wc_main.stack_grow", "scc_rt_abort",
      "scc_rt_thr_worker", Spike.Lib.A64.Flow.Ret0.StackTake.siteL], (L.lab l).toBitVec.toNat = cv l := by
    intro l hl
    have := List.all_eq_true.mp freeLabs l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact lab_cv hlab this.1 this.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := hl
  simp only [freeN, inCv, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    bne_iff_ne, ne_eq, Nat.not_le, Nat.not_lt] at h
  refine .inr (.inr ⟨?_, ?_, ?_, ?_⟩) <;> unfold inPc <;> simp only [e1, e2, e3, e4, e5, e6, e7, e8] <;> omega

/-- **A free pc is off the take site.** -/
theorem site_ne_of_freeN (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    {x : Nat} (h : freeN x = true) : x ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have := List.all_eq_true.mp freeLabs Spike.Lib.A64.Flow.Ret0.StackTake.siteL (by simp)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rw [lab_cv hlab this.1 this.2]
  simp only [freeN, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

/-! ## A block's agreement -/

section Agree

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {n : ND} {blk : List Directive} {blo bhi : Int}

/-- **`ownG` agrees with `ownW` on a covered block at free pcs**: its pcs
(`hin`) and the pc its run ends at (`hlast`) free, the take site `L`'s. -/
theorem blkAgreeW (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hsite : μ.site .take = some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hin : ∀ k < blk.length, freeN (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hlast : ∀ σ c, n.J σ c →
      freeN (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label blk
        ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = ownW L a (phW (pcOf s'))) (fun _ _ => False) exe endPc R F n blk := by
  refine hagW hlab hcode hok hR hal hlo hhi (fun x hx k hk => ?_) (fun σ c _ k hk s m _ _ _ hs => ?_)
    (fun σ c hJ k hk s m _ _ _ hs => ?_)
  · rw [hsite] at hx; cases hx
    exact site_ne_of_freeN hlab (hin k hk)
  · exact goodW_of_freeN hlab (by unfold pcOf; rw [hs]; exact hin k hk)
  · refine goodW_of_freeN hlab ?_
    unfold pcOf; rw [hs]
    rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
    · rw [Spike.Lib.A64.Flow.arun_pc _ hok hk1]; exact hin (k + 1) hk1
    · rw [List.take_of_length_le (by omega)]; exact hlast σ c hJ

end Agree

/-! ## The blocks' phase facts -/

/-- **`wc_main`'s blocks before `.sp4`**: the prologue's three blocks and its
load, the entry block, `.sp0`'s block, its store, the fence, the reserve's
call. -/
def wcTabW : List PhFact :=
  [.blk ".L21_wc_main.stack_check" 0 (Spike.Lib.A64.Flow.chkHead 80) none none,
   .step ".L21_wc_main.stack_check" 2,
   .blk ".L21_wc_main.stack_check" 3 (Spike.Lib.A64.Flow.chkBr ".L21_wc_main.stack_grow") none none,
   .blk ".L21_wc_main.stack_check" 5 (Spike.Lib.A64.Flow.frameSet 80 [(.X0, 0)]) none none,
   .blk ".L21_wc_main.0_entry" 0 Spike.Lib.A64.Flow.WakeWc.wcE none none,
   .blk ".L21_wc_main.sp0" 0 Spike.Lib.A64.Flow.WakeWc.wcS0 none none,
   .step ".L21_wc_main.sp0" 3, .step ".L21_wc_main.sp0" 4,
   .blk ".L21_wc_main.sp0" 5 Spike.Lib.A64.Flow.WakeWc.resB none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem wcFactsW : wcTabW.all (factOk (codeT lo wakeProg) okC phC) = true := by
  decide +kernel

/-- **A fact of `wcTabW` at `phW`.** -/
theorem wcW_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ wcTabW) : factOk (codeOf lo wakeProg) (okPcOf lo wakeProg Λ) phW f = true := by
  have := List.all_eq_true.mp wcFactsW f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at this
  exact this

/-! ## A block inside `SFactsSt2` at `ownG` -/

/-- **A block's obligation at another invariant** (`LowerA64.BlkW.mapC`,
not imported here): same pc and offsets, each control of `n`'s invariant
with one of `n'`'s at the same state, `W` there giving `W'` here. -/
theorem blkW_mapC {W W' : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop} {n n' : ND} {blk : List Directive} (hpc : n'.pc = n.pc)
    (ho : n'.o = n.o) (h : BlkW W K exe endPc R F n' blk)
    (hJ : ∀ σ c, n.J σ c → ∃ c', n'.J σ c' ∧ ∀ s, W s c' → W' s c) : BlkW W' K exe endPc R F n blk := by
  obtain ⟨pc, o, J⟩ := n
  obtain ⟨pc', o', J'⟩ := n'
  simp only at hpc ho
  subst hpc ho
  intro s σ c he hn hd hp hA hF hJn k hk m hA' hD
  obtain ⟨c', hJ', hW⟩ := hJ σ c hJn
  obtain ⟨h1, h2⟩ := h s σ c' he hn hd hp hA hF hJ' k hk m hA' hD
  exact ⟨hW _ h1, h2⟩

/-- **A node's obligation at another invariant** (as `blkW_mapC`). -/
theorem nodeW_mapC {W W' : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop} {n n' : ND} (hpc : n'.pc = n.pc) (ho : n'.o = n.o)
    (h : NodeW W K exe endPc R F n') (hJ : ∀ σ c, n.J σ c → ∃ c', n'.J σ c' ∧ ∀ s, W s c' → W' s c) :
    NodeW W' K exe endPc R F n := by
  obtain ⟨pc, o, J⟩ := n
  obtain ⟨pc', o', J'⟩ := n'
  simp only at hpc ho
  subst hpc ho
  rintro s c ⟨h1, h2, h3, h4, σ, hA, hF, hJn⟩
  obtain ⟨c', hJ', hW⟩ := hJ σ c hJn
  obtain ⟨hw, hk⟩ := h s c' ⟨h1, h2, h3, h4, σ, hA, hF, hJ'⟩
  exact ⟨hW _ hw, hk⟩

/-- **A covered `ret`-free block of `wc_main` before `.sp4` inside
`SFactsSt2` at `ownG`**, at the outside move of any range `rS`: `blkW_pre`
at the first instance with no take phase (`instOkW`), the source control
replaced by `A64Consumer.c0` (`cfacts_c0`: the state facts do not read it),
moved to `ownG` (`blkAgreeW`) at its free pcs (`hfree`) and free end
(`hlast`), its phase fact `hf` from `wcTabW`. -/
theorem blkW_wcG (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND}
    {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt wakeProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hf : PhFact.blk l k blk none none ∈ wcTabW) (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hfree : freeAt l k blk.length = true)
    (hlast : ∀ σ c, n.J σ c →
      freeN (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.A64Consumer.c0 ∧ ∃ c', n.J σ c'⟩
  have hph := blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false) (fun _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (wcW_fact hΛ hf)
  have hW := Spike.Lib.A64.Rt.blkW_pre (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ)
    (lbl := fun _ => none) (rS := rS) (F := F) (n := n') (hp ▸ hb) he hok hR hal hlo' hhi
    (fun _ _ hJ => hJ.1 ▸ Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0) hph
    (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hag := blkAgreeW (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) (n := n') hlab hcode hok hR hal hlo' hhi
    hsite (fun j hj => by rw [← he]; exact freeAt_pc hlab hfree hj)
    (fun σ c hJ => let ⟨_, hJ'⟩ := hJ.2; hlast σ _ hJ')
  have h2 := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 hW) hag
  exact blkW_mapC (n' := n') rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-- info: 'Spike.Lib.A64.WakePh.WcW.freeLabs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.freeLabs

/-- info: 'Spike.Lib.A64.WakePh.WcW.goodW_of_freeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.goodW_of_freeN

/-- info: 'Spike.Lib.A64.WakePh.WcW.blkAgreeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.blkAgreeW

/-- info: 'Spike.Lib.A64.WakePh.WcW.wcFactsW' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.wcFactsW

/-- info: 'Spike.Lib.A64.WakePh.WcW.blkW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.blkW_wcG

end Spike.Lib.A64.WakePh.WcW
