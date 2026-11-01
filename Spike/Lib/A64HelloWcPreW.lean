/-
**hello.w's `wc_main` before `.sp4` inside `SFactsSt2` at `ownGH`: the
label-relative checks and the block/node movers** (AArch64): the twin of `Spike/Lib/A64WakeWcPreW.lean` and the
program-specific
half of `Spike/Lib/A64WakeWcPreWN.lean` at helloProg. A block or a node of
`wc_main` before `.sp4` is proved at the first instance (`instOkH`, owned
words `ownH L a (phH pc)`, no take phase) and moved to `ownGH`, which
picks `ownH` at every pc off its four ranges (`GoodWH`'s last disjunct).

The pcs are checked by the kernel against helloProg's labels, with no
absolute address in this file. wake's program-independent pieces are reused:
`WcW.blkW_mapC`, `WcW.nodeW_mapC`, `WcW.nodeW_dmb_pre`, `WcW.succ_pc4`,
`WcW.c0N`, `WcW.c0N_cfacts`, `WcW.NodeW.ofAll`.

- `cvH`, `inCvH`, `freeNH`, `freeAtH`, `lab_cvH`, `freeAt_pcH`,
  `freeAt_pc0H`, `freeAt_labH`, `freeLabsH`: the label-relative checks.
- `goodW_of_freeNH`, `site_ne_of_freeNH`: `GoodWH` and off the take site.
- `blkAgreeWH`, `nodeAgreeWH`: a block's (a node's) agreement with `ownH`.
- `wcTabWH`, `wcFactsWH`, `wcW_factH`: the blocks' phase facts at `phH`
  (frame 144, five argument spills).
- `blkW_wcGH`, `nodeW_wcGH`: a block (a node) of `wc_main` before `.sp4`
  inside `SFactsSt2` at `ownGH`.
-/
import Spike.Lib.A64HelloTcb2CallW
import Spike.Lib.A64HelloWcSp0
import Spike.Lib.A64WakeWcPreWN

namespace Spike.Lib.A64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk blockAt pcAt)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl CFacts SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.Rt.PhOfTab (pcAt_eq pcAt0_eq blkPh_of_factOk step_of_factOk)
open Kraken.Promising.Lower.A64 (CellAt after)
open Spike.Lib.A64.HelloPh
open Spike.Lib.A64.WakePh (inPc)
open Spike.Lib.A64.WakePh.WcW (blkW_mapC nodeW_mapC succ_pc4 c0N)

/-! ## The label-relative checks -/

/-- A label's address in SccCode.helloProg at the canonical base (`0` if absent). -/
def cvH (l : Label) : Nat := (codeOf lo SccCode.helloProg l).getD 0

/-- `x` in `[cvH l₁, cvH l₂)`. -/
def inCvH (l₁ l₂ : Label) (x : Nat) : Bool := cvH l₁ ≤ x && x < cvH l₂

/-- **A pc where `ownGH` picks `ownH` whatever the state**: off `ownGH`'s four
ranges, and off the take site. -/
def freeNH (x : Nat) : Bool :=
  !inCvH "scc_rt_alloc_tcb" "scc_rt_thread_reserve" x && !inCvH "scc_rt_thread_init" "scc_rt_stack_release" x &&
    !inCvH ".L22_wc_main.sp4" ".L22_wc_main.stack_grow" x && !inCvH "scc_rt_abort" "scc_rt_thr_worker" x &&
    x != cvH Spike.Lib.A64.Flow.Ret0.StackTake.siteL

/-- **The `n` pcs from `l + 4 k` are free.** -/
def freeAtH (l : Label) (k n : Nat) : Bool :=
  (List.range n).all fun j => match pcAt (codeOf lo SccCode.helloProg) l (k + j) with
    | some t => freeNH t
    | none => false

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

/-- A label of SccCode.helloProg read through `L.lab`. -/
theorem lab_cvH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {l : Label}
    (hs : (codeOf lo SccCode.helloProg l).isSome = true) (hb : cvH l < 2 ^ 64) : (L.lab l).toBitVec.toNat = cvH l := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  have e : cvH l = x := by simp [cvH, hx]
  rw [e] at hb ⊢
  rw [hlab l x hx]
  show (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

/-- **The pcs `freeAtH` checks**, read through `L.lab`. -/
theorem freeAt_pcH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {k n : Nat} (h : freeAtH l k n = true) {j : Nat} (hj : j < n) :
    freeNH (L.lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j)).toBitVec.toNat = true := by
  have h1 := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  revert h1
  cases ht : pcAt (codeOf lo SccCode.helloProg) l (k + j) with
  | none => intro h1; cases h1
  | some t =>
    intro h1
    have e := pcAt_eq hlab ht
    rw [Nat.mul_add, Int64.ofNat_add, ← Int64.add_assoc] at e
    rw [e]; exact h1

/-- **`freeAtH` at one pc.** -/
theorem freeAt_pc0H (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {k : Nat} (h : freeAtH l k 1 = true) : freeNH (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true := by
  have := freeAt_pcH hlab h (j := 0) (by decide)
  rwa [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero] at this

/-- **`freeAtH` at a label.** -/
theorem freeAt_labH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {l : Label}
    (h : freeAtH l 0 1 = true) : freeNH (L.lab l).toBitVec.toNat = true := by
  have := freeAt_pc0H hlab h
  rwa [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero] at this

/-- The labels `freeNH` reads are SccCode.helloProg's, below `2 ^ 64`. -/
theorem freeLabsH :
    [("scc_rt_alloc_tcb" : Label), "scc_rt_thread_reserve", "scc_rt_thread_init", "scc_rt_stack_release",
      ".L22_wc_main.sp4", ".L22_wc_main.stack_grow", "scc_rt_abort", "scc_rt_thr_worker",
      Spike.Lib.A64.Flow.Ret0.StackTake.siteL].all
      (fun l => (codeOf lo SccCode.helloProg l).isSome && decide (cvH l < 2 ^ 64)) = true := by
  rw [← codeT_eq]; decide +kernel

/-- **At a free pc `ownGH` picks `ownH`.** -/
theorem goodW_of_freeNH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (h : freeNH (pcOf s) = true) : GoodWH L s := by
  have hl : ∀ l ∈ [("scc_rt_alloc_tcb" : Label), "scc_rt_thread_reserve", "scc_rt_thread_init",
      "scc_rt_stack_release", ".L22_wc_main.sp4", ".L22_wc_main.stack_grow", "scc_rt_abort",
      "scc_rt_thr_worker", Spike.Lib.A64.Flow.Ret0.StackTake.siteL], (L.lab l).toBitVec.toNat = cvH l := by
    intro l hl
    have := List.all_eq_true.mp freeLabsH l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact lab_cvH hlab this.1 this.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := hl
  simp only [freeNH, inCvH, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    bne_iff_ne, ne_eq, Nat.not_le, Nat.not_lt] at h
  refine .inr (.inr ⟨?_, ?_, ?_, ?_⟩) <;> unfold inPc <;> simp only [e1, e2, e3, e4, e5, e6, e7, e8] <;> omega

/-- **A free pc is off the take site.** -/
theorem site_ne_of_freeNH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {x : Nat} (h : freeNH x = true) : x ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have := List.all_eq_true.mp freeLabsH Spike.Lib.A64.Flow.Ret0.StackTake.siteL (by simp)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rw [lab_cvH hlab this.1 this.2]
  simp only [freeNH, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

/-! ## A block's agreement -/

section Agree

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {n : ND} {blk : List Directive} {blo bhi : Int}

/-- **`ownGH` agrees with `ownH` on a covered block at free pcs**: its pcs
(`hin`) and the pc its run ends at (`hlast`) free, the take site `L`'s. -/
theorem blkAgreeWH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hsite : μ.site .take = some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hin : ∀ k < blk.length, freeNH (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hlast : ∀ σ c, n.J σ c →
      freeNH (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label blk
        ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => ownGH L a s = ownH L a (phH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = ownH L a (phH (pcOf s'))) (fun _ _ => False) exe endPc R F n blk := by
  refine hagWH hlab hcode hok hR hal hlo hhi (fun x hx k hk => ?_) (fun σ c _ k hk s m _ _ _ hs => ?_)
    (fun σ c hJ k hk s m _ _ _ hs => ?_)
  · rw [hsite] at hx; cases hx
    exact site_ne_of_freeNH hlab (hin k hk)
  · exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs]; exact hin k hk)
  · refine goodW_of_freeNH hlab ?_
    unfold pcOf; rw [hs]
    rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
    · rw [Spike.Lib.A64.Flow.arun_pc _ hok hk1]; exact hin (k + 1) hk1
    · rw [List.take_of_length_le (by omega)]; exact hlast σ c hJ

end Agree

/-! ## The blocks' phase facts -/

/-- **`wc_main`'s blocks before `.sp4`**: the prologue's three blocks and its
load, the entry block, `.sp0`'s block, its store, the fence, the reserve's
call. -/
def wcTabWH : List PhFact :=
  [.blk ".L22_wc_main.stack_check" 0 (Spike.Lib.A64.Flow.chkHead 144) none none,
   .step ".L22_wc_main.stack_check" 2,
   .blk ".L22_wc_main.stack_check" 3 (Spike.Lib.A64.Flow.chkBr ".L22_wc_main.stack_grow") none none,
   .blk ".L22_wc_main.stack_check" 5
     (Spike.Lib.A64.Flow.frameSet 144 [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)]) none none,
   .blk ".L22_wc_main.0_entry" 0 Spike.Lib.A64.Flow.HelloWc.wcEH none none,
   .blk ".L22_wc_main.sp0" 0 Spike.Lib.A64.Flow.HelloWc.wcS0H none none,
   .step ".L22_wc_main.sp0" 3, .step ".L22_wc_main.sp0" 4,
   .blk ".L22_wc_main.sp0" 5 Spike.Lib.A64.Flow.HelloWc.resBH none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem wcFactsWH : wcTabWH.all (factOk (codeT lo SccCode.helloProg) okC phC) = true := by
  decide +kernel

/-- **A fact of `wcTabWH` at `phH`.** -/
theorem wcW_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ wcTabWH) : factOk (codeOf lo SccCode.helloProg) (okPcOf lo SccCode.helloProg Λ) phH f = true := by
  have := List.all_eq_true.mp wcFactsWH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

/-! ## A block inside `SFactsSt2` at `ownGH` -/

/-- **A covered `ret`-free block of `wc_main` before `.sp4` inside
`SFactsSt2` at `ownGH`**, at the outside move of any range `rS`: `blkW_pre`
at the first instance with no take phase (`instOkH`), the source control
replaced by `A64Consumer.c0` (`cfacts_c0`: the state facts do not read it),
moved to `ownGH` (`blkAgreeWH`) at its free pcs (`hfree`) and free end
(`hlast`), its phase fact `hf` from `wcTabWH`. -/
theorem blkW_wcGH (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND}
    {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hf : PhFact.blk l k blk none none ∈ wcTabWH) (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hfree : freeAtH l k blk.length = true)
    (hlast : ∀ σ c, n.J σ c →
      freeNH (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.A64Consumer.c0 ∧ ∃ c', n.J σ c'⟩
  have hph := blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false) (fun _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (wcW_factH hΛ hf)
  have hW := Spike.Lib.A64.Rt.blkW_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ)
    (lbl := fun _ => none) (rS := rS) (F := F) (n := n') (hp ▸ hb) he hok hR hal hlo' hhi
    (fun _ _ hJ => hJ.1 ▸ Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0) hph
    (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hag := blkAgreeWH (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) (n := n') hlab hcode hok hR hal hlo' hhi
    hsite (fun j hj => by rw [← he]; exact freeAt_pcH hlab hfree hj)
    (fun σ c hJ => let ⟨_, hJ'⟩ := hJ.2; hlast σ _ hJ')
  have h2 := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 hW) hag
  exact blkW_mapC (n' := n') rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-! ## A node's agreement -/

section Agree

variable {L : RuntimeLayout} {a : BitVec 64} {μ : Marks} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND}

/-- **`ownGH` agrees with `ownH` at a node** whose pc and next pc are free
(`hf0`, `hf4`), each of its states at a 4-byte cell off `svc` whose leaves
are 4 bytes on (`hstep`). -/
theorem nodeAgreeWH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : μ.site .take = some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hf0 : freeNH n.pc.toBitVec.toNat = true) (hf4 : freeNH (n.pc + Int64.ofNat 4).toBitVec.toNat = true)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d 4 ∧ (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧
      isaLSE2.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeW (fun s _ => ownGH L a s = ownH L a (phH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = ownH L a (phH (pcOf s'))) (fun _ _ => False) exe endPc R F n := by
  intro s c hAt
  have hpc : s.st.2 = n.pc := hAt.2.2.2.1
  have hp0 : pcOf s = n.pc.toBitVec.toNat := by unfold pcOf; rw [hpc]
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hAt
  refine ⟨⟨ownGH_W hlab (goodW_of_freeNH hlab (by rw [hp0]; exact hf0)), fun s' h => ?_⟩, fun _ h => h⟩
  have hns : ∀ x, μ.site .take = some x → pcOf s ≠ x := by
    intro x hx; rw [hsite] at hx; cases hx; rw [hp0]; exact site_ne_of_freeNH hlab hf0
  have e := succ_pc4 hc hd hex hl hns h
  refine ownGH_W hlab (goodW_of_freeNH hlab ?_)
  unfold pcOf; rw [e, hpc]; exact hf4

end Agree

/-! ## A node at `ownGH` from the instance's -/

section Move

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {rS : Range} {TkW : Nat → Prop}
  {lbl : Lbl} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A node of `wc_main` inside `SFactsSt2` at `ownGH`** from the
instance's `SFacts` at `c0N n` (`h`), its pc and next pc free (`hf0`,
`hf4`), each state at a 4-byte cell off `svc` whose leaves are 4 bytes on
(`hstep`). -/
theorem nodeW_wcGH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) {K : State → State → Prop} {n : ND}
    (h : NodeW (fun s c => SFacts Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
      (fun s => TkW (phH (pcOf s))) lbl s c) K L.exe L.endPc R F (c0N n))
    (hf0 : freeNH n.pc.toBitVec.toNat = true) (hf4 : freeNH (n.pc + Int64.ofNat 4).toBitVec.toNat = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n := by
  have hag := nodeAgreeWH (a := a) (n := c0N n) (exe := L.exe) (endPc := L.endPc) (R := R) (F := F) hlab hsite
    hf0 hf4 fun s c ⟨h1, h2, h3, h4, σ, hA, hF, _, c', hJ⟩ => hstep s c' ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩
  have h2 := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 h) hag
  exact nodeW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

end Move

end Spike.Lib.A64.HelloPh.WcW

/-- info: 'Spike.Lib.A64.HelloPh.WcW.freeLabsH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.freeLabsH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.goodW_of_freeNH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.goodW_of_freeNH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.wcFactsWH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.wcFactsWH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.blkW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.blkW_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.nodeW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.nodeW_wcGH
