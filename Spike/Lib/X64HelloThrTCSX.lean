/-
**hello.w's thread worker and child stub at depth, landing in `X`, on x86-64** (the twin of
`Spike/Lib/A64HelloThrTCSX.lean`): `scc_rt_thr_worker`'s head, the thread worker and the child stub over
`Spike/Lib/HelloSegTCSX.lean`'s `SegTCSX` with the fragment `SH exe endPc Z` (`Spike/Lib/X64HelloThrTCS.lean`), so
every landing pair of the spawned child's segment chain is in the landing fragment `X`. `X` at the flat pieces'
pairs comes from `Z` (`hZX`); the call of `wc_worker` is `call_ndTSSX`, the worker a `SegTCSX` callee.

- `HThrHead.seg_thrHeadSX`: the `.entry` block at depth `0`, then the call of `wc_worker` (`call_ndTSSX`).
- `Child.seg_thrWorkerSX`: the prologue, the head and the tail (`HThrTail.seg_thrTailNN`) at depth `0`,
  `wc_worker` a `SegTCSX` segment at `[]` (`hwk`, asked only at the return address `.x13`).
- `Child.seg_childStubSX`: the stub's four nodes at depth `0`, then the thread worker a `SegTCSX` segment
  (`hthr`) at the re-based region `thrR R`.

## Differences from the AArch64 version

- The flat pieces are x86-64's: the prologue `thr_prologue_segNN` (`Spike/Lib/X64HelloChildNN.lean`, its
  obligation `XProW`), the tail `HThrTail.seg_thrTailNN` (`Spike/Lib/X64HelloThrNN.lean`, its thread pointer
  read through `%fs`: `hT`, `hown`, and its nodes at their executing offsets `HThrTail.NA`), the stub's nodes
  by `seg_ndNNA`, `Wake.Child.test_ndNNA`, `Wake.Child.flag_ndNNA` as in `X64WakeChildNNA.seg_childNNA`.
  No region is asked to be 16-byte aligned (no `hal`).
- `wc_worker` is entered at `-80` (the frame of 64, the saved `%rbp`, the pushed return address) with the callee
  region `[-176, 8)` from its entry: `wc_worker`'s own frame reaches `-96` (`Body.wCall`, `HelloTail`) and its
  call of `scc_rt_print` asks `R'.lo ≤ -96 - 8 + -72` (`PrintF.printF_callTCSX`), the return address at `0`.
  So the head and the thread worker ask `R.lo ≤ -256`, `8 ≤ R.hi`; A64 asks `-272` and `0` (callee
  `[-192, 0)`).
- The thread worker's stack limit is a `LimOk` at the TCB's limit word `tp + 8` (as `X64WakeWorkerLabelsNNA`),
  not A64's premise quantified over the register file; its entry `%rsp` is the region's base (`R.addr 0`,
  where `HThrTail.Code` is stated), a premise-free case split. `wc_worker`'s exits are `HelloTail.E`'s (A64:
  `Wake.WkTailW.E`), its entry `wcJE` with `%rsp = sp0 - 80`.
- The stub ends at `scc_rt_thr_worker`'s entry at offset `-8` (`Child.cE`: its `call` pushes the return
  address), so `hthr` is at `X64WakeChildPre.thrR R` from `sp0 - 8` (`At.toThr`), as wake's
  `seg_childStubNNA`; the stub asks `R.lo ≤ -128`, `0 ≤ R.hi` only.
-/
import Spike.Lib.X64HelloThrTCS
import Spike.Lib.X64HelloChildNN
import Spike.Lib.X64HelloWkTail
import Spike.Lib.X64HelloCallTSSX
import Spike.Lib.X64HelloSegTCSXC
import Spike.Lib.X64WakeChildNN

namespace Spike.Lib.X64.Flow.Worker.Hello

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk LimOk)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64HelloSegTCSX
open Spike.Lib.X64.Flow.Worker.Wake.Child (thrR thrR_ok FStable.thrR At.toThr test_ndNNA flag_ndNNA)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)

set_option linter.unusedSimpArgs false

namespace HThrHead

section ProofSX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {ms : List TermRun.Frame → MemSide isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {Z X : FragS isa}

/-- **`scc_rt_thr_worker`'s head landing in `X`**: the `.entry` block at depth `0` (`seg_ndNNA`, `X` from `Z` by
`hZX`), the call `call_ndTSSX` to a `SegTCSX` callee at `[]`, its region `[-176, 8)` from the call's `%rsp`. -/
theorem seg_thrHeadSX {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -256) (hhi : 8 ≤ R.hi) {J : AS → Ctl → Prop}
    {L : Ctl → Ctl → Prop} (hL : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ L c c')
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry") thE)
    (hZX : ∀ s c fs, Z s c fs → X s c fs)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -176 → 8 ≤ R'.hi →
      FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegTCSX (SH exe endPc Z) X p lbl ms ((At exe endPc R' F' (Ne g)).at [])
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c) []))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN (_root_.Executable.labels exe).label J L .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-80) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN (_root_.Executable.labels exe).label J L .call).J σC c →
      (Ne g).J (enter (-80) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-80) (-176) 8).Off (k - (-80)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-80 + (Ex g x).o.sp, []⟩, σR⟩ c')
    (hZE : NodeZA (fun s c => Z s c []) exe endPc R F (tN (_root_.Executable.labels exe).label J L .e) thE) :
    SegTCSX (SH exe endPc Z) X p lbl ms
      ((At exe endPc R F (tN (_root_.Executable.labels exe).label J L .e)).at [])
      ((Next exe endPc R F N E).at []) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegTCSX.ofTC_seq (Q₀ := At exe endPc R F (tN lab J L .call))
    ((seg_ndNNA (ms := ms []) (N := fun _ : Unit => tN lab J L .call) (E := (nofun : Empty → ND)) (blk := thE)
      (by simp [thE]) thE_ok (by decide) hF hR (Int.le_trans hlo (by decide)) hhi hcodeE (fun σ c hJ => ?_)
      hZE).mono_post ?_)
    (fun _ _ h => nnzS h) (fun _ _ h => hZX _ _ _ h.2) ?_
  · obtain ⟨c', hr, hl⟩ := hL σ c hJ
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, σ, c, hJ, hl, rfl⟩⟩
    · simp only [tN]; rw [thE_run]
    · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndTSSX (e0 := 0) (lo' := -176) (hi' := 8) hR hF (by show R.lo ≤ -80 - 0 + -176; omega)
      (by decide) (by show (-80 : Int) - 0 < R.hi; omega) (by show (-80 : Int) - 0 + 8 ≤ R.hi; omega)
      (by show ((-80 : Int) - 0) % 8 = 0; decide) (by decide) (by decide) hwk hNe hent hret

end ProofSX

end HThrHead

namespace Child

section SegSX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z X : FragS isa}

/-- **The thread worker landing in `X`**: `wc_worker` a `SegTCSX` segment at `[]` (`hwk`, asked only at the
return address `.x13`), the prologue, head and tail at depth `0` (`X` from `Z` by `hZX`). -/
theorem seg_thrWorkerSX {Q : FragS isa} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp)
    {c0 c1 c3 : Ctl} {w : Words} {tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -256) (hhi : 8 ≤ R.hi)
    (hlim : LimOk (ms []) F (tp + (8 : Int64).toBitVec) (sp0 - 8#64 - (64 : Int64).toBitVec))
    (hsplit : LocalRun p c0 c1)
    (hZX : ∀ s c fs, Z s c fs → X s c fs)
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -176 → 8 ≤ R'.hi →
      FStable R' F' → (∀ m, F' m → F m) → ∀ rbp ra : BitVec 64,
        Int64.ofBitVec ra = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13" →
        SegTCSX (SH exe endPc Z) X p lbl ms
          ((At exe endPc R' F' ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
            fun σ c => wcJE c1 w rbp ra tp σ c ∧ σ.regs.rsp.toBitVec = sp0 - 80#64⟩).at [])
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (HelloTail.E c3 rbp ra tp x) s c) []))
    (hK : (ms []).K = some Scc.Sem.X64.abi) {ar : CoreTerm.At} (hret3 : c3.term = .ret ar)
    (hT : LdOk (ms []) F tp)
    (hown : OwnAt (ms []) exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13") tp tp)
    (hSx : StOk (ms []) F (tp + 24#64) 1#64)
    (hz : XProW (fun s c => Z s c []) (fun _ _ => False) exe endPc R F (ms [])
      ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 64 8 ".Lscc_rt_thr_worker.stk" 5 9 3 2 4 thrPs
      (thrJE c0 w tp sp0))
    (hZE : NodeZA (fun s c => Z s c []) exe endPc R F
      (HThrHead.tN (_root_.Executable.labels exe).label (thrJ c0 w tp sp0) (fun _ c => c = c1) .e) HThrHead.thE)
    (hZT : ∀ i, NodeZA (fun s c => Z s c []) exe endPc R F
      (HThrTail.NA (_root_.Executable.labels exe).label c3 tp sp0 i) (HThrTail.blkN i)) :
    SegTCSX (SH exe endPc Z) X p lbl ms
      ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE c0 w tp sp0⟩).at []) Q := by
  by_cases hsp : sp0 = R.addr 0
  case neg =>
    refine SegTCSX.empty fun s c fs ⟨h, _⟩ => ?_
    obtain ⟨-, -, -, -, σ, -, -, hJ, hr⟩ := Wake.Labels.At.rspAt h
    exact hsp (hJ.2.2.2.2.2.2.2.2.symm.trans hr)
  subst hsp
  let lab := (_root_.Executable.labels exe).label
  refine SegTCSX.ofTC_seq (thr_prologue_segNN (ms := ms []) (Z := fun s c => Z s c []) hp hend hF hR
    (Int.le_trans hlo (by decide)) (by omega)
    (nb := HThrHead.tN lab (thrJ c0 w tp (R.addr 0)) (fun _ c => c = c1) .e)
    rfl (by show SO.le HThrHead.oI (oF 64) = true; decide) (fun σ c hJ => ?_) hz) (fun _ _ h => nnzS h)
    (fun _ _ h => hZX _ _ _ h.2) ?_
  · obtain ⟨rfl, hdi, hsi, hdx, hcx, h8, h9, htp, hsp⟩ := hJ
    rw [htp]
    refine ⟨hlim.rt, hlim.mp, hlim.unmapped, fun v hv => ⟨by rw [hsp]; exact hlim.room v hv, fun σ' hr hs => ?_⟩⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdi]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hsi]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdx]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hcx]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, h8]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, h9]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
      bv_omega
  refine SegTCSX.seq (HThrHead.seg_thrHeadSX (N := fun _ : Unit => HThrTail.N lab c3 tp (R.addr 0) .x13)
    (E := (nofun : Empty → ND)) hF hR hlo hhi (fun σ c hJ => ⟨c1, by rw [hJ.1]; exact hsplit, rfl⟩)
    (thECode hp hend) hZX
    (Ne := fun g : {g : BitVec 64 × BitVec 64 // Int64.ofBitVec g.2 = lab ".Lscc_rt_thr_worker.x13"} =>
      ⟨lab "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c1 w g.1.1 g.1.2 tp σ c ∧ σ.regs.rsp.toBitVec = R.addr 0 - 80#64⟩)
    (Ex := fun g y => HelloTail.E c3 g.1.1 g.1.2 tp y)
    (fun R' F' hR' hlo' hhi' hF' hFF g => hwk R' F' hR' hlo' hhi' hF' hFF g.1.1 g.1.2 g.2)
    (fun _ => rfl) ?_ ?_ hZE) ?_
  · rintro σC c ⟨σ0, c0', ⟨-, h16, h24, h32, h40, h48, h56, htp, -, hsp⟩, hc, rfl⟩
    refine ⟨⟨(_, _), ?_⟩, rfl, ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩, ?_⟩
    · show Int64.ofBitVec ((enter (-80) (arun lab HThrHead.thE
        ⟨lab ".Lscc_rt_thr_worker.entry", HThrHead.oI, σ0⟩).σ).slot 0) = lab ".Lscc_rt_thr_worker.x13"
      rw [show lab ".Lscc_rt_thr_worker.x13" = lab ".Lscc_rt_thr_worker.entry" + 29 from hx13 hp]
      simp only [enter, HThrHead.thE_run, upd_apply]
      rfl
    all_goals simp [enter, HThrHead.thE_run, Reg64s.set64, Reg64s.get64, h16, h24, h32, h40, h48, h56, htp, hsp]
    all_goals bv_omega
  · rintro ⟨⟨rbp1, ra1⟩, hpin⟩ ⟨⟩ σC c σx c' σR ⟨σ0, c0', ⟨-, -, -, -, -, -, -, -, hbp, -⟩, -, rfl⟩
      ⟨⟨-, -, -, -, -, -, -, hrb, -, -⟩, -⟩ ⟨hc', hrb', htp'⟩ hreg - - -
    refine .inl ⟨(), hpin.symm, by show SO.le HThrTail.oP ⟨-80 + 8, []⟩ = true; decide, hc', ?_, ?_⟩
    · show σR.regs.fsBase.toBitVec = tp
      rw [hreg]; exact htp'
    · show σR.regs.rbp.toBitVec = _
      have h1 : σx.regs.get64 .rbp = rbp1 := hrb'
      have h2 : (enter (-80) (arun lab HThrHead.thE
          ⟨lab ".Lscc_rt_thr_worker.entry", HThrHead.oI, σ0⟩).σ).regs.rbp.toBitVec = rbp1 := hrb
      rw [hreg]; simp only [Reg64s.get64] at h1; rw [h1, ← h2]
      simp [enter, HThrHead.thE_run, Reg64s.set64, hbp]
  · refine ((SegTCSX.ofTC (HThrTail.seg_thrTailNN (Q := fun _ _ => False) hF hR (Int.le_trans hlo (by decide))
      hhi hK hT hown hSx hret3 (thrCode hp hend) hZT) (fun _ _ h => nnzS h) (fun _ _ h => hZX _ _ _ h.2)
      ?_).mono_pre ?_).mono_post ?_
    · rintro s c ⟨⟩
    · rintro s c fs ⟨h, rfl⟩
      exact ⟨h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim, rfl⟩
    · rintro s c fs ⟨⟨⟩, -⟩

/-- **The child stub landing in `X`**: the stub's four nodes at depth `0` (`X` from `Z` by `hZX`), then the
thread worker a `SegTCSX` segment (`hthr`) at the re-based region `thrR R` from `sp0 - 8`. -/
theorem seg_childStubSX {Q : FragS isa} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp)
    {cW : Ctl} {w : Words} {tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hZX : ∀ s c fs, Z s c fs → X s c fs)
    (hthr : SegTCSX (SH exe endPc Z) X p lbl ms
      ((At exe endPc (thrR R) F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE cW w tp (sp0 - 8#64)⟩).at []) Q)
    (hZc : ∀ i, NodeZA (fun s c => Z s c []) exe endPc R F
      (cN (_root_.Executable.labels exe).label cW w tp sp0 i) (cBlk i)) :
    SegTCSX (SH exe endPc Z) X p lbl ms
      ((At exe endPc R F (childN (_root_.Executable.labels exe).label cW w tp sp0)).at []) Q := by
  have hin := hello_childIn
  simp only [childIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨bts, bje⟩, bxb⟩, bch⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt SccCode.helloCells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  refine SegTCSX.ofTC_seq (Q₀ := At exe endPc R F (cE lab cW w tp sp0))
    ((fn_segTS (S := NNZ exe endPc fun s c => Z s c []) (ms := ms []) (N := cN lab cW w tp sp0)
      (E := fun _ : Unit => cE lab cW w tp sp0) (fun i => ?_) CN.ts).mono_post fun _ _ ⟨_, h⟩ => h)
    (fun _ _ h => nnzS h) (fun _ _ h => hZX _ _ _ h.2)
    (hthr.mono_pre fun s c fs ⟨h, e⟩ => ⟨At.toThr h fun σ c hJ => ?_, e⟩)
  case refine_2 =>
    obtain ⟨h0, hdi, hsi, hdx, hcx, h8, h9, -, htp, hsp, -⟩ := hJ
    simp only [Reg64s.get64] at hdi hsi hdx hcx h8 h9 hsp
    exact ⟨h0, hdi, hsi, hdx, hcx, h8, h9, htp, hsp⟩
  cases i
  case ts =>
    refine test_ndNNA hF (fun s he hn => code bts s he hn) (fun σ c hJ af => ⟨c, .refl c, .inl ⟨CN.je, ?_, rfl, ?_⟩⟩)
      (NodeZA.toW (hZc .ts))
    · show lab x25L + 99 = lab x25L + Int64.ofNat 96 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    · obtain ⟨hS, h0⟩ := hJ
      exact ⟨hS, by rw [testStep_zf, h0]; rfl⟩
  case je =>
    refine seg_ndNNA (blk := jeB) (by simp [jeB]) jeB_ok (by decide) hF hR hlo hhi (fun s he hn => code bje s he hn)
      (fun σ c hJ => ⟨c, .refl c, .inl ⟨CN.xb, ?_, rfl, hJ.1⟩⟩) (hZc .je)
    show lab chL = (arun lab jeB ⟨lab x25L + 99, oC, σ⟩).pc
    rw [jeB_run]; simp only [hJ.2, ite_true]
  case xb =>
    refine flag_ndNNA (fi := .xor_rr32_self .rbp) rfl (by decide) hF
      (fun s he hn => (by simpa using code bxb s he hn : CodeAt s (lab chL) xbp)) (fun σ c hJ fl =>
        ⟨c, .refl c, .inl ⟨CN.ch, ?_, rfl, ?_, ?_⟩⟩) (NodeZA.toW (hZc .xb))
    · rfl
    · obtain ⟨h0, h12, hbx, h13, h14, h15, h9, htp, hsp⟩ := hJ
      refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, h13, h14, h15, h9, hsp]
      simpa [FI.step, FI.regs, Reg64s.set64] using htp
    · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
  case ch =>
    refine seg_ndNNA (blk := chB) (by simp [chB]) chB_ok (by decide) hF hR hlo hhi (fun s he hn => code bch s he hn)
      (fun σ c hJ => ⟨c, .refl c, .inr ⟨(), ?_, rfl, ?_⟩⟩) (hZc .ch)
    · show lab "scc_rt_thr_worker" = (arun lab chB ⟨lab chL + 2, oC, σ⟩).pc
      rw [chB_run]
    · obtain ⟨⟨h0, h12, hbx, h13, h14, h15, h9, htp, hsp⟩, hbp⟩ := hJ
      show cE lab cW w tp sp0 |>.J (arun lab chB ⟨lab chL + 2, oC, σ⟩).σ c
      rw [chB_run]
      simp only [Reg64s.get64] at h12 hbx h13 h14 h15 h9 hbp hsp
      refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Reg64s.get64, Reg64s.set64, h12]
      · simp [Reg64s.get64, Reg64s.set64, hbx]
      · simp [Reg64s.get64, Reg64s.set64, h13]
      · simp [Reg64s.get64, Reg64s.set64, h14]
      · simp [Reg64s.get64, Reg64s.set64, h15]
      · simp [Reg64s.get64, Reg64s.set64, h9]
      · simp [Reg64s.get64, Reg64s.set64, hbp]
      · simpa [Reg64s.set64] using htp
      · simp [Reg64s.get64, Reg64s.set64, hsp]
      · simp only [upd_apply, ite_true]
        rw [Int64.toBitVec_add, BitVec.add_assoc]; rfl

end SegSX

end Child

end Spike.Lib.X64.Flow.Worker.Hello

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.HThrHead.seg_thrHeadSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.HThrHead.seg_thrHeadSX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Child.seg_thrWorkerSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Child.seg_thrWorkerSX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Child.seg_childStubSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Child.seg_childStubSX
