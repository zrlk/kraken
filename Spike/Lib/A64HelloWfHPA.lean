/-
**hello.w's heap abort path keeps both abort phases** (`Wf`'s `AbSt`/`AcSt` at hello's threads abort phase
`AcH`, AArch64; the twin of `A64WakeWfAb`'s dispatcher check and of
`A64WakeWfHP`/`A64WakeWfHPA` at `SccCode.helloProg`): `hpathW_phH`, every obligation of `Abort.Disp.HPathW` at
`AbSt μ (WriteAb.Ab lab) ∧ AcSt μ Cl (HelloWf.AcH lab pfxM)`, for an executable with `InstOk`, its program holding
the runtime's abort code (`abortIn`) and passing the path's phase check (`abortPhHeapOk`), its labels hello's code
labels where they resolve (`hlab`), the heap stub's exit call off the take site (`htk`), `ra` not the threads
abort's return address (`hra`).

Only the pcs of the spawn differ from wake's (`.clone13` for `.clone9`, `HelloWf.spPcsH`); wake's `tOk`/`dChk`
read wake's `spPcs`, so the check and `blkW_dispPh` are restated at `spPcsH`/`AcH`. The rest is wake's and
program independent: `blkW_abSt`, `blkW_acStN`, `WakeWf.d0_x30'`, `tj_x30`, `hpcOf`, `si_step`,
`LowerA64.d0_end`, `tj_keep`, `nodeW_ab_exit`, `nodeW_abSt_svc`, `nodeW_acSt_svc`, `StubW.d0_x0`, and hello's
`HelloWf.blkW_phIH`, `nodeW_siIH`, `phOffHC_sound`, `siOffHC_sound`.

- `tOkH`, `dChkH`, `dChkH_congr`, `dChkHC`, `dChkHC_sound`: the dispatcher's check at `AcH`.
- `blkW_dispPhH`, `blkW_dispIH`: a dispatcher block's states in `AbSt ∧ AcSt` (`WakeWf.blkW_dispPh`/`blkW_dispI`
  at `AcH`).
- `nodeW_svcIH`, `nodeW_exitIH`: the stub's `write` and exit call (`WakeWf.nodeW_svcI`/`nodeW_exitI` at `AcH`).
- `chHH_*`: the checks at hello's code labels.
- `hpathW_phH`, `hra_allocH`.
-/
import Spike.Lib.A64HelloAllocPh
import Spike.Lib.A64WakeWfHPA

namespace Spike.Lib.A64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.LowerA64 (blkLabs aiLab aiTgts_congr labC nvPcs arun_succ_eq sp_slot)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.A64.WriteAb (spLoad dispEPcs dispTPcs)
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.StubW (abortPhHeapOk phOne)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.WakeWf (d0_x30' tj_x30 hpcOf si_step)

/-! ## The check -/

/-- **A target of instruction `k` off both phases but by data** (`WakeWf.tOk` at hello's spawn pcs `spPcsH`). -/
def tOkH (lab : Label → Int64) (pfx : String) (E T : List Nat) (k : Nat) (t : Int64) : Bool :=
  !(nvPcs lab).contains t && (E.contains k || !(dispEPcs lab).contains t) &&
    (T.contains k || !(dispTPcs lab).contains t) && !(spPcsH lab pfx).contains t

/-- **A block's targets off both phases but by data** (`tOkH`), the block at `pc`, without a `ret`. -/
def dChkH (lab : Label → Int64) (pfx : String) (pc : Int64) (E T : List Nat) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match Spike.Lib.A64.Flow.classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) 0 a).all (tOkH lab pfx E T k)
      | none => false
    | none => false

section Congr

variable {lab lab' : Label → Int64} {pfx : String}

theorem spPcsH_congr (h : ∀ l ∈ acLabsH pfx, lab l = lab' l) : spPcsH lab pfx = spPcsH lab' pfx := by
  simp only [spPcsH, Hello.ThreadsAb.pcRet, Hello.ThreadsAb.pcSt, Hello.ThreadsAb.tailPcs, ThreadsAb.failPcs]
  rw [h _ (by simp [acLabsH] : pfx ++ ".sp6" ∈ acLabsH pfx),
    h _ (by simp [acLabsH] : pfx ++ ".clone13" ∈ acLabsH pfx),
    h _ (by simp [acLabsH] : pfx ++ ".1_spawnfail5" ∈ acLabsH pfx)]

theorem tOkH_congr {E T : List Nat} (ha : ∀ l ∈ abLabs, lab l = lab' l) (hc : ∀ l ∈ acLabsH pfx, lab l = lab' l) :
    tOkH lab pfx E T = tOkH lab' pfx E T := by
  unfold tOkH
  rw [Spike.Lib.A64.WakeWf.nvPcs_congr' ha, Spike.Lib.A64.WakeWf.dispEPcs_congr ha,
    Spike.Lib.A64.WakeWf.dispTPcs_congr ha, spPcsH_congr hc]

theorem dChkH_congr {pc : Int64} {E T : List Nat} {blk : List Directive} (h : ∀ L ∈ blkLabs blk, lab L = lab' L)
    (ha : ∀ l ∈ abLabs, lab l = lab' l) (hc : ∀ l ∈ acLabsH pfx, lab l = lab' l) :
    dChkH lab pfx pc E T blk = dChkH lab' pfx pc E T blk := by
  unfold dChkH
  rw [tOkH_congr ha hc]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some d =>
    simp only
    cases hc' : Spike.Lib.A64.Flow.classify d with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, by rw [hc']; exact hL⟩

end Congr

/-- The labels `dChkH` reads, the block at `l`. -/
def dLabsH (pfx : String) (l : Label) (blk : List Directive) : List String :=
  l :: blkLabs blk ++ abLabs ++ acLabsH pfx

/-- **`dChkH` at hello's code labels**, every label it reads resolving, the block at `lab l + 4 k`. -/
def dChkHC (pfx : String) (l : Label) (k : Nat) (E T : List Nat) (blk : List Directive) : Bool :=
  (dLabsH pfx l blk).all (fun x => (codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) &&
    dChkH (labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg) pfx
      (labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg l + Int64.ofNat (4 * k)) E T blk

/-- **`dChkHC` at any labels agreeing with the code labels.** -/
theorem dChkHC_sound {lab : Label → Int64}
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → lab l = Int64.ofNat x)
    {pfx : String} {l : Label} {k : Nat} {E T : List Nat} {blk : List Directive}
    (h : dChkHC pfx l k E T blk = true) : dChkH lab pfx (lab l + Int64.ofNat (4 * k)) E T blk = true := by
  simp only [dChkHC, Bool.and_eq_true] at h
  have hl := lab_labCH hlab h.1
  rw [dChkH_congr (fun x hx => hl x (by simp [dLabsH, hx])) (fun x hx => hl x (by simp [dLabsH, hx]))
    (fun x hx => hl x (by simp [dLabsH, hx])), hl l (by simp [dLabsH])]
  exact h.2

/-! ## The phases kept at a dispatcher block -/

section Blk

variable {μ : Marks} {Cl : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {pfx : String}

/-- **A dispatcher block's states keep both phases** (`WakeWf.blkW_dispPh` at `AcH`): a covered block without a
`ret` (`hnr`), its pcs off the marks' sites (`hpc`), its targets off both phases but by data (`h`), the data past
instruction `k` keeping the code off `4` in `x0` for `k ∈ E` (`hE`) and at `[sp]` for `k ∈ T` (`hT`), and `x30`
off `raT` (`hX`). -/
theorem blkW_dispPhH {n : ND} {blk : List Directive} {lo hi : Int} {E T : List Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-32))
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s)
    (hnr : noRetBlk blk = true)
    (h : dChkH (_root_.Executable.labels exe).label pfx n.pc E T blk = true)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.X0
        ≠ 4)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.sp
        = -32 ∧
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot
        (-32) ≠ 4#64)
    (hX : ∀ σ c, n.J σ c → ∀ k, k < blk.length →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
        ⟨n.pc, n.o, σ⟩).σ.regs.X30.toBitVec ≠ ThreadsAb.raT (_root_.Executable.labels exe).label pfx) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  have key : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, Spike.Lib.A64.Flow.classify blk[k] = some a →
      ∀ s' : State, s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.A64.Flow.Abs R
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so s'.st.1
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label s' ∧
        ¬ AcH (_root_.Executable.labels exe).label pfx s' := by
    intro σ c hJ k hk a ha s' hpc' hA'
    have hc := List.all_eq_true.mp h k (List.mem_range.mpr hk)
    simp only [List.getElem?_eq_getElem hk, ha] at hc
    have ht := List.all_eq_true.mp hc _ (aiTgt_mem (lab := (_root_.Executable.labels exe).label)
      (fall := n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) (ra := 0)
      (σ := (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) a
      fun r hr => (noRet_false hnr k hk r (hr ▸ ha)).elim)
    rw [← hpc'] at ht
    simp only [tOkH, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_true_eq, decide_eq_false_iff_not] at ht
    obtain ⟨⟨⟨hnv, hE'⟩, hT'⟩, hsp⟩ := ht
    refine ⟨?_, fun hac => ?_⟩
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | h1 | ⟨h1, h4⟩ | ⟨h1, h4⟩ | h1 | h1)
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
      · rcases hE' with hk' | hk'
        · exact hE σ c hJ k hk hk' (by rw [hA'.regs] at h4; exact h4)
        · exact hk' h1
      · rcases hT' with hk' | hk'
        · obtain ⟨hs, hsl⟩ := hT σ c hJ k hk hk'
          rw [sp_slot hA' hs hoff] at h4
          exact hsl (Option.some.inj h4)
        · exact hk' h1
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
    · have hx := Hello.ThreadsAb.ac_x30 hac (by simpa [spPcsH] using hsp)
      rw [hA'.regs] at hx
      exact hX σ c hJ k hk hx
  refine BlkW.and (blkW_abSt hcode hok hR hal hlo hhi hpc ?_) (blkW_acStN hcode hok hR hal hlo hhi hpc ?_)
  · intro σ c hJ k hk a ha s' _ _ hpc' hA'
    obtain ⟨hso, hst⟩ := arun_succ_eq _ (am := ⟨n.pc, n.o, σ⟩) hok hk ha
    rw [hso, hst] at hA'
    exact (key σ c hJ k hk a ha s' hpc' hA').1
  · intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' hA'
    obtain ⟨hso, hst⟩ := arun_succ_eq _ (am := ⟨n.pc, n.o, σ⟩) hok hk ha
    rw [hso, hst] at hA'
    exact (key σ c hJ k hk a ha s' hpc' hA').2

end Blk

/-! ## At the program's blocks -/

section Prog

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool}
  {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop} {pfx : String}

/-- **`blkW_dispPhH` at a block of the program** (`WakeWf.blkW_dispI` at `AcH`). -/
theorem blkW_dispIH (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat} {E T : List Nat}
    (hb : blockAt prog l k blk = true) (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-32))
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) 0 blk = true)
    (hnr : noRetBlk blk = true)
    (h : dChkH (_root_.Executable.labels exe).label pfx ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k))
      E T blk = true)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.X0
        ≠ 4)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.sp
        = -32 ∧
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot
        (-32) ≠ 4#64)
    (hX : ∀ σ c, n.J σ c → ∀ k, k < blk.length →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
        ⟨n.pc, n.o, σ⟩).σ.regs.X30.toBitVec ≠ ThreadsAb.raT (_root_.Executable.labels exe).label pfx) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph h
  exact blkW_dispPhH (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb he) hok hR hal hlo hhi hoff
    (hpcOf hI hok hph hnr) hnr h hE hT hX

/-- **An `svc` of the program resuming off both phases' pcs** (`h`), its pc off the sites (`hok`)
(`WakeWf.nodeW_svcI` at `AcH`). -/
theorem nodeW_svcIH (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k : Nat} (hb : blockAt prog l k [Spike.Lib.A64.Flow.svcDir] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (h : siOffH (_root_.Executable.labels exe).label pfx l k = true) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  have hc := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb he
  simp only [siOffH, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  have hP := (hI.off s (by unfold pcOf; rw [hpc, ← he]; exact hok)).1
  have htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a :=
    fun a ha heq => hP.noTake a ha (by unfold pcOf; rw [hpc]; exact heq)
  refine NodeW.and (Spike.Lib.A64.WakeWf.nodeW_abSt_svc hc htk fun s' c' hA' r => ?_)
    (Spike.Lib.A64.WakeWf.nodeW_acSt_svc hc htk fun s' c' hA' => .inr fun r => ?_) s c hA
  · obtain ⟨-, -, -, hpc', -⟩ := hA'
    exact Spike.Lib.A64.WriteAb.not_ab_of_pc (by show s'.st.2 + Int64.ofNat 4 ∉ _; rw [hpc']; exact h.1)
  · obtain ⟨-, -, -, hpc', -⟩ := hA'
    exact Hello.ThreadsAb.not_ac_of_pc (by show s'.st.2 + Int64.ofNat 4 ∉ _; rw [hpc']; exact h.2)

/-- **An exit call keeps both phases** (`WakeWf.nodeW_exitI` at `AcH`): at `x8 = 94` (`hx`) the call is
`exit_group`, which resumes in no state; its pc off the take site (`htk`). -/
theorem nodeW_exitIH (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.svcDir] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (htk : ∀ a, μ.site .take = some a → p.toBitVec.toNat ≠ a) (hx : ∀ σ c, n.J σ c → σ.regs.X8 = 94) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  refine NodeW.and (Spike.Lib.LowerA64.nodeW_ab_exit hI hb he hp htk hx) ?_
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hp] at hpc
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨fun _ h => absurd h (by rw [show abi.atSys s = true from atSvc_of_cellAt (imm := 0) hc]; decide),
    fun _ _ _ call hd s' hs' _ => ?_,
    fun _ a ha hpc' => (htk a ha (by rw [← hpc']; unfold pcOf; rw [hpc])).elim⟩, fun _ h => h⟩
  have hd' : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) =
      some (.exitGroup s.st.1.regs.X0.toNat) := by
    rw [← Spike.Lib.A64.Flow.svcCall_exitGroup (r := s.st.1.regs) (by rw [hA.regs, hx σ c hJ]; rfl)]; rfl
  obtain rfl := Option.some.inj (hd'.symm.trans hd)
  rw [Spike.Lib.A64.Flow.certSuccs_exitGroup] at hs'
  cases hs'

end Prog

/-! ## The checks at hello's code labels -/

local macro "d_dec" : tactic => `(tactic| (simp only [dChkHC, labC, ← codeT_eq]; decide +kernel))
local macro "ph_dec" : tactic => `(tactic| (simp only [phOffHC, ← codeT_eq]; decide +kernel))
local macro "si_dec" : tactic => `(tactic| (simp only [siOffHC, ← codeT_eq]; decide +kernel))

theorem chHH_d0 : dChkHC pfxM "scc_rt_abort" 0 [0, 1, 2, 3] [4] Abort.Disp.d0 = true := by d_dec
theorem chHH_t1 : dChkHC pfxM ".L12_scc_rt_abort.0_entry" 0 [] [0, 1, 2, 3] Abort.Disp.t1 = true := by d_dec
theorem chHH_j1 : dChkHC pfxM ".L12_scc_rt_abort.0_entry" 4 [] [0] Abort.Disp.j1 = true := by d_dec
theorem chHH_t2 : dChkHC pfxM ".L12_scc_rt_abort.2_next1" 0 [] [0, 1, 2, 3] Abort.Disp.t2 = true := by d_dec
theorem chHH_g2 :
    phOffHC pfxM ".L12_scc_rt_abort.3_is2" 0 ".L12_scc_rt_abort.3_is2" Abort.Disp.g2 = true := by ph_dec
theorem chHH_b0 : phOffHC pfxM Abort.heap.fn 0 Abort.heap.fn Abort.b0 = true := by ph_dec
theorem chHH_n1 : siOffHC pfxM Abort.heap.entry 0 = true := by si_dec
theorem chHH_n1b : siOffHC pfxM Abort.heap.entry 1 = true := by si_dec
theorem chHH_b1 : phOffHC pfxM Abort.heap.entry 2 Abort.heap.entry Abort.b1Heap = true := by ph_dec
theorem chHH_svc : siOffHC pfxM Abort.heap.entry 7 = true := by si_dec
theorem chHH_b2 : phOffHC pfxM Abort.heap.entry 8 Abort.heap.entry Abort.b2 = true := by ph_dec

/-! ## The path -/

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl} {ra : BitVec 64}

set_option maxHeartbeats 800000 in
/-- **The heap abort path's nodes keep both abort phases** at hello's threads abort phase (`WakeWf.hpathW_ph` at
`AcH`, hello's code labels). -/
theorem hpathW_phH (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhHeapOk okPc ph lab = true)
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → lab l = Int64.ofNat x)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.heap.exit).toBitVec.toNat ≠ a)
    (hra : ra ≠ ThreadsAb.raT lab pfxM) :
    Abort.Disp.HPathW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab lab) s ∧
      AcSt μ Cl (AcH lab pfxM) s) (fun _ _ => False) exe endPc R F c0 ra := by
  have hl := hI.labOk
  subst hl
  have hsd := hab
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  have hst := hsd.1.1.1.1.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, hx, -, -⟩ := hst
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, pb0, o1, -, o1b, -, pb1, o7, -, pb2, -⟩ := hphs
  have hoff : R.Off (-32) := ⟨by decide, by omega, by omega⟩
  -- the tests' data: the code `2` at `[sp]`, `x30 = ra`
  have hTt : ∀ {blk : List Directive}, (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) →
      ∀ (pc : Int64) (σ : Spike.Lib.A64.Flow.AS), (σ.slot (-32)).toNat = 2 → ∀ k, k < blk.length →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).so.sp = -32 ∧
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).σ.slot (-32) ≠ 4#64 := fun hb pc σ h2 k hk => by
    obtain ⟨h1, h3⟩ := Spike.Lib.LowerA64.tj_keep _ hb pc σ (j := k + 1) (by omega)
    refine ⟨h1, fun h => ?_⟩
    rw [h3] at h
    rw [h] at h2
    exact absurd h2 (by decide)
  have hXt : ∀ {blk : List Directive}, (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) →
      ∀ (pc : Int64) (σ : Spike.Lib.A64.Flow.AS), σ.regs.X30.toBitVec = ra → ∀ k, k < blk.length →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
        ⟨pc, Abort.Disp.oD, σ⟩).σ.regs.X30.toBitVec ≠ ThreadsAb.raT (_root_.Executable.labels exe).label pfxM :=
    fun hb pc σ hr k hk => by rw [tj_x30 _ hb pc σ (by omega), hr]; exact hra
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkW_dispIH hI hd0 (add0 _) Abort.Disp.d0_ok hR hal (by omega) (by omega) hoff pd0 (by decide)
      (dChkHC_sound hlab chHH_d0) (fun σ c hJ k hk hkE => ?_) (fun σ c hJ k hk hkT => ?_)
      (fun σ c hJ k hk => ?_)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      have hk4 : k + 1 < Abort.Disp.d0.length := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkE
        have : Abort.Disp.d0.length = 5 := by decide
        omega
      rw [Spike.Lib.A64.StubW.d0_x0 _ σ hk4]
      intro h
      have h2 := hJ.2.1
      rw [h] at h2
      exact absurd h2 (by decide)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      obtain rfl : k = 4 := by simpa using hkT
      obtain ⟨hsp, hsl⟩ := Spike.Lib.LowerA64.d0_end (_root_.Executable.labels exe).label
        ((_root_.Executable.labels exe).label "scc_rt_abort") σ
      refine ⟨hsp, fun h => ?_⟩
      have h' := congrArg BitVec.toNat (hsl.symm.trans h)
      rw [hJ.2.1] at h'
      exact absurd h' (by decide)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      rw [d0_x30' _ _ σ (by omega), hJ.2.2]
      exact hra
  · refine blkW_dispIH hI ht1 (add0 _) Abort.Disp.t1_ok hR hal (by omega) (by omega) hoff pt1 (by decide)
      (dChkHC_sound hlab chHH_t1) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (fun σ c hJ k hk => ?_)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hTt (.inl rfl) _ σ hJ.2.1 k hk
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hXt (.inl rfl) _ σ hJ.2.2.2 k hk
  · refine blkW_dispIH hI hj1 (by simp only [Abort.Disp.DN.nd2R, add4, add0]) Abort.Disp.j1_ok hR hal
      (by omega) (by omega) hoff pj1 (by decide) (dChkHC_sound hlab chHH_j1) (fun _ _ _ _ _ h => by simp at h)
      (fun σ c hJ k hk _ => ?_) (fun σ c hJ k hk => ?_)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hTt (.inr (.inr rfl)) _ σ hJ.2.1 k hk
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hXt (.inr (.inr rfl)) _ σ hJ.2.2.2 k hk
  · refine blkW_dispIH hI ht2 (add0 _) Abort.Disp.t2_ok hR hal (by omega) (by omega) hoff pt2 (by decide)
      (dChkHC_sound hlab chHH_t2) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (fun σ c hJ k hk => ?_)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hTt (.inr (.inl rfl)) _ σ hJ.2.1 k hk
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hXt (.inr (.inl rfl)) _ σ hJ.2.2.2 k hk
  · exact blkW_phIH hI hg2 (add0 _) Abort.Disp.g2_ok hR hal (by omega) (by omega) pg2 (by decide)
      (phOffHC_sound hlab chHH_g2)
  · exact blkW_phIH hI hb0 (add0 _) Abort.b0_ok hR hal (by omega) (by omega) pb0 (by decide)
      (phOffHC_sound hlab chHH_b0)
  · exact nodeW_siIH hI hn1 (add0 _) o1 (siOffHC_sound hlab chHH_n1)
  · exact nodeW_siIH hI hn1b (by simp only [Abort.NT, add4, add0]) o1b (siOffHC_sound hlab chHH_n1b)
  · exact blkW_phIH hI hb1 (by simp only [Abort.NT, add4, add0]) Abort.b1Heap_ok hR hal (by omega) (by omega)
      pb1 (by decide) (phOffHC_sound hlab chHH_b1)
  · exact nodeW_svcIH hI hsvcIn (by simp only [Abort.NT, Abort.pcSvc, add4, add0]) o7
      (siOffHC_sound hlab chHH_svc)
  · exact blkW_phIH hI hb2 (by simp only [Abort.NT, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal (by omega)
      (by omega) pb2 (by decide) (phOffHC_sound hlab chHH_b2)
  · exact nodeW_exitIH hI hx (add0 _) rfl htk fun _ _ h => h.2.1

/-- **`hpathW_phH`'s `hra` at hello's heap abort entry**: the return address past the full branch of
`scc_rt_alloc` is not the threads abort's. -/
theorem hra_allocH
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) :
    (lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec ≠ ThreadsAb.raT lab pfxM := by
  have h1 : lab ".L2_scc_rt_alloc.4_full" = Int64.ofNat 2164516 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have h2 : lab (pfxM ++ ".1_spawnfail5") = Int64.ofNat 2169872 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  simp only [ThreadsAb.raT, h1, h2]
  decide

end Spike.Lib.A64.HelloWf

/-- info: 'Spike.Lib.A64.HelloWf.dChkHC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.dChkHC_sound

/-- info: 'Spike.Lib.A64.HelloWf.blkW_dispPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.blkW_dispPhH

/-- info: 'Spike.Lib.A64.HelloWf.nodeW_svcIH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.nodeW_svcIH

/-- info: 'Spike.Lib.A64.HelloWf.nodeW_exitIH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.nodeW_exitIH

/-- info: 'Spike.Lib.A64.HelloWf.hpathW_phH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.hpathW_phH

/-- info: 'Spike.Lib.A64.HelloWf.hra_allocH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.hra_allocH
