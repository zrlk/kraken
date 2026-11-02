/-
**hello.w's heap abort path keeps both abort phases** (`Wf`'s `AbSt`/`AcSt` at hello's threads abort phase
`Hello.ThreadsAb.AcH`, x86-64; the twin of `Spike/Lib/A64HelloWfHPA.lean`, and of `Spike/Lib/X64WakeWfAb.lean`'s
dispatcher check and `Spike/Lib/X64WakeWfHPA.lean` at hello.w's cells): `hpathW_phH`, every obligation of
`Abort.Disp.HPathW` at `AbSt μ (WriteAb.Ab lab) ∧ AcSt μ Cl (Hello.ThreadsAb.AcH lab ".Lwc_main")`, for an
executable with `InstOk`, its cells holding the runtime's abort code (`abortIn`) and passing the path's phase check
(`abortPhHeapOk`), its labels hello's code labels where they resolve (`hlab`), the heap stub's exit call off the
take site (`htk`), `ra` not the threads abort's return address (`hra`).

Only the spawn's pcs differ from wake's (the clone at `.x25 + 94`, the store at `.x26`, `spPcsH`); wake's
`tOk`/`dChk` read wake's `spPcs`, so the check and `blkW_dispPh` are restated at `spPcsH`/`AcH`, and the checks
are decided at hello's code labels (`labC lo helloCells`). The rest is wake's and program independent:
`blkW_abSt`, `blkW_acStN`, `WakeWf.hX_of`, `d0_ra`, `d0_sp1`, `d0_bp`, `tj_ra`, `hpcOf`, `LowerX64.d0_end`,
`tj_keep`, `nodeW_ab_exit`, `StubW.d0_rdi`, and hello's `blkW_phIH`, `nodeW_siIH`, `phOffW_sound`, `siOffW_sound`,
`fullChkH_sound`.

- `tOkH`, `dChkH`, `tOkH_congr`, `dChkH_congr`, `dLabsH`, `dChkHC`, `dChkHC_sound`: the dispatcher's check at
  `AcH`.
- `rChkHC`, `rChkHC_sound`: where each dispatcher target reads the pushed word (`WakeWf.rChk`), at hello's code
  labels.
- `blkW_dispPhH`, `blkW_dispIH`: a dispatcher block's states in `AbSt ∧ AcSt` (`WakeWf.blkW_dispPh`/`blkW_dispI`
  at `AcH`).
- `nodeW_sysIH`, `nodeW_exitIH`: the stub's `write` and exit call (`WakeWf.nodeW_sysI`/`nodeW_exitI` at `AcH`).
- `chHH_*`, `rHH_*`: the checks at hello's code labels.
- `hpathW_phH`, `hra_allocH`.

Unlike AArch64 (forced by the x86-64 shape, as in `X64WakeWfHPA`):
- offsets are bytes (`j1` at `.entry + 16`; the stub's `leaq` at `entry + 0`, its block at `+ 7`, the `syscall`
  at `+ 34`, the last block at `+ 36`); the labels are `helloCells`' (`codeLabel`, no numbering) and the spawn's
  prefix is `.Lwc_main` (A64's `pfxM`);
- the stub's `leaq` is one instruction (A64's `adrp`/`add`, `chHH_n1b`), and the `write` call is a `syscall`
  (`chHH_sys`, `nodeW_sysIH`; A64's `svc`, `nodeW_svcIH`), the exit call at `%rax = 231` (A64's `x8 = 94`);
- the return address is the pushed word, so `hX` of each dispatcher block comes from `rChk` (`rHH_*`, no A64
  counterpart) and the run's offsets, with `slot 8` kept (`d0_ra`, `tj_ra`; A64's `x30`, `d0_x30'`/`tj_x30`);
  the spawn's own pcs include the `je` after the `testq` (`pcJe`);
- the code `4` is at `-8(%rbp)` (`R.Off (-8)`; A64's `[sp]`, `R.Off (-32)`), the region is `[-24, 16)` (A64's
  `[-48, 0)`), no alignment premise;
- `hra_allocH`'s return address is past `scc_rt_alloc`'s `call scc_rt_abort` at `.Lscc_rt_alloc.full + 12`
  (A64's `bl` at `+ 8`), read off `fullChkH_sound`.
-/
import Spike.Lib.X64HelloAllocPh
import Spike.Lib.X64WakeWfHPA

namespace Spike.Lib.X64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At CodeAt cellOff arun classify)
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAtB)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.LowerX64 (blkLabs aiTgts_congr labC nvPcs arun_succ_eq bp_slot)
open Spike.Lib.X64.AllocG (abLabs)
open Spike.Lib.X64.WriteAb (dispEPcs)
open Spike.Lib.X64.StubW (abortPhHeapOk phOne)
open Spike.Lib.X64.WakeWf (rChk rLabs rChk_congr hX_of hpcOf d0_ra d0_sp1 d0_bp tj_ra)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Kraken.Promising.Lower.X64 (op64)

/-! ## The check -/

/-- **A target of instruction `k` off both phases but by data** (`WakeWf.tOk` at hello's spawn pcs `spPcsH`).
Unlike AArch64, the spawn's pcs include the `je` after the `testq`. -/
def tOkH (lab : Label → Int64) (pfx : String) (E T : List Nat) (k : Nat) (t : Int64) : Bool :=
  !(nvPcs lab).contains t && (E.contains k || !(dispEPcs lab).contains t) &&
    (T.contains k || !(WriteAb.dispTPcs lab).contains t) && !(spPcsH lab pfx).contains t

/-- **A block's targets off both phases but by data** (`tOkH`), the block at `pc`, without a `ret`. Unlike
AArch64, instruction `k` is at `pc + cellOff blk k` (bytes). -/
def dChkH (lab : Label → Int64) (pfx : String) (pc : Int64) (E T : List Nat) (blk : List (Directive × Nat)) :
    Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some dz => match classify dz.1 with
      | some a => (aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) 0 a).all (tOkH lab pfx E T k)
      | none => false
    | none => false

section Congr

variable {lab lab' : Label → Int64} {pfx : String}

theorem tOkH_congr {E T : List Nat} (ha : ∀ l ∈ abLabs, lab l = lab' l) (hc : ∀ l ∈ acLabs pfx, lab l = lab' l) :
    tOkH lab pfx E T = tOkH lab' pfx E T := by
  unfold tOkH
  rw [Spike.Lib.X64.WakeWf.nvPcs_congr' ha, Spike.Lib.X64.WakeWf.dispEPcs_congr ha,
    Spike.Lib.X64.WakeWf.dispTPcs_congr ha, spPcsH_congr hc]

theorem dChkH_congr {pc : Int64} {E T : List Nat} {blk : List (Directive × Nat)}
    (h : ∀ L ∈ blkLabs blk, lab L = lab' L)
    (ha : ∀ l ∈ abLabs, lab l = lab' l) (hc : ∀ l ∈ acLabs pfx, lab l = lab' l) :
    dChkH lab pfx pc E T blk = dChkH lab' pfx pc E T blk := by
  unfold dChkH
  rw [tOkH_congr ha hc]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some dz =>
    simp only
    cases hc' : classify dz.1 with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨dz, List.mem_of_getElem? hk, by rw [hc']; exact hL⟩

end Congr

/-- The labels `dChkH` reads, the block at `l`. -/
def dLabsH (pfx : String) (l : Label) (blk : List (Directive × Nat)) : List String :=
  l :: blkLabs blk ++ abLabs ++ acLabs pfx

/-- **`dChkH` at hello's code labels**, every label it reads resolving, the block at `lab l + k`. Unlike
AArch64, `k` is in bytes. -/
def dChkHC (pfx : String) (l : Label) (k : Nat) (E T : List Nat) (blk : List (Directive × Nat)) : Bool :=
  (dLabsH pfx l blk).all (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) &&
    dChkH (labC Spike.Lib.X64.HelloPh.lo helloCells) pfx
      (labC Spike.Lib.X64.HelloPh.lo helloCells l + Int64.ofNat k) E T blk

/-- **`dChkHC` at any labels agreeing with the code labels.** -/
theorem dChkHC_sound {lab : Label → Int64}
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some a → lab l = Int64.ofNat a)
    {pfx : String} {l : Label} {k : Nat} {E T : List Nat} {blk : List (Directive × Nat)}
    (h : dChkHC pfx l k E T blk = true) : dChkH lab pfx (lab l + Int64.ofNat k) E T blk = true := by
  simp only [dChkHC, Bool.and_eq_true] at h
  have hl := lab_labC hlab h.1
  rw [dChkH_congr (fun x hx => hl x (by simp [dLabsH, hx])) (fun x hx => hl x (by simp [dLabsH, hx]))
    (fun x hx => hl x (by simp [dLabsH, hx])), hl l (by simp [dLabsH])]
  exact h.2

/-- **`WakeWf.rChk` at hello's code labels**, every label it reads resolving, the block at `lab l + k` (bytes).
Unlike AArch64 (where the return address is `x30`), the threads abort reads the pushed word. -/
def rChkHC (l : Label) (k : Nat) (S P B : List Nat) (blk : List (Directive × Nat)) : Bool :=
  (rLabs l blk).all (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) &&
    rChk (labC Spike.Lib.X64.HelloPh.lo helloCells) (labC Spike.Lib.X64.HelloPh.lo helloCells l + Int64.ofNat k)
      S P B blk

/-- **`rChkHC` at any labels agreeing with the code labels.** -/
theorem rChkHC_sound {lab : Label → Int64}
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some a → lab l = Int64.ofNat a)
    {l : Label} {k : Nat} {S P B : List Nat} {blk : List (Directive × Nat)}
    (h : rChkHC l k S P B blk = true) : rChk lab (lab l + Int64.ofNat k) S P B blk = true := by
  simp only [rChkHC, Bool.and_eq_true] at h
  have hl := lab_labC hlab h.1
  rw [rChk_congr (fun x hx => hl x (by simp [rLabs, hx])) (fun x hx => hl x (by simp [rLabs, hx])),
    hl l (by simp [rLabs])]
  exact h.2

/-! ## The phases kept at a dispatcher block -/

section Blk

variable {μ : Marks} {Cl : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {pfx : String}

/-- **A dispatcher block's states keep both phases** (`WakeWf.blkW_dispPh` at `AcH`): a covered block without a
`ret` (`hnr`), its pcs off the marks' sites (`hpc`), its targets off both phases but by data (`h`), the data past
instruction `k` keeping the code off `4` in `%rdi` for `k ∈ E` (`hE`) and at `-8(%rbp)` for `k ∈ T` (`hT`), and
the pushed return address off `raT` at every target (`hX`). Unlike AArch64, `hX` is stated at the target state
(the pushed word, not `x30`), and there is no alignment premise. -/
theorem blkW_dispPhH {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {E T : List Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : Spike.Lib.X64.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-8))
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk j) → PcOff μ s)
    (hnr : noRetBlk blk = true)
    (h : dChkH (_root_.Executable.labels exe).label pfx n.pc E T blk = true)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.get .rbp = some 0 ∧
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot (-8) ≠ 4#64)
    (hX : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a → ∀ s' : State,
      s'.st.2 ∈ aiTgts (_root_.Executable.labels exe).label
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) 0 a →
      Spike.Lib.X64.Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so
        s'.st.1 (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ ThreadsAb.RaW (_root_.Executable.labels exe).label s'
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx)) :
    BlkW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  have key : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      ∀ s' : State, s'.st.2 = a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.X64.Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so
        s'.st.1 (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ WriteAb.Ab (_root_.Executable.labels exe).label s' ∧
        ¬ Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label pfx s' := by
    intro σ c hJ k hk a ha s' hpc' hA'
    have hc := List.all_eq_true.mp h k (List.mem_range.mpr hk)
    simp only [List.getElem?_eq_getElem hk, ha] at hc
    have hmem := aiTgt_mem (lab := (_root_.Executable.labels exe).label)
      (o := (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so)
      (fall := n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) (ra := 0)
      (σ := (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) a
      fun r => (noRet_false hnr k hk (r ▸ ha)).elim
    rw [← hpc'] at hmem
    have ht := List.all_eq_true.mp hc _ hmem
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
          rw [bp_slot hA' hs hoff] at h4
          exact hsl (Option.some.inj h4)
        · exact hk' h1
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
    · exact hX σ c hJ k hk a ha s' hmem hA' (Hello.ThreadsAb.ac_x30 hac (by simpa [spPcsH] using hsp))
  refine BlkW.and (blkW_abSt hcode hok hR hlo hhi hpc ?_) (blkW_acStN hcode hok hR hlo hhi hpc ?_)
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

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop}
  {pfx : String}

/-- **`blkW_dispPhH` at a block of the program** (`WakeWf.blkW_dispI` at `AcH`). Unlike AArch64, the block is
at `blockAtB` and `lab l + k` (bytes). -/
theorem blkW_dispIH (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {l : Label} {k : Nat} {E T : List Nat}
    (hb : blockAtB cells l k blk = true) (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : Spike.Lib.X64.okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hoff : R.Off (-8))
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat k) 0 blk = true)
    (hnr : noRetBlk blk = true)
    (h : dChkH (_root_.Executable.labels exe).label pfx ((_root_.Executable.labels exe).label l + Int64.ofNat k)
      E T blk = true)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.get .rbp = some 0 ∧
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot (-8) ≠ 4#64)
    (hX : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a → ∀ s' : State,
      s'.st.2 ∈ aiTgts (_root_.Executable.labels exe).label
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) 0 a →
      Spike.Lib.X64.Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so
        s'.st.1 (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ ThreadsAb.RaW (_root_.Executable.labels exe).label s'
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx)) :
    BlkW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph h
  exact blkW_dispPhH (fun s hs hn => he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn) hok hR hlo hhi hoff
    (hpcOf hI hok hph hnr) hnr h hE hT hX

/-- **A `syscall` of the program resuming off both phases' pcs** (`h`, its next pc two bytes on), its pc off the
sites (`hok`) (`WakeWf.nodeW_sysI` at `AcH`). Unlike AArch64 (`svc`), the call is a two-byte `syscall`, also
resuming at an `arch_prctl`. -/
theorem nodeW_sysIH (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k : Nat} (hb : blockAtB cells l k [(op64 .syscall, 2)] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat k).toBitVec.toNat = true)
    (h : siOff (_root_.Executable.labels exe).label pfx l k 2 = true) :
    NodeW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  simp only [siOff, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  rintro s c ⟨hs, hn, -, hpc, -⟩
  have hP := (hI.off s (by unfold pcOf; rw [hpc, ← he]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have hnx : ∀ call s', s' ∈ Kernel.certSuccs abi s call → s'.st.2 = n.pc + Int64.ofNat 2 := by
    intro call s' hs'
    by_cases ha : ∃ a, call = .archSetFs a
    · obtain ⟨a, rfl⟩ := ha
      rw [certSuccs_archSetFs hc a] at hs'
      cases hs' with
      | tail _ h => cases h
      | head => show s.st.2 + Int64.ofNat 2 = _; rw [hpc]
    · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hc fun a he => ha ⟨a, he⟩).1 hs'
      show s.st.2 + Int64.ofNat 2 = _
      rw [hpc]
  have hsys : abi.atSys s = true := atSyscall_of_cellAt hc
  refine ⟨⟨⟨fun _ h => absurd h (by rw [hsys]; decide),
      fun _ _ call _ s' hs' hab' => (WriteAb.not_ab_of_pc (hnx call s' hs' ▸ h.1) hab').elim,
      fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩,
    ⟨fun _ h => absurd h (by rw [hsys]; decide),
      fun _ _ _ call _ s' hs' hac => Hello.ThreadsAb.not_ac_of_pc (hnx call s' hs' ▸ h.2) hac,
      fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩⟩, fun _ h => h⟩

/-- **An exit call keeps both phases** (`WakeWf.nodeW_exitI` at `AcH`): at `%rax = 231` (`hx`) the call is
`exit_group`, which resumes in no state; its pc off the take site (`htk`). Unlike AArch64 (`x8 = 94`, `svc`), the
call is a `syscall` at `%rax = 231`. -/
theorem nodeW_exitIH (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k : Nat} {p : Int64} (hb : blockAtB cells l k [(op64 .syscall, 2)] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = p) (hp : n.pc = p)
    (htk : ∀ a, μ.site .take = some a → p.toBitVec.toNat ≠ a) (hx : ∀ σ c, n.J σ c → σ.regs.get64 .rax = 231#64) :
    NodeW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  refine NodeW.and (Spike.Lib.LowerX64.nodeW_ab_exit hI hb he hp htk hx) ?_
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hp] at hpc
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨fun _ h => absurd h (by rw [show abi.atSys s = true from atSyscall_of_cellAt hc]; decide),
    fun _ _ _ call hd s' hs' _ => ?_,
    fun _ a ha hpc' => (htk a ha (by rw [← hpc']; unfold pcOf; rw [hpc])).elim⟩, fun _ h => h⟩
  have hr : s.st.1.regs.rax.toNat = 231 := by
    have h231 := hx σ c hJ
    rw [← hA.regs] at h231
    simp only [Reg64s.get64] at h231
    rw [← UInt64.toNat_toBitVec, h231]; rfl
  have hd' : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup s.st.1.regs.rdi.toNat) := by
    rw [← Spike.Lib.X64.syscallCall_exitGroup hr]; rfl
  obtain rfl := Option.some.inj (hd'.symm.trans hd)
  rw [Spike.Lib.X64.certSuccs_exitGroup] at hs'
  cases hs'

end Prog

/-! ## The checks at hello's code labels -/

local macro "d_dec" : tactic => `(tactic| (unfold dChkHC; decide +kernel))
local macro "r_dec" : tactic => `(tactic| (unfold rChkHC; decide +kernel))
local macro "ph_dec" : tactic => `(tactic| (unfold phOffW; decide +kernel))
local macro "si_dec" : tactic => `(tactic| (unfold siOffW; decide +kernel))

theorem chHH_d0 : dChkHC ".Lwc_main" "scc_rt_abort" 0 [0, 1, 2] [3] Abort.Disp.d0 = true := by d_dec
theorem chHH_t1 : dChkHC ".Lwc_main" ".Lscc_rt_abort.entry" 0 [] [0, 1, 2, 3] Abort.Disp.t1 = true := by d_dec
theorem chHH_j1 : dChkHC ".Lwc_main" ".Lscc_rt_abort.entry" 16 [] [0] Abort.Disp.j1 = true := by d_dec
theorem chHH_t2 : dChkHC ".Lwc_main" ".Lscc_rt_abort.next1" 0 [] [0, 1, 2, 3] Abort.Disp.t2 = true := by d_dec
theorem rHH_d0 : rChkHC "scc_rt_abort" 0 [] [0] [1, 2, 3] Abort.Disp.d0 = true := by r_dec
theorem rHH_t1 : rChkHC ".Lscc_rt_abort.entry" 0 [] [] [0, 1, 2, 3] Abort.Disp.t1 = true := by r_dec
theorem rHH_j1 : rChkHC ".Lscc_rt_abort.entry" 16 [] [] [0] Abort.Disp.j1 = true := by r_dec
theorem rHH_t2 : rChkHC ".Lscc_rt_abort.next1" 0 [] [] [0, 1, 2, 3] Abort.Disp.t2 = true := by r_dec
theorem chHH_g2 :
    phOffW ".Lwc_main" ".Lscc_rt_abort.is2" 0 ".Lscc_rt_abort.is2" Abort.Disp.g2 = true := by ph_dec
theorem chHH_x0 : phOffW ".Lwc_main" Abort.heap.fn 0 Abort.heap.fn Abort.x0 = true := by ph_dec
theorem chHH_n1 : siOffW ".Lwc_main" Abort.heap.entry 0 7 = true := by si_dec
theorem chHH_x1 : phOffW ".Lwc_main" Abort.heap.entry 7 Abort.heap.entry Abort.x1Heap = true := by ph_dec
theorem chHH_sys : siOffW ".Lwc_main" Abort.heap.entry 34 2 = true := by si_dec
theorem chHH_x2 : phOffW ".Lwc_main" Abort.heap.entry 36 Abort.heap.entry Abort.x2 = true := by ph_dec

/-! ## The path -/

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region}
  {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

set_option maxHeartbeats 800000 in
/-- **The heap abort path's nodes keep both abort phases** at hello's threads abort phase (`WakeWf.hpathW_ph` at
`AcH`, hello's code labels). Unlike AArch64, the region is `[-24, 16)` without an alignment premise, and the
return address is the pushed word (`slot 8`), kept off `raT` by `rHH_*` and the run's offsets. -/
theorem hpathW_phH (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hphs : abortPhHeapOk okPc ph lab = true)
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some a → lab l = Int64.ofNat a)
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.heap.exit).toBitVec.toNat ≠ a)
    (hra : ra ≠ ThreadsAb.raT lab ".Lwc_main") :
    Abort.Disp.HPathW (fun s _ => AbSt μ (WriteAb.Ab lab) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH lab ".Lwc_main") s) (fun _ _ => False) exe endPc R F c0 ra := by
  have hl := hI.labOk
  subst hl
  have hsd := hab
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  have hst := hsd.1.1.1.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hx0, hn1, hx1, hsysIn, hx2, hx, -, -⟩ := hst
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, px0, o1, -, px1, o34, -, px2, -⟩ := hphs
  have hoff : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  have hoff8 : R.Off 8 := ⟨by decide, by omega, by omega⟩
  -- the tests' data: the code `2` at `-8(%rbp)`, `slot 8 = ra`
  have hTt : ∀ {blk : List (Directive × Nat)}, (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) →
      ∀ (pc : Int64) (σ : Spike.Lib.X64.AS), σ.slot (-8) = 2#64 → ∀ k, k < blk.length →
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).so.get .rbp = some 0 ∧
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).σ.slot (-8) ≠ 4#64 := fun hb pc σ h2 k hk => by
    obtain ⟨h1, h3⟩ := Spike.Lib.LowerX64.tj_keep _ hb pc σ (j := k + 1) (by omega)
    refine ⟨h1, fun h => ?_⟩
    rw [h3, h2] at h
    exact absurd h (by decide)
  have hXt : ∀ {blk : List (Directive × Nat)} {pc : Int64} {S P B : List Nat},
      (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) → S = [] → P = [] →
      rChk (_root_.Executable.labels exe).label pc S P B blk = true →
      ∀ σ c, (fun σ c => c = c0 ∧ σ.slot (-8) = 2#64 ∧ σ.slot 8 = ra) σ c →
      ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a → ∀ s' : State,
      s'.st.2 ∈ aiTgts (_root_.Executable.labels exe).label
        (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) 0 a →
      Spike.Lib.X64.Abs R
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨pc, Abort.Disp.oD, σ⟩).so
        s'.st.1
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨pc, Abort.Disp.oD, σ⟩).σ →
      ¬ ThreadsAb.RaW (_root_.Executable.labels exe).label s'
        (ThreadsAb.raT (_root_.Executable.labels exe).label ".Lwc_main") := by
    intro blk pc S P B hb hS hP h
    subst hS hP
    exact hX_of (n := ⟨pc, Abort.Disp.oD, fun σ c => c = c0 ∧ σ.slot (-8) = 2#64 ∧ σ.slot 8 = ra⟩) h hoff8
      (fun _ _ _ _ _ h => by simp at h) (fun _ _ _ _ _ h => by simp at h)
      (fun σ _ _ k hk _ => (Spike.Lib.LowerX64.tj_keep _ hb pc σ (j := k + 1) (by omega)).1)
      (fun σ c hJ k hk => by rw [tj_ra _ hb pc σ (by omega), hJ.2.2]; exact hra)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hr := rChkHC_sound hlab rHH_d0
    rw [ofNat_zero'] at hr
    refine blkW_dispIH hI hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR (by omega) (by omega) hoff pd0 (by decide)
      (dChkHC_sound hlab chHH_d0) (fun σ c hJ k hk hkE => ?_) (fun σ c hJ k hk hkT => ?_)
      (hX_of hr hoff8 (fun _ _ _ _ _ h => by simp at h) (fun σ _ _ k _ hk => ?_) (fun σ _ _ k _ hk => ?_)
        (fun σ c hJ k hk => ?_))
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      have hk3 : k + 1 < Abort.Disp.d0.length := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkE
        have : Abort.Disp.d0.length = 4 := by decide
        omega
      rw [Spike.Lib.X64.StubW.d0_rdi _ σ hk3, hJ.2.1]
      decide
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      obtain rfl : k = 3 := by simpa using hkT
      obtain ⟨hbp, hsl⟩ := Spike.Lib.LowerX64.d0_end (_root_.Executable.labels exe).label
        ((_root_.Executable.labels exe).label "scc_rt_abort") σ
      refine ⟨hbp, ?_⟩
      rw [hsl, hJ.2.1]
      decide
    · obtain rfl : k = 0 := by simpa using hk
      exact d0_sp1 _ _ σ
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      exact d0_bp _ _ σ (by omega) (by simp [Abort.Disp.d0]; omega)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      rw [d0_ra _ _ σ (by omega), hJ.2.2]
      exact hra
  · refine blkW_dispIH hI ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR (by omega) (by omega) hoff pt1 (by decide)
      (dChkHC_sound hlab chHH_t1) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (hXt (.inl rfl) rfl rfl (by have hr := rChkHC_sound hlab rHH_t1; rwa [ofNat_zero'] at hr))
    dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
    exact hTt (.inl rfl) _ σ hJ.2.1 k hk
  · refine blkW_dispIH hI hj1 rfl Abort.Disp.j1_ok hR (by omega) (by omega) hoff pj1 (by decide)
      (dChkHC_sound hlab chHH_j1) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (hXt (.inr (.inr rfl)) rfl rfl (rChkHC_sound hlab rHH_j1))
    dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
    exact hTt (.inr (.inr rfl)) _ σ hJ.2.1 k hk
  · refine blkW_dispIH hI ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR (by omega) (by omega) hoff pt2 (by decide)
      (dChkHC_sound hlab chHH_t2) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (hXt (.inr (.inl rfl)) rfl rfl (by have hr := rChkHC_sound hlab rHH_t2; rwa [ofNat_zero'] at hr))
    dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
    exact hTt (.inr (.inl rfl)) _ σ hJ.2.1 k hk
  · exact blkW_phIH hI hg2 (ofNat_zero' _) Abort.Disp.g2_ok hR (by omega) (by omega) pg2 (by decide)
      (phOffW_sound hlab chHH_g2)
  · exact blkW_phIH hI hx0 (ofNat_zero' _) Abort.x0_ok hR (by omega) (by omega) px0 (by decide)
      (phOffW_sound hlab chHH_x0)
  · exact nodeW_siIH hI hn1 (ofNat_zero' _) o1 (siOffW_sound hlab chHH_n1)
  · exact blkW_phIH hI hx1 rfl Abort.x1Heap_ok hR (by omega) (by omega) px1 (by decide)
      (phOffW_sound hlab chHH_x1)
  · exact nodeW_sysIH hI hsysIn rfl o34 (siOffW_sound hlab chHH_sys)
  · exact blkW_phIH hI hx2 rfl Abort.x2_ok hR (by omega) (by omega) px2 (by decide)
      (phOffW_sound hlab chHH_x2)
  · exact nodeW_exitIH hI hx (ofNat_zero' _) rfl htk fun _ _ h => h.2.1

/-- **`hpathW_phH`'s `hra` at hello's heap abort entry**: the return address past the full branch of
`scc_rt_alloc` is not the threads abort's. Unlike AArch64 (`bl` at `+ 8`), the `call scc_rt_abort` ends at
`.full + 12`; the fact is `fullChkH_sound`'s. -/
theorem hra_allocH
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some a → lab l = Int64.ofNat a) :
    (lab Spike.Lib.X64.Alloc.fullL + 12).toBitVec ≠ ThreadsAb.raT lab ".Lwc_main" :=
  (fullChkH_sound hlab).2.2.2.2

end Spike.Lib.X64.HelloWf

/-- info: 'Spike.Lib.X64.HelloWf.dChkHC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.dChkHC_sound

/-- info: 'Spike.Lib.X64.HelloWf.rChkHC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.rChkHC_sound

/-- info: 'Spike.Lib.X64.HelloWf.blkW_dispPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.blkW_dispPhH

/-- info: 'Spike.Lib.X64.HelloWf.nodeW_sysIH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.nodeW_sysIH

/-- info: 'Spike.Lib.X64.HelloWf.nodeW_exitIH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.nodeW_exitIH

/-- info: 'Spike.Lib.X64.HelloWf.hpathW_phH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.hpathW_phH

/-- info: 'Spike.Lib.X64.HelloWf.hra_allocH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.hra_allocH
