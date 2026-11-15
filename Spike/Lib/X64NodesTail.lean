/-
**The node obligations along a relabelling of the executable and end**
(x86-64; the post-pass transfer of the consumer's `NodesA`, `TakePathS`,
`AbortPathS`): the node obligations at a frame invariant `I` of the states
of one executable and end (`exeE`, `endE`) give them at the relabelled
invariant `relabI I` of the states of another (`exeF`, `endF`), when the
second holds every instruction cell of the first (`TailOK.cell`), the two
label tables agree off `B` (`TailOK.lab`) and no instruction cell names a
label of `B` (`TailOK.free`). The AArch64 twin is
`Spike/Lib/A64NodesTail.lean`.

- `relab_relab`, `exec_shape`, `leaves_keep`, `certSuccs_keep`, `skip_relab`:
  relabelling, the step's leaves and the kernel's view;
- `instr_of_exec`, `instr_of_nodes`: every pair of the node obligations is at
  an instruction cell;
- `TailOK`, `relabI`: the hypotheses and the relabelled invariant;
- `takePathS_tail`, `abortPathS_tail`: the take and abort paths along the
  relabelling;
- `nodesA_tail_own`, `nodesA_tail`: the node obligations along the
  relabelling, the owned words of the relabelled states another's (the rows by
  `RestTail.outS_map`, their landings back through `RestTail.outS_leaf`).
-/
import Spike.Lib.X64AbiRelab
import Spike.Lib.TreeMap
import Spike.Lib.X64ConsumerA

namespace Spike.Lib.X64NodesTail

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt exec_of_cellAt)
open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64RestTail (relab)
open Spike.Lib.RestTail (Leaves)

/-! ## Relabelling and the step's leaves -/

/-- Relabelling back undoes relabelling, at a state of the first executable
and end. -/
theorem relab_relab {exe exe' : _root_.Executable} {endPc endPc' : Int64} {s : State} (he : s.exe = exe)
    (hn : s.endPc = endPc) : relab exe endPc (relab exe' endPc' s) = s := by
  cases s; cases he; cases hn; rfl

/-- **An x86-64 step only moves the machine state**: its tree is a tree of
machine states, each leaf `s` with that machine state. -/
theorem exec_shape {s : State} {t : EvTree State} (hx : exec s = some t) :
    ∃ t0 : EvTree MachineState, t = t0.map fun st => { s with st } := by
  unfold exec at hx
  split at hx
  · cases hx
  · cases hx; exact ⟨_, rfl⟩

/-- **Every leaf of an x86-64 step keeps the executable and end.** -/
theorem leaves_keep {s : State} {t : EvTree State} (hx : exec s = some t) :
    Leaves (fun x => x.exe = s.exe ∧ x.endPc = s.endPc) t := by
  obtain ⟨t0, rfl⟩ := exec_shape hx
  exact (Spike.Lib.TreeMap.leaves_map _ t0).2 (Spike.Lib.TreeMap.leaves_true (fun _ => ⟨rfl, rfl⟩) t0)

/-- The states the kernel may resume a thread in keep its executable and end. -/
theorem certSuccs_keep {s x : State} {call : Kernel.Call} (hx : x ∈ Kernel.certSuccs abi s call) :
    x.exe = s.exe ∧ x.endPc = s.endPc := by
  cases call <;> simp only [Kernel.certSuccs] at hx <;>
    first
    | (obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx; exact ⟨rfl, rfl⟩)
    | (cases hx with | head => exact ⟨rfl, rfl⟩ | tail _ h => cases h)

/-- **Stepping over a transfer site commutes with relabelling** at a cell
both executables hold. -/
theorem skip_relab {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive} {sz : Nat}
    (h : CellAt s d sz) (h' : CellAt (relab exe endPc s) d sz) (m : _root_.Mem 64) :
    abi.skip (abi.setDmem (relab exe endPc s) m) = relab exe endPc (abi.skip (abi.setDmem s m)) := by
  have hc : CellAt (abi.setDmem s m) d sz := ⟨h.valid, h.ne, h.code⟩
  have hc' : CellAt (abi.setDmem (relab exe endPc s) m) d sz := ⟨h'.valid, h'.ne, h'.code⟩
  have hn : nextPc (abi.setDmem (relab exe endPc s) m) = nextPc (abi.setDmem s m) := by
    rw [Spike.Lib.X64AbiRelab.nextPc_of_cellAt hc', Spike.Lib.X64AbiRelab.nextPc_of_cellAt hc]; rfl
  simp only [abi] at hn ⊢
  rw [hn]; rfl

/-! ## Pairs at instruction cells -/

/-- **A step that neither halts nor faults is at an instruction cell**: in a
validly laid-out executable, stepping `s` to a tree other than a fault means
the pc is short of the end and at an instruction (a data cell's step is a
fault). -/
theorem instr_of_exec {s : State} (hv : Kraken.Executable.ValidLayout s.exe) {t : EvTree State}
    (hx : exec s = some t) (hf : ∀ m, t ≠ .fault m) : ∃ i z, CellAt s (.instr i) z := by
  have hne : (s.st.2 == s.endPc) = false := by
    unfold exec at hx
    cases h : (s.st.2 == s.endPc)
    · rfl
    · simp [h] at hx
  have hdir : s.directive.isSome := by
    unfold exec at hx
    cases h : s.directive
    · simp [h] at hx
    · rfl
  have hdc : s.directive = ((Kraken.Executable.codeAt s.exe s.st.2).head?).map (·.1) := by
    unfold State.directive
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress s.exe s.st.2) =
        Kraken.Executable.codeAt s.exe s.st.2 from by
      unfold Kraken.Executable.codeAt
      congr 1]
  rw [hdc] at hdir
  obtain ⟨⟨d, z⟩, rest, hc⟩ : ∃ c rest, Kraken.Executable.codeAt s.exe s.st.2 = c :: rest := by
    cases h : Kraken.Executable.codeAt s.exe s.st.2 with
    | nil => rw [h] at hdir; cases hdir
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hcell : CellAt s d z := ⟨hv, hne, rest, hc⟩
  cases d with
  | instr i => exact ⟨i, z, hcell⟩
  | label l =>
    unfold Kraken.Executable.codeAt at hc
    have hl := List.head_dropWhile_not (fun c : Directive × Nat => c.1.isLabel) (by rw [hc]; nofun)
    have hh : (List.dropWhile (fun c : Directive × Nat => c.1.isLabel)
        (Kraken.Executable.directivesFromAddress s.exe s.st.2)).head (by rw [hc]; nofun) = (.label l, z) := by
      simp only [hc, List.head_cons]
    rw [hh] at hl
    cases hl
  | byteArray a =>
    rw [exec_of_cellAt hcell] at hx
    cases hx
    exact absurd rfl (hf _)

open Spike.Lib.X64ConsumerS (InvS TakePathS) in
open Spike.Lib.X64ConsumerA (NodesA PubOut msOfAX) in
/-- **Every pair of the node obligations is at an instruction cell**, in a
validly laid-out executable: at a system call the `syscall`
(`NodesA.svc`), at the take site its `nop` (`TakePathS.site`), elsewhere the
row's instruction (directly or after the source's publication, `PubOut`),
which does not fault (`OutS.exec_ne_fault`). -/
theorem instr_of_nodes {Λ : Scc.Sem.Layout} {p : CoreTerm.Prog} {μ : Scc.Sem.Marks}
    {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Spike.Lib.X64ConsumerS.OwnS}
    {ar : Spike.Lib.Arena} {I : InvS} {ab : Option (State → Prop)} {Cl : State → Prop} {rS : Scc.Sem.Range}
    {Tk : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl) (hT : TakePathS Λ p μ I rS Tk)
    {lbl lsize s c fs} (hI : I lbl lsize s c fs) (hv : Kraken.Executable.ValidLayout s.exe) :
    ∃ i z, CellAt s (.instr i) z := by
  cases hs : abi.atSys s
  · by_cases ht : ∃ a, μ.site .take = some a ∧ pcOf s = a
    · obtain ⟨a, ha, hpc⟩ := ht
      obtain ⟨-, ⟨_, z, hz⟩, -⟩ := hT.site lbl lsize s c fs hI a ha hpc
      exact ⟨_, z, hz⟩
    · have hnsys : ∀ fs₁ K, (msOfAX Λ μ p rd G own ar I ab lbl lsize fs₁).K = some K →
          K.atSys s = true → False := by
        intro fs₁ K hK' hK''
        obtain rfl : K = abi := by cases ab <;> exact (Option.some.inj hK').symm
        exact absurd hK'' (by simp [hs])
      obtain ⟨c₁, hO⟩ : ∃ c₁, Spike.Lib.OutS p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize)
          (Spike.Lib.Pend p (I lbl lsize)) s c₁ fs := by
        rcases hN.out lbl lsize s c fs hI (fun a ha hpc => ht ⟨a, ha, hpc⟩) (by simp [hs]) with h | h
        · exact ⟨c, h⟩
        · obtain ⟨-, -, c₁, -, -, h⟩ := h
          exact ⟨c₁, h⟩
      obtain ⟨t, ht⟩ : ∃ t, exec s = some t := by
        rcases Spike.Lib.RestTail.OutS.exec_or_sys hO with h | ⟨fs₁, K, h1, h2⟩
        · exact Option.isSome_iff_exists.mp h
        · exact (hnsys fs₁ K h1 h2).elim
      refine instr_of_exec hv ht fun m hm => ?_
      rcases Spike.Lib.RestTail.OutS.exec_ne_fault hO m with h | ⟨fs₁, K, h1, h2⟩
      · exact h (hm ▸ ht)
      · exact hnsys fs₁ K h1 h2
  · obtain ⟨z, hz⟩ := hN.svc lbl lsize s c fs hI hs
    exact ⟨_, z, hz⟩

/-! ## The hypotheses and the relabelled invariant -/

open Spike.Lib.X64LabelCongr (Directive.Free)
open Spike.Lib.X64ConsumerS (InvS OwnS IRun TakePathS AbortPathS)
open Spike.Lib.X64ConsumerA (NodesA)

/-- **The second executable and end hold the first's instructions**: every
instruction cell of a state of `exeE`, `endE` is one of the state relabelled
to `exeF`, `endF` (`cell`), naming no label of `B` (`free`); the two label
tables agree off `B` (`lab`); the first's layout is valid (`valid`). -/
structure TailOK (exeE exeF : _root_.Executable) (endE endF : Int64) (B : List Label) : Prop where
  cell : ∀ (s : State) i z, s.exe = exeE → s.endPc = endE → CellAt s (.instr i) z →
    CellAt (relab exeF endF s) (.instr i) z
  lab : ∀ l, l ∉ B → (_root_.Executable.labels exeF).label l = (_root_.Executable.labels exeE).label l
  free : ∀ (s : State) i z, s.exe = exeE → CellAt s (.instr i) z → Directive.Free B (.instr i)
  valid : Kraken.Executable.ValidLayout exeE

/-- **The relabelled invariant**: the states of `exeF`, `endF` whose
relabelling to `exeE`, `endE` is in `I`. -/
def relabI (exeE exeF : _root_.Executable) (endE endF : Int64) (I : InvS) : InvS :=
  fun lbl lsize s c fs => s.exe = exeF ∧ s.endPc = endF ∧ I lbl lsize (relab exeE endE s) c fs

variable {exeE exeF : _root_.Executable} {endE endF : Int64} {B : List Label}

/-- A state of the relabelled invariant is the relabelling of a state of `I`
of `exeE`, `endE`. -/
theorem relabI.elim {I : InvS} {lbl lsize s c fs} (h : relabI exeE exeF endE endF I lbl lsize s c fs) :
    ∃ s0 : State, (s0.exe = exeE ∧ s0.endPc = endE) ∧ s = relab exeF endF s0 ∧ I lbl lsize s0 c fs :=
  ⟨_, ⟨rfl, rfl⟩, (relab_relab h.1 h.2.1).symm, h.2.2⟩

/-- The relabelling of a state of `I` of `exeE`, `endE` is in the relabelled
invariant. -/
theorem relabI.of {I : InvS} {lbl lsize s c fs} (hs : s.exe = exeE ∧ s.endPc = endE)
    (h : I lbl lsize s c fs) : relabI exeE exeF endE endF I lbl lsize (relab exeF endF s) c fs :=
  ⟨rfl, rfl, by rw [relab_relab hs.1 hs.2]; exact h⟩

/-- A predicate read through the relabelling back, at a relabelled state of
`exeE`, `endE`. -/
theorem comp_relab {P : State → Prop} {s : State} (hs : s.exe = exeE ∧ s.endPc = endE) :
    (P ∘ relab exeE endE) (relab exeF endF s) = P s := by
  simp only [Function.comp]; rw [relab_relab hs.1 hs.2]

/-- The step of a relabelled state at an instruction cell of `exeE`, `endE`. -/
theorem TailOK.exec (hO : TailOK exeE exeF endE endF B) {s : State} (hs : s.exe = exeE ∧ s.endPc = endE)
    {i z} (h : CellAt s (.instr i) z) :
    exec (relab exeF endF s) = (exec s).map (EvTree.map (relab exeF endF)) :=
  Spike.Lib.X64RestTail.exec_relab_cell h (hO.cell s i z hs.1 hs.2 h)
    (fun l hl => by rw [hs.1]; exact hO.lab l hl) (hO.free s i z hs.1 h)

/-- **A step from the relabelled state is a relabelled step** (`TailOK.exec`
as a tree). -/
theorem TailOK.tree (hO : TailOK exeE exeF endE endF B) {s : State} (hs : s.exe = exeE ∧ s.endPc = endE)
    {i z} (h : CellAt s (.instr i) z) {tree : EvTree State} (he : isa.exec (relab exeF endF s) = some tree) :
    ∃ t0, X64.exec s = some t0 ∧ tree = t0.map (relab exeF endF) ∧
      Leaves (fun x => x.exe = exeE ∧ x.endPc = endE) t0 := by
  have he' : X64.exec (relab exeF endF s) = some tree := he
  rw [hO.exec hs h] at he'
  cases ht : X64.exec s with
  | none => rw [ht] at he'; cases he'
  | some t0 =>
    rw [ht] at he'; cases he'
    refine ⟨t0, rfl, rfl, ?_⟩
    have hl := leaves_keep ht
    rw [hs.1, hs.2] at hl
    exact hl

/-- The kernel's view of a relabelled state at an instruction cell. -/
theorem TailOK.abi (hO : TailOK exeE exeF endE endF B) {s : State} (hs : s.exe = exeE ∧ s.endPc = endE)
    {i z} (h : CellAt s (.instr i) z) :
    X64.abi.atSys (relab exeF endF s) = X64.abi.atSys s ∧ X64.abi.nr (relab exeF endF s) = X64.abi.nr s ∧
      X64.abi.arg (relab exeF endF s) = X64.abi.arg s ∧
      (∀ x, X64.abi.ret (relab exeF endF s) x = relab exeF endF (X64.abi.ret s x)) ∧
      (∀ call, Kernel.certSuccs X64.abi (relab exeF endF s) call =
        (Kernel.certSuccs X64.abi s call).map (relab exeF endF)) :=
  Spike.Lib.X64AbiRelab.kAt_relab_cell h (hO.cell s i z hs.1 hs.2 h) X64.abi rfl

/-- **An instruction tree's successors, relabelled**, keep an invariant that
its own successors keep (`AllInv` of `P ∘ relab exeE endE`). -/
theorem allInv_relab {G : Loc → Val → Prop} {P : State → Prop} {t0 : EvTree State}
    (hl : Leaves (fun x => x.exe = exeE ∧ x.endPc = endE) t0) (h : t0.AllInv G P) :
    (t0.map (relab exeF endF)).AllInv G (P ∘ relab exeE endE) :=
  (EvTree.allInv_map G _ _ t0).2 ((Spike.Lib.TreeMap.leaves_and_allInv hl h).mono fun _ ⟨h1, h2⟩ => by
    rw [comp_relab h2]; exact h1)

/-! ## The take and abort paths -/

variable {Λ : Scc.Sem.Layout} {p : Prog} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own own' : OwnS} {ar : Spike.Lib.Arena} {I : InvS} {ab : Option (State → Prop)} {Cl : State → Prop}
  {rS : Range} {Tk Ab : State → Prop}

/-- **The take path along the relabelling.** -/
theorem takePathS_tail (hO : TailOK exeE exeF endE endF B) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakePathS Λ p μ I rS Tk) :
    TakePathS Λ p μ (relabI exeE exeF endE endF I) rS (Tk ∘ relab exeE endE) where
  site lbl lsize s c fs hI a hμ hpc := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    obtain ⟨hTk, ⟨n, sz, hnop⟩, hsys, hr, h1, h2, h3, hpm⟩ := hT.site lbl lsize s0 c fs hI0 a hμ hpc
    refine ⟨by rw [comp_relab hs0]; exact hTk, ⟨n, sz, hO.cell _ _ _ hs0.1 hs0.2 hnop⟩,
      by rw [(hO.abi hs0 hc).1]; exact hsys, hr, h1, h2, h3, fun pm => ?_⟩
    obtain ⟨c', fs', hr', hI', hTk'⟩ := hpm pm
    have hd : abi.dmem (relab exeF endF s0) = abi.dmem s0 := rfl
    rw [hd]
    have hy : (abi.skip (abi.setDmem s0 (Kernel.copyRange pm (abi.dmem s0) rS))).exe = exeE ∧
        (abi.skip (abi.setDmem s0 (Kernel.copyRange pm (abi.dmem s0) rS))).endPc = endE := hs0
    refine ⟨c', fs', hr', ?_, ?_⟩
    · rw [skip_relab hc (hO.cell _ _ _ hs0.1 hs0.2 hc)]; exact relabI.of hy hI'
    · rw [skip_relab hc (hO.cell _ _ _ hs0.1 hs0.2 hc), comp_relab hy]; exact hTk'
  instr lbl lsize s c fs hI hsite hsys tree he := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    obtain ⟨t0, ht0, rfl, hl⟩ := hO.tree hs0 hc he
    rw [(hO.abi hs0 hc).1] at hsys
    have h := allInv_relab (exeF := exeF) (endF := endF) hl (hT.instr lbl lsize s0 c fs hI0 hsite hsys t0 ht0)
    exact h.mono fun x hx => by simp only [Function.comp] at hx ⊢; rw [relab_relab hs0.1 hs0.2]; exact hx
  sys lbl lsize s c fs hI hsys call hd s' hs' := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    have hk := hO.abi hs0 hc
    rw [hk.2.2.2.2 call] at hs'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs'
    have hxe := certSuccs_keep hx
    have hy : x.exe = exeE ∧ x.endPc = endE := ⟨hxe.1.trans hs0.1, hxe.2.trans hs0.2⟩
    rw [hk.1] at hsys
    rw [hk.2.1, hk.2.2.1] at hd
    rw [comp_relab hy, comp_relab hs0]
    exact hT.sys lbl lsize s0 c fs hI0 hsys call hd x hx
  owned lbl lsize s c fs hI hTk := hT.owned lbl lsize (relab exeE endE s) c fs hI.2.2 hTk

/-- **The abort path along the relabelling.** -/
theorem abortPathS_tail (hO : TailOK exeE exeF endE endF B) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakePathS Λ p μ I rS Tk) {cells ctr : Nat} (hA : AbortPathS μ I Ab cells ctr) :
    AbortPathS μ (relabI exeE exeF endE endF I) (Ab ∘ relab exeE endE) cells ctr where
  at_ lbl lsize s c fs hI k a hμ hpc := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    have hk := hO.abi hs0 hc
    rw [hk.2.1, hk.2.2.1, comp_relab hs0]
    exact hA.at_ lbl lsize s0 c fs hI0 k a hμ hpc
  instr lbl lsize s c fs hI hab hsys tree he := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    obtain ⟨t0, ht0, rfl, hl⟩ := hO.tree hs0 hc he
    rw [(hO.abi hs0 hc).1] at hsys
    rw [comp_relab hs0] at hab
    exact allInv_relab (exeF := exeF) (endF := endF) (P := fun s' => ¬ Ab s') hl
      (hA.instr lbl lsize s0 c fs hI0 hab hsys t0 ht0)
  sys lbl lsize s c fs hI hab hsys call hd s' hs' hab' := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    have hk := hO.abi hs0 hc
    rw [hk.2.2.2.2 call] at hs'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs'
    have hxe := certSuccs_keep hx
    have hy : x.exe = exeE ∧ x.endPc = endE := ⟨hxe.1.trans hs0.1, hxe.2.trans hs0.2⟩
    rw [hk.1] at hsys
    rw [hk.2.1, hk.2.2.1] at hd
    rw [comp_relab hy] at hab'
    rw [comp_relab hs0] at hab
    obtain ⟨fd, buf, n, hcall, hr⟩ := hA.sys lbl lsize s0 c fs hI0 hab hsys call hd x hx hab'
    refine ⟨fd, buf, n, hcall, fun r hr' => hr r ?_⟩
    rw [hk.2.2.2.1 r] at hr'
    have h2 := congrArg (relab exeE endE) hr'
    rwa [relab_relab (s := abi.ret s0 r) hs0.1 hs0.2, relab_relab hy.1 hy.2] at h2
  take lbl lsize s c fs hI hab a hμ hpc m := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    have hy : (abi.skip (abi.setDmem s0 m)).exe = exeE ∧ (abi.skip (abi.setDmem s0 m)).endPc = endE := hs0
    rw [comp_relab hs0] at hab
    rw [skip_relab hc (hO.cell _ _ _ hs0.1 hs0.2 hc), comp_relab hy]
    exact hA.take lbl lsize s0 c fs hI0 hab a hμ hpc m

/-! ## The node obligations -/

open Spike.Lib.X64ConsumerA (msOfAX msOfA CtrRow PendA)
open Spike.Lib.RestTail (LeafQ MsMap outS_leaf outS_map)
open Kraken.Promising.Live.RunnerSim (mapT mapO)

/-- A frame run's pair of the relabelled invariant is one of `I`, relabelled back. -/
theorem irun_back {lbl lsize s c fs} (h : IRun p (relabI exeE exeF endE endF I) lbl lsize s c fs) :
    IRun p I lbl lsize (relab exeE endE s) c fs :=
  let ⟨c₀, fs₀, hI, hr⟩ := h
  ⟨c₀, fs₀, hI.2.2, hr⟩

/-- A frame run's pair of the relabelled invariant is the relabelling of one
of `I` of `exeE`, `endE`, with a pair of `I` at the state. -/
theorem irun_elim {lbl lsize s c fs} (h : IRun p (relabI exeE exeF endE endF I) lbl lsize s c fs) :
    ∃ s0 : State, (s0.exe = exeE ∧ s0.endPc = endE) ∧ s = relab exeF endF s0 ∧ IRun p I lbl lsize s0 c fs ∧
      ∃ c₀ fs₀, I lbl lsize s0 c₀ fs₀ :=
  let ⟨c₀, fs₀, hI, hr⟩ := h
  ⟨_, ⟨rfl, rfl⟩, (relab_relab hI.1 hI.2.1).symm, ⟨c₀, fs₀, hI.2.2, hr⟩, c₀, fs₀, hI.2.2⟩

/-- **An outcome of a relabelled thread is a relabelled outcome**, at an
instruction cell of `exeE`, `endE`. -/
theorem TailOK.step (hO : TailOK exeE exeF endE endF B) (A : Arch) {t : Thread isa} {s0 : State}
    (hs0 : s0.exe = exeE ∧ s0.endPc = endE) {i z} (hc : CellAt s0 (.instr i) z) (ht : t.st = relab exeF endF s0)
    {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ outs0 o0, stepOne A { t with st := s0 } tid mem = some outs0 ∧ .ok o0 ∈ outs0 ∧
      o = mapO (relab exeF endF) o0 := by
  have htm : t = mapT (relab exeF endF) { t with st := s0 } := by cases t; subst ht; rfl
  rw [htm] at hs
  exact Spike.Lib.StepOneMap.ok_mem_map (hO.exec hs0 hc)
    (Spike.Lib.X64RestTail.deps_relab_cell hc (hO.cell _ _ _ hs0.1 hs0.2 hc)) rfl hs ho

/-- Every state a row of a state of `exeE`, `endE` lands in keeps them. -/
theorem leafQ_msOfAX {s0 : State} (hs0 : s0.exe = exeE ∧ s0.endPc = endE) (lbl lsize fs) :
    LeafQ (fun x : State => x.exe = exeE ∧ x.endPc = endE) (msOfAX Λ μ p rd G own ar I ab lbl lsize fs) s0 where
  exec t ht := by
    have hl := leaves_keep ht
    rw [hs0.1, hs0.2] at hl
    exact hl
  ret K hK x := by
    obtain rfl : K = abi := by cases ab <;> exact (Option.some.inj hK).symm
    exact hs0
  succs K hK call s' hs' := by
    obtain rfl : K = abi := by cases ab <;> exact (Option.some.inj hK).symm
    have h := certSuccs_keep hs'
    exact ⟨h.1.trans hs0.1, h.2.trans hs0.2⟩

/-- **The memory sides of the rows along the relabelling**, at a state of
`exeE`, `endE` at an instruction cell: the same but the allocation
fragments (into the relabelled invariant, the landing's leaf fact giving
the way back) and the write abort phase (read through the relabelling). -/
theorem msMap_msOfAX (hO : TailOK exeE exeF endE endF B) (hown : ∀ s fs, own' (relab exeF endF s) fs = own s fs)
    {s0 : State} (hs0 : s0.exe = exeE ∧ s0.endPc = endE) {i z} (hc : CellAt s0 (.instr i) z) (lbl lsize fs) :
    MsMap (relab exeF endF)
      ((msOfAX Λ μ p rd G own ar I ab lbl lsize fs).withQ (fun x : State => x.exe = exeE ∧ x.endPc = endE))
      (msOfAX Λ μ p rd G own' ar (relabI exeE exeF endE endF I) (ab.map (· ∘ relab exeE endE)) lbl lsize fs) s0 := by
  have hk := hO.abi hs0 hc
  cases ab with
  | none =>
    exact { rd := rfl, rt := rfl, K := rfl, G := rfl, heap := rfl, ctr := rfl, units := rfl, off := rfl,
            cells := rfl, mp := rfl, lo := rfl, pub := rfl, newOk := rfl, own := hown s0 fs,
            abortAt := Iff.rfl, pl := fun _ h => h,
            xa := fun _ _ _ _ _ h => ⟨h.1.1, relabI.of h.2 h.1.2⟩,
            bo := fun _ _ _ h => h, we := fun _ h => h,
            kAt := fun K hK => by obtain rfl : K = abi := (Option.some.inj hK).symm; exact hk }
  | some Ab =>
    exact { rd := rfl, rt := rfl, K := rfl, G := rfl, heap := rfl, ctr := rfl, units := rfl, off := rfl,
            cells := rfl, mp := rfl, lo := rfl, pub := rfl, newOk := rfl, own := hown s0 fs,
            abortAt := Iff.rfl, pl := fun _ h => h,
            xa := fun _ _ _ _ _ h => ⟨h.1.1, relabI.of h.2 h.1.2⟩,
            bo := fun _ _ _ h => h,
            we := fun _ h r hr => by
              have hy : (abi.ret s0 r).exe = exeE ∧ (abi.ret s0 r).endPc = endE := hs0
              show (Ab ∘ relab exeE endE) (abi.ret (relab exeF endF s0) r)
              rw [hk.2.2.2.1 r, comp_relab hy]
              exact h r hr,
            kAt := fun K hK => by obtain rfl : K = abi := (Option.some.inj hK).symm; exact hk }

/-- **A row at any depth along the relabelling**, landing with a pending
frame run into the relabelled invariant. -/
theorem outS_relab (hO : TailOK exeE exeF endE endF B) (hown : ∀ s fs, own' (relab exeF endF s) fs = own s fs)
    {s0 : State} (hs0 : s0.exe = exeE ∧ s0.endPc = endE) {i z} (hc : CellAt s0 (.instr i) z) {lbl lsize c fs}
    (h : Spike.Lib.OutS p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize) (Spike.Lib.Pend p (I lbl lsize)) s0 c fs) :
    Spike.Lib.OutS p lbl
      (msOfAX Λ μ p rd G own' ar (relabI exeE exeF endE endF I) (ab.map (· ∘ relab exeE endE)) lbl lsize)
      (Spike.Lib.Pend p (relabI exeE exeF endE endF I lbl lsize)) (relab exeF endF s0) c fs := by
  have h' := outS_leaf (fun fs => leafQ_msOfAX hs0 lbl lsize fs) h
  refine (outS_map (relab exeF endF) (hO.exec hs0 hc) (fun fs => msMap_msOfAX hO hown hs0 hc lbl lsize fs)
    h').mono ?_
  rintro _ c' fs' ⟨x, ⟨⟨c'', fs'', hr, hx⟩, hq⟩, rfl⟩
  exact ⟨c'', fs'', hr, relabI.of hq hx⟩

/-- A pending landing of `I` at a state of `exeE`, `endE`, relabelled. -/
theorem pendA_relab {lbl lsize s c fs} (hs : s.exe = exeE ∧ s.endPc = endE)
    (h : PendA p I lbl lsize s c fs) : PendA p (relabI exeE exeF endE endF I) lbl lsize (relab exeF endF s) c fs :=
  let ⟨c', fs', hr, hx⟩ := h.2
  ⟨h.1, c', fs', hr, relabI.of hs hx⟩

/-- **The counter's add along the relabelling.** -/
theorem ctrRow_relab (hO : TailOK exeE exeF endE endF B) (hown : ∀ s fs, own' (relab exeF endF s) fs = own s fs)
    {s0 : State} (hs0 : s0.exe = exeE ∧ s0.endPc = endE) {i z} (hc : CellAt s0 (.instr i) z) {lbl lsize fs c}
    (h : CtrRow (msOfA Λ μ rd G own ar I lbl lsize fs) (fun s' c' => PendA p I lbl lsize s' c' fs) s0 c) :
    CtrRow (msOfA Λ μ rd G own' ar (relabI exeE exeF endE endF I) lbl lsize fs)
      (fun s' c' => PendA p (relabI exeE exeF endE endF I) lbl lsize s' c' fs) (relab exeF endF s0) c := by
  obtain ⟨k, op, g, x, τ, e, n, he, hrt, hmp, hsite, hhold, hop, hG⟩ := h
  have he' : exec s0 = _ := he
  have hl := leaves_keep he'
  refine ⟨k, op, relab exeF endF ∘ g, x, τ, e, n, ?_, hrt, hmp, hsite, hhold, hop, fun old hGo hw hle hlo => ?_⟩
  · show exec _ = _
    rw [hO.exec hs0 hc, he']
    rfl
  · obtain ⟨hG', hX⟩ := hG old hGo (fun w hw' => hw w (by
      show _ ∈ own' (relab exeF endF s0) fs
      rw [hown]; exact hw')) hle hlo
    have hq := hl old
    exact ⟨hG', pendA_relab ⟨hq.1.trans hs0.1, hq.2.trans hs0.2⟩ hX⟩

/-- **The box's initialising store along the relabelling.** -/
theorem newStM_relab (hO : TailOK exeE exeF endE endF B) {s0 : State} (hs0 : s0.exe = exeE ∧ s0.endPc = endE)
    {i z} (hc : CellAt s0 (.instr i) z) {lbl lsize fs c}
    (h : Spike.Lib.NewStM p lbl (msOfA Λ μ rd G own ar I lbl lsize fs) s0 c) :
    Spike.Lib.NewStM p lbl (msOfA Λ μ rd G own' ar (relabI exeE exeF endE endF I) lbl lsize fs)
      (relab exeF endF s0) c := by
  obtain ⟨kr, A, V, s', x, a, ty, e, w, wold, old, hN', he, hmp, hT', hev, hacc, hv, hh, hnum, hA, hle, hxa⟩ := h
  have he' : exec s0 = _ := he
  have hl := leaves_keep he' true
  have hq : s'.exe = exeE ∧ s'.endPc = endE := ⟨hl.1.trans hs0.1, hl.2.trans hs0.2⟩
  refine ⟨kr, A, V, relab exeF endF s', x, a, ty, e, w, wold, old, hN', ?_, hmp, hT', hev, hacc, hv, hh, hnum,
    hA, hle, fun l hl' => ⟨(hxa l hl').1, relabI.of hq (hxa l hl').2⟩⟩
  show exec _ = _
  rw [hO.exec hs0 hc, he']
  rfl

/-- **The node obligations along the relabelling**, the owned words `own'`
of the relabelled states read back through it as `own` (`hown`), the system
calls without a row (`Cl`) read through it back. -/
theorem nodesA_tail_own (hO : TailOK exeE exeF endE endF B) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakePathS Λ p μ I rS Tk) (hown : ∀ s fs, own' (relab exeF endF s) fs = own s fs) :
    NodesA Λ p μ rd G own' ar (relabI exeE exeF endE endF I) (ab.map (· ∘ relab exeE endE))
      (Cl ∘ relab exeE endE) where
  out lbl lsize s c fs hI hpc hcl := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    have hk := hO.abi hs0 hc
    have hcl0 : abi.atSys s0 = true → ¬ Cl s0 := fun h => by
      have h' := hcl (by rw [hk.1]; exact h)
      rwa [comp_relab hs0] at h'
    rcases hN.out lbl lsize s0 c fs hI0 hpc hcl0 with h | ⟨hns, hpub, c₁, hps, hi, h⟩
    · exact .inl (outS_relab hO hown hs0 hc h)
    · exact .inr ⟨by rw [hk.1]; exact hns, hpub, c₁, hps, relabI.of hs0 hi, outS_relab hO hown hs0 hc h⟩
  noRet lbl lsize s c hI := hN.noRet lbl lsize _ c hI.2.2
  cell lbl lsize s c fs hI := hN.cell lbl lsize _ c fs (irun_back hI)
  noSite lbl lsize s c fs hI := by
    obtain ⟨s0, -, rfl, hI0⟩ := relabI.elim hI
    exact hN.noSite lbl lsize s0 c fs hI0
  mapped lbl lsize s c fs hI hsys e he := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    obtain ⟨t0, ht0, rfl, -⟩ := hO.tree hs0 hc he
    rw [(hO.abi hs0 hc).1] at hsys
    exact fun h => hN.mapped lbl lsize s0 c fs hI0 hsys t0 ht0 ((Spike.Lib.TreeMap.touches_map _ t0).1 h)
  place lbl lsize s c fs hI := by
    obtain ⟨s0, -, rfl, hI0⟩ := relabI.elim hI
    exact hN.place lbl lsize s0 c fs hI0
  svc lbl lsize s c fs hI hsys := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    rw [(hO.abi hs0 hc).1] at hsys
    obtain ⟨sz, h⟩ := hN.svc lbl lsize s0 c fs hI0 hsys
    exact ⟨sz, hO.cell _ _ _ hs0.1 hs0.2 h⟩
  ownRun lbl lsize s c fs c' fs' hr hI := by
    have hs : s.exe = exeF ∧ s.endPc = endF := hI.elim (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)
    rw [← relab_relab (exe' := exeE) (endPc' := endE) hs.1 hs.2]; simp only [hown]
    exact hN.ownRun lbl lsize _ c fs c' fs' hr (hI.imp (·.2.2) (·.2.2))
  ownInstr lbl lsize s c fs hI hsys tree he := by
    obtain ⟨s0, hs0, rfl, hI0, c₀, fs₀, hI1⟩ := irun_elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI1 (hs0.1 ▸ hO.valid)
    obtain ⟨t0, ht0, rfl, -⟩ := hO.tree hs0 hc he
    rw [(hO.abi hs0 hc).1] at hsys
    rw [hown]
    exact Spike.Lib.TreeMap.ownTree_map _ (fun x => hown x fs) (hN.ownInstr lbl lsize s0 c fs hI0 hsys t0 ht0)
  ownSys lbl lsize s c fs hI hsys call hd s' hs' := by
    obtain ⟨s0, hs0, rfl, hI0, c₀, fs₀, hI1⟩ := irun_elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI1 (hs0.1 ▸ hO.valid)
    have hk := hO.abi hs0 hc
    rw [hk.1] at hsys
    rw [hk.2.1, hk.2.2.1] at hd
    rw [hk.2.2.2.2 call] at hs'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs'
    simp only [hown]
    exact hN.ownSys lbl lsize s0 c fs hI0 hsys call hd x hx
  ownTake lbl lsize s c fs hI a hμ hpc m := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    rw [skip_relab hc (hO.cell _ _ _ hs0.1 hs0.2 hc)]; simp only [hown]
    exact (hown _ fs).trans (hN.ownTake lbl lsize s0 c fs hI0 a hμ hpc m)
  ctrRow lbl lsize s c fs hI hsys t mem outs o ht hs ho hw := by
    obtain ⟨s0, hs0, rfl, hI0, c₀, fs₀, hI1⟩ := irun_elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI1 (hs0.1 ▸ hO.valid)
    rw [(hO.abi hs0 hc).1] at hsys
    obtain ⟨outs0, o0, hs0', ho0, rfl⟩ := hO.step _ hs0 hc ht hs ho
    exact ctrRow_relab hO hown hs0 hc (hN.ctrRow lbl lsize s0 c fs hI0 hsys _ mem outs0 o0 rfl hs0' ho0 hw)
  arena lbl lsize s c fs hI hsys t mem outs o L ht hs ho hw := by
    obtain ⟨s0, hs0, rfl, hI0, c₀, fs₀, hI1⟩ := irun_elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI1 (hs0.1 ▸ hO.valid)
    rw [(hO.abi hs0 hc).1] at hsys
    obtain ⟨outs0, o0, hs0', ho0, rfl⟩ := hO.step _ hs0 hc ht hs ho
    exact (hN.arena lbl lsize s0 c fs hI0 hsys _ mem outs0 o0 L rfl hs0' ho0 hw).imp id (newStM_relab hO hs0 hc)
  zero lbl lsize s c fs hI := hN.zero lbl lsize _ c fs (irun_back hI)

/-- **The node obligations along the relabelling**, the owned words read
through it (`hown`), the system calls without a row (`Cl`) read through it
back (`nodesA_tail_own` at one `own`). -/
theorem nodesA_tail (hO : TailOK exeE exeF endE endF B) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakePathS Λ p μ I rS Tk) (hown : ∀ s fs, own (relab exeF endF s) fs = own s fs) :
    NodesA Λ p μ rd G own ar (relabI exeE exeF endE endF I) (ab.map (· ∘ relab exeE endE))
      (Cl ∘ relab exeE endE) :=
  nodesA_tail_own hO hN hT hown

end Spike.Lib.X64NodesTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64NodesTail.instr_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64NodesTail.instr_of_nodes

/-- info: 'Spike.Lib.X64NodesTail.takePathS_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64NodesTail.takePathS_tail

/-- info: 'Spike.Lib.X64NodesTail.abortPathS_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64NodesTail.abortPathS_tail

/-- info: 'Spike.Lib.X64NodesTail.nodesA_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64NodesTail.nodesA_tail

/-- info: 'Spike.Lib.X64NodesTail.nodesA_tail_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64NodesTail.nodesA_tail_own
