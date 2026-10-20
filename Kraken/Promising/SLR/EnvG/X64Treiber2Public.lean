/-
**Part 9: the x64 two-thread Treiber stack
`treiber2.kl`, verbatim, end to end** (on the adjacency environment
`EnvGCAdjX`): `x64_treiber2_envG_verbatim`, the `.kl`'s property
`(0:r12=n1 ∧ 1:r12=n2) ∨ (0:r12=n2 ∧ 1:r12=n1)` at every final configuration
reachable under `Arch.tso`, for the `.kl`'s `code` block as written, run by
both threads in the runner's image `treiber2ImageV` (the code, then the data
trailer `top`, `n1`, `n2`), over every valid layout of the image.

- **Parameters** (`tPV`): `top = symT2 "top"`, node `w` at `symT2 "n1"` /
  `symT2 "n2"` (link at offset `0`). `TLocs` from the symbols' distinctness
  and non-nullness (`tLocs_tPV`; the concrete instance discharges them by
  `decide`).
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFCAdjX` (`EnvG/X64AdjLink.lean`) at
  the whole image with `S := sAll`: both threads' exit label `done` is
  followed by the data trailer (`workerV_stuck`), the image is phase-1
  (`treiber2ImageV_phase1FX`); no-fault from the code cells
  (`noFault_QX64CAdjCode`, the data cells never run).
- **Shared postcondition** (`TB2X`) and `hB`: the Treiber node proof's (`DoneR` of some
  thread on the resource), with `r12`.
- **Assembly**: `CmpxPublic.final_of_relPureSafelyQX_tsoF'`, purity from
  `workerV_noNT`, initial erasure `erase_init`, `acq_pair_false`,
  `final_values` (`EnvG/X64Treiber2Final.lean`).

Start predicates fix only what the runner sets: the image, no declarations,
the entry and exit labels, the registers the `.kl` sets (`0:rbx=n1;
1:rbx=n2`), and an empty private memory. Not covered (as for
`x64_treiber_pp_envG_verbatim`): the runner's declarations (`decls = {}`),
final configurations only.
-/
import Kraken.Promising.SLR.EnvG.X64Treiber2VCGen
import Kraken.Promising.SLR.EnvG.X64TreiberAbsPublic

namespace Kraken.Promising.X64.EnvG.Treiber2X

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (initVal_eq)
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 mem_sAll8 split_sAll)

/-! ## Fault-freedom from the code cells -/

section NoFault

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **Every tree from a `QX64CAdj`-state is fault-free** when the code cells
are (`noFault_QX64CAdj` with `DirsNoFaultCode`: a step is never at a data
cell). -/
theorem noFault_QX64CAdjCode (hnf : DirsNoFaultCode e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64CAdj A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec_step he hds hnf hR tree hex

end NoFault

/-! ## Parameters and the shared postcondition -/

/-- Thread `w` is done on the resource `r`: its `r12` and `DoneR`. -/
def FFX (P : Params) (w : Nat) (c : Config isa) (r : Res) : Prop :=
  ∃ th, c.threads[w]? = some th ∧ DoneR P w c.mem r (th.st.st.1.regs.get64 .r12)

/-- **The shared postcondition**: some thread done on the resource. -/
def TB2X (P : Params) (c : Config isa) (r : Res) (_ : Ghost) : Prop := ∃ w, w < 2 ∧ FFX P w c r

/-- **The `.kl`'s property**: the threads popped the two nodes. -/
def Treiber2FinalX (n1 n2 : BitVec 64) (c : Config isa) : Prop :=
  ∃ th0 th1, c.threads[0]? = some th0 ∧ c.threads[1]? = some th1 ∧
    ((th0.st.st.1.regs.get64 .r12 = n1 ∧ th1.st.st.1.regs.get64 .r12 = n2) ∨
      (th0.st.st.1.regs.get64 .r12 = n2 ∧ th1.st.st.1.regs.get64 .r12 = n1))

/-- **`Pu` at the start** (`top` initially `0`). -/
theorem pu_init (P : Params) (hL : TLocs P) {w : Nat} (hw : w < 2) (c : Config isa)
    (hT0 : c.mem.initVal P.top = 0) : Pu P w (σInitX c (thrRes c.mem P w) (ghost₀ P)) := by
  have htn := hL.top_nd' hw
  have htp := top_pt P w
  have hq : ∀ x, ((σInitX c (thrRes c.mem P w) (ghost₀ P)).r.wr x).q = frac P w x := fun _ => rfl
  have hX : ∀ x p, ((σInitX c (thrRes c.mem P w) (ghost₀ P)).r.wr x).X p ↔
      0 < frac P w x ∧ p = (c.mem.initVal x, 0) := fun _ _ => Iff.rfl
  refine ⟨⟨ghost₀_gw P, ?_, ?_, hT0, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hq]; simp only [frac, ↓reduceIte]; grind
  · show 1 ≤ (if P.top = P.top ∧ w = w then 1 else 0); simp
  · intro f hf; simp [σInitX, Views.getFwd] at hf
  · rintro ⟨p, hp, hne⟩
    exact hne (by rw [((hX _ _).mp hp).2])
  · rw [hq]; simp [frac, Ne.symm htn]
  · intro p hp
    rw [((hX _ _).mp hp).2]; exact Nat.zero_le _
  · rw [hq]; simp [frac, Ne.symm htp]

variable [layout : _root_.Layout]

/-- **The parameters of `treiber2.kl`** in the image: `top`, and node `w`
at `n1` (thread `0`) or `n2` (thread `1`). -/
def tPV : Params := ⟨symT2 "top", fun w => if w = 0 then symT2 "n1" else symT2 "n2"⟩

theorem tLocs_tPV (h1 : symT2 "top" ≠ symT2 "n1") (h2 : symT2 "top" ≠ symT2 "n2") (hn : symT2 "n1" ≠ symT2 "n2")
    (hn1 : symT2 "n1" ≠ 0) (hn2 : symT2 "n2" ≠ 0) : TLocs tPV where
  top_nd w hw := by
    rcases w with _ | _ | w
    · exact h1
    · exact h2
    · omega
  n_ne := hn
  n_nz w hw := by
    rcases w with _ | _ | w
    · exact hn1
    · exact hn2
    · omega

variable [Executable.ValidLayout (layout treiber2ImageV)]

/-! ## Shapes, halts and fault-freedom of the image -/

omit layout [Executable.ValidLayout (layout treiber2ImageV)] in
/-- The image's cells are phase-1 (the x64 Treiber proof's popper script). -/
theorem treiber2ImageV_dirsPhase1FX : ∀ d ∈ treiber2ImageV, ∀ (e : _root_.Executable) z, DirPhase1FX e d z := by
  intro d hd e z s pc
  simp only [treiber2ImageV, treiber2CodeV, treiber2DataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  cells_phase1FX

/-- **The whole image is phase-1.** -/
theorem treiber2ImageV_phase1FX : Phase1TreeFX (layout treiber2ImageV) :=
  phase1TreeFX_of_dirs (dirsPhase1FX_layout treiber2ImageV_dirsPhase1FX)

omit [Executable.ValidLayout (layout treiber2ImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem treiber2ImageV_noFaultCode : DirsNoFaultCode (layout treiber2ImageV) := by
  dirs_no_fault_code treiber2ImageV treiber2CodeV treiber2DataV

/-- `done`'s address is the trailer's first data cell. -/
theorem labT2_done : labT2 "done" = (layout treiber2ImageV).addrOf 16 := by
  have hd : labT2 "done" = (layout treiber2ImageV).addrOf 15 :=
    Program.label_addrOf_drop treiber2ImageV_wf.nodup (by decide) (by decide)
  have h15 : (layout treiber2ImageV).2[15]? = some (Directive.label "done", Kraken.Layout.size Directive 15) := by
    simp [Layout.apply_snd, Layout.frag, treiber2ImageV, treiber2CodeV, treiber2DataV]
  rw [Executable.addrOf_succ _ h15, Executable.ValidLayout.label_size 15 "done" _ h15, hd]
  simp

/-- **No instruction steps at the exit label `done`.** -/
theorem workerV_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labT2 "done" → ¬ (layout treiber2ImageV).instrStepEnv env x R := by
  rw [labT2_done]
  exact not_instrStepEnv_of_byteArray (i := 16) (b := .mk #[]) env (by decide)

/-! ## The rules -/

/-- Thread `w`'s postcondition: the exit label and `Dn`. -/
abbrev postWV (P : Params) (w : Nat) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labT2 "done" ∧ Dn P w (x.1.1.regs.get64 .r12) x.2) ∨ False

omit [Executable.ValidLayout (layout treiber2ImageV)] in
theorem postWV_end (P : Params) (w : Nat) : ∀ y, postWV P w y → y.1.2 = labT2 "done" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout treiber2ImageV)] in
/-- **`hB` for thread `w`**: `Dn` at the anchor gives `DoneR` at the
configuration (the Treiber node proof's `hB_w`, `r12`). -/
theorem hB_wV (P : Params) {w : Nat} (hw : w < 2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postWV P w (t.st.st, σ) → t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2X P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePop.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

/-- **Thread `w`'s rule** (layout `sAll`, the whole image). -/
noncomputable def wRuleV (P : Params) (w : Nat) (hw : w < 2) : ThreadRuleRXF (I := isa) Arch.tso (TB2X P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjX (S := sAll) (post := postWV P w) (plan_valid P w) sAll_le16
    treiber2ImageV_phase1FX (postWV_end P w) (workerV_stuck _) (hB_wV P hw)

/-- **Thread `w`'s rule excludes faults** (unconditional in promises). -/
theorem wRuleV_noFault (P : Params) (w : Nat) (hw : w < 2) : NoFaultRuleF (wRuleV P w hw) := by
  unfold wRuleV ThreadRuleRXF.ofSafelyEnvGFCAdjX
  exact noFaultRuleF_ofEnvGFCAdj_struct _ _ (noFault_QX64CAdjCode treiber2ImageV_noFaultCode (postWV_end P w))

/-! ## The start -/

/-- **Thread `w` at its start**, as the runner sets it up: the image, no
declarations, pc at `worker`, end at `done`, the `.kl`'s `rbx` (`n`), and an
empty private memory. -/
structure StartWV (n : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout treiber2ImageV
  decls : s.decls = {}
  pc : s.st.2 = labT2 "worker"
  endPc : s.endPc = labT2 "done"
  rbx : s.st.1.regs.get64 .rbx = n
  dmem : ∀ k, s.st.1.dmem.get? k = none

omit [Executable.ValidLayout (layout treiber2ImageV)] in
theorem StartWV.d8 {n : BitVec 64} {s : State} (h : StartWV n s) : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none :=
  fun a => (split_sAll h.dmem).loadInt_none (mem_sAll8 a) (by decide) (by decide)

section Start

variable {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **Thread `w`'s initial invariant.** -/
theorem invWV_init (hL : TLocs tPV) {w : Nat} (hw : w < 2) {s : isa.State} (hs : [s0, s1][w]? = some s)
    (hS : StartWV (tPV.n w) s) (hT0 : (Config.init [s0, s1] initMem).mem.initVal tPV.top = 0) :
    (wRuleV tPV w hw).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem tPV w)
      (ghost₀ tPV) := by
  have htr : tRes (Config.init [s0, s1] initMem).mem tPV w = thrRes (Config.init [s0, s1] initMem).mem tPV w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  have hst : s.st = (s.st.1, labT2 "worker") := Prod.ext rfl hS.pc
  refine invGFCAdjX_init (s := s) hs rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (workerV_envGCAdj tPV w hL hw rfl s.st.1 (_, 0)
    ⟨hS.rbx, hS.d8, pu_init tPV hL hw _ hT0⟩)

end Start

/-! ## Purity -/

/-- The threads' all-release specifications (the image). -/
noncomputable def treiber2NoNTSpecV : Nat → RelPureSpecQX Arch.tso fun _ _ => False := fun _ =>
  { S := sAll
    le16 := sAll_le16
    e := layout treiber2ImageV
    valid := inferInstance
    endPc := labT2 "done"
    post := fun x => ∃ _ : Nat, (x.1.2 = labT2 "done" ∧ True) ∨ False
    post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

/-- **The all-release specifications hold at the start states.** -/
theorem treiber2NoNTSpecV_init {s0 s1 : State} (h0 : StartWV (tPV.n 0) s0) (h1 : StartWV (tPV.n 1) s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (treiber2NoNTSpecV tid).Holds s := by
  have H : ∀ {n : BitVec 64} {s : State}, StartWV n s → (treiber2NoNTSpecV 0).Holds s := fun {_ s} hS => by
    refine ⟨hS.exe, hS.endPc, hS.decls, split_sAll hS.dmem, ?_⟩
    rw [show s.st = (s.st.1, labT2 "worker") from Prod.ext rfl hS.pc]
    exact TreiberAbs.Safely.uncountT (workerV_noNT _ ((), 0) hS.d8)
  intro tid s hs
  rcases tid with _ | _ | i
  · cases hs; exact H h0
  · cases hs; exact H h1
  · simp at hs

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for the verbatim `treiber2`.** -/
theorem treiber2V_npSafeF (hL : TLocs tPV) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWV (tPV.n 0) s0) (h1 : StartWV (tPV.n 1) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal tPV.top = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.tso (TB2X tPV) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem tPV tid) (ghost₀ tPV) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invWV_init hL (by decide) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invWV_init hL (by decide) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The two-thread Treiber stack `LockFree/X64/treiber2.kl` for x64 under
`Arch.tso`, the `.kl`'s code verbatim**: for every valid layout of the image
`treiber2ImageV` (the `code` block, then the runner's data trailer placing
`top`, `n1`, `n2`) in which the symbols `top`, `n1`, `n2` have distinct
addresses and the nodes are non-null, if thread `0` starts at `worker` with
end `done`, `%rbx = n1` and an empty private memory, thread `1` likewise with
`%rbx = n2` (`StartWV`), and `top` is initially `0`, then every final
configuration reachable under `Arch.tso` has
`(0:r12 = n1 ∧ 1:r12 = n2) ∨ (0:r12 = n2 ∧ 1:r12 = n1)` (the `.kl`'s
`forall`). -/
theorem x64_treiber2_envG_verbatim {fuel : Nat} (h1 : symT2 "top" ≠ symT2 "n1") (h2 : symT2 "top" ≠ symT2 "n2")
    (hn : symT2 "n1" ≠ symT2 "n2") (hn1 : symT2 "n1" ≠ 0) (hn2 : symT2 "n2" ≠ 0) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartWV (symT2 "n1") s0) (h1' : StartWV (symT2 "n2") s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symT2 "top", 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th0 th1, cfg.threads[0]? = some th0 ∧ cfg.threads[1]? = some th1 ∧
      ((th0.st.st.1.regs.get64 .r12 = symT2 "n1" ∧ th1.st.st.1.regs.get64 .r12 = symT2 "n2") ∨
        (th0.st.st.1.regs.get64 .r12 = symT2 "n2" ∧ th1.st.st.1.regs.get64 .r12 = symT2 "n1")) := by
  have hL := tLocs_tPV h1 h2 hn hn1 hn2
  refine CmpxPublic.final_of_relPureSafelyQX_tsoF' (B := TB2X tPV) (Φ := Treiber2FinalX (symT2 "n1") (symT2 "n2"))
    (erase_init hL _) (ghost₀_pend _) treiber2NoNTSpecV (treiber2NoNTSpecV_init h0 h1')
    (treiber2V_npSafeF hL h0 h1' hT0) hc hf fun rF' g' E' hle hsize hB => ?_
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw tPV).mono hle
  have hno := Config.final_not_outstanding hf
  obtain ⟨w0, hw0, th, hth, hd0⟩ := hB 0 (Config.final_done hf hi0)
  obtain ⟨w1, hw1, th', hth', hd1⟩ := hB 1 (Config.final_done hf hi1)
  by_cases hww : w0 = w1
  · subst hww
    exact (TreiberCommon.acq_pair_false E' hi0 hi1 (by decide) hd0.1 hd1.1).elim
  rcases w0 with _ | _ | w0
  · rcases w1 with _ | _ | w1
    · exact absurd rfl hww
    · exact ⟨th, th', hth, hth', final_values E' hW hL hno hi0 hi1 hd0 hd1⟩
    · omega
  · rcases w1 with _ | _ | w1
    · have := final_values E' hW hL hno hi1 hi0 hd1 hd0
      exact ⟨th', th, hth', hth, this⟩
    · exact absurd rfl hww
    · omega
  · omega

end Kraken.Promising.X64.EnvG.Treiber2X

#print axioms Kraken.Promising.X64.EnvG.Treiber2X.x64_treiber2_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.Treiber2X.wRuleV_noFault
