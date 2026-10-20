/-
**Helpers for whole-image AArch64 theorems over
masks.** Generic statements (the copies in `EnvG/A64SpscWhole*`, `EnvG/A64WholeTreiber*` and
`EnvG/A64WholeRelay*` are left as they are):

- `dirs_phase1F_any p`: every cell of the program `p` is phase-1 with failing
  release RMWs, for every ambient executable (`dirs_phase1F`'s script with
  an `∀ e` binder);
- `label_dirPhase1F_any`, `byteArray_dirPhase1F_any`: label and data cells;
- `phase1TreeF_maskKeep_range`: a range mask of such an image is phase-1
  (only its kept cells, labels and empty data cells remain);
- `label_addrOf_succ_maskKeep`: the address of the exit label at cell `i` is
  the mask's address of cell `i + 1` (the label cell has size `0`), where a
  masked data cell halts the thread (`not_instrStepEnv_of_byteArray`);
- `label_addrOf_succ_label`: two adjacent labels share their address (a
  thread's entry label in the runner, and its text's first label);
- `RelPureSpec.toEnd`: the purity specification of a thread running an
  executable to an end address (the image, from the thread's entry label).

The plain-shape family beside the `F` one: `dirs_phase1_any`,
`label_dirPhase1_any`, `byteArray_dirPhase1_any`, `phase1Tree_maskKeep_range`
(the copies in `EnvG/A64SpscWholePublic.lean`, `EnvG/A64WholeRelayPublic.lean`
and `EnvG/A64WholeTreiberPublic.lean` are now their instances).
-/
import Kraken.Promising.SLR.EnvG.A64MaskCore
import Kraken.Promising.SLR.EnvG.A64MaskCfg
import Kraken.Promising.SLR.EnvG.A64RmwFail
import Kraken.Promising.SLR.EnvG.RelPureEnvA64

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

set_option hygiene false in
/-- `dirs_phase1F_any p` proves `∀ d ∈ p, ∀ e z, DirPhase1F e d z` for a
program `p` (a definition) whose instructions make at most one access,
deterministically (`dirs_phase1F`'s script, for every ambient
executable). -/
macro "dirs_phase1F_any " p:ident : tactic => `(tactic| (
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.loadK, _root_.MachineData.storeK, _root_.MachineData.rmwK,
    _root_.MachineData.setRegOrZr, _root_.MachineData.setRegOrSp, _root_.RegOrSp.interpBase,
    _root_.AddrExpr.checkSPAlignment, _root_.AddrExpr.interpLoad, _root_.AddrExpr.interpStore,
    _root_.UnscaledAddrExpr.interpStore,
    _root_.UnscaledAddrExpr.checkSPAlignment, _root_.UnscaledAddrExpr.interpLoad,
    _root_.Literal.interpLoad, _root_.AddrOrLit.interpLoad,
    Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))))

/-- A label cell is phase-1 with failing release RMWs. -/
theorem label_dirPhase1F_any (l : Label) (e : _root_.Executable) (z : Nat) : DirPhase1F e (.label l) z := by
  intro s pc
  simp [_root_.Directive.interp, Kraken.Promising.AArch64.toEv, Phase1ShapeF, DetAccess, SingleAccessS2,
    AccessFree, Kraken.Promising.EvTree.access_empty]

/-- A data cell is phase-1 with failing release RMWs (its tree is a
fault). -/
theorem byteArray_dirPhase1F_any (b : ByteArray) (e : _root_.Executable) (z : Nat) :
    DirPhase1F e (.byteArray b) z := by
  intro s pc
  simp [_root_.Directive.interp, Kraken.Promising.AArch64.toEv, Phase1ShapeF, DetAccess, SingleAccessS2,
    AccessFree, Kraken.Promising.EvTree.access_empty]

/-- **A range mask of a phase-1 image is phase-1** (failing release RMWs). -/
theorem phase1TreeF_maskKeep_range [layout : _root_.Layout] {p : Program} [Executable.ValidLayout (layout p)]
    {lo hi : Nat} (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase1F e d z) :
    Phase1TreeF (layout (p.maskKeep (keepRange lo hi))) :=
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange lo hi) p)
  phase1TreeF_of_dirs (dirsPhase1F_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1F e d z)
    (fun d hd => h d (List.mem_of_mem_drop (List.mem_of_mem_take hd)))
    (fun l => label_dirPhase1F_any l) (byteArray_dirPhase1F_any _)))

set_option hygiene false in
/-- `dirs_phase1_any p` proves `∀ d ∈ p, ∀ e z, DirPhase1 A e d z` for a
program `p` (a definition) whose instructions make at most one access,
deterministically, with no release-kind RMW (`dirs_phase1`'s script, for
every ambient executable). (The shared copy of the whole-image
scripts `SpscA.spscImageA_dirsPhase1` and `Relay.relay3Img_dirsPhase1`.) -/
macro "dirs_phase1_any " p:ident : tactic => `(tactic| (
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.loadK, _root_.MachineData.storeK, _root_.MachineData.rmwK,
    _root_.MachineData.setRegOrZr, _root_.MachineData.setRegOrSp, _root_.RegOrSp.interpBase,
    _root_.AddrExpr.checkSPAlignment, _root_.AddrExpr.interpLoad, _root_.AddrExpr.interpStore,
    _root_.UnscaledAddrExpr.interpStore,
    _root_.UnscaledAddrExpr.checkSPAlignment, _root_.UnscaledAddrExpr.interpLoad,
    _root_.Literal.interpLoad, _root_.AddrOrLit.interpLoad,
    Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape, Kraken.Promising.SLR.EnvG.DetAccess,
      Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
      Kraken.Promising.EvTree.access_empty]))))

/-- A label cell is phase-1 (plain shape, any architecture). -/
theorem label_dirPhase1_any (A : Arch) (l : Label) (e : _root_.Executable) (z : Nat) :
    DirPhase1 A e (.label l) z := by
  intro s pc
  simp [_root_.Directive.interp, Kraken.Promising.AArch64.toEv, Phase1Shape, DetAccess, SingleAccessS,
    AccessFree, Kraken.Promising.EvTree.access_empty]

/-- A data cell is phase-1 (plain shape, any architecture; its tree is a
fault). -/
theorem byteArray_dirPhase1_any (A : Arch) (b : ByteArray) (e : _root_.Executable) (z : Nat) :
    DirPhase1 A e (.byteArray b) z := by
  intro s pc
  simp [_root_.Directive.interp, Kraken.Promising.AArch64.toEv, Phase1Shape, DetAccess, SingleAccessS,
    AccessFree, Kraken.Promising.EvTree.access_empty]

/-- **A range mask of a phase-1 image is phase-1** (plain shape). -/
theorem phase1Tree_maskKeep_range [layout : _root_.Layout] {A : Arch} {p : Program}
    [Executable.ValidLayout (layout p)] {lo hi : Nat}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase1 A e d z) :
    Phase1Tree A (layout (p.maskKeep (keepRange lo hi))) :=
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange lo hi) p)
  phase1Tree_of_dirs (dirsPhase1_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1 A e d z)
    (fun d hd => h d (List.mem_of_mem_drop (List.mem_of_mem_take hd)))
    (fun l => label_dirPhase1_any A l) (byteArray_dirPhase1_any A _)))

/-- The layout's cell `i` of a program is the program's cell `i` with its
size. -/
theorem layout_getElem? [layout : _root_.Layout] {p : Program} {i : Nat} {d : Directive} (hi : p[i]? = some d) :
    (layout p).2[i]? = some (d, Kraken.Layout.size Directive i) := by
  simp [Layout.apply_snd, Layout.frag, hi]

/-- **The label at cell `i` is at the address of cell `i + 1`** (a label
cell has size `0`). -/
theorem label_addrOf_succ [layout : _root_.Layout] {p : Program} [Executable.ValidLayout (layout p)]
    {i : Nat} {x : Label} (hnd : (Program.labels p).Nodup) (hdrop : p.drop i = Program.fromLabel p x)
    (hne : Program.fromLabel p x ≠ []) (hi : p[i]? = some (.label x)) :
    (_root_.Executable.labels (layout p)).label x = (layout p).addrOf (i + 1) := by
  have hc := layout_getElem? (layout := layout) hi
  rw [Executable.addrOf_succ _ hc, Executable.ValidLayout.label_size i x _ hc,
    Program.label_addrOf_drop hnd hdrop hne]
  simp

/-- **The exit label at cell `i`, in a mask**: its address is the mask's
address of cell `i + 1`. -/
theorem label_addrOf_succ_maskKeep [layout : _root_.Layout] {p : Program} [Executable.ValidLayout (layout p)]
    (keep : Nat → Bool) {i : Nat} {x : Label} (hnd : (Program.labels p).Nodup)
    (hdrop : p.drop i = Program.fromLabel p x) (hne : Program.fromLabel p x ≠ []) (hi : p[i]? = some (.label x)) :
    (_root_.Executable.labels (layout p)).label x = (layout (p.maskKeep keep)).addrOf (i + 1) := by
  rw [addrOf_mask (maskOf_layout keep p), label_addrOf_succ hnd hdrop hne hi]

/-- **Adjacent labels share their address**: the label `x` at cell `i`
and the label `y` at cell `i + 1`. -/
theorem label_addrOf_succ_label [layout : _root_.Layout] {p : Program} [Executable.ValidLayout (layout p)]
    {i : Nat} {x y : Label} (hnd : (Program.labels p).Nodup) (hdrop : p.drop i = Program.fromLabel p x)
    (hne : Program.fromLabel p x ≠ []) (hi : p[i]? = some (.label x))
    (hdrop' : p.drop (i + 1) = Program.fromLabel p y) (hne' : Program.fromLabel p y ≠ []) :
    (_root_.Executable.labels (layout p)).label x = (_root_.Executable.labels (layout p)).label y := by
  rw [label_addrOf_succ hnd hdrop hne hi, Program.label_addrOf_drop hnd hdrop' hne']

/-- **A run over a mask, at the image's labels**: the mask has the image's
labels (`labels_mask`). -/
theorem Safely.atImageLabels {e e' : Kraken.Executable Directive} (hm : MaskOf e e') {env : SharedEnv}
    {Q : MachineState × env.State → Prop} {lx l₀ : Label} {s : MachineData} {g : env.State}
    (h : Safely (e'.instrStepEnv env) (fun x => (x.1.2 = (_root_.Executable.labels e').label lx ∧ Q x) ∨ False)
      ((s, (_root_.Executable.labels e').label l₀), g)) :
    Safely (e'.instrStepEnv env) (fun x => (x.1.2 = (_root_.Executable.labels e).label lx ∧ Q x) ∨ False)
      ((s, (_root_.Executable.labels e).label l₀), g) := by
  rwa [labels_mask hm] at h

/-- **The purity specification of a thread running `e` to `endPc`** (a
whole image; the `Safely` judgment's postcondition is the end address, the
counter of a counted run projected away). -/
def RelPureSpec.toEnd {A : Arch} {rel : Loc → Pred} (e : Kraken.Executable Directive)
    [hv : Kraken.Executable.ValidLayout e] (endPc : Int64) : RelPureSpec A rel where
  e := e
  valid := hv
  endPc := endPc
  post := fun x => ∃ _ : Nat, (x.1.2 = endPc ∧ True) ∨ False
  post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.AArch64.EnvG.phase1TreeF_maskKeep_range
#print axioms Kraken.Promising.AArch64.EnvG.label_addrOf_succ_maskKeep
#print axioms Kraken.Promising.AArch64.EnvG.label_addrOf_succ_label
