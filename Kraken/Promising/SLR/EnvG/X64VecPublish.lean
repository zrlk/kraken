/-
**`publish_movdqa.kl` verbatim: a 16-byte record published by `movdqa` is
never torn**.

The `code` block of `Kraken/Examples/LockFree/X64/publish_movdqa.kl` as
written (`publishCodeV`), run by both threads in its image `publishImageV`
(the code, then the runner's data trailer `publishDataV`): thread `0` from
`writer` to `done` stores `xmm0`, then `xmm1`, to `(rec)` with `movdqa`;
thread `1` from `reader` to `done` loads `(rec)` into `xmm2` with `movdqa`.

**Route: the invariant environment** (`SharedEnv.inv S G`,
`Kraken/Promising/InvLinkX64.lean`), not EnvG. The claim is a value-set
property: every write to the 16-byte location `⟨rec, 16⟩` is `v1` or `v2`,
so every read returns `0`, `v1` or `v2` (Kang et al.'s write invariant,
`write_invariant`, which covers promises too). That needs one invariant,
`pubG`, and no plan, ghost state or phase-1 shape. `movdqa` is one atomic
16-byte access (`AvxOperation.interp`, `atomic := w == .W128`), which is
the whole content of "never torn": a non-atomic 16-byte access would be two
8-byte events at `⟨rec, 8⟩` and `⟨rec + 8, 8⟩`, which `S` does not contain.

**Declarations.** The runner's threads carry `decls = {⟨rec, 16⟩}`
(the `.kl` types `rec` as `__int128`). The theorem allows any declarations
`ds` under which a 16-byte access at `rec` is its own footprint
(`ds.AgreesAt rec 16`), which covers both `{}` and the runner's, through
`X64VecDecls` (`ThreadSpec.HoldsD`, `inv_reachableD`): every cell of the
image accesses only `(rec)` at 16 bytes (`publishImageV_cellsDeclsAgree`).

- `writerP_inv`, `readerP_inv`: the two runs (`cfgEnv_partial_at` at the
  fragments `writerFragP`, `readerFragP`; the absolute `movdqa` rules of
  `Kraken/X64VecAbsWP.lean`);
- `publishImageV_cellsDeclsAgree`, `publishImageV_noFaultCode`: the per-cell
  facts;
- **`x64_publish_movdqa_verbatim`**: in every final configuration reachable
  from the `.kl`'s start states (under any architecture), `1:xmm2` is `0`,
  `v1` or `v2`;
- **`x64_publish_movdqa_verbatim_faultFree`**: no reachable configuration has
  a faulting step (`Config.FaultFree`).
-/
import Kraken.X64VecAbsWP
import Kraken.EnvCfgAbs
import Kraken.Promising.SLR.EnvG.X64VecDecls
import Kraken.X64.Parser

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.VecPublish

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **The `code` block of `publish_movdqa.kl`, verbatim.** -/
def publishCodeV : Program := parse("
writer:
  movdqa %xmm0,(rec)
  movdqa %xmm1,(rec)
  jmp done
reader:
  movdqa (rec),%xmm2
  jmp done
done:
")

/-- The `.kl` runner's data trailer of `publish_movdqa.kl`: the symbol `rec`
as a label behind a padding cell. -/
def publishDataV : Program := [.byteArray (.mk #[]), .label "rec"]

/-- The image: the code, then the data trailer. -/
def publishImageV : Program := publishCodeV ++ publishDataV

/-- The writer's fragment: the whole code (the `writer` block falls through
to the `reader` block in the image's block structure, so the fragment keeps
it; the writer's table is `False` there: `jmp done` skips it). -/
def writerFragP : Program := publishCodeV

/-- The reader's fragment: the `reader` block, then the exit label `done`. -/
def readerFragP : Program := parse("
reader:
  movdqa (rec),%xmm2
  jmp done
done:
")

/-- info: 8 -/
#guard_msgs in
#eval publishCodeV.length

theorem publishImageV_wf : Program.WF publishImageV := by decide

theorem writerFragP_sub : Program.subBlocksOfE writerFragP publishImageV = true := by decide

theorem readerFragP_sub : Program.subBlocksOfE readerFragP publishImageV = true := by decide

theorem publishImageV_8 : publishImageV[8]? = some (.byteArray (.mk #[])) := by decide

/-! ## The values and the invariant -/

/-- Version 1 of the record, `{1, 1}` (low word, high word). -/
def pubV1 : BitVec 128 := 0x10000000000000001

/-- Version 2 of the record, `{2, 2}`. -/
def pubV2 : BitVec 128 := 0x20000000000000002

/-- The record is the initial `0`, version 1 or version 2: never torn. -/
def PubVal (v : BitVec 128) : Prop := v = 0 ∨ v = pubV1 ∨ v = pubV2

/-- **The invariant**: the 16-byte location at `a` holds a `PubVal`. -/
def pubG (a : BitVec 64) (l : Loc) (v : Val) : Prop := l = ⟨a, 16⟩ → PubVal v

/-- The shared layout: the one 16-byte location at `a`. -/
abbrev pubS (a : BitVec 64) : SharedEnv.Layout := [(a, 16)]

theorem pubS_le16 (a : BitVec 64) : Le16 (pubS a) := fun x hx => by
  rw [List.mem_singleton] at hx
  subst hx
  simp

/-! ## The symbols -/

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labP (x : Label) : Int64 := (_root_.Executable.labels (layout publishImageV)).label x

/-- A symbol's address in the image. -/
abbrev symP (x : Label) : BitVec 64 := (labP x).toBitVec

variable [Executable.ValidLayout (layout publishImageV)]

local instance publishImageV.env : CodeEnv := ⟨layout publishImageV⟩

theorem writerFragP_placedIn : Program.PlacedIn writerFragP :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := publishImageV) publishImageV_wf rfl (by decide))
    writerFragP_sub

theorem readerFragP_placedIn : Program.PlacedIn readerFragP :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := publishImageV) publishImageV_wf rfl (by decide))
    readerFragP_sub

omit [Executable.ValidLayout (layout publishImageV)] in
theorem writerFragP_last : ∀ l blk, Program.blockAt writerFragP l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labP "done" :=
  Program.after_last_of (by decide)

omit [Executable.ValidLayout (layout publishImageV)] in
theorem readerFragP_last : ∀ l blk, Program.blockAt readerFragP l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labP "done" :=
  Program.after_last_of (by decide)

/-! ## The writer -/

/-- The writer's frame: `xmm0 = v1`, `xmm1 = v2`, `rec` not in `dmem`. -/
abbrev FrameWP (s : MachineData) : Prop :=
  s.zmms.get (.xmm .mm0) = pubV1 ∧ s.zmms.get (.xmm .mm1) = pubV2 ∧ Mem.loadInt s.dmem (symP "rec") 16 = none

/-- **The verbatim writer in `inv S G`** (partial): both stores keep `pubG`. -/
theorem writerP_inv (hal : isAligned 16 (symP "rec") = true) :
    ∀ s, FrameWP s →
      Safely (cenv.instrStepEnv (SharedEnv.inv (pubS (symP "rec")) (pubG (symP "rec"))))
        (fun x => (x.1.2 = labP "done" ∧ True) ∨ False) ((s, labP "writer"), ()) := by
  intro s hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.inv (pubS (symP "rec")) (pubG (symP "rec")))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (fun lb s _ => (lb = "writer" → FrameWP s) ∧ lb ≠ "reader") ?_ rfl
    (by decide) writerFragP_placedIn writerFragP_last s () ⟨fun _ => hs, by decide⟩
  cfg_cases_env [writerFragP]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hT, hne⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals first | exact absurd rfl hne | obtain ⟨hx0, hx1, hd⟩ := hT trivial
  all_goals first
    | exact hal
    | exact hd
    | exact Table.ofLabelsEnv_at ⟨by decide, ⟨fun h => absurd h (by decide), by decide⟩, .inl (by decide)⟩
    | simp [pubG, PubVal, hx0, hx1]

/-! ## The reader -/

omit layout in
/-- The low 128 bits of a register after `replaceLow` are the new bits (a
copy of `VectorMoves.take_replaceLow128`, private there). -/
theorem vec_take_replaceLow128 (x : BitVec 512) (v : BitVec 128) :
    (x.replaceLow v).take 128 = v := by
  simp only [BitVec.replaceLow, BitVec.drop, BitVec.take]
  ext i hi
  have : i < 512 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  simp
  rw [BitVec.getLsbD_append]
  simp [hi, this]

omit layout in
set_option exponentiation.threshold 512 in
/-- Reading back the register a legacy (SSE) move wrote gives the value
moved (a copy of `VectorMoves.get_setLegacy_xmm`, private there). -/
theorem vec_get_setLegacy_xmm (z : RegZmms) (r : RegMm) (v : BitVec 128) :
    (z.setLegacy (.xmm r) v).get (.xmm r) = v := by
  cases r <;> exact vec_take_replaceLow128 _ v

/-- The reader's postcondition at `done`: `xmm2` holds a `PubVal`. -/
abbrev ReaderPostP (s : MachineData) : Prop := PubVal (s.zmms.get (.xmm .mm2))

/-- **The verbatim reader in `inv S G`** (partial): the record it loads is a
`PubVal`. -/
theorem readerP_inv (hal : isAligned 16 (symP "rec") = true) :
    ∀ s, Mem.loadInt s.dmem (symP "rec") 16 = none →
      Safely (cenv.instrStepEnv (SharedEnv.inv (pubS (symP "rec")) (pubG (symP "rec"))))
        (fun x => (x.1.2 = labP "done" ∧ ReaderPostP x.1.1) ∨ False) ((s, labP "reader"), ()) := by
  intro s hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.inv (pubS (symP "rec")) (pubG (symP "rec")))
    (Q := fun s _ => ReaderPostP s) (E := fun _ _ _ => False)
    (fun lb s _ => (lb = "reader" → Mem.loadInt s.dmem (symP "rec") 16 = none) ∧
      (lb = "done" → ReaderPostP s)) ?_ rfl
    (by decide) readerFragP_placedIn readerFragP_last s () ⟨fun _ => hs, fun h => absurd h (by decide)⟩
  cfg_cases_env [readerFragP]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hT, hT2⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals first
    | exact hal
    | exact hT trivial
    | exact hT2 trivial
    | (simp; done)
    | (rename_i v _ hstep _
       exact Table.ofLabelsEnv_at ⟨by decide, ⟨fun h => absurd h (by decide), fun _ => by
          simp only [vec_get_setLegacy_xmm]; exact (SharedEnv.inv_step_load.mp hstep) rfl⟩,
        .inl (by decide)⟩)

/-! ## The per-cell facts -/

omit [Executable.ValidLayout (layout publishImageV)] in
theorem cellsDeclsAgree_layoutP {ds : Decls} {p : Program}
    (h : ∀ d ∈ p, ∀ (s : MachineData) (rng : Std.Rco Int64)
      (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects),
      (∀ s', (next s').DeclsAgree ds) → (∀ pc' s', (jmp pc' s').DeclsAgree ds) →
      Effects.DeclsAgree ds (@Directive.interp (_root_.Executable.labels (layout p)) d s rng next jmp)) :
    CellsDeclsAgree ds (layout p) := by
  intro d z hm s pc
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _ _ _ (fun _ => trivial) (fun _ _ => trivial)

omit [Executable.ValidLayout (layout publishImageV)] in
/-- The address `(rec)` computes in the image. -/
theorem addrRecP (regs : Reg64s) (rng : Std.Rco Int64) :
    @AddrExpr.interp (_root_.Executable.labels (layout publishImageV)) ⟨.W64⟩ ⟨none, none, .label "rec"⟩ regs rng =
      symP "rec" := by
  have := @AddrExpr.zeroExtend_interp_abs_label (_root_.Executable.labels (layout publishImageV)) "rec" regs rng
  simpa using this

omit [Executable.ValidLayout (layout publishImageV)] in
theorem publishImageV_cellsDeclsAgree {ds : Decls} (hd : ds.AgreesAt (symP "rec") 16) :
    CellsDeclsAgree ds (layout publishImageV) := by
  refine cellsDeclsAgree_layoutP ?_
  intro d hd' s rng next jmp hn hj
  simp only [publishImageV, publishCodeV, publishDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd'
  repeat' (rcases hd' with rfl | hd')
  all_goals simp [Directive.interp, Instr.interp, AvxOperation.interp, Effects.DeclsAgree, Operation.interp,
    AvxRegOrMem.interp, MachineData.setAvxLegacy, MachineData.loadAvx, MachineData.storeAvx,
    addrRecP, hn, hj, RelRegOrMem.interp]
  all_goals (repeat' (first | split | simp [Effects.DeclsAgree, hn, hd]))

omit [Executable.ValidLayout (layout publishImageV)] in
/-- `dirsNoFaultCode_layout` at the program's own layout (the label
addresses, hence the alignment of `(rec)`, are the image's). -/
theorem dirsNoFaultCode_layoutP {p : Program}
    (h : ∀ d ∈ p, (∀ b, d ≠ .byteArray b) → ∀ z, DirNoFault (layout p) d z) :
    DirsNoFaultCode (layout p) := by
  intro d z hm hb
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) hb _

omit [Executable.ValidLayout (layout publishImageV)] in
/-- **The image's non-data cells are fault-free**, `rec` being 16-aligned
(`movdqa` checks the alignment). -/
theorem publishImageV_noFaultCode (hal : isAligned 16 (symP "rec") = true) :
    DirsNoFaultCode (layout publishImageV) := by
  refine dirsNoFaultCode_layoutP ?_
  intro d hd' hb z s pc
  simp only [publishImageV, publishCodeV, publishDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd'
  repeat' (rcases hd' with rfl | hd')
  all_goals try exact absurd rfl (hb _)
  all_goals simp [Directive.interp, Instr.interp, AvxOperation.interp, Operation.interp,
    AvxRegOrMem.interp, MachineData.setAvxLegacy, MachineData.loadAvx, MachineData.storeAvx,
    addrRecP, hal, RelRegOrMem.interp, toEv, EvTree.NoFault]
  all_goals (repeat' (first | split | simp [toEv, EvTree.NoFault, EvTree.access_empty]))

/-! ## The exit -/

/-- `done`'s address is the padding cell `8`'s. -/
theorem labP_done : labP "done" = (layout publishImageV).addrOf 8 := by
  have hd : labP "done" = (layout publishImageV).addrOf 7 :=
    Program.label_addrOf_drop publishImageV_wf.nodup (by decide) (by decide)
  have h7 : (layout publishImageV).2[7]? = some (Directive.label "done", Kraken.Layout.size Directive 7) := by
    simp [Layout.apply_snd, Layout.frag, publishImageV, publishCodeV, publishDataV]
  rw [Executable.addrOf_succ _ h7, Executable.ValidLayout.label_size 7 "done" _ h7, hd]
  simp

/-- **No step of the image at the exit label `done`** (the padding cell). -/
theorem publishV_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labP "done" → ¬ (layout publishImageV).instrStepEnv env x R := by
  rw [labP_done]
  exact not_instrStepEnv_of_byteArray (i := 8) (b := .mk #[]) env publishImageV_8

/-! ## The thread specifications and the start -/

/-- The writer's specification: it reaches `done`. -/
abbrev pubSpecW : ThreadSpec (pubS (symP "rec")) (pubG (symP "rec")) :=
  ThreadSpec.ofSafely (layout publishImageV) (labP "done") (fun x => (x.1.2 = labP "done" ∧ True) ∨ False)
    (fun _ h => h.elim And.left False.elim)

/-- The reader's specification: at `done`, `xmm2` holds a `PubVal`. -/
abbrev pubSpecR : ThreadSpec (pubS (symP "rec")) (pubG (symP "rec")) :=
  ThreadSpec.ofSafely (layout publishImageV) (labP "done")
    (fun x => (x.1.2 = labP "done" ∧ ReaderPostP x.1.1) ∨ False) (fun _ h => h.elim And.left False.elim)

/-- Thread `0` is the writer, every other thread a reader. -/
abbrev pubSpec : Nat → ThreadSpec (pubS (symP "rec")) (pubG (symP "rec"))
  | 0 => pubSpecW
  | _ + 1 => pubSpecR

/-- A thread about to run the writer: the image, exit `done`, declarations
`ds`, pc at `writer`, `xmm0 = v1`, `xmm1 = v2`, `rec` not in its private
memory. -/
def PubStartW (ds : Decls) (st : State) : Prop :=
  st.exe = layout publishImageV ∧ st.endPc = labP "done" ∧ st.decls = ds ∧ st.st.2 = labP "writer" ∧
    st.st.1.zmms.get (.xmm .mm0) = pubV1 ∧ st.st.1.zmms.get (.xmm .mm1) = pubV2 ∧
    Split (pubS (symP "rec")) st.st.1.dmem

/-- A thread about to run the reader. -/
def PubStartR (ds : Decls) (st : State) : Prop :=
  st.exe = layout publishImageV ∧ st.endPc = labP "done" ∧ st.decls = ds ∧ st.st.2 = labP "reader" ∧
    Split (pubS (symP "rec")) st.st.1.dmem

theorem pubSpecW_holds (hal : isAligned 16 (symP "rec") = true) {ds : Decls} (hd : ds.AgreesAt (symP "rec") 16)
    {st : State} (h : PubStartW ds st) : pubSpecW.HoldsD ds st := by
  obtain ⟨he, hend, hds, hpc, hx0, hx1, hs⟩ := h
  refine ⟨he, hend, hds, publishImageV_cellsDeclsAgree hd, hs, ?_⟩
  have hst : st.st = (st.st.1, labP "writer") := Prod.ext rfl hpc
  rw [hst]
  exact writerP_inv hal _ ⟨hx0, hx1, hs.loadInt_none (List.mem_singleton_self _) (by decide) (by decide)⟩

theorem pubSpecR_holds (hal : isAligned 16 (symP "rec") = true) {ds : Decls} (hd : ds.AgreesAt (symP "rec") 16)
    {st : State} (h : PubStartR ds st) : pubSpecR.HoldsD ds st := by
  obtain ⟨he, hend, hds, hpc, hs⟩ := h
  refine ⟨he, hend, hds, publishImageV_cellsDeclsAgree hd, hs, ?_⟩
  have hst : st.st = (st.st.1, labP "reader") := Prod.ext rfl hpc
  rw [hst]
  exact readerP_inv hal _ (hs.loadInt_none (List.mem_singleton_self _) (by decide) (by decide))

theorem pubSpec_holds (hal : isAligned 16 (symP "rec") = true) {ds : Nat → Decls}
    (hd : ∀ tid, (ds tid).AgreesAt (symP "rec") 16) {c0 : Config isa}
    (h0w : ∀ t, c0.threads[0]? = some t → PubStartW (ds 0) t.st)
    (h0r : ∀ tid t, tid ≠ 0 → c0.threads[tid]? = some t → PubStartR (ds tid) t.st) :
    ∀ tid t, c0.threads[tid]? = some t → (pubSpec tid).HoldsD (ds tid) t.st := by
  intro tid t ht
  cases tid with
  | zero => exact pubSpecW_holds hal (hd 0) (h0w t ht)
  | succ n => exact pubSpecR_holds hal (hd _) (h0r _ t (by omega) ht)

omit [Executable.ValidLayout (layout publishImageV)] in
theorem pubMemInv {c0 : Config isa} (hmsgs : c0.mem.msgs = #[])
    (hinit : ∀ p ∈ c0.mem.init, pubG (symP "rec") p.1 p.2) : MemInv (pubG (symP "rec")) c0.mem :=
  MemInv.of_init hmsgs (fun _ _ => .inl rfl) hinit

/-! ## The theorems -/

/-- **`publish_movdqa.kl` verbatim: the record is never torn.** In every
final configuration reachable (under any architecture, promises included)
from start states where thread `0` is at `writer` with `xmm0 = v1`,
`xmm1 = v2`, every other thread at `reader`, all running the image with
declarations under which a 16-byte access at `rec` is its own footprint, and
the initial memory holds a `PubVal` at `⟨rec, 16⟩` and no messages, thread
`1`'s `xmm2` is `0`, `v1` or `v2`. -/
theorem x64_publish_movdqa_verbatim (hal : isAligned 16 (symP "rec") = true) {A : Arch} {fuel : Nat}
    {ds : Nat → Decls} (hd : ∀ tid, (ds tid).AgreesAt (symP "rec") 16) {c0 c : Config isa}
    (hmsgs : c0.mem.msgs = #[]) (hinit : ∀ p ∈ c0.mem.init, pubG (symP "rec") p.1 p.2)
    (h0w : ∀ t, c0.threads[0]? = some t → PubStartW (ds 0) t.st)
    (h0r : ∀ tid t, tid ≠ 0 → c0.threads[tid]? = some t → PubStartR (ds tid) t.st)
    (h : Reachable A fuel c0 c) (hf : c.final = true) :
    ∀ t, c.threads[1]? = some t → PubVal (t.st.st.1.zmms.get (.xmm .mm2)) := by
  intro t ht
  obtain ⟨-, hall⟩ := inv_reachableD (pubS_le16 _) pubSpec ds (pubMemInv hmsgs hinit)
    (pubSpec_holds hal hd h0w h0r) h
  obtain ⟨he, hend, -, -, -, hinv⟩ := hall 1 t ht
  exact ((post_of_halted_env (E := SharedEnv.inv (pubS (symP "rec")) (pubG (symP "rec")))
    (post := fun x => (x.1.2 = labP "done" ∧ ReaderPostP x.1.1) ∨ False) (publishV_stuck _) he hend hinv
    (SLR.Config.final_halted hf ht)).resolve_right id).2

/-- **No reachable configuration has a faulting step** (`Config.FaultFree`),
from the same start. -/
theorem x64_publish_movdqa_verbatim_faultFree (hal : isAligned 16 (symP "rec") = true) {A : Arch} {fuel : Nat}
    {ds : Nat → Decls} (hd : ∀ tid, (ds tid).AgreesAt (symP "rec") 16) {c0 : Config isa}
    (hmsgs : c0.mem.msgs = #[]) (hinit : ∀ p ∈ c0.mem.init, pubG (symP "rec") p.1 p.2)
    (h0w : ∀ t, c0.threads[0]? = some t → PubStartW (ds 0) t.st)
    (h0r : ∀ tid t, tid ≠ 0 → c0.threads[tid]? = some t → PubStartR (ds tid) t.st) :
    Config.FaultFree A fuel c0 :=
  faultFree_of_threadSpecD (pubS_le16 _) pubSpec ds (pubMemInv hmsgs hinit) (pubSpec_holds hal hd h0w h0r)
    (fun tid => by cases tid <;> exact publishImageV_noFaultCode hal)

end Kraken.Promising.X64.EnvG.VecPublish

#print axioms Kraken.Promising.X64.EnvG.VecPublish.x64_publish_movdqa_verbatim
#print axioms Kraken.Promising.X64.EnvG.VecPublish.x64_publish_movdqa_verbatim_faultFree
