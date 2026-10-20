/-
**Message passing with a fence-released writer**: the MP
property for the writer `FenceW.fwriterMp` (`str data; dmb ish; str flag`,
both stores plain, `SLR/FenceWTrees.lean`) and the existing MP reader
(`ldar` spin, then `ldr data`), under `Arch.armv8`, with the impure flag
(`φ` owns `Dt`): `mp_fence_armv8`, and its public form `mp_fence` (the
statement of `MpPublic.mp_public`).

This closes, for this program, the KNOWN_GAPS entry "fence-based release
cannot publish an impure value". Assembly, through
`theorem1IIPure_of_relWritesF` (`SLR/PromisePureF.lean`) and the local
`final_of_relWritesF`:

- **`NPSafeP (GHyb g.rel) (K2Scope AllocIds)` per thread**: the writer from
  `FenceW.fwRuleG` (`fw_npSafeP_hyb_S`, a `ThreadRuleRXG (GHyb rel)` whose
  prepay covers the fence-released flag store), the reader from the existing
  `Mp.mpR_npSafeP_hyb_S`.
- **The cell condition** (`RelWritesF` with the flag `t.views.FenceRel`) under
  a *thread-level* reachability invariant `FReach` (the reader's `ReachR`, or
  the writer at one of its positions with `FenceRel` at the flag store). It
  holds at every reachable configuration by `threadInv_reachable`, the
  thread-level analogue of `configInv_reachable` (an instruction step keeps
  it: `dmb ish` establishes `FenceRel` via `stepOne_fenceRel_of_fence_sy`,
  every other step leaves position 4 unreached; a promise step changes
  neither the state nor the views).
- **Erasure, ghost, initial invariants and the final argument**: the existing
  MP ones (`Mp.erase_mpInit`, `Mp.mpGhost`, `Mp.invR_init`, `Mp.mp_final`), as
  the published value is `1`.

Phase-1 limits do not apply (this route does not use `EvTree`'s whole-thread
environment `EnvG`); EnvG has no support for fence-released stores yet.
-/
import Kraken.Promising.SLR.FenceWRule
import Kraken.Promising.SLR.MpAdequacy
import Kraken.Promising.SLR.MpPublic
import Kraken.Promising.SLR.NPSafePHybA64
import Kraken.Promising.SLR.PromisePureF

namespace Kraken.Promising.SLR

open Kraken.Promising

/-! ## Thread-level invariants over the full machine -/

section ThreadInv

variable {I : ISA}

/-- **Thread-level invariants hold at every reachable configuration**
(`configInv_reachable` for predicates on whole threads, views included): if
every instruction step of thread `tid` keeps `J tid`, and so does appending
a promise, then `J` holds of every thread of every configuration reachable
from one where it holds. A promise step only appends to the thread's
promises (`SuccKind.promise`). -/
theorem threadInv_reachable {A : Arch} [I.LawfulState] {fuel : Nat} {J : Nat → Thread I → Prop}
    (hstep : ∀ (tid : Nat) (t : Thread I) (mem : Memory) (outs : List (Except String (Outcome I))) (o : Outcome I),
      J tid t → stepOne A t tid mem = some outs → .ok o ∈ outs → J tid o.thread)
    (hprom : ∀ (tid : Nat) (t : Thread I) (ts : Time), J tid t → J tid { t with prom := t.prom ++ [ts] })
    {c0 c : Config I} (h0 : ∀ tid t, c0.threads[tid]? = some t → J tid t) (h : Reachable A fuel c0 c) :
    ∀ tid t, c.threads[tid]? = some t → J tid t := by
  induction h with
  | refl => exact h0
  | @step c c' c'' hs _ ih =>
    apply ih
    cases succs_cases hs with
    | @instr tid t outs o ht hstep' ho =>
      exact withThread_threads (P := J) h0 (hstep tid t _ outs o (h0 tid t ht) hstep' ho)
    | @promise tid t p ht _ =>
      exact withThread_threads (P := J) h0 (hprom tid t _ (h0 tid t ht))

end ThreadInv

/-! ## Adequacy through the release-or-fence-released condition -/

section Adequacy

variable {I : ISA}

/-- **Program-agnostic adequacy from `theorem1IIPure_of_relWritesF`** (the
`GHyb` analogue of `final_of_relWrites`): erasure initially, the
release-or-fence-released cell condition under a thread-level reachable
invariant, and `NPSafeP (GHyb g₀.rel) (K2Scope AllocIds)` per thread give
the final postcondition `Φ` at every reachable final configuration. -/
theorem final_of_relWritesF [I.LawfulState] (A : Arch) (fuel : Nat) {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config I → Res → Ghost → Prop}
    {Φ : Config I → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (Jinv : Nat → Thread I → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv tid t)
    (hcell : ∀ tid t tree, Jinv tid t → I.exec t.st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (g₀.rel l) v) t.views.FenceRel)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model I) A B tid (GHyb g₀.rel) (K2Scope (model I) AllocIds) n m True
        (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  obtain ⟨v, rF', g', hv, E', hle, hB⟩ :=
    theorem1IIPure_of_relWritesF A fuel B states initMem rF g₀ hH hE hpend Jinv hJ hcell hsafe c hc
      ⟨c, .refl c, hf⟩
  obtain rfl : v = c := Config.VirtualOfG.eq_of_final hf hv
  exact hfin rF' g' E' hle (by rw [Reachable.size_eq hc, Config.init_size]) hB

end Adequacy

end Kraken.Promising.SLR

namespace Kraken.Promising.SLR.MpFence

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.FenceW
open Kraken.Promising.SLR.MpTrees

/-! ## The writer's reachable threads -/

section Writer

variable [layout : _root_.Layout] [hw : Executable.ValidLayout (layout fwriterMp)]

/-- The writer's state at one of its positions. -/
def ReachFS (P : Params) (st : State) : Prop :=
  FrameF P st ∧ ∃ i, i ≤ 5 ∧ AtPos fwriterMp st i

/-- **A writer step keeps `ReachFS`**, and reaches the flag store (position
4) only from `dmb ish` (position 3). -/
theorem reachFS_step (P : Params) {st : State} (h : ReachFS P st) (tree : EvTree State)
    (hex : isa.exec st = some tree) :
    tree.All fun st' => ReachFS P st' ∧ (AtPos fwriterMp st' 4 → AtPos fwriterMp st 3) := by
  obtain ⟨hF, i, hi, hp⟩ := h
  have hne : ∀ {j : Nat} {m : MachineData}, j ≤ 5 → j ≠ 4 →
      AtPos fwriterMp (A64Trees.goto st m ((layout fwriterMp).addrOf j)) 4 → AtPos fwriterMp st 3 :=
    fun {j} {m} hj hj4 h4 => absurd (atPosF_inj hj (by decide)
      (show AtPos fwriterMp (A64Trees.goto st m ((layout fwriterMp).addrOf j)) j from rfl) h4) hj4
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_f_mov2 st (hF.at hp (by decide))] at hex
    cases hex
    exact ⟨⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 1, by decide, rfl⟩,
      hne (by decide) (by decide)⟩
  · rw [exec_f_mov3 st (hF.at hp (by decide))] at hex
    cases hex
    exact ⟨⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 2, by decide, rfl⟩,
      hne (by decide) (by decide)⟩
  · rw [exec_f_str st (hF.at hp (by decide)) hF.x1 hF.dd] at hex
    cases hex
    intro _
    exact ⟨⟨hF.goto rfl rfl rfl, 3, by decide, rfl⟩, hne (by decide) (by decide)⟩
  · rw [exec_f_dmb st (hF.at hp (by decide))] at hex
    cases hex
    intro _
    exact ⟨⟨hF.goto rfl rfl rfl, 4, by decide, rfl⟩, fun _ => hp⟩
  · rw [exec_f_strf st (hF.at hp (by decide)) hF.x0 hF.df] at hex
    cases hex
    intro _
    exact ⟨⟨hF.goto rfl rfl rfl, 5, by decide, rfl⟩, hne (by decide) (by decide)⟩
  · rw [exec_end_f hF hp] at hex
    cases hex

/-- The writer's reachable threads: a reachable state, fence-released views
at the flag store. -/
def ReachF (P : Params) (t : Thread isa) : Prop :=
  ReachFS P t.st ∧ (AtPos fwriterMp t.st 4 → t.views.FenceRel)

/-- **A writer step keeps `ReachF`**: the flag store is reached only from
`dmb ish`, after which the views are `FenceRel`. -/
theorem reachF_step (P : Params) {A : Arch} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa} (h : ReachF P t)
    (hstep : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) : ReachF P o.thread := by
  obtain ⟨hR, h4⟩ := stepOne_leaf A hstep ho (reachFS_step P h.1)
  refine ⟨hR, fun hp4 => ?_⟩
  have hp3 := h4 hp4
  exact stepOne_fenceRel_of_fence_sy hstep ho (exec_f_dmb t.st (h.1.1.at hp3 (by decide)))

/-- **The writer's cell condition**: under `ReachF`, the next instruction's
writes that are neither release nor fence-released are pure for `mpGhost`
(the data store; the flag store is fence-released). -/
theorem cellF (P : Params) (hL : MpLocs P) (A : Arch) (t : Thread isa) (tree : EvTree State)
    (h : ReachF P t) (hex : isa.exec t.st = some tree) :
    tree.RelWritesF A (fun l v => Pred.Pure ((mpGhost P).rel l) v) t.views.FenceRel := by
  obtain ⟨⟨hF, i, hi, hp⟩, h4⟩ := h
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_f_mov2 t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_f_mov3 t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_f_str t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex
    cases hex
    exact ⟨fun _ _ => by
      show Pred.Pure ((mpGhost P).rel P.Dt) _
      rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure _, fun _ => trivial⟩
  · rw [exec_f_dmb t.st (hF.at hp (by decide))] at hex; cases hex; exact fun _ => trivial
  · rw [exec_f_strf t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex
    cases hex
    exact ⟨fun _ hn => absurd (h4 hp) hn, fun _ => trivial⟩
  · rw [exec_end_f hF hp] at hex; cases hex

omit hw in
/-- **The writer's initial invariant.** -/
theorem invXF_init {P : Params} (hL : MpLocs P) {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hF : FrameF P sW) (hp : AtPos fwriterMp sW 0) :
    InvXF P 0 True (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem P 0) (mpGhost P) := by
  refine ⟨⟨⟨mpGhost_rel_Fl, fun v => by rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v⟩,
    Thread.init sW, by simp [Config.init], hF, 0, hp, ?_, fun h => absurd h (by decide)⟩,
    fun ts h => absurd h (pend_mpGhost ts), fun t ht ts hts => ?_⟩
  · simp only [PhaseF, Own0, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    refine ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩
  · obtain ⟨s', -, rfl⟩ := Config.init_get?_thread ht
    cases hts

end Writer

/-! ## Both threads -/

/-- The reachable threads: the writer (layout `lW`, `ReachF`) or the reader
(layout `lR`, `Mp.ReachR`). -/
def FReach (lW lR : _root_.Layout) (P : Params) (t : Thread isa) : Prop :=
  ReachF (layout := lW) P t ∨ ReachR (layout := lR) P t.st

variable (lW lR : _root_.Layout) [hw : Executable.ValidLayout (lW fwriterMp)]
  [hr : Executable.ValidLayout (lR mpReader)]

/-- **`FReach` at every reachable configuration** from the two start
states. -/
theorem fReach_reachable (P : Params) {A : Arch} {fuel : Nat} {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : FrameF (layout := lW) P sW ∧ AtPos (layout := lW) fwriterMp sW 0)
    (hR : FrameR (layout := lR) P sR ∧ AtPos (layout := lR) mpReader sR 0)
    {c : Config isa} (hc : Reachable A fuel (Config.init [sW, sR] initMem) c) {tid : Nat} {t : Thread isa}
    (ht : c.threads[tid]? = some t) : FReach lW lR P t := by
  refine threadInv_reachable (J := fun _ t => FReach lW lR P t) ?_ (fun _ _ _ h => h) ?_ hc tid t ht
  · intro tid t mem outs o h hstep ho
    rcases h with h | h
    · exact .inl (reachF_step (layout := lW) P h hstep ho)
    · exact .inr (stepOne_leaf A hstep ho (reachR_step (layout := lR) P h))
  · intro tid t ht
    obtain ⟨s, hs, rfl⟩ := Config.init_get?_thread ht
    match tid, hs with
    | 0, hs =>
      cases hs
      exact .inl ⟨⟨hW.1, 0, by decide, hW.2⟩,
        fun h4 => absurd (atPosF_inj (layout := lW) (by decide) (by decide) hW.2 h4) (by decide)⟩
    | 1, hs =>
      cases hs
      exact .inr ⟨hR.1, 1, by show sR.st.2 = _; rw [r_addr_1 (layout := lR)]; exact hR.2, by decide⟩
    | n + 2, hs => cases hs

/-- **The cell condition** for both threads. -/
theorem fence_cell (P : Params) (hL : MpLocs P) (A : Arch) (t : Thread isa) (tree : EvTree State)
    (h : FReach lW lR P t) (hex : isa.exec t.st = some tree) :
    tree.RelWritesF A (fun l v => Pred.Pure ((mpGhost P).rel l) v) t.views.FenceRel := by
  rcases h with h | h
  · exact cellF (layout := lW) P hL A t tree h hex
  · exact (cellR (layout := lR) P A t.st tree h hex).relWritesF

/-- **Message passing with a fence-released writer, under `Arch.armv8`**: the
writer `fwriterMp` (thread `0`, laid out by `lW`; `str data; dmb ish;
str flag`, both plain) and the MP reader (thread `1`, laid out by `lR`)
started with `X0 = f`, `X1 = d`, from an initial memory with the flag at
`0`: at every reachable final configuration the reader's `W4` is `1` and the
data word's final value is `1`. -/
theorem mp_fence_armv8 {fuel : Nat} (P : Params) (hL : MpLocs P) {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : FrameF (layout := lW) P sW ∧ AtPos (layout := lW) fwriterMp sW 0)
    (hR : FrameR (layout := lR) P sR ∧ AtPos (layout := lR) mpReader sR 0)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal P.Fl = 0)
    {c : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sR] initMem) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal P.Dt = 1#128 := by
  have hsafe : ∀ tid, tid < [sW, sR].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (MpPost P 1) tid
      (GHyb (mpGhost P).rel) (K2Scope (model isa) AllocIds) n m True
      (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem P tid) (mpGhost P) := by
    intro tid htid n m
    rcases tid with _ | _ | k
    · exact fw_npSafeP_hyb_S (layout := lW) P Arch.armv8 0 1 hL (by decide) (by decide) (mpGhost P).rel
        (fun v => by rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v) n m
        (invXF_init (layout := lW) hL hW.1 hW.2)
    · exact mpR_npSafeP_hyb_S (layout := lR) P Arch.armv8 1 (by decide) (by decide) n m True _ _ _
        (invR_init (layout := lR) hR.1 hR.2)
    · simp only [List.length_cons, List.length_nil] at htid; omega
  exact final_of_relWritesF (I := isa) Arch.armv8 fuel (B := MpPost P 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal P.Dt = 1#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_mpInit P _ hF0) pend_mpGhost
    (fun _ t => FReach lW lR P t) (fun _ hc' _ _ ht => fReach_reachable lW lR P hW hR hc' ht)
    (fun _ t tree h hex => fence_cell lW lR P hL Arch.armv8 t tree h hex)
    hsafe hc hf fun _ _ E' hle hsize hB => mp_final E' hf hsize (by rw [hle.rel]; exact mpGhost_rel_Fl) hB

/-! ## The public statement -/

section Start

variable [layout : _root_.Layout]

/-- The fence-released writer at its start (`MpPublic.StartW` for
`fwriterMp`). -/
structure StartF (f d : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout fwriterMp
  decls : s.decls = {}
  endPc : s.endPc = (layout fwriterMp).addrOf 6
  pc : s.st.2 = (layout fwriterMp).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = f
  x1 : s.st.1.regs.X1.toBitVec = d
  df : Mem.loadInt s.st.1.dmem f 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none

theorem StartF.frame {f d : BitVec 64} {s : State} (h : StartF f d s) :
    FrameF (MpPublic.ghostParams f d) s ∧ AtPos fwriterMp s 0 :=
  ⟨⟨h.exe, h.decls, h.endPc, h.x0, h.x1, h.df, h.dd⟩, h.pc⟩

end Start

/-- **Message passing with a fence-released writer (`dmb ish; str`) for
AArch64 under `Arch.armv8`**, public form (the statement of
`MpPublic.mp_public` with `mpWriter` replaced by `fwriterMp`).

For valid layouts `lW` of `fwriterMp` and `lR` of `mpReader` and addresses
`f ≠ d`: if thread `0` is the writer and thread `1` the reader, each at its
start with `X0 = f`, `X1 = d` (`StartF`, `MpPublic.StartR`), and the initial
memory has the flag word `⟨f, 4⟩` at `0`, then every configuration
`Reachable` under `Arch.armv8` that is final has the reader's `W4` at `1` and
the data word `⟨d, 4⟩` at `1`.

The publication is by a *plain* store after `dmb ish`, with the impure flag
predicate (the flag message owns `Dt`); the coverage notes of `mp_public`
apply (final configurations only, `f ≠ d` as `Loc`s, faults not covered). -/
theorem mp_fence {fuel : Nat} (f d : BitVec 64) (hfd : f ≠ d)
    {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartF (layout := lW) f d sW) (hR : MpPublic.StartR (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 1#128 :=
  mp_fence_armv8 lW lR (MpPublic.ghostParams f d) (MpPublic.ghostParams_mpLocs hfd)
    (StartF.frame (layout := lW) hW) (MpPublic.StartR.frame (layout := lR) hR) hF0 hc hf

end Kraken.Promising.SLR.MpFence

#print axioms Kraken.Promising.SLR.threadInv_reachable
#print axioms Kraken.Promising.SLR.final_of_relWritesF
#print axioms Kraken.Promising.SLR.MpFence.fReach_reachable
#print axioms Kraken.Promising.SLR.MpFence.mp_fence_armv8
#print axioms Kraken.Promising.SLR.MpFence.mp_fence
