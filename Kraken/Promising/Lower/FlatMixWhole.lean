/-
A private FlatHashMap lookup feeding the shared Michael–Scott queue, as a
whole two-thread program on the executable Promising machine
(`Reachable Arch.armv8`), through the value-restricted lowering kit
(`KitVals.lower_promising_valsW`). ISA: AArch64 (`isa`).

* Thread `0` runs `mixProg`: `main` (`Lower/FlatMixMain.lean`) looks a key
  up in a table held in its private `dmem`, stores the answer (the hit's
  value, or the marker `1` on a miss) into the first node's data word and
  enqueues that node, then stores `2` into the second node and enqueues it.
* Thread `1` runs the MS queue pilot's dequeuer `progD`.
* Per thread, the kit's `main`, purity and value triples
  (`Lower/FlatMixVals.lean`); `QG P` bounds `tail` to `0` or a node, keeping
  `enq`'s shared accesses off thread `0`'s private memory (`QPriv`).
* The shared postcondition `MixB` is msqueue2's `MB2` with the enqueuer's
  side strengthened by thread `0`'s stored value; the final reading uses
  that the dequeuer's acquire ids are exclusive.

Statements:
* `mixProg_promising`: every final configuration reachable from starts in
  `MixStartS` (thread `0`) and the pilot's `StartD` (thread `1`), with
  msqueue2's initial memory (`InitV2`) holding `QG`-values, satisfies
  `MixFinal`: the dequeuer read `1` then `2` (`MsQueue2Final`), and thread
  `0`'s `x20` holds the lookup's answer or the marker (`Stored0`).
  **Hypothesis (`Low1`)**: msqueue2's protocol pins the first data word to
  low 32 bits `1`, so a hit's value must have low 32 bits `1`.
* `mixProg_promising_tblD`: the start hypotheses hold at a concrete
  configuration: `tblD` (the table `tbl1` with its control word at `0x3000`,
  off the queue) in `tblDMem`, key `6` (a miss), the queue at the MS queue
  pilot's addresses; so every final configuration has the dequeuer's `1`,
  `2` and thread `0`'s `x20 = 1` (the marker). `mixRunD` explores the same
  configuration promise-free.
-/
import Kraken.Promising.Lower.FlatMixVals
import Kraken.Promising.Lower.KitVals
import Kraken.Promising.Lower.KitFrag
import Kraken.Promising.Lower.MsqPilotWhole
import Kraken.Promising.Lower.FlatWholeProg
import Kraken.Promising.Lower.FlatInsert
import Kraken.Promising.SLR.EnvG.A64MaskHelpers

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Flat.Mix

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.Pilot (NoDmem)
open Kraken.Promising.Lower.MsqPilot (enqFrag progD StartD endD EQG RPG enqFrag_pureF)
open Kraken.Promising.Lower.KitVals (LowerThreadW lower_promising_valsW)
open Kraken.Promising.Lower.Kit (partialTripleEnv_of_fragL)
open Kraken.Promising.SLR.EnvG.Vals (valsEnv)

/-! ## The text and its static facts -/

/-- **Thread `0`'s text**: `main`, `flat_lookup`, `enq`, `done`. -/
def mixProg : Program := mixMain ++ flatLookup ++ enqFrag ++ Whole.doneFrag

theorem mixProg_wf : Program.WF mixProg := by decide
theorem mixProg_ne : mixProg.any (fun d => !d.isLabel) = true := by decide
theorem mixProg_hs : [mixMain, flatLookup, enqFrag].all (Program.subBlocksOfE · mixProg) = true := by decide

theorem mixMain_phase1F : ∀ d ∈ mixMain, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  dirs_phase1F_any mixMain
theorem enq_phase1F : ∀ d ∈ enqFrag, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  dirs_phase1F_any enqFrag

section Static
variable [layout : _root_.Layout]

theorem mixProg_rmwLive : (layout mixProg).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem mixProg_phase1F [Executable.ValidLayout (layout mixProg)] : Phase1TreeF (layout mixProg) := by
  refine phase1TreeF_of_dirs (dirsPhase1F_layout fun d hd => ?_)
  simp only [mixProg, List.mem_append] at hd
  rcases hd with ((h | h) | h) | h
  · exact mixMain_phase1F d h
  · exact Whole.lookup_phase1F d h
  · exact enq_phase1F d h
  · exact Whole.done_phase1F d h

set_option maxRecDepth 8000 in
/-- No step from the end of the text (the trailing label `done`). -/
theorem mixProg_stuck [Executable.ValidLayout (layout mixProg)] (env : SharedEnv) :
    ∀ x R, x.1.2 = (layout mixProg).addrOf mixProg.length → ¬ (layout mixProg).instrStepEnv env x R :=
  not_instrStepEnv_of_end_labels env 1

end Static

/-! ## The shared postcondition -/

/-- Thread `0`'s `x20` holds the lookup's answer or the marker. -/
def Stored0 (x : Tbl × Nat) (c : Config isa) : Prop := ∃ th, c.threads[0]? = some th ∧ StoredIn x th.st.st.1

/-- **The shared postcondition**: msqueue2's dequeuer side, or the
enqueuer's token together with thread `0`'s stored value. -/
def MixB (P : Params2) (x : Tbl × Nat) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  (∃ th, c.threads[1]? = some th ∧
    DoneD2 c.mem P th.st.st.1.regs.X10.toBitVec th.st.st.1.regs.X11.toBitVec ∧ InitV2 c.mem P ∧
    ∀ l, P.IsW l → 1 ≤ r.acq l 0) ∨ (1 ≤ (r.wr P.tokE).q ∧ Stored0 x c)

theorem MixB.mb2 {P : Params2} {x : Tbl × Nat} {c : Config isa} {r : Res} {g : Ghost} (h : MixB P x c r g) :
    MB2 P c r g :=
  h.imp id And.left

/-- The final property: msqueue2's, and thread `0`'s stored value. -/
def MixFinal (x : Tbl × Nat) (c : Config isa) : Prop := MsQueue2Final c ∧ Stored0 x c

/-! ## The threads -/

/-- Thread `0`'s start on its registers and private memory: `lookup`'s
precondition at `ra`, the queue arguments, `Low1`, and a private memory off
the queue. -/
def MixStart (P : Params2) (x : Tbl × Nat) (ra : Int64) (s : MachineData) : Prop :=
  GPre P s.dmem x ra s ∧ (∀ r, lookupN x.1 x.2 = some r → Low1 r) ∧ QPriv P s.dmem

/-- `main`'s protocol spec with the private memory read off the state. -/
theorem mixMain_fragW (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (x : Tbl × Nat) :
    FragSpecEnvL (SharedEnv.counted (EQG P (QG P))) [mixMain, flatLookup, enqFrag] "main"
      (fun ra t g => MixPre P (QG P) t.dmem x ra t g ∧ QPriv P t.dmem) (MixPost P (QG P) x) :=
  ⟨fun hpl ra t g h => (mixMain_fragL P hL ht (QG P) (· = t.dmem) (qFrameOK_priv P _ h.2) t.dmem rfl
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2 x).spec hpl ra t g h.1⟩

/-- `main`'s purity twin (`mixMain_fragG` at the value-restricted purity
environment, `enqFrag_pureF`). -/
theorem mixMain_pureW (P : Params2) (ht : P.t = P.h + 8) (rel : Loc → Pred)
    (hd : ∀ m, m = P.n1 ∨ m = P.n2 → ∀ v : Val, Pred.Pure (rel ⟨m, 4⟩) v) (x : Tbl × Nat) :
    FragSpecEnvL (RPG rel (QG P)) [mixMain, flatLookup, enqFrag] "main"
      (fun ra t _ => MixStart P x ra t) (fun _ _ _ _ _ => True) :=
  ⟨fun hpl ra t g h => (mixMain_fragG (valsEnv (SharedEnv.relPure Arch.armv8 rel) (QG P)) P t.dmem (· = t.dmem)
    rfl h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2 (fun m hm _ _ v _ _ => hd m hm v)
    (fun _ _ => (enqFrag_pureF P ht rel (QG P) _ (qFrameOK_priv P _ h.2.2)).mono
      (fun _ _ _ ⟨hlr, hx0, _, hdm⟩ => ⟨hlr, hx0, hdm⟩) (fun _ _ _ _ _ _ h => h)) x).spec hpl ra t g h.1⟩

/-- `main`'s value triple (`mixMain_fragG` at `inv (QS P) (QG P)`,
`enqFrag_valF`). -/
theorem mixMain_valW (P : Params2) (ht : P.t = P.h + 8) (x : Tbl × Nat) :
    FragSpecEnvL (IVQ P) [mixMain, flatLookup, enqFrag] "main"
      (fun ra t _ => MixStart P x ra t) (fun _ _ _ _ _ => True) :=
  ⟨fun hpl ra t g h => (mixMain_fragG (SharedEnv.inv (QS P) (QG P)) P t.dmem (· = t.dmem)
    rfl h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2
    (fun _ hm _ _ _ _ => by simp [QG, msqGA, MsqValLA]; exact .inr hm)
    (fun m hm => enqFrag_valF P ht _ (qFrameOK_priv P _ h.2.2) m (by rcases hm with rfl | rfl <;> simp [MsqNodeA]))
    x).spec hpl ra t g h.1⟩

/-- `hB` of thread `0`: the enqueuer's token and the stored value. -/
theorem hB_mix (l : _root_.Layout) (P : Params2) (x : Tbl × Nat) :
    ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf (layout := l) mixProg (fun s σ => ∃ _ : Nat, ComE2 P σ ∧ StoredIn x s) (t.st.st, σ) →
      t.prom = [] → EnvRel 0 (planE2 P) σ c t r g cl → cl → MixB P x c r g := by
  intro c t r g cl σ hpost hp hrel _
  obtain ⟨-, -, hC, hS⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr ⟨hC.2.2.1, t, hrel.ht, hS⟩
  · rw [hp] at hts; cases hts

/-- `hB` of thread `1`: always the dequeuer's side (`KitMsq.hB_D`). -/
theorem hB_deq (l : _root_.Layout) (P : Params2) (x : Tbl × Nat) :
    ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf (layout := l) progD (fun s σ => ∃ _ : Nat, Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ)
      (t.st.st, σ) → t.prom = [] → EnvRel 1 (planD2 P) σ c t r g cl → cl → MixB P x c r g := by
  intro c t r g cl σ hpost hp hrel _
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1⟩
  · rw [hp] at hts; cases hts

/-- **Thread `0` as a lowered thread** over the value-restricted
environments. -/
noncomputable def mixT (l : _root_.Layout) [Executable.ValidLayout (l mixProg)] (P : Params2) (hL : QLocs2 P)
    (ht : P.t = P.h + 8) (x : Tbl × Nat)
    (hd : ∀ m, m = P.n1 ∨ m = P.n2 → ∀ v : Val, Pred.Pure ((ghost2 P).rel ⟨m, 4⟩) v) :
    LowerThreadW Arch.armv8 0 (ghost2 P).rel (MixB P x) (QS P) (QG P) where
  l := l
  p := mixProg
  valid := inferInstance
  pl := planE2 P
  hpl := planE2_valid P
  live := mixProg_rmwLive
  shape := mixProg_phase1F
  stuck := mixProg_stuck (layout := l)
  Q s σ := ComE2 P σ.1 ∧ StoredIn x s
  hB := hB_mix l P x
  PreR s _ := MixStart P x ((l mixProg).addrOf mixProg.length) s
  QR _ _ := True
  pure := @partialTripleEnv_of_fragL l mixProg _ _ _ _ _ _ _ (mixMain_pureW P ht _ hd x) mixProg_wf rfl mixProg_ne
    mixProg_hs _ _ (fun _ _ h => h) (fun _ _ _ _ _ _ => trivial)
  Pre s σ := MixPre P (QG P) s.dmem x ((l mixProg).addrOf mixProg.length) s σ ∧ QPriv P s.dmem
  main := @partialTripleEnv_of_fragL l mixProg _ _ _ _ _ _ _ (mixMain_fragW P hL ht x) mixProg_wf rfl mixProg_ne
    mixProg_hs _ _ (fun _ _ h => h) (fun _ _ _ _ _ ⟨hC, hS, _⟩ => ⟨hC, hS⟩)
  PreV s _ := MixStart P x ((l mixProg).addrOf mixProg.length) s
  QV _ _ := True
  vals := @partialTripleEnv_of_fragL l mixProg _ _ _ _ _ _ _ (mixMain_valW P ht x) mixProg_wf rfl mixProg_ne
    mixProg_hs _ _ (fun _ _ h => h) (fun _ _ _ _ _ _ => trivial)

/-- **Thread `1` as a lowered thread**: the pilot's `main` and purity
triples lifted to the value-restricted environments, and `mainD_valQ`. -/
noncomputable def deqT (l : _root_.Layout) [Executable.ValidLayout (l progD)] (P : Params2) (hL : QLocs2 P)
    (ht : P.t = P.h + 8) (x : Tbl × Nat) : LowerThreadW Arch.armv8 1 (ghost2 P).rel (MixB P x) (QS P) (QG P) where
  l := l
  p := progD
  valid := inferInstance
  pl := planD2 P
  hpl := planD2_valid P
  live := MsqPilot.progD_rmwLive (layout := l)
  shape := MsqPilot.progD_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q s σ := Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1
  hB := hB_deq l P x
  PreR s _ := Int64.ofBitVec s.regs.X30.toBitVec = endD (layout := l) ∧ NoDmem s
  QR _ _ := True
  pure := @PartialTripleEnv.countedVals ⟨l progD⟩ _ (QG P) _ _ _ _ (MsqPilot.mainD_pure (layout := l) _)
  Pre := MsqPilot.MainDPre (layout := l) P
  main := @PartialTripleEnv.countedVals ⟨l progD⟩ _ (QG P) _ _ _ _
    (MsqPilot.mainD_partialTripleEnv (layout := l) P hL ht)
  PreV s _ := Int64.ofBitVec s.regs.X30.toBitVec = endD (layout := l) ∧ s.regs.X21.toBitVec = P.h ∧ NoDmem s
  QV _ _ := True
  vals := mainD_valQ (layout := l) P ht

/-! ## The whole program -/

/-- **Thread `0`'s start state**: `mixProg`'s code at layout `l`, no
declarations, at the start of the text returning to its end, with
`MixStart` for that return address. -/
structure MixStartS (l : _root_.Layout) (P : Params2) (x : Tbl × Nat) (s : isa.State) : Prop where
  exe : s.exe = l mixProg
  decls : s.decls = {}
  endPc : s.endPc = (l mixProg).addrOf mixProg.length
  pc : s.st.2 = (l mixProg).addrOf 0
  pre : MixStart P x ((l mixProg).addrOf mixProg.length) s.st.1

/-- **The FlatHashMap-lookup → MS-queue program on the Promising machine**
(AArch64, `Arch.armv8`): for all layouts `l0` of `mixProg` and `l1` of
`progD`, queue parameters `P` with msqueue2's disequalities and
`tail = head + 8`, and a lookup argument `x`: if thread `0` starts in
`MixStartS` (lookup arguments, the table in its private memory, the queue
arguments in `x25`–`x27`, `Low1`, the private memory off the queue), thread
`1` in the pilot's `StartD`, and the initial memory satisfies `InitV2` with
`QG`-values, then every final configuration reachable under `Arch.armv8`
satisfies `MixFinal x`. -/
theorem mixProg_promising {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 mixProg)]
    [Executable.ValidLayout (l1 progD)] (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (x : Tbl × Nat)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : MixStartS l0 P x s0)
    (h1 : StartD (layout := l1) P.h s1) (hi : InitV2 (Config.init [s0, s1] initMem).mem P)
    (hm : ∀ p ∈ initMem, QG P p.1 p.2) {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) c) (hf : c.final = true) : MixFinal x c := by
  obtain ⟨⟨h, t, d, n1⟩, n2⟩ := P
  have hr : ∀ m, m = n1 ∨ m = n2 → ∀ v : Val, Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel ⟨m, 4⟩) v := by
    have hr' : ∀ l, ¬ Params2.IsW ⟨⟨h, t, d, n1⟩, n2⟩ l → ∀ v, Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel l) v :=
      fun l hl v => by rw [ghost2_rel_ne hl]; exact Pred.emp_pure v
    rintro m (rfl | rfl) v
    · exact hr' _ (not_isW_dat _) v
    · exact hr' _ (not_isW_dat2 _) v
  refine lower_promising_valsW Arch.armv8 fuel (QG _) (fun _ hc' => Config.ntFree_armv8 hc') (erase_init2 hL _) rfl
    (MemInv.of_init rfl (fun _ _ => .inl (by simp)) hm)
    (fun tid hh => match tid, hh with
      | 0, _ => mixT l0 _ hL ht x hr
      | 1, _ => deqT l1 _ hL ht x
      | _ + 2, hh => absurd hh (by simp))
    (fun tid hh => ?_) hc hf (fun rF' g' E' hle hsize hB => ?_)
  · rcases tid with _ | _ | _
    · obtain ⟨he, hds, hend, hpc, hpre⟩ := h0
      obtain ⟨⟨hl, h25, h26, h27, -⟩, hlo, hq⟩ := id hpre
      exact ⟨he, hds, hend, hpc, ⟨0, hpre⟩, ⟨0, ⟨hl, h25, h26, h27, rfl, hlo, start1_init _ _⟩, hq⟩, ⟨0, hpre⟩⟩
    · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
      exact ⟨he, hds, hend, hpc, ⟨0, h30, hd8, hd4⟩, ⟨0, h30, h21, ⟨hd8, hd4⟩, comD2_init _ _ hi⟩,
        ⟨0, h30, h21, hd8, hd4⟩⟩
    · simp at hh; omega
  · have hs2 : c.threads.size = 2 := by simpa using hsize
    have hi0 : (0 : Nat) < c.threads.size := by omega
    have hi1 : (1 : Nat) < c.threads.size := by omega
    refine ⟨msqueue2_final_of_hB hL hf E' hle hs2 fun tid hd => (hB tid hd).mb2, ?_⟩
    rcases hB 0 (Config.final_done hf hi0) with ⟨-, -, -, -, a0⟩ | ⟨-, hs⟩
    · rcases hB 1 (Config.final_done hf hi1) with ⟨-, -, -, -, a1⟩ | ⟨-, hs⟩
      · exact (TreiberCommon.acq_pair_false E' hi0 hi1 (by decide) (a0 _ (Or.inl rfl)) (a1 _ (Or.inl rfl))).elim
      · exact hs
    · exact hs

/-! ## The concrete instance, table off the queue -/

/-- Alias of `Flat.wordsAt_load_off` (`Lower/FlatInsert.lean`). -/
theorem wordsAt_load_off (a b : BitVec 64) (f : Nat → Nat) (m : DataMem) (k : Nat) : ∀ n,
    (∀ i < n, 8 ≤ (b - (a + BitVec.ofNat 64 (8 * i))).toNat ∧ (b - (a + BitVec.ofNat 64 (8 * i))).toNat + k ≤ 2 ^ 64) →
      (wordsAt a f n m).loadInt b k = m.loadInt b k :=
  Flat.wordsAt_load_off a b f m k

/-- The queue at the MS queue pilot's addresses (`MsqPilot.initMem`). -/
abbrev P1 : Params2 := ⟨⟨0x1000, 0x1008, 0x1100, 0x1200⟩, 0x1300⟩

/-- `mixProg` at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def layoutM : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize mixProg

set_option maxRecDepth 4000 in
instance validM : Executable.ValidLayout (layoutM mixProg) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- `tbl1` with its control word at `0x3000`, off the MS queue pilot's
addresses (`P1`: `0x1000`–`0x1308`); the slots stay at `0x2000`. -/
def tblD : Tbl := { tbl1 with cb := 0x3000#64 }

theorem tblD_lookup6 : lookupN tblD 6 = some none := by decide +kernel
theorem tblD_bounded6 : tblD.Bounded 6 :=
  ⟨by decide, by decide, fun s => by simp only [tblD, tbl1]; split <;> decide,
   fun s => by simp only [tblD, tbl1]; split <;> decide,
   fun _ => by show (hashN 5).1 * 2 ^ 16 < W64; decide +kernel, by decide⟩
theorem tblD_probeEnds6 : ProbeEnds tblD 6 := by
  show (lookupN tblD 6).isSome = true
  rw [tblD_lookup6]; rfl

/-- **A concrete memory holding `tblD`**: its control word at `0x3000`, its
eight slots at `0x2000` (from the empty memory). -/
def tblDMem : DataMem := wordsAt tblD.sb (slotWords tblD) 16 (wordsAt tblD.cb tblD.ctrl 1 ∅)

theorem tblD_inMem : tblD.InMem tblDMem := by
  have hw : ∀ i, slotWords tblD i < W64 := fun i => by
    simp only [slotWords, tblD, tbl1]; split <;> split <;> decide
  refine ⟨fun g hg => ?_, fun s hs => ?_⟩
  · change g.toNat ≤ 0 at hg
    have e : tblD.cb + g <<< 3 = tblD.sb + BitVec.ofNat 64 0x1000 := by
      rw [shl_ofNat]
      simp only [tblD, tbl1]; bv_omega
    rw [e, tblDMem, wordsAt_load_above _ _ _ _ (by decide) 16 (by decide)]
    rw [show tblD.sb + BitVec.ofNat 64 0x1000 = tblD.cb + BitVec.ofNat 64 (8 * 0) by
      simp only [tblD, tbl1]; bv_omega, show g.toNat = 0 by omega]
    exact wordsAt_load _ _ _ (fun _ => by show (hashN 5).1 * 2 ^ 16 < W64; decide +kernel)
      1 (by decide) 0 (by decide)
  · change s.toNat ≤ 7 at hs
    rw [shl_ofNat]
    have h1 := wordsAt_load tblD.sb (slotWords tblD) (wordsAt tblD.cb tblD.ctrl 1 ∅) hw 16
      (by decide) (2 * s.toNat) (by omega)
    have h2 := wordsAt_load tblD.sb (slotWords tblD) (wordsAt tblD.cb tblD.ctrl 1 ∅) hw 16
      (by decide) (2 * s.toNat + 1) (by omega)
    simp only [slotWords, Nat.mul_mod_right, Nat.mul_add_mod,
      Nat.mul_div_cancel_left _ (by decide : 0 < 2),
      show (2 * s.toNat + 1) / 2 = s.toNat by omega, ↓reduceIte] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [show BitVec.ofNat 64 (2 ^ 4 * s.toNat) = BitVec.ofNat 64 (8 * (2 * s.toNat)) by
        congr 1; omega]
      exact h1
    · rw [show tblD.sb + BitVec.ofNat 64 (2 ^ 4 * s.toNat) + 8#64
          = tblD.sb + BitVec.ofNat 64 (8 * (2 * s.toNat + 1)) by
        simp only [W64] at *; bv_omega]
      exact h2

theorem tblDMem_none (b : BitVec 64) (k : Nat)
    (hs : ∀ i < 16, 8 ≤ (b - (tblD.sb + BitVec.ofNat 64 (8 * i))).toNat ∧
      (b - (tblD.sb + BitVec.ofNat 64 (8 * i))).toNat + k ≤ 2 ^ 64)
    (hc : ∀ i < 1, 8 ≤ (b - (tblD.cb + BitVec.ofNat 64 (8 * i))).toNat ∧
      (b - (tblD.cb + BitVec.ofNat 64 (8 * i))).toNat + k ≤ 2 ^ 64) (hk : 0 < k) :
    tblDMem.loadInt b k = none := by
  rw [tblDMem, wordsAt_load_off _ _ _ _ _ 16 hs, wordsAt_load_off _ _ _ _ _ 1 hc]
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ_eq_map]

theorem qPriv_tblD : QPriv P1 tblDMem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact tblDMem_none _ _ (by decide) (by decide) (by decide)

/-- Thread `0`'s registers and memory: `tblD` in `tblDMem`, key `6`, the
queue arguments, `x30 =` the end of the text. -/
def stMD : MachineData where
  dmem := tblDMem
  regs :=
    { X0 := 0x3000, X1 := 0x2000, X2 := 0, X3 := 7, X4 := 6, X25 := 0x1000, X26 := 0x1200, X27 := 0x1300,
      X30 := 0x100000 + 328 }

/-- Thread `0`: `mixProg` at `layoutM`, from `stMD`. -/
def threadMD : AArch64.State where
  exe := layoutM mixProg
  endPc := 0x100000 + 328
  st := (stMD, 0x100000)

set_option maxRecDepth 8000 in
theorem threadMD_start : MixStartS layoutM P1 (tblD, 6) threadMD := by
  refine ⟨rfl, rfl, by decide, by decide, ⟨⟨?_, tblD_inMem, tblD_bounded6, tblD_probeEnds6⟩, rfl, rfl, rfl, rfl⟩,
    fun r h => ?_, qPriv_tblD⟩
  · refine ⟨rfl, rfl, ?_, ?_, ?_, by decide⟩ <;> decide +kernel
  · rw [tblD_lookup6] at h; cases h; trivial

theorem qLocs2_P1 : QLocs2 P1 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem initV2_P1 : InitV2 (Config.init [threadMD, MsqPilot.threadD] MsqPilot.initMem : Config isa).mem P1 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Config.init] <;> decide

theorem initMem_QG : ∀ p ∈ MsqPilot.initMem, QG P1 p.1 p.2 := by
  simp [MsqPilot.initMem, MsqValLA, MsqValVA, MsqNodeA]

/-- **Non-vacuity, table off the queue**: `mixProg_promising` at `threadMD`
and the MS queue pilot's `threadD`, `initMem`: every final configuration has
the dequeuer's `1`, `2` and thread `0`'s `x20 = 1` (key `6` misses). -/
theorem mixProg_promising_tblD {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [threadMD, MsqPilot.threadD] MsqPilot.initMem) c)
    (hf : c.final = true) : MsQueue2Final c ∧ ∃ th, c.threads[0]? = some th ∧ th.st.st.1.regs.X20.toNat = 1 := by
  obtain ⟨hF, th, h0, r, hr, hx⟩ := mixProg_promising layoutM MsqPilot.layoutD P1 qLocs2_P1 (by decide) (tblD, 6)
    threadMD_start MsqPilot.threadD_start initV2_P1 initMem_QG hc hf
  rw [tblD_lookup6] at hr; cases hr
  exact ⟨hF, th, h0, hx⟩

/-- **The same configuration explored promise-free** (`boundHit = false`):
one final, with thread `0`'s `x20` and the dequeuer's `(x10, x11)`. -/
def mixRunD : List (Nat × Nat × Nat) × Bool × List String :=
  let r := explore Arch.armv8 (Config.init [threadMD, MsqPilot.threadD] MsqPilot.initMem : Config isa)
    (fun c => match c.threads.toList with
      | [m, d] => (m.st.st.1.regs.X20.toNat, d.st.st.1.regs.X10.toBitVec.toNat, d.st.st.1.regs.X11.toBitVec.toNat)
      | _ => (0, 0, 0)) { fuel := 200, maxPromises := some 0 }
  (r.finals, r.boundHit, r.faults)

/-- info: ([(1, 1, 2)], false, []) -/
#guard_msgs in
#eval mixRunD

end Kraken.Promising.Lower.Flat.Mix
