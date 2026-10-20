/-
**The function specifications of `enq` and
`deq`, once each.** ISA: AArch64; environments: msqueue2's
`EE2 P` (the enqueuer, thread `0`) and `ED2 P` (the dequeuer, thread `1`),
`EnvGCAdj` on `planE2`/`planD2` (`EnvG/MsQueue2VC.lean`), counted.

Each spec is a `FunSpecPartialEnv` (`AArch64/EnvCallsPartial.lean`) at the
function's label, proved with one `vcgen` call per block and the existing VCs
of `EnvG/MsQueue2VC.lean` verbatim (`vc_e_*2`, `vc_d_*2`), as the inline
proofs of `EnvG/MsQueue2VCGen.lean`. The frame is the first lowering pilot's `CalleeSaved`
and `NoDmem` (`Lower/PilotSpecs.lean`), unchanged. The queue argument
`q` is `&head`; `tail` is the next word (`P.t = P.h + 8`).

- `enq_spec ph`: for either phase `ph` of the enqueuer (`PhOk`), from `EL'`
  (the node's data word written; node in `x1`) to `Linked` (the node linked
  and `tail` swung past it, `LinkS`).
- `deq_spec`: from `ComD2` to `ComD2`, the dequeued data word `r` in `x0` with
  `First P r` (its own swing of `head` recorded), and `DoneD2 x0 r` for every
  `x0` whose `First` held at entry (FIFO across two calls).

`deq`'s loop has the zero-step back edge `cbz x5, deq` from `deq_ne`
(msqueue2's `deqRank2` issue), so `deq_spec` uses `cfgEnv_partial_fun_rank`,
`cfgEnv_partial_fun` with `cfgEnv_partial_rank_at`'s lexicographic measure
(generic; a hoist candidate beside `cfgEnv_partial_fun`).
-/
import Kraken.Promising.Lower.MsqPilotProg
import Kraken.Promising.Lower.PilotSpecs

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.MsqPilot

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The function rule with a label rank -/

open MachineWP in
/-- **`cfgEnv_partial_fun` with a label rank** `ρ`: every exit to a label of
the fragment is guarded by `EdgeRank` (smaller rank, or the same rank and
later in the text, or a changed state); the conclusion is the run into `E`. -/
theorem cfgEnv_partial_fun_rank [CodeEnv] {env : SharedEnv} {p p' : Program}
    {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    (T : Label → MachineData → env.State → Prop) (ρ : Label → Nat)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g => T l s g ∧ s = s₀ ∧ g = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g ∧ EdgeRank p ρ l s₀ g₀ l' s g
         | none => fun _ _ _ => False);
        fun a s g => Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ EdgeRank p ρ l s₀ g₀ l' s g) a s g ∨ E a s g ⦄)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s g, T l₀ s g → Safely (cenv.instrStepEnv env) (fun x => E x.1.2 x.1.1 x.2)
      ((s, (_root_.Executable.labels cenv).label l₀), g) := by
  have hnd := hwf.nodup
  intro s g hT
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  let N := (Program.view p).2.length
  let ν : Label → Nat := fun l => ρ l * (N + 1) + (N - Program.blockIdx p l)
  have hdec : ∀ l l', Program.blockIdx p l < N →
      (ρ l' < ρ l ∨ (ρ l' = ρ l ∧ Program.blockIdx p l < Program.blockIdx p l')) → ν l' < ν l := by
    intro l l' hl h
    have h1 := hK l'
    rcases h with h | ⟨h, h'⟩
    · have h2 : (ρ l' + 1) * (N + 1) ≤ ρ l * (N + 1) := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at h2
      simp only [ν]
      omega
    · simp only [ν, h]
      omega
  have hedge : ∀ l l' s₀ g₀ s g, Program.blockIdx p l < N → EdgeRank (env := env) p ρ l s₀ g₀ l' s g →
      ν l' < ν l ∨ ¬(s = s₀ ∧ g = g₀) := by
    rintro l l' s₀ g₀ s g hidx (h | h | hne)
    · exact .inl (hdec l l' hidx (.inl h))
    · exact .inl (hdec l l' hidx (.inr h))
    · exact .inr hne
  have key := Program.linkEnv_partial (env := env)
    (post := fun x => E x.1.2 x.1.1 x.2)
    (fun l => (Program.blockAt p l).elim [] (·.body))
    (fun l => (_root_.Executable.labels cenv).label l)
    (fun l s g => (Program.blockAt p l).isSome ∧ T l s g)
    (fun j i => ν j < ν i) (measure ν).wf ?_ ?_
  · exact key l₀ s g ⟨blockAt_entry' hp, hT⟩
  · intro l
    cases hb : Program.blockAt p l with
    | none => exact trivial
    | some blk => simpa using hpl.block l blk hb
  · intro l s₀ g₀
    cases hb : Program.blockAt p l with
    | none => exact fun s g hpre => absurd hpre.1.1 (by simp)
    | some blk =>
      simp only [Option.elim]
      rintro s g ⟨⟨-, hTl⟩, rfl, rfl⟩
      have hidx : Program.blockIdx p l < (Program.view p).2.length := Program.blockIdx_lt hnd hb
      have hw := (hblocks l blk hb s g).le_wp s g ⟨hTl, rfl, rfl⟩
      rw [wpEnv_eq] at hw
      refine Executable.wpEnv_mono ?_ ?_ hw
      · intro s' g' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hsome', -⟩ := Program.blockAt_next hnd hb hnx
          obtain ⟨hq, he⟩ := hq
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hq⟩, ?_⟩
          rcases hedge l l' s g s' g' hidx he with h | hne
          · exact .inl h
          · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩
        | none =>
          rw [hnx] at hq
          exact hq.elim
      · rintro a s' g' (⟨l', hlab, hsome', hTl', he⟩ | he)
        · refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
          rcases hedge l l' s g s' g' hidx he with h | hne
          · exact .inl h
          · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩
        · exact Or.inl he

/-- `deq`'s label rank: `deq_ne` above `deq` (its `cbz x5, deq` is a
zero-step back edge), as `deqRank2`. -/
def deqRank (l : Label) : Nat := if l = "deq_ne" then 1 else 0

/-! ## `enq` -/

section Enq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progE)]

local instance progE.env : CodeEnv := ⟨layout progE⟩

omit layout [Executable.ValidLayout (layout progE)] in
theorem progE_wf : Program.WF progE := by decide

/-- Where `progE`'s blocks sit. -/
theorem progE_placed : Program.Placed progE "main_e" :=
  Program.placed_of_layout progE_wf rfl (by decide)

/-- `enq`'s precondition: `X30 = ra`, `x0 = q = &head`, `x1` the phase's
node, its data word written (`EL'`). -/
def EnqPre (P : Params2) (ph : Ph) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) :
    Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.h ∧ t.regs.X1.toBitVec = ph.n ∧ NoDmem t ∧ EL' P ph σ.1

/-- `enq`'s postcondition: the frame kept, the node linked (`Linked`). -/
def EnqPost (P : Params2) (ph : Ph) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EE2 P)).State)
    (t' : MachineData) (σ' : (SharedEnv.counted (EE2 P)).State) : Prop :=
  CalleeSaved t t' ∧ Linked P ph σ'.1

/-- `enq`'s table: msqueue2's `enq1`/`enq1_loop`/`enq1_fix` rows of
`enqTable2`, behind the argument moves. -/
abbrev enqTable (P : Params2) (ph : Ph) (ra : Int64) (t : MachineData) :
    Label → MachineData → (SharedEnv.counted (EE2 P)).State → Prop :=
  fun lb s σ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧
    CalleeSaved t s ∧
    ((lb = "enq" ∧ s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = ph.n ∧ EL' P ph σ.1) ∨
      (lb = "enq_loop" ∧ s.regs.X1.toBitVec = P.t ∧ s.regs.X2.toBitVec = ph.n ∧ EL' P ph σ.1) ∨
      (lb = "enq_fix" ∧ s.regs.X1.toBitVec = P.t ∧ s.regs.X2.toBitVec = ph.n ∧ ∃ y3 y4 : Val,
        s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧ s.regs.X4.toBitVec = BitVec.setWidth 64 y4 ∧
        BitVec.setWidth 64 y4 ≠ 0 ∧ EL2' P ph y3 y4 σ.1))

set_option hygiene false in
/-- Jump to a table row (selected by `decide`) with its facts `t`, the frame
kept; leaves the edge condition. -/
local macro "eland" t:term : tactic => `(tactic| (
  first
  | refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, ?_⟩, ?_⟩)
    · simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true]
      exact $t
  | refine ⟨by simpa using hd8, by simpa using hd4, by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, ?_⟩
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true]
    exact $t))

set_option hygiene false in
/-- The two reads of a loop iteration (`h2`: `EL2'` after them), as
`MsQueue2VCGen`'s `e_reads`. -/
local macro "e_reads" : tactic => `(tactic| (
  obtain ⟨hx1, hx2, hE⟩ := hT
  have h1 := (vc_e_ldar_tail2 (xcl := false) hph _ hE v3 σ1.1 (by simpa [hx1, Params.tail] using hld1.1)).fence
    hph hf1.1
  have h2 := (vc_e_ldar_link2 hph _ h1 v4 σ3.1 (by simpa using hld2.1)).fence hph hf2.1))

/-- **`enq`'s specification**, once, for both calls. -/
theorem enq_spec (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (ph : Ph) (hph : PhOk P ph) :
    FunSpecPartialEnv (SharedEnv.counted (EE2 P)) ((_root_.Executable.labels cenv).label "enq") (EnqPre P ph)
      (EnqPost P ph) := by
  rintro ra t g ⟨hlr, hx0, hx1, ⟨hd8, hd4⟩, hEL⟩
  refine cfgEnv_partial_fun (p := enqFrag) (enqTable P ph ra t)
    (E := fun a s σ => a = ra ∧ EnqPost P ph ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE progE_placed (by decide)) t g
    ⟨hd8, hd4, hlr, by simp [CalleeSaved], .inl ⟨rfl, hx0, hx1, hEL⟩⟩
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hd8, hd4]; done)
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    obtain ⟨hx0, hx1, hE⟩ := hT
    eland ⟨by simp [hx0, ht], by simp [hx1], (hE.fence hph hf1.1).fence hph hf2.1⟩
  case vc7 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hnz σ4 hld1 hf1 hld2 hf2 _
    e_reads
    simp at hnz
    eland ⟨by simp [hx1], by simp [hx2], v3, v4, by simp, by simp, hnz, h2⟩
    exact .inl (by decide)
  case vc10 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 hld1 hf1 hld2 hf2 hf3 _
    e_reads
    have h := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).1
    simp [hx2]
    simpa [casOp64] using h
  case vc11 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hnz5 σ7 hld1 hf1 hld2 hf2 hf3 hcas hf4 _
    e_reads
    have hc := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hx2, casOp64] using hcas.1)
    simp at hnz5
    rcases hc with ⟨-, hEL⟩ | ⟨h0, -⟩
    · eland ⟨by simp [hx1], by simp [hx2], hEL.fence hph hf4.1⟩
      refine .inr fun ⟨_, hg⟩ => ?_
      subst hg
      have e1 := hld1.2; have e2 := hld2.2; have e3 := hcas.2; have e4 := hf1.2; have e5 := hf2.2
      have e6 := hf3.2; have e7 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at e1 e2 e3
      omega
    · exact absurd (by simpa using h0) hnz5
  case vc14 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 _
    e_reads
    have hc := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hx2, casOp64] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have h := (vc_e_swing2 hL hph _ ((hC.fence hph hf4.1).fence hph hf5.1) (BitVec.setWidth 64 v3)).1
    simp [hx1, hx2]
    simpa [casOp64, Params.tail] using h
  case vc15 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 old2 σ9 σ10 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 hcas2 hf6 _
    e_reads
    have hc := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hx2, casOp64] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have hC2 := (vc_e_swing2 hL hph _ ((hC.fence hph hf4.1).fence hph hf5.1) (BitVec.setWidth 64 v3)).2 old2 σ9.1
      (by simpa [hx1, hx2, casOp64, Params.tail] using hcas2.1)
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, hC2.fence hph hf6.1⟩
  case vc3 =>
    rename_i s σ0 σ1 hf1 _
    obtain ⟨hx1, hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have h := (vc_e_fix2 hL hph _ (h2.fence hph hf1.1) hnz).1
    simp [hx1, hy3, hy4]
    simpa [casOp64, Params.tail] using h
  case vc4 =>
    rename_i s σ0 σ1 old σ2 σ3 hf1 hcas hf2 _
    obtain ⟨hx1, hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have hEL := (vc_e_fix2 hL hph _ (h2.fence hph hf1.1) hnz).2 old σ2.1
      (by simpa [hx1, hy3, hy4, casOp64, Params.tail] using hcas.1)
    eland ⟨by simp [hx1], by simp [hx2], hEL.fence hph hf2.1⟩
    refine .inr fun ⟨_, hg⟩ => ?_
    subst hg
    have e1 := hcas.2; have e2 := hf1.2; have e3 := hf2.2
    simp only [SharedEnv.tick_rmw] at e1
    omega
  all_goals done

end Enq

/-! ## `deq` -/

section Deq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD)]

local instance progD.env : CodeEnv := ⟨layout progD⟩

omit layout [Executable.ValidLayout (layout progD)] in
theorem progD_wf : Program.WF progD := by decide

/-- Where `progD`'s blocks sit. -/
theorem progD_placed : Program.Placed progD "main_d" :=
  Program.placed_of_layout progD_wf rfl (by decide)

/-- The dequeue's frame fact: every `First` of the entry state `σ₀` still
holds (a `YOk`, from `yok_first`). -/
def Kept (P : Params2) (σ₀ : State isa) (σ : State isa) : Prop := ∀ x0, First P x0 σ₀ → First P x0 σ

omit layout [Executable.ValidLayout (layout progD)] in
theorem yok_kept (P : Params2) (σ₀ : State isa) : YOk P (Kept P σ₀) :=
  ⟨fun h hf x0 h0 => (yok_first x0).fence (h x0 h0) hf, fun h hf x0 h0 => (yok_first x0).load (h x0 h0) hf,
    fun h hs x0 h0 => (yok_first x0).rmw (h x0 h0) hs⟩

/-- `deq`'s precondition: `X30 = ra`, `x0 = q = &head`, `ComD2`. -/
def DeqPre (P : Params2) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (ED2 P)).State) : Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.h ∧ NoDmem t ∧ ComD2 P σ.1

/-- `deq`'s postcondition: the frame kept, `ComD2`, the result `r = x0` with
its `First`, and `DoneD2 x0 r` for every `x0` whose `First` held at entry. -/
def DeqPost (P : Params2) (_ : Int64) (t : MachineData) (σ : (SharedEnv.counted (ED2 P)).State)
    (t' : MachineData) (σ' : (SharedEnv.counted (ED2 P)).State) : Prop :=
  CalleeSaved t t' ∧ ComD2 P σ'.1 ∧ First P t'.regs.X0.toBitVec σ'.1 ∧
    ∀ x0, First P x0 σ.1 → DoneD2 σ'.1.snap.mem P x0 t'.regs.X0.toBitVec

/-- `deq`'s table: msqueue2's `deq1a`/`deq1a_ne` rows of `deqTable2`, with the
frame `Kept`. -/
abbrev deqTable (P : Params2) (ra : Int64) (t : MachineData) (σ₀ : State isa) :
    Label → MachineData → (SharedEnv.counted (ED2 P)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.h ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧ CalleeSaved t s ∧
    ((lb = "deq" ∧ ComD2 P σ.1 ∧ Kept P σ₀ σ.1) ∨
      (lb = "deq_ne" ∧ ∃ y3 y5 : Val, s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧
        s.regs.X5.toBitVec = BitVec.setWidth 64 y5 ∧ DQ3 P (Kept P σ₀) y3 y5 σ.1))

set_option hygiene false in
/-- Jump to `deq`'s table row of the target label with its facts `t`. -/
local macro "dland" t:term : tactic => `(tactic| (
  refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4,
    by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, ?_⟩, ?_⟩)
  · (simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true])
    exact $t))

set_option hygiene false in
/-- The three reads of an iteration (`h3`: `DQ3` after them), as
`MsQueue2VCGen`'s `d_reads`. -/
local macro "d_reads" : tactic => `(tactic| (
  have hY := yok_kept P g.1
  have h1 := vc_d_ldar_head2 (xcl := false) hY _ (hT.1.fence hfa.1) (hY.fence hT.2 hfa.1) v3 σ1.1 (by simpa [hx0, Params.head] using hld1.1)
  have h2 := (vc_d_load2 hY _ h1 v4 σ2.1 hld2.1).fence hY hf1.1
  have h3 := ((vc_d_ldar_link2 hY _ h2 v5 σ4.1 (by simpa using hld3.1)).fence hY hf2.1).fence hY hf3.1))

set_option hygiene false in
/-- The edge back to `deq` (the variant decreased). -/
local macro "d_back" : tactic => `(tactic| (
  refine .inr (.inr fun ⟨_, hg⟩ => ?_)
  subst hg
  simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *
  omega))

/-- **`deq`'s specification**, once, for both calls. -/
theorem deq_spec (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) :
    FunSpecPartialEnv (SharedEnv.counted (ED2 P)) ((_root_.Executable.labels cenv).label "deq") (DeqPre P)
      (DeqPost P) := by
  rintro ra t g ⟨hlr, hx0, ⟨hd8, hd4⟩, hC⟩
  refine cfgEnv_partial_fun_rank (p := deqFrag) (deqTable P ra t g.1) deqRank
    (E := fun a s σ => a = ra ∧ DeqPost P ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE progD_placed (by decide)) t g
    ⟨hx0, hd8, hd4, hlr, by simp [CalleeSaved], .inl ⟨rfl, hC, fun _ h => h⟩⟩
  cfg_cases_env_rank [deqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hd8]; done)
  case vc10 =>
    rename_i s σ0 σa v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hfa hld1 hld2 hf1 hld3 hf2 hf3 _
    d_reads
    dland ⟨v3, v5, by simp, by simp, h3⟩
    have e0 := hfa.2; have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    d_back
  case vc11 =>
    rename_i s σ0 σa v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hz σ7 hfa hld1 hld2 hf1 hld3 hf2 hf3 hf4 _
    d_reads
    dland ⟨(h3.fence hY hf4.1).1, (h3.fence hY hf4.1).2.1⟩
    have e0 := hfa.2; have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2
    d_back
  case vc14 =>
    rename_i s σ0 σa v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 hfa hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 _
    d_reads
    simp at hnz
    have h := (vc_d_help2 hL hY _ ((h3.fence hY hf4.1).fence hY hf5.1) hnz).1
    simp [hx0]
    simpa [casOp64, Params.tail, ht] using h
  case vc15 =>
    rename_i s σ0 σa v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 old σ9 σ10 hfa hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 hcas hf6 _
    d_reads
    simp at hnz
    have hc := (vc_d_help2 hL hY _ ((h3.fence hY hf4.1).fence hY hf5.1) hnz).2 old σ9.1
      (by simpa [hx0, ht, casOp64, Params.tail] using hcas.1)
    dland ⟨hc.1.fence hf6.1, hY.fence hc.2 hf6.1⟩
    have e0 := hfa.2; have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2; have e8 := hf5.2; have e9 := hcas.2; have e10 := hf6.2
    d_back
  case vc1 =>
    rename_i s σ0 hz σ1 hf _
    have hY := yok_kept P g.1
    obtain ⟨y3, y5, -, -, hD3⟩ := hT
    dland ⟨(hD3.fence hY hf.1).1, (hD3.fence hY hf.1).2.1⟩
    exact .inl (by decide)
  case vc6 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 hf1 hld hf2 _
    have hY := yok_kept P g.1
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr2 hY _ (hD3.fence hY hf1.1) hnz' u σ2.1 hu.1).fence hY hf2.1
    have h := (vc_d_cas2 hL hY _ hD4).1
    simp [hx0, hy3, hy5]
    simpa [casOp64, Params.head] using h
  case vc7 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 hne σ6 hf1 hld hf2 hcas hf3 hf4 _
    have hY := yok_kept P g.1
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr2 hY _ (hD3.fence hY hf1.1) hnz' u σ2.1 hu.1).fence hY hf2.1
    have hc := (vc_d_cas2 hL hY _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    dland ⟨(hc.1.fence hf3.1).fence hf4.1, hY.fence (hY.fence hc.2.1 hf3.1) hf4.1⟩
    exact .inl (by decide)
  case vc8 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 heq σ6 σ7 σ8 hf1 hld hf2 hcas hf3 hf4 hf5 hf6 _
    have hY := yok_kept P g.1
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr2 hY _ (hD3.fence hY hf1.1) hnz' u σ2.1 hu.1).fence hY hf2.1
    have hc := (vc_d_cas2 hL hY _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    simp [hy3] at heq
    obtain ⟨hF, hD⟩ := hc.2.2 (TreiberCommon.bv64_eq_of_sub_eq_zero heq)
    have hY1 := yok_first (P := P) (BitVec.setWidth 64 (BitVec.setWidth 32 u))
    refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
      (((hc.1.fence hf3.1).fence hf4.1).fence hf5.1).fence hf6.1, ?_, ?_⟩
    · simpa using hY1.fence (hY1.fence (hY1.fence (hY1.fence hF hf3.1) hf4.1) hf5.1) hf6.1
    · intro x0 h0
      have := hD x0 (hD4.2.1 x0 h0)
      simpa [hf3.1.snap, hf4.1.snap, hf5.1.snap, hf6.1.snap] using this
  all_goals done

end Deq

end Kraken.Promising.Lower.MsqPilot
