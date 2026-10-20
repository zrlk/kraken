/-
**The specifications of `enq` and of the try-once `wdeq`** of `wcMsqX`
(`Lower/WcMsqXProg.lean`) on the try-once dequeuer protocol
(`EnvG/X64MsQueueW{Ghost,VC}.lean`). ISA: x64; counted
`EnvGCAdjX Arch.tso` on `sAll`, plans `planE` (thread `0`), `planDW` (`1`).

- `enq_fragXW`: the pilot's `enq` (`MsqXR.enqFrag`, unchanged) at `GWW`
  (`E0W` to `LinkedW`), as the pilot's `enq_fragXR` with the `↦W` VCs.
- `wdeq_fragXW`: from `ComDW` (frame `YW`: the entry's `First` records,
  `InitV`) `wdeq` returns the tag in `rax`: `1` (seen empty; `tokQ` kept) or
  `0` with the node in `rdx`, dequeued by its own swing of `head` (`First`),
  after every earlier dequeue (`DoneD2`), `tokQ` kept unless it is `n1`. The
  only back edge (a failed `lock cmpxchgq`) follows shared accesses.
-/
import Kraken.Promising.Lower.WcMsqXProg
import Kraken.Promising.Lower.MsqXRSpecs
import Kraken.Promising.SLR.EnvG.X64MsQueueWVC
import Kraken.Promising.SLR.EnvG.X64MsQueueWFinal

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.WcMsqX

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 sAll mem_sAll8)
open Kraken.Promising.X64.EnvG.Treiber2X (stepL stepR okR)
open Kraken.Promising.Lower.PilotX (Saved Saved.refl)
open Kraken.Promising.Lower.PilotXR (D8 ofBitVec_reg)
open Kraken.Promising.Lower.MsqXR (enqFrag Kept)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## `enq` -/

/-- `enq`'s precondition: link `ra`, `rdi = &tail`, `rsi = n`, `E0W` of `n`. -/
def EnqPreW (P : Params) (n : BitVec 64) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EEX P)).State) :
    Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ t.regs.get64 .rdi = P.t ∧ t.regs.get64 .rsi = n ∧ D8 t.dmem ∧ E0W P n σ.1

/-- `enq`'s postcondition: the frame kept, `n` linked (`LinkedW`). -/
def EnqPostW (P : Params) (n : BitVec 64) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EEX P)).State)
    (s : MachineData) (σ : (SharedEnv.counted (EEX P)).State) : Prop :=
  Saved t s ∧ ∃ y3, LinkedW P n y3 σ.1

/-- `enq`'s loop table. -/
abbrev enqTableW (P : Params) (n : BitVec 64) (ra : Int64) (t : MachineData) (_ : (SharedEnv.counted (EEX P)).State) :
    Label → MachineData → (SharedEnv.counted (EEX P)).State → Prop :=
  fun lb s σ => s.regs.get64 .r11 = ra.toBitVec ∧ s.regs.get64 .rdi = P.t ∧ s.regs.get64 .rsi = n ∧
    Saved t s ∧ D8 s.dmem ∧
    ((lb = "enq" ∧ E0W P n σ.1) ∨
      (lb = "enq_swing" ∧ ∃ y3 y4, s.regs.get64 .rdx = BitVec.setWidth 64 y3 ∧
        s.regs.get64 .rcx = BitVec.setWidth 64 y4 ∧ BitVec.setWidth 64 y4 ≠ 0 ∧ E2W P n y3 y4 σ.1))

open Lean Elab Tactic in
/-- The counts of the run's fences and RMWs (for a back edge's `omega`). -/
local elab "fen_all" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let e ← Term.exprToSyntax d.toExpr
    let isFen : Bool := match ty.getAppFn.constName? with
      | some (.str n "le") => (n.toString.splitOn "FenceMono").length > 1 | _ => false
    if isFen then evalTactic (← `(tactic| have := (fenC $e).2))
    else if ty.isAppOf ``SharedEnv.step then
      try evalTactic (← `(tactic| have := by with_reducible exact (rmwC $e).2)) catch _ => pure ()

set_option hygiene false in
/-- The registers of the table, the frame `Saved`, after a block (only
caller-saved registers written). -/
local macro "regs_kept" : tactic => `(tactic| (
  all_goals first
    | (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; first | assumption | exact ofBitVec_reg h11)
    | skip))

set_option hygiene false in
/-- `enq`'s three reads: `h3 : E2W` after them. -/
local macro "e_reads" : tactic => `(tactic| (
  obtain ⟨w3, hs1, c1, e3⟩ := ldC hd8 ld1
  have h1 := vc_e_load_tailW _ hT w3 g1.1 (stepL hs1 (by simp [hdi', Params.tail]))
  obtain ⟨w4, hs2, c2, e4⟩ := ldC hd8 ld2
  have h2 := vc_e_load_linkW _ h1 w4 g2.1 (stepL hs2 (by simp [e3]))
  obtain ⟨w5, hs3, c3, e5⟩ := ldC hd8 ld3
  have h3 := vc_e_load2W _ h2 w5 g3.1 hs3))

set_option hygiene false in
/-- Land at `enq` with `E0W` `t` (a back edge: the count went up). -/
local macro "to_enq" t:term : tactic => `(tactic| (
  dsimp only
  refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8,
    .inl ⟨rfl, $t⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
  regs_kept))

set_option hygiene false in
/-- A path through a `lock cmpxchgq` that contradicts its flags. -/
local macro "cas_absurd" : tactic => `(tactic| (
  simp at heq
  simp [CondCode.interp, StatusFlags.from_result] at cn
  first | exact absurd heq cn | exact absurd cn heq | simp [heq] at cn))

set_option hygiene false in
/-- After `e_reads` and the fences up to the link: `hc`, the link's outcomes. -/
local macro "e_link" : tactic => `(tactic| (
  have hE := ((((h3.fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1).fence (fenC f8).1
  have hc := (vc_e_linkW hL _ hE).2 old g9.1 (stepR (rmwC hc).1 (by simp [e3]) (by funext x; simp [cmpxOp64, hsi']))))

set_option maxHeartbeats 12000000 in
/-- **`enq`'s specification** (the fragment, every placement): from `E0W` of
`n` with the link in `r11`, `enq` returns to the link with `n` linked. -/
theorem enq_fragXW (P : Params) (n : BitVec 64) (hL : QLocs P) :
    FragSpecEnv (SharedEnv.counted (EEX P)) enqFrag "enq" (EnqPreW P n) (EnqPostW P n) := by
  refine FragSpecEnv.of_cfg (enqTableW P n) rfl (by decide)
    (fun ra t g ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, Saved.refl t, h4, .inl ⟨rfl, h5⟩⟩) ?_
  intro _; rintro ra t g -
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : (_ ∧ _) ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨h11, hdi, hsi, ⟨sv1, sv2, sv3, sv4, sv5, sv6, fdm⟩, hd8, hT⟩, rfl, rfl⟩ := hx
  all_goals simp only [String.reduceEq, true_and, false_and, or_false, false_or] at hT
  all_goals have hdi' := hdi; have hsi' := hsi; simp only [Reg64s.get64] at hdi' hsi'
  -- `enq`
  case vc1 | vc2 | vc3 => exact ⟨trivial, mem_sAll8 _⟩
  case vc4 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 _
    e_reads
    to_enq (h3.e0.fence (fenC f4).1).fence (fenC f5).1
    subst hg; fen_all; omega
  case vc5 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 _
    e_reads
    simp [CondCode.interp, StatusFlags.from_result] at ct
    dsimp only
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8,
      .inr ⟨rfl, w3, w4, by simp [e3], by simp [e4], by simpa [e4] using ct,
        (((h3.fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1⟩⟩,
      .inl (by decide)⟩)
    regs_kept
  case vc6 | vc9 => exact hd8 _
  case vc7 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 b8 g8 f8 _
    e_reads
    have hE := ((((h3.fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1).fence (fenC f8).1
    exact okRC (okR (vc_e_linkW hL _ hE).1 (by simp [e3]) (by funext x; simp [cmpxOp64, hsi'])) (mem_sAll8 _)
  case vc8 =>
    rename_i old g9 hc heq cn g10 f10 _; cas_absurd
  case vc14 | vc15 =>
    rename_i old g9 hc heq cn g10 f10 g11 f11 _; cas_absurd
  case vc16 | vc17 =>
    rename_i old g9 hc heq cn g10 f10 g11 f11 old2 g12 hc2 heq2 g13 f13 _; cas_absurd
  case vc10 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 b8 g8 f8 old g9 hc heq cn g10 f10
      g11 f11 _
    e_reads; e_link
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hLk⟩
    · exact absurd heq hne
    have hLk' := (hLk.fence (fenC f10).1).fence (fenC f11).1
    exact okRC (okR (vc_e_swingW hL _ hLk').1 (by simp [hdi', Params.tail])
      (by funext x; simp [cmpxOp64, e3, hsi'])) (mem_sAll8 _)
  case vc11 | vc12 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 b8 g8 f8 old g9 hc heq cn g10 f10
      g11 f11 old2 g12 hc2 heq2 g13 f13 _
    e_reads; e_link
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hLk⟩
    · exact absurd heq hne
    have hLk' := (hLk.fence (fenC f10).1).fence (fenC f11).1
    have hs := (vc_e_swingW hL _ hLk').2 old2 g12.1 (stepR (rmwC hc2).1 (by simp [hdi', Params.tail])
      (by funext x; simp [cmpxOp64, e3, hsi']))
    refine .inr ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, _, hs.fence (fenC f13).1⟩
    regs_kept
  case vc13 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 b8 g8 f8 old g9 hc heq cn g10 f10 _
    e_reads; e_link
    simp at heq
    rcases hc with ⟨-, hE0⟩ | ⟨hz, -⟩
    · to_enq hE0.fence (fenC f10).1
      subst hg; fen_all; omega
    · exact absurd hz heq
  -- `enq_swing`
  case vc1 => exact hd8 _
  case vc2 =>
    rename_i g1 f1 _
    obtain ⟨y3, y4, hb, hcx, hnz, h2⟩ := hT
    have hcx' := hcx; have hb' := hb; simp only [Reg64s.get64] at hcx' hb'
    exact okRC (okR (vc_e_helpW hL _ (h2.fence (fenC f1).1) hnz).1 (by simp [hdi', Params.tail])
      (by funext x; simp [cmpxOp64, hb', hcx'])) (mem_sAll8 _)
  case vc3 | vc4 =>
    rename_i g1 f1 old g2 hc heq g3 f3 _
    obtain ⟨y3, y4, hb, hcx, hnz, h2⟩ := hT
    have hcx' := hcx; have hb' := hb; simp only [Reg64s.get64] at hcx' hb'
    have hE := (vc_e_helpW hL _ (h2.fence (fenC f1).1) hnz).2 old g2.1
      (stepR (rmwC hc).1 (by simp [hdi', Params.tail]) (by funext x; simp [cmpxOp64, hb', hcx']))
    to_enq hE.fence (fenC f3).1
    subst hg; fen_all; omega

/-! ## `wdeq` -/

/-- The try-once dequeuer's environment, restricted to `sAll`. -/
noncomputable abbrev EDXW (P : Params) : SharedEnv := EnvGCAdjX Arch.tso 1 (planDW P) sAll

/-- **`wdeq`'s frame**: the first-dequeue records of `g` kept, and the
queue's initial values in the dequeuer's memory. -/
def YW (P : Params) (g σ : EStateX) : Prop := Kept P g σ ∧ InitV σ.snap.mem P

/-- **`tokQ` kept** from `g` to `σ` (the body of `MsQueueX.TokKept`,
`SLR/EnvG/X64MsQueueWVC.lean`; the `TK` lemmas are its lemmas). -/
def TK (P : Params) (g σ : EStateX) : Prop := TokFrozen P.tokQ g.r → TokFrozen P.tokQ σ.r

/-- `YW` is a frame of the dequeuer's VCs (`MsQueueX.yokW_kept`). -/
theorem yokW_YW (P : Params) (g : EStateX) : YOkW P (YW P g) := yokW_kept P g

theorem TK.fence {P : Params} {g σ σ' : EStateX} (h : TK P g σ) (hf : X64.EnvG.FenceLe σ σ') : TK P g σ' :=
  TokKept.fence h hf

theorem TK.load {P : Params} {g σ σ' : EStateX} (h : TK P g σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64}
    {m : Nat} {v : Val} (hs : (EDW P).step (.load k xcl a m) σ v σ') : TK P g σ' :=
  TokKept.load h hs

/-- `wdeq`'s precondition: link `ra`, `rdi = &head`, `ComDW`, `InitV`. -/
def WDeqPre (P : Params) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EDXW P)).State) : Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ t.regs.get64 .rdi = P.h ∧ D8 t.dmem ∧ ComDW P σ.1 ∧ InitV σ.1.snap.mem P

/-- `wdeq`'s postcondition: the frame, `ComDW`, `YW`, and the tag `rax`:
`1` with `tokQ` kept, or `0` with the node `rdx` recorded (`First`, `DoneD2`
after every `First` of the entry) and `tokQ` kept unless `rdx = n1`. -/
def WDeqPost (P : Params) (_ : Int64) (t : MachineData) (g : (SharedEnv.counted (EDXW P)).State)
    (s : MachineData) (σ : (SharedEnv.counted (EDXW P)).State) : Prop :=
  Saved t s ∧ ComDW P σ.1 ∧ YW P g.1 σ.1 ∧
    ((s.regs.get64 .rax = 1 ∧ TK P g.1 σ.1) ∨
      (s.regs.get64 .rax = 0 ∧ First P (s.regs.get64 .rdx) σ.1 ∧
        (∀ x0, First P x0 g.1 → DoneD2 σ.1.snap.mem P x0 (s.regs.get64 .rdx)) ∧
        (TokFrozen P.tokQ g.1.r → TokFrozen P.tokQ σ.1.r ∨ s.regs.get64 .rdx = P.n1)))

/-- `wdeq`'s table: the same facts at `wdeq` and `wdeq_empty`. -/
abbrev wdeqTable (P : Params) (ra : Int64) (t : MachineData) (g : (SharedEnv.counted (EDXW P)).State) :
    Label → MachineData → (SharedEnv.counted (EDXW P)).State → Prop :=
  fun lb s σ => s.regs.get64 .r11 = ra.toBitVec ∧ s.regs.get64 .rdi = P.h ∧ Saved t s ∧ D8 s.dmem ∧
    ComDW P σ.1 ∧ YW P g.1 σ.1 ∧ TK P g.1 σ.1 ∧ (lb = "wdeq" ∨ lb = "wdeq_empty")

/-- `ComDW`, `YW` and `TK` through a fence (`MsQueueX.stW_fence` at `YW`). -/
theorem stW_fence {P : Params} {g σ σ' : EStateX} (h : ComDW P σ ∧ YW P g σ ∧ TK P g σ)
    (hf : X64.EnvG.FenceLe σ σ') : ComDW P σ' ∧ YW P g σ' ∧ TK P g σ' :=
  MsQueueX.stW_fence (yokW_YW P g) h hf

/-- `wdeq`'s result facts through a fence (alias of `MsQueueX.resW_fence`). -/
theorem resW_fence {P : Params} {g σ σ' : EStateX} {x : BitVec 64}
    (h : First P x σ ∧ (∀ x0, First P x0 g → DoneD2 σ.snap.mem P x0 x) ∧
      (TokFrozen P.tokQ g.r → TokFrozen P.tokQ σ.r ∨ x = P.n1)) (hf : X64.EnvG.FenceLe σ σ') :
    First P x σ' ∧ (∀ x0, First P x0 g → DoneD2 σ'.snap.mem P x0 x) ∧
      (TokFrozen P.tokQ g.r → TokFrozen P.tokQ σ'.r ∨ x = P.n1) :=
  MsQueueX.resW_fence h hf

/-- `h` through the fences `fs`, with `lem` the fence lemma. -/
local macro "ff% " lem:term:max h:term:max " [" fs:ident,* "]" : term => do
  let mut acc : Lean.Term := h
  for f in fs.getElems do acc ← `($lem $acc (fenC $f).1)
  return acc

set_option hygiene false in
/-- `wdeq`'s two reads and the test: `h5 : D2W` and `k5 : TK` at the swing. -/
local macro "w_reads" : tactic => `(tactic| (
  obtain ⟨w3, hs1, c1, e3⟩ := ldC hd8 ld1
  have h1 := vc_w_load (yokW_YW P g.1) _ ⟨hC, hY⟩ w3 g1.1 hs1
  obtain ⟨w4, hs2, c2, e4⟩ := ldC hd8 ld2
  have h2 := vc_w_load_link (y3 := w3) (yokW_YW P g.1) _ h1 w4 g2.1 (stepL hs2 (by simp [e3]))
  have k2 := (hK.load hs1).load hs2
  simp [CondCode.interp, StatusFlags.from_result] at cz))

set_option hygiene false in
/-- The swing's permission and outcome `hP`, after `w_reads`. -/
local macro "w_pop" : tactic => `(tactic| (
  have h5 := ff% (fun h hf => D2W.fence (yokW_YW P g.1) h hf) h2 [f3, f4, f5]
  have k5 := ff% TK.fence k2 [f3, f4, f5]
  have hP := (vc_w_pop hL hpt (yokW_YW P g.1) _ h5 (by rw [← e4]; exact cz)).2 old g6.1
    (stepR (rmwC hc).1 (by simp [hdi', Params.head]) (by funext x; simp [cmpxOp64, e3, e4]))
  simp at heq))

set_option maxHeartbeats 12000000 in
/-- **`wdeq`'s specification** (the fragment, every placement). -/
theorem wdeq_fragXW (P : Params) (hL : QLocs P) (hpt : P.trk = false) :
    FragSpecEnv (SharedEnv.counted (EDXW P)) wdeqFrag "wdeq" (WDeqPre P) (WDeqPost P) := by
  refine FragSpecEnv.of_cfg (wdeqTable P) rfl (by decide)
    (fun ra t g ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, Saved.refl t, h3, h4, ⟨fun _ h => h, h5⟩, id, .inl rfl⟩) ?_
  intro _; rintro ra t g -
  cfg_cases_env [wdeqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : (_ ∧ _) ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨h11, hdi, ⟨sv1, sv2, sv3, sv4, sv5, sv6, fdm⟩, hd8, hC, hY, hK, -⟩, rfl, rfl⟩ := hx
  all_goals have hdi' := hdi; simp only [Reg64s.get64] at hdi'
  -- `wdeq`
  case vc1 | vc2 => exact ⟨trivial, mem_sAll8 _⟩
  case vc3 =>
    rename_i v3 g1 ld1 v4 g2 ld2 b3 g3 f3 cz g4 f4 _
    w_reads
    have hb := ff% stW_fence ⟨h2.1, h2.2.1, k2⟩ [f3, f4]
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8, hb.1, hb.2.1, hb.2.2,
      .inr rfl⟩, .inl (by decide)⟩)
    regs_kept
  case vc4 => exact hd8 _
  case vc5 =>
    rename_i v3 g1 ld1 v4 g2 ld2 b3 g3 f3 cz g4 f4 g5 f5 _
    w_reads
    have h5 := ff% (fun h hf => D2W.fence (yokW_YW P g.1) h hf) h2 [f3, f4, f5]
    exact okRC (okR (vc_w_pop hL hpt (yokW_YW P g.1) _ h5 (by rw [← e4]; exact cz)).1
      (by simp [hdi', Params.head]) (by funext x; simp [cmpxOp64, e3, e4])) (mem_sAll8 _)
  case vc6 =>
    rename_i old g6 hc heq cn g7 f7 _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at cn
    exact absurd (by rw [heq]; exact BitVec.sub_self _) cn
  case vc9 =>
    rename_i old g6 hc heq cn g7 f7 b8 g8 f8 g9 f9 g10 f10 _
    simp [CondCode.interp, StatusFlags.from_result] at cn
    exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero cn).symm heq
  case vc7 =>
    rename_i v3 g1 ld1 v4 g2 ld2 b3 g3 f3 cz g4 f4 g5 f5 old g6 hc heq cn g7 f7 b8 g8 f8 g9 f9 g10 f10 _
    w_reads; w_pop
    have hx : BitVec.setWidth 64 old = BitVec.setWidth 64 w3 := heq.trans e3
    have hF := hP.2.2.1 hx
    have hc := ff% ComDW.fence hP.1 [f7, f8, f9, f10]
    have hy := ff% ((yokW_YW P g.1).fence) hP.2.1 [f7, f8, f9, f10]
    have hr := ff% resW_fence ⟨hF.1, fun x0 hx0 => hF.2 x0 (h5.2.1.1 x0 hx0),
      fun h => (hP.2.2.2 (k5 h)).imp_right fun h => h.2⟩ [f7, f8, f9, f10]
    refine .inr ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hc, hy, .inr ⟨by simp, ?_⟩⟩
    regs_kept
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e4]
    exact hr
  case vc8 =>
    rename_i v3 g1 ld1 v4 g2 ld2 b3 g3 f3 cz g4 f4 g5 f5 old g6 hc heq cn g7 f7 _
    w_reads; w_pop
    have hb := ff% stW_fence ⟨hP.1, hP.2.1, fun h => ((hP.2.2.2 (k5 h)).resolve_right fun ⟨hx, _⟩ =>
      heq (hx.trans e3.symm))⟩ [f7]
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8, hb.1, hb.2.1, hb.2.2,
      .inl rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    regs_kept
    subst hg; fen_all; omega
  -- `wdeq_empty`
  case vc1 =>
    rename_i g1 f1 g2 f2 _
    have hb := ff% stW_fence ⟨hC, hY, hK⟩ [f1, f2]
    refine .inr ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hb.1, hb.2.1, .inl ⟨by simp, hb.2.2⟩⟩
    regs_kept

end Kraken.Promising.Lower.WcMsqX
